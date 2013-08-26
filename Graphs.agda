--
-- Graphs of configurations
--

module Graphs where

open import Algebra
  using (module Monoid)
open import Data.Bool
  using (Bool; true; false; if_then_else_; not; _∧_; _∨_)
open import Data.Nat
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.List as List
open import Data.List.Properties
  using (∷-injective; map-compose)
open import Data.List.Any
  using (Any; here; there; module Membership-≡)
open import Data.List.Any.Properties
  using (Any-cong; Any↔; ++↔; return↔; map↔; concat↔; ⊎↔)
open import Data.List.Any.Membership as MB
  using (map-∈↔)
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃; ∃₂)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty
open import Data.Maybe
  using (Maybe; nothing; just)
open import Data.Unit
  using (⊤; tt)

open import Function
open import Function.Inverse as Inv
  using (_↔_; module Inverse)
open import Function.Related as Related
  using ()
  renaming (module EquationalReasoning to ∼-Reasoning)

import Relation.Binary.Sigma.Pointwise as Σ
open import Relation.Binary.Sum
  using (_⊎-cong_)
open import Relation.Binary.Product.Pointwise
  using (_×-cong_)

open import Relation.Binary.List.Pointwise as Pointwise
  using ([]; _∷_)

open import Relation.Nullary

open import Relation.Binary.PropositionalEquality as P
  hiding (sym)
  renaming ([_] to P[_])

private
  module LM {a} {A : Set a} = Monoid (List.monoid A)

open import Util

--
-- Graphs of configurations
--

-- A `Graph C` is supposed to represent a residual program.
-- Technically, a `Graph C` is a tree, with `back` nodes being
-- references to parent nodes.
-- 
-- A graph's nodes contain configurations. Here we abstract away
-- from the concrete structure of configurations.
-- In this model the arrows in the graph carry no information,
-- because, this information can be kept in nodes.
-- (Hence, this information is supposed to be encoded inside
-- "configurations".)
--
-- To simplify the machinery, back-nodes in this model of
-- supercompilation do not contain explicit references
-- to parent nodes. Hence, `back c` means that `c` is foldable
-- to a parent configuration (perhaps, to several ones).
-- 
-- * Back-nodes are produced by folding a configuration to another
--   configuration in the history.
-- * Forth-nodes are produced by
--     + decomposing a configuration into a number of other configurations
--       (e.g. by driving or taking apart a let-expression), or
--     + by rewriting a configuration by another one (e.g. by generalization,
--       introducing a let-expression or applying a lemma during
--       two-level supercompilation).

-- Graph

data Graph (C : Set) : Set where
  back  : ∀ (c : C) → Graph C
  forth : ∀ (c : C) (gs : List (Graph C)) → Graph C

--
-- Lazy graphs of configuration
--

-- A `LazyGraph C` represents a finite set of graphs
-- of configurations (whose type is `Graph C`).
--
-- "Lazy" graphs of configurations will be produced
-- by the "lazy" (staged) version of multi-result
-- supercompilation.

-- LazyGraph

data LazyGraph (C : Set) : Set where
  Ø     : LazyGraph C
  stop  : (c : C) → LazyGraph C
  build : (c : C) (lss : List (List (LazyGraph C))) → LazyGraph C

-- ≡Ø?

≡Ø? : {C : Set} (l : LazyGraph C) → Dec (l ≡ Ø)

≡Ø? Ø = yes refl
≡Ø? (stop c) = no (λ ())
≡Ø? (build c lss) = no (λ ())

-- The semantics of `LazyGraph C` is formally defined by
-- the interpreter `⟪_⟫` that generates a list of `Graph C n` from
-- a `LazyGraph C` by executing commands recorded in `LazyGraph C`.

mutual

  -- ⟪_⟫

  ⟪_⟫ : {C : Set} (l : LazyGraph C) → List (Graph C)

  ⟪ Ø ⟫ = []
  ⟪ stop c ⟫ =
    [ back c ]
  ⟪ build c lss ⟫ =
    map (forth c) ⟪ lss ⟫**

  -- ⟪_⟫**

  ⟪_⟫** : {C : Set} (lss : List (List (LazyGraph C))) →
              List (List (Graph C))

  ⟪ [] ⟫** = []
  ⟪ ls ∷ lss ⟫** = cartesian ⟪ ls ⟫* ++ ⟪ lss ⟫**

  -- ⟪_⟫*

  ⟪_⟫* : {C : Set} (ls : List (LazyGraph C)) →
              List (List (Graph C))
  ⟪ [] ⟫* = []
  ⟪ l ∷ ls ⟫* = ⟪ l ⟫ ∷ ⟪ ls ⟫*

-- `⟪_⟫*` has only been introduced to make the termination
-- checker happy. Actually, it is equivalent to `map ⟪_⟫`.

-- ⟪⟫*-is-map

⟪⟫*-is-map : {C : Set} (ls : List (LazyGraph C)) →
  ⟪ ls ⟫* ≡ map ⟪_⟫ ls

⟪⟫*-is-map [] = refl
⟪⟫*-is-map (l ∷ ls) =
  cong (_∷_ ⟪ l ⟫) (⟪⟫*-is-map ls)


--
-- Usually, we are not interested in the whole bag `⟪ l ⟫`.
-- The goal is to find "the best" or "most interesting" graphs.
-- Hence, there should be developed some techniques of extracting
-- useful information from a `LazyGraph C n` without evaluating
-- `⟪ l ⟫` directly.

-- This can be formulated in the following form.
-- Suppose that a function `select` filters bags of graphs,
-- removing "bad" graphs, so that
--
--     select ⟪ l ⟫
--
-- generates the bag of "good" graphs.
-- Let us find a function `extract` such that
--
--     extract l ≡ select ⟪ l ⟫
--
-- In many cases, `extract` may be more efficient (by several orders
-- of magnityde) than the composition `select ∘ ⟪_⟫`.

-- Sometimes, `extract` can be formulated in terms of "cleaners" of
-- lazy graphs. Let `clean` be a function that transforms lazy graphs,
-- such that
--
--     ⟪ clean l ⟫ ⊆ ⟪ l ⟫
--
-- Then `extract` can be constructed in the following way:
--
--     extract l ≡ ⟪ clean l ⟫
--
-- Theoretically speaking, `clean` is the result of "promoting" `select`:
--
--     select ∘ ⟪_⟫ ≗ ⟪_⟫ ∘ clean
--
-- The nice property of cleaners is that they are composable:
-- given `clean₁` and `clean₂`, `clean₂ ∘ clean₁` is also a cleaner.
--

--
-- Some filters
--

-- Removing graphs that contain "bad" configurations.
-- Configurations represent states of a computation process.
-- Some of these states may be "bad" with respect to the problem
-- that is to be solved by means of supercompilation.

mutual

  -- bad-graph

  bad-graph : {C : Set} (bad : C → Bool) (g : Graph C) → Bool

  bad-graph bad (back c) = bad c
  bad-graph bad (forth c gs) =
    bad c ∨ bad-graph* bad gs

  -- bad-graph*

  bad-graph* : {C : Set} (bad : C → Bool) (gs : List (Graph C)) → Bool

  bad-graph* bad [] = false
  bad-graph* bad (g ∷ gs) =
    bad-graph bad g ∨ bad-graph* bad gs

-- This filter removes the graphs containing "bad" configurations.

-- fl-bad-conf

fl-bad-conf : {C : Set} (bad : C → Bool) (gs : List (Graph C)) →
  List (Graph C)

fl-bad-conf bad gs = filter (not ∘ bad-graph bad) gs

--
-- Some cleaners
--

--
-- A cleaner that removes subtrees that represent empty sets of graphs.
--

mutual

  -- cl-empty

  cl-empty : {C : Set} (l : LazyGraph C) → LazyGraph C

  cl-empty Ø = Ø
  cl-empty (stop c) = stop c
  cl-empty (build c lss) with cl-empty** lss
  ... | [] = Ø
  ... | ls′ ∷ lss′ = build c (ls′ ∷ lss′)

  -- cl-empty**

  cl-empty** : {C : Set} (lss : List (List (LazyGraph C))) →
    List (List (LazyGraph C))

  cl-empty** [] = []
  cl-empty** (ls ∷ lss) with cl-empty-∧ ls
  ... | nothing = cl-empty** lss
  ... | just ls′ = ls′ ∷ cl-empty** lss

  -- cl-empty-∧

  cl-empty-∧ : {C : Set} (ls : List (LazyGraph C)) →
    Maybe (List (LazyGraph C))

  cl-empty-∧ [] = just []
  cl-empty-∧ (l ∷ ls) with cl-empty l
  ... | l′ with ≡Ø? l′
  ... | yes ≡Ø = nothing
  ... | no ≢Ø with cl-empty-∧ ls
  ... | nothing = nothing
  ... | just ls′ = just (l′ ∷ ls′)

--
-- Removing graphs that contain "bad" configurations.
-- The cleaner `cl-bad-conf` corresponds to the filter `fl-bad-conf`.
-- `cl-bad-conf` exploits the fact that "badness" to be monotonic,
-- in the sense that a single "bad" configuration spoils the whole
-- graph.

mutual

  -- cl-bad-conf

  cl-bad-conf : {C : Set} (bad : C → Bool) (l : LazyGraph C) →
    LazyGraph C

  cl-bad-conf bad Ø = Ø
  cl-bad-conf bad (stop c) =
    if bad c then Ø else (stop c)
  cl-bad-conf bad (build c lss) =
    if bad c then Ø else (build c (cl-bad-conf** bad lss))

  -- cl-bad-conf**

  cl-bad-conf** : {C : Set} (bad : C → Bool)
    (lss : List (List (LazyGraph C))) → List (List (LazyGraph C))

  cl-bad-conf** bad [] = []
  cl-bad-conf** bad (ls ∷ lss) =
    cl-bad-conf* bad ls ∷ (cl-bad-conf** bad lss)

  -- cl-bad-conf*

  cl-bad-conf* : {C : Set} (bad : C → Bool)
    (ls : List (LazyGraph C)) → List (LazyGraph C)

  cl-bad-conf* bad [] = []
  cl-bad-conf* bad (l ∷ ls) =
    cl-bad-conf bad l ∷ cl-bad-conf* bad ls


--
-- The graph returned by `cl-bad-conf` may be cleaned by `cl-empty`.
--

-- cl-empty&bad

cl-empty&bad : {C : Set} (bad : C → Bool) (l : LazyGraph C) →
  LazyGraph C

cl-empty&bad bad = cl-empty ∘ cl-bad-conf bad

--
-- Extracting a graph of minimal size (if any).
--

mutual

  -- graph-size

  graph-size  : ∀ {C : Set} (g : Graph C) → ℕ

  graph-size (back c) = 1
  graph-size (forth c gs) = suc (graph-size* gs)

  -- graph-size*

  graph-size* : ∀ {C : Set} (gs : List (Graph C)) → ℕ

  graph-size* [] = 0
  graph-size* (g ∷ gs) = graph-size g + graph-size* gs


-- Now we define a cleaner that produces a lazy graph
-- representing the smallest graph (or the empty set of graphs).

-- We use a trick: ∞ is represented by 0 in (0 , Ø).

-- select-min₂

select-min₂ : ∀ {A : Set} (kx₁ kx₂ : ℕ × A) → ℕ × A

select-min₂ (0 , _) (k₂ , x₂) = k₂ , x₂
select-min₂ (k₁ , x₁) (0 , _) = k₁ , x₁
select-min₂ (k₁ , x₁) (k₂ , x₂) with k₁ ≤? k₂
... | yes _ = k₁ , x₁
... | no  _ = k₂ , x₂

-- select-min

select-min : ∀ {A : Set} (n : A) (kxs : List (ℕ × A)) → ℕ × A

select-min n [] = 0 , n
select-min n (kgs ∷ kgss) = foldl select-min₂ kgs kgss

mutual

  -- cl-min-size

  cl-min-size : ∀ {C : Set} (l : LazyGraph C) → ℕ × LazyGraph C

  cl-min-size Ø =
    0 , Ø
  cl-min-size (stop c) =
    1 , stop c
  cl-min-size (build c lss) with cl-min-size** lss
  ... | 0 , _ = 0 , Ø
  ... | k , ls = suc k , build c [ ls ]

  -- cl-min-size*

  cl-min-size* : ∀ {C : Set} (ls : List (LazyGraph C)) →
    List (ℕ × LazyGraph C)

  cl-min-size* [] = []
  cl-min-size* (l ∷ ls) = cl-min-size l ∷ cl-min-size* ls

  -- cl-min-size**

  cl-min-size** : ∀ {C : Set} (lss : List (List (LazyGraph C))) →
    ℕ × List (LazyGraph C)

  cl-min-size** [] = 0 , []
  cl-min-size** (ls ∷ lss) with cl-min-size-∧ ls | cl-min-size** lss
  ... | kls₁ | kls₂ = select-min₂ kls₁ kls₂

  -- cl-min-size-∧

  cl-min-size-∧ : ∀ {C : Set} (ls : List (LazyGraph C)) →
    ℕ × List (LazyGraph C)

  cl-min-size-∧ [] = 1 , []
  cl-min-size-∧ (l ∷ ls) with cl-min-size l | cl-min-size-∧ ls
  ... | 0 , l′ | _ , ls′ = 0 , l′ ∷ ls′
  ... | _ , l′ | 0 , ls′ = 0 , l′ ∷ ls′
  ... | i , l′ | j , ls′ = i + j , l′ ∷ ls′

{-
--
-- `cl-min-size` is sound:
--
--  Let cl-min-size l ≡ (k , l′). Then
--     ⟪ l′ ⟫ ⊆ ⟪ l ⟫
--     k ≡ graph-size (hd ⟪ l′ ⟫)
--
-- TODO: prove this formally
-}
