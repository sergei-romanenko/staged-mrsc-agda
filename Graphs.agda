--
-- Graphs of configurations
--

module Graphs where

open import Algebra
  using (module Monoid)
open import Data.Bool
  using (Bool; true; false; if_then_else_; not)
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
-- * Split-nodes are produced by decomposing a configuration into
--   a number of other configurations (e.g. by driving or taking apart
--   a let-expression).
-- * Rebuild nodes are produced by rewriting a configuration by another
--   one (e.g. by generalization, introducing a let-expression or
--   applying a lemma during two-level supercompilation).

-- Graph

data Graph (C : Set) : Set where
  back    : ∀ (c : C) → Graph C
  split   : ∀ (c : C) (gs : List (Graph C)) → Graph C
  rebuild : ∀ (c : C) (g : Graph C) → Graph C

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
  Ø       : LazyGraph C
  alt     : (gs₁ gs₂ : LazyGraph C) → LazyGraph C
  back    : ∀ (c : C) → LazyGraph C
  split   : ∀ (c : C) (gss : List (LazyGraph C)) →
              LazyGraph C
  rebuild : ∀ (c : C) (gss : List (LazyGraph C)) →
              LazyGraph C

-- The semantics of `LazyGraph C` is formally defined by
-- the function `⟪_⟫` that generates a list of `Graph C n`
-- from  a `LazyGraph C`.

mutual

  -- ⟪_⟫

  ⟪_⟫ : {C : Set} (gs : LazyGraph C) → List (Graph C)

  ⟪ Ø ⟫ =
    []
  ⟪ alt gs₁ gs₂ ⟫ =
    ⟪ gs₁ ⟫ ++ ⟪ gs₂ ⟫
  ⟪ back c ⟫ =
    [ back c ]
  ⟪ split c gss ⟫ =
    map (split c) (cartesian ⟪ gss ⟫*)
  ⟪ rebuild c gss ⟫ =
    map (rebuild c) (concat ⟪ gss ⟫*)

  -- ⟪_⟫*

  ⟪_⟫* : {C : Set} (gss : List (LazyGraph C)) →
              List (List (Graph C))
  ⟪ [] ⟫* = []
  ⟪ gs ∷ gss ⟫* = ⟪ gs ⟫ ∷ ⟪ gss ⟫*

-- `⟪_⟫*` has only been introduced to make the termination
-- checker happy. Actually, it is equivalent to `map ⟪_⟫`.

-- ⟪⟫*-is-map

⟪⟫*-is-map : {C : Set} (gss : List (LazyGraph C)) →
  ⟪ gss ⟫* ≡ map ⟪_⟫ gss

⟪⟫*-is-map [] = refl
⟪⟫*-is-map (gs ∷ gss) =
  cong (_∷_ ⟪ gs ⟫) (⟪⟫*-is-map gss)


--
-- Usually, we are not interested in the whole bag `⟪ gs ⟫`.
-- The goal is to find "the best" or "most interesting" graphs.
-- Hence, there should be developed some techniques of extracting
-- useful information from a `LazyGraph C n` without evaluating
-- `⟪ gs ⟫` directly.

-- This can be formulated in the following form.
-- Suppose that a function `select` filters bags of graphs,
-- removing "bad" graphs, so that
--
--     select ⟪ gs ⟫
--
-- generates the bag of "good" graphs.
-- Let us find a function `extract` such that
--
--     extract gs ≡ select ⟪ gs ⟫
--
-- In many cases, `extract` may be more efficient (by several orders
-- of magnityde) than the composition `select ∘ ⟪_⟫`.

-- Sometimes, `extract` can be formulated in terms of "cleaners" of
-- lazy graphs. Let `clean` be a function that transforms lazy graphs,
-- such that
--
--     ⟪ clean gs ⟫ ⊆ ⟪ gs ⟫
--
-- Then `extract` can be constructed in the following way:
--
--     extract gs ≡ ⟪ clean gs ⟫
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
  bad-graph bad (split c gs) with bad c
  ... | true = true
  ... | false = bad-graph* bad gs
  bad-graph bad (rebuild c g) with bad c
  ... | true = true
  ... | false = bad-graph bad g

  -- bad-graph*

  bad-graph* : {C : Set} (bad : C → Bool) (gs : List (Graph C)) → Bool

  bad-graph* bad [] = false
  bad-graph* bad (g ∷ gs) with bad-graph bad g
  ... | true = true
  ... | false = bad-graph* bad gs

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

  -- cl-empty′

  cl-empty′ : {C : Set} (gs : LazyGraph C) →
    Maybe (LazyGraph C)

  cl-empty′ Ø =
    nothing
  cl-empty′ (alt gs₁ gs₂) with cl-empty′ gs₁ | cl-empty′ gs₂
  ... | nothing | gs₂′ = gs₂′
  ... | gs₁′ | nothing = gs₁′
  ... | just gs₁′ | just gs₂′ = just (alt gs₁′ gs₂′)
  cl-empty′ (back c) =
    just (back c)
  cl-empty′ (split c gss) with cl-empty-∧ gss
  ... | nothing = nothing
  ... | just gss′ = just (split c gss′)
  cl-empty′ (rebuild c gss) with cl-empty-∨ gss
  ... | [] = nothing
  ... | gss′ = just (rebuild c gss′)

  -- cl-empty-∨

  cl-empty-∨ : {C : Set} (gss : List (LazyGraph C)) →
    List (LazyGraph C)

  cl-empty-∨ [] = []
  cl-empty-∨ (gs ∷ gss) with cl-empty′ gs | cl-empty-∨ gss
  ... | nothing | gss′ = gss′
  ... | just gs′ | gss′ = gs′ ∷ gss′

  -- cl-empty-∧

  cl-empty-∧ : {C : Set} (gss : List (LazyGraph C)) →
    Maybe (List (LazyGraph C))

  cl-empty-∧ [] = just []
  cl-empty-∧ (gs ∷ gss) with cl-empty′ gs
  ... | nothing = nothing
  ... | just gs′ with cl-empty-∧ gss
  ... | nothing = nothing
  ... | just gss′ = just (gs′ ∷ gss′)

  -- cl-empty

  cl-empty : {C : Set} (gs : LazyGraph C) → LazyGraph C

  cl-empty gs with cl-empty′ gs
  ... | nothing = Ø
  ... | just gs′ = gs′


--
-- Removing graphs that contain "bad" configurations.
-- The cleaner `cl-bad-conf` corresponds to the filter `fl-bad-conf`.
-- `cl-bad-conf` exploits the fact that "badness" to be monotonic,
-- in the sense that a single "bad" configuration spoils the whole
-- graph.

mutual

  -- cl-bad-conf

  cl-bad-conf : {C : Set} (bad : C → Bool) (gs : LazyGraph C) →
    LazyGraph C

  cl-bad-conf bad Ø =
    Ø
  cl-bad-conf bad (alt gs₁ gs₂) =
    alt (cl-bad-conf bad gs₁) (cl-bad-conf bad gs₂)
  cl-bad-conf bad (back c) =
    if bad c then Ø else (back c)
  cl-bad-conf bad (split c gss) =
    if bad c then Ø else (split c (cl-bad-conf* bad gss))
  cl-bad-conf bad (rebuild c gss) =
    if bad c then Ø else (rebuild c (cl-bad-conf* bad gss))

  -- cl-bad-conf*

  cl-bad-conf* : {C : Set} (bad : C → Bool)
    (gss : List (LazyGraph C)) → List (LazyGraph C)

  cl-bad-conf* bad [] = []
  cl-bad-conf* bad (gs ∷ gss) =
    cl-bad-conf bad gs ∷ cl-bad-conf* bad gss


--
-- The graph returned by `cl-bad-conf` may be cleaned by `cl-empty`.
--

-- cl-empty&bad

cl-empty&bad : {C : Set} (bad : C → Bool) (gs : LazyGraph C) →
  LazyGraph C

cl-empty&bad bad = cl-empty ∘ cl-bad-conf bad

--
-- Extracting a graph of minimal size (if any).
--

mutual

  -- graph-size

  graph-size  : ∀ {C : Set} (g : Graph C) → ℕ

  graph-size (back c) = 1
  graph-size (split c gs) = suc (graph-size* gs)
  graph-size (rebuild c g) = suc (graph-size g)

  -- graph-size*

  graph-size* : ∀ {C : Set} (g : List (Graph C)) → ℕ

  graph-size* [] = 0
  graph-size* (g ∷ gs) = graph-size g + graph-size* gs


-- Now we define a cleaner that produces a lazy graph
-- representing the smallest graph (or the empty set of graphs).

-- We use a trick: ∞ is represented by 0 in (0 , Ø).

-- select-min₂

select-min₂ : ∀ {C : Set} (kgs₁ kgs₂ : ℕ × LazyGraph C) →
  ℕ × LazyGraph C

select-min₂ (_ , Ø) (k₂ , gs₂) = k₂ , gs₂
select-min₂ (k₁ , gs₁) (_ , Ø) = k₁ , gs₁
select-min₂ (k₁ , gs₁) (k₂ , gs₂) with k₁ ≤? k₂
... | yes _ = k₁ , gs₁
... | no  _ = k₂ , gs₂

-- select-min

select-min : ∀ {C : Set} (kgss : List (ℕ × LazyGraph C)) →
  ℕ × LazyGraph C

select-min [] = 0 , Ø
select-min (kgs ∷ kgss) = foldl select-min₂ kgs kgss

mutual

  -- cl-min-size

  cl-min-size : ∀ {C : Set} (gs : LazyGraph C) → ℕ × LazyGraph C

  cl-min-size Ø =
    0 , Ø -- should be ∞ , Ø
  cl-min-size (alt gs₁ gs₂) =
    select-min₂ (cl-min-size gs₁) (cl-min-size gs₂)
  cl-min-size (back c) =
    1 , back c
  cl-min-size (split c gss) with cl-min-size-∧ gss
  ... | 0 , _ = 0 , Ø
  ... | k , gs = k , split c gs
  cl-min-size (rebuild c gss) with select-min (cl-min-size* gss)
  ... | _ , Ø = 0 , Ø
  ... | k , gs = suc k , rebuild c [ gs ]

  -- cl-min-size*

  cl-min-size* : ∀ {C : Set} (gss : List(LazyGraph C)) →
    List (ℕ × LazyGraph C)

  cl-min-size* [] = []
  cl-min-size* (gs ∷ gss) = cl-min-size gs ∷ cl-min-size* gss

  -- cl-min-size-∧

  cl-min-size-∧ : ∀ {C : Set} (gss : List (LazyGraph C)) →
    ℕ × List (LazyGraph C)

  cl-min-size-∧ [] = 1 , []
  cl-min-size-∧ (gs ∷ gss) with cl-min-size gs | cl-min-size-∧ gss
  ... | 0 , gs′ | _ , gss′ = 0 , gs′ ∷ gss′
  ... | _ , gs′ | 0 , gss′ = 0 , gs′ ∷ gss′
  ... | i , gs′ | j , gss′ = i + j , gs′ ∷ gss′

{-
--
-- `cl-min-size` is sound:
--
--  Let cl-min-size gs ≡ (k , gs′). Then
--     ⟪ gs′ ⟫ ⊆ ⟪ gs ⟫
--     k ≡ graph-size (hd ⟪ gs′ ⟫)
--
-- TODO: prove this formally
-}
