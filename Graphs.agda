--
-- Graphs of configurations
--

module Graphs where

open import Data.Bool
  using (Bool; true; false; if_then_else_)
open import Data.Nat
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.List as List
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃; ∃₂)
open import Data.Empty
open import Data.Maybe
  using (Maybe; nothing; just)

open import Function
  using (_∘_)

open import Relation.Nullary

open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to P[_])

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

-- A `LazyGraph C n` represents a finite set of graphs
-- of configurations (whose type is `Graph C n`).
--
-- "Lazy" graphs of configurations will be produced
-- by the "lazy" (staged) version of multi-result
-- supercompilation.

-- LazyGraph

data LazyGraph (C : Set) : Set where
  ⁇      : ⊥ → LazyGraph C
  Ø       : LazyGraph C
  alt     : (gs₁ gs₂ : LazyGraph C) → LazyGraph C
  back    : ∀ (c : C) → LazyGraph C
  split   : ∀ (c : C) (gss : List (LazyGraph C)) →
              LazyGraph C
  rebuild : ∀ (c : C) (gss : List (LazyGraph C)) →
              LazyGraph C

-- The semantics of `LazyGraph C n` is formally defined by
-- the function `get-graphs` that generates a list of `Graph C n`
-- from  a `LazyGraph C n`.

mutual

  -- get-graphs

  get-graphs : {C : Set} (gs : LazyGraph C) → List (Graph C)

  get-graphs (⁇ a⊥) =
    ⊥-elim a⊥
  get-graphs Ø =
    []
  get-graphs (alt gs₁ gs₂) =
    get-graphs gs₁ ++ get-graphs gs₂
  get-graphs (back c) =
    [ back c ]
  get-graphs (split c gss) =
    map (split c) (cartesian (get-graphs* gss))
  get-graphs (rebuild c gss) =
    map (rebuild c) (concat (get-graphs* gss))

  -- get-graphs*

  get-graphs* : {C : Set} (gss : List (LazyGraph C)) →
              List (List (Graph C))
  get-graphs* [] = []
  get-graphs* (gs ∷ gss) = get-graphs gs ∷ get-graphs* gss

-- `get-graphs*` has only been introduced to make the termination
-- checker happy. Actually, it is equivalent to `map get-graphs`.

-- get-graphs*-is-map

get-graphs*-is-map : {C : Set} (gss : List (LazyGraph C)) →
  get-graphs* gss ≡ map get-graphs gss
get-graphs*-is-map [] = refl
get-graphs*-is-map (x ∷ gss) =
  cong (_∷_ (get-graphs x)) (get-graphs*-is-map gss)


--
-- Usually, we are not interested in the whole bag `get-graphs gs`.
-- The goal is to find "the best" or "most interesting" graphs.
-- Hence, there should be developed some techniques of extracting
-- useful information from a `LazyGraph C n` without evaluating
-- `get-graphs gs` directly.

-- This can be formulated in the following form.
-- Suppose that a function `select` filters bags of graphs,
-- removing "bad" graphs, so that
--
--     select (get-graphs gs)
--
-- generates the bag of "good" graphs.
-- Let us find a function `extract` such that
--
--     extract gs ≡ select (get-graphs gs)
--
-- In many cases, `extract` may be more efficient (by several orders
-- of magnityde) than the composition `select ∘ get-graphs`.

-- Sometimes, `extract` can be formulated in terms of "cleaners" of
-- lazy graphs. Let `clean` be a function that transforms lazy graphs,
-- such that
--
--     get-graphs (clean gs) ⊆ get-graphs gs
--
-- Then `extract` can be constructed in the following way:
--
--     extract gs = get-graphs (clean gs)
--
-- Theoretically speaking, `clean` is the result of "promoting" `select`:
--
--     select ∘ get-graphs ≡ get-graphs ∘ clean
--
-- The nice property of cleaners is that they are composable:
-- given `cleaner₁` and `cleaner₂`, `cleaner₂ ∘ cleaner₁` is also a cleaner.
--

--
-- Some cleaners
--

--
-- A cleaner that removes subtrees that represent empty sets of graphs.
--

cl-empty′ : {C : Set} (gs : LazyGraph C) →
  Maybe (LazyGraph C)
cl-empty-∨ : {C : Set} (gss : List (LazyGraph C)) →
  List (LazyGraph C)
cl-empty-∧ : {C : Set} (gss : List (LazyGraph C)) →
  Maybe (List (LazyGraph C))

-- cl-empty

cl-empty′ (⁇ a⊥) =
  nothing
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

cl-empty-∨ [] = []
cl-empty-∨ (gs ∷ gss) with cl-empty′ gs | cl-empty-∨ gss
... | nothing | gss′ = gss′
... | just gs′ | gss′ = gs′ ∷ gss′

-- cl-empty-∧

cl-empty-∧ [] = just []
cl-empty-∧ (gs ∷ gss) with cl-empty′ gs
... | nothing = nothing
... | just gs′ with cl-empty-∧ gss
... | nothing = nothing
... | just gss′ = just (gs′ ∷ gss′)

cl-empty : {C : Set} (gs : LazyGraph C) → LazyGraph C

cl-empty gs with cl-empty′ gs
... | nothing = Ø
... | just gs′ = gs′

{-
-- TODO:
--`cl-empty` is correct

-- cl-empty-correct

cl-empty-correct : ∀ {C : Set} {n} (gs : LazyGraph C n) →
  get-graphs (cl-empty gs) ≡ get-graphs gs
-}

--
-- Removing graphs that contain "bad" configurations.
-- Configurations represent states of a computation process.
-- Some of these states may be "bad" with respect to the problem
-- that is to be solved by means of supercompilation.
--
-- The cleaner `cl-bad-config` assumes "badness" to be monotonic,
-- in the sense that a single "bad" configuration spoils the whole
-- graph it appears in.
--
-- The graph returned by `cl-bad-config` may be cleaned by `cl-empty`.
--

cl-bad-config : {C : Set} (bad : C → Bool) (gs : LazyGraph C) →
  LazyGraph C
cl-bad-config* : {C : Set} (bad : C → Bool)
  (gss : List (LazyGraph C)) → List (LazyGraph C)

-- cl-bad-config

cl-bad-config bad (⁇ a⊥) =
  ⁇ a⊥
cl-bad-config bad Ø =
  Ø
cl-bad-config bad (alt gs₁ gs₂) =
  alt (cl-bad-config bad gs₁) (cl-bad-config bad gs₂)
cl-bad-config bad (back c) =
  if bad c then Ø else (back c)
cl-bad-config bad (split c gss) =
  if bad c then Ø else (split c (cl-bad-config* bad gss))
cl-bad-config bad (rebuild c gss) =
  if bad c then Ø else (rebuild c (cl-bad-config* bad gss))

-- cl-bad-config*

cl-bad-config* bad [] = []
cl-bad-config* bad (gs ∷ gss) =
  (cl-bad-config bad gs) ∷ cl-bad-config* bad gss

-- cl-empty-bad

cl-empty-bad : {C : Set} (bad : C → Bool) (gs : LazyGraph C) →
  LazyGraph C

cl-empty-bad bad = cl-empty ∘ cl-bad-config bad

--
-- Extracting a graph of minimal size (if any).
--

-- graph-size

graph-size  : ∀ {C : Set} (g : Graph C) → ℕ
graph-size* : ∀ {C : Set} (g : List (Graph C)) → ℕ

graph-size (back c) = 1
graph-size (split c gs) = suc (graph-size* gs)
graph-size (rebuild c g) = suc (graph-size g)

-- graph-size*

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

select-min : ∀ {C : Set} (kgss : List (ℕ × LazyGraph C)) →
  ℕ × LazyGraph C
select-min [] = 0 , Ø
select-min (kgs ∷ kgss) = foldl select-min₂ kgs kgss

-- cl-min-size

cl-min-size : ∀ {C : Set} (gs : LazyGraph C) → ℕ × LazyGraph C
cl-min-size* : ∀ {C : Set} (gss : List(LazyGraph C)) →
  List (ℕ × LazyGraph C)
cl-min-size-∧ : ∀ {C : Set} (gss : List (LazyGraph C)) →
  ℕ × List (LazyGraph C)

cl-min-size (⁇ a⊥) =
  ⊥-elim a⊥
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

cl-min-size* [] = []
cl-min-size* (gs ∷ gss) = cl-min-size gs ∷ cl-min-size* gss

-- cl-min-size-∧

cl-min-size-∧ [] = 1 , []
cl-min-size-∧ (gs ∷ gss) with cl-min-size gs | cl-min-size-∧ gss
... | 0 , gs′ | _ , gss′ = 0 , gs′ ∷ gss′
... | _ , gs′ | 0 , gss′ = 0 , gs′ ∷ gss′
... | i , gs′ | j , gss′ = i + j , gs′ ∷ gss′

--
-- `cl-min-size` is sound:
--
--  Let cl-min-size gs ≡ (k , gs′) where k ≡ 0. Then
--     get-graphs gs′ ⊆ get-graphs gs
--     k ≡ graph-size (hd (get-graphs gs′))
--
-- TODO: prove this formally