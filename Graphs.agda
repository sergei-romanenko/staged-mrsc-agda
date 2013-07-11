--
-- Graphs of configurations
--

module Graphs where

open import Data.Nat
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.List as List
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃; ∃₂)
open import Data.Empty
open import Data.Maybe
  using (Maybe; nothing; just)

open import Relation.Nullary

open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to [_]ⁱ)

open import Util

--
-- Graphs of configurations
--

-- A `Graph C n` is supposed to represent a residual program.
-- Technically, a `Graph C n` is a tree,
-- with `back` nodes being references to parent nodes.
-- A back reference, in a sense, is a `De Bruijn index`.
-- Typing rules ensure that back references cannot be
-- "out of range".
-- 
-- A graph's nodes contain configurations. Here we abstract away
-- from the concrete structure of configurations.
-- In this model the arrows in the graph carry no information,
-- because, this information can be kept in nodes.
-- (Hence, this information is supposed to be encoded inside
-- "configurations".)
-- 
-- back-nodes are produced by folding,
-- case-nodes represent the results of driving,
-- rebuild nodes are produced by generalization and/or decomposition.

-- Graph

data Graph (C : Set) : (n : ℕ) → Set where
  back    : ∀ {n} (c : C) (b : Fin n) → Graph C n
  case    : ∀ {n} (c : C) (gs : List (Graph C (suc n))) → Graph C n
  rebuild : ∀ {n} (c : C) (g : Graph C (suc n)) → Graph C n

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

data LazyGraph (C : Set) : (n : ℕ) → Set where
  ↯       : ∀ {n} → ⊥ → LazyGraph C n
  Ø       : ∀ {n} → LazyGraph C n
  alt     : ∀ {n} (gs₁ gs₂ : LazyGraph C n) → LazyGraph C n
  back    : ∀ {n} (c : C) (b : Fin n) → LazyGraph C n
  case    : ∀ {n} (c : C) (gss : List (LazyGraph C (suc n))) →
              LazyGraph C n
  rebuild : ∀ {n} (c : C) (gss : List (LazyGraph C (suc n))) →
              LazyGraph C n

-- The semantics of `LazyGraph C n` is formally defined by
-- the function `get-graphs` that generates a list of `Graph C n`
-- from  a `LazyGraph C n`.

mutual

  -- get-graphs

  get-graphs : ∀ {C : Set} {n} (gs : LazyGraph C n) → List (Graph C n)

  get-graphs (↯ a-⊥) =
    ⊥-elim a-⊥
  get-graphs Ø =
    []
  get-graphs (alt gs₁ gs₂) =
    get-graphs gs₁ ++ get-graphs gs₂
  get-graphs (back c b) =
    [ back c b ]
  get-graphs (case c gss) =
    map (case c) (cartesian (get-graphs* gss))
  get-graphs (rebuild c gss) =
    map (rebuild c) (concat (get-graphs* gss))

  -- get-graphs*

  get-graphs* : ∀ {C : Set} {n} (gss : List (LazyGraph C n)) →
              List (List (Graph C n))
  get-graphs* [] = []
  get-graphs* (gs ∷ gss) = get-graphs gs ∷ get-graphs* gss

-- `get-graphs*` has only been introduced to make the termination
-- checker happy. Actually, it is equivalent to `map get-graphs`.

-- get-graphs*-is-map

get-graphs*-is-map : ∀ {C : Set} {n} (gss : List (LazyGraph C n)) →
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

-- Extracting a graph of minimal size (if any).

-- graph-size

graph-size  : ∀ {C : Set} {n} (g : Graph C n) → ℕ
graph-size* : ∀ {C : Set} {n} (g : List (Graph C n)) → ℕ

graph-size (back c b) = 1
graph-size (case c gs) = suc (graph-size* gs)
graph-size (rebuild c g) = suc (graph-size g)

-- graph-size*

graph-size* [] = 0
graph-size* (g ∷ gs) = graph-size g + graph-size* gs


-- Now we define a cleaner that produces a lazy graph
-- representing the smallest graph (or the empty set of graphs).

-- We use a trick: ∞ is represented by 0 in (0 , Ø).

-- select-min₂

select-min₂ : ∀ {C : Set} {n} (kgs₁ kgs₂ : ℕ × LazyGraph C n) →
  ℕ × LazyGraph C n

select-min₂ (_ , Ø) (k₂ , gs₂) = k₂ , gs₂
select-min₂ (k₁ , gs₁) (_ , Ø) = k₁ , gs₁
select-min₂ (k₁ , gs₁) (k₂ , gs₂) with k₁ ≤? k₂
... | yes _ = k₁ , gs₁
... | no  _ = k₂ , gs₂

select-min : ∀ {C : Set} {n} (kgss : List (ℕ × LazyGraph C n)) →
  ℕ × LazyGraph C n
select-min [] = 0 , Ø
select-min (kgs ∷ kgss) = foldl select-min₂ kgs kgss

-- cl-min-size

cl-min-size : ∀ {C : Set} {n} (gs : LazyGraph C n) → ℕ × LazyGraph C n
cl-min-size* : ∀ {C : Set} {n} (gss : List(LazyGraph C n)) →
  List (ℕ × LazyGraph C n)
cl-min-size-∧ : ∀ {C : Set} {n} (gss : List (LazyGraph C n)) →
  ℕ × List (LazyGraph C n)

cl-min-size (↯ a-⊥) =
  ⊥-elim a-⊥
cl-min-size Ø =
  0 , Ø -- should be ∞ , Ø
cl-min-size (alt gs₁ gs₂) =
  select-min₂ (cl-min-size gs₁) (cl-min-size gs₂)
cl-min-size (back c b) =
  1 , back c b
cl-min-size (case c gss) with cl-min-size-∧ gss
... | 0 , _ = 0 , Ø
... | k , gs = k , case c gs
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