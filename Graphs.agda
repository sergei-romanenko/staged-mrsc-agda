--
-- Graphs of configurations
--

module Graphs where

open import Data.Nat
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.List as List
open import Data.Empty

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
  nil     : ∀ {n} → LazyGraph C n
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

  get-graphs (↯ ⊥) =
    ⊥-elim ⊥
  get-graphs nil =
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

get-graphs*-is-map : ∀ {C : Set} {n} (gss : List (LazyGraph C n)) →
  get-graphs* gss ≡ map get-graphs gss
get-graphs*-is-map [] = refl
get-graphs*-is-map (x ∷ gss) =
  cong (_∷_ (get-graphs x)) (get-graphs*-is-map gss)

