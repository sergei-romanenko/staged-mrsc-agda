--
-- Infinite trees/graphs
--

{-# OPTIONS --copatterns #-}

module Copat.Cographs where

open import Size

open import Data.Nat
open import Data.Bool
  using (Bool; true; false; if_then_else_)
open import Data.List as List
  using (List; []; _∷_; map; _++_; filter; all; gfilter)
open import Data.List.Any as Any
  using (Any; here; there; any; module Membership-≡)
open import Data.Vec as Vec
  using (Vec; []; _∷_; lookup)
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty
open import Data.Maybe
  using (Maybe; nothing; just; decToMaybe)

open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to P[_])

open import Util
open import BarWhistles
open import Graphs
open import BigStepSc

--
-- Lazy cographs of configurations
--

-- A `LazyCograph C` represents a (potentially) infinite set of graphs
-- of configurations (whose type is `Graph C`).
--
-- "Lazy" cographs of configurations will be produced
-- by the "lazy" (staged) version of multi-result
-- supercompilation.

-- LazyCoraph

mutual

  data LazyCograph {i : Size} (C : Set) : Set where
    Ø     : LazyCograph {i} C
    stop  : (c : C) → LazyCograph {i} C
    build : (c : C) (lss : ∞Children {i} C)  → LazyCograph {i} C

  record ∞Children {i : Size} (C : Set) : Set where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → List (List (LazyCograph {j} C))

open ∞Children public

-- Ø∞≡?

Ø∞≡? : {i : Size} {C : Set} (l : LazyCograph {i} C) → Dec (Ø ≡ l)

Ø∞≡? Ø = yes refl
Ø∞≡? (stop c) = no (λ ())
Ø∞≡? (build c lss) = no (λ ())

-- BigStepMRSC∞

module BigStepMRSC∞ (scWorld : ScWorld) where

  open ScWorld scWorld

  mutual

    -- build-cograph′

    build-cograph′ : ∀ {i} (h : History) (c : Conf) → LazyCograph {i} Conf

    build-cograph′ {i} h c with foldable? h c
    ... | yes f = stop c
    ... | no ¬f =
      build c (build-children h c (c ⇉))

    -- build-children

    build-children :
      {i : Size} (h : History) (c : Conf) (css : List (List Conf))  →
        ∞Children {i} Conf

    force (build-children h c css) =
      map (map (build-cograph′ (c ∷ h))) css

  -- build-cograph

  build-cograph : ∀ {i} (c : Conf) → LazyCograph {i} Conf
  build-cograph = build-cograph′ []

  mutual

    -- prune-cograph′

    prune-cograph′ : (h : History) (b : Bar ↯ h) (l : LazyCograph Conf) →
        LazyGraph Conf

    prune-cograph′ h b Ø = Ø
    prune-cograph′ h b (stop c) = stop c
    prune-cograph′ h b (build c lss) with  ↯? h
    ... | yes w = Ø
    prune-cograph′ h (now w) (build c lss) | no ¬w =
      ⊥-elim (¬w w)
    prune-cograph′ h (later bs) (build c lss) | no ¬w =
      build c (map (map (prune-cograph′ (c ∷ h) (bs c))) (force lss))

  -- prune-cograph

  prune-cograph : (l : LazyCograph Conf) → LazyGraph Conf
  prune-cograph = prune-cograph′ [] bar[]

--
-- Now that we have docomposed `lazy-mrsc`
--     lazy-mrsc ≗ prune-cograph ∘ build-cograph
-- we can push some cleaners into prune-cograph.
--
-- Suppose `clean∞` is a cograph cleaner such that
--     clean ∘ prune-cograph ≗ prune-cograph ∘ clean∞
-- then 
--     clean ∘ lazy-mrsc ≗
--       clean ∘ (prune-cograph ∘ build-cograph) ≗
--       (prune-cograph ∘ clean∞) ∘ build-cograph
--       prune-cograph ∘ (clean∞ ∘ build-cograph)
--
-- The good thing is that `build-cograph` and `clean∞` work in a lazy way,
-- generating subtrees by demand. Hence, evaluating
--     ⟪ prune-cograph ∘ (clean∞ (build-cograph c))  ⟫
-- may be less time and space consuming than evaluating
--     ⟪ clean (lazy-mrsc c) ⟫
--

module _ {C : Set} (bad : C → Bool) where

  mutual

    -- cl∞-bad-conf

    cl∞-bad-conf : ∀ {i} (l : LazyCograph {i} C) → LazyCograph {i} C

    cl∞-bad-conf Ø =
      Ø
    cl∞-bad-conf (stop c) =
      if bad c then Ø else (stop c)
    cl∞-bad-conf (build c lss) with bad c
    ... | true = Ø
    ... | false = build c (cl∞-bad-children lss)

    -- cl∞-bad-children

    cl∞-bad-children : ∀ {i} (lss : ∞Children {i} C) → ∞Children {i} C

    force (cl∞-bad-children lss) {j} =
      map (map cl∞-bad-conf) (force lss)

--
-- A cograph can be cleaned to remove some empty alternatives.
--
-- Note that the cleaning is not perfect, because `cl∞-Ø` has to pass
-- the productivity check.
-- So, `build c []` is not (recursively) replaced with `Ø`. as is done
-- by `cl-empty`.
--

module _ {C : Set} where

  mutual

    -- cl∞-Ø

    cl∞-Ø : ∀ {i} (l : LazyCograph {i} C) → LazyCograph {i} C

    cl∞-Ø Ø = Ø
    cl∞-Ø (stop c) = stop c
    cl∞-Ø (build c lss) =
      build c (cl∞-Ø-children lss)

    -- cl∞-Ø-children

    cl∞-Ø-children : ∀ {i} (lss : ∞Children {i} C) → ∞Children {i} C

    force (cl∞-Ø-children lss) {j} =
      map (map cl∞-Ø) (gfilter cl∞-Ø-child (force lss))

    -- cl∞-Ø-child

    cl∞-Ø-child : ∀ {i} (ls : List (LazyCograph {i} C)) →
      Maybe (List (LazyCograph {i} C))

    cl∞-Ø-child ls with any Ø∞≡? ls
    ... | yes Ø∈ls = nothing
    ... | no  Ø∉ls = just ls

-- An optimized version of `prune-cograph`.
-- The difference is that empty subtrees are removed
-- "on the fly".

module BigStepMRSC∞-Ø (scWorld : ScWorld) where

  open ScWorld scWorld

  mutual

    -- pruneØ-cograph′

    pruneØ-cograph′ : (h : History) (b : Bar ↯ h) (l : LazyCograph Conf) →
      LazyGraph Conf

    pruneØ-cograph′ h b Ø = Ø
    pruneØ-cograph′ h b (stop c) = stop c
    pruneØ-cograph′ h b (build c lss) with  ↯? h
    ... | yes w = Ø
    pruneØ-cograph′ h (now w) (build c lss) | no ¬w =
      ⊥-elim (¬w w)
    pruneØ-cograph′ h (later bs) (build c lss) | no ¬w =
      cl-empty-build c (gfilter (pruneØ-cograph* (c ∷ h) (bs c)) (force lss))

    -- pruneØ-cograph*

    pruneØ-cograph* : (h : History) (b : Bar ↯ h)
      (ls : List (LazyCograph Conf)) → Maybe (List (LazyGraph Conf))

    pruneØ-cograph* h b [] = just []
    pruneØ-cograph* h b (l ∷ ls) with pruneØ-cograph′ h b l
    ... | l′ with Ø≡? l′
    ... | yes _ = nothing
    ... | no _ with pruneØ-cograph* h b ls
    ... | nothing = nothing
    ... | just ls′ = just (l′ ∷ ls′)

  -- pruneØ-cograph

  pruneØ-cograph : (l : LazyCograph Conf) → LazyGraph Conf
  pruneØ-cograph = pruneØ-cograph′ [] bar[]
