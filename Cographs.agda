--
-- Infinite trees/graphs
--

module Cographs where

open import Coinduction

open import Data.Bool
  using (Bool; true; false; if_then_else_)
open import Data.List as List
open import Data.Vec as Vec
  using (Vec; []; _∷_; lookup)
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty

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

-- LazyGraph

data LazyCograph (C : Set) : Set where
  ⁇      : ⊥ → LazyCograph C
  Ø       : LazyCograph C
  alt     : (gs₁ gs₂ : LazyCograph C) → LazyCograph C
  back    : ∀ (c : C) → LazyCograph C
  split   : ∀ (c : C) (gss : ∞(List (LazyCograph C))) →
              LazyCograph C
  rebuild : ∀ (c : C) (gss : ∞(List (LazyCograph C))) →
              LazyCograph C

-- BigStepMRSC

module ∞BigStepMRSC (scWorld : ScWorld) where

  open ScWorld scWorld
  open BigStepMRSC scWorld
    using (lazy-mrsc; lazy-mrsc′)
  
  mutual

    -- build-cograph′

    build-cograph′ : ∀ {n} (h : History n) (c : Conf) →
                       LazyCograph Conf
    build-cograph′ {n} h c with foldable? h c
    ... | yes (i , c⊑hi) = back c
    ... | no ¬f = alt split! rebuild!
      where

      split!   = split c (♯ build-cograph′* (c ∷ h) (c ⇉))
      rebuild! = rebuild c (♯ build-cograph′* (c ∷ h) (c ↷))

    -- build-cograph′*

    build-cograph′* : ∀ {n} (h : History n) (cs : List Conf) →
                        List (LazyCograph Conf)
    build-cograph′* h [] = []
    build-cograph′* h (c ∷ cs) =
      build-cograph′ h c ∷ build-cograph′* h cs

  -- build-cograph

  build-cograph : (c : Conf) → LazyCograph Conf
  build-cograph c = build-cograph′ [] c
  
  -- alt-Ø

  alt-Ø : (gs₁ gs₂ : LazyGraph Conf) → LazyGraph Conf

  alt-Ø Ø gs₂ = gs₂
  alt-Ø gs₁ Ø = gs₁
  alt-Ø gs₁ gs₂ = alt gs₁ gs₂

  mutual

    -- prune-cograph′

    prune-cograph′ : ∀ {n} (h : History n) (b : Bar ↯ h)
                       (gs : LazyCograph Conf) → LazyGraph Conf

    prune-cograph′ h b (⁇ a⊥) = ⁇ a⊥
    prune-cograph′ h b Ø = Ø
    prune-cograph′ h b (alt gs₁ gs₂) =
      alt-Ø (prune-cograph′ h b gs₁) (prune-cograph′ h b gs₂)
    prune-cograph′ h b (back c) = back c
    prune-cograph′ h b (split c gss) with ↯? h
    ... | yes w = Ø
    ... | no ¬w with b
    ... | now bz = ⁇ (¬w bz)
    ... | later bs = split c (prune-cograph′* (c ∷ h) (bs c) (♭ gss))
    prune-cograph′ h b (rebuild c gss) with ↯? h
    ... | yes w = Ø
    ... | no ¬w with b
    ... | now bz = ⁇ (¬w bz)
    ... | later bs = rebuild c (prune-cograph′* (c ∷ h) (bs c) (♭ gss))

    -- prune-cograph′*

    prune-cograph′* : ∀ {n} (h : History n) (b : Bar ↯ h)
                       (gss : List (LazyCograph Conf)) → List (LazyGraph Conf)
    prune-cograph′* h b [] = []
    prune-cograph′* h b (gs ∷ gss) =
      prune-cograph′ h b gs ∷ (prune-cograph′* h b gss)

  -- prune-cograph

  prune-cograph : (gs : LazyCograph Conf) → LazyGraph Conf
  prune-cograph gs = prune-cograph′ [] bar[] gs

  mutual

    -- prune′∘build′-correct

    prune′∘build′-correct :
      ∀ {n} (h : History n) (b : Bar ↯ h) (c : Conf) →
      prune-cograph′ h b (build-cograph′ h c) ≡ lazy-mrsc′ h b c 

    prune′∘build′-correct h b c with foldable? h c
    ... | yes (i , c⊑hi) =
      refl
    ... | no ¬f with ↯? h
    ... | yes w = refl
    ... | no ¬w with b
    ... | now bz = ⊥-elim (¬w bz)
    ... | later bs =
      cong₂ alt (cong (split c)
                      (prune′∘build′*-correct (c ∷ h) (bs c) (c ⇉)))
                (cong (rebuild c)
                      (prune′∘build′*-correct (c ∷ h) (bs c) (c ↷)))

    -- prune′∘build′*-correct

    prune′∘build′*-correct :
      ∀ {n} (h : History n) (b : Bar ↯ h) (cs : List Conf) →
      prune-cograph′* h b (build-cograph′* h cs) ≡ map (lazy-mrsc′ h b) cs

    prune′∘build′*-correct h b [] = refl
    prune′∘build′*-correct h b (c ∷ cs) =
      cong₂ _∷_ (prune′∘build′-correct h b c) (prune′∘build′*-correct h b cs)

  -- prune∘build-correct

  prune∘build-correct :
    (c : Conf) →
    prune-cograph (build-cograph c) ≡ lazy-mrsc c 

  prune∘build-correct c = prune′∘build′-correct [] bar[] c

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

mutual

  -- cl-bad-conf∞

  cl-bad-conf∞ : {C : Set} (bad : C → Bool) (gs : LazyCograph C) →
    LazyCograph C

  cl-bad-conf∞ bad (⁇ a⊥) =
    ⁇ a⊥
  cl-bad-conf∞ bad Ø =
    Ø
  cl-bad-conf∞ bad (alt gs₁ gs₂) =
    alt (cl-bad-conf∞ bad gs₁) (cl-bad-conf∞ bad gs₂)
  cl-bad-conf∞ bad (back c) =
    if bad c then Ø else (back c)
  cl-bad-conf∞ bad (split c gss) with bad c
  ... | true = Ø
  ... | false = split c (♯ (cl-bad-conf∞* bad (♭ gss)))
  cl-bad-conf∞ bad (rebuild c gss) with bad c
  ... | true = Ø
  ... | false = rebuild c (♯ cl-bad-conf∞* bad (♭ gss))

  -- cl-bad-conf∞*

  cl-bad-conf∞* : {C : Set} (bad : C → Bool)
    (gss : List (LazyCograph C)) → List (LazyCograph C)

  cl-bad-conf∞* bad [] = []
  cl-bad-conf∞* bad (gs ∷ gss) =
    (cl-bad-conf∞ bad gs) ∷ cl-bad-conf∞* bad gss


{-
module ClBadConf∞-Correct (scWorld : ScWorld) where

  open ScWorld scWorld
  open ∞BigStepMRSC scWorld

  -- cl-alt-Ø

  cl-alt-Ø :
    (bad : Conf → Bool) (gs₁ gs₂ : LazyGraph Conf) →
    cl-bad-conf bad (alt-Ø gs₁ gs₂) ≡
      alt-Ø (cl-bad-conf bad gs₁) (cl-bad-conf bad gs₂)

  cl-alt-Ø bad gs₁ gs₂ with cl-bad-conf bad gs₁ | cl-bad-conf bad gs₂
  cl-alt-Ø bad gs₁ gs₂ | r₁ | r₂ = {!!}

  mutual

    -- cl-bad-conf∞′-correct

    cl-bad-conf∞′-correct :
      ∀ {n} (h : History n) (b : Bar ↯ h)
      (bad : Conf → Bool) (gs : LazyCograph Conf) →
      cl-bad-conf bad (prune-cograph′ h b gs) ≡
        prune-cograph′ h b (cl-bad-conf∞ bad gs)

    cl-bad-conf∞′-correct h b bad (⁇ a⊥) = refl
    cl-bad-conf∞′-correct h b bad Ø = refl
    cl-bad-conf∞′-correct h b bad (alt gs₁ gs₂)
      rewrite P.sym $ cl-bad-conf∞′-correct h b bad gs₁
            | P.sym $ cl-bad-conf∞′-correct h b bad gs₂
      = {!!}
    cl-bad-conf∞′-correct h b bad (back c) with bad c
    ... | true = refl
    ... | false = refl
    cl-bad-conf∞′-correct h b bad (split c gss) = {!!}
    cl-bad-conf∞′-correct h b bad (rebuild c gss) = {!!}

  -- cl-bad-conf∞-correct

  cl-bad-conf∞-correct :
    (bad : Conf → Bool) (gs : LazyCograph Conf) →
    cl-bad-conf bad (prune-cograph gs) ≡
      prune-cograph (cl-bad-conf∞ bad gs)

  cl-bad-conf∞-correct bad gs =
    cl-bad-conf∞′-correct [] bar[] bad gs
-}