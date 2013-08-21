--
-- Infinite trees/graphs
--

module Cographs where

open import Coinduction

open import Data.Nat
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
  Ø     : LazyCograph C
  stop  : (c : C) → LazyCograph C
  build : (c : C) (gsss : ∞(List (List (LazyCograph C)))) → LazyCograph C

-- BigStepMRSC∞

module BigStepMRSC∞ (scWorld : ScWorld) where

  open ScWorld scWorld
  open BigStepMRSC scWorld
    using (lazy-mrsc; lazy-mrsc′)
  
  mutual

    -- build-cograph′

    build-cograph′ : ∀ {n} (h : History n) (c : Conf) →
                       LazyCograph Conf
    build-cograph′ {n} h c with foldable? h c
    ... | yes (i , c⊑hi) = stop c
    ... | no ¬f =
      build c (♯ build-cograph⇉ h c (c ⇉))

    -- build-cograph′⇉

    build-cograph⇉ :
      ∀ {n} (h : History n) (c : Conf) (css : List (List Conf)) →
            List (List (LazyCograph Conf))
    build-cograph⇉ h c [] = []
    build-cograph⇉ h c (cs ∷ css) =
      build-cograph′* (c ∷ h) cs ∷ build-cograph⇉ h c css

    -- build-cograph′*

    build-cograph′* : ∀ {n} (h : History n) (cs : List Conf) →
                        List (LazyCograph Conf)
    build-cograph′* h [] = []
    build-cograph′* h (c ∷ cs) =
      build-cograph′ h c ∷ build-cograph′* h cs

  -- build-cograph

  build-cograph : (c : Conf) → LazyCograph Conf
  build-cograph c = build-cograph′ [] c
  

  mutual

    -- prune-cograph′

    prune-cograph′ : ∀ {n} (h : History n) (b : Bar ↯ h)
                       (gs : LazyCograph Conf) → LazyGraph Conf

    prune-cograph′ h b Ø = Ø
    prune-cograph′ h b (stop c) = stop c
    prune-cograph′ h b (build c gsss) with  ↯? h
    ... | yes w = Ø
    ... | no ¬w with b
    ... | now bz with ¬w bz
    ... | ()
    prune-cograph′ h b (build c gsss) | no ¬w | later bs =
      build c (map (prune-cograph′* (c ∷ h) (bs c)) (♭ gsss))

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

    prune′∘build′-correct {n} h b c with foldable? h c
    ... | yes (i , c⊑hi) =
      refl
    ... | no ¬f with ↯? h
    ... | yes w = refl
    ... | no ¬w with b
    ... | now bz = ⊥-elim (¬w bz)
    ... | later bs =
      cong (build c) (prune-cograph′⇉ h bs c (c ⇉))

    -- prune-cograph′⇉

    prune-cograph′⇉ :
      ∀ {n} (h : History n) (bs : (c : Conf) → Bar ↯ (c ∷ h))
        (c : Conf) (css : List (List Conf)) →
        map (prune-cograph′* (c ∷ h) (bs c)) (build-cograph⇉ h c css) ≡
        map (map (lazy-mrsc′ (c ∷ h) (bs c))) css

    prune-cograph′⇉ h bs c [] = refl
    prune-cograph′⇉ h bs c (cs ∷ css) =
      cong₂ _∷_ (prune′∘build′*-correct (c ∷ h) (bs c) cs)
                (prune-cograph′⇉ h bs c css)

    -- prune′∘build′*-correct

    prune′∘build′*-correct :
      ∀ {n} (h : History n) (b : Bar ↯ h) (cs : List Conf) →
      prune-cograph′* h b (build-cograph′* h cs) ≡ map (lazy-mrsc′ h b) cs

    prune′∘build′*-correct h b [] = refl
    prune′∘build′*-correct h b (c ∷ cs) =
      cong₂ _∷_ (prune′∘build′-correct h b c) (prune′∘build′*-correct h b cs)

  -- prune∘build-correct

  prune∘build-correct :
    prune-cograph ∘ build-cograph ≗ lazy-mrsc

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

  cl-bad-conf∞ bad Ø =
    Ø
  cl-bad-conf∞ bad (stop c) =
    if bad c then Ø else (stop c)
  cl-bad-conf∞ bad (build c gsss) with bad c
  ... | true = Ø
  ... | false = build c (♯ (cl-bad-conf∞** bad (♭ gsss)))

  -- cl-bad-conf∞**

  cl-bad-conf∞** : {C : Set} (bad : C → Bool)
    (gsss : List (List (LazyCograph C))) → List (List (LazyCograph C))

  cl-bad-conf∞** bad [] = []
  cl-bad-conf∞** bad (gss ∷ gsss) =
    cl-bad-conf∞* bad gss ∷ (cl-bad-conf∞** bad gsss)

  -- cl-bad-conf∞*

  cl-bad-conf∞* : {C : Set} (bad : C → Bool)
    (gss : List (LazyCograph C)) → List (LazyCograph C)

  cl-bad-conf∞* bad [] = []
  cl-bad-conf∞* bad (gs ∷ gss) =
    (cl-bad-conf∞ bad gs) ∷ cl-bad-conf∞* bad gss


module ClBadConf∞-Correct (scWorld : ScWorld) where

  open ScWorld scWorld
  open BigStepMRSC∞ scWorld

  mutual

    -- cl-bad-conf∞′-correct

    cl-bad-conf∞′-correct :
      ∀ {n} (h : History n) (b : Bar ↯ h)
      (bad : Conf → Bool) (gs : LazyCograph Conf) →
      cl-bad-conf bad (prune-cograph′ h b gs) ≡
        prune-cograph′ h b (cl-bad-conf∞ bad gs)

    cl-bad-conf∞′-correct h b bad Ø = refl
    cl-bad-conf∞′-correct h b bad (stop c) with bad c
    ... | true = refl
    ... | false = refl

    cl-bad-conf∞′-correct h b bad (build c gsss)
      with ↯? h | inspect ↯? h | bad c | inspect bad c
    ... | yes w | P[ w≡ ] | true | P[ ≡true ] = refl
    ... | yes w | P[ w≡ ] | false | P[ ≡false ] rewrite w≡ = refl
    ... | no ¬w | P[ w≡ ] | true | P[ ≡true ] with b
    ... | now bz = ⊥-elim (¬w bz)
    ... | later bs rewrite ≡true = refl
    cl-bad-conf∞′-correct h b bad (build c gsss)
      | no ¬w | P[ w≡ ] | false | P[ ≡false ] rewrite w≡ with b
    ... | now bz = ⊥-elim (¬w bz)
    ... | later bs rewrite ≡false =
      cong (build c) (cl-bad-conf∞**′-correct (c ∷ h) (bs c) bad (♭ gsss))

    -- cl-bad-conf∞**′-correct

    cl-bad-conf∞**′-correct :
      ∀ {n} (h : History n) (b : Bar ↯ h)
        (bad : Conf → Bool) (gsss : List (List (LazyCograph Conf))) →
      cl-bad-conf** bad (map (prune-cograph′* h b) gsss) ≡
      map (prune-cograph′* h b) (cl-bad-conf∞** bad gsss)

    cl-bad-conf∞**′-correct h b bad [] = refl
    cl-bad-conf∞**′-correct h b bad (gss ∷ gsss) =
      cong₂ _∷_ (cl-bad-conf∞*′-correct h b bad gss)
                (cl-bad-conf∞**′-correct h b bad gsss)

    -- cl-bad-conf∞*′-correct

    cl-bad-conf∞*′-correct :
      ∀ {n} (h : History n) (b : Bar ↯ h)
        (bad : Conf → Bool) (gss : List (LazyCograph Conf)) →
      cl-bad-conf* bad (prune-cograph′* h b gss) ≡
        prune-cograph′* h b (cl-bad-conf∞* bad gss)

    cl-bad-conf∞*′-correct h b bad [] =
      refl
    cl-bad-conf∞*′-correct h b bad (gs ∷ gss) =
      cong₂ _∷_ (cl-bad-conf∞′-correct h b bad gs)
                (cl-bad-conf∞*′-correct h b bad gss)

  --
  -- cl-bad-conf∞-correct
  --

  cl-bad-conf∞-correct : (bad : Conf → Bool) →
    cl-bad-conf bad ∘ prune-cograph ≗
      prune-cograph ∘ cl-bad-conf∞ bad

  cl-bad-conf∞-correct bad gs =
    cl-bad-conf∞′-correct [] bar[] bad gs
