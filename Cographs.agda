--
-- Infinite trees/graphs
--

module Cographs where

open import Coinduction

open import Data.Nat
open import Data.Bool
  using (Bool; true; false; if_then_else_)
open import Data.List as List
  using (List; []; _∷_; map; _++_; filter; all)
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
  using (Maybe; nothing; just)

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

data LazyCograph (C : Set) : Set where
  Ø     : LazyCograph C
  stop  : (c : C) → LazyCograph C
  build : (c : C) (lss : ∞(List (List (LazyCograph C)))) → LazyCograph C

-- Ø∞≡?

Ø∞≡? : {C : Set} (l : LazyCograph C) → Dec (Ø ≡ l)

Ø∞≡? Ø = yes refl
Ø∞≡? (stop c) = no (λ ())
Ø∞≡? (build c lss) = no (λ ())


-- BigStepMRSC∞

module BigStepMRSC∞ (scWorld : ScWorld) where

  open ScWorld scWorld
  open BigStepMRSC scWorld
    using (lazy-mrsc; lazy-mrsc′)
  
  mutual

    -- build-cograph′

    build-cograph′ : (h : History) (c : Conf) → LazyCograph Conf

    build-cograph′ h c with foldable? h c
    ... | yes f = stop c
    ... | no ¬f =
      build c (♯ build-cograph⇉ h c (c ⇉))

    -- build-cograph⇉

    build-cograph⇉ : (h : History) (c : Conf) (css : List (List Conf)) →
      List (List (LazyCograph Conf))

    build-cograph⇉ h c [] = []
    build-cograph⇉ h c (cs ∷ css) =
      build-cograph* (c ∷ h) cs ∷ build-cograph⇉ h c css

    -- build-cograph*

    build-cograph* : (h : History) (cs : List Conf) →
      List (LazyCograph Conf)

    build-cograph* h [] = []
    build-cograph* h (c ∷ cs) =
      build-cograph′ h c ∷ build-cograph* h cs

  -- build-cograph

  build-cograph : (c : Conf) → LazyCograph Conf
  build-cograph c = build-cograph′ [] c
  

  mutual

    -- prune-cograph′

    prune-cograph′ : (h : History) (b : Bar ↯ h) (l : LazyCograph Conf) →
      LazyGraph Conf

    prune-cograph′ h b Ø = Ø
    prune-cograph′ h b (stop c) = stop c
    prune-cograph′ h b (build c lss) with  ↯? h
    ... | yes w = Ø
    ... | no ¬w with b
    ... | now bz with ¬w bz
    ... | ()
    prune-cograph′ h b (build c lss) | no ¬w | later bs =
      build c (map (prune-cograph* (c ∷ h) (bs c)) (♭ lss))

    -- prune-cograph*

    prune-cograph* : (h : History) (b : Bar ↯ h)
      (ls : List (LazyCograph Conf)) → List (LazyGraph Conf)

    prune-cograph* h b [] = []
    prune-cograph* h b (l ∷ ls) =
      prune-cograph′ h b l ∷ (prune-cograph* h b ls)

  -- prune-cograph

  prune-cograph : (l : LazyCograph Conf) → LazyGraph Conf
  prune-cograph l = prune-cograph′ [] bar[] l

  mutual

    -- prune′∘build′-correct

    prune′∘build′-correct :
      (h : History) (b : Bar ↯ h) (c : Conf) →
      prune-cograph′ h b (build-cograph′ h c) ≡ lazy-mrsc′ h b c 

    prune′∘build′-correct h b c with foldable? h c
    ... | yes f =
      refl
    ... | no ¬f with ↯? h
    ... | yes w = refl
    ... | no ¬w with b
    ... | now bz = ⊥-elim (¬w bz)
    ... | later bs =
      cong (build c) (prune-cograph′⇉ h bs c (c ⇉))

    -- prune-cograph′⇉

    prune-cograph′⇉ :
      (h : History) (bs : (c : Conf) → Bar ↯ (c ∷ h))
      (c : Conf) (css : List (List Conf)) →
        map (prune-cograph* (c ∷ h) (bs c)) (build-cograph⇉ h c css) ≡
        map (map (lazy-mrsc′ (c ∷ h) (bs c))) css

    prune-cograph′⇉ h bs c [] = refl
    prune-cograph′⇉ h bs c (cs ∷ css) =
      cong₂ _∷_ (prune′∘build*-correct (c ∷ h) (bs c) cs)
                (prune-cograph′⇉ h bs c css)

    -- prune′∘build*-correct

    prune′∘build*-correct :
      (h : History) (b : Bar ↯ h) (cs : List Conf) →
      prune-cograph* h b (build-cograph* h cs) ≡ map (lazy-mrsc′ h b) cs

    prune′∘build*-correct h b [] = refl
    prune′∘build*-correct h b (c ∷ cs) =
      cong₂ _∷_ (prune′∘build′-correct h b c) (prune′∘build*-correct h b cs)

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

  -- cl∞-bad-conf

  cl∞-bad-conf : {C : Set} (bad : C → Bool) (l : LazyCograph C) →
    LazyCograph C

  cl∞-bad-conf bad Ø =
    Ø
  cl∞-bad-conf bad (stop c) =
    if bad c then Ø else (stop c)
  cl∞-bad-conf bad (build c lss) with bad c
  ... | true = Ø
  ... | false = build c (♯ (cl∞-bad-conf⇉ bad (♭ lss)))

  -- cl∞-bad-conf⇉

  cl∞-bad-conf⇉ : {C : Set} (bad : C → Bool)
    (lss : List (List (LazyCograph C))) → List (List (LazyCograph C))

  cl∞-bad-conf⇉ bad [] = []
  cl∞-bad-conf⇉ bad (ls ∷ lss) =
    cl∞-bad-conf* bad ls ∷ cl∞-bad-conf⇉ bad lss

  -- cl∞-bad-conf*

  cl∞-bad-conf* : {C : Set} (bad : C → Bool)
    (ls : List (LazyCograph C)) → List (LazyCograph C)

  cl∞-bad-conf* bad [] = []
  cl∞-bad-conf* bad (l ∷ ls) =
    cl∞-bad-conf bad l ∷ cl∞-bad-conf* bad ls


module ClBadConf∞-Correct (scWorld : ScWorld) where

  open ScWorld scWorld
  open BigStepMRSC∞ scWorld

  mutual

    -- cl∞-bad-conf′-correct

    cl∞-bad-conf′-correct :
      (h : History) (b : Bar ↯ h)
      (bad : Conf → Bool) (l : LazyCograph Conf) →
      cl-bad-conf bad (prune-cograph′ h b l) ≡
        prune-cograph′ h b (cl∞-bad-conf bad l)

    cl∞-bad-conf′-correct h b bad Ø = refl
    cl∞-bad-conf′-correct h b bad (stop c) with bad c
    ... | true = refl
    ... | false = refl

    cl∞-bad-conf′-correct h b bad (build c lss)
      with ↯? h | inspect ↯? h | bad c | inspect bad c
    ... | yes w | P[ w≡ ] | true | P[ ≡true ] = refl
    ... | yes w | P[ w≡ ] | false | P[ ≡false ] rewrite w≡ = refl
    ... | no ¬w | P[ w≡ ] | true | P[ ≡true ] with b
    ... | now bz = ⊥-elim (¬w bz)
    ... | later bs rewrite ≡true = refl
    cl∞-bad-conf′-correct h b bad (build c lss)
      | no ¬w | P[ w≡ ] | false | P[ ≡false ] rewrite w≡ with b
    ... | now bz = ⊥-elim (¬w bz)
    ... | later bs rewrite ≡false =
      cong (build c) (cl∞-bad-conf⇉-correct (c ∷ h) (bs c) bad (♭ lss))

    -- cl∞-bad-conf⇉-correct

    cl∞-bad-conf⇉-correct :
      (h : History) (b : Bar ↯ h)
        (bad : Conf → Bool) (lss : List (List (LazyCograph Conf))) →
      cl-bad-conf⇉ bad (map (prune-cograph* h b) lss) ≡
      map (prune-cograph* h b) (cl∞-bad-conf⇉ bad lss)

    cl∞-bad-conf⇉-correct h b bad [] = refl
    cl∞-bad-conf⇉-correct h b bad (ls ∷ lss) =
      cong₂ _∷_ (cl∞-bad-conf*-correct h b bad ls)
                (cl∞-bad-conf⇉-correct h b bad lss)

    -- cl∞-bad-conf*-correct

    cl∞-bad-conf*-correct :
      (h : History) (b : Bar ↯ h)
        (bad : Conf → Bool) (ls : List (LazyCograph Conf)) →
      cl-bad-conf* bad (prune-cograph* h b ls) ≡
        prune-cograph* h b (cl∞-bad-conf* bad ls)

    cl∞-bad-conf*-correct h b bad [] =
      refl
    cl∞-bad-conf*-correct h b bad (l ∷ ls) =
      cong₂ _∷_ (cl∞-bad-conf′-correct h b bad l)
                (cl∞-bad-conf*-correct h b bad ls)

  --
  -- cl∞-bad-conf-correct
  --

  cl∞-bad-conf-correct : (bad : Conf → Bool) →
    cl-bad-conf bad ∘ prune-cograph ≗
      prune-cograph ∘ cl∞-bad-conf bad

  cl∞-bad-conf-correct bad l =
    cl∞-bad-conf′-correct [] bar[] bad l


--
-- A cograph can be cleaned to remove some empty alternatives.
--

mutual

  -- cl∞-Ø

  cl∞-Ø : {C : Set} (l : LazyCograph C) → LazyCograph C

  cl∞-Ø Ø = Ø
  cl∞-Ø (stop c) = stop c
  cl∞-Ø (build c ♯lss) =
    build c (♯ cl∞-Ø⇉ (♭ ♯lss))

  cl∞-Ø⇉ : {C : Set}
    (lss : List (List (LazyCograph C))) → List (List (LazyCograph C))

  cl∞-Ø⇉ [] = []
  cl∞-Ø⇉ (ls ∷ lss) with any Ø∞≡? ls
  ... | yes _ = cl∞-Ø⇉ lss
  ... | no _ = cl∞-Ø* ls ∷ cl∞-Ø⇉ lss

  cl∞-Ø* : {C : Set}
    (ls : List (LazyCograph C)) → List (LazyCograph C)

  cl∞-Ø* [] = []
  cl∞-Ø* (l ∷ ls) = cl∞-Ø l ∷ cl∞-Ø* ls


-- An optimized version of `prune-cograph`.
-- The difference is that empty subtrees are removed
-- "on the fly".

module BigStepMRSC∞-Ø (scWorld : ScWorld) where

  open ScWorld scWorld
  --open BigStepMRSC scWorld
  --  using (lazy-mrsc; lazy-mrsc′)

  -- cl-empty-build

  cl-empty-build : Conf → List (List (LazyGraph Conf)) → LazyGraph Conf

  cl-empty-build c [] = Ø
  cl-empty-build c (ls ∷ lss) = build c (ls ∷ lss)

  mutual

    -- prune-cograph′-Ø

    prune-cograph′-Ø : (h : History) (b : Bar ↯ h) (l : LazyCograph Conf) →
      LazyGraph Conf

    prune-cograph′-Ø h b Ø = Ø
    prune-cograph′-Ø h b (stop c) = stop c
    prune-cograph′-Ø h b (build c ♯lss) with  ↯? h
    ... | yes w = Ø
    ... | no ¬w with b
    ... | now bz with ¬w bz
    ... | ()
    prune-cograph′-Ø h b (build c ♯lss) | no ¬w | later bs with ♭ ♯lss
    ... | lss =
      cl-empty-build c (prune-cograph⇉-Ø (c ∷ h) (bs c) lss)

    -- prune-cograph⇉-Ø

    prune-cograph⇉-Ø : (h : History) (b : Bar ↯ h)
      (lss : List (List (LazyCograph Conf))) → List (List (LazyGraph Conf))
    prune-cograph⇉-Ø h b [] = []
    prune-cograph⇉-Ø h b (ls ∷ lss) with prune-cograph*-Ø h b ls
    ... | nothing = prune-cograph⇉-Ø h b lss
    ... | just ls′ = ls′ ∷ prune-cograph⇉-Ø h b lss

    -- prune-cograph*-Ø

    prune-cograph*-Ø : (h : History) (b : Bar ↯ h)
      (ls : List (LazyCograph Conf)) → Maybe (List (LazyGraph Conf))

    prune-cograph*-Ø h b [] = just []
    prune-cograph*-Ø h b (l ∷ ls) with prune-cograph′-Ø h b l
    ... | l′ with Ø≡? l′
    ... | yes _ = nothing
    ... | no _ with prune-cograph*-Ø h b ls
    ... | nothing = nothing
    ... | just ls′ = just (l′ ∷ ls′)

  -- prune-cograph-Ø

  prune-cograph-Ø : (l : LazyCograph Conf) → LazyGraph Conf
  prune-cograph-Ø l = prune-cograph′-Ø [] bar[] l
