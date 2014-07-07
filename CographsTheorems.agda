--
-- Infinite trees/graphs (theorems)
--

module CographsTheorems where

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
open import Data.Unit

open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to P[_])

open import Util
open import BarWhistles
open import Graphs
open import BigStepSc
open import Cographs

module BigStepMRSC∞-Correctness (scWorld : ScWorld) where

  open ScWorld scWorld
  open BigStepMRSC scWorld
    using (lazy-mrsc; lazy-mrsc′)

  open BigStepMRSC∞ scWorld

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
    prune′∘build′-correct h (now w) c | no ¬f | no ¬w =
      ⊥-elim (¬w w)
    prune′∘build′-correct h (later bs) c | no ¬f | no ¬w =
      cong (build c) (prune′∘build⇉-correct h bs c (c ⇉))

    -- prune′∘build⇉-correct

    prune′∘build⇉-correct :
      (h : History) (bs : (c : Conf) → Bar ↯ (c ∷ h))
      (c : Conf) (css : List (List Conf)) →
        map (prune-cograph* (c ∷ h) (bs c)) (build-cograph⇉ h c css) ≡
        map (map (lazy-mrsc′ (c ∷ h) (bs c))) css

    prune′∘build⇉-correct h bs c [] = refl
    prune′∘build⇉-correct h bs c (cs ∷ css) =
      cong₂ _∷_ (prune′∘build*-correct (c ∷ h) (bs c) cs)
                (prune′∘build⇉-correct h bs c css)

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


module ClBadConf∞-Correctness (scWorld : ScWorld) where

  open ScWorld scWorld
  open BigStepMRSC∞ scWorld

  mutual

    -- cl∞-bad-conf′-correct

    cl∞-bad-conf′-correct :
      (h : History) (b : Bar ↯ h) (bad : Conf → Bool) →
      cl-bad-conf bad ∘ prune-cograph′ h b ≗
        prune-cograph′ h b ∘ cl∞-bad-conf bad

    cl∞-bad-conf′-correct h b bad Ø = refl
    cl∞-bad-conf′-correct h b bad (stop c) with bad c
    ... | true = refl
    ... | false = refl

    cl∞-bad-conf′-correct h b bad (build c lss)
      with ↯? h | inspect ↯? h | bad c | inspect bad c
    ... | yes w | P[ w≡ ] | true | P[ ≡true ] = refl
    ... | yes w | P[ w≡ ] | false | P[ ≡false ] rewrite w≡ = refl
    cl∞-bad-conf′-correct h (now w) bad (build c lss)
      | no ¬w | P[ w≡ ] | true | P[ ≡true ] = ⊥-elim (¬w w)
    cl∞-bad-conf′-correct h (later bs) bad (build c lss)
      | no ¬w | P[ w≡ ] | true | P[ ≡true ] rewrite ≡true = refl
    cl∞-bad-conf′-correct h (now w) bad (build c lss)
      | no ¬w | P[ w≡ ] | false | P[ ≡false ] = ⊥-elim (¬w w)
    cl∞-bad-conf′-correct h (later bs) bad (build c lss)
      | no ¬w | P[ w≡ ] | false | P[ ≡false ] rewrite w≡ | ≡false =
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


module BigStepMRSC∞-Ø-Correctness (scWorld : ScWorld) where

  open ScWorld scWorld
  open BigStepMRSC∞-Ø scWorld

  --
  -- Correctness of `pruneØ-cograph` with respect to `cl-empty` and
  -- `prune-cograph`.

  open BigStepMRSC∞ scWorld

  mutual

    -- pruneØ-cograph′-correct

    pruneØ-cograph′-correct :
      (h : History) (b : Bar ↯ h) (l : LazyCograph Conf) →
        pruneØ-cograph′ h b l ≡ cl-empty (prune-cograph′ h b l)

    pruneØ-cograph′-correct h b Ø = refl
    pruneØ-cograph′-correct h b (stop c) = refl
    pruneØ-cograph′-correct h b (build c lss) with ↯? h
    ... | yes w = refl
    pruneØ-cograph′-correct h (now w) (build c lss) | no ¬w =
      ⊥-elim (¬w w)
    pruneØ-cograph′-correct h (later bs) (build c lss) | no ¬w =
      cong (cl-empty-build c) (pruneØ-cograph⇉-correct c (c ∷ h) (bs c) (♭ lss))

    -- pruneØ-cograph⇉-correct

    pruneØ-cograph⇉-correct : (c : Conf)
      (h : History) (b : Bar ↯ h) (lss : List (List (LazyCograph Conf))) →
        pruneØ-cograph⇉ h b lss ≡ cl-empty⇉ (map (prune-cograph* h b) lss)

    pruneØ-cograph⇉-correct c h b [] = refl
    pruneØ-cograph⇉-correct c h b (ls ∷ lss)
      rewrite pruneØ-cograph*-correct h b ls
      with cl-empty* (prune-cograph* h b ls)
    ... | nothing = pruneØ-cograph⇉-correct c h b lss
    ... | just ls′ = cong (_∷_ ls′) (pruneØ-cograph⇉-correct c h b lss)
    
    -- pruneØ-cograph*-correct

    pruneØ-cograph*-correct :
      (h : History) (b : Bar ↯ h) (ls : List (LazyCograph Conf)) →
        pruneØ-cograph* h b ls ≡ cl-empty* (prune-cograph* h b ls)

    pruneØ-cograph*-correct h b [] = refl
    pruneØ-cograph*-correct h b (l ∷ ls)
      rewrite pruneØ-cograph′-correct h b l
      with cl-empty (prune-cograph′ h b l)
    ... | l′ with Ø≡? l′
    ... | yes _ = refl
    ... | no _ rewrite pruneØ-cograph*-correct h b ls
      with cl-empty* (prune-cograph* h b ls)
    ... | nothing = refl
    ... | just ls′ = refl 

  -- pruneØ-cograph-correct

  pruneØ-cograph-correct :
    pruneØ-cograph ≗ cl-empty ∘ prune-cograph

  pruneØ-cograph-correct l = pruneØ-cograph′-correct [] bar[] l

  --
  -- Correctness of `cl∞-Ø` with respect to `pruneØ-cograph`
  --

  Ø∈→nothing :
    (h : History) (b : Bar ↯ h) (ls : List (LazyCograph Conf)) →
    Any (_≡_ Ø) ls → pruneØ-cograph* h b ls ≡ nothing

  Ø∈→nothing h b .(l ∷ ls) (here {l} {ls} Ø≡l) rewrite P.sym $ Ø≡l = refl
  Ø∈→nothing h b .(l ∷ ls) (there {l} {ls} Ø∈ls)
    with pruneØ-cograph′ h b l
  ... | l′ with Ø≡? l′
  ... | yes Ø≡l′ = refl
  ... | no  Ø≢l′ rewrite Ø∈→nothing h b ls Ø∈ls = refl

  mutual

    -- cl∞-Ø′-correct

    cl∞-Ø′-correct :
      (h : History) (b : Bar ↯ h) (l : LazyCograph Conf) →
        pruneØ-cograph′ h b (cl∞-Ø l) ≡ pruneØ-cograph′ h b l

    cl∞-Ø′-correct h b Ø = refl
    cl∞-Ø′-correct h b (stop c) = refl
    cl∞-Ø′-correct h b (build c lss) with ↯? h
    ... | yes w = refl
    cl∞-Ø′-correct h (now w) (build c lss) | no ¬w =
      ⊥-elim (¬w w)
    cl∞-Ø′-correct h (later bs) (build c lss) | no ¬w =
      cong (cl-empty-build c) (cl∞-Ø⇉-correct (c ∷ h) (bs c) (♭ lss))

    -- cl∞-Ø⇉-correct

    cl∞-Ø⇉-correct :
      (h : History) (b : Bar ↯ h) (lss : List (List (LazyCograph Conf))) →
        pruneØ-cograph⇉ h b (cl∞-Ø⇉ lss) ≡ pruneØ-cograph⇉ h b lss

    cl∞-Ø⇉-correct h b [] = refl
    cl∞-Ø⇉-correct h b (ls ∷ lss) with any Ø∞≡? ls
    ... | yes Ø∈ls rewrite Ø∈→nothing h b ls Ø∈ls = cl∞-Ø⇉-correct h b lss
    ... | no  Ø∉ls
      with pruneØ-cograph* h b ls | inspect (pruneØ-cograph* h b) ls
    ... | nothing | P[ ≡nothing ]
      rewrite cl∞-Ø*-correct h b ls | ≡nothing | cl∞-Ø⇉-correct h b lss = refl
    ... | just ls′ | P[ ≡just ]
      rewrite cl∞-Ø*-correct h b ls | ≡just =
        cong (_∷_ ls′) (cl∞-Ø⇉-correct h b lss)

    cl∞-Ø*-correct :
      (h : History) (b : Bar ↯ h) (ls : List (LazyCograph Conf)) →
        pruneØ-cograph* h b (cl∞-Ø* ls) ≡ pruneØ-cograph* h b ls

    -- cl∞-Ø*-correct

    cl∞-Ø*-correct h b [] = refl
    cl∞-Ø*-correct h b (l ∷ ls) rewrite cl∞-Ø′-correct h b l
      with (pruneØ-cograph′ h b l) 
    ... | l′ with Ø≡? l′
    ... | yes Ø≡l′ = refl
    ... | no  Ø≢l′ rewrite cl∞-Ø*-correct h b ls
      with pruneØ-cograph* h b ls
    ... | nothing = refl
    ... | just ls′ = refl

  -- cl∞-Ø-correct

  cl∞-Ø-correct :
    pruneØ-cograph ∘ cl∞-Ø ≗ pruneØ-cograph

  cl∞-Ø-correct l = cl∞-Ø′-correct [] bar[] l

--
