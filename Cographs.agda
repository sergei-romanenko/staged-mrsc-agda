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
  using (Any; here; there; any)
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
    prune-cograph′ h (now w) (build c lss) | no ¬w =
      ⊥-elim (¬w w)
    prune-cograph′ h (later bs) (build c lss) | no ¬w =
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


--
-- A cograph can be cleaned to remove some empty alternatives.
--
-- Note that the cleaning is not perfect, because `cl∞-Ø` has to pass
-- the productivity check.
-- So, `build c []` is not (recursively) replaced with `Ø`. as is done
-- by `cl-empty`.
--

mutual

  -- cl∞-Ø

  cl∞-Ø : {C : Set} (l : LazyCograph C) → LazyCograph C

  cl∞-Ø Ø = Ø
  cl∞-Ø (stop c) = stop c
  cl∞-Ø (build c ♯lss) =
    build c (♯ cl∞-Ø⇉ (♭ ♯lss))

  -- cl∞-Ø⇉

  cl∞-Ø⇉ : {C : Set}
    (lss : List (List (LazyCograph C))) → List (List (LazyCograph C))

  cl∞-Ø⇉ [] = []
  cl∞-Ø⇉ (ls ∷ lss) with any Ø∞≡? ls
  ... | yes Ø∈ls = cl∞-Ø⇉ lss
  ... | no  Ø∉ls = cl∞-Ø* ls ∷ cl∞-Ø⇉ lss

  -- cl∞-Ø*

  cl∞-Ø* : {C : Set}
    (ls : List (LazyCograph C)) → List (LazyCograph C)

  cl∞-Ø* [] = []
  cl∞-Ø* (l ∷ ls) = cl∞-Ø l ∷ cl∞-Ø* ls


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
      cl-empty-build c (pruneØ-cograph⇉ (c ∷ h) (bs c) (♭ lss))

    -- pruneØ-cograph⇉

    pruneØ-cograph⇉ : (h : History) (b : Bar ↯ h)
      (lss : List (List (LazyCograph Conf))) → List (List (LazyGraph Conf))
    pruneØ-cograph⇉ h b [] = []
    pruneØ-cograph⇉ h b (ls ∷ lss) with pruneØ-cograph* h b ls
    ... | nothing = pruneØ-cograph⇉ h b lss
    ... | just ls′ = ls′ ∷ pruneØ-cograph⇉ h b lss

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

  pruneØ-cograph l = pruneØ-cograph′ [] bar[] l
