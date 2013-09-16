module Protocol.MOESI where

open import Data.Nat as N
  using (ℕ; zero; suc)
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.Bool
  using (Bool; true; false; _∨_)
open import Data.List
  using (List; []; _∷_; _++_)
open import Data.Vec
  using (Vec; []; _∷_)
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃)

open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Graphs
open import BigStepSc
open import BigStepCounters
open import Statistics
  using (length⟪⟫)

MOESI : CntWorld 5
MOESI = ⟨⟨ start , rules , unsafe ⟩⟩
  where

  start = ω ∷ # 0 ∷ # 0 ∷ # 0 ∷ # 0 ∷ []

  rules : Vec ℕω 5 → List (Vec ℕω 5)
  rules (i ∷ m ∷ s ∷ e ∷ o ∷ []) =
    ¶ i ≥ 1     ⇒
      (i ∸ # 1) ∷ # 0 ∷ (s + e + # 1) ∷ # 0 ∷ (o + m) ∷ [] □ ++
    ¶ e ≥ 1     ⇒
      i ∷ (m + # 1) ∷ s ∷ (e ∸ # 1) ∷ o ∷ [] □ ++
    ¶ s + o ≥ 1 ⇒
      (i + m + s + e + o ∸ # 1) ∷ # 0 ∷ # 0 ∷ # 1 ∷ # 0 ∷ [] □ ++
    ¶ i ≥ 1     ⇒
      (i + m + s + e + o ∸ # 1) ∷ # 0 ∷ # 0 ∷ # 1 ∷ # 0 ∷ [] □ ++
    []

  unsafe : Vec ℕω 5 → Bool
  unsafe (i ∷ m ∷ s ∷ e ∷ o ∷ []) =
    ¶? m ≥ 1 ∧ e + s + o ≥ 1 □ ∨
    ¶? m ≥ 2 □ ∨
    ¶? e ≥ 2 □

open CntWorld MOESI

scwMOESI : ScWorld
scwMOESI = mkScWorld 2 10 MOESI

open ScWorld scwMOESI
  using (Conf)

open BigStepMRSC scwMOESI

graph : LazyGraph Conf
graph = lazy-mrsc start

--#graph : length⟪⟫ graph ≡ {!!}
--#graph = refl

graph-cl-unsafe : LazyGraph Conf
graph-cl-unsafe = cl-empty $ cl-unsafe graph

#graph-cl-unsafe : length⟪⟫ graph-cl-unsafe ≡ 19
#graph-cl-unsafe = refl

graph-cl-min-size = cl-min-size graph-cl-unsafe
graph-min-size = ⟪ proj₂ graph-cl-min-size ⟫

-- Cographs

open import Cographs
open BigStepMRSC∞ scwMOESI

cograph : LazyCograph Conf
cograph = build-cograph start

cograph-safe : LazyCograph Conf
cograph-safe = cl∞-Ø $ cl∞-unsafe cograph

cograph-pruned : LazyGraph Conf
cograph-pruned = cl-empty (prune-cograph cograph-safe)

graph-cl-unsafe≡cograph-pruned :
  graph-cl-unsafe ≡ cograph-pruned

graph-cl-unsafe≡cograph-pruned = refl

-- Removing empty subtrees while pruning.

open BigStepMRSC∞-Ø scwMOESI

cograph-pruned-Ø : LazyGraph Conf
cograph-pruned-Ø = pruneØ-cograph cograph-safe

graph-cl-unsafe≡cograph-pruned-Ø :
  graph-cl-unsafe ≡ cograph-pruned-Ø

graph-cl-unsafe≡cograph-pruned-Ø = refl
