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
open import Cographs
open import Statistics
  using (#⟪_⟫)

MOESI : CntWorld
MOESI = ⟨⟨ start , rules , unsafe ⟩⟩
  where
  Conf = Vec ℕω 5

  start = ω ∷ # 0 ∷ # 0 ∷ # 0 ∷ # 0 ∷ []

  rules : Conf → List Conf
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

  unsafe : Conf → Bool
  unsafe (i ∷ m ∷ s ∷ e ∷ o ∷ []) =
    ¶? m ≥ 1 ∧ e + s + o ≥ 1 □ ∨
    ¶? m ≥ 2 □ ∨
    ¶? e ≥ 2 □

open CntSc MOESI 3 10

-- Cographs

cograph : LazyCograph Conf
cograph = build-cograph start

cograph-safe : LazyCograph Conf
cograph-safe = cl∞-Ø $ cl∞-unsafe cograph

-- Removing empty subtrees while pruning.

lgraph : LazyGraph Conf
lgraph = pruneØ-cograph cograph-safe

#lgraph : #⟪ lgraph ⟫ ≡ 3944820
#lgraph = refl

lgraph-min-size = cl-min-size lgraph
graph-min-size = ⟪ proj₂ lgraph-min-size ⟫
