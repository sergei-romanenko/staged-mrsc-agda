module Protocol.MESI where

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
  using (#⟪_⟫; %⟪_⟫)


MESI : CntWorld
MESI = ⟨⟨ start , rules , unsafe ⟩⟩
  where
  Conf = Vec ℕω 4

  start = ω ∷ # 0 ∷ # 0 ∷ # 0 ∷ []

  rules : Conf → List Conf
  rules (i ∷ e ∷ s ∷ m ∷ []) =
    ¶ i ≥ 1     ⇒
        (i ∸ # 1) ∷ # 0 ∷ s + e + m + # 1 ∷ # 0 ∷ [] □ ++
    ¶ e ≥ 1     ⇒
        i ∷ (e ∸ # 1) ∷ s ∷ (m + # 1) ∷ [] □ ++
    ¶ s ≥ 1     ⇒
        (i + e + s + m ∸ # 1) ∷ # 1 ∷ # 0 ∷ # 0 ∷ [] □ ++
    ¶ i ≥ 1     ⇒
        (i + e + s + m ∸ # 1) ∷ # 1 ∷ # 0 ∷ # 0 ∷ [] □ ++
    []

  unsafe : Conf → Bool
  unsafe (i ∷ e ∷ s ∷ m ∷ []) =
    ¶? m ≥ 2 □ ∨
    ¶? s ≥ 1 ∧ m ≥ 1 □

open CntSc MESI 3 10

-- Cographs

cograph : LazyCograph Conf
cograph = build-cograph start

cograph-safe : LazyCograph Conf
cograph-safe = cl∞-Ø $ cl∞-unsafe cograph

-- Removing empty subtrees while pruning.

lgraph-unsafe : LazyGraph Conf
lgraph-unsafe = pruneØ-cograph cograph

--#lgraph-unsafe : #⟪ lgraph-unsafe ⟫ ≡ 26140528192241323162034740828965449857
--#lgraph-unsafe = refl

--%lgraph-unsafe : %⟪ lgraph-unsafe ⟫ ≡
--  26140528192241323162034740828965449857 , ?
--%lgraph-unsafe = refl


lgraph : LazyGraph Conf
lgraph = pruneØ-cograph cograph-safe

--#lgraph : #⟪ lgraph ⟫ ≡ 3
--#lgraph = refl

--%lgraph : %⟪ lgraph ⟫ ≡ 3 , 104
--%lgraph = refl

lgraph-min-size = cl-min-size lgraph

%lgraph-min-size : %⟪ proj₂ lgraph-min-size ⟫ ≡ 1 , 15
%lgraph-min-size = refl

graph-min-size = ⟪ proj₂ lgraph-min-size ⟫
