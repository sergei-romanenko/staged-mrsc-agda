module Protocol.MOSI where

open import Data.Nat as N
  using (ℕ; zero; suc)
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.Bool
  using (Bool; true; false; _∧_; _∨_)
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

MOSI : CntWorld
MOSI = ⟨⟨ start , rules , unsafe ⟩⟩
  where
  Conf = Vec ℕω 4

  start = ω ∷ # 0 ∷ # 0 ∷ # 0 ∷ []

  rules : Conf → List Conf
  rules (i ∷ o ∷ s ∷ m ∷ []) =
    ¶ i ≥ 1     ⇒
        (i ∸ # 1) ∷ (m + o) ∷ (s + # 1) ∷ # 0 ∷ [] □ ++
    ¶ o ≥ 1     ⇒
        (i + o + s + m ∸ # 1) ∷ # 0 ∷ # 0 ∷ # 1 ∷ [] □ ++
    ¶ i ≥ 1     ⇒
        (i + o + s + m ∸ # 1) ∷ # 0 ∷ # 0 ∷ # 1 ∷ [] □ ++
    ¶ s ≥ 1     ⇒
        (i + o + s + m ∸ # 1) ∷ # 0 ∷ # 0 ∷ # 1 ∷ [] □ ++
    ¶ s ≥ 1     ⇒
        (i + # 1) ∷ o ∷ (s ∸ # 1) ∷ m ∷ [] □ ++
    ¶ m ≥ 1     ⇒
        (i + # 1) ∷ o ∷ s ∷ (m ∸ # 1) ∷ [] □ ++
    ¶ o ≥ 1     ⇒
        (i + # 1) ∷ (o ∸ # 1) ∷ s ∷ m ∷ [] □ ++
    []

  unsafe : Conf → Bool
  unsafe (i ∷ o ∷ s ∷ m ∷ []) =
    o ≥ 2 ∨
    m ≥ 2 ∨
    s ≥ 1 ∧ m ≥ 1

open CntSc MOSI 3 10

-- Cographs

cograph : LazyCograph Conf
cograph = build-cograph start

cograph-safe : LazyCograph Conf
cograph-safe = cl∞-Ø $ cl∞-unsafe cograph

-- Removing empty subtrees while pruning.

lgraph : LazyGraph Conf
lgraph = pruneØ-cograph cograph-safe

--#lgraph : #⟪ lgraph ⟫ ≡ 459
--#lgraph = refl

--%lgraph : %⟪ lgraph ⟫ ≡ (459 , 53802)
--%lgraph = refl

lgraph-min-size = cl-min-size lgraph

%lgraph-min-size : %⟪ proj₂ lgraph-min-size ⟫ ≡ (1 , 26)
%lgraph-min-size = refl

graph-min-size = ⟪ proj₂ lgraph-min-size ⟫
