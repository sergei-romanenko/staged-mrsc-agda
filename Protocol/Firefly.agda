module Protocol.Firefly where

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


Firefly : CntWorld
Firefly = ⟨⟨ start , rules , unsafe ⟩⟩
  where
  Conf = Vec ℕω 4

  start = ω ∷ # 0 ∷ # 0 ∷ # 0 ∷ []

  rules : Conf → List Conf
  rules (i ∷ e ∷ s ∷ d ∷ []) =
    ¶ i ≥ 1 ∧ d == 0 ∧ s == 0 ∧ e == 0    ⇒
        (i ∸ # 1) ∷ # 1 ∷ # 0 ∷ # 0 ∷ [] □ ++
    ¶ i ≥ 1 ∧ d ≥ 1    ⇒
        (i ∸ # 1) ∷ e ∷ (s + # 2) ∷ (d ∸ # 1) ∷ [] □ ++
    ¶ i ≥ 1 ∧ s + e ≥ 1    ⇒
        (i ∸ # 1) ∷ # 0 ∷ (s + e + # 1) ∷ d ∷ [] □ ++
    ¶ e ≥ 1     ⇒
        i ∷ (e ∸ # 1) ∷ s ∷ (d + # 1) ∷ [] □ ++
    ¶ s == 1    ⇒
        i ∷ (e + # 1) ∷ # 0 ∷ d ∷ [] □ ++
    ¶ i ≥ 1     ⇒
        (i + e + d + s ∸ # 1) ∷ # 0 ∷ # 0 ∷ # 1 ∷ [] □ ++
    []

  unsafe : Conf → Bool
  unsafe (i ∷ e ∷ s ∷ d ∷ []) =
    d ≥ 1 ∧ s + e ≥ 1 ∨
    e ≥ 2 ∨
    d ≥ 2

open CntSc Firefly 3 10

-- Cographs

cograph : LazyCograph Conf
cograph = build-cograph start

cograph-safe : LazyCograph Conf
cograph-safe = cl∞-Ø $ cl∞-unsafe cograph

-- Removing empty subtrees while pruning.

lgraph-unsafe : LazyGraph Conf
lgraph-unsafe = pruneØ-cograph cograph

--#lgraph-unsafe : #⟪ lgraph-unsafe ⟫ ≡ 156054828074624700461769313524
--#lgraph-unsafe = refl

--%lgraph-unsafe : %⟪ lgraph-unsafe ⟫ ≡
--  (156054828074624700461769313524 , ?)
--%lgraph-unsafe = refl


lgraph : LazyGraph Conf
lgraph = pruneØ-cograph cograph-safe

--#lgraph : #⟪ lgraph ⟫ ≡ 2
--#lgraph = refl

--%lgraph : %⟪ lgraph ⟫ ≡ (2 , 62)
--%lgraph = refl

lgraph-min-size = cl-min-size lgraph

%lgraph-min-size : %⟪ proj₂ lgraph-min-size ⟫ ≡ (1 , 22)
%lgraph-min-size = refl

graph-min-size = ⟪ proj₂ lgraph-min-size ⟫
