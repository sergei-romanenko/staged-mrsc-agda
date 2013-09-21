module Protocol.Illinois where

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


Illinois : CntWorld
Illinois = ⟨⟨ start , rules , unsafe ⟩⟩
  where
  Conf = Vec ℕω 4

  start = ω ∷ # 0 ∷ # 0 ∷ # 0 ∷ []

  rules : Conf → List Conf
  rules (i ∷ e ∷ d ∷ s ∷ []) =
    ¶ i ≥ 1 ∧ e == 0 ∧ d == 0 ∧ s == 0    ⇒
        (i ∸ # 1) ∷ # 1 ∷ # 0 ∷ # 0 ∷ [] □ ++
    ¶ i ≥ 1 ∧ d ≥ 1    ⇒
        (i ∸ # 1) ∷ e ∷ (d ∸ # 1) ∷ (s + # 2) ∷ [] □ ++
    ¶ i ≥ 1 ∧ (s + e) ≥ 1    ⇒
        (i ∸ # 1) ∷ # 0 ∷ d ∷ (s + e + # 1) ∷ [] □ ++
    ¶ e ≥ 1     ⇒
        i ∷ (e ∸ # 1) ∷ (d + # 1) ∷ s ∷ [] □ ++
    ¶ s ≥ 1     ⇒
        (i + s ∸ # 1) ∷ e ∷ (d + # 1) ∷ # 0 ∷ [] □ ++
    ¶ i ≥ 1     ⇒
        (i + e + d + s ∸ # 1) ∷ # 0 ∷ # 1 ∷ # 0 ∷ [] □ ++
    ¶ d ≥ 1     ⇒
        (i + # 1) ∷ e ∷ (d ∸ # 1) ∷ s ∷ [] □ ++
    ¶ s ≥ 1     ⇒
        (i + # 1) ∷ e ∷ d ∷ (s ∸ # 1) ∷ [] □ ++
    ¶ e ≥ 1     ⇒
        (i + # 1) ∷  (e ∸ # 1) ∷ d ∷ s ∷ [] □ ++
    []

  unsafe : Conf → Bool
  unsafe (i ∷ e ∷ d ∷ s ∷ []) =
    d ≥ 1 ∧ s ≥ 1 ∨
    d ≥ 2

open CntSc Illinois 3 10

-- Cographs

cograph : LazyCograph Conf
cograph = build-cograph start

cograph-safe : LazyCograph Conf
cograph-safe = cl∞-Ø $ cl∞-unsafe cograph

-- Removing empty subtrees while pruning.

lgraph-unsafe : LazyGraph Conf
lgraph-unsafe = pruneØ-cograph cograph

--#lgraph-unsafe : #⟪ lgraph-unsafe ⟫ ≡ 536608788097319730334729799104966475309008220461115286788275679409728233362951
--#lgraph-unsafe = refl

--%lgraph-unsafe : %⟪ lgraph-unsafe ⟫ ≡ 536608788097319730334729799104966475309008220461115286788275679409728233362951 , ?
--%lgraph-unsafe = refl


lgraph : LazyGraph Conf
lgraph = pruneØ-cograph cograph-safe

--#lgraph : #⟪ lgraph ⟫ ≡ 2
--#lgraph = refl

--%lgraph : %⟪ lgraph ⟫ ≡ 2 , 73
--%lgraph = refl

lgraph-min-size = cl-min-size lgraph

%lgraph-min-size : %⟪ proj₂ lgraph-min-size ⟫ ≡ 1 , 23
%lgraph-min-size = refl

graph-min-size = ⟪ proj₂ lgraph-min-size ⟫
