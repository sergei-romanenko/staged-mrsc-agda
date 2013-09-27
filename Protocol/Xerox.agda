module Protocol.Xerox where

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

Xerox : CntWorld
Xerox = ⟨⟨ start , rules , unsafe ⟩⟩
  where
  Conf = Vec ℕω 5

  start = ω ∷ # 0 ∷ # 0 ∷ # 0 ∷ # 0 ∷ []

  rules : Conf → List Conf
  rules (i ∷ sc ∷ sd ∷ d ∷ e ∷ []) =
    ¶ i ≥ 1 ∧ d == 0 ∧ sc == 0 ∧ sd == 0 ∧ e == 0 ⇒
        (i ∸ # 1) ∷ # 0 ∷ # 0 ∷ # 0 ∷ # 1 ∷ [] □ ++
    ¶ i ≥ 1 ∧ d + sc + e + sd ≥ 1 ⇒
        (i ∸ # 1) ∷ (sc + e + # 1) ∷ (sd + d) ∷ # 0 ∷ # 0 ∷ [] □ ++
    ¶ i ≥ 1 ∧ d == 0 ∧ sc == 0 ∧ sd == 0 ∧ e == 0 ⇒
        (i ∸ # 1) ∷ # 0 ∷ # 0 ∷ # 1 ∷ # 0 ∷ [] □ ++
    ¶ i ≥ 1 ∧ d + sc + e + sd ≥ 1 ⇒
        (i ∸ # 1) ∷ (sc + e + # 1 + sd + d) ∷ sd ∷ # 0 ∷ # 0 ∷ [] □ ++
    ¶ d ≥ 1 ⇒
        (i + # 1) ∷ sc ∷ sd ∷ (d ∸ # 1) ∷ e ∷ [] □ ++
    ¶ sc ≥ 1 ⇒
        (i + # 1) ∷ (sc ∸ # 1) ∷ sd ∷ d ∷ e ∷ [] □ ++
    ¶ sd ≥ 1 ⇒
        (i + # 1) ∷ sc ∷ (sd ∸ # 1) ∷ d ∷ e ∷ [] □ ++
    ¶ e ≥ 1 ⇒
        (i + # 1) ∷ sc ∷ sd ∷ d ∷ (e ∸ # 1) ∷ [] □ ++
    []

  unsafe : Conf → Bool
  unsafe (i ∷ sc ∷ sd ∷ d ∷ e ∷ []) =
    d ≥ 1 ∧ (e + sc + sd) ≥ 1 ∧
    e ≥ 1 ∧ (sc + sd) ≥ 1 ∧
    d ≥ 2 ∧
    e ≥ 2

open CntSc Xerox 3 10

-- Cographs

cograph : LazyCograph Conf
cograph = build-cograph start

cograph-safe : LazyCograph Conf
cograph-safe = cl∞-Ø $ cl∞-unsafe cograph

-- Removing empty subtrees while pruning.

lgraph-unsafe : LazyGraph Conf
lgraph-unsafe = pruneØ-cograph cograph

--#lgraph-unsafe : #⟪ lgraph-unsafe ⟫ ≡ ?
--#lgraph-unsafe = refl

--%lgraph-unsafe : %⟪ lgraph-unsafe ⟫ ≡ ? , ?
--%lgraph-unsafe = refl


lgraph : LazyGraph Conf
lgraph = pruneØ-cograph cograph-safe

--#lgraph : #⟪ lgraph ⟫ ≡ ?
--#lgraph = refl

--%lgraph : %⟪ lgraph ⟫ ≡ ? , ?
--%lgraph = refl

lgraph-min-size = cl-min-size lgraph

--%lgraph-min-size : %⟪ proj₂ lgraph-min-size ⟫ ≡ 1 , ?
--%lgraph-min-size = refl

graph-min-size = ⟪ proj₂ lgraph-min-size ⟫
