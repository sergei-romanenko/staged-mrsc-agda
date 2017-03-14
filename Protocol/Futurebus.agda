module Protocol.Futurebus where

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

Futurebus : CntWorld
Futurebus = ⟨⟨ start , rules , unsafe ⟩⟩
  where
  Conf = Vec ℕω 9

  start = ω ∷ # 0 ∷ # 0 ∷ # 0 ∷ # 0 ∷ # 0 ∷ # 0 ∷ # 0 ∷ # 0 ∷ []

  rules : Conf → List Conf
  rules (i ∷ sU ∷ eU ∷ eM ∷ pR ∷ pW ∷ pEMR ∷ pEMW ∷ pSU ∷ []) =
    ¶ i ≥ 1 ∧ pW == 0 ⇒
        (i ∸ # 1) ∷ # 0 ∷ # 0 ∷ # 0 ∷
          (pR + # 1) ∷ pW ∷ (pEMR + eM) ∷ pEMW ∷ (pSU + sU + eU) ∷ [] □ ++
    ¶ pEMR ≥ 1 ⇒
        i ∷ (sU + pR + # 1) ∷ eU ∷ eM ∷
          # 0 ∷ pW ∷ (pEMR ∸ # 1) ∷ pEMW ∷ pSU ∷ [] □ ++
    ¶ pSU ≥ 1 ⇒
        i ∷ (sU + pR + pSU) ∷ eU ∷ eM ∷
          # 0 ∷ pW ∷ pEMR ∷ pEMW ∷ # 0 ∷ [] □ ++
    ¶ pR ≥ 2 ∧ pSU == 0 ∧ pEMR == 0 ⇒
        i ∷ (sU + pR) ∷ eU ∷ eM ∷
          # 0 ∷ pW ∷ # 0 ∷ pEMW ∷ # 0 ∷ [] □ ++
    ¶ pR ≥ 2 ∧ pSU == 0 ∧ pEMR == 0 ⇒
        i ∷ (sU + pR) ∷ eU ∷ eM ∷
          # 0 ∷ pW ∷ # 0 ∷ pEMW ∷ # 0 ∷ [] □ ++
    ¶ pR == 1 ∧ pSU == 0 ∧ pEMR == 0 ⇒
        i ∷ sU ∷ (eU + # 1) ∷ eM ∷
          # 0 ∷ pW ∷ # 0 ∷ pEMW ∷ # 0 ∷ [] □ ++
    ¶ i ≥ 1 ∧ pW == 0 ⇒
        (i + eU + sU + pSU + pR + pEMR ∸ # 1) ∷ # 0 ∷ # 0 ∷ # 0 ∷
          # 0 ∷ # 1 ∷ # 0 ∷ (pEMW + eM) ∷ # 0 ∷ [] □ ++
    ¶ pEMW ≥ 1    ⇒
        (i + # 1) ∷ sU ∷ eU ∷ (eM + pW) ∷
          pR ∷ # 0 ∷ pEMR ∷ (pEMW ∸ # 1) ∷ pSU ∷ [] □ ++
    ¶ pEMW == 0   ⇒
        i ∷ sU ∷ eU ∷ (eM + pW) ∷
          pR ∷ # 0 ∷ pEMR ∷ # 0 ∷ pSU ∷ [] □ ++
    ¶ eU ≥ 1    ⇒
        i ∷ sU ∷ (eU ∸ # 1) ∷ (eM + # 1) ∷
          pR ∷ pW ∷ pEMR ∷ pEMW ∷ pSU ∷ [] □ ++
    ¶ i ≥ 1     ⇒
        (i + sU ∸ # 1) ∷  # 0 ∷ eU ∷ (eM + # 1) ∷
          pR ∷ pW ∷ pEMR ∷ pEMW ∷ pSU ∷ [] □ ++
    []

  unsafe : Conf → Bool
  unsafe (i ∷ sU ∷ eU ∷ eM ∷ pR ∷ pW ∷ pEMR ∷ pEMW ∷ pSU ∷ []) =
    sU ≥ 1 ∧ eU + eM ≥ 1 ∨
    eU + eM ≥ 2 ∨
    pR ≥ 1 ∧ pW ≥ 1 ∨
    pW ≥ 2

open CntSc Futurebus 3 10

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

--%lgraph-unsafe : %⟪ lgraph-unsafe ⟫ ≡ (? , ?)
--%lgraph-unsafe = refl


lgraph : LazyGraph Conf
lgraph = pruneØ-cograph cograph-safe

--#lgraph : #⟪ lgraph ⟫ ≡ ?
--#lgraph = refl

--%lgraph : %⟪ lgraph ⟫ ≡ (? , ?)
--%lgraph = refl

lgraph-min-size = cl-min-size lgraph

--%lgraph-min-size : %⟪ proj₂ lgraph-min-size ⟫ ≡ (1 , 9)
--%lgraph-min-size = refl

--graph-min-size = ⟪ proj₂ lgraph-min-size ⟫
