module Protocol.MSI where

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

MSI : CntWorld
MSI = ⟨⟨ start , rules , unsafe ⟩⟩
  where
  Conf = Vec ℕω 3

  start = ω ∷ # 0 ∷ # 0 ∷ []

  rules : Conf → List Conf
  rules (i ∷ m ∷ s ∷ []) =
    ¶ i ≥ 1     ⇒
        (i + m + s ∸ # 1) ∷ # 1 ∷ # 0 ∷ [] □ ++
    ¶ s ≥ 1     ⇒
        (i + m + s ∸ # 1) ∷ # 1 ∷ # 0 ∷ [] □ ++
    ¶ i ≥ 1     ⇒
        (i ∸ # 1) ∷ # 0 ∷ m + s + # 1 ∷ [] □ ++
    []

  unsafe : Conf → Bool
  unsafe (i ∷ m ∷ s ∷ []) =
    m ≥ 1 ∧ s ≥ 1 ∨
    m ≥ 2

open CntSc MSI 3 10

-- Cographs

cograph : LazyCograph Conf
cograph = build-cograph start

cograph-safe : LazyCograph Conf
cograph-safe = cl∞-Ø $ cl∞-unsafe cograph

-- Removing empty subtrees while pruning.

lgraph-unsafe : LazyGraph Conf
lgraph-unsafe = pruneØ-cograph cograph

--#lgraph-unsafe : #⟪ lgraph-unsafe ⟫ ≡ 5370016
--#lgraph-unsafe = refl

--%lgraph-unsafe : %⟪ lgraph-unsafe ⟫ ≡ 5370016 , 274510815
--%lgraph-unsafe = refl


lgraph : LazyGraph Conf
lgraph = pruneØ-cograph cograph-safe

#lgraph : #⟪ lgraph ⟫ ≡ 3
#lgraph = refl

%lgraph : %⟪ lgraph ⟫ ≡ 3 , 58
%lgraph = refl

lgraph-min-size = cl-min-size lgraph

%lgraph-min-size : %⟪ proj₂ lgraph-min-size ⟫ ≡ 1 , 9
%lgraph-min-size = refl

graph-min-size = ⟪ proj₂ lgraph-min-size ⟫
