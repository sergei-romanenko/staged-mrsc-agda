module Protocol.Berkley where

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

Berkley : CntWorld
Berkley = ⟨⟨ start , rules , unsafe ⟩⟩
  where
  Conf = Vec ℕω 4

  start = ω ∷ # 0 ∷ # 0 ∷ # 0 ∷ []

  rules : Conf → List Conf
  rules (i ∷ n ∷ u ∷ e ∷ []) =
    ¶ i ≥ 1     ⇒
        (i ∸ # 1) ∷ (n + e) ∷ (u + # 1) ∷ # 0 ∷ [] □ ++
    ¶ i ≥ 1     ⇒
        (i + n + u + e ∸ # 1) ∷ # 0 ∷ # 0 ∷ # 1 ∷ [] □ ++
    ¶ n + u ≥ 1     ⇒
        (i + n + u ∸ # 1) ∷ # 0 ∷ # 0 ∷ (e + # 1) ∷ [] □ ++
    []

  unsafe : Conf → Bool
  unsafe (i ∷ n ∷ u ∷ e ∷ []) =
    e ≥ 1 ∧ u + n ≥ 1 ∨
    e ≥ 2

open CntSc Berkley 3 10

-- Cographs

cograph : LazyCograph Conf
cograph = build-cograph start

cograph-safe : LazyCograph Conf
cograph-safe = cl∞-Ø $ cl∞-unsafe cograph

-- Removing empty subtrees while pruning.

lgraph-unsafe : LazyGraph Conf
lgraph-unsafe = pruneØ-cograph cograph

--#lgraph-unsafe : #⟪ lgraph-unsafe ⟫ ≡ 5038823438947735862
--#lgraph-unsafe = refl

--%lgraph-unsafe : %⟪ lgraph-unsafe ⟫ ≡ (5038823438947735862 , ?)
--%lgraph-unsafe = refl

lgraph : LazyGraph Conf
lgraph = pruneØ-cograph cograph-safe

--#lgraph : #⟪ lgraph ⟫ ≡ 62247
--#lgraph = refl

--%lgraph : %⟪ lgraph ⟫ ≡ (62247 , 3135052)
--%lgraph = refl

lgraph-min-size = cl-min-size lgraph

%lgraph-min-size : %⟪ proj₂ lgraph-min-size ⟫ ≡ (1 , 9)
%lgraph-min-size = refl

graph-min-size = ⟪ proj₂ lgraph-min-size ⟫
