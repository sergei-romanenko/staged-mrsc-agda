module Protocol.Synapse where

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

Synapse : CntWorld
Synapse = ⟨⟨ start , rules , unsafe ⟩⟩
  where
  Conf = Vec ℕω 3

  start = ω ∷ # 0 ∷ # 0 ∷ []

  rules : Conf → List Conf
  rules (i ∷ d ∷ v ∷ []) =
    ¶ i ≥ 1     ⇒
        (i + d ∸ # 1) ∷ # 0 ∷ (v + # 1) ∷ [] □ ++
    ¶ v ≥ 1     ⇒
        (i + d + v ∸ # 1) ∷ # 1 ∷ # 0 ∷ [] □ ++
    ¶ i ≥ 1     ⇒
        (i + d + v ∸ # 1) ∷ # 1 ∷ # 0 ∷ [] □ ++
    []

  unsafe : Conf → Bool
  unsafe (i ∷ d ∷ v ∷ []) =
    d ≥ 1 ∧ v ≥ 1 ∨
    d ≥ 2

open CntSc Synapse 3 10

graph : LazyGraph Conf
graph = lazy-mrsc start

#graph : #⟪ graph ⟫ ≡ 112020
#graph = refl

--%graph : %⟪ graph ⟫ ≡ 112020 , 4024002
--%graph = refl

graph-cl-unsafe : LazyGraph Conf
graph-cl-unsafe = cl-empty $ cl-unsafe graph

-- Cographs

cograph : LazyCograph Conf
cograph = build-cograph start

cograph-safe : LazyCograph Conf
cograph-safe = cl∞-Ø $ cl∞-unsafe cograph

cograph-pruned : LazyGraph Conf
cograph-pruned = cl-empty $ prune-cograph cograph-safe

graph-cl-unsafe≡cograph-pruned :
  graph-cl-unsafe ≡ cograph-pruned

graph-cl-unsafe≡cograph-pruned = refl

-- Removing empty subtrees while pruning.

lgraph : LazyGraph Conf
lgraph = pruneØ-cograph cograph-safe

graph-cl-unsafe≡lgraph :
  graph-cl-unsafe ≡ lgraph

graph-cl-unsafe≡lgraph = refl

#lgraph : #⟪ lgraph ⟫ ≡ 5
#lgraph = refl

%lgraph : %⟪ lgraph ⟫ ≡ 5 , 97
%lgraph = refl

lgraph-min-size = cl-min-size lgraph

%lgraph-min-size : %⟪ proj₂ lgraph-min-size ⟫ ≡ 1 , 9
%lgraph-min-size = refl

graph-min-size = ⟪ proj₂ lgraph-min-size ⟫
