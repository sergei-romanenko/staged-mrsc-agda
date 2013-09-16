module Protocol.Synapse where

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
open import Statistics
  using (length⟪⟫)

Synapse : CntWorld 3
Synapse = ⟨⟨ start , rules , unsafe ⟩⟩
  where

  start = ω ∷ # 0 ∷ # 0 ∷ []

  rules : Vec ℕω 3 → List (Vec ℕω 3)
  rules (i ∷ d ∷ v ∷ []) =
    ¶ i ≥ 1     ⇒
        (i + d ∸ # 1) ∷ # 0 ∷ (v + # 1) ∷ [] □ ++
    ¶ v ≥ 1     ⇒
        (i + d + v ∸ # 1) ∷ # 1 ∷ # 0 ∷ [] □ ++
    ¶ i ≥ 1     ⇒
        (i + d + v ∸ # 1) ∷ # 1 ∷ # 0 ∷ [] □ ++
    []

  unsafe : Vec ℕω 3 → Bool
  unsafe (i ∷ d ∷ v ∷ []) =
    ¶? d ≥ 1 ∧ v ≥ 1 □ ∨
    ¶? d ≥ 2 □

open CntWorld Synapse

scwSynapse : ScWorld
scwSynapse = mkScWorld 3 10 Synapse

open ScWorld scwSynapse
 using (Conf)

open BigStepMRSC scwSynapse

graph : LazyGraph Conf
graph = lazy-mrsc start

#graph : length⟪⟫ graph ≡ 112020
#graph = refl

graph-cl-unsafe : LazyGraph Conf
graph-cl-unsafe = cl-empty $ cl-unsafe graph

#graph-cl-unsafe : length⟪⟫ graph-cl-unsafe ≡ 5
#graph-cl-unsafe = refl

graph-cl-min-size = cl-min-size graph-cl-unsafe
graph-min-size = ⟪ proj₂ graph-cl-min-size ⟫

-- Cographs

open import Cographs
open BigStepMRSC∞ scwSynapse

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

open BigStepMRSC∞-Ø scwSynapse

cograph-pruned-Ø : LazyGraph Conf
cograph-pruned-Ø = pruneØ-cograph cograph-safe

graph-cl-unsafe≡cograph-pruned-Ø :
  graph-cl-unsafe ≡ cograph-pruned-Ø

graph-cl-unsafe≡cograph-pruned-Ø = refl
