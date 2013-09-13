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

open import Relation.Nullary

open import Graphs
open import BigStepSc
open import BigStepCounters

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

scwSynapse : ScWorld
scwSynapse = mkScWorld 3 10 Synapse

open BigStepMRSC scwSynapse

graph : LazyGraph (ωConf 3)
graph = lazy-mrsc (CntWorld.start Synapse)

graph-cl-unsafe : LazyGraph (ωConf 3)
graph-cl-unsafe = CntWorld.cl-unsafe Synapse graph

graph-cl-min-size = cl-min-size graph-cl-unsafe
graph-min-size = ⟪ proj₂ graph-cl-min-size ⟫

-- Cographs

open import Cographs
open BigStepMRSC∞ scwSynapse

graph∞ : LazyCograph (ωConf 3)
graph∞ = build-cograph (CntWorld.start Synapse)

graph∞-safe : LazyCograph (ωConf 3)
graph∞-safe = cl-bad-conf∞ (CntWorld.unsafe Synapse) graph∞

graph∞-pruned : LazyGraph (ωConf 3)
graph∞-pruned = cl-empty (prune-cograph graph∞-safe)

open import Relation.Binary.PropositionalEquality

graph-cl-unsafe≡graph∞-pruned :
  graph-cl-unsafe ≡ graph∞-pruned

graph-cl-unsafe≡graph∞-pruned = refl
