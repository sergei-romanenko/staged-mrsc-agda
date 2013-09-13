module ProtocolMOESI where

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

MOESI : CntWorld 5
MOESI = ⟨⟨ start , rules , unsafe ⟩⟩
  where

  start = ω ∷ # 0 ∷ # 0 ∷ # 0 ∷ # 0 ∷ []

  rules : Vec ℕω 5 → List (Vec ℕω 5)
  rules (i ∷ m ∷ s ∷ e ∷ o ∷ []) =
    ¶ i ≥ 1     ⇒
      (i ∸ # 1) ∷ # 0 ∷ (s + e + # 1) ∷ # 0 ∷ (o + m) ∷ [] □ ++
    ¶ e ≥ 1     ⇒
      i ∷ (m + # 1) ∷ s ∷ (e ∸ # 1) ∷ o ∷ [] □ ++
    ¶ s + o ≥ 1 ⇒
      (i + m + s + e + o ∸ # 1) ∷ # 0 ∷ # 0 ∷ # 1 ∷ # 0 ∷ [] □ ++
    ¶ i ≥ 1     ⇒
      (i + m + s + e + o ∸ # 1) ∷ # 0 ∷ # 0 ∷ # 1 ∷ # 0 ∷ [] □ ++
    []

  unsafe : Vec ℕω 5 → Bool
  unsafe (i ∷ m ∷ s ∷ e ∷ o ∷ []) =
    ¶? m ≥ 1 ∧ e + s + o ≥ 1 □ ∨
    ¶? m ≥ 2 □ ∨
    ¶? e ≥ 2 □

scwMOESI : ScWorld
scwMOESI = mkScWorld 2 10 MOESI

open BigStepMRSC scwMOESI

graph : LazyGraph (ωConf 5)
graph = lazy-mrsc (CntWorld.start MOESI)

graph-cl-unsafe : LazyGraph (ωConf 5)
graph-cl-unsafe = CntWorld.cl-unsafe MOESI graph

graph-cl-min-size = cl-min-size graph-cl-unsafe
graph-min-size = ⟪ proj₂ graph-cl-min-size ⟫

-- Cographs

open import Cographs
open BigStepMRSC∞ scwMOESI

graph∞ : LazyCograph (ωConf 5)
graph∞ = build-cograph (CntWorld.start MOESI)

graph∞-safe : LazyCograph (ωConf 5)
graph∞-safe = cl-bad-conf∞ (CntWorld.unsafe MOESI) graph∞

graph∞-pruned : LazyGraph (ωConf 5)
graph∞-pruned = cl-empty (prune-cograph graph∞-safe)

open import Relation.Binary.PropositionalEquality

graph-cl-unsafe≡graph∞-pruned :
  graph-cl-unsafe ≡ graph∞-pruned

graph-cl-unsafe≡graph∞-pruned = refl
