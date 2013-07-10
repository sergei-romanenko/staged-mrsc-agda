module ProtocolMOSI where

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

open import Relation.Nullary

open import Graphs
open import BigStepSc
open import BigStepCounters

MOSI : CntWorld 4
MOSI = ⟪ start , rules , unsafe ⟫
  where

  start = ω ∷ # 0 ∷ # 0 ∷ # 0 ∷ []

  rules : Vec ℕω 4 → List (Vec ℕω 4)
  rules (i ∷ o ∷ s ∷ m ∷ []) =
    ¶ i ≥ 1     ⇒
        (i ∸ # 1) ∷ (m + o) ∷ (s + # 1) ∷ # 0 ∷ [] □ ++
    ¶ o ≥ 1     ⇒
        (i + o + s + m ∸ # 1) ∷ # 0 ∷ # 0 ∷ # 1 ∷ [] □ ++
    ¶ i ≥ 1     ⇒
        (i + o + s + m ∸ # 1) ∷ # 0 ∷ # 0 ∷ # 1 ∷ [] □ ++
    ¶ s ≥ 1     ⇒
        (i + o + s + m ∸ # 1) ∷ # 0 ∷ # 0 ∷ # 1 ∷ [] □ ++
    ¶ s ≥ 1     ⇒
        (i + # 1) ∷ o ∷ (s ∸ # 1) ∷ m ∷ [] □ ++
    ¶ m ≥ 1     ⇒
        (i + # 1) ∷ o ∷ s ∷ (m ∸ # 1) ∷ [] □ ++
    ¶ o ≥ 1     ⇒
        (i + # 1) ∷ (o ∸ # 1) ∷ s ∷ m ∷ [] □ ++
    []

  unsafe : Vec ℕω 4 → Bool
  unsafe (i ∷ o ∷ s ∷ m ∷ []) =
    ¶? o ≥ 2 □ ∨
    ¶? m ≥ 2 □ ∨
    ¶? s ≥ 1 ∧ m ≥ 1 □

scwMOSI : ScWorld
scwMOSI = mkScWorld 2 10 MOSI

open BigStepMRSC scwMOSI public

MOSI-graph : LazyGraph (ωConf 4) 0
MOSI-graph = lazy-mrsc (CntWorld.start MOSI)
