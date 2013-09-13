module Protocol.MOSI where

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
open import Relation.Binary.PropositionalEquality

open import Graphs
open import BigStepSc
open import BigStepCounters
open import Statistics
  using (length⟪⟫)

MOSI : CntWorld 4
MOSI = ⟨⟨ start , rules , unsafe ⟩⟩
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
scwMOSI = mkScWorld 3 10 MOSI

open BigStepMRSC scwMOSI

graph : LazyGraph (ωConf 4)
graph = lazy-mrsc (CntWorld.start MOSI)

graph-cl-unsafe : LazyGraph (ωConf 4)
graph-cl-unsafe = CntWorld.cl-unsafe MOSI graph

#graph-cl-unsafe : length⟪⟫ graph-cl-unsafe ≡ 459
#graph-cl-unsafe = refl

graph-cl-min-size = cl-min-size graph-cl-unsafe
graph-min-size = ⟪ proj₂ graph-cl-min-size ⟫

-- Cographs

open import Cographs
open BigStepMRSC∞ scwMOSI

graph∞ : LazyCograph (ωConf 4)
graph∞ = build-cograph (CntWorld.start MOSI)

graph∞-safe : LazyCograph (ωConf 4)
graph∞-safe = cl-bad-conf∞ (CntWorld.unsafe MOSI) graph∞

graph∞-pruned : LazyGraph (ωConf 4)
graph∞-pruned = cl-empty (prune-cograph graph∞-safe)

graph-cl-unsafe≡graph∞-pruned :
  graph-cl-unsafe ≡ graph∞-pruned

graph-cl-unsafe≡graph∞-pruned = refl
