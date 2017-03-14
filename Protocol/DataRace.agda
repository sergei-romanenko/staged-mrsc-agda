module Protocol.DataRace where

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

DataRace : CntWorld
DataRace = ⟨⟨ start , rules , unsafe ⟩⟩
  where
  Conf = Vec ℕω 3

  start = ω ∷ # 0 ∷ # 0 ∷ []

  rules : Conf → List Conf
  rules (out ∷ cs ∷ scs ∷ []) =
    ¶ out ≥ 1 ∧ cs == 0 ∧ scs == 0 ⇒
        (out ∸ # 1) ∷ # 1 ∷ # 0 ∷ [] □ ++
    ¶ out ≥ 1 ∧ cs == 0 ⇒
        (out ∸ # 1) ∷ # 0 ∷ (scs + # 1) ∷ [] □ ++
    ¶ cs ≥ 1 ⇒
        (out + # 1) ∷ (cs ∸ # 1) ∷ scs ∷ [] □ ++
    ¶ scs ≥ 1 ⇒
        (out + # 1) ∷ cs ∷ (scs ∸ # 1) ∷ [] □ ++
    []

  unsafe : Conf → Bool
  unsafe (out ∷ cs ∷ scs ∷ []) =
    cs ≥ 1 ∧ scs ≥ 1

open CntSc DataRace 3 10

-- Cographs

cograph : LazyCograph Conf
cograph = build-cograph start

cograph-safe : LazyCograph Conf
cograph-safe = cl∞-Ø $ cl∞-unsafe cograph

-- Removing empty subtrees while pruning.

lgraph-unsafe : LazyGraph Conf
lgraph-unsafe = pruneØ-cograph cograph

--#lgraph-unsafe : #⟪ lgraph-unsafe ⟫ ≡ 669
--#lgraph-unsafe = refl

--%lgraph-unsafe : %⟪ lgraph-unsafe ⟫ ≡ (669 , 15846)
--%lgraph-unsafe = refl


lgraph : LazyGraph Conf
lgraph = pruneØ-cograph cograph-safe

--#lgraph : #⟪ lgraph ⟫ ≡ 16
--#lgraph = refl

--%lgraph : %⟪ lgraph ⟫ ≡ (16 , 237)
--%lgraph = refl

lgraph-min-size = cl-min-size lgraph

%lgraph-min-size : %⟪ proj₂ lgraph-min-size ⟫ ≡ (1 , 6)
%lgraph-min-size = refl

graph-min-size = ⟪ proj₂ lgraph-min-size ⟫
