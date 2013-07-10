module BigStepScTests where

open import Data.Nat
open import Data.List as List
open import Data.List.Any
  using (Any; here; there)
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.Vec as Vec
  using (Vec; []; _∷_; lookup)
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃)
open import Relation.Binary.List.Pointwise
  using ([]; _∷_)
  renaming (Rel to Pointwise)
open import Data.Empty

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to [_]ⁱ)

open import Graphs
open import BarWhistles
open import BigStepSc


-- ScWorld3

module ScWorld3 where

  -- This is a silly world with 3 possible configurations.
  -- (Just for testing.)

  data C3 : Set where
    c0 c1 c2 : C3

  _≟C3_ : (c c′ : C3) → Dec (c ≡ c′)
  c0 ≟C3 c0 = yes refl
  c0 ≟C3 c1 = no (λ ())
  c0 ≟C3 c2 = no (λ ())
  c1 ≟C3 c0 = no (λ ())
  c1 ≟C3 c1 = yes refl
  c1 ≟C3 c2 = no (λ ())
  c2 ≟C3 c0 = no (λ ())
  c2 ≟C3 c1 = no (λ ())
  c2 ≟C3 c2 = yes refl

  _⇉′ : (c : C3) → List C3

  c0 ⇉′ = c1 ∷ c2 ∷ []
  c1 ⇉′ = c0 ∷ []
  c2 ⇉′ = c1 ∷ []

  _↴′ : (c : C3) → List C3
  c0 ↴′ = c1 ∷ []
  _ ↴′  = []


  scWorld3 : ScWorld
  scWorld3 = record
    { Conf = C3
    ; _≟Conf_ = _≟C3_
    ; _⊑_ = _≡_
    ; _⊑?_ = _≟C3_
    ; _⇉ = _⇉′
    ; _↴ = _↴′
    ; whistle = pathLengthWhistle C3 4
    }


-- NDSC-test3

module NDSC-test3 where

  open ScWorld3
  open ScWorld scWorld3
  open BigStepNDSC scWorld3

  w3graph1 : [] ⊢NDSC c0 ↪
    case c0
      (case c1 (back c0 (suc zero) ∷ []) ∷
        case c2
          (case c1 (back c0 (suc (suc zero)) ∷ []) ∷ []) ∷ [])
  w3graph1 =
    ndsc-drive ¬f1
      ((ndsc-drive ¬f2
        ((ndsc-fold (suc zero , refl)) ∷ [])) ∷
      (ndsc-drive ¬f3
        ((ndsc-drive ¬f4
          ((ndsc-fold (suc (suc zero) , refl)) ∷ []))
        ∷ [])) ∷ [])
    where
    ¬f1 : ¬ Σ (Fin zero) (λ z → c0 ≡ lookup z [])
    ¬f1 (() , _)
    ¬f2 : ¬ Σ (Fin (suc zero)) (λ z → c1 ≡ lookup z (c0 ∷ []))
    ¬f2 (zero , ())
    ¬f2 (suc () , _)
    ¬f3 : ¬ Σ (Fin (suc zero)) (λ z → c2 ≡ lookup z (c0 ∷ []))
    ¬f3 (zero , ())
    ¬f3 (suc () , _)
    ¬f4 : ¬ Σ (Fin (suc (suc zero))) (λ z → c1 ≡ lookup z (c2 ∷ c0 ∷ []))
    ¬f4 (zero , ())
    ¬f4 (suc zero , ())
    ¬f4 (suc (suc ()) , _)

  w3graph2 : [] ⊢NDSC c0 ↪
    rebuild c0 (case c1 (back c0 (suc zero) ∷ []))
  w3graph2 =
    ndsc-rebuild ¬f1 (here refl)
      (ndsc-drive ¬f2 ((ndsc-fold (suc zero , refl)) ∷ []))
    where
    ¬f1 : Σ (Fin zero) (λ z → c0 ≡ lookup z []) → ⊥
    ¬f1 (() , _)
    ¬f2 : Σ (Fin (suc zero)) (λ z → c1 ≡ lookup z (c0 ∷ [])) → ⊥
    ¬f2 (zero , ())
    ¬f2 (suc () , _)

