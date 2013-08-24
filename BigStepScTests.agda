module BigStepScTests where

open import Data.Nat
open import Data.List as List
open import Data.List.Any
  using (Any; here; there; module Membership-≡)
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃)
open import Relation.Binary.List.Pointwise
  using ([]; _∷_)
  renaming (Rel to Pointwise)
open import Data.Empty

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to P[_])

open Membership-≡

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

  _↷′ : (c : C3) → List C3
  c0 ↷′ = c1 ∷ []
  _ ↷′  = []


  scWorld3 : ScWorld
  scWorld3 = record
    { Conf = C3
    ; _⊑_ = _≡_
    ; _⊑?_ = _≟C3_
    ; _⇉ = λ c → [ c ⇉′ ] ++ map [_] (c ↷′)
    ; whistle = pathLengthWhistle C3 4
    }


-- NDSC-test3

module NDSC-test3 where

  open ScWorld3
  open ScWorld scWorld3
  open BigStepNDSC scWorld3

  w3graph1 : [] ⊢NDSC c0 ↪
    forth c0
      (forth c1 [ back c0 ] ∷
       forth c2 [ forth c1 [ back c0 ] ] ∷ [])
  w3graph1 =
    ndsc-build ¬f1 (here refl)
      (ndsc-build ¬f2 (here refl)
        (ndsc-fold (there (here refl)) ∷ []) ∷
      (ndsc-build ¬f3 (here refl)
        (ndsc-build ¬f4 (here refl)
          (ndsc-fold (there (there (here refl))) ∷ []) ∷ [])) ∷ [])      
    where
    ¬f1 : c0 ∈ [] → ⊥
    ¬f1 ()
    ¬f2 : c1 ∈ c0 ∷ [] → ⊥
    ¬f2 (here ())
    ¬f2 (there ())
    ¬f3 : c2 ∈ c0 ∷ [] → ⊥
    ¬f3 (here ())
    ¬f3 (there ())
    ¬f4 : c1 ∈ c2 ∷ c0 ∷ [] → ⊥
    ¬f4 (here ())
    ¬f4 (there (here ()))
    ¬f4 (there (there ()))

  w3graph2 : [] ⊢NDSC c0 ↪
    forth c0 [ forth c1 (back c0 ∷ [])]
  w3graph2 =
    ndsc-build ¬f1 (there (here refl))
      (ndsc-build ¬f2 (here refl)
        (ndsc-fold (there (here refl)) ∷ []) ∷ [])
    where
    ¬f1 : c0 ∈ [] → ⊥
    ¬f1 ()
    ¬f2 : c1 ∈ c0 ∷ [] → ⊥
    ¬f2 (here ())
    ¬f2 (there ())

