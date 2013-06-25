module BigStepSc where

{- ### Schemes of different types of big-step supercompilation ### -}

{-
A variation of the scheme presented in the paper

Ilya G. Klyuchnikov, Sergei A. Romanenko. Formalizing and Implementing
Multi-Result Supercompilation.
In Third International Valentin Turchin Workshop on Metacomputation
(Proceedings of the Third International Valentin Turchin Workshop on
Metacomputation. Pereslavl-Zalessky, Russia, July 5-9, 2012).
A.V. Klimov and S.A. Romanenko, Ed. - Pereslavl-Zalessky: Ailamazyan
University of Pereslavl, 2012, 260 p. ISBN 978-5-901795-28-6, pages
142-164. 
-}

open import Data.Nat
open import Data.Fin as F
  using (Fin)
open import Data.Vec as Vec
  using (Vec; []; _∷_; lookup; zip)
open import Relation.Binary.Vec.Pointwise
  using (Pointwise′; []; _∷_)
open import Data.List
open import Data.List.All
  using (All; _∷_; [])
open import Data.List.Any as Any
  using (Any)
open import Data.Product
  using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.Empty
--open import Data.Maybe
--  using (Maybe)

open import Function

open import Relation.Nullary
open import Relation.Binary
  using (Setoid; DecSetoid)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_)


record ScWorld : Set₁ where

  field
    Conf : Set
    _≟Conf_ : (c₁ c₂ : Conf) → Dec (c₁ ≡ c₂)
    _⊑_ : (c c′ : Conf) → Set
    _⊑?_ : (c c′ : Conf) → Dec (c ⊑ c′)
    --Contr : Set
    -- Drive step
    _⇉_ : (c : Conf) {n : ℕ} (cs : Vec Conf n) → Set

  History : Set
  History = List Conf

  conf-setoid : Setoid _ _
  conf-setoid = P.setoid Conf

  conf-decSetoid : DecSetoid _ _
  conf-decSetoid = P.decSetoid _≟Conf_

  module conf-Membership = Any.Membership conf-setoid
  open conf-Membership

  Foldable : (h : History) (c : Conf) → Set
  Foldable h c = Any (_⊑_ c) h

  foldable? : (h : History) (c : Conf) → Dec (Foldable h c)
  foldable? h c = Any.any (_⊑?_ c) h

  data Graph : (h : History) → Set where
    case : ∀ {h n} (c : Conf) (gs : Vec (Graph (c ∷ h)) n) → Graph h
    back : ∀ {h} c (f : Foldable h c) → Graph h


record BigStepNDSC (scWorld : ScWorld) : Set₁ where

  open ScWorld scWorld

  infix 4 _⊢NDSC_↪_

  data _⊢NDSC_↪_ :
    (h : History) (c : Conf) (g : Graph h) → Set where
    ndsc-fold  : ∀ {h c} (f : Foldable h c) → h ⊢NDSC c ↪ back c f
    ndsc-drive : ∀ {h c n} {cs : Vec Conf n} {gs : Vec (Graph (c ∷ h)) n}
      (ds : c ⇉ cs) →
      --(∀ i → c ∷ h ⊢NDSC (lookup i cs) ↪ (lookup i gs)) →
      Pointwise′ (_⊢NDSC_↪_ (c ∷ h)) cs gs →
      h ⊢NDSC c ↪ (case c gs)

module NDSC-test3 where

  data Conf3 : Set where
    c0 c1 c2 : Conf3

  _≟Conf_ : (c c′ : Conf3) → Dec (c ≡ c′)
  c0 ≟Conf c0 = yes P.refl
  c0 ≟Conf c1 = no (λ ())
  c0 ≟Conf c2 = no (λ ())
  c1 ≟Conf c0 = no (λ ())
  c1 ≟Conf c1 = yes P.refl
  c1 ≟Conf c2 = no (λ ())
  c2 ≟Conf c0 = no (λ ())
  c2 ≟Conf c1 = no (λ ())
  c2 ≟Conf c2 = yes P.refl

  infix 4 _⇉′_

  data _⇉′_ : (c : Conf3) {n : ℕ} (cs : Vec Conf3 n) → Set where
    c0⇉c1c2 : c0 ⇉′ c1 ∷ c2 ∷ []
    c1⇉c0   : c1 ⇉′ c0 ∷ []
    c2⇉c1   : c2 ⇉′ c1 ∷ []

  w3 : ScWorld
  w3 = record
    { Conf = Conf3
    ; _≟Conf_ = _≟Conf_
    ; _⊑_ = _≡_
    ; _⊑?_ = _≟Conf_
    ; _⇉_ = _⇉′_
    }

  open ScWorld w3

  bs3r : BigStepNDSC w3
  bs3r = record { }
  open BigStepNDSC bs3r

  w3graph1 : [] ⊢NDSC c0 ↪
    case c0
      (case c1
        (back c0 (Any.there (Any.here P.refl)) ∷ []) ∷
          case c2
            (case c1 (back c0 (Any.there (Any.there (Any.here P.refl)))
              ∷ []) ∷ []) ∷ [])
  w3graph1 =
    ndsc-drive c0⇉c1c2
      (ndsc-drive c1⇉c0
        (ndsc-fold (Any.there (Any.here P.refl)) ∷ []) ∷
        ndsc-drive c2⇉c1
          (ndsc-drive c1⇉c0
            (ndsc-fold (Any.there (Any.there (Any.here P.refl))) ∷ []) ∷
          []) ∷ [])

