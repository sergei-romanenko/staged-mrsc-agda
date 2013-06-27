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

open import Level
  using (Level; _⊔_)
open import Data.Nat
  hiding(_⊔_)
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.Vec as Vec
  using (Vec; []; _∷_; lookup)
open import Relation.Binary.Vec.Pointwise
  using (Pointwise′; []; _∷_)
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty

open import Function

open import Relation.Nullary
open import Relation.Unary
  using (Decidable)
open import Relation.Binary
  using (Setoid; DecSetoid)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl)

-- AnyV

AnyV : ∀ {n a ℓ} {A : Set a} (P : A → Set ℓ) (xs : Vec A n) → Set ℓ
AnyV P xs = ∃ λ i → P (lookup i xs) 

-- anyV

anyV : ∀ {n a p} {A : Set a} {P : A → Set p} →
  Decidable P → Decidable (AnyV {n} P)

anyV {P = P} dp [] = no helper
  where helper : AnyV P [] → ⊥
        helper (() , _)

anyV {P = P} dp (x ∷ xs) with dp x
... | yes px = yes (zero , px)
... | no ¬px with anyV dp xs
... | yes (i , py) = yes (suc i , py)
... | no ¬ipy = no helper
  where helper : AnyV P (x ∷ xs) → ⊥
        helper (zero , px) = ¬px px
        helper (suc i , py) = ¬ipy (i , py)

-- ScWorld

record ScWorld : Set₁ where

  field

    -- Configurations.
    Conf : Set

    -- The equality of configurations is decidable.
    _≟Conf_ : (c₁ c₂ : Conf) → Dec (c₁ ≡ c₂)

    -- c ⊑ c′ means that c′ is more general than c.
    _⊑_ : (c c′ : Conf) → Set

    -- ⊑ is decidable.
    _⊑?_ : (c c′ : Conf) → Dec (c ⊑ c′)

    -- Contractions (currently they are not taken into account).
    --Contr : Set

    -- Driving a configuration leads to a finite number of new ones.
    _⇉ : (c : Conf) → ∃ λ k → Vec Conf k

    -- Rebuilding a configuration replaces it with an equivalent one.
    -- We suppose that the number of possible rebuildings is finite!
    _↴ : (c : Conf) → ∃ λ k → Vec Conf k


  conf-setoid : Setoid _ _
  conf-setoid = P.setoid Conf

  conf-decSetoid : DecSetoid _ _
  conf-decSetoid = P.decSetoid _≟Conf_

  History : ℕ → Set
  History n = Vec Conf n

  Foldable : ∀ {n} (h : History n) (c : Conf) → Set
  Foldable {n} h c = AnyV (_⊑_ c) h

  foldable? : ∀ {n} (h : History n) (c : Conf) → Dec (Foldable h c)
  foldable? h c = anyV (_⊑?_ c) h

  data Graph : (n : ℕ) → Set where
    case    : ∀ {n k} (c : Conf) (gs : Vec (Graph (suc n)) k) → Graph n
    back    : ∀ {n} (c : Conf) (b : Fin n) → Graph n
    rebuild : ∀ {n} (c : Conf) (g : Graph (suc n)) → Graph n

-- Bar

data Bar {A : Set} (D : ∀ {m} → Vec A m → Set) :
         {n : ℕ} (h : Vec A n) → Set where
  here  : ∀ {n} {h : Vec A n} (bz : D h) → Bar D h
  there : ∀ {n} {h : Vec A n} (bs : ∀ a → Bar D (a ∷ h)) → Bar D h


-- WhistleWorld

record WhistleWorld (scWorld : ScWorld) : Set₁ where
  open ScWorld scWorld

  field

    -- Dangerous histories
    Dangerous : ∀ {n} (h : History n) → Set
    dangerous? : ∀ {n} (h : History n) → Dec (Dangerous h)

    -- Bar-induction
    bar[] : Bar Dangerous []


-- BigStepNDSC

module BigStepNDSC (scWorld : ScWorld) where

  open ScWorld scWorld

  infix 4 _⊢NDSC_↪_

  data _⊢NDSC_↪_ : {n : ℕ}
    (h : History n) (c : Conf) (g : Graph n) → Set where
    ndsc-fold  : ∀ {n} {h : History n} {c}
      (f : Foldable h c) →
      h ⊢NDSC c ↪ back c (proj₁ f)
    ndsc-drive : ∀ {n h c k}
      {cs : Vec Conf k} {gs : Vec (Graph (suc n)) k}
      (ds : c ⇉ ≡ k , cs) →
      --(∀ i → c ∷ h ⊢NDSC (lookup i cs) ↪ (lookup i gs)) →
      Pointwise′ (_⊢NDSC_↪_ (c ∷ h)) cs gs →
      h ⊢NDSC c ↪ (case c gs)
    ndsc-rebuild : ∀ {n h c k}
      {cs : Vec Conf k} {g : Graph (suc n)}
      (r : c ↴ ≡ k , cs)
      (i : Fin k) →
      c ∷ h ⊢NDSC (lookup i cs) ↪ g →
      h ⊢NDSC c ↪ rebuild c g

-- ScWorld3

module ScWorld3 where

  -- This is a silly world with 3 possible configurations.
  -- (Just for testing.)

  data Conf3 : Set where
    c0 c1 c2 : Conf3

  _≟Conf3_ : (c c′ : Conf3) → Dec (c ≡ c′)
  c0 ≟Conf3 c0 = yes refl
  c0 ≟Conf3 c1 = no (λ ())
  c0 ≟Conf3 c2 = no (λ ())
  c1 ≟Conf3 c0 = no (λ ())
  c1 ≟Conf3 c1 = yes refl
  c1 ≟Conf3 c2 = no (λ ())
  c2 ≟Conf3 c0 = no (λ ())
  c2 ≟Conf3 c1 = no (λ ())
  c2 ≟Conf3 c2 = yes refl

  _⇉′ : (c : Conf3) → (∃ λ k → Vec Conf3 k)

  c0 ⇉′ = , c1 ∷ c2 ∷ []
  c1 ⇉′ = , c0 ∷ []
  c2 ⇉′ = , c1 ∷ []

  _↴′ : (c : Conf3) → (∃ λ k → Vec Conf3 k)
  c0 ↴′ = , c1 ∷ []
  _ ↴′ = , []

  scWorld3 : ScWorld
  scWorld3 = record
    { Conf = Conf3
    ; _≟Conf_ = _≟Conf3_
    ; _⊑_ = _≡_
    ; _⊑?_ = _≟Conf3_
    ; _⇉ = _⇉′
    ; _↴ = _↴′
    }


-- Whistle3

module Whistle3 where

  open ScWorld3
  open ScWorld scWorld3

  Dangerous3 : ∀ {n} (h : History n) → Set
  Dangerous3 {n} h = 4 ≤ n

  dangerous3? : ∀ {n} (h : History n) → Dec (Dangerous3 h)
  dangerous3? {n} h = 4 ≤? n

  bar[]3 : ∀ {n} (h : History n) → Bar Dangerous3 h
  bar[]3 h =
    there (λ a →
      there (λ a₁ →
        there (λ a₂ →
          there (λ a₃ →
            here (s≤s (s≤s (s≤s (s≤s z≤n))))))))

  whistleWorld3 : WhistleWorld scWorld3
  whistleWorld3 = record
    { Dangerous = Dangerous3
    ; dangerous? = dangerous3?;
    bar[] = bar[]3 [] }
  

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
    ndsc-drive refl
      ((ndsc-drive refl
        ((ndsc-fold (suc zero , refl)) ∷ [])) ∷
      (ndsc-drive refl
        ((ndsc-drive refl
          ((ndsc-fold (suc (suc zero) , refl)) ∷ []))
        ∷ [])) ∷ [])

  w3graph2 : [] ⊢NDSC c0 ↪
    rebuild c0 (case c1 (back c0 (suc zero) ∷ []))
  w3graph2 =
    ndsc-rebuild refl zero
      (ndsc-drive refl ((ndsc-fold (suc zero , refl)) ∷ []))


--
-- Extracting the residual graph from a proof
--

module GraphExtraction (scWorld : ScWorld) where
  open ScWorld scWorld
  open BigStepNDSC scWorld

  -- getGraph

  getGraph : ∀ {n} {h : History n} {c : Conf} {g : Graph n}
    (p : h ⊢NDSC c ↪ g) → Graph n

  getGraph (ndsc-fold {c = c} (i , c⊑c′)) = back c i
  getGraph (ndsc-drive {c = c} {gs = gs} ds ps) = case c gs
  getGraph (ndsc-rebuild {c = c} {g = g} r i p) = rebuild c g

  -- getGraph-sound

  getGraph-sound : ∀ {n} {h : History n} {c : Conf} {g : Graph n}
    (p : h ⊢NDSC c ↪ g) → getGraph p ≡ g

  getGraph-sound (ndsc-fold f) = refl
  getGraph-sound (ndsc-drive ds x) = refl
  getGraph-sound (ndsc-rebuild r i p) = refl
