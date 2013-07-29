module AlmostFullRel where

open import Level
  using ()

open import Data.Product as Prod
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃; ∃₂)
open import Data.Sum as Sum
  using (_⊎_; inj₁; inj₂; [_,_]′)

open import Function.Equivalence
  using (_⇔_; equivalence)

open import Relation.Binary
  using (Rel; _⇒_) renaming (Decidable to Decidable₂)


--
-- Almost-full relations
--

data Almost-full {ℓ} {A : Set ℓ} : Rel A ℓ → Set (Level.suc ℓ) where
  now   : ∀ {_≫_} → (z : ∀ x y → x ≫ y) →
               Almost-full _≫_
  later : ∀ {_≫_} → (s : ∀ c → Almost-full (λ x y → x ≫ y ⊎ c ≫ x)) →
               Almost-full _≫_

-- af-⇒

af-⇒ : 
  ∀ {ℓ} {A : Set ℓ} {P Q : Rel A ℓ} →
    (p⇒q : P ⇒ Q) →
    (af : Almost-full P) → Almost-full Q

af-⇒ p⇒q (now z) =
  now (λ x y → p⇒q (z x y))
af-⇒ p⇒q (later s) =
  later (λ c → af-⇒ (Sum.map p⇒q p⇒q) (s c))

--
-- Well-founded trees
--

data WFT {ℓ} (A  :  Set ℓ) : Set ℓ where 
  now   : WFT A
  later : (s : A → WFT A) → WFT A

--
-- _⟱_ (secure by)
-- The tree can be separated from the relation.
--
-- (This is a form of "staging", a wft being a "program" that
-- transforms a relation.)
--

infix 4 _⟱_

-- _⟱_

_⟱_ : ∀ {ℓ} {A : Set ℓ} (_≫_ : Rel A ℓ) (t :  WFT A) → Set ℓ
_≫_ ⟱ now = ∀ x y → x ≫ y
_≫_ ⟱ later g = ∀ c → (λ x y → x ≫ y ⊎ c ≫ x) ⟱ g c

-- Almost-full⟱

Almost-full⟱ : ∀ {ℓ} {A : Set ℓ} (R : Rel A ℓ) → Set ℓ
Almost-full⟱ {A = A} R = Σ (WFT A) (λ t → R ⟱ t)

-- af⟱→af

af⟱→af : ∀ {ℓ} {A : Set ℓ} {R : Rel A ℓ} → Almost-full⟱ R → Almost-full R

af⟱→af (now , R⟱) =
  now R⟱
af⟱→af (later s , R⟱) = later (λ c → af⟱→af (s c , R⟱ c))

-- af→af⟱

af→af⟱ : ∀ {ℓ} {A : Set ℓ} {R : Rel A ℓ} → Almost-full R → Almost-full⟱ R

af→af⟱ (now z) =
  now , z
af→af⟱ {R = R} (later s) =
  later (λ c → proj₁ (af→af⟱ (s c))) , (λ c → proj₂ (af→af⟱ (s c)))

-- af⟱⇔af

af⟱⇔af : ∀ {ℓ} {A : Set ℓ} {R : Rel A ℓ} → Almost-full⟱ R ⇔ Almost-full R

af⟱⇔af = equivalence af⟱→af af→af⟱

