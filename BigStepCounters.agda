module BigStepCounters where

open import Data.Nat as N
  using (ℕ; zero; suc)
open import Data.Nat.Properties as NP
  using ()
open import Data.List as List
  using (List; []; _∷_)
open import Data.Vec as Vec
  using (Vec; []; _∷_)
open import Relation.Binary.Vec.Pointwise as Pointwise
  using (Pointwise; Pointwise-≡)
open import Data.Empty

open import Function
open import Function.Equivalence as FEQV
  using (module Equivalence)
open import Function.Equality as FEQU
  using (_⟨$⟩_)

open import Relation.Nullary
open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Relation.Nullary.Negation
  using (¬?)
open import Relation.Unary
  using () renaming (Decidable to Decidable₁)
open import Relation.Binary
  using (Rel) renaming (Decidable to Decidable₂)
open import Relation.Binary.PropositionalEquality
  renaming ([_] to [_]ⁱ)

open import Util

-- ℕω

data ℕω : Set where
  ω : ℕω
  ⟨_⟩ : (i : ℕ) → ℕω

infixl 6 _+_ _∸_

-- _+_

_+_ : (m n : ℕω) → ℕω

ω + n = ω
m + ω = ω
⟨ i ⟩ + ⟨ j ⟩ = ⟨ i N.+ j ⟩

-- _∸_

_∸_ : (m n : ℕω) → ℕω

ω ∸ n = ω
m ∸ ω = ω
⟨ i ⟩ ∸ ⟨ j ⟩ = ⟨ i N.∸ j ⟩

infix 4 _≥_ _≥?_ _▹ω_ _▹ω?_

-- _≥_

data _≥_ : (m : ℕω) (j : ℕ) → Set where
  ω≥j   : ∀ {j : ℕ} → ω ≥ j
  ⟨i⟩≥j : ∀ {i j : ℕ} → (i≥j : i N.≥ j) → ⟨ i ⟩ ≥ j

-- _≥?_

_≥?_ : Decidable₂ _≥_

ω ≥? j = yes ω≥j

⟨ i ⟩ ≥? j with j N.≤? i
... | yes j≤i = yes (⟨i⟩≥j j≤i)
... | no ¬j≤i = no helper
  where helper : ⟨ i ⟩ ≥ j → ⊥
        helper (⟨i⟩≥j i≥j) = ¬j≤i i≥j

-- _▹ω_

data _▹ω_ : (m : ℕω) (j : ℕ) → Set where
  ω=j   : ∀ {j} → ω ▹ω j
  ⟨i⟩=i : ∀ {i} → ⟨ i ⟩ ▹ω i

-- ⟨i⟩=j→i≡j

⟨i⟩=j→i≡j : ∀ {i j} → ⟨ i ⟩ ▹ω j → i ≡ j
⟨i⟩=j→i≡j ⟨i⟩=i = refl

-- _▹ω?_

_▹ω?_ : Decidable₂ _▹ω_

ω ▹ω? n = yes ω=j
⟨ i ⟩ ▹ω? j with i N.≟ j
... | yes i≡j rewrite i≡j = yes ⟨i⟩=i
... | no  i≢j = no helper
  where helper : ⟨ i ⟩ ▹ω j → ⊥
        helper ⟨i⟩=j = i≢j (⟨i⟩=j→i≡j ⟨i⟩=j)

-- m ⊑₁ n means that n is more general than m.

-- _⊑₁_

data _⊑₁_ : (m n : ℕω) → Set where
  m⊑₁ω : ∀ {m} → m ⊑₁ ω
  ⟨i⟩⊑₁⟨i⟩ : ∀ {i} → ⟨ i ⟩ ⊑₁ ⟨ i ⟩

-- ⟨i⟩⊑₁⟨j⟩→i≡j

⟨i⟩⊑₁⟨j⟩→i≡j : ∀ {i j} → ⟨ i ⟩ ⊑₁ ⟨ j ⟩ → i ≡ j
⟨i⟩⊑₁⟨j⟩→i≡j ⟨i⟩⊑₁⟨i⟩ = refl

-- _⊑₁?_

_⊑₁?_ : Decidable₂ _⊑₁_

m ⊑₁? ω =
  yes m⊑₁ω
ω ⊑₁? ⟨ i ⟩ =
  no (λ ())
⟨ i ⟩ ⊑₁? ⟨ j ⟩ with i N.≟ j
... | yes i≡j rewrite i≡j = yes ⟨i⟩⊑₁⟨i⟩
... | no  i≢j = no helper
  where helper : ⟨ i ⟩ ⊑₁ ⟨ j ⟩ → ⊥
        helper ⟨i⟩⊑₁⟨j⟩ = i≢j (⟨i⟩⊑₁⟨j⟩→i≡j ⟨i⟩⊑₁⟨j⟩)

infix 4 _≟ω_

⟨i⟩≡⟨j⟩→i≡j : ∀ {i j} → ⟨ i ⟩ ≡ ⟨ j ⟩ → i ≡ j
⟨i⟩≡⟨j⟩→i≡j refl = refl

-- _≟ω_

_≟ω_ : Decidable₂ {A = ℕω} _≡_

ω ≟ω ω = yes refl
ω ≟ω ⟨ i ⟩ = no (λ ())
⟨ i ⟩ ≟ω ω = no (λ ())
⟨ i ⟩ ≟ω ⟨ j ⟩ with i N.≟ j
... | yes i≡j rewrite i≡j = yes refl
... | no  i≢j = no (i≢j ∘ ⟨i⟩≡⟨j⟩→i≡j)

--
-- Configurations
--

ωConf : (k : ℕ) → Set
ωConf = Vec ℕω

_≟ωConf_ : ∀ {k} → Decidable₂ (_≡_ {A = ωConf k})
c ≟ωConf c′ with  Pointwise.decidable _≟ω_ c c′
... | yes PW-c≡c′ = yes (Equivalence.to Pointwise-≡ ⟨$⟩ PW-c≡c′)
... | no ¬PW-c≡c′ = no (¬PW-c≡c′ ∘ _⟨$⟩_ (Equivalence.from Pointwise-≡))

-- _⊑_

_⊑_ : ∀ {k} (c c′ : ωConf k) → Set

_⊑_ {k} c c′ = Pointwise _⊑₁_ c c′

-- _⊑?_

_⊑?_ : ∀ {k} → Decidable₂ (_⊑_ {k})
_⊑?_ = Pointwise.decidable _⊑₁?_

-- Rebuildings

-- _↴₁

_↴₁ : ∀ (n : ℕω) → List ℕω
ω ↴₁ = ω ∷ []
⟨ i ⟩ ↴₁ = ω ∷ ⟨ i ⟩ ∷ []

-- _↴ 

_↴ : ∀ {k} (c : ωConf k) → List (ωConf k)
--_↴ {k} c =  remove (vec-cartesian (Vec.map _↴₁ c))
_↴ {k} c = remove-c (vec-cartesian (Vec.map _↴₁ c))
  where remove-c = List.filter (λ c′ → ⌊ ¬? (c ≟ωConf c′) ⌋)
