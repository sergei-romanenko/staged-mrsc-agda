module BigStepCounters where

open import Data.Nat as N
  using (ℕ; zero; suc)
open import Data.Nat.Properties as NP
  using (≤-step)
open import Data.List as List
  using (List; []; _∷_; [_])
open import Data.List.Any as Any
  using (Any; here; there; module Membership-≡)
open import Data.Vec as Vec
  using (Vec; []; _∷_)
open import Relation.Binary.Vec.Pointwise as Pointwise
  using (Pointwise; Pointwise-≡)
open import Data.Bool as Bool
  using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.Empty
open import Data.Unit
  using (⊤; tt)
open import Data.Sum
  using (_⊎_; inj₁; inj₂; [_,_]′)

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
open import Relation.Nullary.Sum

open import Relation.Unary
  using () renaming (Decidable to Decidable₁)
open import Relation.Binary
  using (Rel) renaming (Decidable to Decidable₂)
open import Relation.Binary.PropositionalEquality
  renaming ([_] to P[_])

open import Util
open import Graphs
open import BigStepSc
open import BarWhistles

-- ℕω

data ℕω : Set where
  ω  : ℕω
  #_ : (i : ℕ) → ℕω

infixl 6 _+_ _∸_

-- _+_

_+_ : (m n : ℕω) → ℕω

ω + n = ω
m + ω = ω
# i + # j = # (i N.+ j)

-- _∸_

_∸_ : (m n : ℕω) → ℕω

ω ∸ n = ω
m ∸ ω = ω
# i ∸ # j = # (i N.∸ j)

infix 4 _≥_ _≥?_ _▹ω_ _▹ω?_

-- _≥_

data _≥_ : (m : ℕω) (j : ℕ) → Set where
  ω≥j   : ∀ {j : ℕ} → ω ≥ j
  #i≥j : ∀ {i j : ℕ} → (i≥j : i N.≥ j) → # i ≥ j

-- _≥?_

_≥?_ : Decidable₂ _≥_

ω ≥? j = yes ω≥j

# i ≥? j with j N.≤? i
... | yes j≤i = yes (#i≥j j≤i)
... | no ¬j≤i = no helper
  where helper : # i ≥ j → ⊥
        helper (#i≥j i≥j) = ¬j≤i i≥j

-- _▹ω_

data _▹ω_ : (m : ℕω) (j : ℕ) → Set where
  ω=j   : ∀ {j} → ω ▹ω j
  #i=i : ∀ {i} → # i ▹ω i

-- #i=j→i≡j

#i▹ωj→i≡j : ∀ {i j} → # i ▹ω j → i ≡ j
#i▹ωj→i≡j #i=i = refl

-- _▹ω?_

_▹ω?_ : Decidable₂ _▹ω_

ω ▹ω? n = yes ω=j
# i ▹ω? j with i N.≟ j
... | yes i≡j rewrite i≡j = yes #i=i
... | no  i≢j = no helper
  where helper : # i ▹ω j → ⊥
        helper #i=j = i≢j (#i▹ωj→i≡j #i=j)

-- m ⊑₁ n means that n is more general than m.

-- _⊑₁_

data _⊑₁_ : (m n : ℕω) → Set where
  m⊑₁ω : ∀ {m} → m ⊑₁ ω
  #i⊑₁#i : ∀ {i} → # i ⊑₁ # i

-- #i⊑₁#j→i≡j

#i⊑₁#j→i≡j : ∀ {i j} → # i ⊑₁ # j → i ≡ j
#i⊑₁#j→i≡j #i⊑₁#i = refl

-- _⊑₁?_

_⊑₁?_ : Decidable₂ _⊑₁_

m ⊑₁? ω =
  yes m⊑₁ω
ω ⊑₁? # i =
  no (λ ())
# i ⊑₁? # j with i N.≟ j
... | yes i≡j rewrite i≡j = yes #i⊑₁#i
... | no  i≢j = no helper
  where helper : # i ⊑₁ # j → ⊥
        helper #i⊑₁#j = i≢j (#i⊑₁#j→i≡j #i⊑₁#j)

infix 4 _≟ω_

#i≡#j→i≡j : ∀ {i j} → # i ≡ # j → i ≡ j
#i≡#j→i≡j refl = refl

-- _≟ω_

_≟ω_ : Decidable₂ {A = ℕω} _≡_

ω ≟ω ω = yes refl
ω ≟ω # i = no (λ ())
# i ≟ω ω = no (λ ())
# i ≟ω # j with i N.≟ j
... | yes i≡j rewrite i≡j = yes refl
... | no  i≢j = no (i≢j ∘ #i≡#j→i≡j)

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

-- _↷₁

_↷₁ : ∀ (n : ℕω) → List ℕω
ω ↷₁ = ω ∷ []
(# i) ↷₁ = ω ∷ # i ∷ []

-- _↷ 

_↷ : ∀ {k} (c : ωConf k) → List (ωConf k)
_↷ {k} c = remove-c (vec-cartesian (Vec.map _↷₁ c))
  where remove-c = List.filter (λ c′ → ⌊ ¬? (c ≟ωConf c′) ⌋)

record CntWorld (k : ℕ) : Set₁ where
  constructor
    ⟨⟨_,_,_⟩⟩
  field

    start : ωConf k

    -- Driving (deterministic)
    _⇊ : (c : ωConf k) → List (ωConf k)

    unsafe : (c : ωConf k) → Bool

  cl-unsafe : ∀ (l : LazyGraph (ωConf k)) → LazyGraph (ωConf k)
  cl-unsafe = cl-empty&bad unsafe

-- TooBig₁

TooBig₁ : ∀ (l : ℕ) (n : ℕω) → Set
TooBig₁ l ω = ⊥
TooBig₁ l (# i) = l N.≤ i

-- tooBig₁?

tooBig₁? : ∀ (l : ℕ) → Decidable₁ (TooBig₁ l)
tooBig₁? l ω = no id
tooBig₁? l (# i) = l N.≤? i

-- TooBig

TooBig : ∀ (l : ℕ) {k} (c : ωConf k) → Set
TooBig l {k} c = Any (TooBig₁ l) (Vec.toList c)

tooBig? : ∀ (l : ℕ) {k} → Decidable₁ (TooBig l {k})
tooBig? l {k} c = Any.any (tooBig₁? l) (Vec.toList c)


mkScWorld : ∀ (l : ℕ) (maxDepth : ℕ) {k} (cntWorld : CntWorld k) → ScWorld
mkScWorld l maxDepth {k} ⟨⟨ start , _⇊ , unsafe ⟩⟩ = record
  { Conf = ωConf k
  ; _⊑_ = _⊑_
  ; _⊑?_ = _⊑?_
  ; _⇉ = λ c → c ⇊ ∷ List.map [_] (c ↷) -- driving + rebuilding
  ; whistle = ⟨ (λ h → (maxDepth N.≤ List.length h) ⊎ (↯ h))
              , (λ c h → [ inj₁ ∘ ≤-step , inj₂ ∘ inj₂ ]′)
              , (λ h → (maxDepth N.≤? List.length h) ⊎-dec (↯? h))
              , bar[]
              ⟩
  }
  where

  ↯ : ∀ (h : List (ωConf k)) → Set

  ↯ [] = ⊥
  ↯ (c ∷ h) = TooBig l c ⊎ ↯ h

  ↯? : Decidable₁ ↯
  ↯? [] = no id
  ↯? (c ∷ h) with ↯? h
  ... | yes dh = yes (inj₂ dh)
  ... | no ¬dh with tooBig? l c
  ... | yes tb = yes (inj₁ tb)
  ... | no ¬tb = no [ ¬tb , ¬dh ]′

  -- The whistle is based on the combination of `pathLengthWhistle` and
  -- and `↯`.

  -- TODO: It is possible to construct a whistle based on the fact that
  -- the set of configurations such that `¬ TooBig l c` is finite.

  bar[] : Bar (λ h → maxDepth N.≤ List.length h ⊎ ↯ h) []
  bar[] = bar-⊎ [] (BarWhistle.bar[] (pathLengthWhistle (ωConf k) maxDepth))

--
-- A "DSL" for encoding counter systems in a user-friendly form.
--

-- ¶_≥_⇒_□

¶_≥_⇒_□ : ∀ {k} (m : ℕω) (j : ℕ) (result : ωConf k) → List (ωConf k)

¶ m ≥ j ⇒ r □ =
  if ⌊ m ≥? j ⌋ then r ∷ [] else []

-- ¶_≥_□

¶?_≥_□ : ∀ (m : ℕω) (j : ℕ) → Bool
¶? m ≥ n □ =
  ⌊ m ≥? n ⌋

-- ¶_≥_∧_≥_□

¶?_≥_∧_≥_□ : ∀ (m : ℕω) (j : ℕ)(m′ : ℕω) (j′ : ℕ) → Bool
¶? m ≥ j ∧ m′ ≥ j′ □ =
  ⌊ m ≥? j ⌋ ∧ ⌊ m′ ≥? j′ ⌋
