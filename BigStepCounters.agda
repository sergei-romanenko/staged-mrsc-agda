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
open import BarWhistles
open import Graphs
open import BigStepSc
open import Cographs

-- ℕω

data ℕω : Set where
  ω  : ℕω
  #_ : (i : ℕ) → ℕω

infixl 8 _+_ _∸_

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

infix 4 _≥#_ _≥#?_ _=#_ _=#?_

-- _≥_

data _≥#_ : (m : ℕω) (j : ℕ) → Set where
  ω≥j   : ∀ {j : ℕ} → ω ≥# j
  #i≥j : ∀ {i j : ℕ} → (i≥j : i N.≥ j) → # i ≥# j

-- _≥?_

_≥#?_ : Decidable₂ _≥#_

ω ≥#? j = yes ω≥j

# i ≥#? j with j N.≤? i
... | yes j≤i = yes (#i≥j j≤i)
... | no ¬j≤i = no helper
  where helper : # i ≥# j → ⊥
        helper (#i≥j i≥j) = ¬j≤i i≥j

-- _=#_

data _=#_ : (m : ℕω) (j : ℕ) → Set where
  ω=j   : ∀ {j} → ω =# j
  #i=i : ∀ {i} → # i =# i

-- #i=j→i≡j

#i=#j→i≡j : ∀ {i j} → # i =# j → i ≡ j
#i=#j→i≡j #i=i = refl

-- _=#?_

_=#?_ : Decidable₂ _=#_

ω =#? n = yes ω=j
# i =#? j with i N.≟ j
... | yes i≡j rewrite i≡j = yes #i=i
... | no  i≢j = no helper
  where helper : # i =# j → ⊥
        helper #i=j = i≢j (#i=#j→i≡j #i=j)

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

#i≡#j→i≡j : ∀ {i j} → # i ≡ # j → i ≡ j
#i≡#j→i≡j refl = refl

-- _≟ω_

infix 4 _≟ω_

_≟ω_ : Decidable₂ {A = ℕω} _≡_

ω ≟ω ω = yes refl
ω ≟ω # i = no (λ ())
# i ≟ω ω = no (λ ())
# i ≟ω # j with i N.≟ j
... | yes i≡j rewrite i≡j = yes refl
... | no  i≢j = no (i≢j ∘ #i≡#j→i≡j)

--
-- "Worlds of counters"
-- (To be converted to worlds of supercompilation.)
--

record CntWorld {k : ℕ} : Set₁ where
  constructor
    ⟨⟨_,_,_⟩⟩

  Conf : Set
  Conf = Vec ℕω k

  field

    -- Initial configuration
    start : Conf

    -- Driving (deterministic)
    _⇊ : (c : Conf) → List Conf

    -- Which configurations are (semantically) unsafe?
    unsafe : (c : Conf) → Bool

--
-- Converting a world of counters to a world of supercompilation.
--

module CntSc {k : ℕ} (cntWorld : CntWorld {k})
  (maxℕ : ℕ) (maxDepth : ℕ) where

  open CntWorld cntWorld public

  _≟Conf_ : Decidable₂ (_≡_ {A = Conf})

  c ≟Conf c′ with  Pointwise.decidable _≟ω_ c c′
  ... | yes PW-c≡c′ = yes (Equivalence.to Pointwise-≡ ⟨$⟩ PW-c≡c′)
  ... | no ¬PW-c≡c′ = no (¬PW-c≡c′ ∘ _⟨$⟩_ (Equivalence.from Pointwise-≡))

  -- _⊑_

  _⊑_ : (c c′ : Conf) → Set

  _⊑_ c c′ = Pointwise _⊑₁_ c c′

  -- _⊑?_

  _⊑?_ : Decidable₂ _⊑_
  _⊑?_ = Pointwise.decidable _⊑₁?_

  -- Rebuildings

  -- _↷₁

  _↷₁ : ∀ (n : ℕω) → List ℕω
  ω ↷₁ = ω ∷ []
  (# i) ↷₁ = ω ∷ # i ∷ []

  -- _↷ 

  _↷ : (c : Conf) → List Conf
  _↷ c = remove-c (vec-cartesian (Vec.map _↷₁ c))
    where remove-c = List.filter (λ c′ → ⌊ ¬? (c ≟Conf c′) ⌋)

  -- TooBig₁

  TooBig₁ : (n : ℕω) → Set
  TooBig₁ ω = ⊥
  TooBig₁ (# i) = maxℕ N.≤ i

  -- tooBig₁?

  tooBig₁? : Decidable₁ TooBig₁
  tooBig₁? ω = no id
  tooBig₁? (# i) = maxℕ N.≤? i

  -- TooBig

  TooBig : (c : Conf) → Set
  TooBig c = Any TooBig₁ (Vec.toList c)

  tooBig? : Decidable₁ TooBig
  tooBig? c = Any.any tooBig₁? (Vec.toList c)


  mkScWorld : (cntWorld : CntWorld {k}) → ScWorld
  mkScWorld ⟨⟨ start , _⇊ , unsafe ⟩⟩ = record
    { Conf = Conf
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

    ↯ : ∀ (h : List Conf) → Set

    ↯ [] = ⊥
    ↯ (c ∷ h) = TooBig c ⊎ ↯ h

    ↯? : Decidable₁ ↯
    ↯? [] = no id
    ↯? (c ∷ h) with ↯? h
    ... | yes dh = yes (inj₂ dh)
    ... | no ¬dh with tooBig? c
    ... | yes tb = yes (inj₁ tb)
    ... | no ¬tb = no [ ¬tb , ¬dh ]′

    -- The whistle is based on the combination of `pathLengthWhistle` and
    -- and `↯`.

    -- TODO: It is possible to construct a whistle based on the fact that
    -- the set of configurations such that `¬ TooBig l c` is finite.

    bar[] : Bar (λ h → maxDepth N.≤ List.length h ⊎ ↯ h) []
    bar[] = bar-⊎ [] (BarWhistle.bar[] (pathLengthWhistle Conf maxDepth))


  scWorld : ScWorld
  scWorld = mkScWorld cntWorld

  open BigStepMRSC scWorld public
  open BigStepMRSC∞ scWorld public
  open BigStepMRSC∞-Ø scWorld public

  cl-unsafe : ∀ (l : LazyGraph Conf) → LazyGraph Conf
  cl-unsafe = cl-bad-conf unsafe

  cl∞-unsafe : ∀ (l : LazyCograph Conf) → LazyCograph Conf
  cl∞-unsafe = cl∞-bad-conf unsafe


--
-- A "DSL" for encoding counter systems in a user-friendly form.
--

infix 7 _≥_ _==_
infix 5 ¶_⇒_□

-- _≥_

_≥_ : ∀ (m : ℕω) (j : ℕ) → Bool
m ≥ n =
  ⌊ m ≥#? n ⌋

-- _==_

_==_ : ∀ (m : ℕω) (j : ℕ) → Bool

m == j =
  ⌊ m =#? j ⌋

-- _⇒_□

¶_⇒_□ : ∀ {k} (p : Bool) (result : Vec ℕω k) → List (Vec ℕω k)

¶ p ⇒ r □ =
  if p then r ∷ [] else []
