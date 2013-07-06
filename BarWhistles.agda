module BarWhistles where

open import Level
  using ()
open import Data.Nat
open import Data.Nat
  hiding(_⊔_)
open import Data.Nat.Properties
  using (≤′⇒≤; ≤⇒≤′; ≰⇒>)
open import Data.List as List
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.Vec as Vec
  using (Vec; []; _∷_; _∈_; here; there; lookup)
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃; ∃₂)
open import Data.Empty

open import Function

open import Relation.Nullary
open import Relation.Unary
  using () renaming (Decidable to Decidable₁)

open import Relation.Binary
  using (Rel) renaming (Decidable to Decidable₂)
open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to [_]ⁱ)

open import Induction.WellFounded


open import Util

-- Bar

-- The set of finite paths such that either
-- (1) B h is valid right now; or
-- (2) for all possible a₁ ∷ h either
--     (1) B (a₁ ∷ h) is valid right now; or
--     (2) for all possible a₂ ∷ a₁ ∷ h either ...

data Bar {A : Set} (B : ∀ {m} → Vec A m → Set) :
         {n : ℕ} (h : Vec A n) → Set where
  now   : ∀ {n} {h : Vec A n} (bz : B h) → Bar B h
  later : ∀ {n} {h : Vec A n} (bs : ∀ a → Bar B (a ∷ h)) → Bar B h


record BarWhistle (A : Set) : Set₁ where

  -- Bar whistles deal with sequences of some entities
  -- (which in our model of supercompilations are configurations).

  constructor
    ⟨_,_,_⟩
  field

    -- Dangerous histories
    Dangerous : ∀ {n} (h : Vec A n) → Set
    dangerous? : ∀ {n} (h : Vec A n) → Dec (Dangerous h)

    -- Bar-induction
    bar[] : Bar Dangerous []


-- BarGen

-- This module shows the generation of finite sequences
-- by means of a bar whistle.

module BarGen {A : Set} (g : ∀ {m} → Vec A m → A) (w : BarWhistle A) where

  open BarWhistle w

  barGen′ : ∀ {k} (h : Vec A k) (b : Bar Dangerous h) →
              ∃₂ λ n (h′ : Vec A n) → Dangerous h′
  barGen′ {k} h (now bz) = k , h , bz
  barGen′ {k} h (later bs) with g h
  ... | c = barGen′ (c ∷ h) (bs c)

  barGen : ∃₂ λ n (h : Vec A n) → Dangerous h
  barGen = barGen′ [] bar[]


-- A fan, or an finitely branching tree, is a tree
-- each node of which has a finite number of immediate successor nodes.

data Fan (A : Set) : Set where
  fan : List (A × Fan A) → Fan A

-- BarFanGen

-- This module shows the generation of finitely branching trees
-- by means of a bar whistle.

module BarFanGen
  {A : Set} (_⇉ : ∀ {k} → Vec A k → List A) (w : BarWhistle A)
  where
  open BarWhistle w

  fanGen′ : ∀ {k} (h : Vec A k) (b : Bar Dangerous h) → Fan A
  fanGen′ h (now bz) =
    fan []
  fanGen′ h (later bs) =
    fan (map (λ c → c , fanGen′ (c ∷ h) (bs c)) (h ⇉))

  fanGen : Fan A
  fanGen = fanGen′ [] bar[]

--
-- Bar whistles based on the length of the sequence
--

-- pathLengthWhistle

pathLengthWhistle : (A : Set) (l : ℕ) → BarWhistle A

pathLengthWhistle A l = ⟨ Dangerous , Dangerous? , bar[] ⟩
  where

  Dangerous : ∀ {n} (h : Vec A n) → Set
  Dangerous {n} h = l ≤ n

  Dangerous? : ∀ {n} (h : Vec A n) → Dec (Dangerous h)
  Dangerous? {n} h = l ≤? n

  bar : ∀ m n (h : Vec A n) (d : m + n ≡ l) → Bar Dangerous h
  bar zero .l h refl =
    now (≤′⇒≤ ≤′-refl)
  bar (suc m) n h d =
    later (λ c → bar m (suc n) (c ∷ h) m+1+n≡l)
    where
    open ≡-Reasoning
    m+1+n≡l = begin m + suc n ≡⟨ m+1+n≡1+m+n m n ⟩ suc (m + n) ≡⟨ d ⟩ l ∎

  bar[] : Bar Dangerous []
  bar[] = bar l zero [] (l + zero ≡ l ∋ proj₂ *+.+-identity l)

--
-- Bar whistles based on inverse image
--

-- inverseImageWhistle

inverseImageWhistle : {A B : Set} (f : A → B)
  (w : BarWhistle B) → BarWhistle A

inverseImageWhistle {A} {B} f ⟨ d , d? , bd[] ⟩ =
  ⟨ d ∘ Vec.map f , d? ∘ Vec.map f , bar [] bd[] ⟩
  where

  bar : ∀ {n} (h : Vec A n) (b : Bar d (Vec.map f h)) → Bar (d ∘ Vec.map f) h
  bar h (now bz) = now bz
  bar h (later bs) = later (λ c → bar (c ∷ h) (bs (f c)))

--
-- Bar whistles based on well-founded relations
--

-- wfWhistle

wfWhistle : ∀ {A : Set} (_<_ : Rel A Level.zero) → Decidable₂ _<_ →
              (wf : Well-founded _<_) → BarWhistle A
wfWhistle {A} _<_ _<?_ wf = ⟨ Dangerous , dangerous? , bar[] ⟩
  where

  Dangerous : ∀ {n} (h : Vec A n) → Set
  Dangerous [] = ⊥
  Dangerous (c ∷ []) = ⊥
  Dangerous (c′ ∷ c ∷ h) = ¬ c′ < c

  dangerous? : ∀ {n} (h : Vec A n) → Dec (Dangerous h)
  dangerous? [] = no id
  dangerous? (c ∷ []) = no id
  dangerous? (c′ ∷ c ∷ h) with c′ <? c
  ... | yes c′<c = no (λ c′≮c → c′≮c c′<c)
  ... | no  c′≮c = yes c′≮c

  bar : ∀ c {n} (h : Vec A n) → Acc _<_ c → Bar Dangerous (c ∷ h)
  bar c h (acc rs) with dangerous? (c ∷ h)
  ... | yes dch = now dch
  ... | no ¬dch = later helper
    where helper : ∀ c′ → Bar Dangerous (c′ ∷ c ∷ h)
          helper c′ with c′ <? c
          ... | yes c′<c = bar c′ (c ∷ h) (rs c′ c′<c)
          ... | no  c′≮c = now c′≮c

  bar[] : Bar Dangerous []
  bar[] = later (λ c → bar c [] (wf c))

--
-- Whistles based on the idea that some elements of the sequence
-- "cover" other elements.
-- c′ ⋑ c means that c′ "covers" c.
--

module ⊎⋑-Whistle
  {A : Set} (_⋑_ : A → A → Set) (_⋑?_ : Decidable₂ _⋑_)
  where

  -- ⊎⋑-Dangerous

  ⊎⋑-Dangerous : {n : ℕ} (h : Vec A n) → Set
  ⊎⋑-Dangerous [] = ⊥
  ⊎⋑-Dangerous (c ∷ h) = VecAny (flip _⋑_ c) h

  -- ⊎⋑-dangerous?

  ⊎⋑-dangerous? : {n : ℕ} (h : Vec A n) → Dec (⊎⋑-Dangerous h)
  ⊎⋑-dangerous? [] = no id
  ⊎⋑-dangerous? (c ∷ h) = vecAny (flip _⋑?_ c) h

  -- ⊎⋑-Bar

  data ⊎⋑-Bar : {n : ℕ} (h : Vec A n) → Set where
    now   : ∀ {n} (h : Vec A n) (bz : ⊎⋑-Dangerous h) → ⊎⋑-Bar h
    later : ∀ {n} {h : Vec A n} (bs : ∀ c → ⊎⋑-Bar (c ∷ h)) → ⊎⋑-Bar h

  -- ⊎⋑-bar→bar

  ⊎⋑-bar→bar : {n : ℕ} (h : Vec A n) → ⊎⋑-Bar h → Bar ⊎⋑-Dangerous  h
  ⊎⋑-bar→bar h (now .h bz) =
    now bz
  ⊎⋑-bar→bar h (later bs) =
    later (λ c → ⊎⋑-bar→bar (c ∷ h) (bs c))

  -- ⊎⋑-whistle

  ⊎⋑-whistle : (⊎⋑-bar[] : ⊎⋑-Bar []) → BarWhistle A
  ⊎⋑-whistle ⊎⋑-bar[] =
    ⟨ ⊎⋑-Dangerous , ⊎⋑-dangerous? , ⊎⋑-bar→bar [] ⊎⋑-bar[] ⟩

