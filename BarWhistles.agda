module BarWhistles where

open import Data.Nat
open import Data.Nat
  hiding(_⊔_)
open import Data.Nat.Properties
  using (≤′⇒≤; ≤⇒≤′; ≰⇒>)
open import Data.Vec as Vec
  using (Vec; []; _∷_; lookup)
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃)
open import Data.Empty

open import Function

open import Relation.Nullary

open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to [_]ⁱ)

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

-- inverseImageWhistle

inverseImageWhistle : (A B : Set) (f : A → B)
  (w : BarWhistle B) → BarWhistle A

inverseImageWhistle A B f ⟨ d , d? , bd[] ⟩ =
  ⟨ d ∘ Vec.map f , d? ∘ Vec.map f , bar [] bd[] ⟩
  where
  bar : ∀ {n} (h : Vec A n) (b : Bar d (Vec.map f h)) → Bar (d ∘ Vec.map f) h
  bar h (now bz) = now bz
  bar h (later bs) = later (λ c → bar (c ∷ h) (bs (f c)))

