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

  -- Bar whistles deal with sequences some entities
  -- (which in our model of supercompilations are configurations).

  field

    -- Dangerous histories
    Dangerous : ∀ {n} (h : Vec A n) → Set
    dangerous? : ∀ {n} (h : Vec A n) → Dec (Dangerous h)

    -- Bar-induction
    bar[] : Bar Dangerous []


-- pathLengthWhistle

pathLengthWhistle : (A : Set) (l : ℕ) → BarWhistle A

pathLengthWhistle A l = record
  { Dangerous = PLDangerous
  ; dangerous? = plDangerous?
  ; bar[] = plBar[] }
  where

  PLDangerous : ∀ {n} (h : Vec A n) → Set
  PLDangerous {n} h = l ≤ n

  plDangerous? : ∀ {n} (h : Vec A n) → Dec (PLDangerous h)
  plDangerous? {n} h = l ≤? n

  plBar : ∀ m n (h : Vec A n) (d : m + n ≡ l) → Bar PLDangerous h
  plBar zero .l h refl =
    now (≤′⇒≤ ≤′-refl)
  plBar (suc m) n h d =
    later (λ c → plBar m (suc n) (c ∷ h) m+1+n≡l)
    where
    open ≡-Reasoning
    m+1+n≡l = begin m + suc n ≡⟨ m+1+n≡1+m+n m n ⟩ suc (m + n) ≡⟨ d ⟩ l ∎

  plBar[] : Bar PLDangerous []
  plBar[] = plBar l zero [] (l + zero ≡ l ∋ proj₂ *+.+-identity l)
