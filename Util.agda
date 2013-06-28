module Util where

open import Data.Nat
  hiding(_⊔_)
open import Data.Nat.Properties
  using (≤′⇒≤; ≤⇒≤′; ≰⇒>)
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃)


open import Relation.Binary.PropositionalEquality as P

open import Algebra
  using (module CommutativeSemiring)

module *+ = CommutativeSemiring Data.Nat.Properties.commutativeSemiring

-- m+1+n≡1+m+n

m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
m+1+n≡1+m+n zero n = refl
m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)

-- m∸n+n≡m

m∸n+n≡m : (m n : ℕ) → n ≤ m → m ∸ n + n ≡ m
m∸n+n≡m m .0 z≤n = begin
  m ∸ 0 + 0
    ≡⟨⟩
  m + 0
    ≡⟨ proj₂ *+.+-identity m ⟩
  m
  ∎
  where open ≡-Reasoning
m∸n+n≡m .(suc n) .(suc m) (s≤s {m} {n} n≤m) = begin
  suc n ∸ suc m + suc m
    ≡⟨⟩
  n ∸ m + suc m
    ≡⟨ m+1+n≡1+m+n (n ∸ m) m ⟩
  suc (n ∸ m + m)
    ≡⟨ cong suc (m∸n+n≡m n m n≤m) ⟩
  suc n
  ∎
  where open ≡-Reasoning
