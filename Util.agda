module Util where

open import Level
  using (Lift; lift; lower)

open import Data.Bool
  using (Bool; true; false)
open import Data.Nat
  hiding(_⊔_)
open import Data.Nat.Properties
  using (≤′⇒≤; ≤⇒≤′; ≰⇒>)
open import Data.List
open import Data.List.Properties
  using (∷-injective; foldr-universal; foldr-fusion)
open import Data.List.Any
  using (Any; here; there; module Membership-≡)
open import Data.List.Any.Properties
  using (Any-cong; ⊥↔Any[]; Any↔; ++↔; ∷↔; return↔; map↔; concat↔; ⊎↔)
open import Data.List.Any.Membership as MB
  using (map-∈↔)
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.Vec as Vec
  using (Vec; []; _∷_; lookup)
open import Data.Product as Prod
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃; <_,_>; uncurry)
open import Data.Sum as Sum
  using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Empty

open import Function
open import Function.Equality
  using (_⟨$⟩_)
open import Function.Equivalence as Eq
  using (_⇔_; module Equivalence)
open import Function.Inverse as Inv
  using (_↔_; module Inverse)

open import Function.Related as Related
  using ()
  renaming (module EquationalReasoning to ∼-Reasoning)

import Relation.Binary.Sigma.Pointwise as Σ
open import Relation.Binary.Sum
  using (_⊎-cong_)
open import Relation.Binary.Product.Pointwise
  using (_×-cong_)

open import Relation.Binary.List.Pointwise as Pointwise
  using ([]; _∷_)

open import Relation.Nullary
open import Relation.Unary
  using () renaming (Decidable to Decidable₁)
open import Relation.Binary.PropositionalEquality as P
  hiding (sym)
  renaming ([_] to P[_])

open import Algebra
  using (module CommutativeSemiring)

module *+ = CommutativeSemiring Data.Nat.Properties.commutativeSemiring

open import Function.Related.TypeIsomorphisms
  using(×⊎-CommutativeSemiring)

module ×⊎ {k ℓ} = CommutativeSemiring (×⊎-CommutativeSemiring k ℓ)

open Membership-≡

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


-- foldr∘map

foldr∘map : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  (f : A → B) (g : B → C → C) (n : C) →
  foldr g n ∘ map f ≗ foldr (g ∘ f) n
foldr∘map f g n =
  foldr-universal (foldr g n ∘ map f) (g ∘ f) n refl (λ x xs → refl)

-- gfilter-++-commute

gfilter-++-commute :
  ∀ {a b} {A : Set a} {B : Set b} (f : A → Maybe B) xs ys →
    gfilter f (xs ++ ys) ≡ gfilter f xs ++ gfilter f ys
 
gfilter-++-commute f [] ys = refl
gfilter-++-commute f (x ∷ xs) ys with f x
... | just y = cong (_∷_ y) (gfilter-++-commute f xs ys)
... | nothing = gfilter-++-commute f xs ys

-- filter-++-commute

filter-++-commute :
  ∀ {a} {A : Set a} (p : A → Bool) xs ys →
    filter p (xs ++ ys) ≡ filter p xs ++ filter p ys

filter-++-commute f xs ys =
  gfilter-++-commute (λ z → Data.Bool.if f z then just z else nothing) xs ys

-- filter∘map

filter∘map :
  ∀ {a b} {A : Set a} {B : Set b} (p : B → Bool) (f : A → B) xs →
  filter p (map f xs) ≡ map f (filter (p ∘ f) xs)

filter∘map p f [] = refl
filter∘map p f (x ∷ xs) with p (f x)
... | true = cong (_∷_ (f x)) (filter∘map p f xs)
... | false = filter∘map p f xs

-- filter-false

filter-false :
  ∀ {a} {A : Set a} (xs : List A) →
    filter (const false) xs ≡ []

filter-false [] = refl
filter-false (x ∷ xs) = filter-false xs

-- filter-cong

filter-cong :
  ∀ {a} {A : Set a} {p q : A → Bool} →
    p ≗ q → filter p ≗ filter q

filter-cong p≗q [] = refl
filter-cong {p = p} {q = q} p≗q (x ∷ xs)
  rewrite p≗q x with q x
... | true = cong (_∷_ x) (filter-cong p≗q xs)
... | false = filter-cong p≗q xs

--
-- Some "technical" theorems about `Any`
--

-- ⊥⊎

⊥⊎ : ∀ {A : Set} → A ↔ (⊥ ⊎ A)

⊥⊎ {A} = record
  { to = →-to-⟶ inj₂
  ; from = →-to-⟶ to
  ; inverse-of = record
    { left-inverse-of = λ x → refl
    ; right-inverse-of = from∘to
    }
  }
  where
  to : (⊥ ⊎ A) → A
  to = [ ⊥-elim , id ]′
  from∘to : (x : ⊥ ⊎ A) → inj₂ (to x) ≡ x
  from∘to (inj₁ ())
  from∘to (inj₂ x) = refl

-- ⊥×

⊥× : ∀ {A : Set} → ⊥ ↔ (⊥ × A)

⊥× {A} = record
  { to = →-to-⟶ (λ ())
  ; from = →-to-⟶ (uncurry (λ a⊥ x → a⊥))
  ; inverse-of = record
    { left-inverse-of = λ a⊥ → ⊥-elim a⊥
    ; right-inverse-of = uncurry (λ a⊥ x → ⊥-elim a⊥)
    }
  }

-- ⊥↔[]∈map∷

⊥↔[]∈map∷ : ∀ {A : Set} (x : A) (yss : List (List A)) →
  ⊥ ↔ (List A ∋ []) ∈ map (_∷_ x) yss

⊥↔[]∈map∷ {A} x yss = record
  { to = →-to-⟶ (to x yss)
  ; from = →-to-⟶ (from x yss)
  ; inverse-of = record
    { left-inverse-of = λ a⊥ → ⊥-elim a⊥
    ; right-inverse-of = to∘from x yss
    }
  }
  where
  to : ∀ (x : A) (yss : List (List A)) → ⊥ → [] ∈ map (_∷_ x) yss
  to x [] a⊥ = ⊥-elim a⊥
  to x (ys ∷ yss) a⊥ = there (to x yss a⊥)

  from : ∀ (x : A) (yss : List (List A)) → [] ∈ map (_∷_ x) yss → ⊥
  from x [] ()
  from x (ys ∷ yss) (here ())
  from x (ys ∷ yss) (there []∈map∷) = from x yss []∈map∷

  to∘from : ∀ (x′ : A) (yss′ : List (List A)) →
    (p : [] ∈ map (_∷_ x′) yss′) → to x′ yss′ (from x′ yss′ p) ≡ p
  to∘from x [] ()
  to∘from x (ys ∷ yss) (here ())
  to∘from x (ys ∷ yss) (there p) = cong there (to∘from x yss p)


-- concat↔∘Any↔

concat↔∘Any↔ : {A B : Set}
  (z : B) (g : B → B) (f : A → List B) (xs : List A) →
  ∃ (λ x → x ∈ xs × ∃ (λ y → y ∈ f x × z ≡ g y)) ↔
  z ∈ map g (concat (map f xs))
concat↔∘Any↔ z g f xs =
  ∃ (λ x → x ∈ xs × ∃ (λ y → y ∈ f x × z ≡ g y))
    ∼⟨ Σ.cong Inv.id (Inv.id ×-cong Any↔) ⟩
  ∃ (λ x → x ∈ xs × (Any (λ y → z ≡ g y) (f x)))
    ∼⟨ _ ∎ ⟩
  ∃ (λ x → x ∈ xs × (Any (λ y → z ≡ g y) ∘ f) x)
    ∼⟨ _ ∎ ⟩
  ∃ (λ x → x ∈ xs × (Any (_≡_ z ∘ g) ∘ f) x)
    ∼⟨ Any↔ ⟩
  Any (Any (_≡_ z ∘ g) ∘ f) xs
    ∼⟨ map↔ ⟩
  Any (Any (_≡_ z ∘ g)) (map f xs)
    ∼⟨ concat↔ ⟩
  Any (_≡_ z ∘ g) (concat (map f xs))
    ∼⟨ map↔ ⟩
  Any (_≡_ z) (map g (concat (map f xs)))
    ∼⟨ _ ∎ ⟩
  z ∈ map g (concat (map f xs))
  ∎
  where open ∼-Reasoning

-- ∈*∘map

∈*∘map→ :
  ∀ {A B : Set} (f : A → List B) (xs : List A) {ys : List B} →
  Pointwise.Rel _∈_ ys (map f xs) → Pointwise.Rel (λ x y → y ∈ f x) xs ys

∈*∘map→ f [] {[]} _ = []
∈*∘map→ f [] {_ ∷ _} ()
∈*∘map→ f (x ∷ xs) (y∈fx ∷ ys∈*) =
  y∈fx ∷ ∈*∘map→ f xs ys∈*

-- ∈*∘map←

∈*∘map← :
  ∀ {A B : Set} (f : A → List B) (xs : List A) {ys : List B} →
  Pointwise.Rel (λ x y → y ∈ f x) xs ys → Pointwise.Rel _∈_ ys (map f xs)

∈*∘map← f [] [] = []
∈*∘map← f (x ∷ xs) (y∈fx ∷ xs∈*) = y∈fx ∷ ∈*∘map← f xs xs∈*


--
-- Cartesian product
--

-- cartesian2

cartesian2 : ∀ {a} {A : Set a} → List A → List (List A) → List (List A)
cartesian2 [] yss = []
cartesian2 (x ∷ xs) yss = map (_∷_ x) yss ++ cartesian2 xs yss

-- cartesian

cartesian : ∀ {A : Set} (xss : List (List A)) → List (List A)
cartesian [] = [ [] ]
cartesian (xs ∷ xss) = cartesian2 xs (cartesian xss)

--
-- Some "technical" theorems about cartesian products
--

-- cartesian-is-foldr

cartesian-is-foldr : ∀  {A : Set} (xss : List (List A)) →
  cartesian xss ≡ foldr cartesian2 [ [] ] xss

cartesian-is-foldr [] = refl
cartesian-is-foldr (xs ∷ xss) = cong (cartesian2 xs) (cartesian-is-foldr xss)

-- cartesian∘map

cartesian∘map : ∀ {A B : Set} (f : A → List B) (xs : List A) →
  cartesian (map f xs) ≡ foldr (cartesian2 ∘ f) [ [] ]  xs
cartesian∘map f xs = begin
  cartesian (map f xs)
    ≡⟨ cartesian-is-foldr (map f xs) ⟩
  foldr cartesian2 [ [] ] (map f xs)
    ≡⟨ foldr∘map f cartesian2 [ [] ] xs ⟩
  foldr (cartesian2 ∘ f) [ [] ] xs
  ∎
  where open ≡-Reasoning

-- cartesian2[]

cartesian2[] : ∀ {A : Set} (xs : List A) →
  cartesian2 xs [] ≡ []

cartesian2[] [] = refl
cartesian2[] (x ∷ xs) = cartesian2[] xs


-- ⊥↔[]∈cartesian2

⊥↔[]∈cartesian2 : ∀ {A : Set} (xs : List A) (yss : List (List A)) →
  ⊥ ↔ [] ∈ cartesian2 xs yss

⊥↔[]∈cartesian2 [] yss =
  ⊥↔Any[]

⊥↔[]∈cartesian2 {A} (x ∷ xs) yss =
  ⊥
    ↔⟨ ⊥⊎ ⟩
  (⊥ ⊎ ⊥)
    ↔⟨ ⊥↔[]∈map∷ x yss ⊎-cong ⊥↔[]∈cartesian2 xs yss ⟩
  ([] ∈ map (_∷_ x) yss ⊎ [] ∈ cartesian2 xs yss)
    ↔⟨ ++↔ ⟩
  [] ∈ (map (_∷_ x) yss ++ cartesian2 xs yss)
  ∎
  where open ∼-Reasoning

-- Some important properties of `cartesian`

-- ≡×∈→map∷

≡×∈→map∷ : ∀ {A : Set} {x : A} {xs : List A} {y : A} {yss : List (List A)} →
  (x ≡ y × xs ∈ yss) → x ∷ xs ∈ map {B = List A} (_∷_ y) yss

≡×∈→map∷ (refl , here refl) = here refl
≡×∈→map∷ (refl , there xs∈yss) = there (≡×∈→map∷ (refl , xs∈yss))

-- map∷→≡×∈

map∷→≡×∈ : ∀ {A : Set} {x : A} {xs : List A} {y : A} {yss : List (List A)} →
  x ∷ xs ∈ map {B = List A} (_∷_ y) yss → (x ≡ y × xs ∈ yss)

map∷→≡×∈ {yss = []} ()
map∷→≡×∈ {yss = ys ∷ yss} (here x∷xs≡y∷ys) =
  helper (∷-injective x∷xs≡y∷ys)
  where helper : _ → _
        helper (x≡y , xs≡ys) = x≡y , here xs≡ys
map∷→≡×∈ {yss = ys ∷ yss} (there x∷xs∈) =
  helper (map∷→≡×∈ x∷xs∈)
  where helper : _ → _
        helper (x≡y , xs∈yss) = x≡y , there xs∈yss

-- ≡×∈↔map∷

≡×∈↔map∷ : ∀ {A : Set} (x : A) (xs : List A) (y : A) (yss : List (List A)) →
  (x ≡ y × xs ∈ yss) ↔ x ∷ xs ∈ map {B = List A} (_∷_ y) yss

≡×∈↔map∷ {A} x xs y yss = record
  { to = →-to-⟶ ≡×∈→map∷
  ; from = →-to-⟶ map∷→≡×∈
  ; inverse-of = record
    { left-inverse-of = to∘from
    ; right-inverse-of = from∘to
    }
  }
  where
  open ∼-Reasoning

  to∘from : ∀ {A : Set} {x : A} {xs : List A} {y : A} {yss : List (List A)} →
    (p : x ≡ y × xs ∈ yss) → map∷→≡×∈ (≡×∈→map∷ p) ≡ p
  to∘from (refl , here refl) = refl
  to∘from {y = y} {yss = ys ∷ yss} (refl , there xs∈yss)
    rewrite to∘from {y = y} (refl {x = y} , xs∈yss)
    = refl

  from∘to : ∀ {A : Set} {x : A} {xs : List A} {y : A} {yss : List (List A)} →
    (p : x ∷ xs ∈ map (_∷_ y) yss) → ≡×∈→map∷ (map∷→≡×∈ p) ≡ p
  from∘to {yss = []} ()
  from∘to {yss = ys ∷ yss} (here refl) = refl
  from∘to {yss = ys ∷ yss} (there x∷xs∈) with map∷→≡×∈ x∷xs∈ | from∘to x∷xs∈
  ... | refl , xs∈yss | ft rewrite ft = refl

-- ∈∈↔∷cartesian

∈∈↔∷cartesian2 :
  ∀ {A : Set} (x : A) (xs ys : List A) (yss : List (List A)) →
    (x ∈ ys × xs ∈ yss) ↔ x ∷ xs ∈ cartesian2 ys yss

∈∈↔∷cartesian2 x xs [] yss =
  (x ∈ [] × xs ∈ yss)
    ↔⟨ (sym $ ⊥↔Any[]) ×-cong (_ ∎) ⟩
  (⊥ × xs ∈ yss)
    ↔⟨ sym $ ⊥× ⟩
  ⊥
    ↔⟨ ⊥↔Any[] ⟩
  x ∷ xs ∈ []
  ∎
  where open ∼-Reasoning

∈∈↔∷cartesian2 x xs (y ∷ ys) yss =
  (x ∈ y ∷ ys × xs ∈ yss)
    ↔⟨ sym (∷↔ (_≡_ x)) ×-cong (_ ∎) ⟩
  ((x ≡ y ⊎ x ∈ ys) × xs ∈ yss)
    ↔⟨ proj₂ ×⊎.distrib (xs ∈ yss) (x ≡ y) (x ∈ ys) ⟩
  (x ≡ y × xs ∈ yss ⊎ x ∈ ys × xs ∈ yss)
    ↔⟨ ≡×∈↔map∷ x xs y yss ⊎-cong ∈∈↔∷cartesian2 x xs ys yss ⟩
  (x ∷ xs ∈ map (_∷_ y) yss ⊎ x ∷ xs ∈ cartesian2 ys yss)
    ↔⟨ ++↔ ⟩
  x ∷ xs ∈ (map (_∷_ y) yss ++ cartesian2 ys yss)
    ≡⟨ refl ⟩
  x ∷ xs ∈ cartesian2 (y ∷ ys) yss
  ∎
  where open ∼-Reasoning

-- ⊥↔[]∈*

⊥↔[]∈* : ∀ {A : Set} (ys : List A) yss →
  ⊥ ↔ Pointwise.Rel _∈_ [] (ys ∷ yss)
⊥↔[]∈* {A} ys yss = record
  { to = →-to-⟶ (λ a⊥ → ⊥-elim a⊥)
  ; from = →-to-⟶ (from ys yss)
  ; inverse-of = record
    { left-inverse-of = (λ ())
    ; right-inverse-of = (from∘to ys yss)
    }
  }
  where
  from : ∀ (ys : List A) (yss : List (List A)) →
    Pointwise.Rel _∈_ [] (ys ∷ yss) → ⊥
  from y yss ()
  from∘to : ∀ (ys : List A) (yss : List (List A)) →
    (p : Pointwise.Rel _∈_ [] (ys ∷ yss)) → ⊥-elim (from ys yss p) ≡ p
  from∘to ys yss ()



×∈*↔∈* : ∀ {A : Set} (x : A) xs ys yss →
  (x ∈ ys × Pointwise.Rel _∈_ xs yss) ↔ Pointwise.Rel _∈_ (x ∷ xs) (ys ∷ yss)

×∈*↔∈* x xs ys yss = record
  { to = →-to-⟶ to
  ; from = →-to-⟶ from
  ; inverse-of = record
    { left-inverse-of = to∘from
    ; right-inverse-of = from∘to
    }
  }
  where
  to : x ∈ ys × Pointwise.Rel _∈_ xs yss →
          Pointwise.Rel _∈_ (x ∷ xs) (ys ∷ yss)
  to (x∈ys , xs∈*yss) = x∈ys ∷ xs∈*yss
  from : Pointwise.Rel _∈_ (x ∷ xs) (ys ∷ yss) →
           x ∈ ys × Pointwise.Rel _∈_ xs yss
  from (x∈ys ∷ xs∈*yss) = x∈ys , xs∈*yss
  to∘from : (p : x ∈ ys × Pointwise.Rel _∈_ xs yss) → from (to p) ≡ p
  to∘from (x∈ys , xs∈*yss) = refl
  from∘to : (p : Pointwise.Rel _∈_ (x ∷ xs) (ys ∷ yss)) → to (from p) ≡ p
  from∘to (x∈ys ∷ xs∈*yss) = refl

-- 
-- A proof of correctness of `cartesian`
-- with respect to `Pointwise.Rel _∈_`

-- ∈*↔∈cartesian

∈*↔∈cartesian :
  ∀ {A : Set} {xs : List A} {yss : List (List A)} →
    Pointwise.Rel _∈_ xs yss ↔ xs ∈ cartesian yss

∈*↔∈cartesian {A} {[]} {[]} = record
  { to = →-to-⟶ from
  ; from = →-to-⟶ to
  ; inverse-of = record
    { left-inverse-of = to∘from
    ; right-inverse-of = from∘to
    }
  }
  where
  from : _ → _
  from p = here refl
  to : _ → _
  to p = []
  to∘from : (p : Pointwise.Rel _∈_ [] []) → [] ≡ p
  to∘from [] = refl
  from∘to : (p : [] ∈ [] ∷ []) → here refl ≡ p
  from∘to (here refl) = refl
  from∘to (there ())

∈*↔∈cartesian {A} {[]} {ys ∷ yss} =
  Pointwise.Rel _∈_ [] (ys ∷ yss)
    ↔⟨ sym $ ⊥↔[]∈* ys yss ⟩
  ⊥
    ↔⟨ ⊥↔[]∈cartesian2 ys (cartesian yss) ⟩
  [] ∈ cartesian2 ys (cartesian yss)
    ≡⟨ refl ⟩
  [] ∈ cartesian (ys ∷ yss)
  ∎
  where open ∼-Reasoning

∈*↔∈cartesian {A} {x ∷ xs} {[]} = record
  { to = →-to-⟶ from
  ; from = →-to-⟶ to
  ; inverse-of = record
    { left-inverse-of = to∘from
    ; right-inverse-of = from∘to
    }
  }
  where
  from : (p : Pointwise.Rel _∈_ (x ∷ xs) []) → x ∷ xs ∈ [] ∷ []
  from ()
  to : (p : x ∷ xs ∈ [] ∷ []) → Pointwise.Rel _∈_ (x ∷ xs) []
  to (here ())
  to (there ())
  to∘from : (p : Pointwise.Rel _∈_ (x ∷ xs) []) → to (from p) ≡ p
  to∘from ()
  from∘to : (p : x ∷ xs ∈ [] ∷ []) → from (to p) ≡ p
  from∘to (here ())
  from∘to (there ())

∈*↔∈cartesian {A} {x ∷ xs} {ys ∷ yss} =
  Pointwise.Rel _∈_ (x ∷ xs) (ys ∷ yss)
    ↔⟨ sym $ ×∈*↔∈* x xs ys yss ⟩
  (x ∈ ys × Pointwise.Rel _∈_ xs yss)
    ↔⟨ (_ ∎) ×-cong ∈*↔∈cartesian ⟩
  (x ∈ ys × xs ∈ cartesian yss)
    ↔⟨ ∈∈↔∷cartesian2 x xs ys (cartesian yss) ⟩
  x ∷ xs ∈ cartesian2 ys (cartesian yss)
    ≡⟨ refl ⟩
  x ∷ xs ∈ cartesian (ys ∷ yss)
  ∎
  where open ∼-Reasoning

--
-- Monotonicity of `Pointwise.Rel _∈_` and `cartesian`.
--

-- ∈*-mono

∈*-mono : {A : Set} {xs : List A} {yss₁ yss₂ : List (List A)} →
  Pointwise.Rel _⊆_ yss₁ yss₂ →
  Pointwise.Rel _∈_ xs yss₁ → Pointwise.Rel _∈_ xs yss₂

∈*-mono [] [] = []
∈*-mono (ys₁⊆ys₂ ∷ yss₁⊆*yss₂) (x∈ys₁ ∷ xs∈*yss₁) =
  (ys₁⊆ys₂ x∈ys₁) ∷ ∈*-mono yss₁⊆*yss₂ xs∈*yss₁

-- cartesian-mono

cartesian-mono : ∀ {A : Set} (xss₁ xss₂ : List (List A)) →
  Pointwise.Rel _⊆_ xss₁ xss₂ →
  cartesian xss₁ ⊆ cartesian xss₂

cartesian-mono xss₁ xss₂ xss₁⊆xss₂ {zs} =
  zs ∈ cartesian xss₁
    ↔⟨ sym $ ∈*↔∈cartesian ⟩
  Pointwise.Rel _∈_ zs xss₁
    ∼⟨ ∈*-mono xss₁⊆xss₂ ⟩
  Pointwise.Rel _∈_ zs xss₂
    ↔⟨ ∈*↔∈cartesian ⟩
  zs ∈ cartesian xss₂
  ∎
  where open ∼-Reasoning

-- ∈*∘map-mono

∈*∘map-mono : {A B : Set} {⟪_⟫ : A → List B} (clean : A → A) →
  (mono : ∀ x → ⟪ clean x ⟫ ⊆ ⟪ x ⟫) (xs : List A) →
  Pointwise.Rel _⊆_ (map (⟪_⟫ ∘ clean) xs) (map ⟪_⟫ xs)

∈*∘map-mono clean mono [] = []
∈*∘map-mono clean mono (x ∷ xs) =
  (mono x) ∷ ∈*∘map-mono clean mono xs

--
-- filter∘cartesian
--

-- filter∘cartesian2

filter∘cartesian2 :
  ∀ {A : Set} (p : A → Bool) (xs : List A) (xss : List (List A)) →
    filter (all p) (cartesian2 xs xss) ≡
      cartesian2 (filter p xs) (filter (all p) xss)

filter∘cartesian2 p [] xss = refl

filter∘cartesian2 p (x ∷ xs) xss with p x | inspect p x

... | true | P[ ≡true ] = begin
  filter (all p) (cartesian2 (x ∷ xs) xss)
    ≡⟨⟩
  filter (all p) (map (_∷_ x) xss ++ cartesian2 xs xss)
    ≡⟨ filter-++-commute (all p) (map (_∷_ x) xss) (cartesian2 xs xss) ⟩
  filter (all p) (map (_∷_ x) xss) ++ filter (all p) (cartesian2 xs xss)
    ≡⟨ cong₂ _++_ helper₂ (filter∘cartesian2 p xs xss) ⟩
  map (_∷_ x) (filter (all p) xss) ++
  cartesian2 (filter p xs) (filter (all p) xss)
  ∎
  where
  open ≡-Reasoning
  helper₁ : all p ∘ _∷_ x ≡ all p
  helper₁ rewrite ≡true = refl

  helper₂ : filter (all p) (map (_∷_ x) xss) ≡ map (_∷_ x) (filter (all p) xss)
  helper₂ = begin
    filter (all p) (map (_∷_ x) xss)
      ≡⟨ filter∘map (all p) (_∷_ x) xss ⟩
    map (_∷_ x) (filter (all p ∘ _∷_ x) xss)
      ≡⟨ cong (map (_∷_ x)) (cong (flip filter xss) helper₁) ⟩
    map (_∷_ x) (filter (all p) xss)
    ∎

... | false | P[ ≡false ] = begin
  filter (all p) (cartesian2 (x ∷ xs) xss)
    ≡⟨⟩
  filter (all p) (map (_∷_ x) xss ++ cartesian2 xs xss)
    ≡⟨ filter-++-commute (all p) (map (_∷_ x) xss) (cartesian2 xs xss) ⟩
  filter (all p) (map (_∷_ x) xss) ++ filter (all p) (cartesian2 xs xss)
    ≡⟨ cong₂ _++_ helper₂ (filter∘cartesian2 p xs xss) ⟩
  [] ++ cartesian2 (filter p xs) (filter (all p) xss)
    ≡⟨⟩
  cartesian2 (filter p xs) (filter (all p) xss)
  ∎
  where
  open ≡-Reasoning

  helper₁ : all p ∘ _∷_ x ≡ const false
  helper₁ rewrite ≡false = refl

  helper₂ : filter (all p) (map (_∷_ x) xss) ≡ []
  helper₂ = begin
    filter (all p) (map (_∷_ x) xss)
      ≡⟨ filter∘map (all p) (_∷_ x) xss ⟩
    map (_∷_ x) (filter (all p ∘ _∷_ x) xss)
      ≡⟨ cong (map (_∷_ x)) (cong (flip filter xss) helper₁) ⟩
    map (_∷_ x) (filter (const false) xss)
      ≡⟨ cong (map (_∷_ x)) (filter-false xss) ⟩
    map (_∷_ x) []
      ≡⟨⟩
    []
    ∎

-- filter∘cartesian

filter∘cartesian :
  ∀ {A : Set} (p : A → Bool) (xss : List (List A)) →
    filter (all p) (cartesian xss) ≡ cartesian (map (filter p) xss)

filter∘cartesian p [] = refl
filter∘cartesian p (xs ∷ xss) = begin
  filter (all p) (cartesian (xs ∷ xss))
    ≡⟨⟩
  filter (all p) (cartesian2 xs (cartesian xss))
    ≡⟨ filter∘cartesian2 p xs (cartesian xss) ⟩
  cartesian2 (filter p xs) (filter (all p) (cartesian xss))
    ≡⟨ cong (cartesian2 (filter p xs)) (filter∘cartesian p xss) ⟩
  cartesian2 (filter p xs) (cartesian (map (filter p) xss))
    ≡⟨⟩
  cartesian (filter p xs ∷ map (filter p) xss)
    ≡⟨⟩
  cartesian (map (filter p) (xs ∷ xss))
  ∎
  where open ≡-Reasoning

--
-- Cartesian product for vectors
--

-- vec-cartesian2

vec-cartesian2 : ∀ {k} {A : Set} → List A → List (Vec A k) →
  List (Vec A (suc k))

vec-cartesian2 [] yss = []
vec-cartesian2 (x ∷ xs) yss = map (_∷_ x) yss ++ vec-cartesian2 xs yss

-- vec-cartesian

vec-cartesian : ∀ {k} {A : Set} (xss : Vec (List A) k) → List (Vec A k)
vec-cartesian [] = [ [] ]
vec-cartesian (xs ∷ xss) = vec-cartesian2 xs (vec-cartesian xss)
