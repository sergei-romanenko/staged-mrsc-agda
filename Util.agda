module Util where

open import Level
  using (Lift; lift; lower)

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
  using (⊥↔Any[]; Any↔; ++↔; ∷↔; return↔; map↔; concat↔; ⊎↔)
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.Vec as Vec
  using (Vec; []; _∷_; lookup)
open import Data.Product as Prod
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃; <_,_>)
open import Data.Sum as Sum
  using (_⊎_; inj₁; inj₂; [_,_]′)
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

-- AnyV

AnyV : ∀ {n a ℓ} {A : Set a} (P : A → Set ℓ) (xs : Vec A n) → Set ℓ
AnyV P xs = ∃ λ i → P (lookup i xs) 

-- anyV

anyV : ∀ {n a p} {A : Set a} {P : A → Set p} →
  Decidable₁ P → Decidable₁ (AnyV {n} P)

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

-- VecAny

VecAny : ∀ {n a ℓ} {A : Set a} (P : A → Set ℓ) (xs : Vec A n) → Set ℓ
VecAny P [] = Level.Lift ⊥
VecAny P (x ∷ xs) = P x ⊎ VecAny P xs

-- vecAny

vecAny : ∀ {n a ℓ} {A : Set a} {P : A → Set ℓ} →
  Decidable₁ P → Decidable₁ (VecAny {n} P)
vecAny dp [] = no Level.lower
vecAny dp (x ∷ xs) with dp x
... | yes dpx = yes (inj₁ dpx)
... | no ¬dpx with vecAny dp xs
... | yes dpxs = yes (inj₂ dpxs)
... | no ¬dpxs = no [ ¬dpx , ¬dpxs ]′

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

--
-- Some "technical" theorems about `Any`
--

-- ⊥⊎

⊥⊎ : ∀ {A : Set} → A ↔ (⊥ ⊎ A)

⊥⊎ {A} = record
  { to = →-to-⟶ from
  ; from = →-to-⟶ to
  ; inverse-of = record
    { left-inverse-of = λ x → refl
    ; right-inverse-of = from∘to
    }
  }
  where
  from = inj₂
  to : (⊥ ⊎ A) → A
  to (inj₁ ())
  to (inj₂ x) = x
  from∘to : (x : ⊥ ⊎ A) → inj₂ (to x) ≡ x
  from∘to (inj₁ ())
  from∘to (inj₂ x) = refl

-- Lift⊥↔⊥

Lift⊥↔⊥ : ∀ {ℓ} → Lift {Level.zero} {ℓ} ⊥ ↔ ⊥
Lift⊥↔⊥ {ℓ} = record
  { to = →-to-⟶ lower
  ; from = →-to-⟶ lift
  ; inverse-of = record
    { left-inverse-of = λ _ → refl
    ; right-inverse-of = λ ()
    }
  }

-- Lift⊥↔Any[]

Lift⊥↔Any[] : ∀ {a} {A : Set a} {P : A → Set} → Lift {ℓ = a} ⊥ ↔ Any P []

Lift⊥↔Any[] {P = P} =
  Lift ⊥ ↔⟨ Lift⊥↔⊥ ⟩ ⊥ ↔⟨ ⊥↔Any[] ⟩ Any P [] ∎
  where open ∼-Reasoning

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


-- map↔∘Any↔

map↔∘Any↔ : {A : Set}
  (x : A) (f : List A → A) (xss : List (List A)) →
  ∃ (λ xs → xs ∈ xss × x ≡ f xs) ↔ x ∈ map f xss
map↔∘Any↔ x f xss =
  ∃ (λ xs → xs ∈ xss × x ≡ f xs)
    ∼⟨ Any↔ ⟩
  Any (_≡_ x ∘ f) xss
    ∼⟨ map↔ ⟩
  Any (_≡_ x) (map f xss)
    ∼⟨ _ ∎ ⟩
  x ∈ map f xss
  ∎
  where open ∼-Reasoning

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

-- ∈∈→∷cartesian

∈∈→∷cartesian :
  ∀ {A : Set} (x : A) (xs ys : List A) (yss : List (List A)) →
    (x ∈ ys × xs ∈ yss) → x ∷ xs ∈ cartesian2 ys yss

∈∈→∷cartesian x xs [] yss =
  (x ∈ [] × xs ∈ yss)
    ∼⟨ proj₁ ⟩
  x ∈ []
    ↔⟨ sym $ ⊥↔Any[] ⟩
  ⊥
    ∼⟨ ⊥-elim ⟩
  x ∷ xs ∈ []
  ∎
  where open ∼-Reasoning

∈∈→∷cartesian x xs (y ∷ ys) yss =
  (x ∈ y ∷ ys × xs ∈ yss)
    ↔⟨ sym (∷↔ (_≡_ x)) ⟨ ×⊎.*-cong ⟩ _ ∎ ⟩
  ((x ≡ y ⊎ x ∈ ys) × xs ∈ yss)
    ↔⟨ proj₂ ×⊎.distrib (xs ∈ yss) (x ≡ y) (x ∈ ys) ⟩
  (x ≡ y × xs ∈ yss ⊎ x ∈ ys × xs ∈ yss)
    ∼⟨ Sum.map helper (∈∈→∷cartesian x xs ys yss) ⟩
  (x ∷ xs ∈ map (_∷_ y) yss ⊎ x ∷ xs ∈ cartesian2 ys yss)
    ↔⟨ ++↔ ⟩
  x ∷ xs ∈ (map (_∷_ y) yss ++ cartesian2 ys yss)
    ≡⟨ refl ⟩
  x ∷ xs ∈ cartesian2 (y ∷ ys) yss
  ∎
  where
  open ∼-Reasoning
  helper : ∀ {x y xs yss} → x ≡ y × xs ∈ yss → x ∷ xs ∈ map (_∷_ y) yss
  helper (refl , here refl) = here refl
  helper (x≡y , there xs∈yss) = there (helper (x≡y , xs∈yss))

-- []cartesian→⊥

[]cartesian→⊥ :
  ∀ {A : Set} (ys : List A) (yss : List (List A)) →
     [] ∈ cartesian2 ys yss → ⊥

[]cartesian→⊥ [] yss =
  λ ()
[]cartesian→⊥ (x ∷ ys) yss =
  [] ∈ map (_∷_ x) yss ++ cartesian2 ys yss
    ↔⟨ sym ++↔ ⟩
  ([] ∈ map (_∷_ x) yss ⊎ [] ∈ cartesian2 ys yss)
    ∼⟨ Sum.map (helper x yss) ([]cartesian→⊥ ys yss) ⟩
  (⊥ ⊎ ⊥)
     ↔⟨ sym $ ⊥⊎ ⟩
  ⊥
  ∎
  where
  open ∼-Reasoning
  helper : ∀ x yss → [] ∈ map (_∷_ x) yss → ⊥
  helper x [] ()
  helper x (y ∷ yss) (here ())
  helper x (y ∷ yss) (there []∈) = helper x yss []∈

-- ∷cartesian→∈∈

∷cartesian→∈∈ :
  ∀ {A : Set} (x : A) (xs ys : List A) (yss : List (List A)) →
     x ∷ xs ∈ cartesian2 ys yss → (x ∈ ys × xs ∈ yss)

∷cartesian→∈∈ x xs [] yss =
  λ ()
∷cartesian→∈∈ x xs (y ∷ ys) yss =
  x ∷ xs ∈ cartesian2 (y ∷ ys) yss
    ≡⟨ refl ⟩
  x ∷ xs ∈ map (_∷_ y) yss ++ cartesian2 ys yss
    ↔⟨ sym ++↔ ⟩
  (x ∷ xs ∈ map (_∷_ y) yss ⊎ x ∷ xs ∈ cartesian2 ys yss)
    ∼⟨ Sum.map (helper x xs y yss) (∷cartesian→∈∈ x xs ys yss) ⟩
  ((x ≡ y × xs ∈ yss) ⊎ (x ∈ ys × xs ∈ yss))
    ∼⟨ [ < inj₁ ∘ proj₁ , proj₂ > , < inj₂ ∘ proj₁ , proj₂ > ]′ ⟩
  ((x ≡ y ⊎ x ∈ ys) × xs ∈ yss)
    ↔⟨ ∷↔ (_≡_ x) ⟨ ×⊎.*-cong ⟩ _ ∎ ⟩
  (x ∈ y ∷ ys × xs ∈ yss)
  ∎
  where
  open ∼-Reasoning
  helper : ∀ x xs y yss → x ∷ xs ∈ map (_∷_ y) yss → x ≡ y × xs ∈ yss
  helper x xs y [] ()
  helper x xs y (ys ∷ yss) (here x∷xs≡y∷ys) = helper₂ (∷-injective x∷xs≡y∷ys)
    where helper₂ : x ≡ y × xs ≡ ys → x ≡ y × xs ∈ ys ∷ yss
          helper₂ (x≡y , xs≡ys) = x≡y , here xs≡ys
  helper x xs y (ys ∷ yss) (there x∷xs∈) = helper₂ (helper x xs y yss x∷xs∈)
    where helper₂ : x ≡ y × xs ∈ yss → x ≡ y × xs ∈ ys ∷ yss
          helper₂ (x≡y , xs∈yss) = x≡y , there xs∈yss


-- ⊥↔[]∈cartesian2

⊥↔[]∈cartesian2 : ∀ {A : Set} (xs : List A) (yss : List (List A)) →
  ⊥ ↔ [] ∈ cartesian2 xs yss
⊥↔[]∈cartesian2 [] yss =
  ⊥↔Any[]
⊥↔[]∈cartesian2 {A} (x ∷ xs) yss =
  ⊥
    ↔⟨ ⊥⊎ ⟩
  (⊥ ⊎ ⊥)
    ↔⟨ ⊥↔[]∈map∷ x yss ⟨ ×⊎.+-cong ⟩ ⊥↔[]∈cartesian2 xs yss ⟩
  ([] ∈ map (_∷_ x) yss ⊎ [] ∈ cartesian2 xs yss)
    ↔⟨ ++↔ ⟩
  [] ∈ (map (_∷_ x) yss ++ cartesian2 xs yss)
  ∎
  where open ∼-Reasoning

-- []∉cartesian2

[]∉cartesian2 : ∀ {A : Set} (xs : List A) (yss : List (List A)) →
  [] ∈ cartesian2 xs yss → ⊥
[]∉cartesian2 x yss []∈ = Inverse.from (⊥↔[]∈cartesian2 x yss) ⟨$⟩ []∈

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

-- The main property of `cartesian`

∈*→∈cartesian :
  ∀ {A : Set} (xs : List A) (yss : List (List A)) →
    Pointwise.Rel _∈_ xs yss → xs ∈ cartesian yss

∈*→∈cartesian .[] .[] [] = here refl
∈*→∈cartesian .(x ∷ xs) .(ys ∷ yss) (_∷_ {x} {xs} {ys} {yss} r rs) =
  ∈∈→∷cartesian x xs ys (cartesian yss) (r , (∈*→∈cartesian xs yss rs))

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
