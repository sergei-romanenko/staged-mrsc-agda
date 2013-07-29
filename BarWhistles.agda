{-
In our model of big-step supercompilation whistles are assumed to be
"inductive bars". See:

Thierry Coquand. About Brouwer's fan theorem. September 23, 2003.
Revue internationale de philosophie, 2004/4 n° 230, p. 483-489.

http://www.cairn.info/revue-internationale-de-philosophie-2004-4-page-483.htm
http://www.cairn.info/load_pdf.php?ID_ARTICLE=RIP_230_0483

-}

module BarWhistles where

open import Level
  using ()
open import Data.Nat
open import Data.Nat.Properties
  using (≤′⇒≤; ≤⇒≤′; ≰⇒>)
open import Data.List as List
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.Vec as Vec
  using (Vec; []; _∷_; here; there; lookup)
open import Data.Product as Prod
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃; ∃₂)
open import Data.Sum as Sum
  using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Empty

open import Function
open import Function.Related as Related
  using ()
  renaming (module EquationalReasoning to ∼-Reasoning)

open import Relation.Nullary
open import Relation.Unary
  using (_∈_; _∪_; _⊆′_)
  renaming (Decidable to Decidable₁)

open import Relation.Binary
  using (Rel; _⇒_) renaming (Decidable to Decidable₂)
open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to P[_])

open import Induction.WellFounded


open import Util
open import AlmostFullRel

-- Bar

-- The set of finite paths such that either
-- (1) B h is valid right now; or
-- (2) for all possible a₁ ∷ h either
--     (1) B (a₁ ∷ h) is valid right now; or
--     (2) for all possible a₂ ∷ a₁ ∷ h either ...

data Bar {A : Set} (B : ∀ {m} → Vec A m → Set) :
         {n : ℕ} (h : Vec A n) → Set where
  now   : ∀ {n} {h : Vec A n} (bz : B h) → Bar B h
  later : ∀ {n} {h : Vec A n} (bs : ∀ c → Bar B (c ∷ h)) → Bar B h


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
    -- (In Coquand's terms, Bar Dangerous is required to be "an inductive bar".)
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
-- Bar D h is "monotonic" with respect to D.
--

-- bar-mono

bar-mono : ∀ {A : Set}
  {D D′ : ∀ {m} (h : Vec A m) → Set} →
  (∀ {m} → D {m} ⊆′ D′ {m}) →
  ∀ {n} (h : Vec A n) (b : Bar D h) → Bar D′ h
bar-mono D→D′ h (now bz) =
  now (D→D′ h bz)
bar-mono D→D′ h (later bs) =
  later (λ c → bar-mono D→D′ (c ∷ h) (bs c))

-- bar-⊎

bar-⊎ : ∀ {A : Set}
  {D P : ∀ {m} (h : Vec A m) → Set} →
  ∀ {n} (h : Vec A n) →
  Bar D h → Bar (D ∪ P) h
bar-⊎ = bar-mono (λ {m} h → inj₁)


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

record ⋑-World (A : Set) : Set₁ where

  infix 4 _⋑_ _⋑?_ _⋑⋑_  _⋑⋑?_

  field
    _⋑_ : A → A → Set
    _⋑?_ : Decidable₂ _⋑_

  -- _⋑⋑_

  _⋑⋑_ : ∀ {n : ℕ} (h : Vec A n) (c : A) → Set
  h ⋑⋑ c = VecAny (flip _⋑_ c) h

  -- ⋑↯

  ⋑↯ : {n : ℕ} (h : Vec A n) → Set
  ⋑↯ [] = ⊥
  ⋑↯ (c ∷ h) = h ⋑⋑ c ⊎ ⋑↯ h

  -- _⋑⋑?_

  _⋑⋑?_ : ∀ {n : ℕ} (h : Vec A n) (c : A) → Dec (h ⋑⋑ c)
  h ⋑⋑? c = vecAny (flip _⋑?_ c) h

  -- ⋑↯?

  ⋑↯? : {n : ℕ} (h : Vec A n) → Dec (⋑↯ h)
  ⋑↯? [] = no id
  ⋑↯? (c ∷ h) with h ⋑⋑? c
  ... | yes ⋑c = yes (inj₁ ⋑c)
  ... | no ¬⋑c with ⋑↯? h
  ... | yes dh = yes (inj₂ dh)
  ... | no ¬dh = no [ ¬⋑c , ¬dh ]′

-- ⋑-whistle

⋑-whistle : {A : Set} (⋑-world : ⋑-World A)
            (⋑-bar[] : Bar (⋑-World.⋑↯ ⋑-world) []) → BarWhistle A
⋑-whistle ⋑-world ⋑-bar[] =
  ⟨ ⋑↯ , ⋑↯? , ⋑-bar[] ⟩
  where open ⋑-World ⋑-world


--
-- Almost-full relations
--

module bar⋑↯⇔af⋑≫ {A : Set} (⋑-world : ⋑-World A) where

  open ⋑-World ⋑-world

  ⋑≫ : {n : ℕ} (h : Vec A n) (x y : A) → Set
  ⋑≫ h x y = ⋑↯ (x ∷ h) ⊎ (x ⋑ y)

  bar⋑↯→af⋑≫ : {n : ℕ} (h : Vec A n) → Bar ⋑↯ h →
               Almost-full (⋑≫ h)
  bar⋑↯→af⋑≫ h (now bz) =
    now (λ x y → inj₁ (inj₂ bz))
  bar⋑↯→af⋑≫ {n} h (later bs) =
    later {_≫_ = ⋑≫ h} (λ c → af-⇒ (step c) (afch c))
    where
    open ∼-Reasoning
    afch : ∀ c → Almost-full (⋑≫ (c ∷ h))
    afch c = bar⋑↯→af⋑≫ (c ∷ h) (bs c)
    step : ∀ c {x} {y} → ⋑≫ (c ∷ h) x y → ⋑≫ h x y ⊎ ⋑≫ h c x
    step c {x} {y} =
      ⋑≫ (c ∷ h) x y
        ↔⟨ _ ∎ ⟩
      (⋑↯ (x ∷ c ∷ h) ⊎ x ⋑ y)
        ↔⟨ _ ∎ ⟩
      ((c ∷ h ⋑⋑ x ⊎ ⋑↯ (c ∷ h)) ⊎ x ⋑ y)
        ↔⟨ _ ∎ ⟩
      (((c ⋑ x ⊎ h ⋑⋑ x) ⊎ (h ⋑⋑ c ⊎ ⋑↯ h)) ⊎ x ⋑ y)
        ∼⟨ [ [ [ inj₂ ∘ inj₂ , inj₁ ∘ inj₁ ∘ inj₁ ]′ ,
               [ inj₂ ∘ inj₁ ∘ inj₁ , inj₁ ∘ inj₁ ∘ inj₂ ]′ ]′ ,
             inj₁ ∘ inj₂ ]′ ⟩
      (((h ⋑⋑ x ⊎ ⋑↯ h) ⊎ x ⋑ y) ⊎ ((h ⋑⋑ c ⊎ ⋑↯ h) ⊎ c ⋑ x))
        ↔⟨ _ ∎ ⟩
      ((⋑↯ (x ∷ h) ⊎ x ⋑ y) ⊎ (⋑↯ (c ∷ h) ⊎ c ⋑ x))
        ↔⟨ _ ∎ ⟩
      (⋑≫ h x y ⊎ ⋑≫ h c x)
      ∎

  ----

  af⋑≫→bar⋑↯ : {n : ℕ} (h : Vec A n) →
    Almost-full (⋑≫ h) → Bar ⋑↯ h

  af⋑≫→bar⋑↯ {n} h (now z) = later (λ c → later (λ c′ → now (helper c′ c (z c c′))))
    where
    open ∼-Reasoning
    helper : ∀ c′ c → ⋑↯ (c ∷ h) ⊎ c ⋑ c′ → ⋑↯ (c′ ∷ c ∷ h)
    helper c′ c =
      (⋑↯ (c ∷ h) ⊎ c ⋑ c′)
        ∼⟨ [ inj₂ , inj₁ ∘ inj₁ ]′ ⟩
      ((c ⋑ c′ ⊎ (h ⋑⋑ c′)) ⊎ ⋑↯ (c ∷ h))
        ↔⟨ _ ∎ ⟩
      (c ∷ h ⋑⋑ c′ ⊎ ⋑↯ (c ∷ h))
        ↔⟨ _ ∎ ⟩
      ⋑↯ (c′ ∷ c ∷ h) ∎ 
  af⋑≫→bar⋑↯ {n} h (later s) = later (λ c → helper c)
    where
    open ∼-Reasoning
    step : ∀ c {x y} → ⋑≫ h x y ⊎ ⋑≫ h c x → ⋑≫ (c ∷ h) x y
    step c {x} {y} =
      (⋑≫ h x y ⊎ ⋑≫ h c x)
        ↔⟨ _ ∎ ⟩
      ((⋑↯ (x ∷ h) ⊎ x ⋑ y) ⊎ ⋑↯ (c ∷ h) ⊎ c ⋑ x)
        ↔⟨ _ ∎ ⟩
      (((h ⋑⋑ x ⊎ ⋑↯ h) ⊎ x ⋑ y) ⊎ (h ⋑⋑ c ⊎ ⋑↯ h) ⊎ c ⋑ x)
        ∼⟨ [ [ [ inj₁ ∘ inj₁ ∘ inj₂ , inj₁ ∘ inj₂ ∘ inj₂ ]′ , inj₂ ]′ ,
             [ [ inj₁ ∘ inj₂ ∘ inj₁ , inj₁ ∘ inj₂ ∘ inj₂ ]′ ,
                 inj₁ ∘ inj₁ ∘ inj₁ ]′ ]′ ⟩
      (((c ⋑ x ⊎ h ⋑⋑ x) ⊎ h ⋑⋑ c ⊎ ⋑↯ h) ⊎ x ⋑ y)
        ↔⟨ _ ∎ ⟩
      ((c ∷ h ⋑⋑ x ⊎ ⋑↯ (c ∷ h)) ⊎ x ⋑ y)
        ↔⟨ _ ∎ ⟩
      (⋑↯ (x ∷ c ∷ h) ⊎ x ⋑ y)
        ↔⟨ _ ∎ ⟩
      ⋑≫ (c ∷ h) x y
      ∎
    helper : ∀ c → Bar ⋑↯ (c ∷ h)
    helper c = af⋑≫→bar⋑↯ (c ∷ h) (af-⇒ (step c) (s c))

