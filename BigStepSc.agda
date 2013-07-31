module BigStepSc where

{- ### Schemes of different types of big-step supercompilation ### -}

{-
A variation of the scheme presented in the paper

Ilya G. Klyuchnikov, Sergei A. Romanenko. Formalizing and Implementing
Multi-Result Supercompilation.
In Third International Valentin Turchin Workshop on Metacomputation
(Proceedings of the Third International Valentin Turchin Workshop on
Metacomputation. Pereslavl-Zalessky, Russia, July 5-9, 2012).
A.V. Klimov and S.A. Romanenko, Ed. - Pereslavl-Zalessky: Ailamazyan
University of Pereslavl, 2012, 260 p. ISBN 978-5-901795-28-6, pages
142-164. 
-}

open import Level
  using (Level)
open import Data.Nat
open import Data.Nat.Properties
  using (≤′⇒≤; ≤⇒≤′; ≰⇒>)
open import Data.List as List
open import Data.List.Properties
  using (map-compose; map-cong; foldr-fusion)
open import Data.List.Any
  using (Any; here; there)
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.Vec as Vec
  using (Vec; []; _∷_; lookup)
open import Relation.Binary.List.Pointwise
  using ([]; _∷_)
  renaming (Rel to Pointwise)
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty

open import Function

open import Relation.Nullary
open import Relation.Unary
  using () renaming (Decidable to Decidable₁)
open import Relation.Binary
  using (Setoid; DecSetoid)
open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to [_]ⁱ)

{-
open import Algebra
  using (module Monoid)
private
  module LM {a} {A : Set a} = Monoid (List.monoid A)
-}

open import Util
open import BarWhistles
open import Graphs


-- ScWorld

record ScWorld : Set₁ where

  field

    -- Configurations.
    Conf : Set

    -- The equality of configurations is decidable.
    _≟Conf_ : (c₁ c₂ : Conf) → Dec (c₁ ≡ c₂)

    -- c ⊑ c′ means that c′ is more general than c.
    _⊑_ : (c c′ : Conf) → Set

    -- ⊑ is decidable.
    _⊑?_ : (c c′ : Conf) → Dec (c ⊑ c′)

    -- Contractions (currently they are not taken into account).
    --Contr : Set

    -- Driving a configuration leads to a finite number of new ones.
    _⇉ : (c : Conf) → List Conf

    -- Rebuilding a configuration replaces it with an equivalent
    -- or more general one.
    -- We suppose that the number of possible rebuildings is finite!
    _↴ : (c : Conf) → List Conf

    -- A bar whistle.
    whistle : BarWhistle Conf

  open BarWhistle whistle public

  conf-setoid : Setoid _ _
  conf-setoid = P.setoid Conf

  conf-decSetoid : DecSetoid _ _
  conf-decSetoid = P.decSetoid _≟Conf_

  History : ℕ → Set
  History n = Vec Conf n

  Foldable : ∀ {n} (h : History n) (c : Conf) → Set
  Foldable {n} h c = AnyV (_⊑_ c) h

  foldable? : ∀ {n} (h : History n) (c : Conf) → Dec (Foldable h c)
  foldable? h c = anyV (_⊑?_ c) h


-- BigStepNDSC

module BigStepNDSC (scWorld : ScWorld) where

  open ScWorld scWorld

  infix 4 _⊢NDSC_↪_

  data _⊢NDSC_↪_ : ∀ {n} (h : History n) (c : Conf) (g : Graph Conf n)
                                                               → Set where
    ndsc-fold  : ∀ {n} {h : History n} {c}
      (f : Foldable h c) →
      h ⊢NDSC c ↪ back c (proj₁ f)
    ndsc-drive : ∀ {n h c}
      {gs : List (Graph Conf (suc n))}
      (¬f : ¬ Foldable h c) →
      (s  : Pointwise (_⊢NDSC_↪_ (c ∷ h)) (c ⇉) gs) →
      h ⊢NDSC c ↪ (case c gs)
    ndsc-rebuild : ∀ {n h c c′}
      {g  : Graph Conf (suc n)}
      (¬f : ¬ Foldable h c)
      (i  : Any (_≡_ c′) (c ↴)) →
      (s  : c ∷ h ⊢NDSC c′ ↪ g) →
      h ⊢NDSC c ↪ rebuild c g

--
-- Big-step multi-result supercompilation
--

-- BigStepMRSC

module BigStepMRSC (scWorld : ScWorld) where

  open ScWorld scWorld

  -- Relational big-step multi-result supercompilation.

  infix 4 _⊢MRSC_↪_

  data _⊢MRSC_↪_ : ∀ {n} (h : History n) (c : Conf) (g : Graph Conf n)
                                                               → Set where
    mrsc-fold  : ∀ {n} {h : History n} {c}
      (f : Foldable h c) →
      h ⊢MRSC c ↪ back c (proj₁ f)
    mrsc-drive : ∀ {n h c}
      {gs : List (Graph Conf (suc n))}
      (¬f : ¬ Foldable h c)
      (¬w : ¬ ↯ h) →
      (s  : Pointwise (_⊢MRSC_↪_ (c ∷ h)) (c ⇉) gs) →
      h ⊢MRSC c ↪ (case c gs)
    mrsc-rebuild : ∀ {n h c c′}
      {g  : Graph Conf (suc n)}
      (¬f : ¬ Foldable h c)
      (¬w : ¬ ↯ h) →
      (i  : Any (_≡_ c′) (c ↴)) →
      (s  : c ∷ h ⊢MRSC c′ ↪ g) →
      h ⊢MRSC c ↪ rebuild c g

  -- Functional big-step multi-result supercompilation.
  -- (The naive version builds Cartesian products immediately.)

  -- naive-mrsc′

  naive-mrsc′ : ∀ {n} (h : History n) (b : Bar ↯ h) (c : Conf) →
                  List (Graph Conf n)
  naive-mrsc′ {n} h b c with foldable? h c
  ... | yes (i , c⊑hi) = [ back c i ]
  ... | no ¬f with ↯? h
  ... | yes w = []
  ... | no ¬w with b
  ... | now bz = ⊥-elim (¬w bz)
  ... | later bs = drive! ++ rebuild!
    where
    drive! =
      map (case c)
          (cartesian (map (naive-mrsc′ (c ∷ h) (bs c)) (c ⇉)))
    rebuild! =
      map (rebuild c)
          (concat (map (naive-mrsc′ (c ∷ h) (bs c)) (c ↴)))
  
  -- naive-mrsc

  naive-mrsc : (c : Conf) → List(Graph Conf 0)
  naive-mrsc c = naive-mrsc′ [] bar[] c

  -- "Lazy" multi-result supercompilation.
  -- (Cartesian products are not immediately built.)

  -- lazy-mrsc is essentially a "staged" version of naive-mrsc
  -- with get-graphs being an "interpreter" that evaluates the "program"
  -- returned by lazy-mrsc.

  -- lazy-mrsc′

  lazy-mrsc′ : ∀ {n} (h : History n) (b : Bar ↯ h) (c : Conf) →
                  LazyGraph Conf n
  lazy-mrsc′ {n} h b c with foldable? h c
  ... | yes (i , c⊑hi) = back c i
  ... | no ¬f with ↯? h
  ... | yes w = Ø
  ... | no ¬w with b
  ... | now bz = ⁇ (¬w bz)
  ... | later bs = alt drive! rebuild!
    where
    drive!   = case c (map (lazy-mrsc′ (c ∷ h) (bs c)) (c ⇉))
    rebuild! = rebuild c (map (lazy-mrsc′ (c ∷ h) (bs c)) (c ↴))


  -- lazy-mrsc

  lazy-mrsc : (c : Conf) → LazyGraph Conf 0
  lazy-mrsc c = lazy-mrsc′ [] bar[] c

--
-- Extracting the residual graph from a proof
--

module GraphExtraction (scWorld : ScWorld) where
  open ScWorld scWorld
  open BigStepNDSC scWorld

  -- extractGraph

  extractGraph : ∀ {n} {h : History n} {c : Conf} {g : Graph Conf n}
    (p : h ⊢NDSC c ↪ g) → Graph Conf n

  extractGraph (ndsc-fold {c = c} (i , c⊑c′)) = back c i
  extractGraph (ndsc-drive {c = c} {gs = gs} ¬f ps) = case c gs
  extractGraph (ndsc-rebuild {c = c} {g = g} ¬f i p) = rebuild c g

  -- extractGraph-sound

  extractGraph-sound : ∀ {n} {h : History n} {c : Conf} {g : Graph Conf n}
    (p : h ⊢NDSC c ↪ g) → extractGraph p ≡ g

  extractGraph-sound (ndsc-fold f) = refl
  extractGraph-sound (ndsc-drive ¬f ps) = refl
  extractGraph-sound (ndsc-rebuild ¬f i p) = refl

