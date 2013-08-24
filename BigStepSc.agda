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
open import Data.List.Any as Any
  using (Any; here; there; module Membership-≡)
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.Vec as Vec
  using (Vec; []; _∷_; lookup)
open import Relation.Binary.List.Pointwise as Pointwise
  using (Rel; []; _∷_)
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
  renaming ([_] to P[_])

open Membership-≡

open import Util
open import BarWhistles
open import Graphs


-- ScWorld

record ScWorld : Set₁ where

  field

    -- Configurations.
    Conf : Set

    -- c ⊑ c′ means that c is foldable to c′.
    _⊑_ : (c c′ : Conf) → Set

    -- ⊑ is decidable.
    _⊑?_ : (c c′ : Conf) → Dec (c ⊑ c′)


    -- Transforming a configuration decomposes it in a (finite) number
    -- of other configurations. Since this transformation my be
    -- non-deterministic, the result of the transformation is
    -- a list of lists of configurations.

    -- Sometimes, a configuration can be "decomposed" into a single
    -- configuration (in which case the transformation is usually called
    -- a "reduction" step). 
    _⇉ : (c : Conf) → List (List Conf)

    -- A bar whistle.
    whistle : BarWhistle Conf

  open BarWhistle whistle public

  History : Set
  History = List Conf

  Foldable : ∀ (h : History) (c : Conf) → Set
  Foldable h c = Any (_⊑_ c) h

  foldable? : ∀ (h : History) (c : Conf) → Dec (Foldable h c)
  foldable? h c = Any.any (_⊑?_ c) h

-- If we need labeled edges in the graph of configurations,
-- the labels can be hidden inside configurations.
-- ("Configurations" do not have to be just symbolic expressions, as
-- they can contain any additional information.)

-- ScWorldWithLabels

record ScWorldWithLabels : Set₁ where

  field

    -- Configurations.
    Conf : Set
    -- Edge labels
    Label : Set

    -- c ⊑ c′ means that c is foldable to c′.
    _⊑_ : (c c′ : Conf) → Set

    -- ⊑ is decidable.
    _⊑?_ : (c c′ : Conf) → Dec (c ⊑ c′)

    -- Driving/splitting/rebuilding a configuration
    _⇉ : (c : Conf) → List (List (Label × Conf))

    -- A bar whistle.
    whistle : BarWhistle Conf

-- injectLabelsInScWorld

injectLabelsInScWorld : ScWorldWithLabels → ScWorld

injectLabelsInScWorld w = record
  { Conf = Label × Conf
  ; _⊑_ = _⊑′_
  ; _⊑?_ = _⊑?′_
  ; _⇉ = _⇉ ∘ proj₂
  ; whistle = inverseImageWhistle proj₂ whistle
  }
  where
  open ScWorldWithLabels w

  _⊑′_ : Label × Conf → Label × Conf → Set
  (l , c) ⊑′ (l′ , c′) = c ⊑ c′

  _⊑?′_ : (c c′ : Label × Conf) → Dec (proj₂ c ⊑ proj₂ c′)
  (l , c) ⊑?′ (l′ , c′) = c ⊑? c′

--
-- Big-step non-deterministic supercompilation
--

-- BigStepNDSC

module BigStepNDSC (scWorld : ScWorld) where

  open ScWorld scWorld

  infix 4 _⊢NDSC_↪_

  data _⊢NDSC_↪_ : ∀ (h : History) (c : Conf) (g : Graph Conf) → Set where
    ndsc-fold  : ∀ {h : History} {c}
      (f : Foldable h c) →
      h ⊢NDSC c ↪ back c

    ndsc-build : ∀ {h : History} {c}
      {cs : List (Conf)}
      {gs : List (Graph Conf)}
      (¬f : ¬ Foldable h c) →
      (i : cs ∈ c ⇉)
      (s  : Pointwise.Rel (_⊢NDSC_↪_ (c ∷ h)) cs gs) →
      h ⊢NDSC c ↪ (forth c gs)

--
-- Big-step multi-result supercompilation
--

-- BigStepMRSC

module BigStepMRSC (scWorld : ScWorld) where

  open ScWorld scWorld

  -- Relational big-step multi-result supercompilation.

  infix 4 _⊢MRSC_↪_

  data _⊢MRSC_↪_ : ∀ (h : History) (c : Conf) (g : Graph Conf) → Set where
    mrsc-fold  : ∀ {h : History} {c}
      (f : Foldable h c) →
      h ⊢MRSC c ↪ back c

    mrsc-build : ∀ {h : History} {c}
      {cs : List Conf}
      {gs : List (Graph Conf)}
      (¬f : ¬ Foldable h c)
      (¬w : ¬ ↯ h) →
      (i : cs ∈ c ⇉)
      (s  : Pointwise.Rel (_⊢MRSC_↪_ (c ∷ h)) cs gs) →
      h ⊢MRSC c ↪ (forth c gs)

  --
  -- Functional big-step multi-result supercompilation.
  -- (The naive version builds Cartesian products immediately.)
  --

  -- naive-mrsc′

  naive-mrsc′ : ∀ (h : History) (b : Bar ↯ h) (c : Conf) →
                  List (Graph Conf)
  naive-mrsc′ h b c with foldable? h c
  ... | yes f = [ back c ]
  ... | no ¬f with ↯? h
  ... | yes w = []
  ... | no ¬w with b
  ... | now bz with ¬w bz
  ... | ()
  naive-mrsc′ h b c | no ¬f | no ¬w | later bs =
    map (forth c)
        (concat (map (cartesian ∘ map (naive-mrsc′ (c ∷ h) (bs c))) (c ⇉)))

  -- naive-mrsc

  naive-mrsc : (c : Conf) → List (Graph Conf)
  naive-mrsc c = naive-mrsc′ [] bar[] c

  -- "Lazy" multi-result supercompilation.
  -- (Cartesian products are not immediately built.)

  -- lazy-mrsc is essentially a "staged" version of naive-mrsc
  -- with get-graphs being an "interpreter" that evaluates the "program"
  -- returned by lazy-mrsc.

  -- lazy-mrsc′

  lazy-mrsc′ : ∀ (h : History) (b : Bar ↯ h) (c : Conf) →
                  LazyGraph Conf
  lazy-mrsc′ h b c with foldable? h c
  ... | yes f = stop c
  ... | no ¬f with ↯? h
  ... | yes w = Ø
  ... | no ¬w with b
  ... | now bz with ¬w bz
  ... | ()
  lazy-mrsc′ h b c | no ¬f | no ¬w | later bs =
    build c (map (map (lazy-mrsc′ (c ∷ h) (bs c))) (c ⇉))

  -- lazy-mrsc

  lazy-mrsc : (c : Conf) → LazyGraph Conf
  lazy-mrsc c = lazy-mrsc′ [] bar[] c

--
-- Extracting the residual graph from a proof
--

module GraphExtraction (scWorld : ScWorld) where
  open ScWorld scWorld
  open BigStepNDSC scWorld

  -- extractGraph

  extractGraph : ∀ {h : History} {c : Conf} {g : Graph Conf}
    (p : h ⊢NDSC c ↪ g) → Graph Conf

  extractGraph (ndsc-fold {c = c} f) = back c
  extractGraph (ndsc-build {c = c} {gs = gs} ¬f i ps) = forth c gs

  -- extractGraph-sound

  extractGraph-sound : ∀ {h : History} {c : Conf} {g : Graph Conf}
    (p : h ⊢NDSC c ↪ g) → extractGraph p ≡ g

  extractGraph-sound (ndsc-fold f) = refl
  extractGraph-sound (ndsc-build ¬f i ps) = refl
