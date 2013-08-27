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

-- Now we formulate an idealized model of big-step multi-result
-- supercompilation.

-- The knowledge about the input language a supercompiler deals with
-- is represented by a "world of supercompilation", which is a record
-- that specifies the following.
--
-- * `Conf` is the type of "configurations". Note that configurations are
--   not required to be just expressions with free variables! In general,
--   they may represent sets of states in any form/language and as well may
--   contain any _additional_ information.
-- 
-- * `_⊑_` is a "foldability relation". c ⊑ c′ means that c is foldable to c′.
--   (In such cases c′ is usually said to be " more general than c".)
--
-- * `_⊑?_` is a decision procedure for `_⊑_`. This procedure is necessary
--   for implementing supercompilation in functional form.
--
-- * `_⇉` is a function that gives a number of possible decompositions of
--   a configuration. Let `c` be a configuration and `cs` a list of
--   configurations such that `cs ∈ c`. Then `c` can be "reduced to"
--   (or "decomposed into") configurations in `cs`.
--
--   Suppose that driving is determinstic and, given a configuration `c`,
--   produces a list of configurations `c ⇊`. Suppose that rebuilding
--   (generalization, application of lemmas) is non-deterministic and
--   `c ↷` is the list of configurations that can be produced by
--   rebuilding. Then (in this special case) `_⇉` is implemented as follows:
--
--       c ⇉ = [ c ⇊ ] ++ map [_] (c ↷)
--
-- * `whistle` is a "bar whistle" that is used to ensure termination of
--   functional supercompilation (see the module `BarWhistles`).
--
-- * `History` is a list of configuration that have been produced
--   in order to reach the current configuration.
--
-- * `Foldable h c` means that `c` is foldable to a configuration in
--   the history `h`.
--
-- * `foldable? h c` decides whether `Foldable h c`.

-- ScWorld

record ScWorld : Set₁ where

  field
    Conf : Set
    _⊑_ : (c c′ : Conf) → Set
    _⊑?_ : (c c′ : Conf) → Dec (c ⊑ c′)
    _⇉ : (c : Conf) → List (List Conf)
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

  infix 4 _⊢NDSC_↪_ _⊢NDSC*_↪_

  data _⊢NDSC_↪_ : ∀ (h : History) (c : Conf) (g : Graph Conf) → Set
  _⊢NDSC*_↪_ : ∀ (h : History) (cs : List Conf) (gs : List (Graph Conf)) → Set

  h ⊢NDSC* cs ↪ gs = Pointwise.Rel (_⊢NDSC_↪_ h) cs gs

  data _⊢NDSC_↪_ where

    ndsc-fold  : ∀ {h : History} {c}
      (f : Foldable h c) →
      h ⊢NDSC c ↪ back c

    ndsc-build : ∀ {h : History} {c}
      {cs : List (Conf)} {gs : List (Graph Conf)}
      (¬f : ¬ Foldable h c) →
      (i : cs ∈ c ⇉)
      (s  : (c ∷ h) ⊢NDSC* cs ↪ gs) →
      h ⊢NDSC c ↪ forth c gs


--
-- Big-step multi-result supercompilation
--

-- BigStepMRSC

module BigStepMRSC (scWorld : ScWorld) where

  open ScWorld scWorld

  -- Relational big-step multi-result supercompilation.

  infix 4 _⊢MRSC_↪_ _⊢MRSC*_↪_

  data _⊢MRSC_↪_ : ∀ (h : History) (c : Conf) (g : Graph Conf) → Set
  _⊢MRSC*_↪_ : ∀ (h : History) (cs : List Conf) (gs : List (Graph Conf)) → Set

  h ⊢MRSC* cs ↪ gs = Pointwise.Rel (_⊢MRSC_↪_ h) cs gs

  data _⊢MRSC_↪_ where
    mrsc-fold  : ∀ {h : History} {c}
      (f : Foldable h c) →
      h ⊢MRSC c ↪ back c

    mrsc-build : ∀ {h : History} {c}
      {cs : List Conf} {gs : List (Graph Conf)}
      (¬f : ¬ Foldable h c)
      (¬w : ¬ ↯ h) →
      (i : cs ∈ c ⇉)
      (s  : (c ∷ h) ⊢MRSC* cs ↪ gs) →
      h ⊢MRSC c ↪ forth c gs

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
