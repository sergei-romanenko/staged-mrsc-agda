module AbstractSc where

{- ### Schemes of different types of supercompilation ### -}

{-
As presented in the paper

Ilya G. Klyuchnikov, Sergei A. Romanenko. Formalizing and Implementing
Multi-Result Supercompilation.
In Third International Valentin Turchin Workshop on Metacomputation
(Proceedings of the Third International Valentin Turchin Workshop on
Metacomputation. Pereslavl-Zalessky, Russia, July 5-9, 2012).
A.V. Klimov and S.A. Romanenko, Ed. - Pereslavl-Zalessky: Ailamazyan
University of Pereslavl, 2012, 260 p. ISBN 978-5-901795-28-6, pages
142-164. 
-}

open import Data.Bool using (Bool; true; false)
open import Data.List
open import Data.Product
open import Data.Empty
open import Data.Maybe
open import Data.Star using(Star; ε; _◅_)

open import Relation.Nullary
open import Relation.Unary using (_∈_)
open import Relation.Binary.PropositionalEquality

open import Function using (_∘_)

{-
### Notation: ###

  g – a current graph of configurations
  β – a current node in a graph of configurations
  c – a configuration in a current node β
-}

record AbstractScStruct : Set₁ where

  field

    Graph : Set
    Configuration : Set
    Node : Set
    DriveInfo : Set

    conf : Node → Configuration

    foldable : (g : Graph)(β α : Node) → Set
    foldable? : (g : Graph)(β : Node) → Maybe Node
    fold : (g : Graph)(β α : Node) → Graph

    driveStep : Configuration → DriveInfo
    addChildren : (g : Graph)(β : Node)(cs : DriveInfo) → Graph

    rebuilding : (c : Configuration) → Configuration
    rebuildings : (c c' : Configuration) → Set
    rebuild : (g : Graph)(β : Node)(c' : Configuration) → Graph

    dangerous : (g : Graph)(β : Node) → Bool

    foldable?-correct : ∀ {g β α} → foldable? g β ≡ just α → foldable g β α
    rebuilding-correct : ∀ {c c'} → rebuilding c ≡ c' → c' ∈ rebuildings c

{-
### (a) SC: Deterministic (traditional) supercompilation ###

  (Fold)

  ∃α : foldable(g, β, α)
  ----------------------
  g → fold(g, β, α)

  (Drive)

  ∄α : foldable(g, β, α)
  ¬dangerous(g, β)
  cs = driveStep(c)
  --------------------------
  g → addChildren(g, β, cs)

  (Rebuild)

  ∄α : foldable(g, β, α)
  dangerous(g, β)
  c′ = rebuilding(g, c)
  ----------------------
  g → rebuild(g, β, c′)
-}

module AbstractSC (s : AbstractScStruct) where

  open AbstractScStruct s

  data _⊢SC_ (g : Graph) : Graph → Set where
    sc-fold : ∀ β α →
      (f : foldable? g β ≡ just α) →
        g ⊢SC fold g β α
    sc-drive : ∀ β cs →
      (¬f : foldable? g β ≡ nothing) →
      (¬w : dangerous g β ≡ false) →
      (d  : driveStep (conf β) ≡ cs) →
        g ⊢SC addChildren g β cs
    sc-rebuild : ∀ β c c' →
      (¬f : foldable? g β ≡ nothing) →
      (w  : dangerous g β ≡ true) →
      (r  : rebuilding c ≡ c') →
        g ⊢SC rebuild g β c'

{-

### (b) NDSC: Non-deterministic supercompilation (transformation relation) ###

  (Fold)

  ∃α : foldable(g, β, α)
  ----------------------
  g → fold(g, β, α)

  (Drive)

  ∄α : foldable(g, β, α)
  cs = driveStep(c)
  --------------------------
  g → addChildren(g, β, cs)

  (Rebuild)

  ∄α : foldable(g, β, α)
  c′ ∈ rebuildings(c)
  ----------------------
  g → rebuild(g, β, c′)

-}

module AbstractNDSC (s : AbstractScStruct) where

  open AbstractScStruct s

  data _⊢NDSC_ (g : Graph) : Graph → Set where
    ndsc-fold : ∀ {β α} →
      (f : foldable? g β ≡ just α) →
        g ⊢NDSC fold g β α
    ndsc-drive : ∀ {β cs} →
      (¬f : foldable? g β ≡ nothing) →
      (d  : driveStep (conf β) ≡ cs) →
        g ⊢NDSC addChildren g β cs
    ndsc-rebuild : ∀ {β c c'} →
      (¬f : foldable? g β ≡ nothing) →
      (rs : c' ∈ rebuildings c) →
        g ⊢NDSC rebuild g β c'

{-

### (c) MRSC: Multi-result supercompilation ###

  (Fold)

  ∃α : foldable(g, β, α)
  ----------------------
  g → fold(g, β, α)

  (Drive)

  ∄α : foldable(g, β, α)
  ¬dangerous(g, β)
  cs = driveStep(c)
  --------------------------
  g → addChildren(g, β, cs)

  (Rebuild)

  ∄α : foldable(g, β, α)
  c′ ∈ rebuildings(c)
  -----------------------------------------
  g → rebuild(g, β, c′)

-}

module AbstractMRSC (s : AbstractScStruct) where

  open AbstractScStruct s

  data _⊢MRSC_ (g : Graph) : Graph → Set where
    mrsc-fold : ∀ {β α} →
      (f : foldable? g β ≡ just α) →
        g ⊢MRSC fold g β α
    mrsc-drive : ∀ {β cs} →
      (¬f : foldable? g β ≡ nothing) →
      (¬w : dangerous g β ≡ false) →
      (d  : driveStep (conf β) ≡ cs) →
        g ⊢MRSC addChildren g β cs
    mrsc-rebuild : ∀ {β c c'} →
      (¬f : foldable? g β ≡ nothing) →
      (rs : c' ∈ rebuildings c) →
        g ⊢MRSC rebuild g β c'

-- Now let us prove some "natural" theorems.
-- A formal verification is useful
-- just to ensure that "the ends meet".

-- This model of supercompilation is extremely abstract.
-- So there is not much to prove.

module SC→MRSC→NDSC (s : AbstractScStruct) where

  open AbstractScStruct s
  open AbstractSC s
  open AbstractMRSC s
  open AbstractNDSC s

  SC→MRSC : ∀ {g g'} → g ⊢SC g' → g ⊢MRSC g'
  SC→MRSC (sc-fold β α f) =
    mrsc-fold f
  SC→MRSC (sc-drive β cs ¬f ¬w d) =
    mrsc-drive ¬f ¬w d
  SC→MRSC (sc-rebuild β c c' ¬f w r) =
    mrsc-rebuild ¬f (rebuilding-correct r)

  MRSC→NDSC : ∀ {g g'} → g ⊢MRSC g' → g ⊢NDSC g'
  MRSC→NDSC (mrsc-fold f) =
    ndsc-fold f
  MRSC→NDSC (mrsc-drive ¬f ¬w d) =
    ndsc-drive ¬f d
  MRSC→NDSC (mrsc-rebuild ¬f rs) =
    ndsc-rebuild ¬f rs

  SC→NDSC : ∀ {g g'} → g ⊢SC g' → g ⊢NDSC g'
  SC→NDSC = MRSC→NDSC ∘ SC→MRSC

  -- Transitive closures

  _⊢SC*_ : Graph → Graph → Set
  _⊢SC*_ = Star _⊢SC_

  _⊢NDSC*_ : Graph → Graph → Set
  _⊢NDSC*_ = Star _⊢NDSC_

  _⊢MRSC*_ : Graph → Graph → Set
  _⊢MRSC*_ = Star _⊢MRSC_

  -- Theorems

  SC*→MRSC* : ∀ {g g'} → g ⊢SC* g' → g ⊢MRSC* g'
  SC*→MRSC* ε = ε
  SC*→MRSC* (x ◅ xs) = SC→MRSC x ◅ SC*→MRSC* xs

  MRSC*→NDSC* : ∀ {g g'} → g ⊢MRSC* g' → g ⊢NDSC* g'
  MRSC*→NDSC* ε = ε
  MRSC*→NDSC* (x ◅ xs) = MRSC→NDSC x ◅ MRSC*→NDSC* xs

  SC*→NDSC* : ∀ {g g'} → g ⊢SC* g' → g ⊢NDSC* g'
  SC*→NDSC* = MRSC*→NDSC* ∘ SC*→MRSC*
