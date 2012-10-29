module Rules where

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

open import Data.Bool
open import Data.List
open import Data.Product
open import Data.Empty
open import Data.Maybe

open import Relation.Nullary
open import Relation.Unary using (_∈_)
open import Relation.Binary.PropositionalEquality

{-
### Notation: ###

g – a current graph of configurations
β – a current node in a graph of configurations
c – a configuration in a current node β
-}

postulate

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

  foldable?-correct : ∀ g β α → foldable? g β ≡ just α → foldable g β α
  rebuilding-correct : ∀ c c' → rebuilding c ≡ c' → c' ∈ rebuildings c

  dangerous : (g : Graph)(β : Node) → Bool

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

data _⊢SC_ (g : Graph) : Graph → Set where
  sc-fold : ∀ β α →
    foldable? g β ≡ just α →
    g ⊢SC fold g β α
  sc-drive : ∀ β cs →
    foldable? g β ≡ nothing →
    T(not (dangerous g β)) →
    driveStep (conf β) ≡ cs →
    g ⊢SC addChildren g β cs
  sc-rebuild : ∀ β c c' →
    foldable? g β ≡ nothing →
    T (dangerous g β) →
    rebuilding c ≡ c' →
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

data _⊢NDSC_ (g : Graph) : Graph → Set where
  ndsc-fold : ∀ β α →
    foldable? g β ≡ just α →
    g ⊢NDSC fold g β α
  ndsc-drive : ∀ β cs →
    foldable? g β ≡ nothing →
    driveStep (conf β) ≡ cs →
    g ⊢NDSC addChildren g β cs
  ndsc-rebuild : ∀ β c c' →
    foldable? g β ≡ nothing →
    c' ∈ rebuildings c →
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

data _⊢MRSC_ (g : Graph) : Graph → Set where
  mrsc-fold : ∀ β α →
    foldable? g β ≡ just α →
    g ⊢MRSC fold g β α
  mrsc-drive : ∀ β cs →
    foldable? g β ≡ nothing →
    T (not (dangerous g β)) →
    driveStep (conf β) ≡ cs →
    g ⊢MRSC addChildren g β cs
  mrsc-rebuild : ∀ β c c' →
    foldable? g β ≡ nothing →
    c' ∈ rebuildings c →
    g ⊢MRSC rebuild g β c'
