open import BigStepSc

module BigStepScTheorems (scWorld : ScWorld) where

open import Level
  using (Level)
open import Data.Nat
open import Data.List as List
open import Data.List.Properties
  using (map-compose; map-cong; foldr-fusion)
open import Data.List.Any
  using (Any; here; there; module Membership-≡)
open import Data.List.Any.Properties
  using (++↔)
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.Vec as Vec
  using (Vec; []; _∷_; lookup)
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty

open import Function
open import Function.Equality
  using (_⟨$⟩_)
open import Function.Equivalence as Eq
  using (_⇔_; module Equivalence)
open import Function.Inverse as Inv
  using (_↔_; module Inverse)

open import Relation.Binary.List.Pointwise
  using ([]; _∷_)
  renaming (Rel to Pointwise)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to [_]ⁱ)


open import Util
open import BarWhistles
open import Graphs

open ScWorld scWorld

--
-- MRSC is sound with respect to NDSC
--

module MRSC→NDSC′ where

  open BigStepNDSC scWorld
  open BigStepMRSC scWorld

  MRSC→NDSC : ∀ {n h c g} → _⊢MRSC_↪_ {n} h c g → h ⊢NDSC c ↪ g
  MRSC→NDSC (mrsc-fold f) = ndsc-fold f
  MRSC→NDSC (mrsc-drive {n} {h} {c} {gs} ¬f ¬w ∀i⊢ci↪g) =
    ndsc-drive ¬f (pw-map ∀i⊢ci↪g)
    where
    pw-map : ∀ {cs : List Conf} {gs : List (Graph Conf (suc n))}
               (qs : Pointwise (_⊢MRSC_↪_ (c ∷ h)) cs gs) →
             Pointwise (_⊢NDSC_↪_ (c ∷ h)) cs gs
    pw-map [] = []
    pw-map (q ∷ qs) = MRSC→NDSC q ∷ (pw-map qs)
  MRSC→NDSC (mrsc-rebuild ¬f ¬w i ⊢ci↪g) =
    ndsc-rebuild ¬f i (MRSC→NDSC ⊢ci↪g)


--
-- `naive-mrsc` is correct with respect to `_⊢MRSC_↪_`
--

{-
module MRSC-correctness where

  open Membership-≡
  open BigStepMRSC scWorld

  naive-mrsc-soundness′ :
    ∀ {n} (h : History n) (b : Bar Dangerous h) (c : Conf) (g : Graph Conf n) →
    g ∈ naive-mrsc′ h b c → h ⊢MRSC c ↪ g

  naive-mrsc-soundness′ h b c g q with foldable? h c
  naive-mrsc-soundness′ h b c g (here g≡) | yes (i , c⊑hi) rewrite g≡ =
    mrsc-fold (i , c⊑hi)
  naive-mrsc-soundness′ h b c g (there ()) | yes (i , c⊑hi)
  ... | no ¬f with dangerous? h
  naive-mrsc-soundness′ {n} h b c g () | no ¬f | yes w
  ... | no ¬w with b
  ... | now bz = ⊥-elim (¬w bz)
  ... | later bs = helper (Inverse.from ++↔ ⟨$⟩ q)
    where
    gs₁ gs₂ : List (Graph Conf _)
    gs₁ = map (case c) (cartesian (map (naive-mrsc′ (c ∷ h) (bs c)) (c ⇉)))
    gs₂ = map (rebuild c) (concat (map (naive-mrsc′ (c ∷ h) (bs c)) (c ↴)))

    helper : ∀ (q′ : g ∈ gs₁ ⊎ g ∈ gs₂) → h ⊢MRSC c ↪ g
    helper (inj₁ g∈gs₁) = {!mrsc-drive!}
    helper (inj₂ g∈gs₂) = {!mrsc-rebuild!}
-}

--
-- `naive-mrsc` and `lazy-mrsc` produce the same bag of graphs!
--

module MRSC-naive≡lazy where

  open BigStepMRSC scWorld

  mutual

    -- naive≡lazy′

    naive≡lazy′ : ∀ {n} (h : History n) (b : Bar Dangerous h) (c : Conf) →
      naive-mrsc′ h b c ≡ get-graphs (lazy-mrsc′ h b c)

    naive≡lazy′ {n} h b c with foldable? h c
    ... | yes (i , c⊑hi) = refl
    ... | no ¬f with dangerous? h
    ... | yes w = refl
    ... | no ¬w with b
    ... | now bz = refl
    ... | later bs =
      cong₂ (λ u v → map (case c) (cartesian u) ++ map (rebuild c) (concat v))
        (map∘naive-mrsc′ (c ∷ h) (bs c) (c ⇉))
        (map∘naive-mrsc′ (c ∷ h) (bs c) (c ↴))

    -- map∘naive-mrsc′

    map∘naive-mrsc′ : ∀ {n} (h : History n) (b : Bar Dangerous h)
                            (cs : List Conf) →
      map (naive-mrsc′ h b) cs ≡ get-graphs* (map (lazy-mrsc′ h b) cs)

    map∘naive-mrsc′ h b cs = begin
      map (naive-mrsc′ h b) cs
        ≡⟨ map-cong (naive≡lazy′ h b) cs ⟩
      map (get-graphs ∘ lazy-mrsc′ h b) cs
        ≡⟨ map-compose cs ⟩
      map get-graphs (map (lazy-mrsc′ h b) cs)
        ≡⟨ sym $ get-graphs*-is-map (map (lazy-mrsc′ h b) cs) ⟩
      get-graphs* (map (lazy-mrsc′ h b) cs)
      ∎
      where open ≡-Reasoning

  -- naive≡lazy

  naive≡lazy : ∀ (c : Conf) →
    naive-mrsc c ≡ get-graphs (lazy-mrsc c)
  naive≡lazy c = naive≡lazy′ [] bar[] c
