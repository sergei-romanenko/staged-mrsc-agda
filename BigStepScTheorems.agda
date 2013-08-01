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
  using (Any↔; ++↔; return↔; map↔; concat↔; ⊎↔)
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.Vec as Vec
  using (Vec; []; _∷_; lookup)
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃; ∃₂)
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
open import Function.Related as Related
  using ()
  renaming (module EquationalReasoning to ∼-Reasoning)

import Relation.Binary.Sigma.Pointwise as Σ
open import Relation.Binary.Product.Pointwise
  using (_×-cong_)

open import Relation.Binary.List.Pointwise as Pointwise
  using ([]; _∷_)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to P[_])


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

  MRSC→NDSC (mrsc-fold f) =
    ndsc-fold f

  MRSC→NDSC (mrsc-drive {n} {h} {c} {gs} ¬f ¬w ∀i⊢ci↪g) =
    ndsc-drive ¬f (pw-map ∀i⊢ci↪g)
    where
    pw-map : ∀ {cs : List Conf} {gs : List (Graph Conf (suc n))}
               (qs : Pointwise.Rel (_⊢MRSC_↪_ (c ∷ h)) cs gs) →
             Pointwise.Rel (_⊢NDSC_↪_ (c ∷ h)) cs gs
    pw-map [] = []
    pw-map (q ∷ qs) = MRSC→NDSC q ∷ (pw-map qs)

  MRSC→NDSC (mrsc-rebuild ¬f ¬w i ⊢ci↪g) =
    ndsc-rebuild ¬f i (MRSC→NDSC ⊢ci↪g)


--
-- `naive-mrsc` is correct with respect to `_⊢MRSC_↪_`
--

module MRSC-correctness where

  open Membership-≡
  open BigStepMRSC scWorld

  -- naive-mrsc-sound′

  naive-mrsc-sound′ :
    ∀ {n} (h : History n) (b : Bar ↯ h) (c : Conf) (g : Graph Conf n) →
    g ∈ naive-mrsc′ h b c → h ⊢MRSC c ↪ g

  naive-mrsc-sound′ h b c g q with foldable? h c
  naive-mrsc-sound′ h b c g (here g≡) | yes (i , c⊑hi) rewrite g≡ =
    mrsc-fold (i , c⊑hi)
  naive-mrsc-sound′ h b c g (there ()) | yes (i , c⊑hi)
  ... | no ¬f with ↯? h
  naive-mrsc-sound′ {n} h b c g () | no ¬f | yes w
  ... | no ¬w with b
  ... | now bz = ⊥-elim (¬w bz)
  ... | later bs = helper (Inverse.from ++↔ ⟨$⟩ q)
    where
    step : ∀ c → List (Graph Conf _)
    step = naive-mrsc′ (c ∷ h) (bs c)

    gss₀ : List (List (Graph Conf _))
    gss₀ = cartesian (map step (c ⇉))

    gs₁ gs₂ : List (Graph Conf _)
    gs₁ = map (case c) gss₀
    gs₂ = map (rebuild c) (concat (map step (c ↴)))

    drive-helper : ∃ (λ gs′ → gs′ ∈ gss₀ × g ≡ case c gs′) ↔ g ∈ gs₁
    drive-helper =
      ∃ (λ gs′ → gs′ ∈ gss₀ × g ≡ case c gs′)
        ∼⟨ Any↔ ⟩
      Any (_≡_ g ∘ case c) (cartesian (map step (c ⇉)))
        ∼⟨ map↔ ⟩
      Any (_≡_ g) (map (case c) (cartesian (map step (c ⇉))))
        ∼⟨ _ ∎ ⟩
      g ∈ map (case c) (cartesian (map step (c ⇉)))
      ∎
      where open ∼-Reasoning

    rebuild-helper :
      ∃ (λ c′ → c′ ∈ c ↴ × ∃ (λ g′ → g′ ∈ step c′ × g ≡ rebuild c g′)) ↔
      g ∈ gs₂
    rebuild-helper =
      ∃ (λ c′ → c′ ∈ (c ↴) × ∃ (λ g′ → g′ ∈ step c′ × g ≡ rebuild c g′))
        ∼⟨ Σ.cong Inv.id (Inv.id ×-cong Any↔) ⟩
      ∃ (λ c′ → c′ ∈ (c ↴) × (Any (λ g′ → g ≡ rebuild c g′) (step c′)))
        ∼⟨ _ ∎ ⟩
      ∃ (λ c′ → c′ ∈ (c ↴) × (Any (λ g′ → g ≡ rebuild c g′) ∘ step) c′)
        ∼⟨ _ ∎ ⟩
      ∃ (λ c′ → c′ ∈ (c ↴) × (Any (_≡_ g ∘ rebuild c) ∘ step) c′)
        ∼⟨ Any↔ ⟩
      Any (Any (_≡_ g ∘ rebuild c) ∘ step) (c ↴)
        ∼⟨ map↔ ⟩
      Any (Any (_≡_ g ∘ rebuild c)) (map step (c ↴))
        ∼⟨ concat↔ ⟩
      Any (_≡_ g ∘ rebuild c) (concat (map step (c ↴)))
        ∼⟨ map↔ ⟩
      Any (_≡_ g) (map (rebuild c) (concat (map step (c ↴))))
        ∼⟨ _ ∎ ⟩
      g ∈ map (rebuild c) (concat (map step (c ↴)))
      ∎
      where open ∼-Reasoning

    helper : ∀ (q′ : g ∈ gs₁ ⊎ g ∈ gs₂) → h ⊢MRSC c ↪ g

    helper (inj₁ g∈gs₁) with Inverse.from drive-helper ⟨$⟩ g∈gs₁
    ... | gs′ , gs′∈gss₀ , g≡ rewrite g≡ =
      mrsc-drive ¬f ¬w pw
      where

      pw′ : ∀ cs′′ gs′′ → gs′′ ∈ cartesian (map step cs′′) →
              Pointwise.Rel (_⊢MRSC_↪_ (c ∷ h)) cs′′ gs′′
      pw′ [] .[] (here refl) = []
      pw′ [] gs′′ (there ())
      pw′ (c′′ ∷ cs′′) [] gs′′∈ =
        ⊥-elim ([]∉cartesian2 (step c′′) (cartesian (map step cs′′)) gs′′∈)
      pw′ (c′′ ∷ cs′′) (g′′ ∷ gs′′) gs′′∈
        with ∷cartesian→∈∈ g′′ gs′′ (step c′′) (cartesian (map step cs′′)) gs′′∈
      ... | g′′∈ , gs′′∈′  =
        naive-mrsc-sound′ (c ∷ h) (bs c) c′′ g′′ g′′∈ ∷
        pw′ cs′′ gs′′ gs′′∈′

      pw : Pointwise.Rel (_⊢MRSC_↪_ (c ∷ h)) (c ⇉) gs′
      pw = pw′ (c ⇉) gs′ gs′∈gss₀

    helper (inj₂ g∈gs₂) with Inverse.from rebuild-helper ⟨$⟩ g∈gs₂
    ... | c′ , c′∈c↴ , g′ , g′∈step-c′ , g≡ rewrite g≡ =
      mrsc-rebuild ¬f ¬w c′∈c↴ (naive-mrsc-sound′ (c ∷ h) (bs c) c′ g′ g′∈step-c′)

  naive-mrsc-sound :
    (c : Conf) (g : Graph Conf 0) →
      g ∈ naive-mrsc c → [] ⊢MRSC c ↪ g

  naive-mrsc-sound c g = naive-mrsc-sound′ [] bar[] c g

--
-- The main theorem:
-- `naive-mrsc` and `lazy-mrsc` produce the same bag of graphs!
--

module MRSC-naive≡lazy where

  open BigStepMRSC scWorld

  mutual

    -- naive≡lazy′

    naive≡lazy′ : ∀ {n} (h : History n) (b : Bar ↯ h) (c : Conf) →
      naive-mrsc′ h b c ≡ get-graphs (lazy-mrsc′ h b c)

    naive≡lazy′ {n} h b c with foldable? h c
    ... | yes (i , c⊑hi) = refl
    ... | no ¬f with ↯? h
    ... | yes w = refl
    ... | no ¬w with b
    ... | now bz = refl
    ... | later bs =
      cong₂ (λ u v → map (case c) (cartesian u) ++ map (rebuild c) (concat v))
        (map∘naive-mrsc′ (c ∷ h) (bs c) (c ⇉))
        (map∘naive-mrsc′ (c ∷ h) (bs c) (c ↴))

    -- map∘naive-mrsc′

    map∘naive-mrsc′ : ∀ {n} (h : History n) (b : Bar ↯ h)
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
