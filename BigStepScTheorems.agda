open import BigStepSc

module BigStepScTheorems (scWorld : ScWorld) where

open import Level
  using (Level)
open import Data.Nat
open import Data.List as List
open import Data.List.Properties
  using (map-compose; map-cong; foldr-fusion; map-++-commute)
open import Data.List.Any
  using (Any; here; there; module Membership-≡)
open import Data.List.Any.Properties
  using (Any↔; Any-cong; ++↔; return↔; map↔; concat↔; ⊎↔)
open import Data.List.Any.Membership as MB
  using (map-∈↔)
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
  using (_⇔_; equivalence; module Equivalence)
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
open import Relation.Binary.PropositionalEquality as P
  hiding (sym)
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

  MRSC→NDSC : ∀ {n} {h : History n} {c g} →
    h ⊢MRSC c ↪ g → h ⊢NDSC c ↪ g

  MRSC→NDSC (mrsc-fold f) =
    ndsc-fold f

  MRSC→NDSC (mrsc-split {n} {h} {c} {gs} ¬f ¬w ∀i⊢ci↪g) =
    ndsc-split ¬f (pw-map ∀i⊢ci↪g)
    where
    pw-map : ∀ {cs : List Conf} {gs : List (Graph Conf)}
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
    ∀ {n} (h : History n) (b : Bar ↯ h) {c : Conf} {g : Graph Conf} →
    g ∈ naive-mrsc′ h b c → h ⊢MRSC c ↪ g

  naive-mrsc-sound′ h b {c} q with foldable? h c
  naive-mrsc-sound′ h b (here g≡) | yes (i , c⊑hi) rewrite g≡ =
    mrsc-fold (i , c⊑hi)
  naive-mrsc-sound′ h b (there ()) | yes (i , c⊑hi)
  ... | no ¬f with ↯? h
  naive-mrsc-sound′ {n} h b () | no ¬f | yes w
  naive-mrsc-sound′ {n} h b {c} {g} q | no ¬f | no ¬w with b
  ... | now bz with ¬w bz
  ... | ()
  naive-mrsc-sound′ {n} h b {c} {g} q | no ¬f | no ¬w | later bs =
    helper (++→⊎ q)
    where
    open ∼-Reasoning

    step : ∀ c → List (Graph Conf)
    step = naive-mrsc′ (c ∷ h) (bs c)

    gss₀ : List (List (Graph Conf))
    gss₀ = cartesian (map step (c ⇉))

    gs₁ gs₂ : List (Graph Conf)
    gs₁ = map (forth c) gss₀
    gs₂ = map (λ g → forth c [ g ]) (concat (map step (c ↷)))

    ++→⊎ :
      g ∈ map (forth c) (cartesian (map step (c ⇉))) ++
          map (λ g → forth c [ g ]) (concat (map step (c ↷))) →
      g ∈ gs₁ ⊎ g ∈ gs₂
    ++→⊎ =
      g ∈ map (forth c) (cartesian (map step (c ⇉))) ++
          map (λ g → forth c [ g ]) (concat (map step (c ↷)))
        ≡⟨ refl ⟩
      g ∈ gs₁ ++ gs₂
        ↔⟨ sym $ ++↔ ⟩
      (g ∈ gs₁ ⊎ g ∈ gs₂)
      ∎

    split-helper :
       g ∈ gs₁ → ∃ (λ gs′ → gs′ ∈ gss₀ × g ≡ forth c gs′)
    split-helper =
      _ ↔⟨ sym $ map-∈↔ ⟩ _ ∎

    rebuild-helper :
      g ∈ map (λ g → forth c [ g ]) (concat (map step (c ↷))) →
      ∃ (λ c′ → c′ ∈ c ↷ × ∃ (λ g′ → g′ ∈ step c′ × g ≡ forth c [ g′ ]))
    rebuild-helper =
      _ ↔⟨ sym $ concat↔∘Any↔ g (λ g′ → forth c [ g′ ]) step (c ↷) ⟩ _ ∎

    helper : (g ∈ gs₁ ⊎ g ∈ gs₂) → h ⊢MRSC c ↪ g

    helper (inj₁ g∈gs₁) with split-helper g∈gs₁
    ... | gs′ , gs′∈gss₀ , g≡ rewrite g≡ =
      mrsc-split ¬f ¬w pw
      where

      pw₀ : ∀ {cs gs} → gs ∈ cartesian (map step cs) →
        Pointwise.Rel _∈_ gs (map step cs)
      pw₀ = _ ↔⟨ sym $ ∈*↔∈cartesian ⟩ _ ∎

      pw₁ : ∀ {cs gs} → Pointwise.Rel _∈_ gs (map step cs) →
              Pointwise.Rel (_⊢MRSC_↪_ (c ∷ h)) cs gs
      pw₁ {cs} gs∈* =
        Pointwise.map (naive-mrsc-sound′ (c ∷ h) (bs c)) (∈*∘map→ step cs gs∈*)

      pw₂ : ∀ {cs gs} → gs ∈ cartesian (map step cs) →
              Pointwise.Rel (_⊢MRSC_↪_ (c ∷ h)) cs gs

      pw₂ = pw₁ ∘ pw₀

      pw : Pointwise.Rel (_⊢MRSC_↪_ (c ∷ h)) (c ⇉) gs′
      pw = pw₂ gs′∈gss₀

    helper (inj₂ g∈gs₂) with rebuild-helper g∈gs₂
    ... | c′ , c′∈c↷ , g′ , g′∈step-c′ , g≡ rewrite g≡ =
      mrsc-rebuild ¬f ¬w c′∈c↷ (naive-mrsc-sound′ (c ∷ h) (bs c) g′∈step-c′)

  -- naive-mrsc-sound

  naive-mrsc-sound :
    {c : Conf} {g : Graph Conf} →
      g ∈ naive-mrsc c → [] ⊢MRSC c ↪ g

  naive-mrsc-sound =
    naive-mrsc-sound′ [] bar[]

  -- naive-mrsc-complete′

  naive-mrsc-complete′ :
    ∀ {n} (h : History n) (b : Bar ↯ h) {c : Conf} {g : Graph Conf} →
     h ⊢MRSC c ↪ g → g ∈ naive-mrsc′ h b c

  naive-mrsc-complete′ h b {c} q with foldable? h c
  naive-mrsc-complete′ h b (mrsc-fold f) | yes (i , c⊑hi) =
    here refl
  naive-mrsc-complete′ h b (mrsc-split ¬f ¬w s) | yes f =
    ⊥-elim (¬f f)
  naive-mrsc-complete′ h b (mrsc-rebuild ¬f ¬w i q) | yes f =
    ⊥-elim (¬f f)
  ... | no  ¬f  with ↯? h
  naive-mrsc-complete′ h b (mrsc-fold f) | no ¬f | yes w =
    ⊥-elim (¬f f)
  naive-mrsc-complete′ h b (mrsc-split _ ¬w s) | no ¬f | yes w =
    ⊥-elim (¬w w)
  naive-mrsc-complete′ h b (mrsc-rebuild _ ¬w i q) | no ¬f | yes w =
    ⊥-elim (¬w w)
  ... | no ¬w with b
  ... | now w = ⊥-elim (¬w w)
  naive-mrsc-complete′ h b (mrsc-fold f) | no ¬f | no ¬w | later bs =
    ⊥-elim (¬f f)
  naive-mrsc-complete′ h b {c} (mrsc-split {gs = gs} _ _ s)
    | no ¬f | no ¬w | later bs =
    helper (gs , gs∈gss₀ , refl)
    where
    open ∼-Reasoning

    step = naive-mrsc′ (c ∷ h) (bs c)
    gss₀ = cartesian (map step (c ⇉))

    gs₁ gs₂ : List (Graph Conf)
    gs₁ = map (forth c) gss₀
    gs₂ = map (λ g → forth c [ g ]) (concat (map step (c ↷)))

    pw : ∀ {cs gs} →
           Pointwise.Rel (_⊢MRSC_↪_ (c ∷ h)) cs gs →
           Pointwise.Rel _∈_ gs (map step cs)
    pw [] = []
    pw (r ∷ rs) = naive-mrsc-complete′ (c ∷ h) (bs c) r ∷ pw rs

    s→gs∈gss₀ : _ → gs ∈ gss₀
    s→gs∈gss₀ =
      Pointwise.Rel (_⊢MRSC_↪_ (c ∷ h)) (c ⇉) gs
        ∼⟨ pw ⟩
      Pointwise.Rel _∈_ gs (map step (c ⇉))
        ↔⟨ ∈*↔∈cartesian ⟩
      gs ∈ cartesian (map step (c ⇉))
        ↔⟨ _ ∎ ⟩
      gs ∈ gss₀
      ∎

    gs∈gss₀ : gs ∈ gss₀
    gs∈gss₀ = s→gs∈gss₀ s

    helper :
      _ → _
    helper =
      ∃ (λ gs′ → gs′ ∈ gss₀ × forth c gs ≡ forth c gs′)
        ↔⟨ map-∈↔ ⟩
      forth c gs ∈ map (forth c) gss₀
        ↔⟨ _ ∎ ⟩
      forth c gs ∈ gs₁
        ∼⟨ inj₁ ⟩
      (forth c gs ∈ gs₁ ⊎ forth c gs ∈ gs₂)
        ↔⟨ ++↔ ⟩
      forth c gs ∈ gs₁ ++ gs₂
      ∎

  naive-mrsc-complete′ .h b (mrsc-rebuild {n} {h} {c} {c′} {g} _ _ i q)
    | no ¬f | no ¬w | later bs =
    helper (c′ , i , g , g∈ , refl)
    where
    open ∼-Reasoning

    step = naive-mrsc′ (c ∷ h) (bs c)
    gs₁ = map (forth c) (cartesian (map step (c ⇉)))
    gs₂ = map (λ g → forth c [ g ]) (concat (map step (c ↷)))

    g∈ : g ∈ step c′
    g∈ = naive-mrsc-complete′ (c ∷ h) (bs c) q

    helper =
      ∃ (λ c′ → c′ ∈ c ↷ ×
           ∃ (λ g′ → g′ ∈ step c′ × forth c [ g ] ≡ forth c [ g′ ]))
        ↔⟨ concat↔∘Any↔ (forth c [ g ]) (λ g′ → forth c [ g′ ]) step (c ↷) ⟩
      forth c [ g ] ∈ gs₂
        ∼⟨ inj₂ ⟩
      (forth c [ g ] ∈ gs₁ ⊎ forth c [ g ] ∈ gs₂)
        ↔⟨ ++↔ ⟩
      forth c [ g ] ∈ gs₁ ++ gs₂
      ∎

  -- naive-mrsc-complete

  naive-mrsc-complete :
    {c : Conf} {g : Graph Conf} →
     [] ⊢MRSC c ↪ g → g ∈ naive-mrsc c

  naive-mrsc-complete r =
    naive-mrsc-complete′ [] bar[] r

  --
  -- ⊢MRSC↪⇔naive-mrsc
  --

  ⊢MRSC↪⇔naive-mrsc :
    {c : Conf} {g : Graph Conf} →
     [] ⊢MRSC c ↪ g ⇔ g ∈ naive-mrsc c

  ⊢MRSC↪⇔naive-mrsc =
    equivalence naive-mrsc-complete naive-mrsc-sound

--
-- The main theorem:
-- `naive-mrsc` and `lazy-mrsc` produce the same bag of graphs!
--

module MRSC-naive≡lazy where

  open BigStepMRSC scWorld

  -- ⟪⟫∘foldr

  ⟪⟫∘foldr : {C : Set} (gss : List (LazyGraph C)) →
    ⟪ foldr alt Ø gss ⟫ ≡ concat ⟪ gss ⟫*

  ⟪⟫∘foldr [] = refl
  ⟪⟫∘foldr (gs ∷ gss) = cong (_++_ ⟪ gs ⟫) (⟪⟫∘foldr gss)

  mutual

    -- naive≡lazy′

    naive≡lazy′ : ∀ {n} (h : History n) (b : Bar ↯ h) (c : Conf) →
      naive-mrsc′ h b c ≡ ⟪ lazy-mrsc′ h b c ⟫

    naive≡lazy′ {n} h b c with foldable? h c
    ... | yes (i , c⊑hi) = refl
    ... | no ¬f with ↯? h
    ... | yes w = refl
    ... | no ¬w with b
    ... | now bz with ¬w bz
    ... | ()
    naive≡lazy′ {n} h b c | no ¬f | no ¬w | later bs = begin
      map (forth c) (cartesian (map step (c ⇉))) ++
      map (λ g → forth c [ g ]) (concat (map step (c ↷)))
        ≡⟨ cong₂ _++_ (cong (map (forth c) ∘ cartesian)
                            (map∘naive-mrsc′ (c ∷ h) (bs c) (c ⇉)))
                      shuffle ⟩
      map (forth c) (cartesian ⟪ map lazy-step (c ⇉) ⟫*) ++
      map (forth c) (cartesian [ ⟪ foldr alt Ø (map lazy-step (c ↷)) ⟫ ]) 
      ∎
      where
      open ≡-Reasoning

      step = naive-mrsc′ (c ∷ h) (bs c)
      lazy-step = lazy-mrsc′ (c ∷ h) (bs c)

      shuffle-forth : ∀ {C : Set} (c : C) (gs : List (Graph C)) →
        map (λ g → forth c [ g ]) gs ≡ map (forth c) (cartesian [ gs ])

      shuffle-forth c [] = refl
      shuffle-forth c (g ∷ gs) =
        cong (_∷_ (forth c (g ∷ []))) (shuffle-forth c gs)

      shuffle :
        map (λ g → forth c [ g ]) (concat (map step (c ↷))) ≡
        map (forth c) (cartesian [ ⟪ foldr alt Ø (map lazy-step (c ↷)) ⟫ ])

      shuffle = begin
        map (λ g → forth c [ g ]) (concat (map step (c ↷)))
          ≡⟨ shuffle-forth c (concat (map step (c ↷))) ⟩
        map (forth c) (cartesian [ concat (map step (c ↷)) ])
          ≡⟨ cong (λ u → map (forth c) (cartesian [ concat u ]))
                  (map∘naive-mrsc′ (c ∷ h) (bs c) (c ↷)) ⟩
        map (forth c) (cartesian [ concat ⟪ map lazy-step (c ↷) ⟫* ])
          ≡⟨ cong (λ u → map (forth c) (cartesian [ u ]))
                  (P.sym $ ⟪⟫∘foldr (map lazy-step (c ↷))) ⟩
        map (forth c) (cartesian [ ⟪ foldr alt Ø (map lazy-step (c ↷)) ⟫ ])
        ∎

    -- map∘naive-mrsc′

    map∘naive-mrsc′ : ∀ {n} (h : History n) (b : Bar ↯ h)
                            (cs : List Conf) →
      map (naive-mrsc′ h b) cs ≡ ⟪ map (lazy-mrsc′ h b) cs ⟫*

    map∘naive-mrsc′ h b cs = begin
      map (naive-mrsc′ h b) cs
        ≡⟨ map-cong (naive≡lazy′ h b) cs ⟩
      map (⟪_⟫ ∘ lazy-mrsc′ h b) cs
        ≡⟨ map-compose cs ⟩
      map ⟪_⟫ (map (lazy-mrsc′ h b) cs)
        ≡⟨ P.sym $ ⟪⟫*-is-map (map (lazy-mrsc′ h b) cs) ⟩
      ⟪ map (lazy-mrsc′ h b) cs ⟫*
      ∎
      where open ≡-Reasoning

  --
  -- naive≡lazy
  --

  naive≡lazy : ∀ (c : Conf) →
    naive-mrsc c ≡ ⟪ lazy-mrsc c ⟫

  naive≡lazy c = naive≡lazy′ [] bar[] c
