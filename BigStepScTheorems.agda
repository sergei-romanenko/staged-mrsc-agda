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
  using (map-∈↔; concat-∈↔)
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

  MRSC→NDSC : ∀ {h : History} {c g} →
    h ⊢MRSC c ↪ g → h ⊢NDSC c ↪ g

  MRSC→NDSC (mrsc-fold f) =
    ndsc-fold f

  MRSC→NDSC (mrsc-build {h} {c} {cs} {gs} ¬f ¬w i ∀i⊢ci↪g) =
    ndsc-build ¬f i (pw-map ∀i⊢ci↪g)
    where
    pw-map : {cs : List Conf} {gs : List (Graph Conf)}
             (qs : Pointwise.Rel (_⊢MRSC_↪_ (c ∷ h)) cs gs) →
             Pointwise.Rel (_⊢NDSC_↪_ (c ∷ h)) cs gs
    pw-map [] = []
    pw-map (q ∷ qs) = MRSC→NDSC q ∷ (pw-map qs)


--
-- `naive-mrsc` is correct with respect to `_⊢MRSC_↪_`
--

module MRSC-correctness where

  open Membership-≡
  open BigStepMRSC scWorld

  -- naive-mrsc-sound′

  naive-mrsc-sound′ :
    (h : History) (b : Bar ↯ h) {c : Conf} {g : Graph Conf} →
    g ∈ naive-mrsc′ h b c → h ⊢MRSC c ↪ g

  naive-mrsc-sound′ h b {c} q with foldable? h c
  naive-mrsc-sound′ h b (here g≡) | yes f rewrite g≡ =
    mrsc-fold f
  naive-mrsc-sound′ h b (there ()) | yes f
  ... | no ¬f with ↯? h
  naive-mrsc-sound′ h b () | no ¬f | yes w
  naive-mrsc-sound′ h b {c} {g} q | no ¬f | no ¬w with b
  ... | now bz with ¬w bz
  ... | ()
  naive-mrsc-sound′ h b {c} {g} q | no ¬f | no ¬w | later bs =
    helper q
    where
    open ∼-Reasoning

    step : ∀ c → List (Graph Conf)
    step = naive-mrsc′ (c ∷ h) (bs c)

    gss : List (List (Graph Conf))
    gss = concat (map (cartesian ∘ map step) (c ⇉))

    helper₄ : ∀ cs gs →
      gs ∈ cartesian (map step cs) →
        Pointwise.Rel (_⊢MRSC_↪_ (c ∷ h)) cs gs
    helper₄ cs gs =
      gs ∈ cartesian (map step cs)
        ↔⟨ sym $ ∈*↔∈cartesian ⟩
      Pointwise.Rel _∈_ gs (map step cs)
        ∼⟨ ∈*∘map→ step cs ⟩
      Pointwise.Rel (λ c′ gs′ → gs′ ∈ step c′) cs gs
        ∼⟨ Pointwise.map (naive-mrsc-sound′ (c ∷ h) (bs c)) ⟩
      Pointwise.Rel (_⊢MRSC_↪_ (c ∷ h)) cs gs
      ∎

    helper₃ : ∀ gss′ css → gss′ ∈ map (cartesian ∘ map step) css → _
    helper₃ gss′ css =
      gss′ ∈ map (cartesian ∘ map step) css
        ↔⟨ sym $ map-∈↔ ⟩
      ∃ (λ cs → (cs ∈ css) × gss′ ≡ (cartesian ∘ map step) cs)
      ∎

    helper₂ : ∀ gs′ → gs′ ∈ gss → _
    helper₂ gs′ =
      gs′ ∈ gss
        ↔⟨ sym $ concat-∈↔ ⟩
      ∃ (λ gss′ → gs′ ∈ gss′ × gss′ ∈ map (cartesian ∘ map step) (c ⇉))
      ∎

    helper₁ : ∃ (λ gs′ → gs′ ∈ gss × g ≡ forth c gs′) → h ⊢MRSC c ↪ g
    helper₁ (gs′ , gs′∈gss , g≡) rewrite g≡ with helper₂ gs′ gs′∈gss
    ... | gss′ , gs′∈gss′ , gss′∈ with helper₃ gss′ (c ⇉) gss′∈
    ... | cs , cs∈css , gss′≡ rewrite gss′≡ =
      mrsc-build ¬f ¬w cs∈css (helper₄ cs gs′ gs′∈gss′)

    helper : g ∈ map (forth c) gss  → h ⊢MRSC c ↪ g
    helper =
      g ∈ map (forth c) gss
        ↔⟨ sym $ map-∈↔ ⟩
      ∃ (λ gs′ → gs′ ∈ gss × g ≡ forth c gs′)
        ∼⟨ helper₁ ⟩
      h ⊢MRSC c ↪ g
      ∎

  --
  -- naive-mrsc-sound
  --

  naive-mrsc-sound :
    {c : Conf} {g : Graph Conf} →
      g ∈ naive-mrsc c → [] ⊢MRSC c ↪ g

  naive-mrsc-sound =
    naive-mrsc-sound′ [] bar[]

  -- naive-mrsc-complete′

  naive-mrsc-complete′ :
    (h : History) (b : Bar ↯ h) {c : Conf} {g : Graph Conf} →
      h ⊢MRSC c ↪ g → g ∈ naive-mrsc′ h b c

  naive-mrsc-complete′ h b {c} q with foldable? h c
  naive-mrsc-complete′ h b (mrsc-fold f) | yes f′ =
    here refl
  naive-mrsc-complete′ h b (mrsc-build ¬f ¬w i s) | yes f =
    ⊥-elim (¬f f)
  naive-mrsc-complete′ h b q | no ¬f with ↯? h
  naive-mrsc-complete′ h b (mrsc-fold f) | no ¬f | yes w =
    ⊥-elim (¬f f)
  naive-mrsc-complete′ h b (mrsc-build _ ¬w i s) | no ¬f | yes w =
    ⊥-elim (¬w w)
  naive-mrsc-complete′ h b (mrsc-fold f) | no ¬f | no ¬w =
    ⊥-elim (¬f f)
  naive-mrsc-complete′ h b (mrsc-build _ _ i s) | no ¬f | no ¬w with b
  naive-mrsc-complete′ h b (mrsc-build _ _ i s) | no ¬f | no ¬w | now bz =
    ⊥-elim (¬w bz)
  naive-mrsc-complete′ h b {c} (mrsc-build {cs = cs} {gs = gs} _ _ cs∈c⇉ s)
    | no ¬f | no ¬w | later bs =
    helper (gs , gs∈gss , refl)
    where
    open ∼-Reasoning

    step = naive-mrsc′ (c ∷ h) (bs c)
    gsss = map (cartesian ∘ map step) (c ⇉)
    gss = concat gsss

    pw→cart : ∀ cs gs →
      Pointwise.Rel (_⊢MRSC_↪_ (c ∷ h)) cs gs →
        gs ∈ cartesian (map step cs)
    pw→cart cs gs =
      Pointwise.Rel (_⊢MRSC_↪_ (c ∷ h)) cs gs
        ∼⟨ Pointwise.map (naive-mrsc-complete′ (c ∷ h) (bs c)) ⟩
      Pointwise.Rel (λ c′ gs′ → gs′ ∈ step c′) cs gs
        ∼⟨ ∈*∘map← step cs ⟩
      Pointwise.Rel _∈_ gs (map step cs)
        ↔⟨ ∈*↔∈cartesian ⟩
      gs ∈ cartesian (map step cs)
      ∎

    →gss′∈gsss : ∀ gss′ → _ → gss′ ∈ gsss
    →gss′∈gsss gss′ =
        ∃ (λ cs′ → cs′ ∈ c ⇉ × gss′ ≡ cartesian (map step cs′))
        ↔⟨ map-∈↔ ⟩
      gss′ ∈ map (cartesian ∘ map step) (c ⇉)
        ≡⟨ refl ⟩
      gss′ ∈ gsss
      ∎

    →gs∈gss : _ → gs ∈ gss
    →gs∈gss =
      ∃ (λ gss′ → gs ∈ gss′ × gss′ ∈ gsss)
        ↔⟨ concat-∈↔ ⟩
      gs ∈ concat (map (cartesian ∘ map step) (c ⇉))
        ↔⟨ _ ∎ ⟩
      gs ∈ gss
      ∎

    gs∈cart : gs ∈ cartesian (map step cs)
    gs∈cart = pw→cart cs gs s

    cart∈gsss : cartesian (map step cs) ∈ gsss
    cart∈gsss = →gss′∈gsss (cartesian (map step cs)) (cs , cs∈c⇉ , refl)

    gs∈gss : gs ∈ gss
    gs∈gss = →gs∈gss (cartesian (map step cs) , gs∈cart , cart∈gsss)

    helper : _ → _
    helper =
      ∃ (λ gs′ → gs′ ∈ gss × forth c gs ≡ forth c gs′)
        ↔⟨ map-∈↔ ⟩
      (forth c gs) ∈ map (forth c) gss
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

  mutual

    -- naive≡lazy′

    naive≡lazy′ : (h : History) (b : Bar ↯ h) (c : Conf) →
      naive-mrsc′ h b c ≡ ⟪ lazy-mrsc′ h b c ⟫

    naive≡lazy′ h b c with foldable? h c
    ... | yes f = refl
    ... | no ¬f with ↯? h
    ... | yes w = refl
    ... | no ¬w with b
    ... | now bz with ¬w bz
    ... | ()
    naive≡lazy′ h b c | no ¬f | no ¬w | later bs =
      cong (map (forth c)) (helper (c ⇉))
      where
      open ≡-Reasoning

      naive-step = naive-mrsc′ (c ∷ h) (bs c)
      lazy-step = lazy-mrsc′ (c ∷ h) (bs c)

      helper : ∀ css →
        concat (map (cartesian ∘ map naive-step) css) ≡
          ⟪ map (map lazy-step) css ⟫**

      helper [] = refl
      helper (cs ∷ css) = begin
        concat (map (cartesian ∘ map naive-step) (cs ∷ css))
          ≡⟨⟩
        cartesian (map naive-step cs) ++
          concat (map (cartesian ∘ map naive-step) css)
          ≡⟨ cong₂ _++_ (cong cartesian (map∘naive-mrsc′ (c ∷ h) (bs c) cs))
                        (helper css) ⟩
        cartesian ⟪ map lazy-step cs ⟫* ++ ⟪ map (map lazy-step) css ⟫**
          ≡⟨⟩
        ⟪ map (map lazy-step) (cs ∷ css) ⟫**
        ∎

    -- map∘naive-mrsc′

    map∘naive-mrsc′ : (h : History ) (b : Bar ↯ h) (cs : List Conf) →
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

  naive≡lazy : (c : Conf) →
    naive-mrsc c ≡ ⟪ lazy-mrsc c ⟫

  naive≡lazy c = naive≡lazy′ [] bar[] c
