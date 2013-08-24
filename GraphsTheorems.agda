--
-- Graphs of configurations
--

module GraphsTheorems where

open import Algebra
  using (module Monoid)
open import Data.Bool
  using (Bool; true; false; if_then_else_; not)
open import Data.Nat
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.List as List
open import Data.List.Properties
  using (∷-injective; map-compose; map-++-commute)
open import Data.List.Any
  using (Any; here; there; module Membership-≡)
open import Data.List.Any.Properties
  using (Any-cong; Any↔; ++↔; return↔; map↔; concat↔; ⊎↔)
open import Data.List.Any.Membership as MB
  using (map-∈↔)
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃; ∃₂)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty
open import Data.Maybe
  using (Maybe; nothing; just)
open import Data.Unit
  using (⊤; tt)

open import Function
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

private
  module LM {a} {A : Set a} = Monoid (List.monoid A)

open import Util
open import Graphs

--
-- `cl-empty` is correct
--

mutual

  -- cl-empty-correct

  cl-empty-correct : ∀ {C : Set} (gs : LazyGraph C) →
    ⟪ cl-empty gs ⟫ ≡ ⟪ gs ⟫

  cl-empty-correct Ø =
    refl
  cl-empty-correct (stop c) =
    refl
  cl-empty-correct (build c gsss)
    rewrite P.sym $ cl-empty**-correct gsss
    with cl-empty** gsss
  ... | [] = refl
  ... | gss′ ∷ gsss′ = refl

  -- cl-empty**-correct

  cl-empty**-correct : ∀ {C : Set} (gsss : List (List (LazyGraph C))) →
    ⟪ cl-empty** gsss ⟫** ≡ ⟪ gsss ⟫**

  cl-empty**-correct [] = refl
  cl-empty**-correct (gss ∷ gsss)
    with cl-empty-∧ gss | inspect cl-empty-∧ gss
  cl-empty**-correct (gss ∷ gsss)
    | nothing | P[ ≡nothing ]
    rewrite cl-empty-∧-nothing gss ≡nothing
          | cl-empty**-correct gsss = refl
  cl-empty**-correct (gss ∷ gsss)
    | just gss′ | P[ ≡just ]
    rewrite cl-empty-∧-just gss gss′ ≡just
          | cl-empty**-correct gsss = refl

  -- cl-empty-∧-nothing

  cl-empty-∧-nothing : ∀ {C : Set} (gss : List (LazyGraph C)) →
    cl-empty-∧ gss ≡ nothing → cartesian ⟪ gss ⟫* ≡ []

  cl-empty-∧-nothing [] ()
  cl-empty-∧-nothing (gs ∷ gss) eq  with cl-empty′ gs | inspect cl-empty′ gs
  cl-empty-∧-nothing (gs ∷ gss) eq | nothing | P[ ≡nothing ]
    rewrite P.sym $ cl-empty-nothing gs ≡nothing = refl
  cl-empty-∧-nothing (gs ∷ gss) eq | just gs′ | P[ ≡gs′ ]
    with cl-empty-∧ gss | inspect cl-empty-∧ gss
  cl-empty-∧-nothing (gs ∷ gss) eq | just gs′ | P[ ≡gs′ ] | nothing | P[ ≡gss′ ]
    rewrite cl-empty-∧-nothing gss ≡gss′ | cartesian2[] (⟪ gs ⟫)
    = refl
  cl-empty-∧-nothing (gs ∷ gss) () | just gs′ | P[ ≡gs′ ] | just gss′ | _

  -- cl-empty-∧-just

  cl-empty-∧-just : ∀ {C : Set} (gss gss′ : List (LazyGraph C)) →
    cl-empty-∧ gss ≡ just gss′ → ⟪ gss ⟫* ≡ ⟪ gss′ ⟫*

  cl-empty-∧-just [] [] eq = refl
  cl-empty-∧-just [] (gs′ ∷ gss′) ()
  cl-empty-∧-just (gs ∷ gss) gss′ eq with cl-empty′ gs | inspect cl-empty′ gs
  cl-empty-∧-just (gs ∷ gss) gss′ () | nothing | _
  ... | just gs₁ | ≡just-gs₁
    with cl-empty-∧ gss | inspect cl-empty-∧ gss
  cl-empty-∧-just (gs ∷ gss) gss′ ()
    | just gs₁ | ≡just-gs₁ | nothing | _ 
  cl-empty-∧-just (gs ∷ gss) .(gs₁ ∷ gss₁) refl
    | just gs₁ | P[ ≡gs₁ ] | just gss₁ | P[ ≡gss₁ ]
    rewrite cl-empty-just gs gs₁ ≡gs₁ | cl-empty-∧-just gss gss₁ ≡gss₁ = refl

  -- cl-empty-nothing

  cl-empty-nothing : ∀ {C : Set} (gs : LazyGraph C) →
    cl-empty′ gs ≡ nothing → [] ≡ ⟪ gs ⟫

  cl-empty-nothing gs ≡nothing with cl-empty-correct gs
  ... | []≡ rewrite ≡nothing = []≡

  -- cl-empty-just

  cl-empty-just : ∀ {C : Set} (gs gs′ : LazyGraph C) →
    cl-empty′ gs ≡ just gs′ → ⟪ gs′ ⟫ ≡ ⟪ gs ⟫

  cl-empty-just gs gs′ ≡just with cl-empty-correct gs
  ... | cl≡ rewrite ≡just  = cl≡


--
-- `cl-bad-conf` is sound
--

module ClBadConf-Sound where

  open Membership-≡

  -- cl-bad-conf*-is-map

  cl-bad-conf*-is-map :
    {C : Set} (bad : C → Bool) (gss : List (LazyGraph C)) →
    cl-bad-conf* bad gss ≡ map (cl-bad-conf bad) gss

  cl-bad-conf*-is-map bad [] =
    refl
  cl-bad-conf*-is-map bad (gs ∷ gss) =
    cong (_∷_ (cl-bad-conf bad gs)) (cl-bad-conf*-is-map bad gss)

  mutual

    cl-bad-conf-sound :
      {C : Set} (bad : C → Bool) (gs : LazyGraph C) →
      ⟪ cl-bad-conf bad gs ⟫ ⊆ ⟪ gs ⟫

    cl-bad-conf-sound bad Ø =
      id
    cl-bad-conf-sound bad (stop c) with bad c
    ... | true = λ ()
    ... | false = id
    cl-bad-conf-sound bad (build c gsss) {g} with bad c
    ... | true = λ ()
    ... | false =
      g ∈ map (forth c) ⟪ cl-bad-conf** bad gsss ⟫**
        ↔⟨ sym $ map-∈↔ ⟩
      ∃ (λ g′ → g′ ∈ ⟪ cl-bad-conf** bad gsss ⟫** × g ≡ forth c g′)
        ∼⟨ Σ.cong Inv.id (cl-bad-conf**-sound bad gsss ×-cong id) ⟩
      ∃ (λ g′ → g′ ∈ ⟪ gsss ⟫** × g ≡ forth c g′)
        ↔⟨ map-∈↔ ⟩
      g ∈ map (forth c) ⟪ gsss ⟫**
      ∎ where open ∼-Reasoning

    cl-bad-conf**-sound :
      {C : Set} (bad : C → Bool) (gsss : List (List (LazyGraph C))) →
      ⟪ cl-bad-conf** bad gsss ⟫** ⊆ ⟪ gsss ⟫**

    cl-bad-conf**-sound bad [] =
      id
    cl-bad-conf**-sound bad (gss ∷ gsss) {g} =
      g ∈ cartesian ⟪ cl-bad-conf* bad gss ⟫* ++ ⟪ cl-bad-conf** bad gsss ⟫**
       ↔⟨ sym $ ++↔ ⟩
      (g ∈ cartesian ⟪ cl-bad-conf* bad gss ⟫* ⊎
        g ∈ ⟪ cl-bad-conf** bad gsss ⟫**)
       ∼⟨ cl-bad-conf-cartesian bad gss ⊎-cong cl-bad-conf**-sound bad gsss ⟩
      (g ∈ cartesian ⟪ gss ⟫* ⊎ g ∈ ⟪ gsss ⟫**)
        ↔⟨ ++↔ ⟩
      g ∈ cartesian ⟪ gss ⟫* ++ ⟪ gsss ⟫**
      ∎ where open ∼-Reasoning

    -- cl-bad-conf-cartesian

    cl-bad-conf-cartesian :
      {C : Set} (bad : C → Bool) (gss : List (LazyGraph C)) →
      cartesian ⟪ cl-bad-conf* bad gss ⟫* ⊆ cartesian ⟪ gss ⟫*

    cl-bad-conf-cartesian {C} bad gss {gs} =
      cartesian-mono ⟪ cl-bad-conf* bad gss ⟫* ⟪ gss ⟫* (helper tt)
      where
      open ∼-Reasoning

      ∈*∘map : ∀ gss →
        Pointwise.Rel _⊆_ (map (⟪_⟫ ∘ cl-bad-conf bad) gss) (map ⟪_⟫ gss)
      ∈*∘map [] = []
      ∈*∘map (gs ∷ gss) = cl-bad-conf-sound bad gs ∷ ∈*∘map gss

      helper : ⊤ → Pointwise.Rel _⊆_ ⟪ cl-bad-conf* bad gss ⟫* ⟪ gss ⟫*
      helper =
        ⊤
          ∼⟨ const (∈*∘map gss) ⟩
        Pointwise.Rel _⊆_ (map (⟪_⟫ ∘ cl-bad-conf bad) gss) (map ⟪_⟫ gss)
          ∼⟨ subst (λ u → Pointwise.Rel _⊆_ u (map ⟪_⟫ gss))
                   (map-compose gss) ⟩
        Pointwise.Rel _⊆_ (map ⟪_⟫ (map (cl-bad-conf bad) gss)) (map ⟪_⟫ gss)
          ∼⟨ subst₂ (λ u v → Pointwise.Rel _⊆_ u v)
                    (P.sym $ ⟪⟫*-is-map (map (cl-bad-conf bad) gss))
                    (P.sym $ ⟪⟫*-is-map gss) ⟩
        Pointwise.Rel _⊆_ ⟪ map (cl-bad-conf bad) gss ⟫* ⟪ gss ⟫*
          ∼⟨ subst (λ u → Pointwise.Rel _⊆_ ⟪ u ⟫* ⟪ gss ⟫*)
                   (P.sym $ cl-bad-conf*-is-map bad gss) ⟩
        Pointwise.Rel _⊆_ ⟪ cl-bad-conf* bad gss ⟫* ⟪ gss ⟫*
        ∎


--
-- `cl-bad-conf` is correct with respect to `fl-bad-conf`.
--

module ClBadConf~FlBadConf where

  not∘bad-graph* : {C : Set} (bad : C → Bool) →
    not ∘ bad-graph* bad ≗ all (not ∘ bad-graph bad)

  not∘bad-graph* bad [] = refl
  not∘bad-graph* bad (gs ∷ gss) with bad-graph bad gs
  ... | true = refl
  ... | false = not∘bad-graph* bad gss

  mutual

    cl-bad-conf-correct : {C : Set} (bad : C → Bool) →
      --⟪_⟫ ∘ cl-bad-conf bad ≗ fl-bad-conf bad ∘ ⟪_⟫
      ∀ gs → ⟪ cl-bad-conf bad gs ⟫ ≡ fl-bad-conf bad ⟪ gs ⟫

    cl-bad-conf-correct bad Ø =
      refl
    cl-bad-conf-correct bad (stop c) with bad c
    ... | true = refl
    ... | false = refl
    cl-bad-conf-correct bad (build c gsss) with bad c | inspect bad c

    ... | true | P[ ≡true ] = begin
      []
        ≡⟨⟩
      map (forth c) []
        ≡⟨ cong (map (forth c)) (P.sym $ filter-false ⟪ gsss ⟫**) ⟩
      map (forth c) (filter (const false) ⟪ gsss ⟫**)
        ≡⟨ cong (map (forth c))
                (cong (flip filter ⟪ gsss ⟫**) helper₁) ⟩
      map (forth c) (filter ((not ∘ bad-graph bad) ∘ forth c) ⟪ gsss ⟫**)
        ≡⟨ P.sym $ filter∘map (not ∘ bad-graph bad)
                              (forth c) ⟪ gsss ⟫** ⟩
      filter (not ∘ bad-graph bad) (map (forth c) ⟪ gsss ⟫**)
        ≡⟨⟩
      fl-bad-conf bad (map (forth c) ⟪ gsss ⟫**)
      ∎
      where
      open ≡-Reasoning
      helper₁ : const false ≡ not ∘ bad-graph bad ∘ forth c
      helper₁ rewrite ≡true = refl

    ... | false | P[ ≡false ] = begin
      map (forth c) ⟪ cl-bad-conf** bad gsss ⟫**
        ≡⟨ cong (map (forth c)) (cl-bad-conf**-correct bad gsss) ⟩
      map (forth c) (filter (not ∘ bad-graph* bad) ⟪ gsss ⟫**)
        ≡⟨ cong (map (forth c))
                (cong (flip filter ⟪ gsss ⟫**) (P.sym $ helper₁)) ⟩
      map (forth c) (filter ((not ∘ bad-graph bad) ∘ forth c) ⟪ gsss ⟫**)
        ≡⟨ P.sym $ filter∘map (not ∘ bad-graph bad)
                              (forth c) ⟪ gsss ⟫** ⟩
      filter (not ∘ bad-graph bad) (map (forth c) ⟪ gsss ⟫**)
        ≡⟨⟩
      fl-bad-conf bad (map (forth c) ⟪ gsss ⟫**)
      ∎
      where
      open ≡-Reasoning
      helper₁ : not ∘ bad-graph bad ∘ forth c ≡ not ∘ bad-graph* bad
      helper₁ rewrite ≡false = refl

    -- cl-bad-conf**-correct

    cl-bad-conf**-correct : {C : Set} (bad : C → Bool) →
      ∀ gsss → ⟪ cl-bad-conf** bad gsss ⟫** ≡
                 filter (not ∘ bad-graph* bad) ⟪ gsss ⟫**


    cl-bad-conf**-correct bad [] = refl
    cl-bad-conf**-correct bad (gss ∷ gsss) = begin
      ⟪ cl-bad-conf** bad (gss ∷ gsss) ⟫**
        ≡⟨ refl ⟩
      cartesian ⟪ cl-bad-conf* bad gss ⟫* ++ ⟪ cl-bad-conf** bad gsss ⟫**
        ≡⟨ cong₂ _++_ (cartesian∘cl-bad* bad gss)
                      (cl-bad-conf**-correct bad gsss) ⟩
      filter (not ∘ bad-graph* bad) (cartesian ⟪ gss ⟫*) ++
      filter (not ∘ bad-graph* bad) ⟪ gsss ⟫**
        ≡⟨ P.sym $ filter-++-commute (not ∘ bad-graph* bad)
                                     (cartesian ⟪ gss ⟫*) ⟪ gsss ⟫** ⟩
      filter (not ∘ bad-graph* bad) (cartesian ⟪ gss ⟫* ++ ⟪ gsss ⟫**)
        ≡⟨⟩
      filter (not ∘ bad-graph* bad) ⟪ gss ∷ gsss ⟫**
      ∎
      where open ≡-Reasoning

    -- cartesian∘cl-bad*

    cartesian∘cl-bad* : {C : Set} (bad : C → Bool) →
      ∀ (gss : List (LazyGraph C)) →
      cartesian ⟪ cl-bad-conf* bad gss ⟫* ≡
      filter (not ∘ bad-graph* bad) (cartesian ⟪ gss ⟫*)

    cartesian∘cl-bad* bad gss = begin
      cartesian ⟪ cl-bad-conf* bad gss ⟫*
        ≡⟨ cong cartesian (cl-bad-conf*-correct bad gss) ⟩
      cartesian (map (fl-bad-conf bad) ⟪ gss ⟫*)
        ≡⟨⟩
      cartesian (map (filter (not ∘ bad-graph bad)) ⟪ gss ⟫*)
        ≡⟨ P.sym $ filter∘cartesian (not ∘ bad-graph bad) ⟪ gss ⟫* ⟩
      filter (all (not ∘ bad-graph bad)) (cartesian ⟪ gss ⟫*)
        ≡⟨ P.sym $ filter-cong (not∘bad-graph* bad) (cartesian ⟪ gss ⟫*) ⟩
      filter (not ∘ bad-graph* bad) (cartesian ⟪ gss ⟫*)
      ∎ where open ≡-Reasoning


    cl-bad-conf*-correct : {C : Set} (bad : C → Bool) →
      ∀ gss → ⟪ cl-bad-conf* bad gss ⟫* ≡ map (fl-bad-conf bad) ⟪ gss ⟫*

    cl-bad-conf*-correct bad [] = refl
    cl-bad-conf*-correct bad (gs ∷ gss) = begin
      ⟪ cl-bad-conf* bad (gs ∷ gss) ⟫*
        ≡⟨⟩
      ⟪ cl-bad-conf bad gs ⟫ ∷ ⟪ cl-bad-conf* bad gss ⟫*
        ≡⟨ cong₂ _∷_ (cl-bad-conf-correct bad gs)
                     (cl-bad-conf*-correct bad gss) ⟩
      fl-bad-conf bad ⟪ gs ⟫ ∷ map (fl-bad-conf bad) ⟪ gss ⟫*
        ≡⟨⟩
      map (fl-bad-conf bad) (⟪ gs ⟫ ∷ ⟪ gss ⟫*)
        ≡⟨⟩
      map (fl-bad-conf bad) ⟪ gs ∷ gss ⟫*
      ∎ where open ≡-Reasoning


--
-- `cl-min-size` is sound:
--
--  Let cl-min-size gs ≡ (k , gs′). Then
--     ⟪ gs′ ⟫ ⊆ ⟪ gs ⟫
--     k ≡ graph-size (hd ⟪ gs′ ⟫)
--
-- TODO: prove this formally