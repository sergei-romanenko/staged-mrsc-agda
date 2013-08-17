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
  cl-empty-correct (alt gs₁ gs₂)
    rewrite P.sym $ cl-empty-correct gs₁
          | P.sym $ cl-empty-correct gs₂
    with cl-empty′ gs₁ | cl-empty′ gs₂
  ... | nothing | nothing = refl
  ... | nothing | just gs′₂ = refl
  ... | just gs′₁ | nothing = begin
    ⟪ gs′₁ ⟫
      ≡⟨ P.sym $ proj₂ LM.identity ⟪ gs′₁ ⟫ ⟩
    ⟪ gs′₁ ⟫ ++ []
    ∎ where open ≡-Reasoning
  ... | just gs′₁ | just gs′₂ = refl
  cl-empty-correct (back c) =
    refl
  cl-empty-correct (split c gss) with cl-empty-∧ gss | inspect cl-empty-∧ gss
  ... | nothing | P[ ≡nothing ]
    rewrite cl-empty-∧-nothing gss ≡nothing = refl
  ... | just gss′ | P[ ≡just ]
    rewrite cl-empty-∧-just gss gss′ ≡just = refl
  cl-empty-correct (rebuild c gss)
    with cl-empty-∨ gss | inspect cl-empty-∨ gss
  ... | [] | P[ ≡[] ] rewrite cl-empty-∨-correct gss [] ≡[] = refl
  ... | gs′ ∷ gss′ | P[ ≡gs′∷gss′ ]
    rewrite cl-empty-∨-correct gss (gs′ ∷ gss′) ≡gs′∷gss′ = refl

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

  -- cl-empty-∨-correct

  cl-empty-∨-correct :
    ∀ {C : Set} (gss : List (LazyGraph C)) (gss′ : List (LazyGraph C)) →
    cl-empty-∨ gss ≡ gss′ →
      concat ⟪ gss ⟫* ≡ concat ⟪ gss′ ⟫*

  cl-empty-∨-correct [] [] ≡gss′ = refl
  cl-empty-∨-correct [] (x ∷ gss′) ()
  cl-empty-∨-correct (gs ∷ gss) gss′ ≡gss′
    with cl-empty′ gs | inspect cl-empty′ gs
  ... | nothing | P[ ≡nothing ]
    rewrite P.sym $ cl-empty-nothing gs ≡nothing
          | cl-empty-∨-correct gss gss′ ≡gss′ = refl
  cl-empty-∨-correct (gs ∷ gss) [] () | just gs₁ | P[ ≡just ]
  cl-empty-∨-correct (gs ∷ gss) (gs′  ∷ gss′) ≡gs′∷gss′ | just gs₁ | P[ ≡just ]
    with ∷-injective ≡gs′∷gss′
  ... | gs₁≡gs′ , ≡gss′
    rewrite gs₁≡gs′
          | cl-empty-just gs gs′ ≡just | cl-empty-∨-correct gss gss′ ≡gss′
    = refl

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
    cl-bad-conf-sound bad (alt gs₁ gs₂) {g}
      with cl-bad-conf-sound bad gs₁ | cl-bad-conf-sound bad gs₂
    ... | cl-gs₁⊆gs₁ | cl-gs₂⊆gs₂ =
      g ∈ (⟪ cl-bad-conf bad gs₁ ⟫ ++ ⟪ cl-bad-conf bad gs₂ ⟫)
        ↔⟨ sym $ ++↔ ⟩
      (g ∈ ⟪ cl-bad-conf bad gs₁ ⟫ ⊎ g ∈ ⟪ cl-bad-conf bad gs₂ ⟫)
        ∼⟨ cl-bad-conf-sound bad gs₁ ⊎-cong cl-bad-conf-sound bad gs₂ ⟩
      (g ∈ ⟪ gs₁ ⟫ ⊎ g ∈ ⟪ gs₂ ⟫)
        ↔⟨ ++↔ ⟩
      g ∈ (⟪ gs₁ ⟫ ++ ⟪ gs₂ ⟫)
      ∎ where open ∼-Reasoning
    cl-bad-conf-sound bad (back c) with bad c
    ... | true = λ ()
    ... | false = id
    cl-bad-conf-sound bad (split c gss) {g} with bad c 
    ... | true = λ ()
    ... | false =
      g ∈ map (split c) (cartesian ⟪ cl-bad-conf* bad gss ⟫*)
        ↔⟨ sym $ map-∈↔ ⟩
      (∃ λ g′ → g′ ∈ cartesian ⟪ cl-bad-conf* bad gss ⟫* × (g ≡ split c g′))
        ∼⟨ Σ.cong Inv.id (cl-bad-conf-cartesian bad gss ×-cong id) ⟩
      (∃ λ g′ → g′ ∈ cartesian ⟪ gss ⟫* × (g ≡ split c g′))
        ↔⟨ map-∈↔ ⟩
      g ∈ map (split c) (cartesian ⟪ gss ⟫*)
      ∎ where open ∼-Reasoning
    cl-bad-conf-sound bad (rebuild c gss) {g} with bad c
    ... | true = λ ()
    ... | false =
      g ∈ map (rebuild c) (concat ⟪ cl-bad-conf* bad gss ⟫*)
        ↔⟨ sym $ map-∈↔ ⟩
      (∃ λ g′ → g′ ∈ concat ⟪ cl-bad-conf* bad gss ⟫* × (g ≡ rebuild c g′))
        ∼⟨ Σ.cong Inv.id (cl-bad-conf-concat bad gss ×-cong id) ⟩
      (∃ λ g′ → g′ ∈ concat ⟪ gss ⟫* × (g ≡ rebuild c g′))
        ↔⟨ map-∈↔ ⟩
      g ∈ map (rebuild c) (concat ⟪ gss ⟫*)
      ∎ where open ∼-Reasoning

    -- cl-bad-conf-concat

    cl-bad-conf-concat :
      {C : Set} (bad : C → Bool) (gss : List (LazyGraph C)) →
      concat ⟪ cl-bad-conf* bad gss ⟫* ⊆ concat ⟪ gss ⟫*

    cl-bad-conf-concat bad [] =
      id
    cl-bad-conf-concat bad (gs ∷ gss) {g} =
      g ∈ (⟪ cl-bad-conf bad gs ⟫ ++ concat ⟪ cl-bad-conf* bad gss ⟫*)
        ↔⟨ sym $ ++↔ ⟩
      (g ∈ ⟪ cl-bad-conf bad gs ⟫ ⊎ g ∈ concat ⟪ cl-bad-conf* bad gss ⟫*)
        ∼⟨ cl-bad-conf-sound bad gs ⊎-cong cl-bad-conf-concat bad gss ⟩
      (g ∈ ⟪ gs ⟫ ⊎ g ∈ concat ⟪ gss ⟫*)
        ↔⟨ ++↔ ⟩
      g ∈ (⟪ gs ⟫ ++ concat ⟪ gss ⟫*)
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

    cl-bad-conf-correct bad Ø = refl

    cl-bad-conf-correct bad (alt gs₁ gs₂) = begin
      ⟪ cl-bad-conf bad gs₁ ⟫ ++ ⟪ cl-bad-conf bad gs₂ ⟫
        ≡⟨ cong₂ _++_ (cl-bad-conf-correct bad gs₁)
                      (cl-bad-conf-correct bad gs₂) ⟩
      fl-bad-conf bad ⟪ gs₁ ⟫ ++ fl-bad-conf bad ⟪ gs₂ ⟫
        ≡⟨ P.sym $ filter-++-commute (not ∘ bad-graph bad) ⟪ gs₁ ⟫ ⟪ gs₂ ⟫ ⟩
      fl-bad-conf bad (⟪ gs₁ ⟫ ++ ⟪ gs₂ ⟫)
      ∎
      where open ≡-Reasoning

    cl-bad-conf-correct bad (back c) with bad c
    ... | true = refl
    ... | false = refl

    cl-bad-conf-correct bad (split c gss) with bad c | inspect bad c
    ... | true | P[ ≡true ] = helper (cartesian ⟪ gss ⟫*)
      where
      open ≡-Reasoning
      helper₁ : const false ≡ not ∘ bad-graph bad ∘ split c
      helper₁ rewrite ≡true = refl

      helper : ∀ gs → [] ≡ filter (not ∘ bad-graph bad) (map (split c) gs)
      helper gs = begin
        []
          ≡⟨⟩
        map (split c) []
          ≡⟨ cong (map (split c)) (P.sym $ filter-false gs) ⟩
        map (split c) (filter (const false) gs)
          ≡⟨ cong (map (split c)) (cong (flip filter gs) helper₁) ⟩
        map (split c) (filter (not ∘ bad-graph bad ∘ split c) gs)
          ≡⟨ P.sym $ filter∘map (not ∘ bad-graph bad) (split c) gs ⟩
        filter (not ∘ bad-graph bad) (map (split c) gs)
        ∎
    ... | false | P[ ≡false ] = helper gss
      where
      open ≡-Reasoning

      helper₁ : not ∘ bad-graph bad ∘ split c ≡ not ∘ bad-graph* bad
      helper₁ rewrite ≡false = refl

      helper : ∀ gss →
        map (split c)(cartesian ⟪ cl-bad-conf* bad gss ⟫*) ≡
        fl-bad-conf bad (map (split c) (cartesian ⟪ gss ⟫*))

      helper gss = begin
        map (split c)(cartesian ⟪ cl-bad-conf* bad gss ⟫*)
          ≡⟨ cong (map (split c)) (cartesian∘cl-bad* bad gss) ⟩
        map (split c) (filter (not ∘ bad-graph* bad) (cartesian ⟪ gss ⟫*))
          ≡⟨ cong (map (split c)) (cong (flip filter (cartesian ⟪ gss ⟫*))
                                        (P.sym $ helper₁)) ⟩
        map (split c)
            (filter (not ∘ bad-graph bad ∘ split c) (cartesian ⟪ gss ⟫*))
          ≡⟨ P.sym $ filter∘map (not ∘ bad-graph bad)
                                (split c) (cartesian ⟪ gss ⟫*) ⟩
        filter (not ∘ bad-graph bad) (map (split c) (cartesian ⟪ gss ⟫*))
          ≡⟨⟩
        fl-bad-conf bad (map (split c) (cartesian ⟪ gss ⟫*))
        ∎

    cl-bad-conf-correct bad (rebuild c gss) with bad c | inspect bad c

    ... | true  | P[ ≡true  ] = helper (concat ⟪ gss ⟫*)
      where
      open ≡-Reasoning

      helper₁ :
        (λ g → false) ≡
        (λ g → not (bad-graph bad (rebuild c g)))
      helper₁ rewrite ≡true = refl

      helper : ∀ gs → [] ≡ fl-bad-conf bad (map (rebuild c) gs)
      helper gs = begin
        []
          ≡⟨⟩
        map (rebuild c) []
          ≡⟨ cong (map (rebuild c)) (P.sym $ filter-false gs) ⟩
        map (rebuild c) (filter (const false) gs)
          ≡⟨ cong (map (rebuild c)) (cong (flip filter gs) helper₁) ⟩
        map (rebuild c) (filter (not ∘ bad-graph bad ∘ rebuild c) gs)
          ≡⟨ P.sym $ filter∘map (not ∘ bad-graph bad) (rebuild c) gs ⟩
        filter (not ∘ bad-graph bad) (map (rebuild c) gs)
          ≡⟨⟩
        fl-bad-conf bad (map (rebuild c) gs)
        ∎

    ... | false | P[ ≡false ] = helper gss
      where
      open ≡-Reasoning

      helper₃ :
        (λ g → not (bad-graph bad g)) ≡
        (λ g → not (bad-graph bad (rebuild c g)))
      helper₃ rewrite ≡false = refl

      helper₂ : ∀ gs →
        map (rebuild c) ⟪ cl-bad-conf bad gs ⟫ ≡
        fl-bad-conf bad (map (rebuild c) ⟪ gs ⟫)
      helper₂ gs = begin
        map (rebuild c) ⟪ cl-bad-conf bad gs ⟫
          ≡⟨ cong (map (rebuild c)) (cl-bad-conf-correct bad gs) ⟩
        map (rebuild c) (fl-bad-conf bad ⟪ gs ⟫)
          ≡⟨ cong (map (rebuild c)) (cong (flip filter ⟪ gs ⟫) helper₃) ⟩
        map (rebuild c)
            (filter (λ g → not (bad-graph bad (rebuild c g))) ⟪ gs ⟫)
          ≡⟨⟩
        map (rebuild c) (filter (not ∘ bad-graph bad ∘ rebuild c) ⟪ gs ⟫)
          ≡⟨ P.sym $ filter∘map (not ∘ bad-graph bad) (rebuild c) ⟪ gs ⟫ ⟩
        filter (not ∘ bad-graph bad) (map (rebuild c) ⟪ gs ⟫)
          ≡⟨⟩
        fl-bad-conf bad (map (rebuild c) ⟪ gs ⟫)
        ∎

      helper : ∀ gss →
        map (rebuild c) (concat ⟪ cl-bad-conf* bad gss ⟫*) ≡
        fl-bad-conf bad (map (rebuild c) (concat ⟪ gss ⟫*))
      helper [] = refl
      helper (gs ∷ gss) = begin
        _
          ≡⟨ map-++-commute (rebuild c)
                            ⟪ cl-bad-conf bad gs ⟫
                            (concat ⟪ cl-bad-conf* bad gss ⟫*) ⟩
        map (rebuild c) ⟪ cl-bad-conf bad gs ⟫ ++
        map (rebuild c) (concat ⟪ cl-bad-conf* bad gss ⟫*)
          ≡⟨ cong₂ _++_ (helper₂ gs) (helper gss) ⟩
        fl-bad-conf bad (map (rebuild c) ⟪ gs ⟫) ++
        fl-bad-conf bad (map (rebuild c) (concat ⟪ gss ⟫*))
          ≡⟨ P.sym $ filter-++-commute (not ∘ bad-graph bad)
                                       (map (rebuild c) ⟪ gs ⟫)
                                       (map (rebuild c) (concat ⟪ gss ⟫*)) ⟩
        fl-bad-conf bad (map (rebuild c) ⟪ gs ⟫ ++
        map (rebuild c) (concat ⟪ gss ⟫*))
          ≡⟨ cong (fl-bad-conf bad)
                  (P.sym $ map-++-commute (rebuild c) 
                                          ⟪ gs ⟫ (concat ⟪ gss ⟫*)) ⟩
        fl-bad-conf bad (map (rebuild c) (⟪ gs ⟫ ++ concat ⟪ gss ⟫*))
        ∎

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