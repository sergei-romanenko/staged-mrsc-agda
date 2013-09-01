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
  using (List; []; _∷_; map; _++_; filter; all)
open import Data.List.Properties
  using (∷-injective; map-compose; map-++-commute)
open import Data.List.Any as Any
  using (Any; here; there; any; module Membership-≡)
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

  cl-empty-correct : ∀ {C : Set} (l : LazyGraph C) →
    ⟪ cl-empty l ⟫ ≡ ⟪ l ⟫

  cl-empty-correct Ø =
    refl
  cl-empty-correct (stop c) =
    refl
  cl-empty-correct (build c lss)
    rewrite P.sym $ cl-empty⇉-correct lss
    with cl-empty⇉ lss
  ... | [] = refl
  ... | ls′ ∷ lss′ = refl

  cl-empty⇉-correct : ∀ {C : Set} (lss : List (List (LazyGraph C))) →
    ⟪ cl-empty⇉ lss ⟫⇉ ≡ ⟪ lss ⟫⇉

  cl-empty⇉-correct [] = refl
  cl-empty⇉-correct (ls ∷ lss) with cl-empty* ls | inspect cl-empty* ls
  ... | ls′ | P[ ≡ls′ ] with any Ø≡? ls′
  ... | yes anyØ
    rewrite P.sym $ ≡ls′ | cl-empty-any-Ø ls anyØ
          | cl-empty⇉-correct lss = refl
  ... | no ¬anyØ
    rewrite P.sym $ ≡ls′ | cl-empty*-correct ls
          | cl-empty⇉-correct lss = refl

  -- cl-empty*-correct

  cl-empty*-correct :  ∀ {C : Set} (ls : List (LazyGraph C)) →
    ⟪ cl-empty* ls ⟫* ≡ ⟪ ls ⟫*

  cl-empty*-correct [] = refl
  cl-empty*-correct (l ∷ ls) =
    cong₂ _∷_ (cl-empty-correct l) (cl-empty*-correct ls)

  -- cl-empty-any-Ø

  cl-empty-any-Ø :  ∀ {C : Set} (ls : List (LazyGraph C)) →
    Any (_≡_ Ø) (cl-empty* ls) → cartesian ⟪ ls ⟫* ≡ []

  cl-empty-any-Ø [] ()
  cl-empty-any-Ø (l ∷ ls) eq  with cl-empty l | inspect cl-empty l
  ... | l′ | P[ ≡l′ ] with Ø≡? l′
  ... | yes Ø≡
    rewrite P.sym $ cl-empty-correct l | ≡l′ | P.sym $ Ø≡ = refl
  cl-empty-any-Ø (l ∷ ls) (here Ø≡) | l′ | P[ ≡l′ ] | no Ø≢ =
    ⊥-elim (Ø≢ Ø≡)
  cl-empty-any-Ø (l ∷ ls) (there eq) | l′ | P[ ≡l′ ] | no Ø≢
    rewrite cl-empty-any-Ø ls eq | cartesian2[] ⟪ l ⟫ = refl


--
-- `cl-bad-conf` is sound
--

module ClBadConf-Sound where

  open Membership-≡

  -- cl-bad-conf*-is-map

  cl-bad-conf*-is-map :
    {C : Set} (bad : C → Bool) (ls : List (LazyGraph C)) →
    cl-bad-conf* bad ls ≡ map (cl-bad-conf bad) ls

  cl-bad-conf*-is-map bad [] =
    refl
  cl-bad-conf*-is-map bad (l ∷ ls) =
    cong (_∷_ (cl-bad-conf bad l)) (cl-bad-conf*-is-map bad ls)

  mutual

    cl-bad-conf-sound :
      {C : Set} (bad : C → Bool) (l : LazyGraph C) →
      ⟪ cl-bad-conf bad l ⟫ ⊆ ⟪ l ⟫

    cl-bad-conf-sound bad Ø =
      id
    cl-bad-conf-sound bad (stop c) with bad c
    ... | true = λ ()
    ... | false = id
    cl-bad-conf-sound bad (build c lss) {g} with bad c
    ... | true = λ ()
    ... | false =
      g ∈ map (forth c) ⟪ cl-bad-conf⇉ bad lss ⟫⇉
        ↔⟨ sym $ map-∈↔ ⟩
      ∃ (λ g′ → g′ ∈ ⟪ cl-bad-conf⇉ bad lss ⟫⇉ × g ≡ forth c g′)
        ∼⟨ Σ.cong Inv.id (cl-bad-conf⇉-sound bad lss ×-cong id) ⟩
      ∃ (λ g′ → g′ ∈ ⟪ lss ⟫⇉ × g ≡ forth c g′)
        ↔⟨ map-∈↔ ⟩
      g ∈ map (forth c) ⟪ lss ⟫⇉
      ∎ where open ∼-Reasoning

    cl-bad-conf⇉-sound :
      {C : Set} (bad : C → Bool) (lss : List (List (LazyGraph C))) →
      ⟪ cl-bad-conf⇉ bad lss ⟫⇉ ⊆ ⟪ lss ⟫⇉

    cl-bad-conf⇉-sound bad [] =
      id
    cl-bad-conf⇉-sound bad (ls ∷ lss) {g} =
      g ∈ cartesian ⟪ cl-bad-conf* bad ls ⟫* ++ ⟪ cl-bad-conf⇉ bad lss ⟫⇉
       ↔⟨ sym $ ++↔ ⟩
      (g ∈ cartesian ⟪ cl-bad-conf* bad ls ⟫* ⊎
        g ∈ ⟪ cl-bad-conf⇉ bad lss ⟫⇉)
       ∼⟨ cl-bad-conf-cartesian bad ls ⊎-cong cl-bad-conf⇉-sound bad lss ⟩
      (g ∈ cartesian ⟪ ls ⟫* ⊎ g ∈ ⟪ lss ⟫⇉)
        ↔⟨ ++↔ ⟩
      g ∈ cartesian ⟪ ls ⟫* ++ ⟪ lss ⟫⇉
      ∎ where open ∼-Reasoning

    -- cl-bad-conf-cartesian

    cl-bad-conf-cartesian :
      {C : Set} (bad : C → Bool) (ls : List (LazyGraph C)) →
      cartesian ⟪ cl-bad-conf* bad ls ⟫* ⊆ cartesian ⟪ ls ⟫*

    cl-bad-conf-cartesian {C} bad ls {gs} =
      cartesian-mono ⟪ cl-bad-conf* bad ls ⟫* ⟪ ls ⟫* (helper tt)
      where
      open ∼-Reasoning

      ∈*∘map : ∀ ls →
        Pointwise.Rel _⊆_ (map (⟪_⟫ ∘ cl-bad-conf bad) ls) (map ⟪_⟫ ls)
      ∈*∘map [] = []
      ∈*∘map (l ∷ ls) = cl-bad-conf-sound bad l ∷ ∈*∘map ls

      helper : ⊤ → Pointwise.Rel _⊆_ ⟪ cl-bad-conf* bad ls ⟫* ⟪ ls ⟫*
      helper =
        ⊤
          ∼⟨ const (∈*∘map ls) ⟩
        Pointwise.Rel _⊆_ (map (⟪_⟫ ∘ cl-bad-conf bad) ls) (map ⟪_⟫ ls)
          ∼⟨ subst (λ u → Pointwise.Rel _⊆_ u (map ⟪_⟫ ls))
                   (map-compose ls) ⟩
        Pointwise.Rel _⊆_ (map ⟪_⟫ (map (cl-bad-conf bad) ls)) (map ⟪_⟫ ls)
          ∼⟨ subst₂ (λ u v → Pointwise.Rel _⊆_ u v)
                    (P.sym $ ⟪⟫*-is-map (map (cl-bad-conf bad) ls))
                    (P.sym $ ⟪⟫*-is-map ls) ⟩
        Pointwise.Rel _⊆_ ⟪ map (cl-bad-conf bad) ls ⟫* ⟪ ls ⟫*
          ∼⟨ subst (λ u → Pointwise.Rel _⊆_ ⟪ u ⟫* ⟪ ls ⟫*)
                   (P.sym $ cl-bad-conf*-is-map bad ls) ⟩
        Pointwise.Rel _⊆_ ⟪ cl-bad-conf* bad ls ⟫* ⟪ ls ⟫*
        ∎


--
-- `cl-bad-conf` is correct with respect to `fl-bad-conf`.
--

module ClBadConf~FlBadConf where

  not∘bad-graph* : {C : Set} (bad : C → Bool) →
    not ∘ bad-graph* bad ≗ all (not ∘ bad-graph bad)

  not∘bad-graph* bad [] = refl
  not∘bad-graph* bad (g ∷ gs) with bad-graph bad g
  ... | true = refl
  ... | false = not∘bad-graph* bad gs

  mutual

    cl-bad-conf-correct : {C : Set} (bad : C → Bool) →
      ⟪_⟫ ∘ cl-bad-conf bad ≗ fl-bad-conf bad ∘ ⟪_⟫

    cl-bad-conf-correct bad Ø =
      refl
    cl-bad-conf-correct bad (stop c) with bad c
    ... | true = refl
    ... | false = refl
    cl-bad-conf-correct bad (build c lss) with bad c | inspect bad c

    ... | true | P[ ≡true ] = begin
      []
        ≡⟨⟩
      map (forth c) []
        ≡⟨ cong (map (forth c)) (P.sym $ filter-false ⟪ lss ⟫⇉) ⟩
      map (forth c) (filter (const false) ⟪ lss ⟫⇉)
        ≡⟨ cong (map (forth c))
                (cong (flip filter ⟪ lss ⟫⇉) helper₁) ⟩
      map (forth c) (filter ((not ∘ bad-graph bad) ∘ forth c) ⟪ lss ⟫⇉)
        ≡⟨ P.sym $ filter∘map (not ∘ bad-graph bad)
                              (forth c) ⟪ lss ⟫⇉ ⟩
      filter (not ∘ bad-graph bad) (map (forth c) ⟪ lss ⟫⇉)
        ≡⟨⟩
      fl-bad-conf bad (map (forth c) ⟪ lss ⟫⇉)
      ∎
      where
      open ≡-Reasoning
      helper₁ : const false ≡ not ∘ bad-graph bad ∘ forth c
      helper₁ rewrite ≡true = refl

    ... | false | P[ ≡false ] = begin
      map (forth c) ⟪ cl-bad-conf⇉ bad lss ⟫⇉
        ≡⟨ cong (map (forth c)) (cl-bad-conf⇉-correct bad lss) ⟩
      map (forth c) (filter (not ∘ bad-graph* bad) ⟪ lss ⟫⇉)
        ≡⟨ cong (map (forth c))
                (cong (flip filter ⟪ lss ⟫⇉) (P.sym $ helper₁)) ⟩
      map (forth c) (filter ((not ∘ bad-graph bad) ∘ forth c) ⟪ lss ⟫⇉)
        ≡⟨ P.sym $ filter∘map (not ∘ bad-graph bad)
                              (forth c) ⟪ lss ⟫⇉ ⟩
      filter (not ∘ bad-graph bad) (map (forth c) ⟪ lss ⟫⇉)
        ≡⟨⟩
      fl-bad-conf bad (map (forth c) ⟪ lss ⟫⇉)
      ∎
      where
      open ≡-Reasoning
      helper₁ : not ∘ bad-graph bad ∘ forth c ≡ not ∘ bad-graph* bad
      helper₁ rewrite ≡false = refl

    -- cl-bad-conf⇉-correct

    cl-bad-conf⇉-correct : {C : Set} (bad : C → Bool) →
      ∀ lss → ⟪ cl-bad-conf⇉ bad lss ⟫⇉ ≡
                 filter (not ∘ bad-graph* bad) ⟪ lss ⟫⇉


    cl-bad-conf⇉-correct bad [] = refl
    cl-bad-conf⇉-correct bad (ls ∷ lss) = begin
      ⟪ cl-bad-conf⇉ bad (ls ∷ lss) ⟫⇉
        ≡⟨ refl ⟩
      cartesian ⟪ cl-bad-conf* bad ls ⟫* ++ ⟪ cl-bad-conf⇉ bad lss ⟫⇉
        ≡⟨ cong₂ _++_ (cartesian∘cl-bad* bad ls)
                      (cl-bad-conf⇉-correct bad lss) ⟩
      filter (not ∘ bad-graph* bad) (cartesian ⟪ ls ⟫*) ++
      filter (not ∘ bad-graph* bad) ⟪ lss ⟫⇉
        ≡⟨ P.sym $ filter-++-commute (not ∘ bad-graph* bad)
                                     (cartesian ⟪ ls ⟫*) ⟪ lss ⟫⇉ ⟩
      filter (not ∘ bad-graph* bad) (cartesian ⟪ ls ⟫* ++ ⟪ lss ⟫⇉)
        ≡⟨⟩
      filter (not ∘ bad-graph* bad) ⟪ ls ∷ lss ⟫⇉
      ∎
      where open ≡-Reasoning

    -- cartesian∘cl-bad*

    cartesian∘cl-bad* : {C : Set} (bad : C → Bool) →
      ∀ (ls : List (LazyGraph C)) →
      cartesian ⟪ cl-bad-conf* bad ls ⟫* ≡
      filter (not ∘ bad-graph* bad) (cartesian ⟪ ls ⟫*)

    cartesian∘cl-bad* bad ls = begin
      cartesian ⟪ cl-bad-conf* bad ls ⟫*
        ≡⟨ cong cartesian (cl-bad-conf*-correct bad ls) ⟩
      cartesian (map (fl-bad-conf bad) ⟪ ls ⟫*)
        ≡⟨⟩
      cartesian (map (filter (not ∘ bad-graph bad)) ⟪ ls ⟫*)
        ≡⟨ P.sym $ filter∘cartesian (not ∘ bad-graph bad) ⟪ ls ⟫* ⟩
      filter (all (not ∘ bad-graph bad)) (cartesian ⟪ ls ⟫*)
        ≡⟨ P.sym $ filter-cong (not∘bad-graph* bad) (cartesian ⟪ ls ⟫*) ⟩
      filter (not ∘ bad-graph* bad) (cartesian ⟪ ls ⟫*)
      ∎ where open ≡-Reasoning


    cl-bad-conf*-correct : {C : Set} (bad : C → Bool) →
      ∀ ls → ⟪ cl-bad-conf* bad ls ⟫* ≡ map (fl-bad-conf bad) ⟪ ls ⟫*

    cl-bad-conf*-correct bad [] = refl
    cl-bad-conf*-correct bad (l ∷ ls) = begin
      ⟪ cl-bad-conf* bad (l ∷ ls) ⟫*
        ≡⟨⟩
      ⟪ cl-bad-conf bad l ⟫ ∷ ⟪ cl-bad-conf* bad ls ⟫*
        ≡⟨ cong₂ _∷_ (cl-bad-conf-correct bad l)
                     (cl-bad-conf*-correct bad ls) ⟩
      fl-bad-conf bad ⟪ l ⟫ ∷ map (fl-bad-conf bad) ⟪ ls ⟫*
        ≡⟨⟩
      map (fl-bad-conf bad) (⟪ l ⟫ ∷ ⟪ ls ⟫*)
        ≡⟨⟩
      map (fl-bad-conf bad) ⟪ l ∷ ls ⟫*
      ∎ where open ≡-Reasoning


--
-- `cl-min-size` is sound:
--
--  Let cl-min-size l ≡ (k , l′). Then
--     ⟪ l′ ⟫ ⊆ ⟪ l ⟫
--     k ≡ graph-size (hd ⟪ l′ ⟫)
--
-- TODO: prove this formally