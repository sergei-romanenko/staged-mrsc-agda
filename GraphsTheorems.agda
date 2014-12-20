--
-- Graphs of configurations
--

module GraphsTheorems where

open import Algebra
  using (module Monoid)
open import Data.Bool
  using (Bool; true; false; if_then_else_; not; _∨_)
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
  ... | nothing | P[ ≡nothing ]
    rewrite cl-empty-nothing ls ≡nothing | cl-empty⇉-correct lss = refl
  ... | just ls′ | P[ ≡just ]
    rewrite cl-empty-just ls ls′ ≡just | cl-empty⇉-correct lss = refl

  -- cl-empty-nothing

  cl-empty-nothing : ∀ {C : Set} (ls : List (LazyGraph C)) →
    cl-empty* ls ≡ nothing → cartesian ⟪ ls ⟫* ≡ []

  cl-empty-nothing [] ()
  cl-empty-nothing (l ∷ ls) eq with cl-empty l | inspect cl-empty l
  ... | l′ | P[ ≡l′ ] with Ø≡? l′
  ... | yes Ø≡l′ rewrite P.sym $ cl-empty-correct l | ≡l′ | P.sym $ Ø≡l′ = refl
  cl-empty-nothing (l ∷ ls) eq | l′ | P[ ≡l′ ] | no Ø≢l′
    with cl-empty* ls | inspect cl-empty* ls
  cl-empty-nothing (l ∷ ls) () | l′ | P[ ≡l′ ] | no Ø≢l′ | just ls′ | _
  cl-empty-nothing (l ∷ ls) eq | l′ | P[ ≡l′ ] | no Ø≢l′
    | nothing | P[ ≡nothing ]
    rewrite cl-empty-nothing ls ≡nothing | cartesian2[] ⟪ l ⟫ = refl

  -- cl-empty-just

  cl-empty-just : ∀ {C : Set} (ls ls′ : List (LazyGraph C)) →
    cl-empty* ls ≡ just ls′ → cartesian ⟪ ls ⟫* ≡ cartesian ⟪ ls′ ⟫*

  cl-empty-just [] .[] refl = refl
  cl-empty-just (l ∷ ls) ls′ eq with cl-empty l | inspect cl-empty l
  ... | l₁ | P[ ≡l₁ ] with Ø≡? l₁
  cl-empty-just (l ∷ ls) ls′ () | l₁ | P[ ≡l₁ ] | yes Ø≡l₁
  cl-empty-just (l ∷ ls) ls′ eq | l₁ | P[ ≡l₁ ] | no  Ø≢l₁
    with cl-empty* ls | inspect cl-empty* ls
  cl-empty-just (l ∷ ls) .(l₁ ∷ ls₁) refl | l₁ | P[ ≡l₁ ] | no Ø≢l₁
    | just ls₁ | P[ ≡just ]
    rewrite P.sym $ cl-empty-correct l | ≡l₁
          | cl-empty-just ls ls₁ ≡just = refl
  cl-empty-just (l ∷ ls) ls′ () | l₁ | P[ ≡l₁ ] | no Ø≢l₁
    | nothing | P[ ≡nothing ]

--
-- `cl-bad-conf` is sound
--

module ClBadConf-Sound (C : Set) (bad : C → Bool) where

  open Membership-≡

  -- cl-bad-conf*-is-map

  cl-bad-conf*-is-map :
    (ls : List (LazyGraph C)) →
      cl-bad-conf* bad ls ≡ map (cl-bad-conf bad) ls

  cl-bad-conf*-is-map [] =
    refl
  cl-bad-conf*-is-map (l ∷ ls) =
    cong (_∷_ (cl-bad-conf bad l)) (cl-bad-conf*-is-map ls)

  mutual

    cl-bad-conf-sound :
      (l : LazyGraph C) →
        ⟪ cl-bad-conf bad l ⟫ ⊆ ⟪ l ⟫

    cl-bad-conf-sound Ø =
      id
    cl-bad-conf-sound (stop c) with bad c
    ... | true = λ ()
    ... | false = id
    cl-bad-conf-sound (build c lss) {g} with bad c
    ... | true = λ ()
    ... | false =
      g ∈ map (forth c) ⟪ cl-bad-conf⇉ bad lss ⟫⇉
        ↔⟨ sym $ map-∈↔ ⟩
      ∃ (λ g′ → g′ ∈ ⟪ cl-bad-conf⇉ bad lss ⟫⇉ × g ≡ forth c g′)
        ∼⟨ Σ.cong Inv.id (cl-bad-conf⇉-sound lss ×-cong id) ⟩
      ∃ (λ g′ → g′ ∈ ⟪ lss ⟫⇉ × g ≡ forth c g′)
        ↔⟨ map-∈↔ ⟩
      g ∈ map (forth c) ⟪ lss ⟫⇉
      ∎ where open ∼-Reasoning

    cl-bad-conf⇉-sound :
      (lss : List (List (LazyGraph C))) →
        ⟪ cl-bad-conf⇉ bad lss ⟫⇉ ⊆ ⟪ lss ⟫⇉

    cl-bad-conf⇉-sound [] =
      id
    cl-bad-conf⇉-sound (ls ∷ lss) {g} =
      g ∈ cartesian ⟪ cl-bad-conf* bad ls ⟫* ++ ⟪ cl-bad-conf⇉ bad lss ⟫⇉
       ↔⟨ sym $ ++↔ ⟩
      (g ∈ cartesian ⟪ cl-bad-conf* bad ls ⟫* ⊎
        g ∈ ⟪ cl-bad-conf⇉ bad lss ⟫⇉)
       ∼⟨ cl-bad-conf-cartesian ls ⊎-cong cl-bad-conf⇉-sound lss ⟩
      (g ∈ cartesian ⟪ ls ⟫* ⊎ g ∈ ⟪ lss ⟫⇉)
        ↔⟨ ++↔ ⟩
      g ∈ cartesian ⟪ ls ⟫* ++ ⟪ lss ⟫⇉
      ∎ where open ∼-Reasoning

    -- cl-bad-conf-cartesian

    cl-bad-conf-cartesian :
      (ls : List (LazyGraph C)) →
        cartesian ⟪ cl-bad-conf* bad ls ⟫* ⊆ cartesian ⟪ ls ⟫*

    cl-bad-conf-cartesian ls {gs} =
      cartesian-mono ⟪ cl-bad-conf* bad ls ⟫* ⟪ ls ⟫* (helper tt)
      where
      open ∼-Reasoning

      ∈*∘map : ∀ ls →
        Pointwise.Rel _⊆_ (map (⟪_⟫ ∘ cl-bad-conf bad) ls) (map ⟪_⟫ ls)
      ∈*∘map [] = []
      ∈*∘map (l ∷ ls) = cl-bad-conf-sound l ∷ ∈*∘map ls

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
                   (P.sym $ cl-bad-conf*-is-map ls) ⟩
        Pointwise.Rel _⊆_ ⟪ cl-bad-conf* bad ls ⟫* ⟪ ls ⟫*
        ∎


--
-- `cl-bad-conf` is correct with respect to `fl-bad-conf`.
--

module ClBadConf~FlBadConf (C : Set) (bad : C → Bool) where

  not∘bad-graph* :
    not ∘ bad-graph* bad ≗ all (not ∘ bad-graph bad)

  not∘bad-graph* [] = refl
  not∘bad-graph* (g ∷ gs) with bad-graph bad g
  ... | true = refl
  ... | false = not∘bad-graph* gs

  not∘bad-graph : {c : C} {b : Bool} → bad c ≡ b →
    not ∘ _∨_ b ∘ bad-graph* bad ≡ not ∘ bad-graph bad ∘ forth c
  not∘bad-graph {c} {b} bad-c≡b = begin
    not ∘ _∨_ b ∘ bad-graph* bad
      ≡⟨ cong (λ bad-c → not ∘ _∨_ bad-c ∘ bad-graph* bad) (P.sym $ bad-c≡b) ⟩
    not ∘ _∨_ (bad c) ∘ bad-graph* bad
      ≡⟨⟩
    not ∘ bad-graph bad ∘ forth c
    ∎ where open ≡-Reasoning

  mutual

    cl-bad-conf-correct :
      ⟪_⟫ ∘ cl-bad-conf bad ≗ fl-bad-conf bad ∘ ⟪_⟫

    cl-bad-conf-correct Ø =
      refl
    cl-bad-conf-correct (stop c) with bad c
    ... | true = refl
    ... | false = refl
    cl-bad-conf-correct (build c lss) with bad c | inspect bad c

    ... | true | P[ ≡true ] = begin
      []
        ≡⟨⟩
      map (forth c) []
        ≡⟨ cong (map (forth c)) (P.sym $ filter-false ⟪ lss ⟫⇉) ⟩
      map (forth c) (filter (const false) ⟪ lss ⟫⇉)
        ≡⟨ cong (map (forth c))
                (cong (flip filter ⟪ lss ⟫⇉) (not∘bad-graph ≡true)) ⟩
      map (forth c) (filter ((not ∘ bad-graph bad) ∘ forth c) ⟪ lss ⟫⇉)
        ≡⟨ P.sym $ filter∘map (not ∘ bad-graph bad)
                              (forth c) ⟪ lss ⟫⇉ ⟩
      filter (not ∘ bad-graph bad) (map (forth c) ⟪ lss ⟫⇉)
        ≡⟨⟩
      fl-bad-conf bad (map (forth c) ⟪ lss ⟫⇉)
      ∎ where open ≡-Reasoning

    ... | false | P[ ≡false ] = begin
      map (forth c) ⟪ cl-bad-conf⇉ bad lss ⟫⇉
        ≡⟨ cong (map (forth c)) (cl-bad-conf⇉-correct lss) ⟩
      map (forth c) (filter (not ∘ bad-graph* bad) ⟪ lss ⟫⇉)
        ≡⟨ cong (map (forth c))
                (cong (flip filter ⟪ lss ⟫⇉) (not∘bad-graph ≡false)) ⟩
      map (forth c) (filter ((not ∘ bad-graph bad) ∘ forth c) ⟪ lss ⟫⇉)
        ≡⟨ P.sym $ filter∘map (not ∘ bad-graph bad)
                              (forth c) ⟪ lss ⟫⇉ ⟩
      filter (not ∘ bad-graph bad) (map (forth c) ⟪ lss ⟫⇉)
        ≡⟨⟩
      fl-bad-conf bad (map (forth c) ⟪ lss ⟫⇉)
      ∎ where open ≡-Reasoning

    -- cl-bad-conf⇉-correct

    cl-bad-conf⇉-correct :
      ∀ lss → ⟪ cl-bad-conf⇉ bad lss ⟫⇉ ≡
                 filter (not ∘ bad-graph* bad) ⟪ lss ⟫⇉

    cl-bad-conf⇉-correct [] = refl
    cl-bad-conf⇉-correct (ls ∷ lss) = begin
      ⟪ cl-bad-conf⇉ bad (ls ∷ lss) ⟫⇉
        ≡⟨ refl ⟩
      cartesian ⟪ cl-bad-conf* bad ls ⟫* ++ ⟪ cl-bad-conf⇉ bad lss ⟫⇉
        ≡⟨ cong₂ _++_ (cartesian∘cl-bad* ls)
                      (cl-bad-conf⇉-correct lss) ⟩
      filter (not ∘ bad-graph* bad) (cartesian ⟪ ls ⟫*) ++
      filter (not ∘ bad-graph* bad) ⟪ lss ⟫⇉
        ≡⟨ P.sym $ filter-++-commute (not ∘ bad-graph* bad)
                                     (cartesian ⟪ ls ⟫*) ⟪ lss ⟫⇉ ⟩
      filter (not ∘ bad-graph* bad) (cartesian ⟪ ls ⟫* ++ ⟪ lss ⟫⇉)
        ≡⟨⟩
      filter (not ∘ bad-graph* bad) ⟪ ls ∷ lss ⟫⇉
      ∎ where open ≡-Reasoning

    -- cartesian∘cl-bad*

    cartesian∘cl-bad* :
      ∀ (ls : List (LazyGraph C)) →
      cartesian ⟪ cl-bad-conf* bad ls ⟫* ≡
      filter (not ∘ bad-graph* bad) (cartesian ⟪ ls ⟫*)

    cartesian∘cl-bad* ls = begin
      cartesian ⟪ cl-bad-conf* bad ls ⟫*
        ≡⟨ cong cartesian (cl-bad-conf*-correct ls) ⟩
      cartesian (map (fl-bad-conf bad) ⟪ ls ⟫*)
        ≡⟨⟩
      cartesian (map (filter (not ∘ bad-graph bad)) ⟪ ls ⟫*)
        ≡⟨ P.sym $ filter∘cartesian (not ∘ bad-graph bad) ⟪ ls ⟫* ⟩
      filter (all (not ∘ bad-graph bad)) (cartesian ⟪ ls ⟫*)
        ≡⟨ P.sym $ filter-cong not∘bad-graph* (cartesian ⟪ ls ⟫*) ⟩
      filter (not ∘ bad-graph* bad) (cartesian ⟪ ls ⟫*)
      ∎ where open ≡-Reasoning


    cl-bad-conf*-correct :
      ∀ ls → ⟪ cl-bad-conf* bad ls ⟫* ≡ map (fl-bad-conf bad) ⟪ ls ⟫*

    cl-bad-conf*-correct [] = refl
    cl-bad-conf*-correct (l ∷ ls) = begin
      ⟪ cl-bad-conf* bad (l ∷ ls) ⟫*
        ≡⟨⟩
      ⟪ cl-bad-conf bad l ⟫ ∷ ⟪ cl-bad-conf* bad ls ⟫*
        ≡⟨ cong₂ _∷_ (cl-bad-conf-correct l)
                     (cl-bad-conf*-correct ls) ⟩
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
