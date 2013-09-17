module Statistics where

open import Data.Nat
open import Data.List as List
  using (List; []; _∷_; [_]; length; _++_; concat; map; filter;
         foldr; foldl; sum; product)
open import Data.List.Properties
  using (length-map; length-++; map-cong)
open import Data.List.Any as Any
  using (Any; here; there; module Membership-≡)
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃; ∃₂)
open import Data.Empty

open import Function

open import Relation.Nullary
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.PropositionalEquality as P
  hiding (sym)
  renaming ([_] to P[_])


open import Util
open import BarWhistles
open import Graphs
open import BigStepSc

--
-- Counting without generation
--

-- The main idea of staged supercompilation consists in
-- replacing the analysis of residual graphs with the analysis
-- of the program that generates the graphs.
--
-- Gathering statistics about graphs is just a special case of
-- such analysis. For example, it is possible to count the number of
-- residual graphs that would be produced without actually generating
-- the graphs.
--
-- Technically, we can define a function `#⟪⟫` that analyses
-- lazy graphs such that
--   #⟪ l ⟫ ≡ length ⟪ l ⟫

--
-- Counting results of `cartesian2` and `cartesian`.
--

-- length∘cartesian2

length∘cartesian2 : ∀ {A : Set} →
  (xs : List A) → (yss : List (List A)) →
  length (cartesian2 xs yss) ≡ length xs * length yss

length∘cartesian2 [] yss = refl
length∘cartesian2 (x ∷ xs) yss = begin
  length (map (_∷_ x) yss ++ cartesian2 xs yss)
    ≡⟨ length-++ (map (_∷_ x) yss) ⟩
  length (map (_∷_ x) yss) + length (cartesian2 xs yss)
    ≡⟨ cong₂ _+_ (length-map (_∷_ x) yss) (length∘cartesian2 xs yss) ⟩
  length yss + length xs * length yss
  ∎
  where open ≡-Reasoning

-- length∘cartesian

length∘cartesian : ∀ {A : Set} (xss : List (List A)) →
    length (cartesian xss) ≡ product (map length xss)

length∘cartesian [] = refl
length∘cartesian (xs ∷ xss) = begin
  length (cartesian (xs ∷ xss))
    ≡⟨⟩
  length (cartesian2 xs (cartesian xss))
    ≡⟨ length∘cartesian2 xs (cartesian xss) ⟩
  length xs * length (cartesian xss)
    ≡⟨ cong (_*_ (length xs)) (length∘cartesian xss) ⟩
  length xs * product (map length xss)
    ≡⟨⟩
  product ((length xs) ∷ map length xss)
    ≡⟨⟩
  product (map length (xs ∷ xss))
  ∎
  where open ≡-Reasoning

mutual

  -- #⟪_⟫

  #⟪_⟫ : ∀ {C : Set} (l : LazyGraph C) → ℕ

  #⟪ Ø ⟫ = 0
  #⟪ stop c ⟫ = 1
  #⟪ build c lss ⟫ = #⟪ lss ⟫⇉

  -- #⟪_⟫⇉

  #⟪_⟫⇉ : ∀ {C : Set} (lss : List (List (LazyGraph C))) → ℕ

  #⟪ [] ⟫⇉ = 0
  #⟪ ls ∷ lss ⟫⇉ = #⟪ ls ⟫* + #⟪ lss ⟫⇉

  -- #⟪_⟫*

  #⟪_⟫* : ∀ {C : Set} (ls : List (LazyGraph C)) → ℕ

  #⟪ [] ⟫* = 1
  #⟪ l ∷ ls ⟫* = #⟪ l ⟫ * #⟪ ls ⟫*

mutual

  -- #⟪⟫-correct

  #⟪⟫-correct : ∀ {C : Set} (l : LazyGraph C) →
   #⟪ l ⟫ ≡ length ⟪ l ⟫

  #⟪⟫-correct Ø = refl
  #⟪⟫-correct (stop c) = refl
  #⟪⟫-correct (build c lss) = begin
    #⟪ build c lss ⟫
      ≡⟨⟩
    #⟪ lss ⟫⇉
      ≡⟨ #⟪⟫⇉-correct lss ⟩
    length ⟪ lss ⟫⇉
      ≡⟨ P.sym $ length-map (forth c) ⟪ lss ⟫⇉ ⟩
    length (map (forth c) ⟪ lss ⟫⇉)
      ≡⟨⟩
    length ⟪ build c lss ⟫
    ∎
    where open ≡-Reasoning

  -- #⟪⟫⇉-correct

  #⟪⟫⇉-correct : ∀ {C : Set} (lss : List (List (LazyGraph C))) →
    #⟪ lss ⟫⇉ ≡ length ⟪ lss ⟫⇉

  #⟪⟫⇉-correct [] = refl
  #⟪⟫⇉-correct (ls ∷ lss) = begin
    #⟪ ls ∷ lss ⟫⇉
      ≡⟨⟩
    #⟪ ls ⟫* + #⟪ lss ⟫⇉
      ≡⟨ cong₂ _+_ (#⟪⟫*-correct ls) (#⟪⟫⇉-correct lss) ⟩
    length (cartesian ⟪ ls ⟫*) + length ⟪ lss ⟫⇉
      ≡⟨ P.sym $ length-++ (cartesian ⟪ ls ⟫*) ⟩
    length (cartesian ⟪ ls ⟫* ++ ⟪ lss ⟫⇉)
      ≡⟨⟩
    length ⟪ ls ∷ lss ⟫⇉
    ∎
    where open ≡-Reasoning

  -- #⟪⟫*-correct

  #⟪⟫*-correct :  ∀ {C : Set} (ls : List (LazyGraph C)) →
    #⟪ ls ⟫* ≡ length (cartesian ⟪ ls ⟫*)

  #⟪⟫*-correct [] = refl
  #⟪⟫*-correct (l ∷ ls) = begin
    #⟪ l ∷ ls ⟫*
      ≡⟨⟩
    #⟪ l ⟫ * #⟪ ls ⟫*
      ≡⟨ cong₂ _*_ (#⟪⟫-correct l) (#⟪⟫*-correct ls) ⟩
    length ⟪ l ⟫ * length (cartesian ⟪ ls ⟫*)
      ≡⟨ P.sym $ length∘cartesian2 ⟪ l ⟫ (cartesian ⟪ ls ⟫*) ⟩
    length (cartesian2 ⟪ l ⟫ (cartesian ⟪ ls ⟫*))
      ≡⟨⟩
    length (cartesian ⟪ l ∷ ls ⟫*)
    ∎
    where open ≡-Reasoning

--
-- Optimized version of `naive-mrsc` exploiting `cartesianMap`
--

module BigStepMRSC-cartesianMap (scWorld : ScWorld) where

  open ScWorld scWorld
  open BigStepMRSC scWorld

  --
  -- Functional big-step multi-result supercompilation.
  -- (The naive version builds Cartesian products immediately.)
  -- The difference from `naive-mrsc` is that `cartesian ∘ map`
  -- is replaced with `cartesianMap`.
  --

  -- naive-mrsc-cm′

  naive-mrsc-cm′ : ∀ (h : History) (b : Bar ↯ h) (c : Conf) →
                  List (Graph Conf)
  naive-mrsc-cm′ h b c with foldable? h c
  ... | yes f = [ back c ]
  ... | no ¬f with ↯? h
  ... | yes w = []
  ... | no ¬w with b
  ... | now bz with ¬w bz
  ... | ()
  naive-mrsc-cm′ h b c | no ¬f | no ¬w | later bs =
    map (forth c)
        (concat (map (cartesianMap (naive-mrsc-cm′ (c ∷ h) (bs c))) (c ⇉)))

  -- naive-mrsc

  naive-mrsc-cm : (c : Conf) → List (Graph Conf)
  naive-mrsc-cm c = naive-mrsc-cm′ [] bar[] c


  naive-mrsc-cm′-correct : ∀ (h : History) (b : Bar ↯ h) (c : Conf) →
    naive-mrsc-cm′ h b c ≡ naive-mrsc′ h b c

  naive-mrsc-cm′-correct h b c with foldable? h c
  ... | yes f = refl
  ... | no ¬f with ↯? h
  ... | yes w = refl
  ... | no ¬w with b
  ... | now bz with ¬w bz
  ... | ()
  naive-mrsc-cm′-correct h b c | no ¬f | no ¬w | later bs =
    cong (map (forth c) ∘ concat) (helper (c ⇉))
    where
    open EqR (P._→-setoid_ _ _)

    helper₂ : map (naive-mrsc-cm′ (c ∷ h) (bs c)) ≗
              map (naive-mrsc′ (c ∷ h) (bs c))
    helper₂ = map-cong (naive-mrsc-cm′-correct (c ∷ h) (bs c))

    helper : map (cartesianMap (naive-mrsc-cm′ (c ∷ h) (bs c))) ≗
             map (cartesian ∘ map (naive-mrsc′ (c ∷ h) (bs c)))
    helper = begin
      map (cartesianMap (naive-mrsc-cm′ (c ∷ h) (bs c)))
        ≈⟨ map-cong (cartesianMap-correct (naive-mrsc-cm′ (c ∷ h) (bs c))) ⟩
      map (cartesian ∘ map (naive-mrsc-cm′ (c ∷ h) (bs c)))
        ≈⟨ map-cong (λ h → cong cartesian (helper₂ h)) ⟩
      map (cartesian ∘ map (naive-mrsc′ (c ∷ h) (bs c)))
      ∎

  -- naive-mrsc-cm-correct
  
  naive-mrsc-cm-correct : (c : Conf) →
    naive-mrsc-cm c ≡ naive-mrsc c

  naive-mrsc-cm-correct c =
    naive-mrsc-cm′-correct [] bar[] c
