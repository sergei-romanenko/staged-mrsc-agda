module Statistics where

open import Data.Nat
open import Data.List as List
  using (List; []; _∷_; [_]; length; _++_; concat; map; filter;
         foldr; foldl; sum; product)
open import Data.List.Properties
  using (length-map; length-++
        ; map-compose; map-cong; map-++-commute; sum-++-commute)
open import Data.List.Any as Any
  using (Any; here; there)
open import Data.Product as Prod
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃; ∃₂)
open import Data.Empty

open import Function

open import Relation.Nullary
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.PropositionalEquality as P
  hiding (sym)
  renaming ([_] to P[_])

import Data.Nat.Properties as NatProp
open NatProp.SemiringSolver


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

--
-- Counting nodes in collections of graphs
--
-- Let us find a function `%⟪_⟫`, such that
--   %⟪ l ⟫ = #⟪ l ⟫ , sum (map graph-size ⟪ l ⟫)
--

mutual

  -- %⟪_⟫

  %⟪_⟫ : {C : Set} (l : LazyGraph C) → ℕ × ℕ

  %⟪ Ø ⟫ = 0 , 0
  %⟪ stop c ⟫ = 1 , 1
  %⟪ build c lss ⟫ = %⟪ lss ⟫⇉

  -- %⟪_⟫⇉

  %⟪_⟫⇉ : {C : Set} (lss : List (List (LazyGraph C))) → ℕ × ℕ

  %⟪ [] ⟫⇉ = 0 , 0
  %⟪ ls ∷ lss ⟫⇉ with %⟪ ls ⟫* | %⟪ lss ⟫⇉
  ... | k′ , n′ | k , n = k′ + k , k′ + n′ + n

  -- %⟪_⟫*

  %⟪_⟫* : {C : Set} (ls : List (LazyGraph C)) → ℕ × ℕ

  %⟪ [] ⟫* = 1 , 0
  %⟪ l ∷ ls ⟫* with %⟪ l ⟫ | %⟪ ls ⟫*
  ... | k′ , n′ | k , n = k′ * k , k′ * n + k * n′
