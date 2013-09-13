module Statistics where

open import Data.Nat
open import Data.List as List
  using (List; []; _∷_; [_]; length; _++_; map; filter;
         foldr; foldl; sum; product)
open import Data.List.Properties
  using (length-map; length-++)
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃; ∃₂)

open import Function

open import Relation.Binary.PropositionalEquality as P
  hiding (sym)
  renaming ([_] to P[_])


open import Util
open import Graphs

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

  length⟪⟫ : ∀ {C : Set} (l : LazyGraph C) → ℕ

  length⟪⟫ Ø = 0
  length⟪⟫ (stop c) = 1
  length⟪⟫ (build c lss) = length⟪⟫⇉ lss

  length⟪⟫⇉ : ∀ {C : Set} (lss : List (List (LazyGraph C))) → ℕ
  length⟪⟫⇉ [] = 0
  length⟪⟫⇉ (ls ∷ lss) = (length⟪⟫* ls) + length⟪⟫⇉ lss

  length⟪⟫* : ∀ {C : Set} (ls : List (LazyGraph C)) → ℕ
  length⟪⟫* [] = 1
  length⟪⟫* (l ∷ ls) = length⟪⟫ l * length⟪⟫* ls

mutual

  length⟪⟫-correct : ∀ {C : Set} (l : LazyGraph C) →
   length⟪⟫ l ≡ length ⟪ l ⟫

  length⟪⟫-correct Ø = refl
  length⟪⟫-correct (stop c) = refl
  length⟪⟫-correct (build c lss) = begin
    length⟪⟫ (build c lss)
      ≡⟨⟩
    length⟪⟫⇉ lss
      ≡⟨ length⟪⟫⇉-correct lss ⟩
    length ⟪ lss ⟫⇉
      ≡⟨ P.sym $ length-map (forth c) ⟪ lss ⟫⇉ ⟩
    length (map (forth c) ⟪ lss ⟫⇉)
      ≡⟨⟩
    length ⟪ build c lss ⟫
    ∎
    where open ≡-Reasoning

  length⟪⟫⇉-correct : ∀ {C : Set} (lss : List (List (LazyGraph C))) →
    length⟪⟫⇉ lss ≡ length ⟪ lss ⟫⇉

  length⟪⟫⇉-correct [] = refl
  length⟪⟫⇉-correct (ls ∷ lss) = begin
    length⟪⟫⇉ (ls ∷ lss)
      ≡⟨⟩
    length⟪⟫* ls + length⟪⟫⇉ lss
      ≡⟨ cong₂ _+_ (length⟪⟫*-correct ls) (length⟪⟫⇉-correct lss) ⟩
    length (cartesian ⟪ ls ⟫*) + length ⟪ lss ⟫⇉
      ≡⟨ P.sym $ length-++ (cartesian ⟪ ls ⟫*) ⟩
    length (cartesian ⟪ ls ⟫* ++ ⟪ lss ⟫⇉)
      ≡⟨⟩
    length ⟪ ls ∷ lss ⟫⇉
    ∎
    where open ≡-Reasoning

  length⟪⟫*-correct :  ∀ {C : Set} (ls : List (LazyGraph C)) →
    length⟪⟫* ls ≡ length (cartesian ⟪ ls ⟫*)

  length⟪⟫*-correct [] = refl
  length⟪⟫*-correct (l ∷ ls) = begin
    length⟪⟫* (l ∷ ls)
      ≡⟨⟩
    length⟪⟫ l * length⟪⟫* ls
      ≡⟨ cong₂ _*_ (length⟪⟫-correct l) (length⟪⟫*-correct ls) ⟩
    length ⟪ l ⟫ * length (cartesian ⟪ ls ⟫*)
      ≡⟨ P.sym $ length∘cartesian2 ⟪ l ⟫ (cartesian ⟪ ls ⟫*) ⟩
    length (cartesian2 ⟪ l ⟫ (cartesian ⟪ ls ⟫*))
      ≡⟨⟩
    length (cartesian ⟪ l ∷ ls ⟫*)
    ∎
    where open ≡-Reasoning
