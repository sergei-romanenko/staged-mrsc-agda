module StatisticsTheorems where

open import Data.Nat
open import Data.List as List
  using (List; []; _∷_; [_]; length; _++_; concat; map; filter;
         foldr; foldl; sum; product)
open import Data.List.Properties
  using (length-map; length-++
        ; map-compose; map-cong; map-++-commute; sum-++-commute)
open import Data.List.Any as Any
  using (Any; here; there; module Membership-≡)
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
open import Statistics

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

--
-- Proof of correctness of `#⟪⟫`
--

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
-- Proof of correctness of `%⟪_⟫`
--

-- The main problem with `%⟪_⟫` is that it returns a pair,
-- such that
--     proj₁ %⟪ l ⟫ ≡ #⟪ l ⟫
--
-- Dealing with pairs complicates the proofs (from the technical
-- point of view).
--
-- Thus we define a function `%′⟪_⟫` such that
--     proj₂ %⟪ l ⟫ ≡ %′⟪ l ⟫
-- Computationally, `%′⟪_⟫` is inefficient, but is easier
-- to deal with in proofs.
--
-- Then we prove that
--     %′⟪ l ⟫ ≡ sum (map graph-size ⟪ l ⟫)
-- By transitivity, this implies that
--     proj₂ %⟪ l ⟫ ≡ sum (map graph-size ⟪ l ⟫)
--

--
-- A few "technical" lemmas.
-- (Some names, like `lemma₂`, are really stupid...)
--

-- lemma₂

lemma₂ : {A : Set} (f : A → ℕ) (x : A) (yss : List (List A)) →
  sum (map (sum ∘ map f) (map (_∷_ x) yss)) ≡
    length yss * f x + sum (map (sum ∘ map f) yss)

lemma₂ f x [] = refl
lemma₂ f x (ys ∷ yss) = begin
  (f x + sum (map f ys)) + sum (map (sum ∘ map f) (map (_∷_ x) yss))
    ≡⟨ cong (_+_ (f x + sum (map f ys))) (lemma₂ f x yss) ⟩
  (f x + sum (map f ys)) + (length yss * f x + sum (map (sum ∘ map f) yss))
    ≡⟨ solve 4 (λ a b c d → a :+ b :+ (c :+ d) :=
                              (a :+ c) :+ (b :+ d)) refl
             (f x) (sum (map f ys)) (length yss * f x)
             (sum (map (sum ∘ map f) yss)) ⟩
  (f x + length yss * f x) + (sum (map f ys) + sum (map (sum ∘ map f) yss))
  ∎
  where open ≡-Reasoning

-- lemma

lemma : {A : Set} (f : A → ℕ) (xs : List A) (yss : List (List A)) →
  sum (map (sum ∘ map f) (cartesian2 xs yss)) ≡
    length xs * sum (map (sum ∘ map f) yss) + sum (map f xs) * length yss 

lemma f [] yss = refl
lemma f (x ∷ xs) yss = begin
  sum (map (sum ∘ map f) (map (_∷_ x) yss ++ cartesian2 xs yss))
    ≡⟨ cong sum (map-++-commute
                  (sum ∘ map f) (map (_∷_ x) yss) (cartesian2 xs yss)) ⟩
  sum (map (sum ∘ map f) (map (_∷_ x) yss) ++
    map (sum ∘ map f) (cartesian2 xs yss))
    ≡⟨ sum-++-commute (map (sum ∘ map f) (map (_∷_ x) yss))
         (map (sum ∘ map f) (cartesian2 xs yss)) ⟩
  sum (map (sum ∘ map f) (map (_∷_ x) yss)) +
    sum (map (sum ∘ map f) (cartesian2 xs yss))
    ≡⟨ cong (_+_ (sum (map (sum ∘ map f) (map (_∷_ x) yss))))
            (lemma f xs yss) ⟩
  sum (map (sum ∘ map f) (map (_∷_ x) yss)) +
    (length xs * sum (map (sum ∘ map f) yss) + sum (map f xs) * length yss)
    ≡⟨ cong (flip _+_ (length xs * sum (map (sum ∘ map f) yss) +
                         sum (map f xs) * length yss))
            (lemma₂ f x yss) ⟩
  length yss * f x + sum (map (sum ∘ map f) yss) +
    (length xs * sum (map (sum ∘ map f) yss) + sum (map f xs) * length yss)
    ≡⟨ solve 5 (λ a b c d e → a :* b :+ c :+ (d :+ e :* a) :=
                                (c :+ d) :+ (b :+ e) :* a) refl
             (length yss) (f x) (sum (map (sum ∘ map f) yss))
             (length xs * sum (map (sum ∘ map f) yss)) (sum (map f xs)) ⟩
  (sum (map (sum ∘ map f) yss) + length xs * sum (map (sum ∘ map f) yss)) +
      (f x + sum (map f xs)) * length yss
  ∎
  where open ≡-Reasoning

-- graph-size*-is-sum

graph-size*-is-sum : {C : Set} (gs : List (Graph C)) →
  graph-size* gs ≡ sum (map graph-size gs)

graph-size*-is-sum [] = refl
graph-size*-is-sum (g ∷ gs) =
  cong (_+_ (graph-size g)) (graph-size*-is-sum gs)

--
-- Now we define `%′⟪ l ⟫` and prove that
--
-- * proj₁ %⟪ l ⟫ ≡ #⟪ l ⟫
-- * proj₂ %⟪ l ⟫ ≡ %′⟪ l ⟫
--
-- Hence, we could use `%′⟪_⟫` in proofs instead of `%⟪_⟫`.
-- `%′⟪_⟫` is inefficient, as it makes a lot of calls to `#⟪_⟫`.
-- However, as far as proofs are concerned, this is not of importance...
--

mutual

  -- %′⟪_⟫

  %′⟪_⟫ : {C : Set} (l : LazyGraph C) → ℕ

  %′⟪ Ø ⟫ = 0
  %′⟪ stop c ⟫ = 1
  %′⟪ build c lss ⟫ = %′⟪ lss ⟫⇉

  -- %′⟪_⟫⇉

  %′⟪_⟫⇉ : {C : Set} (lss : List (List (LazyGraph C))) → ℕ

  %′⟪ [] ⟫⇉ = 0
  %′⟪ ls ∷ lss ⟫⇉ = #⟪ ls ⟫* + %′⟪ ls ⟫* + %′⟪ lss ⟫⇉

  -- %′⟪_⟫*

  %′⟪_⟫* : {C : Set} (ls : List (LazyGraph C)) → ℕ

  %′⟪ [] ⟫* = 0
  %′⟪ l ∷ ls ⟫* = #⟪ l ⟫ * %′⟪ ls ⟫* + #⟪ ls ⟫* * %′⟪ l ⟫

mutual

  -- %⟪⟫-correct₁

  %⟪⟫-correct₁ : {C : Set} (l : LazyGraph C) →
    proj₁ %⟪ l ⟫ ≡ #⟪ l ⟫

  %⟪⟫-correct₁ Ø = refl
  %⟪⟫-correct₁ (stop c) = refl
  %⟪⟫-correct₁ (build c lss) = %⟪⟫⇉-correct₁ lss

  %⟪⟫⇉-correct₁ : {C : Set} (lss : List (List (LazyGraph C))) →
    proj₁ %⟪ lss ⟫⇉ ≡ #⟪ lss ⟫⇉

  %⟪⟫⇉-correct₁ [] = refl
  %⟪⟫⇉-correct₁ (ls ∷ lss) =
    cong₂ _+_ (%⟪⟫*-correct₁ ls) (%⟪⟫⇉-correct₁ lss)

  %⟪⟫*-correct₁ : {C : Set} (ls : List (LazyGraph C)) →
    proj₁ %⟪ ls ⟫* ≡ #⟪ ls ⟫*

  %⟪⟫*-correct₁ [] = refl
  %⟪⟫*-correct₁ (l ∷ ls) =
    cong₂ _*_ (%⟪⟫-correct₁ l) (%⟪⟫*-correct₁ ls)

mutual

  -- %⟪⟫-correct₂

  %⟪⟫-correct₂ : {C : Set} (l : LazyGraph C) →
    proj₂ %⟪ l ⟫ ≡ %′⟪ l ⟫

  %⟪⟫-correct₂ Ø = refl
  %⟪⟫-correct₂ (stop c) = refl
  %⟪⟫-correct₂ (build c lss) = %⟪⟫⇉-correct₂ lss

  %⟪⟫⇉-correct₂ : {C : Set} (lss : List (List (LazyGraph C))) →
    proj₂ %⟪ lss ⟫⇉ ≡ %′⟪ lss ⟫⇉

  %⟪⟫⇉-correct₂ [] = refl
  %⟪⟫⇉-correct₂ (ls ∷ lss)
    rewrite %⟪⟫*-correct₁ ls | %⟪⟫*-correct₂ ls | %⟪⟫⇉-correct₂ lss
    = refl

  %⟪⟫*-correct₂ : {C : Set} (ls : List (LazyGraph C)) →
    proj₂ %⟪ ls ⟫* ≡ %′⟪ ls ⟫*

  %⟪⟫*-correct₂ [] = refl
  %⟪⟫*-correct₂ (l ∷ ls)
    rewrite %⟪⟫-correct₁ l | %⟪⟫*-correct₂ ls | %⟪⟫*-correct₁ ls
          | %⟪⟫-correct₂ l
    = refl

--
-- A few "technical" lemmas.
-- (Some names, like `lemma₃`, are really stupid...)
--

-- map-suc

map-suc : {A : Set} (f : A → ℕ) (xs : List A) →
  sum (map (suc ∘ f) xs) ≡ length xs + sum (map f xs)

map-suc f [] = refl
map-suc f (x ∷ xs) = cong suc helper
  where
  open ≡-Reasoning
  helper = begin
    f x + sum (map (suc ∘ f) xs)
      ≡⟨ cong (_+_ (f x)) (map-suc f xs) ⟩
    f x + (length xs + sum (map f xs))
      ≡⟨ solve 3 (λ a b c → a :+ (b :+ c) := b :+ (a :+ c))
               refl (f x) (length xs) (sum (map f xs)) ⟩
    length xs + (f x + sum (map f xs))
    ∎

lemma₃ : ∀ {C : Set} (c : C) (lss : List (List (LazyGraph C))) →
  #⟪ lss ⟫⇉ + sum (map (sum ∘ map graph-size) ⟪ lss ⟫⇉) ≡
  sum (map (graph-size ∘ forth c) ⟪ lss ⟫⇉)

lemma₃ c [] = refl
lemma₃ c (ls ∷ lss) = begin
  #⟪ ls ⟫* + #⟪ lss ⟫⇉ +
    sum (map sz (cartesian ⟪ ls ⟫* ++ ⟪ lss ⟫⇉))
    ≡⟨ cong (_+_ (#⟪ ls ⟫* + #⟪ lss ⟫⇉) ∘ sum)
            (map-++-commute sz
                            (cartesian ⟪ ls ⟫*) ⟪ lss ⟫⇉) ⟩
  #⟪ ls ⟫* + #⟪ lss ⟫⇉ +
    sum (map sz (cartesian ⟪ ls ⟫*) ++ map sz ⟪ lss ⟫⇉)
    ≡⟨ cong (_+_ (#⟪ ls ⟫* + #⟪ lss ⟫⇉))
            (sum-++-commute (map sz (cartesian ⟪ ls ⟫*))
                            (map sz ⟪ lss ⟫⇉)) ⟩
  #⟪ ls ⟫* + #⟪ lss ⟫⇉ +
    (sum (map sz (cartesian ⟪ ls ⟫*)) + sum (map sz ⟪ lss ⟫⇉))
    ≡⟨ solve 4 (λ a b c d → a :+ b :+ (c :+ d) :=
                  a :+ c :+ (b :+ d)) refl
             #⟪ ls ⟫* #⟪ lss ⟫⇉
             (sum (map sz (cartesian ⟪ ls ⟫*))) (sum (map sz ⟪ lss ⟫⇉)) ⟩
  #⟪ ls ⟫* + sum (map sz (cartesian ⟪ ls ⟫*)) +
    (#⟪ lss ⟫⇉ + sum (map sz ⟪ lss ⟫⇉))
    ≡⟨ cong₂ _+_ (cong₂ _+_ (#⟪⟫*-correct ls) refl)
                 (cong₂ _+_ (#⟪⟫⇉-correct lss) refl) ⟩
  length (cartesian ⟪ ls ⟫*) + sum (map sz (cartesian ⟪ ls ⟫*)) +
    (length ⟪ lss ⟫⇉ + sum (map sz ⟪ lss ⟫⇉))
    ≡⟨ P.sym $ cong₂ _+_
               (map-suc sz (cartesian ⟪ ls ⟫*))
               (map-suc sz ⟪ lss ⟫⇉) ⟩
  sum (map (suc ∘ sz) (cartesian ⟪ ls ⟫*)) +
    sum (map (suc ∘ sz) ⟪ lss ⟫⇉)
    ≡⟨ P.sym $ sum-++-commute
                 (map (suc ∘ sz) (cartesian ⟪ ls ⟫*))
                 (map (suc ∘ sz) ⟪ lss ⟫⇉) ⟩
  sum (map (suc ∘ sz) (cartesian ⟪ ls ⟫*) ++
    map (suc ∘ sz) ⟪ lss ⟫⇉)
    ≡⟨ cong sum (P.sym $ map-++-commute
                           (suc ∘ sz) (cartesian ⟪ ls ⟫*) ⟪ lss ⟫⇉) ⟩
  sum (map (suc ∘ sz) (cartesian ⟪ ls ⟫* ++ ⟪ lss ⟫⇉))
    ≡⟨ cong sum (map-cong (λ gs → cong suc (P.sym $ graph-size*-is-sum gs))
                          (cartesian ⟪ ls ⟫* ++ ⟪ lss ⟫⇉)) ⟩
  sum (map (suc ∘ graph-size*) (cartesian ⟪ ls ⟫* ++ ⟪ lss ⟫⇉))
  ∎
  where
  open ≡-Reasoning
  sz : {C : Set} (gs : List (Graph C)) → ℕ
  sz = sum ∘ map graph-size

--
-- `%′⟪ l ⟫` returns the number of nodes in the graphs in `⟪ l ⟫` .
--

mutual

  %′⟪⟫-correct : {C : Set} (l : LazyGraph C) →
    %′⟪ l ⟫ ≡ sum (map graph-size ⟪ l ⟫)

  %′⟪⟫-correct Ø = refl
  %′⟪⟫-correct (stop c) = refl
  %′⟪⟫-correct (build c lss) = begin
    %′⟪ lss ⟫⇉
      ≡⟨ %′⟪⟫⇉-correct lss ⟩
    #⟪ lss ⟫⇉ + sum (map (sum ∘ map graph-size) ⟪ lss ⟫⇉)
      ≡⟨ lemma₃ c lss ⟩
    sum (map (graph-size ∘ forth c) ⟪ lss ⟫⇉)
      ≡⟨ cong sum (map-compose ⟪ lss ⟫⇉) ⟩
    sum (map graph-size (map (forth c) ⟪ lss ⟫⇉))
    ∎
    where open ≡-Reasoning

  %′⟪⟫⇉-correct : {C : Set} (lss : List (List (LazyGraph C))) →
    %′⟪ lss ⟫⇉ ≡ #⟪ lss ⟫⇉ + sum (map (sum ∘ map graph-size) ⟪ lss ⟫⇉)

  %′⟪⟫⇉-correct [] = refl
  %′⟪⟫⇉-correct (ls ∷ lss) rewrite %′⟪⟫⇉-correct lss = begin
    #⟪ ls ⟫* + %′⟪ ls ⟫* +
      (#⟪ lss ⟫⇉ + sum (map (sum ∘ map graph-size) ⟪ lss ⟫⇉))
      ≡⟨ solve 4 (λ a b c d →
               (a :+ b) :+ (c :+ d) := (a :+ c) :+ (b :+ d)) refl
               #⟪ ls ⟫* %′⟪ ls ⟫* #⟪ lss ⟫⇉
               (sum (map (sum ∘ map graph-size) ⟪ lss ⟫⇉)) ⟩
    (#⟪ ls ⟫* + #⟪ lss ⟫⇉) +
      (%′⟪ ls ⟫* + sum (map (sum ∘ map graph-size) ⟪ lss ⟫⇉))
      ≡⟨ cong (_+_ (#⟪ ls ⟫* + #⟪ lss ⟫⇉)) helper ⟩
    #⟪ ls ⟫* + #⟪ lss ⟫⇉ +
      sum (map (sum ∘ map graph-size) (cartesian ⟪ ls ⟫* ++ ⟪ lss ⟫⇉))
    ∎
    where
    open ≡-Reasoning
    helper = begin
      %′⟪ ls ⟫* + sum (map (sum ∘ map graph-size) ⟪ lss ⟫⇉)
        ≡⟨ cong₂ _+_ (%′⟪⟫*-correct ls) refl ⟩
      sum (map (sum ∘ map graph-size) (cartesian ⟪ ls ⟫*)) +
        sum (map (sum ∘ map graph-size) ⟪ lss ⟫⇉)
        ≡⟨ P.sym $ sum-++-commute
             (map (sum ∘ map graph-size) (cartesian ⟪ ls ⟫*))
             (map (sum ∘ map graph-size) ⟪ lss ⟫⇉) ⟩
      sum (map (sum ∘ map graph-size) (cartesian ⟪ ls ⟫*) ++
        map (sum ∘ map graph-size) ⟪ lss ⟫⇉)
        ≡⟨ cong sum (P.sym $ map-++-commute
             (sum ∘ map graph-size) (cartesian ⟪ ls ⟫*) ⟪ lss ⟫⇉) ⟩
      sum (map (sum ∘ map graph-size) (cartesian ⟪ ls ⟫* ++ ⟪ lss ⟫⇉))
      ∎

  %′⟪⟫*-correct : {C : Set} (ls : List (LazyGraph C)) →
    %′⟪ ls ⟫* ≡ sum (map (sum ∘ map graph-size) (cartesian ⟪ ls ⟫*))

  %′⟪⟫*-correct [] = refl
  %′⟪⟫*-correct (l ∷ ls) = begin
    #⟪ l ⟫ * %′⟪ ls ⟫* + #⟪ ls ⟫* * %′⟪ l ⟫
      ≡⟨ solve 3 (λ a b c → a :+ b :* c := a :+ c :* b)
               refl (#⟪ l ⟫ * %′⟪ ls ⟫*) #⟪ ls ⟫* %′⟪ l ⟫ ⟩
     #⟪ l ⟫ * %′⟪ ls ⟫* + %′⟪ l ⟫ * #⟪ ls ⟫*    
      ≡⟨ cong₂ _+_
               (cong₂ _*_ (#⟪⟫-correct l) (%′⟪⟫*-correct ls))
               (cong₂ _*_ (%′⟪⟫-correct l) (#⟪⟫*-correct ls)) ⟩
    length ⟪ l ⟫ * sum (map (sum ∘ map graph-size) (cartesian ⟪ ls ⟫*)) +
      sum (map graph-size ⟪ l ⟫) * length (cartesian ⟪ ls ⟫*)
      ≡⟨ P.sym $ lemma graph-size ⟪ l ⟫ (cartesian ⟪ ls ⟫*) ⟩
    sum (map (sum ∘ map graph-size) (cartesian2 ⟪ l ⟫ (cartesian ⟪ ls ⟫*)))
    ∎
    where open ≡-Reasoning

--
-- Finally, by putting all pieces together,
-- we get the proof of correctness for `%⟪_⟫`.
--

mutual

  -- %⟪⟫-correct

  %⟪⟫-correct : {C : Set} (l : LazyGraph C) →
    %⟪ l ⟫ ≡ #⟪ l ⟫ , sum (map graph-size ⟪ l ⟫)

  %⟪⟫-correct l = begin
    %⟪ l ⟫
      ≡⟨⟩
    (proj₁ %⟪ l ⟫ , proj₂ %⟪ l ⟫)
      ≡⟨ cong₂ _,_ (%⟪⟫-correct₁ l) (%⟪⟫-correct₂ l) ⟩
    (#⟪ l ⟫ , %′⟪ l ⟫)
      ≡⟨ cong (_,_ #⟪ l ⟫) (%′⟪⟫-correct l) ⟩
    (#⟪ l ⟫ , sum (map graph-size ⟪ l ⟫))
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

  naive-mrsc-cm′′ : ∀ (h : History) (b : Bar ↯ h) (c : Conf) (¬w : ¬ ↯ h) →
                  List (Graph Conf)

  naive-mrsc-cm′ h b c with foldable? h c
  ... | yes f = [ back c ]
  ... | no ¬f with ↯? h
  ... | yes w = []
  ... | no ¬w =
    naive-mrsc-cm′′ h b c ¬w

  naive-mrsc-cm′′ h (now w) c ¬w =
    ⊥-elim (¬w w)
  naive-mrsc-cm′′ h (later bs) c ¬w =
    map (forth c)
        (concat (map (cartesianMap (naive-mrsc-cm′ (c ∷ h) (bs c))) (c ⇉)))

  -- naive-mrsc

  naive-mrsc-cm : (c : Conf) → List (Graph Conf)
  naive-mrsc-cm c = naive-mrsc-cm′ [] bar[] c


  -- naive-mrsc-cm′-correct

  naive-mrsc-cm′-correct : ∀ (h : History) (b : Bar ↯ h) (c : Conf) →
    naive-mrsc-cm′ h b c ≡ naive-mrsc′ h b c

  naive-mrsc-cm′-correct′ :
    ∀ (h : History) (b : Bar ↯ h) (c : Conf) (¬w : ¬ ↯ h) →
      naive-mrsc-cm′′ h b c ¬w ≡ naive-mrsc′′ h b c ¬w

  naive-mrsc-cm′-correct h b c with foldable? h c
  ... | yes f = refl
  ... | no ¬f with ↯? h
  ... | yes w = refl
  ... | no ¬w =
    naive-mrsc-cm′-correct′ h b c ¬w

  naive-mrsc-cm′-correct′ h (now w) c ¬w =
    ⊥-elim (¬w w)
  naive-mrsc-cm′-correct′ h (later bs) c ¬w =
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
