# Counting without generation

The main idea of staged supercompilation consists in
replacing the analysis of residual graphs with the analysis
of the program that generates the graphs.

Gathering statistics about graphs is just a special case of
such analysis. For example, it is possible to count the number of
residual graphs that would be produced without actually generating
the graphs.

## Counting residual graphs

Technically, we can define a function `#⟪_⟫` that analyses
lazy graphs such that
```
#⟪⟫-correct : ∀ {C : Set} (l : LazyGraph C) →
    #⟪ l ⟫ ≡ length ⟪ l ⟫
```
Here is the definition of `#⟪_⟫` (see `Statistics.agda`).
```
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
```
The proof of `#⟪⟫-correct` is based on the following lemma:
```
length∘cartesian2 : ∀ {A : Set} →
  (xs : List A) → (yss : List (List A)) →
  length (cartesian2 xs yss) ≡ length xs * length yss
```

# Counting nodes in collections of residual graphs

We can define a function `%⟪_⟫`, such that
```
%⟪⟫-correct : {C : Set} (l : LazyGraph C) →
    %⟪ l ⟫ ≡ #⟪ l ⟫ , sum (map graph-size ⟪ l ⟫)

```
`%⟪⟫` computes the number of graphs represented by `l` and
the total number of nodes in the graphs represented by `l`.
It does so to avoid calling `#⟪_⟫` (which would lead to
the same values being calculated several times).

Here is the definition of `%⟪_⟫` (see `Statistics.agda`).
```
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
```
The proof of `%⟪⟫-correct` is rather tedious...
