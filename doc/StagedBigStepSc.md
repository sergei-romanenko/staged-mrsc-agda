# Staging big-step multi-result supercompilation

We can decompose the process of supercompilation into two stages
```
#!agda
    naive-mrsc ≗ ⟪_⟫ ∘ lazy-mrsc
```
where `⟪_⟫` is a unary function, and `f ≗ g` means that `f x = g y` for all `x`.

At the first stage, `lazy-mrsc` generates a "lazy graph", which, essentially, is 
a "program" to be "executed" by `⟪_⟫`.

## Lazy graphs of configuration

A `LazyGraph C` represents a finite set of graphs
of configurations (whose type is `Graph C`).
  
```
#!agda
data LazyGraph (C : Set) : Set where
  Ø     : LazyGraph C
  stop  : (c : C) → LazyGraph C
  build : (c : C) (lss : List (List (LazyGraph C))) → LazyGraph C
```
A lazy graph is a tree whose nodes are "commands" to be executed
by the interpreter `⟪_⟫`.

The exact semantics of lazy graphs is given by the function `⟪_⟫`, which
calls auxiliary functions `⟪_⟫*` and `⟪_⟫`
(see `Graphs.agda`).

```
#!agda
⟪_⟫ : {C : Set} (l : LazyGraph C) → List (Graph C)
⟪_⟫* : {C : Set} (ls : List (LazyGraph C)) → List (List (Graph C))
⟪_⟫⇉ : {C : Set} (lss : List (List (LazyGraph C))) → List (List (Graph C))
```
Here is the definition of the main function `⟪_⟫`:
```
#!agda
⟪ Ø ⟫ = []
⟪ stop c ⟫ = [ back c ]
⟪ build c lss ⟫ = map (forth c) ⟪ lss ⟫⇉
```
It can be seen that `Ø` means "generate no graphs", `stop` means
"generate a back-node and stop".

The most interesting case is a build-node `build c lss`, where `c` is
a configuration and  `lss` a list of lists of lazy graphs.
Recall that, in general, a configuration can be decomposed
into a list of configurations in several different ways.
Thus, each `ls ∈ lss` corresponds to a decomposition of `c` into
a number of configurations `c[1], ... c[k]`. By supercompiling
each `c[i]` we get a collection of graphs that can be represnted
by a lazy graph `ls[i].

The function `⟪_⟫*` considers each lazy graph in a list of lazy graphs `ls`,
and turns it into a list of graphs:
```
#!agda
⟪ [] ⟫* = []
⟪ l ∷ ls ⟫* = ⟪ l ⟫ ∷ ⟪ ls ⟫*
```
The function `⟪_⟫⇉` considers all possible decompositions of
a configuration, and for each decomposition computes all possible
combinations of subgraphs:

```
#!agda
⟪ [] ⟫⇉ = []
⟪ ls ∷ lss ⟫⇉ = cartesian ⟪ ls ⟫* ++ ⟪ lss ⟫⇉

```
There arises a natural question: why `⟪_⟫*` is defined by explicit
recursion, while it does exactly the same job as would do `map ⟪_⟫`?
The answer is that Agda's termination checker does not accept `map ⟪_⟫`,
because it cannot see that the argument in the recursive calls to `⟪_⟫`
becomes structurally smaller. For the same reason `⟪_⟫⇉` is also
defined by explicit recursion.

## A functional specification of lazy multi-result supercompilation
Given a configuration `c`, the function `lazy-mrsc` produces a lazy graph.
```
#!agda
lazy-mrsc : (c : Conf) → LazyGraph Conf
```
`lazy-mrsc` is defined in terms of a more general function `lazy-mrsc′`
```
#!agda
lazy-mrsc′ : ∀ (h : History) (b : Bar ↯ h) (c : Conf) → LazyGraph Conf
lazy-mrsc c = lazy-mrsc′ [] bar[] c
```
The general structure of `lazy-mrsc′` is [very similar](BigStepSc)
to that of `naive-mrsc′`, but, unlike `naive-mrsc`, it does not build Cartesian products immediately.

```
#!agda
lazy-mrsc′ h b c with foldable? h c
... | yes f = stop c
... | no ¬f with ↯? h
... | yes w = Ø
... | no ¬w with b
... | now bz with ¬w bz
... | ()
lazy-mrsc′ h b c | no ¬f | no ¬w | later bs =
  build c (map (map (lazy-mrsc′ (c ∷ h) (bs c))) (c ⇉))
```
Let us compare the most interesting parts of `naive-mrsc` and `lazy-mrsc`:
```
#!agda
map (forth c)
    (concat (map (cartesian ∘ map (naive-mrsc′ (c ∷ h) (bs c))) (c ⇉)))
...
build c (map (map (lazy-mrsc′ (c ∷ h) (bs c))) (c ⇉))
```
Note that `cartesian` disappears from `lazy-mrsc`.

## Correctness of `lazy-mrsc` and `⟪_⟫`

`lazy-mrsc` and `⟪_⟫` are correct with respect to `naive-mrsc`.
In Agda this is formulated as follows:
```
#!agda
naive≡lazy : (c : Conf) → naive-mrsc c ≡ ⟪ lazy-mrsc c ⟫
```
In other words, for any initial configuraion `c`,
`⟪ lazy-mrsc c ⟫` returns the same list of graphs
(the same configurations in the same order!) as
would return `naive-mrsc c`.

A formal proof of `naive≡lazy` can be found in  `BigStepScTheorems.agda`.
