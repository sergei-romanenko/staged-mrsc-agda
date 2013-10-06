# Cleaning lazy graphs

A function `clean` is said to be a "cleaner" if for any lazy
graphs `l`
```
    ⟪ clean l ⟫ ⊆ ⟪ l ⟫
```
Suppose that a function `filter` filters bags of graphs,
removing "bad" graphs, so that
```
    filter ⟪ l ⟫
```
generates the bag of "good" graphs. Let `clean` be a cleaner such that
```
    filter ∘ ⟪_⟫ ≗ ⟪_⟫ ∘ clean
```
Then we can replace filtering of graphs with cleaning of
lazy graphs
```
    filter ∘ naive-mrsc ≗ ⟪_⟫ ∘ clean ∘ lazy-mrsc
```
In `Graphs.agda` there are defined a number of filters and
corresponding cleaniers.

## Filter `fl-bad-conf` and cleaner `cl-bad-conf`

```
fl-bad-conf : {C : Set} (bad : C → Bool) (gs : List (Graph C)) →
  List (Graph C)

cl-bad-conf : {C : Set} (bad : C → Bool) (l : LazyGraph C) →
  LazyGraph C
```
Configurations represent states of a computation process.
Some of these states may be "bad" with respect to the problem
that is to be solved by means of supercompilation.

Given a predicate `bad` that returns `true` for "bad" configurations,
`fl-bad-conf bad gs` removes from `gs` the graphs that contain
at least one "bad" configuration.

The cleaner `cl-bad-conf` corresponds to the filter `fl-bad-conf`.
`cl-bad-conf` exploits the fact that "badness" to be monotonic,
in the sense that a single "bad" configuration spoils the whole
graph.

`cl-bad-conf` is correct with respect to `fl-bad-conf`:
```
cl-bad-conf-correct : {C : Set} (bad : C → Bool) →
  ⟪_⟫ ∘ cl-bad-conf bad ≗ fl-bad-conf bad ∘ ⟪_⟫
```
A formal proof of this theorem is given in `GraphsTheorems.agda`.

It is instructive to take a look at the implementation of
`cl-bad-conf` in `Graphs.agda`, to get the general idea of
how cleaners are really implemented:
```
cl-bad-conf : {C : Set} (bad : C → Bool) (l : LazyGraph C) →
  LazyGraph C

cl-bad-conf⇉ : {C : Set} (bad : C → Bool)
  (lss : List (List (LazyGraph C))) → List (List (LazyGraph C))

cl-bad-conf* : {C : Set} (bad : C → Bool)
  (ls : List (LazyGraph C)) → List (LazyGraph C)

-- cl-bad-conf

cl-bad-conf bad Ø = Ø
cl-bad-conf bad (stop c) =
  if bad c then Ø else (stop c)
cl-bad-conf bad (build c lss) =
  if bad c then Ø else (build c (cl-bad-conf⇉ bad lss))

-- cl-bad-conf⇉

cl-bad-conf⇉ bad [] = []
cl-bad-conf⇉ bad (ls ∷ lss) =
  cl-bad-conf* bad ls ∷ (cl-bad-conf⇉ bad lss)

-- cl-bad-conf*

cl-bad-conf* bad [] = []
cl-bad-conf* bad (l ∷ ls) =
  cl-bad-conf bad l ∷ cl-bad-conf* bad ls

```

## Cleaner `cl-empty`

`cl-empty` is a cleaner that removes subtrees of a lazy graph that
represent empty sets of graphs.
```
cl-empty : {C : Set} (l : LazyGraph C) → LazyGraph C
```

`cl-bad-conf` is correct with respect to `⟪_⟫`:
```
cl-empty-correct : ∀ {C : Set} (l : LazyGraph C) →
  ⟪ cl-empty l ⟫ ≡ ⟪ l ⟫
```
A formal proof of this theorem is given in `GraphsTheorems.agda`.

## Cleaner `cl-min-size`
The function `cl-min-size`
```
  cl-min-size : ∀ {C : Set} (l : LazyGraph C) → ℕ × LazyGraph C
```
takes as input a lazy graph`l` and returns either `0 , Ø`,
if `l` contains no graphs, or a pair `(k , l′)`,
where `l′` is a lazy graph, representing a single graph `g′`
of minimal size `k`.

More formally,

* `⟪ l′ ⟫ = [ g′ ]`.
* `graph-size g′ = k`
* `k ≤ graph-size g` for all `g ∈ ⟪ l ⟫`.

The main idea behind `cl-min-size` is that, if we have a node
`build c lss`, then we can clean each `ls ∈ lss`.

Let us consider an `ls ∈ lss`. We can clean with `cl-min-size` each
`l ∈ ls` to obtain `ls′` a new list of lazy graphs .
If `Ø ∈ ls′`, we replace the node `build c lss` with `Ø`.
The reason is that computing the Cartesian product
for `ls′` would produce an empty set of results. Otherwise,
we replace `build c lss` with `build c lss′`.

A good thing about `cl-min-size` is it cleans any lazy graph `l`
in linear time with respect to the size of `l`.

TODO: A formal proof of correctness of `cl-min-size`.