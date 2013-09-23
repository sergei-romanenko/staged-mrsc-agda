# Is it possible to filter results that have not yet been produced?

## Trial and error

A popular approach to problem solving is _trial and error_:

* Generate alternatives.
* Evaluate alternatives.
* Select the best alternatives.

## Multi-result supercompilation and filtering

When trying to apply supercompilation to problem solving we naturally come to 
the idea of _multi-result_ supercompilation: instead of trying to guess, which 
residual graph of configurations is "the best" one, a multi-result supercompiler 
(`mrsc`) produces a collection of residual graphs.

Suppose we have a multi-result supercompiler `mrsc` and a filter `filter`. 
Combining them, we get a problem-solver

```
#!agda
    solver = filter ∘ mrsc
```

The supercompiler `mrsc` is a general-purpose tool (at least to some extent), 
while the filter incorporates some knowledge about the problem domain. A good 
feature of this design is its modularity and the clear separation of concerns: 
(in ideal case) `mrsc` knows nothing about the problem domain, while `filter` 
knows nothing about supercompilation.

## Fusion of supercompilation and filtering

However, the main problem with multi-result supercompilation is that it can 
produce millions of residual graphs! Hence, it seems to be a good idea to 
suppress the generation of the majority residual graphs "on the fly", in the 
process of supercompilation. This can be achieved if the criteria `filter` is 
based upon are "monotonic": if some parts of a partially constructed residual 
graph are "bad", then the completed residual graph is also certain to be a "bad" 
one.

We can exploit monotonicity by fusing `filter` and `mrsc` into a monolithic 
program
```
#!agda
    solver′ = fuse filter mrsc
```
where `fuse` is an automatic tool (based, for example, on supercompilation), or 
just a postgraduate who has been taught (by his scientific adviser) to perform 
fusion by hand. :-)

An evident drawback of this approach is its non-modularity. Every time `filter` 
is modified, the fusion of `mrsc` and `filter` has to be repeated.

## Staged supercompilation: multiple results seen as a residual program

Here we put forward an alternative approach which:

1. Completely separates supercompilation from filtering.
2. Enables filtering of partially constructed residual graphs.

Thus the technique is modular, and yet reduces the search space and consumed 
computational resources.

We suggest the following "recipe".

### Small-step ==> big-step

Supercompilation can be formulated either in "small-step" or in "big-step" 
style. Small-step supercompilation proceeds by rewriting a graph of 
configuration. Big-step supercompilation is specified/implemented in 
compositional style: the construction of a graph amounts to constructing its 
subgraphs, followed by synthesizing the whole graph from its previously 
constructed parts. Multi-result supercompilation was formulated in small-step 
style. First of all, given a multi-result supercompiler `mrsc`, let us 
re-implement, _to produce a big-step supercompiler_ `naive-mrsc`.

### Identifying Cartesian products

Now, by studying the internal structure of `naive-mrsc`, we can see that, at 
some places, `naive-mrsc` calculates "Cartesian products": if a graph `g` is to 
be constructed from `k` subgraphs `g[1]`, ... , `g[k]`, `naive-mrsc` computes `k` 
sets of graphs `gs[1]`, ... , `gs[k]` and then considers all possible `g[i] ∈ gs[i]` 
for `i = 1,..., k` and constructs corresponding versions of the graph `g`.

### Staging: delaying Cartesian products

At this point we can decompose the process of supercompilation into two stages
```
#!agda
    naive-mrsc ≗ ⟪_⟫ ∘ lazy-mrsc
```
where `⟪_⟫` is a unary function, and `f ≗ g` means that `f x = f y` for all `x`.

At the first stage, `lazy-mrsc` generates a "lazy graph", which, essentially, is 
a "program" to be "executed" by `⟪_⟫`. Unlike `naive-mrsc`, `lazy-mrsc` 
does not calculate Cartesian products immediately: instead, it outputs requests 
for `⟪_⟫` to calculate then at the second stage.

### Fusing filtering with the generation of graphs

Suppose, `l` is a lazy graph produced by `lazy-mrsc`. By evaluating `⟪ l ⟫`,
we could generate the same bag of graphs, as would have been produced by 
the original `naive-mrsc`.

Usually, we are not interested in the whole bag `⟪ l ⟫`.
The goal is to find "the best" or "most interesting" graphs.
Hence, there should be developed some techniques of extracting
useful information from a lazy graph `l` without evaluating
`⟪ l ⟫` directly.

This can be formulated in the following form.
Suppose that a function `filter` filters bags of graphs,
removing "bad" graphs, so that
```
#!agda
    filter ⟪ l ⟫
```
generates the bag of "good" graphs.

Let us find a function `extract` such that
```
#!agda
    extract l = filter ⟪ l ⟫
```
In many cases, `extract` may be more efficient (by several orders
of magnitude) than the composition `filter ∘ ⟪_⟫`.

Sometimes, `extract` can be formulated in terms of "cleaners" of
lazy graphs. Let `clean` be a function that transforms lazy graphs,
such that
```
#!agda
    ⟪ clean l ⟫ ⊆ ⟪ l ⟫
```
Then `extract` can be constructed in the following way:
```
#!agda
    extract l = ⟪ clean l ⟫
```
Theoretically speaking, `clean` is the result of "promoting" `filter`:
```
#!agda
    filter ∘ ⟪_⟫ ≗ ⟪_⟫ ∘ clean
```
The nice property of cleaners is that they are composable:
given `clean₁` and `clean₂`, `clean₂ ∘ clean₁` is also a cleaner.

### Typical cleaners

Typical tasks are finding graphs of minimal size and removing graphs that 
contain "bad" configurations. It is easy to implement corresponding cleaners in 
a such a way that the lazy graph is traversed only once, in a linear time.

### What are the advantages?

To sum up, we get the following scheme:
```
#!agda
    filter ∘ naive-mrsc ≗
      filter  ∘ (⟪_⟫ ∘ lazy-mrsc) =
      (filter  ∘ ⟪_⟫) ∘ lazy-mrsc) ≗
      (⟪_⟫ ∘ clean) ∘ lazy-mrsc)
```
We can see that:

* The construction is modular: `lazy-mrsc` and `⟪_⟫` do not have to know 
anything about filtering, while `clean` does not have to know anything about 
`lazy-mrsc` and `⟪_⟫`.

* Cleaners are composable: we can decompose a sophisticated cleaner into a 
composition of simpler cleaners.

* In many cases (of practical importance) cleaners can be implemented in such a 
way that the best graphs can be extracted from a lazy graph in linear time.

## Codata and corecursion: decomposing `lazy-mrsc`

By using codata and corecursion, we can decompose `lazy-mrsc` into two stages
```
#!agda
    lazy-mrsc ≗ prune-cograph ∘ build-cograph
```
where `build-cograph` constructs a (potentially) infinite tree, while `prune-cograph` traverses this tree and turns it into a lazy graph (which is finite).

The point is that `build-cograph` performs driving and rebuilding configurations, while `prune-cograph` uses whistle to turn an infinite tree to a finite graph. Thus `build-cograph` knows nothing about the whistle, while `prune-cograph` knows nothing about driving and rebuilding. This further improves the modularity of multi-result supercompilation.

## Cleaning before whistling

Now it turnes out that some cleaners can be pushed over `prune-cograph`!

Suppose `clean` is a lazy graph cleaner and `clean∞` a cograph cleaner, such that
```
#!agda
    clean ∘ prune-cograph ≗ prune-cograph ∘ clean∞
```
then 
```
#!agda
    clean ∘ lazy-mrsc ≗
        clean ∘ (prune-cograph ∘ build-cograph) ≗
        (prune-cograph ∘ clean∞) ∘ build-cograph =
        prune-cograph ∘ (clean∞ ∘ build-cograph)
```
The good thing is that `build-cograph` and `clean∞` work in a lazy way,
generating subtrees by demand. Hence, evaluating
```
#!agda
    ⟪ prune-cograph ∘ (clean∞ (build-cograph c))  ⟫
```
-- is likely to be less time and space consuming than directly evaluating
```
#!agda
    ⟪ clean (lazy-mrsc c) ⟫
```

## A model of big-step multi-result supercompilation in Agda

At the moment, there has been developed an abstract model in Agda of big-step 
multi-result supercompilation. A formal proof is given of the fact that
```
#!agda
    ∀ (c : Conf) → naive-mrsc c ≡ ⟪ lazy-mrsc c ⟫
```
By the way of testing, the abstract model is instantiated to produce a 
multi-result supercompiler for counter systems.

*TO DO:* The Agda stuff should be reimplemented in Scala, to produce tables with 
nice results of measurements. An implementation in Scala is desirable, in order 
to obtain experimental results, which could be easy compare with the results 
produced by a small-step supercompiler (implemented in Scala and based on 
spaghetti stacks).
