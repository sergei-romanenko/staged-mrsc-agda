# An example: big-step supercompilation for counter systems

The abstract model of big-step multi-result supercompilation
presented in `BigStepSc.agda` can be instantiated to produce
runnable supercompilers.

In `BigStepCounters` there is implemented a toolkit for
describing counter systems and turning them into working
supercompilers.

## Worlds of counters

A counter system is characterized by two parameters: `k` and `maxℕ`,
and configurations have simple structure. Any configuration
is a list of fixed length `k`. Each component of this list is
either the symbol `ω` or a natural number `n`, such that `n < maxℕ`.

A specification of a counter system is a "world of counters",
which is a record of the type `CntWorld`:
```
record CntWorld {k : ℕ} : Set₁ where
  Conf : Set
  Conf = Vec ℕω k

  field
    start : Conf
    _⇊ : (c : Conf) → List Conf
    unsafe : (c : Conf) → Bool
```
where

* `k` is the number of components in a configuration.
* `Conf` is the type of configurations.
* `start` is the initial configuration.
* `_⇊` specifies how to drive a configuration: `c ⇊` returns
  a list of configurations in which `c` is decomposed. (Driving
  in the case of counter systems is deterministic.)
* `unsafe` determines which configurations are considered to be
  (semantically) "unsafe".

Then there is defined the module `CntSc`
```
module CntSc {k : ℕ} (cntWorld : CntWorld {k})
  (maxℕ : ℕ) (maxDepth : ℕ) where
...
```
which has a number of parameters.

* `k` is the number of components in a configuration,
* `cntWorld` is a world of counters.
* `maxℕ` is the limit on the size of natural numbers in configurations
  (for a component `n` there must hold `n < maxℕ`).
* `maxDepth` is the limit on the length of histories
  (is used by the whistle).

When instantiated, `CntSc` produces

* A world of supercompilation `scWorld`.
* A number of functions for generating graphs,
  lazy graphs and cographs.
* A cleaner `cl-unsafe = cl-bad-conf unsafe`.
* A cograph cleaner `cl∞-unsafe = cl∞-bad-conf unsafe`.

## Making a supercompiler

In the subfolder `Protocol` there are defined a number of
worlds of supercompilation, which are models of communication
protocols.

In order to be specific, let us consider the protocol `Synapse`.

The world of counters in the case of `Synapse` is declared as
```
Synapse : CntWorld
Synapse = ...
```
We can convert `Synapse` into a world of supercompilation:
```
open CntSc Synapse 3 10
```
Now we can generate a lazy graph, clean it and extract a graph
of minimal size:
```
graph : LazyGraph Conf
graph = lazy-mrsc start

graph-cl-unsafe : LazyGraph Conf
graph-cl-unsafe = cl-empty $ cl-unsafe graph

graph-cl-min-size = cl-min-size graph-cl-unsafe
graph-min-size = ⟪ proj₂ graph-cl-min-size ⟫
```
If we want to deal with cographs, this can be done
as follows:
```
cograph : LazyCograph Conf
cograph = build-cograph start

cograph-safe : LazyCograph Conf
cograph-safe = cl∞-Ø $ cl∞-unsafe cograph

cograph-pruned : LazyGraph Conf
cograph-pruned = cl-empty $ prune-cograph cograph-safe
```
We can test that in both cases we get the same result:
```
graph-cl-unsafe≡cograph-pruned :
  graph-cl-unsafe ≡ cograph-pruned

graph-cl-unsafe≡cograph-pruned = refl
```
Note that in Agda unit testing is a special case of
theorem proving: so, we prove the theorem that `graph-cl-unsafe`
and `cograph-pruned` are the same thing.

Empty subtrees can be removed in the process of pruning.
```
cograph-pruned-Ø : LazyGraph Conf
cograph-pruned-Ø = pruneØ-cograph cograph-safe

graph-cl-unsafe≡cograph-pruned-Ø :
  graph-cl-unsafe ≡ cograph-pruned-Ø

graph-cl-unsafe≡cograph-pruned-Ø = refl
```