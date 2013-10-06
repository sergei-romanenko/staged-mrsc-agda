#A model of big-step multi-result supercompilation

We have formulated an idealized model of big-step multi-result supercompilation. This model is rather abstract, and yet it can be instantiated to produce runnable supercompilers.

Given an initial configuration `c`, a supercompiler produces a list of "residual" graphs of configurations:
```
    g[1], ... , g[k]
```

What is a "graph of configurations"?

## Graphs of configurations

Graphs of configurations are supposed to represent "residual programs" and are defined in Agda (see `Graphs.agda`) in the following way:

```
data Graph (C : Set) : Set where
  back  : ∀ (c : C) → Graph C
  forth : ∀ (c : C) (gs : List (Graph C)) → Graph C
```

Technically, a `Graph C` is a tree, with `back` nodes being
references to parent nodes.

A graph's nodes contain configurations. Here we abstract away
from the concrete structure of configurations.
In this model the arrows in the graph carry no information,
because, this information can be kept in nodes.
(Hence, this information is supposed to be encoded inside
"configurations".)

To simplify the machinery, back-nodes in this model of
supercompilation do not contain explicit references
to parent nodes. Hence, `back c` means that `c` is foldable
to a parent configuration (perhaps, to several ones).

* Back-nodes are produced by folding a configuration to another
  configuration in the history.

* Forth-nodes are produced by

    + decomposing a configuration into a number of other configurations
      (e.g. by driving or taking apart a let-expression), or

    + by rewriting a configuration by another one (e.g. by generalization,
      introducing a let-expression or applying a lemma during
      two-level supercompilation).

## "Worlds" of supercompilation

The knowledge about the input language a supercompiler deals with
is represented by a "world of supercompilation", which is a record
that specifies the following.

* `Conf` is the type of "configurations". Note that configurations are
   not required to be just expressions with free variables! In general,
   they may represent sets of states in any form/language and as well may
   contain any _additional_ information.
 
* `_⊑_` is a "foldability relation". `c ⊑ c′` means that `c` is foldable
  to `c′`. (In such cases `c′` is usually said to be "more general"
  than `c`.)

* `_⊑?_` is a decision procedure for `_⊑_`. This procedure is necessary
  for implementing supercompilation in functional form.

* `_⇉` is a function that gives a number of possible decompositions of
  a configuration. Let `c` be a configuration and `cs` a list of
  configurations such that `cs ∈ c ⇉`. Then `c` can be "reduced to"
  (or "decomposed into") configurations `cs`.

  Suppose that driving is deterministic and, given a configuration `c`,
  produces a list of configurations `c ⇊`. Suppose that rebuilding
  (generalization, application of lemmas) is non-deterministic and
  `c ↷` is the list of configurations that can be produced by
  rebuilding. Then (in this special case) `_⇉` can be implemented as
  follows:
```
    c ⇉ = [ c ⇊ ] ++ map [_] (c ↷)
```

* `whistle` is a "bar whistle" (see `BarWhistle.agda`) that is used
  to ensure termination of functional supercompilation.

Thus we have the following definition in Agda:
```
record ScWorld : Set₁ where

  field
    Conf : Set
    _⊑_ : (c c′ : Conf) → Set
    _⊑?_ : (c c′ : Conf) → Dec (c ⊑ c′)
    _⇉ : (c : Conf) → List (List Conf)
    whistle : BarWhistle Conf

  open BarWhistle whistle public

  History : Set
  History = List Conf

  Foldable : ∀ (h : History) (c : Conf) → Set
  Foldable h c = Any (_⊑_ c) h

  foldable? : ∀ (h : History) (c : Conf) → Dec (Foldable h c)
  foldable? h c = Any.any (_⊑?_ c) h
```

Note that, in addition to (abstract) fields, there are a few concrete
type and function definitions.

* `History` is a list of configuration that have been produced
  in order to reach the current configuration.

* `Foldable h c` means that `c` is foldable to a configuration in
  the history `h`.

* `foldable? h c` decides whether `Foldable h c`.

## Graphs with labeled edges

If we need labeled edges in the graph of configurations,
the labels can be hidden inside configurations.
(Recall that "configurations" do not have to be just symbolic expressions, as
they can contain any additional information.)

Here is the definition in Agda of words of supercompilation with labeled edges:
```
record ScWorldWithLabels : Set₁ where
  field
    Conf : Set    -- configurations
    Label : Set   -- edge labels
    _⊑_ : (c c′ : Conf) → Set            -- c is foldable to c′
    _⊑?_ : (c c′ : Conf) → Dec (c ⊑ c′)  -- ⊑ is decidable
    -- Driving/splitting/rebuilding a configuration:
    _⇉ : (c : Conf) → List (List (Label × Conf))
    whistle : BarWhistle Conf            -- a bar whistle
```

There is defined (in `BigStepSc.agda`) a function
```
injectLabelsInScWorld : ScWorldWithLabels → ScWorld
```
that injects a world with labeled edges into a world without labels
(by hiding labels inside configurations).

## A relational specification of big-step non-deterministic supercompilation

In `BigStepSc.agda` there is given a relational definition of
non-deterministic supercompilation in terms of two relations
```
infix 4 _⊢NDSC_↪_ _⊢NDSC*_↪_

data _⊢NDSC_↪_ : ∀ (h : History) (c : Conf) (g : Graph Conf) → Set
_⊢NDSC*_↪_ : ∀ (h : History) (cs : List Conf) (gs : List (Graph Conf)) → Set
```
which are defined with respect to a world of supercompilation.

Let `h` be a history, `c` a configuration and `g` a graph. Then
`h ⊢NDSC c ↪ g` means that `g` can be produced from `h` and `c` by
non-deterministic supercompilation.

Let `h` be a history, `cs` a list of configurations, `gs` a list
of graphs, and `length cs = length gs`. Then `h ⊢NDSC* cs ↪ gs`
means that each `g ∈ gs` can be produced from the history `h`
and the corresponding `c ∈ cs` by non-deterministic supercompilation.
Or, in Agda:
```
h ⊢NDSC* cs ↪ gs = Pointwise.Rel (_⊢NDSC_↪_ h) cs gs
```
`⊢NDSC_↪_` is defined by two rules
```
data _⊢NDSC_↪_ where

  ndsc-fold  : ∀ {h : History} {c}
    (f : Foldable h c) →
    h ⊢NDSC c ↪ back c

  ndsc-build : ∀ {h : History} {c}
    {cs : List (Conf)} {gs : List (Graph Conf)}
    (¬f : ¬ Foldable h c)
    (i : cs ∈ c ⇉)
    (s : (c ∷ h) ⊢NDSC* cs ↪ gs) →
    h ⊢NDSC c ↪ forth c gs
```
The rule `ndsc-fold` says that if `c` is foldable to a configuration in `h`
there can be produced the graph `back c` (consisting of a single back-node).

The rule `ndsc-build` says that there can be produced a node `forth c gs` if
the following conditions are satisfied.

* `c` _is not_ foldable to a configuration in the history `h`.
* `c ⇉` contains a list of configurations `cs`, such that
  `(c ∷ h) ⊢NDSC* cs ↪ gs`.

Speaking more operationally, the supercompiler first decides how to decompose
`c` into a list of configurations `cs`by selecting a `cs ∈ c`. Then,
for each `c ∈ cs` the supercompiler produces a graph `g`, to obtain a list of
graphs `gs`, and builds the graph `c ↪ forth c gs`.

## A relational specification of big-step multi-result supercompilation

The main difference between multi-result and non-deterministic
supercompilation is that multi-result uses a _whistle_ (see `Whistles.agda`)
in order to ensure the finiteness of the collection of residual graphs.

In `BigStepSc.agda` there is given a relational definition of
multi-result supercompilation in terms of two relations
```
infix 4 _⊢MRSC_↪_ _⊢MRSC*_↪_

data _⊢MRSC_↪_ : ∀ (h : History) (c : Conf) (g : Graph Conf) → Set
_⊢MRSC*_↪_ : ∀ (h : History) (cs : List Conf) (gs : List (Graph Conf)) → Set
```
Again, `_⊢MRSC*_↪_` is a "point-wise" version of `_⊢MRSC_↪_`:
```
h ⊢MRSC* cs ↪ gs = Pointwise.Rel (_⊢MRSC_↪_ h) cs gs
```
`⊢MRSC_↪_` is defined by two rules
```
data _⊢MRSC_↪_ where
  mrsc-fold  : ∀ {h : History} {c}

    (f : Foldable h c) →
    h ⊢MRSC c ↪ back c

  mrsc-build : ∀ {h : History} {c}
    {cs : List Conf} {gs : List (Graph Conf)}
    (¬f : ¬ Foldable h c)
    (¬w : ¬ ↯ h) →
    (i : cs ∈ c ⇉)
    (s : (c ∷ h) ⊢MRSC* cs ↪ gs) →
    h ⊢MRSC c ↪ forth c gs
```

We can see that `⊢NDSC_↪_` and `_⊢MRSC_↪_` differ only in that there is
an additional condition `¬ ↯ h` in the rule `mrsc-build`.

The predicate `↯` is provided by the whistle, `↯ h` meaning that
the history `h` is "dangerous". Unlike the rule `ndsc-build`,
the rule `mrsc-build` is only applicable when `¬ ↯ h`, i.e.
the history `h` is not dangerous.

Multi-result supercompilation is a special case of non-deterministic
supercompilation, in the sense that any graph produced by multi-result
supercompilation can also be produced by non-deterministic
supercompilation:

```
MRSC→NDSC : ∀ {h : History} {c g} →
  h ⊢MRSC c ↪ g → h ⊢NDSC c ↪ g
```
A proof of this theorem can be found in `BigStepScTheorems.agda`.

## Bar whistles

Now we are going to give an alternative definition of multi-result
supercompilation in form of a total function `naive-mrsc`.
The termination of `naive-mrsc` is guaranteed by a "whistle".

In our model of big-step supercompilation whistles are assumed to be
"inductive bars". See:

> Thierry Coquand. **About Brouwer's fan theorem.** September 23, 2003.
> Revue internationale de philosophie, 2004/4 n° 230, p. 483-489.

> <http://www.cairn.info/revue-internationale-de-philosophie-2004-4-page-483.htm>

> <http://www.cairn.info/load_pdf.php?ID_ARTICLE=RIP_230_0483>

Inductive whistles are defined in Agda in the following way.

First of all, `BarWhistles.agda` contains the following declaration
of `Bar D h`:
```
data Bar {A : Set} (D : List A → Set) :
         (h : List A) → Set where
  now   : {h : List A} (bz : D h) → Bar D h
  later : {h : List A} (bs : ∀ c → Bar D (c ∷ h)) → Bar D h
```
At the first glance, this declaration looks as a puzzle. But, actually,
it is not as mysterious as it may seem.

We consider sequences of elements (of some type `A`), and a predicate
`D`. If `D h` holds for a sequence `h`, `h` is said to be "dangerous".

`Bar D h` means that either (1) `h` is dangerous, i.e.
`D h` is valid right now (the rule `now`), or
(2) `Bar D (c ∷ h)` is valid for **all** possible `c ∷ h`
(the rule `later`). Hence, for any continuation `c ∷ h`
the sequence will **eventually** become dangerous.

The subtle point is that if `Bar D []` is valid, it implies that
**any** sequence will eventually become dangerous.

A _bar whistle_ is a record (see `BarWhistles.agda`)
```
record BarWhistle (A : Set) : Set₁ where
  field
    ↯ : (h : List A) → Set
    ↯∷ : (c : A) (h : List A) → ↯ h → ↯ (c ∷ h)
    ↯? : (h : List A) → Dec (↯ h)

    bar[] : Bar ↯ []
```
where

* `↯` is a predicate on sequences, `↯ h` meaning that the sequence
`h` is dangerous.
* `↯∷` postulates that if `↯ h` then `↯ (c ∷ h)` for all possible
`c ∷ h`. In other words, if `h` is dangerous, so are all continuations
of `h`. 
* `↯?` says that `↯` is decidable.
* `bar[]` says that any sequence eventually becomes dangerous.
(In Coquand's terms, `Bar ↯` is required to be "an inductive bar".)

## A function for computing Cartesian products

The functional specification of big-step multi-result supercompilation
considered in the following section is based on the function
`cartesian`:
```
cartesian : ∀ {A : Set} (xss : List (List A)) → List (List A)
```
`cartesian` takes as input a list of lists `xss` (see `Util.agda`).
Each list `xs ∈ xss` represents the set of possible values of
the correspondent component.

Namely, suppose that `xss` has the form
```
    xs[1], xs[2], ... , xs[k]
```
Then `cartesian` returns a list containing all possible lists of
the form
```
    x[1] ∷ x[2] ∷ ... ∷ x[k] ∷ []
```
where `x[i] ∈ xs[i]`. In Agda, this property of `cartesian` is
formulated as follows:
```
∈*↔∈cartesian :
  ∀ {A : Set} {xs : List A} {yss : List (List A)} →
    Pointwise.Rel _∈_ xs yss ↔ xs ∈ cartesian yss
```
A proof of the theorem `∈*↔∈cartesian` can be found in `Util.agda`.

## A functional specification of big-step multi-result supercompilation

A functional specification of big-step multi-result supercompilation
is given in the form of a total function (in `BigStepSc.agda`)
that takes the initial configuration `c` and returns a list of residual
graphs:

```
naive-mrsc : (c : Conf) → List (Graph Conf)
naive-mrsc′ : ∀ (h : History) (b : Bar ↯ h) (c : Conf) →
                List (Graph Conf)

naive-mrsc c = naive-mrsc′ [] bar[] c
```
`naive-mrsc` is defined in terms of a more general function
`naive-mrsc′`, which takes more arguments: a history `h`,
a proof `b` of the fact `Bar ↯ h`, and a configuration `c`.

Note that `naive-mrsc` calls `naive-mrsc′` with the empty history and
has to supply a proof of the fact `Bar ↯ []`. But this proof is
supplied by the whistle!
```
naive-mrsc′ h b c with foldable? h c
... | yes f = [ back c ]
... | no ¬f with ↯? h
... | yes w = []
... | no ¬w with b
... | now bz with ¬w bz
... | ()
naive-mrsc′ h b c | no ¬f | no ¬w | later bs =
  map (forth c)
      (concat (map (cartesian ∘ map (naive-mrsc′ (c ∷ h) (bs c))) (c ⇉)))
```
The definition of `naive-mrsc` is straightforward.

* If `c` is foldable to the history `h`, a back-node is generated
  and the function terminates.

* Otherwise, if `↯ h` (i.e. the history `h` is dangerous), the function
  terminates producing no graphs.

* Otherwise, `h` is not dangerous, and the configuration `c`
  can be decomposed. (Also there are some manipulations with the
  parameter `b` that will be explained later.)

* Thus `c ⇉` returns a list of lists of configurations. The function
  considers each each `cs ∈ c ⇉`, and, for each `c′ ∈ cs` recursively
  calls itself in the following way:  
      `naive-mrsc′ (c ∷ h) (bs c) c′`  
  producing a list of residual graphs `gs′`. So, `cs` is
  transformed into gss, a list of lists of graphs. Note that
  `length cs = length gss`.

* Then the function computes cartesian product `cartesian gss`,
  to produce a list of lists of graphs. Then the results
  corresponding to each `cs ∈ c ⇉` are concatenated by `concat`.

* At this moment the function has obtained a list of lists of graphs,
  and calls `map (forth c)` to turn each graph list into a forth-node.

The function `naive-mrsc` is correct (sound and complete)
with respect to the relation `_⊢MRSC_↪_`:
```
  ⊢MRSC↪⇔naive-mrsc :
    {c : Conf} {g : Graph Conf} →
     [] ⊢MRSC c ↪ g ⇔ g ∈ naive-mrsc c
```
A proof of this theorem can be found in `BigStepScTheorems.agda`.

## Why `naive-mrsc′` always terminates?

The problem with `naive-mrsc′` is that in the recursive call
```
naive-mrsc′ (c ∷ h) (bs c) c′
```
the history grows (`h` becomes `c ∷ h`), and the configuration
is replaced with another configuration of unknown size (`c` becomes
`c′`). Hence, these parameters do not become "structurally smaller".

But Agda's termination checker still accepts this recursive call,
because the second parameter does become smaller (`later bs`
becomes `bs c`). Note that the termination checker considers
`bs` and `bs c` to be of the same "size". Since `bs` is smaller
than `later bs` (a constructor is removed), and `bs` and `bs c` are
of the same size, `bs c` is "smaller" than `later bs`.

Thus purpose of the parameter `b` is to persuade the termination
checker that the function terminates. If `lazy-mrsc` is reimplemented
in a language in which the totality of functions is not checked,
the parameter `b` is not required and can be removed.


