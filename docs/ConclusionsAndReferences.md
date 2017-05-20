# Conclusions and references

## Conclusions

When using supercompilation for problem solving, it seems natural
to produce a collection of residual graphs of configurations
by multi-result supercompilation and then
then to filter this collection according to some criteria.
Unfortunately, this may lead to combinatorial explosion.

We have suggested the following solution.

* Instead of generating and filtering a collection of residual
  graphs of configurations, we can produce a compact representation
  for the collection of graphs (a "lazy graph"), and then analyze
  this representation.

* This compact representation can be derived from
  a (big-step) multi-result supercompiler in a systematic way by
  (manually) staging this supercompiler to represent it
  as a composition of two stages. At the first stage, some
  graph-building operations are delayed to be later performed
  at the second stage.

* The result produced by the first stage is a "lazy graph",
  which is, essentially, a program to be interpreted at the
  second stage, to actually generate a collection of residual
  graphs.

* The key point of our approach is that a number of problems
  can be solved by directly analyzing the lazy graphs, rather
  than by actually generating and analyzing the collections
  of graphs they represent.

* In some cases of practical importance, the analysis of
  a lazy graph can be performed in linear time.

## Related work

The idea that supercompilation can produce a compact representation
of a collection of residual graphs is due to Grechanik
[Gre2012ovgr]. In particular, the data structure `LazyGraph C`
we use for representing the results of the first phase of
the staged multi-result supercompiler can be considered as
a representation of "overtrees", which was informally described
in [Gre2012ovgr].

Big-step supercompilation was studied and implemented by
Bolingbroke and Peyton Jones [Bol2010scev]. Our approach
differs in that we are interested in applying supercompilation to
problem solving. Thus

* We consider multi-result supercompilation, rather than
  single-result supercompilation.

* Our big-step supercompilation constructs graphs of configurations
  in an explicit way, because the graphs are going to be filtered
  and/or analyzed at a later stage.

* Bolingbroke and Peyton Jones considered big-step supercompilation
  in functional form, while we have studied both a relational
  specification of big-step supercompilation and the functional
  one and have proved the correctness of the functional
  specification with respect to the relational one.

A relational specification of single-result supercompilation
was suggested by Klimov [Kli2008rel], who argued that
supercompilation relations can be used for simplifying proofs
of correctness of supercompilers. Later, Klyuchnikov [Klyu2010]
used a supercompilation relation for proving the correctness
of a small-step single-result supercompiler for
a higher-order functional language. In the present work we
consider a supercompilation relation for a _big-step_
_multi-result_ supercompilation.

We have developed an abstract model of big-step multi-result
supercompilation in the language Agda and have proved a number
of properties of this model. This model, in some respects,
differs from the other models of supercompilation.

The MRSC Toolkit by Klyuchnikov and Romanenko [Klyu2011mrsc]
abstracts away some aspects of supercompilation, such as
the structure of configurations and the details of the
subject language. However, the MRSC Toolkit is a framework
for implementing small-step supercompilers, while our model
in Agda formalizes big-step supercompilation. Besides,
the MRSC Toolkit is implemented in Scala, for which reason
it currently provides no means for neither formulating nor
proving theorems about supercompilers implemented with
the MRSC Toolkit.

Krustev was the first to formally verify a simple supercompiler
by means of a proof assistant [Kru2010scver]. Unlike the MRSC
Toolkit and our model of supercompilation, Krustev deals with
a specific supercompiler for a concrete subject language.
(Note, however, that also the subject language is simple,
it is still Turing complete.)

In another paper Krustev presents a framework for building
formally verifiable supercompilers [Kru2013scfr]. It is
similar to the MRSC in that it abstracts away some details
of supercompilation, such as the subject language and
the structure of configurations, providing, unlike the MRSC
Toolkit, means for formulating and proving theorems about
supercompilers.

However, in both cases Krustev deals with single-result
supercompilation, while the primary goal of our model of
supercompilation is to formalize and investigate some subtle
aspects of multi-result supercompilation.

## References

* [Bol2010scev] Maximilian C. Bolingbroke and Simon L. Peyton Jones.
__Supercompilation by evaluation.__
In _Proceedings of the third ACM Haskell symposium on Haskell (Haskell '10)_.
ACM, New York, NY, USA, 2010, pages 135-146.
DOI=10.1145/1863523.1863540 <http://doi.acm.org/10.1145/1863523.1863540>

* [Kli2008rel] Andrei V. Klimov.
__A program specialization relation based on supercompilation and its properties.__
In _First International Workshop on Metacomputation in Russia
(Proceedings of the first International Workshop on Metacomputation in Russia.
Pereslavl-Zalessky, Russia, July 2-5, 2008)_.
A. P. Nemytykh, Ed. - Pereslavl-Zalessky: Ailamazyan University of Pereslavl, 2008, 108 p.
ISBN 978-5-901795-12-5, pages 54-77.

* [Kli2012cnt] Andrei V. Klimov, Ilya G. Klyuchnikov, Sergei A. Romanenko.
__Automatic Verification of Counter Systems via Domain-Specific Multi-Result Supercompilation.__
In _Third International Valentin Turchin Workshop on Metacomputation
(Proceedings of the Third International Valentin Turchin Workshop on Metacomputation.
Pereslavl-Zalessky, Russia, July 5-9, 2012)_.
A.V. Klimov and S.A. Romanenko, Ed. - Pereslavl-Zalessky: Ailamazyan University of Pereslavl, 2012, 260 p.
ISBN 978-5-901795-28-6, pages 112-141.

* [Klyu2010] Ilya Klyuchnikov.
__Supercompiler HOSC: proof of correctness.__ Preprint 31.
Keldysh Institute of Applied Mathematics, Moscow. 2010.
URL: <http://library.keldysh.ru/preprint.asp?lg=e&id=2010-31>

* [Klyu2011mrsc] Ilya G. Klyuchnikov and Sergei A. Romanenko.
__MRSC: a toolkit for building multi-result supercompilers.__
Preprint 77, Keldysh Institute of Applied Mathematics, 2011.
URL: <http://library.keldysh.ru/preprint.asp?lg=e&id=2011-77>.

* [Klyu2012form] Ilya G. Klyuchnikov, Sergei A. Romanenko.
__Formalizing and Implementing Multi-Result Supercompilation.__
In _Third International Valentin Turchin Workshop on Metacomputation
(Proceedings of the Third International Valentin Turchin Workshop on Metacomputation.
Pereslavl-Zalessky, Russia, July 5-9, 2012)_.
A.V. Klimov and S.A. Romanenko, Ed. - Pereslavl-Zalessky: Ailamazyan University of Pereslavl, 2012, 260 p.
ISBN 978-5-901795-28-6, pages 142-164.

* [Klyu2012brgr] Ilya G. Klyuchnikov and Sergei A. Romanenko.
__Multi-result supercompilation as branching growth of the penultimate level in metasystem transitions.__
In _Proceedings of the 8th international conference on Perspectives of System Informatics (PSI'11),
Edmund Clarke, Irina Virbitskaite, and Andrei Voronkov (Eds.)_.
Lecture Notes in Computer Science, volume 7162, pages 210-226. Springer-Verlag, Berlin, Heidelberg, 2012.
(ISBN: 978-3-642-29708-3) DOI=10.1007/978-3-642-29709-0_19

* [Gre2012ovgr] Sergei A. Grechanik.
__Overgraph Representation for Multi-Result Supercompilation.__
In _Third International Valentin Turchin Workshop on Metacomputation
(Proceedings of the Third International Valentin Turchin Workshop on Metacomputation._
Pereslavl-Zalessky, Russia, July 5-9, 2012).
A.V. Klimov and S.A. Romanenko, Ed. - Pereslavl-Zalessky: Ailamazyan University of Pereslavl, 2012, 260 p.
ISBN 978-5-901795-28-6, pages 48-65.

* [Kru2010scver] Dimitur N. Krustev.
__A simple supercompiler formally verified in Coq.__
In _A. P. Nemytykh, editor, Second International Valentin Turchin Memorial Workshop
on Metacomputation in Russia, Pereslavl-Zalessky, Russia, July 1–5, 2010, pages 102-127_.
Ailamazyan University of Pereslavl, Pereslavl-Zalessky, 2010.

* [Kru2013scfr] Dimitur N. Krustev.
__Towards a Framework for Building Formally Verified Supercompilers in Coq.__
In _Proceedings of the 13th International Symposium on Trends in Functional Programming (TFP 2012),
St Andrews, UK, June 12-14, 2012_.
Lecture Notes in Computer Science Volume 7829, 2013, pp 133-148.
