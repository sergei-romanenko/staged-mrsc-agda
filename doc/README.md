# Staged Multi-result Supercompilation: Filtering by Transformation

When trying to apply supercompilation to problem solving we naturally come to 
the idea of _multi-result_ supercompilation: instead of trying to guess, which 
residual graph of configurations is "the best" one, a multi-result supercompiler 
(`mrsc`) produces a collection of residual graphs.

However, the main problem with multi-result supercompilation is that it can 
produce millions of residual graphs!

Luckily, filtering can be performed before producing final results
of supercompilation...

How? This is explained in the preprint

* Sergei A. Grechanik, Ilya G. Klyuchnikov, Sergei A. Romanenko.
__Staged multi-result supercompilation: filtering before producing.__
Keldysh Institute Preprints, (70), 2013.    
<http://library.keldysh.ru//preprint.asp?lg=e&id=2013-70>

The wiki pages are, on the one hand, a draft of the preprint,
but, on the other hand, they contain some additional stuff,
omitted in the preprint for the lack of space.

The paper

* Sergei Grechanik, Ilya Klyuchnikov, and Sergei Romanenko.
__Staged Multi-Result Supercompilation: Filtering by Transformation.__
In *Fourth International Valentin Turchin Workshop on Metacomputation
(Proceedings of the Fourth International Valentin Turchin Workshop
on Metacomputation. Pereslavl-Zalessky, Russia, June 29 -
July 3, 2014)*.    
A.V. Klimov and S.A. Romanenko, Ed. -
Pereslavl-Zalessky: Publishing House "University of Pereslavl", 2014,
256 p. ISBN 978-5-901795-31-6, pages 54-78.    
[link](http://meta2014.pereslavl.ru/papers/papers.html)
[PDF](http://meta2014.pereslavl.ru/papers/2014_Grechanik_Klyuchnikov_Romanenko__Staged_Multi-Result_Supercompilation__Filtering_by_Transformation.pdf)
[slides](http://pat.keldysh.ru/~roman/doc/2014_Grechanik_Klyuchnikov_Romanenko__Staged_Multi-Result_Supercompilation__Filtering_by_Transformation__slides.pdf)

is an extended version of the preprint.

## TOC

* [Is it possible to filter results that have not yet been produced?](FilteringBeforeProducing.md)
* [A model of big-step multi-result supercompilation in Agda](BigStepSc.md).
* [Staging big-step multi-result supercompilation](StagedBigStepSc.md).
* [Cleaning lazy graphs](CleaningLazyGraphs.md).
* [Codata and corecursion: cleaning before whistling](CleaningBeforeWhistling.md).
* [Counting without generation](CountingWithoutGeneration.md).
* [An example: big-step supercompilation for counter systems](BigStepCounters.md).
* [Conclusions and references](ConclusionsAndReferences.md).
* Source code [in Agda](https://github.com/sergei-romanenko/staged-mrsc-agda). (Usable with Agda 2.4.2.2 and stdlib 0.9.)
* [Presentation](https://bitbucket.org/sergei.romanenko/staged-mrsc-agda/downloads).
