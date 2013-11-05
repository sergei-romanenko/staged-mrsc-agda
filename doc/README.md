# Staged Multi-result Supercompilation: Filtering before Producing

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

## TOC

* [Is it possible to filter results that have not yet been produced?](FilteringBeforeProducing.md)
* [A model of big-step multi-result supercompilation in Agda](BigStepSc.md).
* [Staging big-step multi-result supercompilation](StagedBigStepSc.md).
* [Cleaning lazy graphs](CleaningLazyGraphs.md).
* [Codata and corecursion: cleaning before whistling](CleaningBeforeWhistling.md).
* [Counting without generation](CountingWithoutGeneration.md).
* [An example: big-step supercompilation for counter systems](BigStepCounters.md).
* [Conclusions and references](ConclusionsAndReferences.md).
* Source code [in Agda](https://github.com/sergei-romanenko/staged-mrsc-agda). (Usable with Agda 2.3.2 and stdlib 0.7.)
* [Presentation](https://bitbucket.org/sergei.romanenko/staged-mrsc-agda/downloads).
