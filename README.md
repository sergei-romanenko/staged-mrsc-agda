# Staged Multi-result Supercompilation: Filtering before Producing

When trying to apply supercompilation to problem solving we naturally come to 
the idea of _multi-result_ supercompilation: instead of trying to guess, which 
residual graph of configurations is "the best" one, a multi-result supercompiler 
(`mrsc`) produces a collection of residual graphs.

However, the main problem with multi-result supercompilation is that it can 
produce millions of residual graphs!

Luckily, filtering can be performed before producing final results
of supercompilation...

See more details [here](doc/Home.md).
