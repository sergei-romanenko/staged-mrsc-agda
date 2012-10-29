module Rules where

{- ### Schemes of different types of supercompilation ### -}

{-
As presented in the paper

Ilya G. Klyuchnikov, Sergei A. Romanenko. Formalizing and Implementing
Multi-Result Supercompilation.
In Third International Valentin Turchin Workshop on Metacomputation
(Proceedings of the Third International Valentin Turchin Workshop on
Metacomputation. Pereslavl-Zalessky, Russia, July 5-9, 2012).
A.V. Klimov and S.A. Romanenko, Ed. - Pereslavl-Zalessky: Ailamazyan
University of Pereslavl, 2012, 260 p. ISBN 978-5-901795-28-6, pages
142-164. 
-}

{-
### Notation: ###

g – a current graph of configurations
β – a current node in a graph of configurations
c – a configuration in a current node β
-}

{-
### (a) SC: Deterministic (traditional) supercompilation ###

(Fold)

∃α : foldable(g, β, α)
----------------------
g → fold(g, β, α)

(Drive)

∄α : foldable(g, β, α)
¬dangerous(g, β)
cs = driveStep(c)
--------------------------
g → addChildren(g, β, cs)

(Rebuild)
∄α : foldable(g, β, α)
dangerous(g, β)
c′ = rebuilding(g, c)
----------------------
g → rebuild(g, β, c′)
-}

{-

### (b) NDSC: Non-deterministic supercompilation (transformation relation) ###

(Fold)

∃α : foldable(g, β, α)
----------------------
g → fold(g, β, α)

(Drive)

∄α : foldable(g, β, α)
cs = driveStep(c)
--------------------------
g → addChildren(g, β, cs)

(Rebuild)
∄α : foldable(g, β, α)
c′ ∈ rebuildings(c)
----------------------
g → rebuild(g, β, c′)

-}

{-

### (c) MRSC: Multi-result supercompilation ###

(Fold)

∃α : foldable(g, β, α)
----------------------
g → fold(g, β, α)

(Drive)

∄α : foldable(g, β, α)
¬dangerous(g, β)
cs = driveStep(c)
--------------------------
g → addChildren(g, β, cs)

(Rebuild)

∄α : foldable(g, β, α) c′ ∈ rebuildings(c)
-----------------------------------------
g → rebuild(g, β, c′)

-}
