# Type, Ability, and Effect Systems

## Overview

A general logical relation suitable for proving purity, applicable to a range of typing disciplines and language designs [1]. 




## Compilation

To generate/update the `CoqMakefile` from `_CoqProject`:

`coq_makefile -f _CoqProject -o CoqMakefile`

Then, to compile/check all proof scripts listed in `_CoqProject`:

`make -f CoqMakefile all`

Compatibility tested with Coq `8.17.1`.

## References

[1] **Type, Ability, and Effect Systems: Perspectives on Purity, Semantics, and Expressiveness**</br>
Yuyan Bao, Tiark Rompf
([pdf](https://www.cs.purdue.edu/homes/rompf/papers/bao_purity25.pdf)).
