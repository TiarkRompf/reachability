# Expressive Reachability Types with Sound and Decidable Bidirectional Type Checking

## Overview


* `stlc_reach_ref_overlap_self_fresh_mut_stp.v`:
    Coq mechanization of the $\lambda^\diamond_R$-calculus [2] and its type checking algorithm.
    - Syntactic definitions
    - Semantic definitions [1]
    - Metatheory
    - Typing examples
    - Bidirectional typing algorithm
    - Metatheory of the algorithm
    - Type checking examples

## References

[1] **Modeling Reachability Types with Logical Relations: Semantic Type Soundness, Termination, and Equational Theory** (arXiv 2023)</br>
Yuyan Bao, Guannan Wei, Oliver Bračevac, Tiark Rompf
([pdf](https://arxiv.org/pdf/2309.05885.pdf)).

[2] **Escape with Your Self: Expressive Reachability Types with Sound and Decidable Bidirectional Type Checking** </br>
Songlin Jia, Guannan Wei, Siyuan He, Yueyang Tang, Yuyan Bao, Tiark Rompf.


## Compilation

To generate/update the `CoqMakefile` from `_CoqProject`:

`coq_makefile -f _CoqProject -o CoqMakefile`

Then, to compile/check all proof scripts listed in `_CoqProject`:

`make -f CoqMakefile all`

Compatibility tested with Coq `8.17.1`.


