# Unary Logical Relations for Reachability Types

## Overview

Step-Indexed Logical relations for proving semantic type soundness of reachability types [1], gradually increasing in complexity. 


Basics (Winter 2024)

- [stlc_ref_indexed_reachb.v](stlc_ref_indexed_reachb.v)
- [stlc_ref_indexed_reachb_effs.v](stlc_ref_indexed_reachb_effs.v)
- [stlc_ref_indexed_reach_nested.v](stlc_ref_indexed_reach_nested.v)
- [stlc_ref_indexed_reach_nested_effs.v](stlc_ref_indexed_reach_nested_effs.v)


## Compilation

To generate/update the `CoqMakefile` from `_CoqProject`:

`coq_makefile -f _CoqProject -o CoqMakefile`

Then, to compile/check all proof scripts listed in `_CoqProject`:

`make -f CoqMakefile all`

Compatibility tested with Coq `8.17.1`.

## References

[1] **Reachability Types: Tracking Aliasing and Separation in Higher-order Functional Programs** (OOPSLA 2021)</br>
Yuyan Bao, Guannan Wei, Oliver Bračevac, Luke Jiang, Qiyang He, Tiark Rompf
([pdf](https://www.cs.purdue.edu/homes/rompf/papers/bao-oopsla21.pdf)).

[2] **Polymorphic Reachability Types: Tracking Aliasing and Separation in Higher-order Generic Programs** (POPL 2024)</br>
Guannan Wei, Oliver Bračevac, Siyuan He, Yuyan Bao, Tiark Rompf
([pdf](https://www.cs.purdue.edu/homes/rompf/papers/wei-popl24.pdf)).

[3] **Graph IRs for Impure Higher-Order Languages: Making Aggressive Optimizations Affordable with Precise Effect Dependencies** (OOPSLA 2023)</br>
Oliver Bračevac, Guannan Wei, Luke Jiang, Supun Abeysinghe, Songlin Jia, Siyuan He, Yuyan Bao, Tiark Rompf
([pdf](https://www.cs.purdue.edu/homes/rompf/papers/bracevac-oopsla23.pdf)).

[4] **Modeling Reachability Types with Logical Relations: Semantic Type Soundness, Termination, and Equational Theory** (arXiv 2023)</br>
Yuyan Bao, Guannan Wei, Oliver Bračevac, Tiark Rompf
([pdf](https://arxiv.org/pdf/2309.05885.pdf)).

[5] **Escape with Your Self: Expressive Reachability Types with Sound and Decidable Bidirectional Type Checking** </br>
Songlin Jia, Guannan Wei, Siyuan He, Yueyang Tang, Yuyan Bao, Tiark Rompf.