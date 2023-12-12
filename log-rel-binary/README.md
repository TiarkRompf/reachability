# Binary Logical Relations for Reachability Types

## Overview

Logical relations for establishing equational reasoning principles for reachability types [1], gradually increasing in complexity. 

Basics, fundamental lemma, contextual equivalence

- [stlc.v](stlc.v)
- [stlc_ref.v](stlc_ref.v)
- [stlc_reach_ref.v](stlc_reach_ref.v)
- [stlc_reach_ref_effects.v](stlc_reach_ref_effects.v)

Proof of reordering (e.g. concurrency, parallel execution)

- [stlc_reach_ref_effects_reorder_pempty.v](stlc_reach_ref_effects_reorder_pempty.v)
- [stlc_reach_ref_effects_reorder_psep.v](stlc_reach_ref_effects_reorder_psep.v)
- [stlc_reach_ref_effects_reorder_fresh.v](stlc_reach_ref_effects_reorder_fresh.v)
- [stlc_reach_ref_effects_reorder_stfilter.v](stlc_reach_ref_effects_reorder_stfilter.v)

Proof of beta equivalence (e.g. inlining as compiler optimization)

- [stlc_reach_ref_effects_reorder_beta1.v](stlc_reach_ref_effects_reorder_beta1.v)
- [stlc_reach_ref_effects_reorder_beta2.v](stlc_reach_ref_effects_reorder_beta2.v)


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

