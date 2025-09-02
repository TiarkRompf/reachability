# Unary Logical Relations for Reachability Types

## Overview

Logical relations for proving semantic type soundness and termination of reachability types [1], gradually increasing in complexity. 


Basics (Winter 2022)

- [stlc.v](stlc.v)
- [stlc_reach.v](stlc_reach.v)
- [stlc_ref.v](stlc_ref.v)
- [stlc_reach_ref.v](stlc_reach_ref.v)
- [stlc_reach_ref_minimal.v](stlc_reach_ref_minimal.v)

Effects: kill, move, swap (Spring 2023)

- [stlc_reach_ref_effects.v](stlc_reach_ref_effects.v)
- [stlc_reach_ref_kill.v](stlc_reach_ref_kill.v)
- [stlc_reach_ref_kill_nested.v](stlc_reach_ref_kill_nested.v)
- [stlc_reach_ref_move.v](stlc_reach_ref_move.v)
- [stlc_reach_ref_move_nested.v](stlc_reach_ref_move_nested.v)
- [stlc_reach_ref_swap.v](stlc_reach_ref_swap.v)

Effects: simpler model, only writes (Summer 2023)

- [stlc_reach_ref_effects_stty_fresh.v](stlc_reach_ref_effects_stty_fresh.v)
- [stlc_reach_ref_effects_stty_fresh_fun.v](stlc_reach_ref_effects_stty_fresh_fun.v)
- [stlc_reach_ref_effects_stty_fresh_stchain.v](stlc_reach_ref_effects_stty_fresh_stchain.v)
- [stlc_reach_ref_effects_stty_nofresh.v](stlc_reach_ref_effects_stty_nofresh.v)
- [stlc_reach_ref_effects_stty_tseq_stc.v](stlc_reach_ref_effects_stty_tseq_stc.v)

Overlap, self, freshness (Summer 2023)

- [stlc_reach_ref_overlap.v](stlc_reach_ref_overlap.v)
- [stlc_reach_ref_overlap_trans.v](stlc_reach_ref_overlap_trans.v)
- [stlc_reach_ref_overlap_self_fresh.v](stlc_reach_ref_overlap_self_fresh.v)
- [stlc_reach_ref_overlap_self_fresh_mut.v](stlc_reach_ref_overlap_self_fresh_mut.v)
- [stlc_reach_ref_overlap_self_fresh_mut_nested.v](stlc_reach_ref_overlap_self_fresh_mut_nested.v)

Tight qualifiers (Fall 2023)

- [stlc_reach_ref_kill_tight.v](stlc_reach_ref_kill_tight.v) -- tight effect qualifiers, no upcasting/escaping
- [stlc_reach_ref_kill_tight_effects.v](stlc_reach_ref_kill_tight_effects.v) -- pure expressions don't change the store
- [stlc_reach_ref_kill_tight_tight_effects.v](stlc_reach_ref_kill_tight_tight_effects.v) -- tighten qualifiers further


Subtyping (Spring 2024)

- [stlc_reach_ref_overlap_self_fresh_mut.v](stlc_reach_ref_overlap_self_fresh_mut_stp.v) -- subtyping, pair encoding, escaping via upcast to self-ref, also type checking [5]



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