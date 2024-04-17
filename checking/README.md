# Expressive Reachability Types with Sound and Decidable Bidirectional Type Checking

## Overview

* `stlc_reach_ref_overlap_self_fresh_mut_stp.v`:
    Bidirectional type system $\lambda^\diamond_R$ with decidable type checking/inference, including refined subtyping for self-references [2].

## Mechanization Outline ([`stlc_reach_ref_overlap_self_fresh_mut_stp.v`](stlc_reach_ref_overlap_self_fresh_mut_stp.v))

| Section | Item | Mechanization | Paper |
|---------|------|---------------|-------|
| Syntactic Definitions | Term Typing   | `Inductive has_type` | $\S 3.2$ |
|                       | Subtyping     | `Inductive stp`      | $\S 3.3$ |
|                       | Subqualifying | `Inductive qstp`     | $\S 3.3$ |
| Semantic Definitions | Bigstep Interpreter    | `Fixpoint teval`      |
|                      | Value Interpretation   | `Fixpoint val_type`   |
|                      | Semantic Typing        | `Definition sem_type` |
|                      | Semantic Subtyping     | `Definition sem_stp2` |
|                      | Semantic Subqualifying | `Definition sem_qstp` |
|                      | Various semantic typing rules | ... |
| Metatheory | Subqualifying | `Theorem qstp_fundamental`  |
|            | Subtyping     | `Theorem stp2_fundamental`  |
|            | Typing        | `Theorem full_total_safety` | $\S 3.4$ |
| Typing Examples | Box (V1) | Transparent `Lemma t_box_transparent`,<br>`Lemma t_unbox_transparent`,<br>`Lemma ex_box_unbox_transparent1` |
|                 |          | Opaque `Lemma t_unbox_opaque1` |
|                 | Box (v2) | Transparent `Lemma t_box_transparent2`,<br>`Lemma t_unbox_transparent2`,<br>`Lemma ex_box_unbox_transparent2` |
|                 |          | Opaque `Lemma t_unbox_opaque2` |
|                 |          | Subtyping `Lemma upcast_box`, `Lemma ex_escape1` |
|                 | Pair     | Transparent `Lemma t_pair_transparent`,<br>`Lemma t_fst_transparent`,<br>`Lemma t_snd_transparent` |
|                 |          | Opaque `Lemma TPair_opaque_fst`,<br>`Lemma TPair_opaque_snd` |
|                 |          | Subtyping `Lemma t_pair_trans_to_opaque` |
| Typing Algorithm | Qualifier Upcast     | `Definition get_qstp`,<br>`Lemma get_qstp_is_sound`         | $\S 4.1$ |
|                  | Qualifier Checking   | `Definition check_qstp`,<br>`Lemma check_qstp_is_sound`     | $\S 4.1$ |
|                  | Subtype Checking     | `Fixpoint upcast`,<br>`Lemma upcast_is_sound`               | $\S 4.2$ |
|                  | Avoidance Algorithm  | `Fixpoint avoidance`,<br>`Lemma avoidance_is_sound`         | $\S 4.3$ |
|                  | Bidirectional Typing | `Fixpoint bidirectional`,<br>`Lemma bidirectional_is_sound` | $\S 4.4$ |
| Type Checking Examples | Subtype Checking    | `Example upcast_with_pair`          |
|                        | Avoidance Algorithm | `Example avoidance_with_pair_{a,b}` |
|                        | End-to-End Example  | `Definition pair_example`           | $\S 5$ |

## References

[1] **Modeling Reachability Types with Logical Relations: Semantic Type Soundness, Termination, and Equational Theory** (arXiv 2023)</br>
Yuyan Bao, Guannan Wei, Oliver Bračevac, Tiark Rompf
([pdf](https://arxiv.org/pdf/2309.05885.pdf)).

[2] **Escape with Your Self: Expressive Reachability Types with Sound and Decidable Bidirectional Type Checking** </br>
Songlin Jia, Guannan Wei, Siyuan He, Yueyang Tang, Yuyan Bao, Tiark Rompf
([pdf](https://arxiv.org/pdf/2404.08217.pdf)).


## Compilation

To generate/update the `CoqMakefile` from `_CoqProject`:

`coq_makefile -f _CoqProject -o CoqMakefile`

Then, to compile/check all proof scripts listed in `_CoqProject`:

`make -f CoqMakefile all`

Compatibility tested with Coq `8.17.1`.


