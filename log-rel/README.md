# Artifact for "Modeling Reachability Types with Logical Relations"

## Overview of Coq Files by Section

- Section 2 -- Simply-typed lambda calculus (STLC) (Main Paper -- Syntax \& Static Semantics: Fig. 1; logical relation (LR): Fig. 2; Extended Version -- Syntax \& Static Semantics \& Dynamic Semantics: Fig. 1)
    * standard model (without the highlighted parts in Fig. 2): [sec2_stlc.v](sec2_stlc.v)
    * extended model with added store invariants (with the highlighted parts in Fig. 2): [sec2_stlc_highlighted.v](sec2_stlc_highlighted.v)
- Section 3.1- 3.4 -- Reachability types (RT) with first-order store (main paper -- Syntax: Fig. 4; LR: Fig. 5, Semantic typing: Fig. 6; Extended Version -- Unabridged Syntax: Fig. 4)
    * with top-level subtyping built into term typing (t-sub; t-sub-var): [sec3_reach.v](sec3_reach.v)
    * with subtyping as separate relation (Extended Version Fig. 7) [sec3_reach_stp.v](sec3_reach_stp.v)
- Section 3.5 -- Higher-order state (Main Paper -- Fig. 7; Extended Version -- Fig. 8 )
    * [sec3_reach_nested.v](sec3_reach_nested.v)
- Section 3.6 -- Effects (Main Paper -- LR \& Semantic typing: Fig. 8; Extended Version -- LR: Fig. 8; Semantic Typing: Fig. 8)
    * [sec3_reach_nested_effs.v](sec3_reach_nested_effs.v)
- Section 4 -- Binary LR (Main Paper -- LR: Fig. 9; Extended Version -- Context typing: Fig. 11;)
    * without effects: [sec6_reach_binary.v](sec4_reach_binary.v)
    * with effects: [sec6_reach_binary_effs.v](sec4_reach_binary_effs.v)
- Section 5 -- Equational theory (Main Paper -- Equational rules: Fig. 10; illustrated proof of reordering: Fig. 11)
    * store invariants used in the reordering proofs without effects [sec5_store_invariances.v](sec5_store_invariances.v)
    * reordering without effects (Theorem 5.3) [sec5_reorder.v](sec5_reorder.v) 
    * store invariants used in the beta and reordering proofs with effects[sec5_store_invariances_effs.v](sec5_store_invariances_effs.v)
    * reordering with effects (Theorem 5.3): [sec5_reorder_effs.v](sec5_reorder_effs.v)
    * beta conversion (Theorem 5.7): [sec5_beta.v](sec5_beta.v)



## General Notes

This project defines logical relations for a family of reachability type systems with increasing sets of features.
It proves semantic properties, including semantic type soundness, termination, effect safety and program observational equivalence.

In the Coq formalization, qualifiers are a set of variables. We use boolean values to denote the freshness marker, self-reference marker and parameters appeared in qualifiers, e.g., reference type (TRef false q) means values stored in locations are not fresh, and may reach locations in q.

In the definition of context typing, we define one-step context rules, and rule `cx_trans` is used for composing those context typing rules.


## Key Definitions and Theorems

More details can be found in the [artifact document](artifact_doc.pdf).

Notation: P: main paper; S: extended version

| Section | Item | Mechanization | Paper |
|---------|------|---------------|-------|
| Syntactic Definitions | Term Typing   | `Inductive has_type` | P $\S 3.2$ |
|                       | Subtyping     | `Inductive stp`      | S $\S 3.5$ |
|                       | Subqualifying | `Inductive qstp`     | S $\S 3.5$ |
|                       | Context Typing | `Inductive ctx_type` | S $\S 4$
| Semantic Definitions | Bigstep Interpreter    | `Fixpoint teval`      | S $\S 1$
|                      | Value Interpretation   | `Fixpoint val_type`   | P $\S 2.2$, P $\S 3.3$, S $\S 4$, P $\S 3.5$, S $\S 5$, P $\S 3.6$
|                      | Semantic Typing        | `Definition sem_type` | P $\S 3.4$, P $\S 3.5$, P $\S 3.6$, P $\S 4.3$
|                      | Semantic Subqualifying | `Definition sem_qtp` | S $\S 3.5$
|                      | Semantic Subpretyping  | `Definition sem_stp`  | S $\S 3.5$  
|                      | Semantic Subtyping     | `Definition sem_sqtp` | S $\S 3.5$
|                      | Contexual Equivalence  | `Definition context_equiv` | P $\S 4.1$
|                      | Various semantic typing rules | Lemmas start with `sem_` | P $\S 3.3$, P $\S 3.5$, S $\S 3.4 $, P $\S 3.6$, S: $\S 3.6$
| Metatheory | Subqualifying | `Theorem qtp_fundamental`  | S $\S 3.5$
| | Subpretying | `Theorem stp_fundamental`  | S $\S 3.5$
| | Subtyping | `Theorem sqtp_fundamental` | S $\S 3.5$
|            | Typing        | `Theorem fundamental_property` | P $\S 3.4$, P $\S 3.5$, P $\S 3.6$, P $\S 4.4$ |
|            | Contextual Equivalence | `Theorem contextual_equivalence` | P $\S 4.4$
|            | Time Travelling | `Lemma valt_store_change` | P $\S 2.2$, P $\S 3.3$, P $\S 3.5$, P $\S 3.6$, P $\S 4.3$
|            | Encapsulation   | `Lemma encapsulation`  | P $\S 3.4$, P $\S 3.5$, P $\S 3.6$, P $\S 4.4$    
| Equational Theory | Re-ordering-$\lambda^\diamondsuit$ & Re-ordering-$\lambda^{\diamondsuit}_{\varepsilon}$ | `Theorem reorder_seq` | P $\S 5.1$|
| |$\beta$-equivalence | `Theorem beta_equivalence` | P $\S 5.2$
| | Store Invariants | `Lemma store_invariance` | S $\S 7$
| |                  | `Lemma store_invariance2`| S $\S 7$
| |                  | `Lemma store_invariance3`| S $\S 7$
| |                  | `Lemma store_invariance2'`| S $\S 7$
| |                  | `Lemma store_invariance3'`| S $\S 7$


## Reusability Guide

The following components are reusable and extensible for future research:

- `env.v`: This file contains the module for general theories of environments as lists of De Bruijn levels, suitable for representing syntax with variable binding. This module is independent of the specific systems presented in the paper, and can be reused in the development of any system involving variable binding.
- `qualifiers.v`: This file provides modular and general reasoning about qualifiers. Extending a system with additional terms or types requires no change to this file.

- `tactics.v`: This file contains general-purpose tactics for relating propositions to Boolean expressions.

The following shows how to experiment new equational rules using the current systems:
- Proving new equational rules without effects: Create a new Coq file, and import the files `sec4_reach_binary.v` and `sec5_store_invariants.v`.
    
- Proving new equational rules with effects: Create a new Coq file, and import the files `sec4_reach_binary_effs.v` and `sec5_store_invariants_effs.v`. 

The following shows how to extend the current systems:

- Adding new types: For each system, new types can be introduced by extending the inductive defined type `ty` in the corresponding file. 

- Adding new language constructs: For each system, new language constructs can be introduced by extending the inductive defined type `tm` in the corresponding file. 
- Adding new typing rules: For each system, new typing rules can be introduced by extending the inductive defined proposition `has_type` in the corresponding file. 



## Compilation

To generate/update the `CoqMakefile` from `_CoqProject`:

`coq_makefile -f _CoqProject -o CoqMakefile`

Then, to compile/check all proof scripts listed in `_CoqProject`:

`make -f CoqMakefile all`

Compatibility tested with Coq `8.17.1`.


## References

[1] **Modeling Reachability Types with Logical Relations** </br>
Yuyan Bao, Songlin Jia, Guannan Wei, Oliver Bračevac, Tiark Rompf
([pdf](https://doi.org/10.1145/3763116)).

[2] **Modeling Reachability Types with Logical Relations** (Extended Version)</br>
Yuyan Bao, Songlin Jia, Guannan Wei, Oliver Bračevac, Tiark Rompf
([pdf](https://arxiv.org/pdf/2309.05885)).