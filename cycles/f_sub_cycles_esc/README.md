# Artifact for "Complete the Cycle: Reachability Types with Expressive Cyclic References"

Conference: OOPSLA 2025 R2

This document serves as the Artifact Overview, following the OOPSLA 2025
guidelines.

## Introduction

This artifact supports the following claims from the paper:

| Claim                                                 | Supported? | How                                         |
| -------                                               | ---------- | --------                                    |
| Type system with cyclic references                    | Yes        | Fully mechanized in `f_sub_cycles_esc.v`    |
| Soundness: progress, preservation, separation         | Yes        | Mechanized theorems in `f_sub_cycles_esc.v` |
| Case studies (e.g., fixed-point, escaping refs, etc.) | Yes        | Mechanized in `examples.v`                  |

This guide includes:
- Build instructions and dependencies (See "Getting Started Guide" below)
- Documentation mapping paper content to formal definitions (See
  [Paper-to-Artifact Correspondence](#paper-to-artifact-correspondence))
- [Explicit Axioms and Assumptions](#explicit-axioms-and-assumptions)
- [Reusability Guide](#reusability-guide)

## Getting Started Guide

### Requirements

- **Coq version**: 8.17.1  
- **OCaml version**: 4.13.1

Depending on the hardware used, compilation can take from **35-65 minutes**. If time-constrained, you may inspect `.vo` files and example scripts directly.

### Hardware Used

Compilation was tested on a machine with the following specifications:

- Architecture: x86\_64
- CPU: Intel(R) Xeon(R) Platinum 8168 @ 2.70GHz, 96 physical cores (192 threads)
- RAM: 768 GB
- OS: Linux, 64-bit

### Installation Guide

If you do not have OPAM installed, follow the instructions at
https://opam.ocaml.org/doc/Install.html. Then continue below with steps 1–3.

#### 1. Create a fresh switch with the required OCaml version
```
opam switch create reachability-coq 4.13.1
eval $(opam env)
```

#### 2. Install Coq and dependencies
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.17.1
```

Check that the installation succeeded:

```
coqc -v
# Should output: The Coq Proof Assistant, version 8.17.1
```

#### 3. Build the Proof

To compile the development, run the following commands in the root directory:

```
coq_makefile -f _CoqProject -o Makefile
make
```

## Paper-to-Artifact Correspondence

This artifact accompanies the paper and corresponds to the system described in
**Section 4**, which is an extension based on the system presented in **Section
3**. It includes metatheory presented in **Section 3.5** and case studies
presented in **Section 5**.

The following tables list correspondence between definitions/lemmas in the
mechanization and that in the paper. All mechanized lemmas are located in
`f_sub_cycles_esc.v`, and all examples are located in `examples.v`

### The Type System

| **Coq Definition** | **Coq File**         | **Paper**                         |
| ----               | ----                 | ----                              |
| `has_type`         | `f_sub_cycles_esc.v` | Typing (Fig. 8, Fig. 11, Fig. 12) |
| `stp`              | `f_sub_cycles_esc.v` | Subtyping (Fig. 9)                |
| `q_trans_tenv`     | `f_sub_cycles_esc.v` | Transitive Lookup (Fig. 10)       |
| `wf_senv`          | `f_sub_cycles_esc.v` | Well-Formed Stores (Fig. 11)      |

### Metatheory

| **Coq Lemma**                        | **Coq File**         | **Lemma in Paper** |
| ----                                 | ----                 | ----               |
| `qenv_saturated_iff`                 | `f_sub_cycles_esc.v` | Lemma 3.1          |
| `q_trans_tenv_subst1`                | `f_sub_cycles_esc.v` | Lemma 3.2          |
| `substitution_gen`                   | `f_sub_cycles_esc.v` | Lemma 3.3          |
| `progress`                           | `f_sub_cycles_esc.v` | Lemma 3.4          |
| `preservation`                       | `f_sub_cycles_esc.v` | Lemma 3.5          |
| `preservation_of_separation`         | `f_sub_cycles_esc.v` | Lemma 3.6          |
| `parallel_progress_and_preservation` | `f_sub_cycles_esc.v` | Lemma 3.7          |

### Examples

| **Coq Example**                    | **Coq File** | **Example in Paper**          |
| ----                               | ----         | ----                          |
| `knot_typable`                     | `examples.v` | Figure 1b                     |
| `typing_parallel_update`           | `examples.v` | Figure 2b and Section 5.2     |
| `escaping_example_typable`         | `examples.v` | Figure 3b                     |
| `fixpoint_typable`                 | `examples.v` | Section 5.1 `fix`             |
| `nested_ref_type`                  | `examples.v` | Section 5.3 `escapeNestedRef` |
| `use_writable_as_readonly_typable` | `examples.v` | Section 5.3 `useImmutableRef` |

_Note_: Figure 2b is substantially similar to `typing_parallel_update`, in the
sense that the two blocks reference two distinct references, although there is
a transitively reachable path between the references via the store.  Besides,
Section 5.2 is also substantially similar to `typing_parallel_update`, except
that the mechanized example only has two distinct references, rather than four,
but it demonstrates the same safety property of performing parallel updates on
references with transitive reachability via the store.

### Proof Structure and File Organization

| File Name            | Description                                                                          |
| ----                 | ----                                                                                 |
| `boolean.v`          | Reflections on booleans, primarily used for qualifier freshness reasoning            |
| `examples_infra.v`   | Shared infrastructure for examples, including reusable definitions and helper lemmas |
| `f_sub_cycles_esc.v` | Formalization of the λ<:◦ calculus: typing rules and metatheory (type safety)        |
| `nats.v`             | Functional finite set implementation using unary natural numbers                     |
| `qualifiers_base.v`  | Core qualifier representation and basic operations/reflection lemmas                 |
| `qualifiers.v`       | Key lemmas and properties of qualifiers used in the main proofs                      |
| `vars.v`             | Variable representations and utility functions (e.g., free variables, renaming)      |
| `env.v`              | Typing environments and operations on environments (extension, domain, lookup)       |
| `examples.v`         | Fully-typed mechanized examples in paper                                             |
| `lang.v`             | Syntax definitions for the language (terms, types, qualifiers, reference constructs) |
| `qenv.v`             | Specialized qualifier environment used in typing and subtyping derivations           |
| `qualifiers_slow.v`  | Additional qualifier lemmas that are provable but computationally expensive          |
| `tactics.v`          | Custom tactics to streamline repetitive proof patterns                               |

## Explicit Axioms and Assumptions

No lemmas are admitted in the main proof. The system is proven end-to-end. 

In the examples, `typing_par` is an axiom that assumes a function
taking two closures capturing disjoint/separate resources, which is not an
essential contribution of this work, and thus is left unproven. It is used to
demonstrate safe parallel update, that two transitively reachable references
via the store are nevertheless considered disjoint/separate.

To audit axioms and admits, run the following commands below. You should
expect to see outputs similar to:

```
# To check for trusted axioms in compiled modules:
coqchk -R . Top *.vo
# To manually check for admitted proofs or axioms:
grep -rn 'Axiom\|Admitted' .
```

Upon running the second command, you should expect to see output similar to the
following:

```
./examples.v:476:Axiom typing_par : forall (Γ : tenv) (φ : qual) (Σ : senv),
```

### Deviations from the Paper

The type system formalization uses Locally Nameless Representation, where terms
are represented using named free variables and de Bruijn indices for bound
variables (cf. Aydemir et al., 2008).

Some typing rules have been split into multiple separate ones in mechanization
to aid analysis. Notable differences include: 

- `T-APP` in the paper is implemented by `t_app_var`, `t_app_empty`, and
  `t_app` in the mechanization, where the former two correspond to special
  cases of the rule where the premise of the highlighted condition in `T-APP`
  does not hold.

## Reusability Guide

The following components are reusable and extensible for future research:

- `lang.v`: This file contains core language definitions, suitable for
  extending with new constructs.
- `qualifiers_base.v`, `qualifiers_slow.v`, `qualifiers.v`: Modular and general
  qualifier reasoning. `qualifiers_slow.v` contains computationally expensive
  lemmas about the qualifiers that do not need to be recompiled when other
  components are modified.
- `f_sub_cycles_esc.v`: This file contains the type system framework and main
  lemmas leading to the soundness theorems.
- `examples.v`, `examples_infra.v`: These are mechanized case studies, and can
  be used as templates for developing new examples.

To create a new example, follow the structure of `fixpoint_typable` or
`escaping_example_typable`. 

To add a new typing rule, extend the inductive `has_type` in
`f_sub_cycles_esc.v` and adapt supporting lemmas accordingly.

### Limitations

- `f_sub_cycles_esc.v` has a large file size. The artifact can be made more
  reusable by breaking this file into logically separate components.
- Case studies in `examples.v` generally require long proofs. Implementing
  automation and tactics for common proof patterns can reduce the effort for
  proving examples.
- Compilation time is nontrivial. Improving the compilation time can involve
  serious investments in redesigning the underlying qualifier structure and
  efficient automation tactics.

We thank the reviewers for their time and care in evaluating this artifact. We
hope this formalization proves useful for understanding, validating, and
extending the system described in our paper.
