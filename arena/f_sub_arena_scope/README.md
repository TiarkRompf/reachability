# $\{A\}_{<:}^♦$- Calculus : Scoped Resource Management

This document overviews the artifact for the paper "When Lifetimes Liberate: A Type System for Arenas with Higher-Order Reachability Tracking".

This artifact corresponds to the $\{A\}_{<:}^♦$- Calculus presented in Section 5.

## Introduction

This guide includes:
- Build instructions and dependencies (See "Build the Proof" below)
- Documentation mapping paper content to formal definitions (See
  [Paper-to-Artifact Correspondence](#paper-to-artifact-correspondence))
- [Static Typing](#static-typing)

## Build the Proof

Please refer to the main `README.md` for detailed guide.

### Requirements

- **Coq version**: 8.18.0
- **OCaml version**: 4.14.1

The compilation can take approximately **25** minutes. The file `qualifiers_slow.v` may take 12 minutes to compile.

To compile the development, run the following commands in the directory of `_CoqProject`:

First, generate or update the `CoqMakefile` from `_CoqProject`:

`coq_makefile -f _CoqProject -o CoqMakefile`

Then, to compile or check all proof scripts listed in `_CoqProject`:

`make -f CoqMakefile all`

## Paper-to-Artifact Correspondence

This directory stores the $\{A\}_{<:}^♦$-Calculus in the section 5 of the paper.

The following tables list correspondence between definitions/lemmas in the
mechanization and that in the paper.

### The Type System

| **Coq Definition** | **Coq File**         | **Paper**                         |
| ----               | ----                 | ----                              |
| `has_type`         | `rules.v`            | Typing (Fig. 14)                  |
| `stp`              | `rules.v`            | Subtyping (Fig. 8)*               |
| `qstp`             | `rules.v`            | Qualifier Subtyping (Fig. 8)*     |
| `step`             | `rules.v`            | Reduction                         |
| `local_locs`       | `rules.v`            | Local Locations (Fig. 12)         |
| `wf_step`          | `type_safety.v`      | Well-Stepped Terms (Fig. 12)      |
| `envUpdate`        | `type_safety.v`      | Environment Update (Fig. 13)      |
| `CtxOK`            | `type_safety.v`      | Well-Typed Stores (Fig. 13)       |
| `vtp`              | `vtp_subst.v`        | Value Typing                      |
| `has_type_static`  | `corollary.v`        | /                                 |

The subtyping and qualifier subtyping are the same as the $A_{<:}^♦$ calculus. 

### Metatheory

| **Coq Lemma**                        | **Coq File**         | **Lemma in Paper** |
| ----                                 | ----                 | ----               |
| `has_type_filter`                    | `weaken_narrow.v`    | Lemma C.1          |
| `vtp_has_type`                       | `vtp_subst.v`        | Lemma C.2          |
| `vtp_kill_retype`                    | `vtp_subst.v`        | Lemma C.3          |
| `vtp_non_fresh`                      | `vtp_subst.v`        | Lemma C.4          |
| `wf_step_value`                      | `type_safety.v`      | Lemma C.5          |
| `wf_step_preserve`                   | `type_safety.v`      | Lemma C.6          |
| `has_type_local_loc_sep`             | `weaken_narrow.v`    | Lemma C.7          |
| `substitution_gen`                   | `vtp_subst.v`        | Lemma C.8, C.9     |
| `progress`                           | `corollary.v`        | Lemma 5.1 / C.10   |
| `preservation`                       | `corollary.v`        | Lemma 5.2 / C.11   |
| `static_typing`                      | `corollary.v`        | /                  |

### Examples

| **Coq Example**                    | **Coq File** | **Example in Paper**          |
| ----                               | ----         | ----                          |
| `makeHandler_typable`              | `examples.v` | Section 6.1                   |
| `multi_hop_typable`                | `examples.v` | Section 6.3                   |




### Proof Structure and File Organization

| File Name            | Description                                                                          |
| ----                 | ----                                                                                 |
| `boolean.v`          | Reflections on booleans, primarily used for qualifier freshness reasoning            |
| `corollary.v`        | Preservation, Progress, and Static Typing Lemmas                                     |
| `env.v`              | Typing context, indexing lemmas                                                      |
| `examples_infra.v`   | Shared infrastructure for examples                                                   |
| `examples.v`         | Examples                                                                             |
| `killsep.v`          | Separation Wrapper and Lemmas                                                        |
| `lang.v`             | Program Syntax                                                                       |
| `lemmas.v`           | Auxiliary Lemmas                                                                     |
| `nats.v`             | Functional finite set implementation using unary natural numbers                     |
| `ops.v`              | Operations (open, substitute, splice, transitive closures)                           |
| `qenv.v`             | Store Typing Context and more context lemmas                                         |
| `qualifiers_base.v`  | Core qualifier representation and basic operations/reflection lemmas                 |
| `qualifiers_slow.v`  | Additional qualifier lemmas that are provable but computationally expensive          |
| `qualifiers.v`       | Key lemmas and properties of qualifiers used in the main proofs                      |
| `rules.v`            | Language definitions (typing, subtyping, etc)                                        |
| `tactic.v`           | Useful tactics for proof                                                             |
| `type_safety.v`      | The main safety proof, and the soundness definitions                                 |
| `vars.v`             | Variables and Locations                                                              |
| `vtp_subst.v`        | Value Typing, Substitution Lemmas                                                    |
| `weaken_narrow.v`    | Weakening, narrowing, and other typing lemmas                                        |

## Deliverables

All the proofs are checked without admits.


## Static Typing

We only list the dynamic typing in the paper (Fig. 13) and mark the contents only applicable in dynamic typing. 

The static typing are listed as `has_type_static` in `corollary.v`. 
We additionally prove Lemma `static_typing` to show that the dynamic typing degrades to static typing with an empty store.

The static typing system is a strict extension from the $A_{<:}^♦$ calculus.




We thank the reviewers for their time and care. 
We hope this artifact can help understanding and validating our system.