# $A_{<:}^♦$- Calculus : Invisible, Non-Lexical, Coarse-Grained

This document overviews the artifact for the paper "When Lifetimes Liberate: A Type System for Arenas with Higher-Order Reachability Tracking".

This artifact corresponds to the $A_{<:}^♦$- Calculus presented in Section 4. 
The calculus is the strict **subset** of the calculus $\{A\}_{<:}^♦$, so we refer readers interested in sound deallocation reasoning to the other artifact.

We extend the calculus with **natural numbers and booleans** to encode the factorial example.

## Introduction

This guide includes:
- Build instructions and dependencies (See "Build the Proof" below)
- Documentation mapping paper content to formal definitions (See
  [Paper-to-Artifact Correspondence](#paper-to-artifact-correspondence))

## Build the Proof

Please refer to the main `README.md` for detailed guide.

### Requirements

- **Coq version**: 8.18.0
- **OCaml version**: 4.14.1

The compilation can take approximately **22** minutes. The file `qualifiers_slow.v` may take 12 minutes to compile.

To compile the development, run the following commands in the directory of `_CoqProject`:

First, generate or update the `CoqMakefile` from `_CoqProject`:

`coq_makefile -f _CoqProject -o CoqMakefile`

Then, to compile or check all proof scripts listed in `_CoqProject`:

`make -f CoqMakefile all`

## Paper-to-Artifact Correspondence

This directory stores the $A_{<:}^♦$-Calculus in the section 4 of the paper.

The following tables list correspondence between definitions/lemmas in the
mechanization and that in the paper.

### The Type System

| **Coq Definition** | **Coq File**         | **Paper**                         |
| ----               | ----                 | ----                              |
| `has_type`         | `f_sub_arena.v`      | Typing (Fig. 7)                   |
| `stp`              | `f_sub_arena.v`      | Subtyping (Fig. 8)                |
| `qstp`             | `f_sub_arena.v`      | Qualifier Subtyping (Fig. 8)      |
| `step`             | `f_sub_arena.v`      | Reduction (Fig. 9)                |
| `CtxOK`            | `f_sub_arena.v`      | Well-Typed Stores (Fig. 9)        |
| `vtp`              | `f_sub_arena.v`      | Value Typing                      |


### Metatheory

As the paper does not list intermediate lemmas for the calculus, we only list the main deliverables.

| **Coq Lemma**                        | **Coq File**         | **Lemma in Paper** |
| ----                                 | ----                 | ----               |
| `progress`                           | `f_sub_arena.v`      | Lemma 4.1          |
| `preservation`                       | `f_sub_arena.v`      | Lemma 4.2          |
| `type_safety`                        | `f_sub_arena.v`      | /                  |

### Examples

| **Coq Example**                    | **Coq File** | **Example in Paper**          |
| ----                               | ----         | ----                          |
| `loop_typable`                     | `examples.v` | Section 6.2                   |
| `fact_typable`                     | `examples.v` | /                             |




### Proof Structure and File Organization

| File Name            | Description                                                                          |
| ----                 | ----                                                                                 |
| `boolean.v`          | Reflections on booleans, primarily used for qualifier freshness reasoning            |
| `env.v`              | Typing context, indexing lemmas                                                      |
| `examples.v`         | Examples                                                                             |
| `lang.v`             | Program Syntax                                                                       |
| `nats.v`             | Functional finite set implementation using unary natural numbers                     |
| `qenv.v`             | Store Typing Context and more context lemmas                                         |
| `qualifiers_base.v`  | Core qualifier representation and basic operations/reflection lemmas                 |
| `qualifiers_slow.v`  | Additional qualifier lemmas that are provable but computationally expensive          |
| `qualifiers.v`       | Key lemmas and properties of qualifiers used in the main proofs                      |
| `tactic.v`           | Useful tactics for proof                                                             |
| `vars.v`             | Variables and Locations                                                              |
| `f_sub_arena.v`      | Typing, Subtyping, and Soundness Theorems                                            |

## Deliverables

All the proofs are checked without admits.





We thank the reviewers for their time and care. 
We hope this artifact can help understanding and validating our system.