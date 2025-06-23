# Artifact for "Complete the Cycle: Reachability Types with Expressive Cyclic References"

Conference: OOPSLA 2025 R2

## Overview

This artifact contains the mechanized formalization and proof for the paper
"Complete the Cycle: Reachability Types with Expressive Cyclic References". The
artifact includes:

- Complete mechanization of the type system and metatheory (`f_sub_cycles_esc.v`)
	- Mechanized formalization of the type system in Coq
	- Typing rules, soundness theorems, and key lemmas
	- Case studies illustrating the typing for the fixed-point combinator,
	  infinite loop, factorial function, fine-grained parallelization, escaping
	  references, and read-only references
- Complete mechanization of the examples shown in the paper (`examples.v`)
- Build instructions and dependencies (See "Building the Artifact" below)
- Documentation mapping paper content to formal definitions (See "Paper-to-Artifact Correspondence" below)
- Notes on proof, axioms, assumptions, and divergences (See "Notes" below)

## Building the Artifact

To compile the development, run the following commands in the root directory:

1. `coq_makefile -f _CoqProject -o Makefile`
2. `make`

### Requirements

- **Coq version**: 8.17.1  
- **OCaml version**: 4.13.1

Compilation takes approximately **65 minutes** on a high-performance server.

### Hardware Used

Compilation was tested on a machine with the following specifications:

- Architecture: x86\_64
- CPU: Intel(R) Xeon(R) Platinum 8168 @ 2.70GHz, 96 physical cores (192 threads)
- RAM: 768 GB
- OS: Linux, 64-bit

## Paper-to-Artifact Correspondence

This artifact accompanies the paper and corresponds to the system described in
**Section 4**, which is an extension based on the system presented in **Section
3**. It includes metatheory presented in **Section 3.5** and case studies
presented in **Section 5**.

The following tables list correspondence between definitions/lemmas in the
mechanization and that in the paper. All mechanized lemmas are located in
`f_sub_cycles_esc.v`, and all examples are located in `examples.v`

### The Type System

**Coq Definition** | **Coq File**                      | **Paper**                         |
-                  | -                                 | -                                 |
`has_type`         | `f_sub_cycles_esc.v` | Typing (Fig. 8, Fig. 11, Fig. 12) |
`stp`              | `f_sub_cycles_esc.v` | Subtyping (Fig. 9)                |
`q_trans_tenv`     | `f_sub_cycles_esc.v` | Transitive Lookup (Fig. 10)       |
`wf_senv`          | `f_sub_cycles_esc.v` | Well-Formed Stores (Fig. 11)      |

### Metatheory

**Coq Lemma**                        | **Coq File**                      | **Lemma in Paper** |
-                                    | -                                 | -                  |
`q_trans_tenv_subst1`                | `f_sub_cycles_esc.v` | Lemma 3.1          |
`substitution_gen`                   | `f_sub_cycles_esc.v` | Lemma 3.2          |
`progress`                           | `f_sub_cycles_esc.v` | Lemma 3.3          |
`preservation`                       | `f_sub_cycles_esc.v` | Lemma 3.4          |
`preservation_of_separation`         | `f_sub_cycles_esc.v` | Lemma 3.5          |
`parallel_progress_and_preservation` | `f_sub_cycles_esc.v` | Lemma 3.6          |

### Examples

**Coq Example**                    | **Coq File** | **Example in Paper**          |
-                                  | -            | -
`knot_typable`                     | `examples.v` | Figure 1b                     |
`typing_parallel_update`           | `examples.v` | Figure 2b                     |
`escaping_example_typable`         | `examples.v` | Figure 3b                     |
`fixpoint_typable`                 | `examples.v` | Section 5.1 `fix`             |
`typing_parallel_update`           | `examples.v` | Section 5.2                   |
`nested_ref_type`                  | `examples.v` | Section 5.3 `escapeNestedRef` |
`use_writable_as_readonly_typable` | `examples.v` | Section 5.3 `useImmutableRef` |

_Note_: Figure 2b is substantially similar to `typing_parallel_update`, in the
sense that the two blocks reference two distinct references, although there is
a transitively reachable path between the references via the store.
Besides, Section 5.2 is also substantially similar to `typing_parallel_update`, except
that the mechanized example only have two distinct references, rather than
four, but it demonstrates the same safety property of performing parallel
updates on references with transitive reachability via the store.

### Proof Structure and File Organization

| File Name                         | Description                                                                          |
| ----                              | ----                                                                                 |
| `boolean.v`                       | Reflections on booleans, primarily used for qualifier freshness reasoning            |
| `examples_infra.v`                | Shared infrastructure for examples, including reusable definitions and helper lemmas |
| `f_sub_cycles_esc.v` | Formalization of the λ<:◦ calculus: typing rules and metatheory (type safety)        |
| `nats.v`                          | Functional finite set implementation using unary natural numbers                     |
| `qualifiers_base.v`               | Core qualifier representation and basic operations/reflection lemmas                 |
| `qualifiers.v`                    | Key lemmas and properties of qualifiers used in the main proofs                      |
| `vars.v`                          | Variable representations and utility functions (e.g., free variables, renaming)      |
| `env.v`                           | Typing environments and operations on environments (extension, domain, lookup)       |
| `examples.v`                      | Fully-typed mechanized examples in paper                                             |
| `lang.v`                          | Syntax definitions for the language (terms, types, qualifiers, reference constructs) |
| `qenv.v`                          | Specialized qualifier environment used in typing and subtyping derivations           |
| `qualifiers_slow.v`               | Additional qualifier lemmas that are provable but computationally expensive          |
| `tactics.v`                       | Custom tactics to streamline repetitive proof patterns                               |

## Notes

No lemmas are admitted in the main proof. The system is proven end-to-end. 

In the examples, `typing_par` is an axiom that assumes a function
taking two closures capturing disjoint/separate resources, which is not an
essential contribution of this work, and thus is left unproven. It is used to
demonstrate safe parallel update, that two transitively reachable references
via the store are nevertheless considered disjoint/separate.

To audit axioms and admits, run the following commands below and you should
observe similar outputs:

```
> coqchk -R . Top *.vo             # Trust check
...
Modules were successfully checked
> grep -rn 'Axiom\|Admitted' .
./examples.v:476:Axiom typing_par : forall (Γ : tenv) (φ : qual) (Σ : senv),
```

## Deviations from the Paper

The type system formalization uses Locally Nameless Representation, where terms
are represented using named free variables and de Bruijn indices for bound
variables (cf. Aydemir et al., 2008).

Some typing rules have been split into multiple separate ones in mechanization
to aid analysis. Notable differences include: 

- `T-APP` in the paper is comprised of `t_app_var`, `t_app_empty`, and `t_app`
  in the mechanization, where the former two correspond to special cases of the
  rule where the premise of the highlighted condition in `T-APP` does not hold.
