# When Lifetimes Liberate: A Type System for Arenas with Higher-Order Reachability Tracking

## Overview

This artifact is for the paper "When Lifetimes Liberate: A Type System for Arenas with Higher-Order Reachability Tracking".

We present two calculus: $A_{<:}^♦$ and $\{A\}_{<:}^♦$.

* [`f_sub_arena`](f_sub_arena) -- the $A_{<:}^♦$-calculus featuring invisible, non-lexical arenas, and coarse-grained reachability tracking. Present in Section 4.
* [`f_sub_arena_scope`](f_sub_arena_scope) -- the $\{A\}_{<:}^♦$-calculus is built on top of $A_{<:}^♦$, featuring scopes and sound deallocation reasoning. Present in Section 5.


The $\{A\}_{<:}^♦$-calculus strictly generalizes the $A_{<:}^♦$-calculus.

## Getting Started Guide

We provide either a docker containing the artifact and the build-from-scratch approach.

### Quick Start with Docker

#### 1. Fetch the latest docker image
Fetch by command (recommended):
```
  docker pull pinkelf/reachability-arena
```

Or download the attached `reachability-arena.tar` from [Zenodo](https://zenodo.org/records/18370232) and load by command:
```
  docker load -i reachability-arena.tar
```

#### 2. Run the docker image
Run image by command:
```
  docker run -it --rm pinkelf/reachability-arena
```

#### 3. Build the Coq proofs
The artifact have two folders containing $A_{<:}^♦$ and $\{A\}_{<:}^♦$ respectively, you can build separately.

Build system $A_{<:}^♦$:
```
  cd f_sub_arena
  make -f CoqMakefile all
```

Build system $\{A\}_{<:}^♦$:
```
  cd f_sub_arena_scope
  make -f CoqMakefile all
```

The build is successful if complete without error messages.


### Build from Scratch

The artifact has been tested on Rocq version `8.18.0` (and `8.17.1`) with opam switch `4.14.1`. Other versions are not guaranteed.

### Installation Guide

If you do not have OPAM installed, follow the instructions at
https://opam.ocaml.org/doc/Install.html. Then continue below with steps 1–3.

#### 1. Create a fresh switch with the required OCaml version
```
opam switch create reachability-coq 4.14.1
eval $(opam env)
```

#### 2. Install Coq and dependencies
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.18.0
```

Check that the installation succeeded:

```
coqc -v
# Should output: The Coq Proof Assistant, version 8.18.0
```

#### 3. Build the Proof

To compile the development, run the following commands in the sub-directory `f_sub_arena` or `f_sub_arena_scope`:

First, generate or update the `CoqMakefile` from `_CoqProject`:

`coq_makefile -f _CoqProject -o CoqMakefile`

Then, to compile or check all proof scripts listed in `_CoqProject`:

`make -f CoqMakefile all`


## Correspondence

For more details, please refer to the `README.md` inside sub-directory `f_sub_arena` or `f_sub_arena_scope`.

## Explicit Axioms and Assumptions

### Axioms

No lemmas are admitted in the main proof. The systems are proven end-to-end.

To audit axioms and admits, run the following commands below. You should
expect to see outputs similar to:
```
# To check for trusted axioms in compiled modules:
coqchk -R . Top *.vo
# To manually check for admitted proofs or axioms:
grep -rn 'Axiom\|Admitted' .
```

### Deviations from the Paper

The artifact of `f_sub_arena` additionally implements **natural number**, **boolean**, and **branch** in addition to the paper presentation. 
We additionally include the factorial example to illustrate the ability to implement cycles.
These developments are parallel to the main type system and considered trivial for soundness.

The type system formalization uses Locally Nameless Representation, where terms and types are represented using named free variables and de Bruijn indices for bound variables (cf. Aydemir et al., 2008).


## Reusability Guide

The following components are reusable and extensible for future research:

- `qualifiers_base.v`, `qualifiers_slow.v`, `qualifiers.v`: The implementation and reasoning of reachability qualifiers. Researchers can persistently reuse the implementation for development of similar qualifiers.
- Soundness proofs: The Rocq proofs are ad-hoc to the specific system by nature. Researchers can extend the typing system and focus only on reasoning the extensions.
- Examples `examples.v`: The mechanized examples for case studies. Researchers can directly reuse the example mechanization infrastructure `examples_infra.v`, and reuse `examples.v` as templates.


We thank the reviewers for their time and care. 
We hope this artifact can help understand and validate our system.