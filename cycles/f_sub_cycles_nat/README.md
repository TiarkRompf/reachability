# The $\mathsf{F}_{<:}^{\circ}$-Calculus: Bounded type-and-reachability polymorphism with cyclic references and natural numbers

## Compilation

To generate/update the `CoqMakefile` from `_CoqProject`:

`coq_makefile -f _CoqProject -o CoqMakefile`

Then, to compile/check all proof scripts listed in `_CoqProject`:

`make -f CoqMakefile all`

Compatibility tested with Coq `8.17.0`.

## Variant

$\lambda^{\diamond}$-calculus with support for cyclic references and natural numbers. It introduces new mechanisms to construct and reason about cyclic reference types, while still maintaining bounded type-and-qualifier polymorphism, akin to System $F_{<:}$.

Based on [fsub-trans](../f_sub_trans), this version inherit its explicit computational mechanism for transitive closure in the presence of **cyclic references**. This enables precise qualifier tracking, allowing references to store values capturing the reference itself, while preserving type soundness.

This version should be considered as the reference mechanization of the $\mathsf{F}_{<:}^{\circ}$-calculus, supporting both cyclic references and natural numbers.

## File Index

This version comes with a slightly altered utility structure, as described below:

### Main Files

- [`boolean.v`](boolean.v) — Reflection on booleans, mainly used to express qualifier freshness.
- [`env.v`](env.v) — Environments and operations.
- [`examples.v`](examples.v) — Example proofs demonstrating recursion enabled by cyclic references and numeric computations.
- [`f_sub_cycles_nat.v`](f_sub_cycles_nat.v) — The $\mathsf{F}_{<:}^{\circ}$-calculus: definitions and metatheory (type safety theorem, preservation of separation, and progress/preservation of parallel reductions).
- [`lang.v`](lang.v) — Term and type definitions.
- [`nats.v`](nats.v) — Functional set implementation for natural numbers.
- [`qenv.v`](qenv.v) — A generic environment supporting transitive closure lookup.
- [`qualifiers.v`](qualifiers.v) — Main lemmas for properties of qualifiers.
- [`qualifiers_base.v`](qualifiers_base.v) — Implementation of qualifier structure and basic reflection lemmas.
- [`qualifiers_slow.v`](qualifiers_slow.v) — Qualifier lemmas that take more time to compile.
- [`tactics.v`](tactics.v) — Miscellaneous tactics used in proofs.
- [`vars.v`](vars.v) — Variable representation and operations.
