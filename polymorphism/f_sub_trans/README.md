# The $\mathsf{F}_{<:}^{\diamond}$-Calculus: Bounded type-and-reachability polymorphism with explicit transitive closure

## Compilation

To generate/update the `CoqMakefile` from `_CoqProject`:

`coq_makefile -f _CoqProject -o CoqMakefile`

Then, to compile/check all proof scripts listed in `_CoqProject`:

`make -f CoqMakefile all`

Compatibility tested with Coq `8.17.0`.

Compilation takes approximately 6 minutes on an Apple M1 Pro CPU.

## Variant

This version extends the [base](lambda_diamond_base)
$\lambda^{\diamond}$-calculus with bounded type-and-qualifier polymorphism,
akin to System $F_{<:}$. As a variant of [fsub](f_sub_diamond), which uses
saturation to approximate transitive closure, this version makes transitive
closure more precise by providing an explicit mechanism to computationally
derive the transitive closure of a qualifier.

This version should be considered as the reference mechanization of the
$F_{<:}\diamond$-calculus from POPL '24.

## File Index

This version comes with a slightly altered utility structure, as described below:

### Main Files

* [`boolean.v`](boolean.v) -- Reflections on boolean, mainly used to express qualifier freshness
* [`lang.v`](lang.v) -- Term, type definition
* [`nats.v`](nats.v) -- Functional set implementation
* [`qenv.v`](qenv.v) -- A generic environment supporting transitive closure lookup
* [`qualifiers.v`](qualifiers.v) -- Main lemmas for properties on qualifiers
* [`qualifiers_base.v`](qualifiers_base.v) -- Qualifier structure implementation and basic reflection lemmas
* [`qualifiers_slow.v`](qualifiers_slow.v) -- Qualifier lemmas that take more time to compile
* [`env.v`](env.v) -- Environments and operations.
* [`vars.v`](vars.v) -- Variables.
* [`tactics.v`](tactics.v) -- Misc. tactics.
* [`f_sub_trans.v`](f_sub_trans.v) -- The $\mathsf{F}_{<:}^{\diamond}$-calculus: definitions and metatheory (type safety theorem and preservation of separation).
