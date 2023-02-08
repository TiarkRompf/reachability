# Type Soundness of the Base+Overlap+Effect $\lambda_\varepsilon^*$-Calculus in Coq

## Variant

This variant of $\lambda^*$ changes the [overlap version](../../base/lambda_star_overlap/) as follows:

* Add a simple effect system tracking effectful uses of operands in form of an additional
qualifier (set of variables and store locations) in the typing judgment.
* Add explicit `let` bindings for sequencing computations.
* `preservation_of_separation` still holds just as in the [overlap version](../../base/lambda_star_overlap/). We additionally show that disjoint effects also remain separate after stepping, just as qualifiers.
* A fully-fledged effect quantale framework as proposed in the OOPSLA'21 paper is out of scope of this mechanization.

## Mechanization Outline ([lambda_star.v](lambda_star.v))

| Paper | Mechanization |
|-------|---------------|
| Term typing `Γ∣Σ ⊢ t : Tᵈ { ε }` | `Inductive has_type` |
| Subtyping `Γ∣Σ ⊢ T₁ᵈ¹ { ε₁ } <: T₂ᵈ² { ε₂ }` | `Inductive stp` |
| Qualifier (& effect) subtyping `Γ∣Σ ⊢ q₁ <: q₂` | `Inductive qstp` |
| Lemma 3.1 | `Lemma substitution_gen`, `Lemma substitution` |
| Theorem 3.2 & 3.3 | `Theorem type_safety` |
| Corollary 3.4 | `Corollary preservation_of_separation` |

## Qualifier/Effect Operations (Section 3.2 & [qualifiers.v](qualifiers.v))

| Paper | Mechanization |
|-------|---------------|
| Inclusion `q₁ ⊑ q₂` | `subqual` with notation `_⊑_` |
| Union `q₁ ⊔ q₂` | `qlub` with notation `_⊔_` |
| `⊥`-aware intersection `q₁ ⊓ q₂` | `qqcap` with notation `_⋒_` |
| - | Standard intersection `qglb` with notation `_⊓_` |
| Cancelling plus `q₁ + q₂` | `qplus` with notation `_⊕_` |
| Cancelling union `q₁ ⊕ q₂` | `qqplus` with notation `_⋓_` |
| Sequential composition `ɛ₁ ▹ ɛ₂` | `qlub` with notation `_⊔_` |
| Join `ɛ₁ ⊔ ɛ₂` | `qlub` with notation `_⊔_` |

Due to the absence of the `⊥` qualifier in this version, it holds that `qlub = qqplus` and `qglb = qqcap`.

## File Index

### Main Files

* [`lambda_star.v`](lambda_star.v) -- The λ*-calculus: definitions and metatheory (type safety theorem and preservation of separation).

### Support Libraries
* [`qualifiers.v`](qualifiers.v) -- Reachability qualifiers in locally nameless style.
* [`env.v`](env.v) -- Environments and operations.
* [`vars.v`](vars.v) -- Variables.
* [`tactics.v`](tactics.v) -- Misc. tactics.
* [`setfacts.v`](setfacts.v) -- Properties of finite sets and auxiliary functions, e.g., splicing and unsplicing sets.
### Support Libraries (Third Party)
* [`NatSets.v`](NatSets.v) -- Finite sets of natural numbers with extensional equality.
* [`FSetDecide.v`](FSetDecide.v)
* [`FSetNotin.v`](FSetNotin.v)
* [`FiniteSets.v`](FiniteSets.v)
* [`ListFacts.v`](ListFacts.v)

## Compilation

To generate/update the `CoqMakefile` from `_CoqProject`:

`coq_makefile -f _CoqProject -o CoqMakefile`

Then, to compile/check all proof scripts listed in `_CoqProject`:

`make -f CoqMakefile all`

Compatibility tested with Coq `8.15.0`.


