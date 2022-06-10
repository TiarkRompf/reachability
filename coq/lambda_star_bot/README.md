# Type Soundness of the Base+Bot λ*-Calculus in Coq

## Variant

This variant adds a non-track qualifier `⊥` to [λ*-base](../lambda_star_base).

* Qualifier subtyping is ordinary set inclusion and lacks function self-qualifiers and recursive functions. In particular, escaping closures cannot be typed.

* The qualifiers in this version can be either the bottom or sets of variables. The bottom qualifier indicates untracked computations. This enables support for polymorphic references.

* Strict separation between functions and arguments, i.e., function and argument qualifiers may not overlap at call sites, and the observed aliasing between a function's implementation and its parameter is disjoint.

## Mechanization Outline ([lambda_star.v](lambda_star.v))

| Paper | Mechanization |
|-------|---------------|
| Term typing `Γ∣Σ ⊢ t : Tᵈ` | `Inductive has_type` |
| Subtyping `Γ∣Σ ⊢ T₁ᵈ¹ <: T₂ᵈ²` | `Inductive stp` |
| Qualifier subtyping `Γ∣Σ ⊢ q₁ <: q₂` | `Inductive qstp` |
| Lemma 3.1 | `Lemma substitution_gen{1,2}`, `Lemma substitution` |
| Theorem 3.2 & 3.3 | `Theorem type_safety` |
| Corollary 3.4 | `Corollary preservation_of_separation` |

## Qualifier Operations (Section 3.2 & [qualifiers.v](qualifiers.v))

| Paper | Mechanization |
|-------|---------------|
| Inclusion `q₁ ⊑ q₂` | `subqual` with notation `_⊑_` |
| Union `q₁ ⊔ q₂` | `qlub` with notation `_⊔_` |
| `⊥`-aware intersection `q₁ ⊓ q₂` | `qqcap` with notation `_⋒_` |
| - | Standard intersection `qglb` with notation `_⊓_` |
| Cancelling plus `q₁ + q₂` | `qplus` with notation `_⊕_` |
| Cancelling union `q₁ ⊕ q₂` | `qqplus` with notation `_⋓_` |

## File Index

### Main Files

* [`lambda_star.v`](lambda_star.v) -- The λ*-calculus: definitions and metatheory (invertiable value typing, type safety theorem and corollary).
* [`examples.v`](examples.v) -- Mechanized examples from the OOPSLA'21 paper, and limitations of this variant.

### Support Libraries
* [`examples_infra.v`](examples_infra.v) -- Auxiliary definitions and tactics used in [`examples.v`](examples.v).
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


