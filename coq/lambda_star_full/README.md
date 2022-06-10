# Type Soundness of the λ*-Calculus in Coq

## Variant

This is the complete variant of λ* (OOPSLA'21, Section 3) combining all
previous features: overlap, recursive
functions, function self qualifiers, and non-track bottom qualifiers.

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

## Notes

* It is not necessary to integrate an abstraction rule `Γ ⊢ qf <: f` for `Γ(f) = (T1^q1 => T2^q2)^qf+f` into qualifier subtyping, and it can remain simple set inclusion. Instead, we add a new _term typing_ rule
  ```
  Γ|Σ ⊢ e : T ^ qf + f
  Γ(f) = (T1^q1 => T2^q2)^qf+f
  ---------------------------- [t-self]
  Γ|Σ ⊢ e : T ^ f
  ```
  where a term's qualifier can be replaced by the function's self qualifier in the context, if it matches.

* Self qualifier abstraction is incompatible with the ["eager"](../lambda_star_overlap/) version always assigning transitively closed qualifiers, and necessarily requires the lazy system with the weaker invariant.

* The rule `[t-self]` is incompatible with the narrowing lemma. This is not a limitation, as function self references bound in the context never need to be narrowed in the type safety proof. Narrowing only applies to a function's arguments. To distinguish function arguments from their self references, the mechanization adds a boolean flag to typing assumptions (`true` for self references, `false` for arguments). `[t-self]` considers only variables `f` with the `true` flag, and only assumptions with a `false` flag are narrow-able.

## File Index

### Main Files

* [`lambda_star.v`](lambda_star.v) -- The λ*-calculus: definitions and metatheory (type safety theorem and preservation of separation).
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
