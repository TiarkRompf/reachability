# The $\mathsf{F}_{<:}^{\diamond}$-Calculus: Bounded Type-and-Qualifier Polymorphism

## Overview

### Mechanized Examples from the Paper

* [`examples.v`](examples.v): Basic examples from Section 2 and 5.
* [`examples_cell_opaque.v`](examples_cell_opaque.v) -- Example: Demonstrating opaque Church encodings for scope transfers on a single Cell type.
* [`examples_pairs.v`](examples_pairs.v): Data type examples from Section 2, including Figure 1 (counter, `Section OpaquePairEndToEnd`), transparent vs. opaque pairs, and conversion of the former into the latter.

### Tips to Get Started

* The mechanization uses locally nameless, where free variables are deBruijn *levels* (prefixed with `$`) and bound variables are deBruijn *indices* (prefixed with `#`). Numeric store locations are prefixed with `&`.
* Study the notations for qualifiers in [`qualifiers.v`](qualifiers.v).
* Study the type system and definitions at the top of the main proof file [`f_sub_diamond.v`](f_sub_diamond.v).

## Compilation

To generate/update the `CoqMakefile` from `_CoqProject`:

`coq_makefile -f _CoqProject -o CoqMakefile`

Then, to compile/check all proof scripts listed in `_CoqProject`:

`make -f CoqMakefile all`

Compatibility tested with Coq `8.20.1`.

Compilation takes approximately 6 minutes on an Apple M1 Pro CPU.

## Variant

This version extends the [base](lambda_diamond_base) $\lambda^{\diamond}$-calculus with bounded
type-and-qualifier polymorphism, akin to System $F_{<:}$.

### Limitations of this Variant

* Function/type applications can be fully dependent on the argument, but currently not on the self-qualifier of the function/universal type.
Their occurrence remains "shallow", i.e., they may appear in the immediate codomain qualifier, but not deeply in the codomain type.
However, this does not inhibit any of the paper's examples.

## Mechanization Outline ([f_sub_diamond.v](f_sub_diamond.v))

| Paper | Mechanization |
|-------|---------------|
| Term typing `[Γ∣Σ]ᵠ ⊢ t : Tᵈ` | `Inductive has_type` |
| Subtyping `Γ∣Σ ⊢ T₁ᵈ¹ <: T₂ᵈ²` | `Inductive stp` |
| Qualifier subtyping `Γ∣Σ ⊢ q₁ <: q₂` | `Inductive qstp` |
| Term Substitution Lemmas | Terms: `substitution{1,2}`, Types : `substitution_stp{1,2}`, Qualifiers : `subst_qstp` |
| Type-and Qualifier Substitution Lemmas | Terms: `substitution{1,2}_ty`, Types : `substitution_stp{1,2}_ty`, Qualifiers : `subst_ty_qstp` |
| Type Safety, Progress & Preservation | `Theorem type_safety` and derived corollaries `progress` and `preservation` |
| Preservation of Separation | `Corollary preservation_of_separation` |

## Qualifiers & Operations ([qualifiers.v](qualifiers.v))

| Paper | Mechanization |
|-------|---------------|
| Inclusion `q₁ ⊆ q₂` | `subqual` with notation `_⊑_` |
| Union `q₁ ∪ q₂` | `qlub` with notation `_⊔_` |
| Intersection `q₁ ∩ q₂` | `qglb` with notation `_⊓_` |
| Contextual freshness marker `{♦}` | Notation `{♦}` |
| Overlap (diamond intersection) `q₁ ∩♦ q₂` | `q₁ ⋒ q₂` used in contexts where the operands are `saturated` |
| Qualifier growth `q[p/♦]` | `qqplus` with notation `_⋓_`, i.e., `q[p/♦] ⇝ q ⋓ p` |

## Notes

* In contrast to the paper, the mechanization inlines
the syntactic category of "qualified types" `Q ::= Tᵈ`, i.e., it separates
the type and qualifier in signatures.

* Hybrid treatment of qualifiers/saturation: Variables are one-step (or lazy), store locations are fully transitive (or eager).

## File Index

### Main Files

* [`f_sub_diamond.v`](f_sub_diamond.v) -- The $\mathsf{F}_{<:}^{\diamond}$-calculus: definitions and metatheory (type safety theorem and preservation of separation).
* [`examples.v`](examples.v) -- Basic mechanized examples of the calculus from the paper.
* [`examples_cell_opaque.v`](examples_cell_opaque.v) -- Example: Demonstrating opaque Church encodings for scope transfers on a single Cell type.
* [`examples_pairs.v`](examples_pairs.v) -- Examples: Church encodings (transparent and opaque) of pairs and usage examples from the paper.

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
