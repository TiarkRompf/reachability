# Type Soundness of the Base λ*-Calculus in Coq

## Variant

This is the simplest version of λ* (Section 3 in the OOPSLA'21 paper), with the following limitations:

* Qualifier subtyping `Γ∣Σ ⊢ q₁ <: q₂` is identified with qualifier inclusion `q₁ ⊑ q₂`, and thus lacks function self-qualifiers and recursive functions. As a consequence, escaping closures cannot be typed.

* Lack of a bottom qualifier `⊥` for untracked computations: Reachability qualifiers are sets only, with the consequence that mutable references are monomorphic and restricted to values of a base type.

* Strict separation between functions and arguments, i.e., function and argument qualifiers may not overlap at call sites, and the observed aliasing between a function's implementation and its parameter is disjoint.

## Mechanization Outline ([lambda_star.v](lambda_star.v))

| Paper | Mechanization |
|-------|---------------|
| Term typing `Γ∣Σ ⊢ t : Tᵈ` | `Inductive has_type` |
| Subtyping `Γ∣Σ ⊢ T₁ᵈ¹ <: T₂ᵈ²` | `Inductive stp` |
| Qualifier subtyping `Γ∣Σ ⊢ q₁ <: q₂` | `Inductive qstp` |
| Lemma 3.1 | `Lemma substitution_gen`, `Lemma substitution` |
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

Due to the absence of the `⊥` qualifier in this version, it holds that `qlub = qqplus` and `qglb = qqcap`.

## Notes

* Syntactic type soundness (theorem 3.2 and 3.3 in the paper) is formulated as a combined type-safety theorem.
  The proof relies on invertible value typing and widening as used in the [alternative proof strategy](https://github.com/TiarkRompf/minidot/blob/57f6f31e21d61122d0f48b74fad2247074fa3cf8/oopsla16/dot_soundness_alt.v) for the dependent object types (DOT) calculus. The standard progress & preservation properties are implied as corollaries since reduction is deterministic. It would be equally possible to prove progress & preservation lemmas in the standard way, with type safety as corallary, but the chosen design facilitates some extensions, notably with function self qualifiers.

* Context filters are merged into the typing judgment instead of being an explicit operation, i.e., typing takes the form `Γ|Σ ⊢ᵠ t : Tᵈ`, where `φ ⊑ dom(Γ) ∪ dom(Σ)`, which indicates that the term is typed in the restricted context `Γᵠ := { x : Tᵈ ∈ Γ | d ⊑ φ }`.

* The proof of the substitution lemma 3.1 for function applications critically requires _preservation of separation under substitution_: for two disjoint qualifiers `(df ⋒ d1) = ∅` and a substitution `θ`, it should hold that `(θdf ⋒ θd1) = ∅`. This property holds under the specific conditions in the substitution lemma (cf. `Lemma subst1_preserves_separation`).

  * Having no overlap between functions and arguments leads to a useful invariant for the substitution lemma: Starting from a well-typed term `∅|Σ ⊢ᵠ t : Tᵈ` in an empty context, as the substition lemma proof traverses the typing derivation, the context will only ever be extended with assumptions of the form `x : T ^ (σ ⊕ x)` where `σ ⊑ dom(Σ)`. That is, each context entry aliases no free variables other than its own, plus some store locations. This context invariant is formalized by `Definition wf_tenv` and a precondition of `Lemma substitution_gen`, a suitably generalized substitution lemma.


  * Another critical piece is the invariant that `Γ|Σ ⊢ᵠ t : Tᵈ` implies `d ⊑ φ`, i.e., typing can only assign qualifiers that are visible under the given filter (cf. `Lemma has_type_filter`).

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


