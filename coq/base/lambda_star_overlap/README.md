# Type Soundness of the Base+Overlap λ*-Calculus in Coq

## Variant

This variant of λ* changes the [base version](../lambda_star_base/) as follows:

* Functions and arguments are now allowed to _overlap_ at call sites, permitting more programs to be typed, e.g.,

```scala
val c1 = ... // Ref[Int] ^ {c1}
val c2 = ... // Ref[Int] ^ {c2}

// addRef : (Ref[Int] ^ {c1} => Int ^ {}) ^ {c1, c2}
def addRef(c3 : Ref[Int] ^ {c1}): Int =
    !c1 + !c2 + !c3

// permitted overlap is controlled by the qualifier in the function's domain:
addRef(c1) // ok now, was prohibited in base version
addRef(c2) // type error, c2 ∉ {c1} ⊓ {c1,c2}
```

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

* Just as the [base version](../lambda_star_base/), the proof of the substitution lemma 3.1 for function applications critically requires reasoning
about the interaction of substitutions with the intersection constraints in `t-app`. The difference here is that instead of complete disjointness, some
overlap is permitted, and the associated property (`Lemma subst1_preserves_separation`) generalizes as follows: let `df` be the function's qualifier,   `d1` be the argument's qualifier, and `θ` a substitution, then it should hold that `(θdf ⋒ θd1) = θ(df ⋒ d1)`. This property holds under the specific conditions in the substitution lemma.

* General overlap between functions and arguments destroys the previous "qualifiers in typing contexts consists of self-references and locations" invariant. Instead, reasoning about the substitution `θ` in the overlap requires that type assignments `Γ∣Σ ⊢ᵠ t : Tᵈ`  always ensure _saturation_ of the qualifier `d`, i.e.,
  `d` is transitively closed w.r.t. reachability in context `Γ` and `Σ` (cf. `Definition saturated`).

  * This invariant of typing derivations is captured by `Lemma has_type_saturated` and requires that all entries in `Γ` are `saturated` (cf. `Definition wf_tenv`).
    Ensuring the invariant requires strengthening `t_abs`, `t_app`, and `t_sub` with additional saturation constraints.

* The type safety proof in this version now requires narrowing on term typing (cf. `Lemma narrowing_gen` and `narrowing`), instead of widening on value typings used in the base version.

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


