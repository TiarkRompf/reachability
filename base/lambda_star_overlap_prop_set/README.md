# Type Soundness of the Base+Overlap λ*-Calculus in Coq (with Propositional Set Implementation)

## Propositional Set

A unique aspect of the propositional set is that it uses Coq's native data structure (`bool` and `Prop`) to implement the set data structure, with no external library dependencies.

The boolean version of a set is a function of type `nat -> bool`, where the returning boolean indicates whether the provided natural number is in the set.
The propositional version is a a function of type `nat -> Prop`, where the returning proposition is valid only if the natural number is in the set.

The boolean version can be useful when we need to perform operations based on membership criteria (e.g. using `if` conditions); on the other hand, the propositional version is useful for theorem proving, where one can easily write auxiliary tactics leveraging Coq's native propositional reasoning to facilitate powerful automation.

We provide reflection lemmas to convert between both the boolean and the propositional version, effectively showing the equality between them.

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

| Paper                                | Mechanization                                  |
| -------                              | ---------------                                |
| Term typing `Γ∣Σ ⊢ t : Tᵈ`           | `Inductive has_type`                           |
| Subtyping `Γ∣Σ ⊢ T₁ᵈ¹ <: T₂ᵈ²`       | `Inductive stp`                                |
| Qualifier subtyping `Γ∣Σ ⊢ q₁ <: q₂` | `Inductive qstp`                               |
| Lemma 3.1                            | `Lemma substitution_gen`, `Lemma substitution` |
| Theorem 3.2 & 3.3                    | `Theorem type_safety`                          |
| Corollary 3.4                        | `Corollary preservation_of_separation`         |

## Qualifier Operations (Section 3.2 & [qualifiers.v](qualifiers.v))

| Paper                       | Mechanization                                     |
| -------                     | ---------------                                   |
| Inclusion `q₁ ⊑ q₂`         | `subq` with notation `_⊑_`                        |
| Lifted Inclusion `q₁ ⊑↑ q₂` | `Subq (Q_lift _) (Q_lift _)` with notation `_⊑↑_` |
| Union `q₁ ⊔ q₂`             | `qor` with notation `_⊔_`                         |
| Intersection `q₁ ⊓ q₂`      | `qand` with notation `_⊓_`                        |
| Cancelling plus `q₁ + q₂`   | `qplus` with notation `_⊕_`                       |
| Cancelling union `q₁ ⊕ q₂`  | `qqplus` with notation `_⋓_`                      |

## File Index

### Main Files

* [`lambda_star.v`](lambda_star.v) -- The λ*-calculus: definitions and metatheory (type safety theorem and preservation of separation).
* [`examples.v`](examples.v) -- A selection of mechanized examples from the OOPSLA'21 paper.

### Support Libraries
* [`nats.v`](nats.v) -- Natural Number set implementation, contains both the boolean and the propositional version, with reflection lemmas to convert between them.
* [`vars.v`](vars.v) -- Variables.
* [`env.v`](env.v) -- Environments and operations.
* [`qualifiers.v`](qualifiers.v) -- Reachability qualifiers in locally nameless style.
* [`examples_infra.v`](examples_infra.v) -- Auxiliary definitions and tactics used in [`examples.v`](examples.v).
* [`tactics.v`](tactics.v) -- Misc. tactics.

## Notes

* Just as the [overlap version](../lambda_star_overlap/), the proof allows some overlap between the argument passed to `t-app` and the function's captured variables. The main difference is that this variant uses a propositional set representation. 

* This variant now eliminates the need for narrowing lemma on term typing.

## Compilation

To generate/update the `CoqMakefile` from `_CoqProject`:

`coq_makefile -f _CoqProject -o CoqMakefile`

Then, to compile/check all proof scripts listed in `_CoqProject`:

`make -f CoqMakefile all`

Compatibility tested with Coq `8.17.1`.
