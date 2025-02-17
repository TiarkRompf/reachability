# The $\lambda^{\diamond}$-Calculus: More Precise Reachability Polymorphism

## Variant

The $\lambda^{\diamond}$-calculus improves upon the qualifier presentation
over the original $\lambda^{\ast}$-calculus, in a way that unlocks
truly generic code paths (paper forthcoming).

### The Problem: The Track/Untrack Distinction is Not Parametric

To make reachability types scale to large code bases, we expect them
to support generic definitions in a way that is precise, natural, and unsurprising.
However, the original $\lambda^{\ast}$-calculus does not meet these criteria, because
of its distinction between untracked types (those qualified with `⊥`) and tracked
types (qualified with variable sets).

To see why the qualifier dichotomy is problematic, suppose we naively added type polymorphism
to $\lambda^*$. Here is the identity function:
```scala
def id[A](x : T^∅): T^{x} = x
```
which accepts any `T` argument, e.g.,
```scala
val y : Ref[Int]^{y}
val z : Ref[Int]^{z,a,b}
id(y)          // : Ref[Int]^{y}
id(z)          // : Ref[Int]^{z,a,b}
id(new Ref(0)) // : Ref[Int]^{}
```
In the case for _tracked_ arguments, dependent application ensures that result qualifiers correctly vary with
the respective argument qualifiers. However, once we pass _untracked_ arguments
```scala
val i = 0 : Int^⊥
id(i)          // : Int^{x}[x ↦ ⊥] = Int^{}
```
we observe that the arguments's qualifier is not preserved, but instead upcast to a tracking status.

Why can't we make the type more precise and just return `Int^⊥`? This can subvert the tracking of resources
in the type system. Consider:
```scala
val i = ...    // : T^⊥
def fakeid[A](x : T^∅): T^{x} = alloc()
// suppose "precise" instantation:
fakeid(i)      // : T^{x}[x ↦ ⊥] = T^⊥
```
The `fakeid` function returns a _fresh resource_ on each call, which should be tracked in the qualifier!
But `fakeid(i)` becomes _untracked_. To correctly track resources, $\lambda^*$ needs to
return a tracked result, preventing definitions that are fully generic in qualifiers.

### The Solution: A New Notion of Contextual Freshness

We eliminate the set vs. `⊥` distinction in favor of uniformly qualifying types with sets. Empty sets now indicate untracked types, e.g.,
```scala
1 // new type: Int^{}, old type: Int^⊥
```
and we introduce the _freshness marker_ `♦`, a special set element indicating that a qualifier contains statically unobservable variables/locations, e.g.,
```scala
new Ref(0) // new type: Ref[Int]^{♦}, old type: Ref[Int]^{}
```
where `♦` indicates that allocations produce "contextually fresh" reference cells.
An expression that is contextually fresh (i.e., `♦` occurs in its static qualifier) may grow at
run time, e.g.,
```scala
new Ref(0) // : Ref[Int]^{♦}
-->
ℓ          // : Ref[Int]^{ℓ}
```
where `ℓ` is a fresh store location.

This new model for qualifiers scales better to type polymorphism without loss of precision and
unpleasant surprises:
```scala
def id[A](x : T^{♦}): T^{x} = x
val y : Ref[Int]^{y}
val z : Ref[Int]^{z,a,b}
id(y)          // : Ref[Int]^{y}
id(z)          // : Ref[Int]^{z,a,b}
id(new Ref(0)) // : Ref[Int]^{♦}
id(0)          // : Int^{} <-- tracking status retained
```
Plus, we cannot even define the problematic `fakeid` function any longer:
```scala
def fakeid[A](x : T^{♦}): T^{x} = alloc() // error: alloc(): T^{♦} </: T^{x}
```
because `♦` is distinct from any variable `x`.

Occurrences of `♦` in function parameters indicate that the
function accepts "contextually fresh" arguments which have unobservable reachability information (such as `id` above). In contrast, parameters lacking the `♦` marker prescribe that arguments can have at most the
expected reachability information:
```scala
val y : T^{a,b}
val z : T^{a,b,c,d}
def id2[A](x : T^{a,b,c}): T^{x} = x
id2(y) // ok
id2(z) // error: {a,b,c,d} </: {a,b,c}
```

### Bonus: Nested References without an Effect System

The base $\lambda^*$-calculus restricts mutable references to untracked element types, ruling out
references to references unless a flow-sensitive effect system with move semantics is layered
on top. Our new reachability qualifier model already permits a form of nested references:

```scala
val x : Ref[Int^{}]^q
val y : Ref[Int^{}]^q
val v : Ref[Int^{}]^p
val z = new Ref(x) // : Ref[Ref[Int^{}]^q]^{}
z := y             // ok
z := v             // error if p ≠ q
```
References `Ref[T^q]` can store values with a fixed static qualifier `q` that is not contextually fresh (i.e., it lacks `♦` it cannot grow at run time).

### Limitations of this Variant

As before, we incrementally develop more complex calculi.

* Function applications can be dependent on the argument, but currently not on the self-qualifier of the function.

* This version still lacks type polymorphism.

## Mechanization Outline ([lambda_diamond.v](lambda_diamond.v))

| Paper | Mechanization |
|-------|---------------|
| Term typing `[Γ∣Σ]ᵠ ⊢ t : Tᵈ` | `Inductive has_type` |
| Subtyping `Γ∣Σ ⊢ T₁ᵈ¹ <: T₂ᵈ²` | `Inductive stp` |
| Qualifier subtyping `Γ∣Σ ⊢ q₁ <: q₂` | `Inductive qstp` |
| Substitution Lemmas | Terms: `substitution{1,2}`, Types : `substitution_stp{1,2}`, Qualifiers : `subst_qstp` |
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

* [`lambda_diamond.v`](lambda_diamond.v) -- The $\lambda^{\diamond}$-calculus: definitions and metatheory (type safety theorem and preservation of separation).
* [`examples.v`](examples.v) -- Mechanized tour of the calculus.

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

Compatibility tested with Coq `8.20.1`.
