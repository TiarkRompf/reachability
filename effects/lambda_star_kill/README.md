# The Base λ*-Calculus with Use and Kill effect in Coq

## Effect

One primary addition of this variant of the λ*-Calculus is a flow-sensitive effect system that models, in addition to reachability information, the effects induced by each construct.
The "use" effect associated with a term indicates that the evaluation of the term will induce a "use" side effect on the objects specified in the effect; 
similarly, the "kill" effect on a term indicates that evaluating the term will induce a destructive action (e.g. freeing a resource) on the specified objects. 
A safe program is one that never uses resources that has been previously killed.

The typing relation now has two extra components: the use effect and kill effect, each of which is represented using same structure used for qualifiers.

## Effect Operations and Predicates

| Name         | Notes                                                                                                                                                                                                   |
| ------       | ------                                                                                                                                                                                                  |
| `eff_seq_ok` | This predicate ensures the the composition of two effects are well-defined. Namely, the killed qualifiers in the first effect is disjoint from the used qualifiers in the second effect.                |

## Type Safety

- The `type_safety` lemma asserts that, given a well-typed term `t` (`has_type [] (ldom Σ) Σ t T d eu ek`), there are two possibilities:
    1. `t` is a value (`value t`), or 
    2. for some store `σ` that is well-formed with respect to `t`'s use effect `eu`, that is, `eu` does not use killed store locations in `σ` (`CtxOK [] (ldom Σ) Σ σ k` says that `k` is the killed locations in `σ`, and `eff_seq_ok ∅ k eu ek` says that `eu` is disjoint from `k`), we can step `t` to get a new term `t'` and a new store `σ'` (`step t σ t' σ'`), where typing is preserved (`preserve [] Σ t' T d eu ek σ' k`).
- The `preservation` lemma states that, the stepped term `t'` can be typed with the same type `T`, but permits a slightly different qualifier (`d ⊔ d'`) and effects (`eu' ⊔ eu''` and `ek' ⊔ ek''`). The new qualifier `d'` can possibly grow by one store location (`disjointq Σ Σ' d'`). Both components of the effect can shrink (e.g. `eu' ⊑ eu`), and possibly also include the new location (e.g. `disjointq Σ Σ' eu''`).

## File Index

### Main Files

* [`lambda_star.v`](lambda_star.v) -- The λ*-calculus: definitions and metatheory (type safety theorem and preservation of separation).
* [`examples.v`](examples.v) -- Mechanized examples demonstrating safety aspect of the system, namely, a well-typed term does not exhibit use-after-kill errors.

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

Compatibility tested with Coq `8.17.1`.
