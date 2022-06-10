# Reachability Types
## Abstract
   Ownership type systems, based on the idea of enforcing unique access paths, have been primarily focused on objects and top-level classes. However, existing models do not as readily reflect the finer aspects of nested lexical scopes, capturing, or escaping closures in higher-order functional programming patterns, which are increasingly adopted even in mainstream object-oriented languages. We present a new type system, $\lambda^{\ast}$, which enables expressive ownership-style reasoning across higher-order functions. It tracks sharing and separation through reachability sets, and layers additional mechanisms for selectively enforcing uniqueness on top of it. Based on reachability sets, we extend the type system with an expressive flow-sensitive effect system, which enables flavors of move semantics and ownership transfer. In addition, we present several case studies and extensions, including applications to capabilities for algebraic effects, one-shot continuations, and safe parallelization.

## Paper: https://doi.org/10.1145/3485516

## Prototype: http://tiarkrompf.github.io/notes/?/graph-ir/

## Coq mechanization: [here](coq).
