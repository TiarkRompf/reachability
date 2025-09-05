# Reachability Types

Reachability types are a new take on modeling lifetimes and sharing in high-level functional languages, showing how to integrate Rust-style reasoning capabilities with higher-order functions, polymorphic types, and similar high-level abstractions.

## Mechanization Overview

* [`base`](https://github.com/TiarkRompf/reachability/tree/main/base/) -- Coq mechanization of the $λ^*$-calculus [1] and its variations, gradually increasing in complexity.

* [`effects`](https://github.com/TiarkRompf/reachability/tree/main/effects/) -- Coq mechanization of the $λ_\varepsilon^*$-calculus [1] and its variations, gradually increasing in complexity.

* [`polymorphism`](https://github.com/TiarkRompf/reachability/tree/main/polymorphism/) -- Coq mechanization of the $λ^\diamond$-calculus [2] and its variations, featuring a refined reachability model that scales to parametric type polymorphism.

* [`log-rel-experiment`](./log-rel-experiment/) -- Experimenting semantic models of $λ^\diamond$, $λ_\varepsilon^\diamond$, and its variants [4,5].

* [`log-rel`](./log-rel/) -- Unary/Binary logical relations for proving semantic type soundness and termination of $λ^\diamond$, $λ_\varepsilon^\diamond$, as well as proofs of equational rules [4].

* [`log-rel-step-indexed`](https://github.com/TiarkRompf/reachability/tree/main/log-rel-step-indexed/) -- Step-indexed logical relations for $λ^\diamond$, $λ_\varepsilon^\diamond$ and its variants [4].

* [`checking`](https://github.com/TiarkRompf/reachability/tree/main/checking/) -- Bidirectional type system $\lambda^\diamond_R$ with decidable type checking/inference, including refined subtyping for self-references [5]

* [`cycles`](https://github.com/TiarkRompf/reachability/tree/main/cycles/) -- Bounded type-and-reachability polymorphism with cyclic references and natural numbers.

## Prototype Implementations

* Interactive [prototype](http://tiarkrompf.github.io/notes/?/graph-ir/) for [1],
also demonstrating the use of reachability types for graph-based IRs for impure functional languages [3].

* A standalone prototype language [Diamond](https://github.com/Kraks/diamond-lang) implements
polymorphic reachability types [2].

## Contributors

* [Oliver Bračevac](https://bracevac.org) (Initial mechanization lead 2021-2022)
* [Guannan Wei](https://continuation.passing.style) (Polymorphism lead 2023-2024)
* [Yuyan Bao](https://yuyanbao.github.io) (Logical relations lead 2023-2024)
* [Songlin Jia](https://songlinj.github.io) (Type checking lead 2024-2025)
* [Siyuan He](https://sweetsinpackets.github.io)
* [David Deng](https://github.com/PROgram52bc)
* [Yueyang Tang](https://github.com/Emanon42)
* [Tiark Rompf](https://tiarkrompf.github.io)

## References

[1] **Reachability Types: Tracking Aliasing and Separation in Higher-order Functional Programs** (OOPSLA 2021)</br>
Yuyan Bao, Guannan Wei, Oliver Bračevac, Luke Jiang, Qiyang He, Tiark Rompf
([pdf](https://www.cs.purdue.edu/homes/rompf/papers/bao-oopsla21.pdf)).

[2] **Polymorphic Reachability Types: Tracking Aliasing and Separation in Higher-order Generic Programs** (POPL 2024)</br>
Guannan Wei, Oliver Bračevac, Siyuan He, Yuyan Bao, Tiark Rompf
([pdf](https://www.cs.purdue.edu/homes/rompf/papers/wei-popl24.pdf)).

[3] **Graph IRs for Impure Higher-Order Languages: Making Aggressive Optimizations Affordable with Precise Effect Dependencies** (OOPSLA 2023)</br>
Oliver Bračevac, Guannan Wei, Luke Jiang, Supun Abeysinghe, Songlin Jia, Siyuan He, Yuyan Bao, Tiark Rompf
([pdf](https://www.cs.purdue.edu/homes/rompf/papers/bracevac-oopsla23.pdf)).

[4] **Modeling Reachability Types with Logical Relations: Semantic Type Soundness, Termination, and Equational Theory** (arXiv 2023)</br>
Yuyan Bao, Guannan Wei, Oliver Bračevac, Tiark Rompf
([pdf](https://arxiv.org/pdf/2309.05885.pdf)).

[5] **Escape with Your Self: Expressive Reachability Types with Sound and Decidable Bidirectional Type Checking** </br>
Songlin Jia, Guannan Wei, Siyuan He, Yueyang Tang, Yuyan Bao, Tiark Rompf
([pdf](https://arxiv.org/pdf/2404.08217.pdf)).
