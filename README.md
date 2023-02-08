# Reachability Types

Reachability types are a new take on modeling lifetimes and sharing in high-level functional languages, showing how to integrate Rust-style reasoning capabilities with higher-order functions, polymorphic types, and similar high-level abstractions.

## Mechanizations

### Overview

* [`base`](base) -- Coq mechanization of the $λ^*$-calculus [1] and its variations, gradually increasing in complexity.

* [`polymorphism`](polymorphism) -- Coq mechanization of the $λ^\diamond$-calculus [2] and its variations, featuring a refined reachability model that scales to parametric type polymorphism.

* [`lr`](lr) -- Logical relations for proving semantic type soundness of the $λ^*$-calculus [1,3].

### Acknowledgements

The mechanizations based on sets reuse some libraries by the [UPenn PL Club](https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/index.html) that complement the FSet library shipping with [Coq](https://coq.inria.fr/distrib/current/stdlib/Coq.FSets.FSetInterface.html). We set up the FSet library with extensional equality as inspired by [Boruch-Gruszecki et al.](https://arxiv.org/abs/2105.11896)'s artifact.

## Prototype Implementations

* Interactive [prototype](http://tiarkrompf.github.io/notes/?/graph-ir/) for [1],
also demonstrating the use of reachability types for graph-based IRs for impure functional languages [3].

## Contributors

* [Oliver Bračevac](https://bracevac.org) (Mechanization lead)
* [Guannan Wei](https://continuation.passing.style)
* [Yuyan Bao](https://github.com/YuyanBao)
* [Siyuan He](https://sweetsinpackets.github.io)
* [David Deng](https://github.com/PROgram52bc)
* [Tiark Rompf](https://tiarkrompf.github.io)

## References

[1] **Reachability Types: Tracking Aliasing and Separation in Higher-order Functional Programs** (OOPSLA 2021)</br>
by Yuyan Bao, Guannan Wei, Oliver Bračevac, Luke Jiang, Qiyang He, and Tiark Rompf
([pdf](https://dl.acm.org/doi/10.1145/3485516)).

[2] **Polymorphic Reachability Types: Tracking Aliasing and Separation in Higher-order Generic Programs** (2023)</br>
by Guannan Wei, Oliver Bračevac, Siyuan He, Yuyan Bao, and Tiark Rompf
(to appear).

[3] **Graph IRs for Impure Higher-Order Languages -- Making Aggressive Optimizations Affordable with Precise Effect Dependencies** (2023)</br>
by Oliver Bračevac, Guannan Wei, Luke Jiang, Supun Abeysinghe, Songlin Jia, Siyuan He, Yuyan Bao, and Tiark Rompf
(to appear).
