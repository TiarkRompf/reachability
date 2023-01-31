# Reachability Types

## Mechanizations

### Overview

* [`base`](base) -- Coq mechanization of the $λ^*$-calculus [1] and its variations, gradually increasing in complexity.

* [`polymorphism`](polymorphism) -- Coq mechanization of the $λ^\diamond$-calculus [2] and its variations, featuring a refined reachability model that scales to parametric type polymorphism.


### Acknowledgements

The mechanizations based on sets reuse some libraries by the [UPenn PL Club](https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/index.html) that complement the FSet library shipping with [Coq](https://coq.inria.fr/distrib/current/stdlib/Coq.FSets.FSetInterface.html). We further
would like to thank [Boruch-Gruszecki et al.](https://arxiv.org/abs/2105.11896), whose artifact taught us how to set up the FSet library with extensional equality.

## Prototype Implementations

* Tiark Rompf's [prototype](http://tiarkrompf.github.io/notes/?/graph-ir/) for [1],
also demonstrating the use of reachability types for graph-based IRs for impure functional languages.

## Contributors

* [Oliver Bračevac](https://bracevac.org) (Mechanization lead)
* [Guannan Wei](https://continuation.passing.style)
* [Yuyan Bao](https://github.com/YuyanBao)
* [Siyuan He](https://sweetsinpackets.github.io)
* [Tiark Rompf](https://tiarkrompf.github.io)

## References

[1] **Reachability Types: Tracking Aliasing and Separation in Higher-order Functional Programs** (OOPSLA 2021)</br>
by Yuyan Bao, Guannan Wei, Oliver Bračevac, Luke Jiang, Qiyang He, and Tiark Rompf
([pdf](https://dl.acm.org/doi/10.1145/3485516)).

[2] **Polymorphic Reachability Types: Tracking Aliasing and Separation in Higher-order Generic Programs** (2023)</br>
by Guannan Wei, Oliver Bračevac, Siyuan He, Yuyan Bao, and Tiark Rompf
(to appear).
