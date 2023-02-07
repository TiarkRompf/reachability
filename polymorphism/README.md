# Polymorphic Reachability Types

## Overview

The $λ^\diamond$-calculus [1], a refined reachability model that scales to parametric type polymorphism. More versions are forthcoming.

* [`Base`](lambda_diamond_base) -- Base system introducing the new reachability model, lacking type polymorphism.
* [`Fsub`](f_sub_diamond) -- Bounded type-and-reachability polymorphism.

```mermaid
graph TD
    subgraph poly[Polymorphism]
      Base
      Fsub
    end
    Base-->Fsub
```

## References

[1] **Polymorphic Reachability Types: Tracking Aliasing and Separation in Higher-order Generic Programs** (2023)</br>
by Guannan Wei, Oliver Bračevac, Siyuan He, Yuyan Bao, and Tiark Rompf
(to appear).
