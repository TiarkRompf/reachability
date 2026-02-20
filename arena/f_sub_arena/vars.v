Definition id := nat.
Definition loc := nat. (* store locations *)
Definition offset : Type := nat. (* store offset *)

(* locally nameless for binders in terms and types/qualifiers *)
Inductive var : Type :=
| varF : id -> var (* free var (deBruijn level) *)
| varB : id -> var (* locally-bound variable (deBruijn index) *)
.

Notation "# i" := (varB i) (at level 0, right associativity).
Notation "$ i" := (varF i) (at level 0, right associativity).
