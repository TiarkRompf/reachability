import Lean4.Checking

namespace Reachability.embedding

syntax "⊤": rttype
syntax "Unit": rttype
syntax "Nat": rttype
syntax ident: rttype
syntax "Ref[" rttype "~" rtqual "]": rttype
syntax "(" rttype "~" rtqual "⊗" rttype "~" rtqual ")": rttype
syntax "List[" rttype "]": rttype
syntax "(" (rtid)? "(" rtid ":" rttype "~" rtqual ")" "→" rttype "~" rtqual ")": rttype
syntax "(∀" (rtid)? "[" rtid "<:" rttype "~" rtqual "]." rttype "~" rtqual ")": rttype

macro_rules
| `([rttype| ⊤]) => `(fun (_: ℕ) =>
  ty.TTop)
| `([rttype| Unit]) => `(fun (_: ℕ) =>
  ty.TUnit)
| `([rttype| Nat]) => `(fun (_: ℕ) =>
  ty.TNat)
| `([rttype| $X:ident]) => `(fun (_: ℕ) =>
  ty.TVar $X)
| `([rttype| Ref[$T ~ $q]]) => `(fun (n: ℕ) =>
  ty.TRef1 ([rttype| $T] n) [rtqual| $q])
| `([rttype| ( $T1 ~ $q1 ⊗ $T2 ~ $q2 )]) => `(fun (n: ℕ) =>
  ty.TProd ([rttype| $T1] n) [rtqual| $q1] ([rttype| $T2] n) [rtqual| $q2])
| `([rttype| List[$T]]) => `(fun (n: ℕ) =>
  ty.TList ([rttype| $T] n))
| `([rttype| ($f($x : $T1 ~ $q1) → $T2 ~ $q2)]) => `(fun (n: ℕ) =>
  let [rtid| $f] := %n; ty.TFun' n
    ([%n ↦ #0] [rttype| $T1] (n+1))
    ([%n ↦ #0] [rtqual| $q1])
    (let [rtid| $x] := %(n+1); [rttype| $T2] (n+2))
    (let [rtid| $x] := %(n+1); [rtqual| $q2]))
| `([rttype| (∀$f[$x <: $T1 ~ $q1]. $T2 ~ $q2)]) => `(fun (n: ℕ) =>
  let [rtid| $f] := %n; ty.TAll' n
    ([%n ↦ #0] [rttype| $T1] (n+1))
    ([%n ↦ #0] [rtqual| $q1])
    (let [rtid| $x] := %(n+1); [rttype| $T2] (n+2))
    (let [rtid| $x] := %(n+1); [rtqual| $q2]))
| `([rttype| (($x : $T1 ~ $q1) → $T2 ~ $q2)]) => `([rttype| (_($x : $T1 ~ $q1) → $T2 ~ $q2)])
| `([rttype| (∀[$X <: $T1 ~ $q1]. $T2 ~ $q2)]) => `([rttype| (∀_[$X <: $T1 ~ $q1]. $T2 ~ $q2)])

syntax "unit": rtterm
syntax:max num: rtterm
syntax:60 rtterm:60 "+" rtterm:61: rtterm
syntax:70 rtterm:70 "*" rtterm:71: rtterm
syntax:max ident: rtterm
syntax "ref" rtterm: rtterm
syntax "!" rtterm: rtterm
syntax rtterm ":=" rtterm: rtterm
syntax rtterm rtterm:max : rtterm
syntax rtterm "[" rttype "~" rtqual "]" : rtterm
syntax ".(" rtterm "," rtterm ")": rtterm
syntax rtterm "._1": rtterm
syntax rtterm "._2": rtterm
syntax "nil": rtterm
syntax rtterm "::" rtterm: rtterm
syntax rtterm ".fold" rtterm "{" rtid "," rtid "=>" rtterm "}": rtterm
syntax "lam" (rtid)? "(" rtid ")" "." rtterm : rtterm
syntax "lam" (rtid)? "(" rtid ":" rttype "~" rtqual ")" "." rtterm : rtterm
syntax "lam" (rtid)? "[" rtid "]" "." rtterm : rtterm
syntax "lam" (rtid)? "[" rtid "<:" rttype "~" rtqual "]" "." rtterm : rtterm
syntax "(" rtterm ":" rttype "~" rtqual ")": rtterm
syntax "let" rtid "=" rtterm "in" rtterm: rtterm
syntax "let" "(" rtid ":" rttype "~" rtqual ")" "=" rtterm "in" rtterm: rtterm

macro_rules
| `([rtterm| unit]) => `(fun (_: ℕ) =>
  tm.tunit)
| `([rtterm| $n:num]) => `(fun (_: ℕ) =>
  tm.tnat $n)
| `([rtterm| $x + $y]) => `(fun (n: ℕ) =>
  tm.tadd ([rtterm| $x] n) ([rtterm| $y] n))
| `([rtterm| $x * $y]) => `(fun (n: ℕ) =>
  tm.tmul ([rtterm| $x] n) ([rtterm| $y] n))
| `([rtterm| $x:ident]) => `(fun (_: ℕ) =>
  tm.tvar! $x)
| `([rtterm| ref $t]) => `(fun (n: ℕ) =>
  tm.tref ([rtterm| $t] n))
| `([rtterm| ! $t]) => `(fun (n: ℕ) =>
  tm.tget ([rtterm| $t] n))
| `([rtterm| $t1 := $t2]) => `(fun (n: ℕ) =>
  tm.tput ([rtterm| $t1] n) ([rtterm| $t2] n))
| `([rtterm| .( $t1 , $t2 )]) => `(fun (n: ℕ) =>
  tm.tpair ([rtterm| $t1] n) ([rtterm| $t2] n))
| `([rtterm| $t ._1]) => `(fun (n: ℕ) =>
  tm.tfst ([rtterm| $t] n))
| `([rtterm| $t ._2]) => `(fun (n: ℕ) =>
  tm.tsnd ([rtterm| $t] n))
| `([rtterm| nil]) => `(fun (_: ℕ) =>
  tm.tnil)
| `([rtterm| $t1 :: $t2]) => `(fun (n: ℕ) =>
  tm.tcons ([rtterm| $t1] n) ([rtterm| $t2] n))
| `([rtterm| $tl .fold $t0 { $x , $acc => $t1 }]) => `(fun (n: ℕ) =>
  tm.tfold ([rtterm| $tl] n) ([rtterm| $t0] n)
    (let [rtid| $x] := %n; let [rtid| $acc] := %(n+1); [rtterm| $t1] (n+2)))
| `([rtterm| $t1 $t2]) => `(fun (n: ℕ) =>
  tm.tapp ([rtterm| $t1] n) ([rtterm| $t2] n))
| `([rtterm| $t1 [ $T ~ $q ]]) => `(fun (n: ℕ) =>
  tm.ttapp ([rtterm| $t1] n) ([rttype| $T] n) [rtqual| $q])
| `([rtterm| lam $f($x) . $body]) => `(fun (n: ℕ) =>
  let [rtid|$f] := %n; let [rtid|$x] := %(n+1);
  tm.tabs none ([rtterm| $body] (n+2)))
| `([rtterm| lam $f($x : $T ~ $q) . $body]) => `(fun (n: ℕ) =>
  let [rtid| $f] := %n; tm.tabs
    (([%n ↦ #0] [rttype| $T] (n+1)),
     ([%n ↦ #0] [rtqual| $q]))
    (let [rtid| $x] := %(n+1); [rtterm| $body] (n+2)))
| `([rtterm| lam $f[$x] . $body]) => `(fun (n: ℕ) =>
  let [rtid|$f] := %n; let [rtid|$x] := %(n+1);
  tm.ttabs none ([rtterm| $body] (n+2)))
| `([rtterm| lam $f[$X <: $T ~ $q] . $body]) => `(fun (n: ℕ) =>
  let [rtid| $f] := %n; tm.ttabs
    (([%n ↦ #0] [rttype| $T] (n+1)),
     ([%n ↦ #0] [rtqual| $q]))
    (let [rtid| $X] := %(n+1); [rtterm| $body] (n+2)))
| `([rtterm| ($t : $T ~ $q)]) => `(fun (n: ℕ) =>
  tm.tanno ([rtterm| $t] n) ([rttype| $T] n) [rtqual| $q])
| `([rtterm| let $x = $t1 in $t2]) => `([rtterm| (lam _($x) . $t2) $t1])
| `([rtterm| let ($x : $T ~ $q) = $t1 in $t2]) => `([rtterm| let $x = ($t1 : $T ~ $q) in $t2])
| `([rtterm| lam ($x) . $body]) => `([rtterm| lam _($x) . $body])
| `([rtterm| lam ($x : $T ~ $q) . $body]) => `([rtterm| lam _($x : $T ~ $q) . $body])
| `([rtterm| lam [$X <: $T ~ $q] . $body]) => `([rtterm| lam _[$X <: $T ~ $q] . $body])


section Church_Bool

def ty.CBool := [rttype|
  (∀[T <: ⊤ ~{✦, #0}]. ((x: T ~{✦, #0}) → ((y: T ~{✦, #0}) → T ~{x, y}) ~{x}) ~∅)
]

def ctrue := [rtterm|
  lam [T <: ⊤ ~{✦, #0}] . lam (x: T ~{✦, #0}) . lam (_: T ~{✦, #0}) . x
]

def cfalse := [rtterm|
  lam [T <: ⊤ ~{✦, #0}] . lam (_: T ~{✦, #0}) . lam (x: T ~{✦, #0}) . x
]

syntax "BOOL": rttype
macro_rules
| `([rttype| BOOL]) => `(ty.CBool)

def ccond := [rtterm|
  lam [T <: ⊤ ~{✦, #0}] . lam (b: BOOL ~{✦, #0}) . b [T ~{T}]
]

syntax "TRUE": rtterm
syntax "FALSE": rtterm
macro_rules
| `([rtterm| TRUE]) => `([rtterm| (⟪ctrue⟫: BOOL ~∅)])
| `([rtterm| FALSE]) => `([rtterm| (⟪cfalse⟫: BOOL ~∅)])

def andb := [rtterm|
  lam (x: BOOL ~∅) . lam (y: BOOL ~∅) . x [BOOL ~∅] y TRUE
]
def orb := [rtterm|
  lam (x: BOOL ~∅) . lam (y: BOOL ~∅) . x [BOOL ~∅] TRUE y
]
def negb := [rtterm|
  lam (x: BOOL ~∅) . x [BOOL ~∅] FALSE TRUE
]

def cbool_example := [rtterm|
  (let x = ref TRUE in x: Ref[BOOL ~∅] ~{✦})
]
#eval check_program cbool_example

end Church_Bool


section Church_Nat

-- (A → A) → A → A
def ty.TNat := [rttype|
  (∀[A <: ⊤ ~{✦, #0}].
    ((_: ((_: A ~{A}) → A ~{A}) ~ {#0, ✦}) →
    ((_: A ~{A}) → A ~{A}) ~{#0, #1}) ~{#0, #1})
]

syntax "NAT": rttype
macro_rules
| `([rttype| NAT]) => `(ty.TNat)

-- Λ[X]. λf.λx. x
def zero := [rtterm|
  lam [X <: ⊤ ~{#0, ✦}] .
    lam (_ : ((_: X ~{X}) → X ~{X}) ~{#0, ✦}) .
      lam (x : X ~{X}) .
        x
]
#eval check_program zero

def one := [rtterm|
  lam [X <: ⊤ ~{#0, ✦}] .
    lam (f : ((_: X ~{X}) → X ~{X}) ~{#0, ✦}) .
      lam (x : X ~{X}) .
        f x
]
#eval check_program one

-- λn. λf. λx. f (n f x)
def succ := [rtterm|
  lam (n : NAT ~{✦, #0}) .
    lam [X <: ⊤ ~{#0, ✦}] .
      lam (f : ((_: X ~{X}) → X ~{X}) ~{#0, ✦}) .
        lam (x : X ~{X}) .
          f (n [X ~{X}] f x)
]
#eval check_program succ

def nadd := [rtterm|
  lam (m: NAT ~∅) . lam (n: NAT ~∅) .
    m [NAT ~∅] ⟪succ⟫ n
]

def nmul := [rtterm|
  lam (m: NAT ~∅) . lam (n: NAT ~∅) . lam [X <: ⊤ ~{#0, ✦}] .
    lam (f : ((_: X ~{X}) → X ~{X}) ~{#0, ✦}) .
    n [X ~{X}] (m [X ~{X}] f)
]

def nrepeat := [rtterm|
  lam (n: NAT ~∅) . lam (f: ((_: NAT ~∅) → Unit ~∅) ~{✦, #0}) .
    n [NAT ~∅] (lam (i) . let _ = f i in ⟪succ⟫ i) ⟪zero⟫
]
#eval check_program nrepeat

def translate_num (n: ℕ) :=
  if n > 2 then
    [rtterm| let succ = ⟪succ⟫ in ⟪go [rtterm| succ] n⟫]
  else go succ n
where go (succ: ℕ → tm): ℕ → ℕ → tm
  | 0 => zero
  | 1 => one
  | n + 1 => [rtterm| ⟪succ⟫ ⟪translate_num.go succ n⟫]

syntax:max "." num: rtterm
syntax:60 rtterm:60 ".+" rtterm:61: rtterm
syntax:70 rtterm:70 ".*" rtterm:71: rtterm
syntax "FOR" rtid "<" rtterm "IN" rtterm: rtterm
macro_rules
| `([rtterm| .$n:num]) => `([rtterm| (⟪translate_num $n⟫ : NAT ~∅)])
| `([rtterm| $m .+ $n]) => `([rtterm| ⟪nadd⟫ $m $n])
| `([rtterm| $m .* $n]) => `([rtterm| (⟪nmul⟫ $m $n : NAT ~∅)])
| `([rtterm| FOR $x < $n IN $body]) => `([rtterm| ⟪nrepeat⟫ $n (lam ($x) . $body)])

def cnat_example := [rtterm|
  let x = ref (.1 .+ .1 .* .2) in
  let (_: Ref[NAT ~∅] ~{x}) = x in
  let _ =
    FOR i < .10 IN
      x := (!x) .+ i in
  ! x
]
#eval check_program cnat_example

-- ∀a. ((a → a) → a → a) → ((a → a) → a → a) → (a → a) → a → a
-- λm. λn. λf. λx. m (n f) x
def pow := [rtterm| --m^n
  lam (m : NAT ~∅) . lam (n : NAT ~∅) .
    -- (lam [X <: ⊤ ~{#0, ✦}] . n [((_: X ~{X}) → X ~{X}) ~{X}] (m [X ~{X}]): Nat ~∅)
    n [NAT ~∅] (lam (x) . m .* x) .1
]

#eval check_program pow

def pow_example := [rtterm|
  let n0 = .0 in
  let n1 = .1 in
  let succ = ⟪succ⟫ in
  let n2 = succ n1 in
  let n3 = succ n2 in
  let pow = ⟪pow⟫ in
  let n9 = pow n3 n2 in
  let (_: NAT ~∅) = n0 in
  let (_: NAT ~∅) = n1 in
  let (_: NAT ~∅) = n2 in
  let (_: NAT ~∅) = n3 in
  let (_: NAT ~∅) = n9 in
  n9
]

#eval check_program pow_example

end Church_Nat


section escapingpairs

def ty.TPair (X : ℕ → ty) (qx : ql) (Y : ℕ → ty) (qy : ql) := [rttype|
  (∀[R <: ⊤~{#0,✦}]. (
    (_: ((_: ⟪X⟫ ~ qx) → ((_: ⟪Y⟫ ~ qy) → R ~{R}) ~{#0, #1}) ~{✦, #0}) →
    R ~{R}
  )~{#0,#1})
]

syntax "PAIR[" rttype "~" rtqual "," rttype "~" rtqual "]": rttype
macro_rules
| `([rttype| PAIR[$X ~ $qx , $Y ~ $qy]]) => `(fun (n: ℕ) =>
  ty.TPair [rttype| $X] [rtqual| $qx] [rttype| $Y] [rtqual| $qy] n)

def mkpair := [rtterm|
  lam [A <: ⊤ ~{#0, ✦}] . lam [B <: ⊤ ~{#0, ✦}] .
  lam (a: A ~{A}) . lam (b: B ~{B}) .
  lam [C <: ⊤ ~{#0, ✦}] . lam (f: ((_: A ~{A}) → ((_: B ~{B}) → C ~{C}) ~{#0, #1}) ~{✦, #0}) .
  f a b
]

#eval check_program mkpair

def tfst := [rtterm|
  lam (x) . lam (_) . x
]

def tsnd := [rtterm|
  lam (_) . lam (y) . y
]

def tfst' := [rtterm|
  lam [X <: ⊤ ~{#0, ✦}] . lam [Y <: ⊤ ~{#0, ✦}] .
  lam (p: PAIR[X ~{X}, Y ~{Y}] ~{#0, ✦}) .
    p [X ~{X}] ⟪tfst⟫
]

#eval check_program tfst'

def tsnd' := [rtterm|
  lam [X <: ⊤ ~{#0, ✦}] . lam [Y <: ⊤ ~{#0, ✦}] .
  lam (p : PAIR[X ~{X}, Y ~{Y}] ~{#0, ✦}) .
    p [Y ~{Y}] ⟪tsnd⟫
]

#eval check_program tsnd'

def transparent_pair := [rtterm|
  let mkpair = ⟪mkpair⟫ in
  let x = ref TRUE in
  let y = ref FALSE in
  let p = mkpair [Ref[BOOL~∅] ~{x}] [Ref[BOOL~∅] ~{y}] x y in
  let (_ : Ref[BOOL~∅] ~{x}) = p [Ref[BOOL~∅] ~{x}] ⟪tfst⟫ in
  let (_ : Ref[BOOL~∅] ~{y}) = p [Ref[BOOL~∅] ~{y}] ⟪tsnd⟫ in
  let (_ : Ref[BOOL~∅] ~{x}) = ⟪tfst'⟫ [Ref[BOOL~∅] ~{x}] [Ref[BOOL~∅] ~{y}] p in
  let (_ : Ref[BOOL~∅] ~{y}) = ⟪tsnd'⟫ [Ref[BOOL~∅] ~{x}] [Ref[BOOL~∅] ~{y}] p in
  TRUE
]

#eval check_program transparent_pair
#eval bench_program "pair-trans" transparent_pair

def transparent_pair_native := [rtterm|
  let x = ref 1 in
  let y = ref 0 in
  let p = .(x, y) in
  let _ = p ._1 in
  let _ = p ._2 in
  let _ = p ._1 in
  let _ = p ._2 in
  1
]

#eval check_program transparent_pair_native
#eval bench_program "pair-trans" transparent_pair_native

def opaque_pair := [rtterm|
  let p = (
    let mkpair = ⟪mkpair⟫ in
    let x = ref TRUE in
    let y = ref FALSE in
    let p = mkpair [Ref[BOOL~∅] ~{x}] [Ref[BOOL~∅] ~{y}] x y in
    p) in
  let (_ : Ref[BOOL~∅] ~{p}) = p [Ref[BOOL~∅] ~{p}] ⟪tfst⟫ in
  let (_ : Ref[BOOL~∅] ~{p}) = p [Ref[BOOL~∅] ~{p}] ⟪tsnd⟫ in
  let (_ : Ref[BOOL~∅] ~{p}) = ⟪tfst'⟫ [Ref[BOOL~∅] ~{p}] [Ref[BOOL~∅] ~{p}] p in
  let (_ : Ref[BOOL~∅] ~{p}) = ⟪tsnd'⟫ [Ref[BOOL~∅] ~{p}] [Ref[BOOL~∅] ~{p}] p in
  TRUE
]

#eval check_program opaque_pair
#eval bench_program "pair-opaque" opaque_pair

def opaque_pair_native := [rtterm|
  let p = (
    let x = ref 1 in
    let y = ref 0 in
    let p = .(x, y) in
    p) in
  let _ = p ._1 in
  let _ = p ._2 in
  let _ = p ._1 in
  let _ = p ._2 in
  1
]

#eval check_program opaque_pair_native
#eval bench_program "pair-opaque" opaque_pair_native

end escapingpairs


section safepar

def par := [rtterm|
  lam (f : ((_: Unit~∅) → Unit~∅) ~{✦}) .
    lam (g : ((_: Unit~∅) → Unit~∅) ~{✦}) .
      (unit: Unit~{f, g}) -- simulate using incr, decr
]
#eval check_program par

def safepar_var := [rtterm|
  let par = ⟪par⟫ in
  let a = ref .0 in
  let b = ref .0 in
  let _ = a in
  par (lam (_) . a := (!a) .+ .1) (lam (_) . b := (!b) .+ .1)
]
#eval check_program safepar_var
#eval bench_program "par-var1" safepar_var

def safepar_var_native := [rtterm|
  let par = ⟪par⟫ in
  let a = ref 0 in
  let b = ref 0 in
  let _ = a in
  par (lam (_) . a := (!a) + 1) (lam (_) . b := (!b) + 1)
]
#eval check_program safepar_var_native
#eval bench_program "par-var1" safepar_var_native

def unsafepar_var := [rtterm|
  let par = ⟪par⟫ in
  let a = ref .0 in
  let _ = ref .0 in
  let c = a in
  par (lam (_) . a := (!a) .+ .1) (lam (_) . c := (!c) .+ .1)
]
#guard_msgs (drop error) in #eval check_program unsafepar_var
#eval bench_program "par-var2" unsafepar_var

def unsafepar_var_native := [rtterm|
  let par = ⟪par⟫ in
  let a = ref 0 in
  let _ = ref 0 in
  let c = a in
  par (lam (_) . a := (!a) + 1) (lam (_) . c := (!c) + 1)
]
#guard_msgs (drop error) in #eval check_program unsafepar_var_native
#eval bench_program "par-var2" unsafepar_var_native

def safepar_fun := [rtterm|
  let par = ⟪par⟫ in
  let inc = lam (x: Ref[NAT ~∅] ~{✦}) . x := (!x) .+ .1 in
  let a = ref .0 in
  let b = ref .0 in
  par (lam (_) . inc a) (lam (_) . inc b)
]
#eval check_program safepar_fun
#eval bench_program "par-fun1" safepar_fun

def safepar_fun_native := [rtterm|
  let par = ⟪par⟫ in
  let inc = lam (x: Ref[Nat ~∅] ~{✦}) . x := (!x) + 1 in
  let a = ref 0 in
  let b = ref 0 in
  par (lam (_) . inc a) (lam (_) . inc b)
]
#eval check_program safepar_fun_native
#eval bench_program "par-fun1" safepar_fun_native

def unsafepar_fun := [rtterm|
  let par = ⟪par⟫ in
  let inc = (let d = ref .0 in
    lam (_: Ref[NAT ~∅] ~{✦}) . d := (!d) .+ .1) in
  let a = ref .0 in
  let b = ref .0 in
  par (lam (_) . inc a) (lam (_) . inc b)
]
#guard_msgs (drop error) in #eval check_program unsafepar_fun
#eval bench_program "par-fun2" unsafepar_fun

def unsafepar_fun_native := [rtterm|
  let par = ⟪par⟫ in
  let inc = (let d = ref 0 in
    lam (_: Ref[Nat ~∅] ~{✦}) . d := (!d) + 1) in
  let a = ref 0 in
  let b = ref 0 in
  par (lam (_) . inc a) (lam (_) . inc b)
]
#guard_msgs (drop error) in #eval check_program unsafepar_fun_native
#eval bench_program "par-fun2" unsafepar_fun_native

def safepar_ref := [rtterm|
  let par = ⟪par⟫ in
  let a = ref .0 in
  let b = ref .0 in
  let a1 = ref a in
  let b1 = ref b in
  par (lam (_) . (!a1) := (!!a1) .+ .1) (lam (_) . (!b1) := (!!b1) .+ .1)
]
#eval check_program safepar_ref
#eval bench_program "par-ref1" safepar_ref

def safepar_ref_native := [rtterm|
  let par = ⟪par⟫ in
  let a = ref 0 in
  let b = ref 0 in
  let a1 = ref a in
  let b1 = ref b in
  par (lam (_) . (!a1) := (!!a1) + 1) (lam (_) . (!b1) := (!!b1) + 1)
]
#eval check_program safepar_ref_native
#eval bench_program "par-ref1" safepar_ref_native

def unsafepar_ref := [rtterm|
  let par = ⟪par⟫ in
  let a = ref .0 in
  let _ = ref .0 in
  let a1 = ref a in
  let b1 = ref a in
  par (lam (_) . (!a1) := (!!a1) .+ .1) (lam (_) . (!b1) := (!!b1) .+ .1)
]
#guard_msgs (drop error) in #eval check_program unsafepar_ref
#eval bench_program "par-ref2" unsafepar_ref

def unsafepar_ref_native := [rtterm|
  let par = ⟪par⟫ in
  let a = ref 0 in
  let _ = ref 0 in
  let a1 = ref a in
  let b1 = ref a in
  par (lam (_) . (!a1) := (!!a1) + 1) (lam (_) . (!b1) := (!!b1) + 1)
]
#guard_msgs (drop error) in #eval check_program unsafepar_ref_native
#eval bench_program "par-ref2" unsafepar_ref_native

def counter := [rtterm|
  lam (n : NAT ~∅) .
    let c = ref n in
    ⟪mkpair⟫ [((_: Unit~∅) → Unit~∅) ~{c}] [((_: Unit ~∅) → Unit~∅) ~{c}]
      (lam (_) . c := (!c) .+ .1) (lam (_) . c := (!c) .+ .1)
]
#eval check_program counter

def counter_native := [rtterm|
  lam (n : Nat ~∅) .
    let c = ref n in
      .(lam (_: Unit ~∅) . c := (!c) + 1, lam (_: Unit ~∅) . c := (!c) + 1)
]
#eval check_program counter

def sequential_counter_example := [rtterm|
  let ctr = ⟪counter⟫ .0 in
  let incr = ⟪tfst'⟫ [((_: Unit~∅) → Unit~∅) ~{ctr}] [((_: Unit~∅) → Unit~∅) ~{ctr}] ctr in
  let decr = ⟪tsnd'⟫ [((_: Unit~∅) → Unit~∅) ~{ctr}] [((_: Unit~∅) → Unit~∅) ~{ctr}] ctr in
  let (_: ((_: Unit~∅) → Unit~∅) ~{ctr}) = incr in
  let (_: ((_: Unit~∅) → Unit~∅) ~{ctr}) = decr in
  let (_: Unit~∅) = incr unit in  -- should apply on unit
  let (_: Unit~∅) = decr unit in
  ctr
]
#eval check_program sequential_counter_example
#eval bench_program "seq-ctr" sequential_counter_example

def sequential_counter_example_native := [rtterm|
  let ctr = ⟪counter_native⟫ 0 in
  let incr = ctr ._1 in
  let decr = ctr ._2 in
  let (_: ((_: Unit~∅) → Unit~∅) ~{ctr}) = incr in
  let (_: ((_: Unit~∅) → Unit~∅) ~{ctr}) = decr in
  let (_: Unit~∅) = incr unit in  -- should apply on unit
  let (_: Unit~∅) = decr unit in
  ctr
]
#eval check_program sequential_counter_example_native
#eval bench_program "seq-ctr" sequential_counter_example_native

def affirmative_par_example := [rtterm|
  let counter = ⟪counter⟫ in
  let ctr1 = counter .0 in
  let ctr2 = counter .0 in
  let incr1 = ⟪tfst'⟫ [((_: Unit~∅) → Unit~∅) ~{ctr1}] [((_: Unit~∅) → Unit~∅) ~{ctr1}] ctr1 in
  let decr2 = ⟪tsnd'⟫ [((_: Unit~∅) → Unit~∅) ~{ctr2}] [((_: Unit~∅) → Unit~∅) ~{ctr2}] ctr2 in
  -- let (_: ((_: ((_: Unit~∅) → Unit~∅)~{✦}) → Unit~∅) ~{incr}) = ⟪par⟫ incr in
  let _ = ⟪par⟫ incr1 decr2 in -- error here
  FALSE
]
#eval check_program affirmative_par_example
#eval bench_program "par-ctr1" affirmative_par_example

def affirmative_par_example_native := [rtterm|
  let counter = ⟪counter_native⟫ in
  let ctr1 = counter 0 in
  let ctr2 = counter 0 in
  let incr1 = ctr1 ._1 in
  let decr2 = ctr2 ._2 in
  let _ = ⟪par⟫ incr1 decr2 in -- error here
  0
]
#eval check_program affirmative_par_example_native
#eval bench_program "par-ctr1" affirmative_par_example_native

-- negative example, expect failure
def negative_par_example := [rtterm|
  let ctr = ⟪counter⟫ .0 in
  let incr = ⟪tfst'⟫ [((_: Unit~∅) → Unit~∅) ~{ctr}] [((_: Unit~∅) → Unit~∅) ~{ctr}] ctr in
  let decr = ⟪tsnd'⟫ [((_: Unit~∅) → Unit~∅) ~{ctr}] [((_: Unit~∅) → Unit~∅) ~{ctr}] ctr in
  -- let (_: ((_: ((_: Unit~∅) → Unit~∅)~{✦}) → Unit~∅) ~{incr}) = ⟪par⟫ incr in
  let _ = ⟪par⟫ incr decr in -- error here
  FALSE
]
#guard_msgs (drop error) in #eval check_program negative_par_example
#eval bench_program "par-ctr2" negative_par_example

def negative_par_example_native := [rtterm|
  let ctr = ⟪counter_native⟫ 0 in
  let incr = ctr ._1 in
  let decr = ctr ._2 in
  let _ = ⟪par⟫ incr decr in -- error here
  0
]
#guard_msgs (drop error) in #eval check_program negative_par_example_native
#eval bench_program "par-ctr2" negative_par_example_native

def parshared := [rtterm|
  lam (a : ⊤~{✦, #0}) .
  lam (f : ((_: Unit~∅) → Unit~∅) ~{✦,a}) .
    lam (g : ((_: Unit~∅) → Unit~∅) ~{✦,a}) .
      (unit: Unit~{f, g}) -- simulate using incr, decr
]
#eval check_program parshared

def parshared_example1 := [rtterm|
  let par = ⟪parshared⟫ in
  let a = ref .0 in
  let b = ref .0 in
  let c = ref .1 in
  par c (lam (_) . a := (!a) .+ (!c)) (lam (_) . b := (!b) .+ (!c))
]
#eval check_program parshared_example1
#eval bench_program "par-shr1" parshared_example1

def parshared_example1_native := [rtterm|
  let par = ⟪parshared⟫ in
  let a = ref 0 in
  let b = ref 0 in
  let c = ref 1 in
  par c (lam (_) . a := (!a) + (!c)) (lam (_) . b := (!b) + (!c))
]
#eval check_program parshared_example1_native
#eval bench_program "par-shr1" parshared_example1_native

def parshared_example2 := [rtterm|
  let par = ⟪parshared⟫ in
  let a = ref .0 in
  let b = ref .0 in
  let c = ref .1 in
  par c (lam (_) . a := (!a) .+ (!c)) (lam (_) . b := (!b) .+ (!a))
]
#guard_msgs (drop error) in #eval check_program parshared_example2
#eval bench_program "par-shr2" parshared_example2

def parshared_example2_native := [rtterm|
  let par = ⟪parshared⟫ in
  let a = ref 0 in
  let b = ref 0 in
  let c = ref 1 in
  par c (lam (_) . a := (!a) + (!c)) (lam (_) . b := (!b) + (!a))
]
#guard_msgs (drop error) in #eval check_program parshared_example2_native
#eval bench_program "par-shr2" parshared_example2_native

end safepar

section effectcapability

def try_type (CanThrow: id) := [rttype|
  (∀[A <: ⊤ ~{#0, ✦}].
    ((_: ((_: CanThrow ~{✦}) → A ~{A}) ~{#0, ✦}) →
    ((_: ((_: Unit ~∅) → A ~{A}) ~{#0, ✦}) → A ~{A}) ~{A}) ~{A})
]

def throw_type (CanThrow: id) := [rttype|
  (∀[A <: ⊤ ~{#0, ✦}]. ((_: CanThrow ~{#0, ✦}) → A ~{A}) ~{A})
]

def try1_safe := [rtterm|
  lam [CanThrow <: ⊤ ~{#0, ✦}] .
  lam (tryCatch: ⟪try_type CanThrow⟫ ~{✦}) .
  lam (throw_: ⟪throw_type CanThrow⟫ ~∅) .
  tryCatch [Unit ~∅]
    (lam (c) . throw_ [Unit ~∅] c)
    (lam (_) . unit)
]

#eval check_program try1_safe
-- #eval bench_program "try-safe" try1_safe

def unreach_type := [rttype|
  (∀[T <: ⊤ ~{✦, #0}]. T~{T})
]

def try2_escape := [rtterm|
  lam [CanThrow <: ⊤ ~{#0, ✦}] .
  lam (tryCatch: ⟪try_type CanThrow⟫ ~{✦}) .
  lam (throw_: ⟪throw_type CanThrow⟫ ~∅) .
  lam (unreachable: ⟪unreach_type⟫ ~{✦}) .
  let c = tryCatch [CanThrow ~{✦}]
      (lam (c) . c) -- (lam (_) . unreachable[CanThrow ~∅])
      (lam (_) . unreachable[CanThrow ~∅]) in
  throw_ [Unit ~∅] c
]

#guard_msgs (drop error) in #eval check_program try2_escape
-- #eval bench_program "try-esc" try2_escape

def mytry_type (CanThrow: id) := [rttype|
  ((_: ((_: CanThrow ~{✦, #0}) → Unit ~∅) ~{✦, #0}) → Unit ~∅)
]

def try3_escf := [rtterm|
  lam [CanThrow <: ⊤ ~{#0, ✦}] .
  lam (tryCatch: ⟪try_type CanThrow⟫ ~{✦}) .
  lam (throw_: ⟪throw_type CanThrow⟫ ~∅) .
  lam (unreachable: ⟪unreach_type⟫ ~{✦}) .
  let mytry = tryCatch [⟪mytry_type CanThrow⟫ ~{✦}]
      (lam (c) . lam (f) . f c) -- (lam (_) . unreachable[⟪mytry_type CanThrow⟫ ~∅])
      (lam (_) . unreachable[⟪mytry_type CanThrow⟫ ~∅]) in
  mytry (lam (c) . throw_ [Unit ~∅] c)
]

#guard_msgs (drop error) in #eval check_program try3_escf
-- #eval bench_program "try-fun" try3_escf

def try4_nocap := [rtterm|
  lam [CanThrow <: ⊤ ~{#0, ✦}] .
  lam (tryCatch: ⟪try_type CanThrow⟫ ~{✦}) .
  lam (throw_: ⟪throw_type CanThrow⟫ ~∅) .
  let nocap = lam [A <: ⊤ ~{#0, ✦}] .
    lam (cap: CanThrow ~{✦, #0}) .
    lam (body: ((_: Unit ~∅) → A ~{A}) ~{✦,A}) .
      let _ = cap in
      body unit in
  tryCatch [Unit ~∅]
    (lam (c) .
      let raiseError = lam (_: Unit ~∅) . throw_ [Unit ~∅] c in
      let _ = nocap [Unit ~∅] c
        (lam (_) .
          let _ = raiseError unit in  -- comment out this line to pass
          unit) in
      raiseError unit)
    (lam (_) . unit)
]

#guard_msgs (drop error) in #eval check_program try4_nocap
-- #eval bench_program "try-nocap" try4_nocap

def withFile_escape := [rtterm|
  lam [File <: Ref[NAT~∅]~{✦}] .
  lam (withF: (∀[T <: ⊤~{#0, ✦}]. ((_: NAT~∅) → ((_: ((_: File~{✦}) → T~{T})~{#0,✦}) → T~{T})~{T})~{T})~{#0, ✦}) .
  withF [File~{✦}] .0 (lam (f) . f)
]
#guard_msgs (drop error) in #eval check_program withFile_escape
#eval bench_program "withfile-esc" withFile_escape

def withFile_escape_native := [rtterm|
  lam [File <: Ref[Nat~∅]~{✦}] .
  lam (withF: (∀[T <: ⊤~{#0, ✦}]. ((_: Nat~∅) → ((_: ((_: File~{✦}) → T~{T})~{#0,✦}) → T~{T})~{T})~{T})~{#0, ✦}) .
  withF [File~{✦}] 0 (lam (f) . f)
]
#guard_msgs (drop error) in #eval check_program withFile_escape_native
#eval bench_program "withfile-esc" withFile_escape_native

def withFile_seq := [rtterm|
  -- let par = ⟪par⟫ in
  lam [File <: Ref[NAT~∅]~{✦}] .
  lam (withF: (∀[T <: ⊤~{#0, ✦}]. ((_: NAT~∅) → ((_: ((_: File~{✦}) → T~{T})~{#0,✦}) → T~{T})~{T})~{T})~{#0, ✦}) .
  -- let read = lam (f: File~{✦}) . !f in
  let write = lam (f: File~{✦}) . lam (c: NAT~∅) . f := c in
  withF [Unit~∅] .0 (lam (f) .
    let warn = lam (m: NAT~∅) . write f (m .+ .1) in
    let error = lam (m: NAT~∅) . write f (m .* .1) in
    let _ = warn .1 in
    let _ = error .1 in
    -- par (lam (_) . warn .1) (lam (_) . error .1)
    unit
  )
]
#eval check_program withFile_seq
#eval bench_program "withfile-seq" withFile_seq

def withFile_seq_native := [rtterm|
  -- let par = ⟪par⟫ in
  lam [File <: Ref[Nat~∅]~{✦}] .
  lam (withF: (∀[T <: ⊤~{#0, ✦}]. ((_: Nat~∅) → ((_: ((_: File~{✦}) → T~{T})~{#0,✦}) → T~{T})~{T})~{T})~{#0, ✦}) .
  -- let read = lam (f: File~{✦}) . !f in
  let write = lam (f: File~{✦}) . lam (c: Nat~∅) . f := c in
  withF [Unit~∅] 0 (lam (f) .
    let warn = lam (m: Nat~∅) . write f (m + 1) in
    let error = lam (m: Nat~∅) . write f (m * 1) in
    let _ = warn 1 in
    let _ = error 1 in
    -- par (lam (_) . warn .1) (lam (_) . error .1)
    unit
  )
]
#eval check_program withFile_seq_native
#eval bench_program "withfile-seq" withFile_seq_native

def withFile_par := [rtterm|
  let par = ⟪par⟫ in
  lam [File <: Ref[NAT~∅]~{✦}] .
  lam (withF: (∀[T <: ⊤~{#0, ✦}]. ((_: NAT~∅) → ((_: ((_: File~{✦}) → T~{T})~{#0,✦}) → T~{T})~{T})~{T})~{#0, ✦}) .
  -- let read = lam (f: File~{✦}) . !f in
  let write = lam (f: File~{✦}) . lam (c: NAT~∅) . f := c in
  withF [Unit~∅] .0 (lam (f) .
    let warn = lam (m: NAT~∅) . write f (m .+ .1) in
    let error = lam (m: NAT~∅) . write f (m .* .1) in
    let _ = warn .1 in
    let _ = error .1 in
    par (lam (_) . warn .1) (lam (_) . error .1)
    -- unit
  )
]
#guard_msgs (drop error) in #eval check_program withFile_par
#eval bench_program "withfile-par" withFile_par

def withFile_par_native := [rtterm|
  let par = ⟪par⟫ in
  lam [File <: Ref[Nat~∅]~{✦}] .
  lam (withF: (∀[T <: ⊤~{#0, ✦}]. ((_: Nat~∅) → ((_: ((_: File~{✦}) → T~{T})~{#0,✦}) → T~{T})~{T})~{T})~{#0, ✦}) .
  -- let read = lam (f: File~{✦}) . !f in
  let write = lam (f: File~{✦}) . lam (c: Nat~∅) . f := c in
  withF [Unit~∅] 0 (lam (f) .
    let warn = lam (m: Nat~∅) . write f (m + 1) in
    let error = lam (m: Nat~∅) . write f (m * 1) in
    let _ = warn 1 in
    let _ = error 1 in
    par (lam (_) . warn 1) (lam (_) . error 1)
    -- unit
  )
]
#guard_msgs (drop error) in #eval check_program withFile_par_native
#eval bench_program "withfile-par" withFile_par_native

end effectcapability


section lists

def tnil := [rtterm|
  lam [A <: ⊤ ~{#0, ✦}] .
    -- R can depend or not depend on A
    lam [R <: ⊤ ~{#0, ✦}] .
      lam (_: ((_: A ~{A}) → ((_: R ~{R}) → R ~{R}) ~{#0}) ~{✦, #0}) .
        lam (n : R ~{R}) . n
]

#eval check_program tnil

-- NOTE: The inner part is R^R -> R^R instead of (x:R^R) -> x^x
-- ∀R. (A → R → R) → R → R
def ty.TList (A : ℕ → ty) (aq : ql) := [rttype|
  (∀[R <: ⊤ ~{#0, ✦}]. (
    (_: ((_: ⟪A⟫ ~aq) → ((_: R ~{R}) → R ~{R}) ~{#0, #1}) ~{#0, ✦}) →
    ((_: R ~{R}) → R ~{R}) ~{#0, #1}
  ) ~{#0, #1})
]

def ty.UList (A : ℕ → ty) := [rttype|
  (∀l[R <: ⊤ ~{#0, ✦}]. (
    (_: ((_: ⟪A⟫ ~{l}) → ((_: R ~{R}) → R ~{R}) ~{#0, #1}) ~{#0, ✦}) →
    ((_: R ~{R}) → R ~{R}) ~{#0, #1}
  ) ~{#0, #1})
]

syntax "LIST[" rttype "~" rtqual "]": rttype
syntax "ULIST[" rttype "]": rttype
macro_rules
| `([rttype| LIST[$T ~ $q]]) => `(fun (n: ℕ) =>
  ty.TList [rttype| $T] [rtqual| $q] n)
| `([rttype| ULIST[$T]]) => `(fun (n: ℕ) =>
  ty.UList [rttype| $T] n)

def cons := [rtterm|
  lam [A <: ⊤ ~{#0, ✦}] .
    lam (hd : A ~{A}) .
      lam (tl : LIST[A ~{A}] ~{A}) .
        lam [R <: ⊤ ~{#0, ✦}] .
          lam (c : ((_: A ~{A}) → ((_: R ~{R}) → R ~{R}) ~{#0,#1}) ~{#0,✦}) .
            lam (n : R ~{R}) . c hd (tl [R ~{R}] c n)
]

#eval check_program cons

def sum := [rtterm|
  lam (lst: ULIST[Ref[NAT~∅]] ~{✦, #0}) .
    lst [NAT ~∅] (lam (r) . lam (a) . a .+ (!r)) .0
]
#eval check_program sum

def sum_native := [rtterm|
  lam (lst: List[Ref[Nat~∅]] ~{✦, #0}) .
    lst .fold 0 { r, a => a + !r }
]
#eval check_program sum_native

def cons_example := [rtterm|
  let CONS = ⟪cons⟫ in
  let sum = ⟪sum⟫ in
  let l = (
    let x = ref .0 in
    let y = ref .1 in
    let z = ref .2 in
    let l0 = ⟪tnil⟫ [Ref[NAT~∅] ~∅] in
    let _ = sum l0 in
    let l1 = CONS [Ref[NAT~∅] ~{x}] x l0 in
    let _ = sum l1 in
    let l2 = CONS [Ref[NAT~∅] ~{x,y}] y l1 in
    let _ = sum l2 in
    let l3 = CONS [Ref[NAT~∅] ~{x,y,z}] z l2 in
    let _ = sum l3 in
    l3) in
  let (_: LIST[Ref[NAT~∅] ~{l}] ~{l}) = l in
  sum l
]
#eval check_program cons_example
#eval bench_program "list-sum" cons_example

def cons_example_native := [rtterm|
  let sum = ⟪sum_native⟫ in
  let l = (
    let x = ref 0 in
    let y = ref 1 in
    let z = ref 2 in
    let (l0: List[Ref[Nat~∅]]~∅) = nil in
    let _ = sum l0 in
    let l1 = x :: nil in
    let _ = sum l1 in
    let l2 = y :: l1 in
    let _ = sum l2 in
    let l3 = z :: l2 in
    let _ = sum l3 in
    l3) in
  let _ = l in
  sum l
]
#eval check_program cons_example_native
#eval bench_program "list-sum" cons_example_native

-- isnil = λX. λl:List X. l [Bool] (λhd:X. λtl:Bool. false) true
def isnil := [rtterm|
  lam [X <: ⊤ ~{#0, ✦}] .
    lam (l: LIST[X ~{X}] ~{X}) .
      l [BOOL ~∅] (lam (_) . lam (_) . FALSE) TRUE
]
#eval check_program isnil

def isnil_native := [rtterm|
  lam [X <: ⊤ ~{#0, ✦}] .
    lam (l: List[X] ~{#0, ✦}) .
      l .fold 0 { _, _ => 1 }
]
#eval check_program isnil_native

/-
  map : (X → Y ) → List X → List Y
  Λa. Λb. λ(f : a → b). λ(xs : ∀r. (a → r → r) → r → r).
    xs (∀r. (b → r → r) → r → r)
      (λ(x : a) (acc : ∀r. (b → r → r) → r → r).cons b (f x) acc) (nil b)
-/

def map := [rtterm|
  lam [X <: ⊤ ~{#0, ✦}] . lam [Y <: ⊤ ~{#0, ✦}] .
    lam (f: ((_: X ~{X}) → Y ~{Y}) ~{#0,✦}) .
      lam (xs: LIST[X ~{X}] ~{#0,✦}) .
        -- construction part, LIST[Y] should alias f
        xs [LIST[Y ~{Y}] ~{Y}]
          (lam (x) . lam (acc) . ⟪cons⟫ [Y ~{Y}] (f x) acc)
          (⟪tnil⟫ [Y ~{Y}])
]
#eval check_program map

def map_native := [rtterm|
  lam [X <: ⊤ ~{#0, ✦}] . lam [Y <: ⊤ ~{#0, ✦}] .
    lam (f: ((_: X ~{X}) → Y ~{Y}) ~{#0,✦}) .
      lam (xs: List[X] ~{X}) .
        xs .fold (nil : List[Y] ~{Y}) { x, acc => (f x) :: acc }
]
#eval check_program map_native

def list := [rtterm|
  let NIL = ⟪tnil⟫ in
  let CONS = ⟪cons⟫ in
  let map = ⟪map⟫ in
  let isnil = ⟪isnil⟫ in
  let x = ref TRUE in
  let y = ref FALSE in
  let sl = CONS [Ref[BOOL~∅] ~{x}] x (NIL [Ref[BOOL~∅] ~{x}]) in
  let (_: LIST[Ref[BOOL~∅] ~{x}] ~{x}) = sl in
  let (_: LIST[Ref[BOOL~∅] ~{y}] ~{y}) =
    map [Ref[BOOL~∅] ~{x}] [Ref[BOOL~∅] ~{y}] (lam (_) . y) sl in
  let (_: BOOL~∅) = isnil [Ref[BOOL~∅] ~{x, y}] sl in
  sl
]
#eval check_program list
#eval bench_program "list-map" list

def list_native := [rtterm|
  let map = ⟪map_native⟫ in
  let isnil = ⟪isnil_native⟫ in
  let x = ref 1 in
  let y = ref 0 in
  let sl = x :: nil in
  let _ = sl in
  let _ = map [Ref[Nat~∅] ~{x}] [Ref[Nat~∅] ~{y}] (lam (_) . y) sl in
  let _ = isnil [Ref[Nat~∅] ~{x}] sl in
  sl
]
#eval check_program list_native
#eval bench_program "list-map" list_native

end lists


section seplists

def mnil := [rtterm|
  lam [A <: ⊤ ~{#0, ✦}] .
    -- R can dependent or not dependent on A
    lam [R <: ⊤ ~{✦}] .
      lam (_ : ((_: A ~{✦}) → ((_: R ~{R}) → R ~{R}) ~{#0,#1}) ~{✦}) .
        lam (n: R ~{R}) . n
]

-- NOTE: The inner part is R^R -> R^R instead of (x:R^R) -> x^x
-- ∀R. (A → R → R) → R → R
def ty.TList2 (A : ℕ → ty) := [rttype|
  (∀ [R <: ⊤ ~{✦}]. (
    (_: ((_: ⟪A⟫ ~{✦}) → ((_: R ~{R}) → R ~{R}) ~ {#0,#1}) ~{✦}) →
    ((_: R ~{R}) → R ~{R}) ~{#0, #1}
  ) ~{#0, #1})
]

syntax "MLIST[" rttype "]": rttype
macro_rules
| `([rttype| MLIST[$T]]) => `(fun (n: ℕ) =>
  ty.TList2 [rttype| $T] n)

def mcons := [rtterm|
  lam [A <: ⊤ ~{#0, ✦}] .
    lam (hd: A ~{✦}) . lam (tl: MLIST[A] ~{✦}) .
      (lam [R <: ⊤ ~{✦}] .
        lam (c : ((_: A ~{✦}) → ((_: R ~{R}) → R ~{R}) ~{#0,#1}) ~{✦}) .
          lam (n: R ~{R}) . c hd (tl [R ~{R}] c n)
      : MLIST[A] ~{hd,tl})  -- eager coercion to avoid upcasting adding extra variables
]

def miter := [rtterm|
  lam [X <: ⊤ ~{#0, ✦}] .
    lam (f : ((_: X ~{✦}) → Unit ~∅) ~∅) .
      lam (xs : MLIST[X] ~{#0,✦}) .
        -- construction part, LIST[Y] should alias f
        xs [Unit ~∅]
          (lam (x) . lam (_) . f x)
          unit
]

#eval check_program miter

def test_list2 := [rtterm|
  let mcons = ⟪mcons⟫ in
  let l0 = ⟪mnil⟫ [Ref[BOOL~∅] ~{✦}] in
  let (_: MLIST[Ref[BOOL~∅]] ~∅) = l0  in
  let x = ref TRUE in
  let y = ref FALSE in
  let l1 = mcons [Ref[BOOL~∅] ~{✦}] x l0 in
  let (_ : MLIST[Ref[BOOL~∅]] ~{l1}) = l1 in
  let l2 = mcons [Ref[BOOL~∅] ~{✦}] y l1 in
  let (_ : MLIST[Ref[BOOL~∅]] ~{l2}) = l2 in
  let _ = ⟪miter⟫ [Ref[BOOL~∅] ~{✦}] (lam (x) . x := !x) l2 in
  TRUE
]

#eval check_program test_list2
#eval bench_program "mlist-sep" test_list2

def test_list2_fail := [rtterm|
  let mcons = ⟪mcons⟫ in
  let l0 = ⟪mnil⟫ [Ref[BOOL~∅] ~{✦}] in
  let (_: MLIST[Ref[BOOL~∅]] ~∅) = l0  in
  let x = ref TRUE in
  let y = ref FALSE in
  let l1 = mcons [Ref[BOOL~∅] ~{✦}] x l0 in
  let (_ : MLIST[Ref[BOOL~∅]] ~{l1}) = l1 in
  let l2 = mcons [Ref[BOOL~∅] ~{✦}] y l1 in
  let _ = mcons [Ref[BOOL~∅] ~{✦}] x l2 in
  TRUE
]

#guard_msgs (drop error) in #eval check_program test_list2_fail
#eval bench_program "mlist-shr" test_list2_fail

end seplists


section benchnat

def create_bench (n: ℕ) (t: ℕ → tm) :=
  if n > 5 then
    [rtterm| let i = ⟪t⟫ .+ .10 in ⟪create_bench (n - 10) [rtterm| i]⟫]
  else
    [rtterm| ⟪t⟫ .+ ⟪translate_num n⟫]

def benchnat i :=
  bench_program s!"benchnat-{i}"
    -- (translate_num i)
    (create_bench i zero)
    -- (translate_num.go succ i)

#eval benchnat 10
#eval benchnat 20
#eval benchnat 30
#eval benchnat 40
#eval benchnat 50
#eval benchnat 60
#eval benchnat 70
#eval benchnat 80
#eval benchnat 90
#eval benchnat 100
#eval benchnat 110
#eval benchnat 120
#eval benchnat 130
#eval benchnat 140
#eval benchnat 150
#eval benchnat 160
#eval benchnat 170
#eval benchnat 180
#eval benchnat 190
#eval benchnat 200
#eval benchnat 210
#eval benchnat 220
#eval benchnat 230
#eval benchnat 240

end benchnat
