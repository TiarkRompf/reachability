import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Lean4.Attrs

notation:max "‖" L "‖" => List.length L
notation:max "?[" b "]" s:66 => if b then s else ∅

namespace Reachability

-- identifier

inductive id: Type
| fresh
| bv (n: Nat)
| fv (n: Nat)
deriving DecidableEq

class Subst (α β: Type) where
  subst: id → β → α → α

export Subst (subst)

notation:max "[" x "↦" xs "]" q:66 =>  Subst.subst x xs q

notation "✦" => id.fresh
prefix:max "%" => id.fv
prefix:max "#" => id.bv

instance: Subst id id where
  subst x x' x0 := if x = x0 then x' else x0

def id.splice (i: id) (n δ: ℕ): id :=
  match i with
  | %x => if x < n then %x else %(x + δ)
  | x =>  x

attribute [simp] id.splice.eq_1 id.splice.eq_2

instance bvShift: HAdd id Nat id where
  hAdd x n := match x with
  | #x => #(x + n)
  | _ => x

-- qualifiers

abbrev ql := Finset id
abbrev qnat := Finset.range
attribute [sets] Finset.instHasSubset
attribute [default_instance] Finset.instSingleton

def qdom (fr: Bool) (bvs fvs: Nat): ql :=
  ?[fr] {✦} ∪ (qnat bvs).image (# ·) ∪ (qnat fvs).image (% ·)

@[sets]
def closed_ql (fr: Bool) (bvs fvs: Nat) (q: ql): Prop :=
  q ⊆ qdom fr bvs fvs

def closed_ql.fvs f (q: ql) := ∀⦃x⦄, %x ∈ q → x < f

instance: Subst ql ql where
  subst x xs q := q \ {x} ∪ ?[x ∈ q] xs

@[simp]
instance: Subst ql id where
  subst x x' q := [x ↦ {x'}] q

@[simp]
instance: Subst ql (id × ql) where
  subst x xs t := [x ↦ {xs.1} ∪ xs.2] t

def ql.splice (q: ql) (n δ: ℕ): ql :=
  q.image (id.splice · n δ)

attribute [simp← low] ql.splice.eq_1

instance bvsShift: HAdd ql ℕ ql where
  hAdd q n := q.image (· + n)

-- type definitions

inductive ty : Type where
| TTop  : ty
| TBool  : ty
| TRef   : ty → ql → ty
| TFun   : ty → ql → ty → ql → ty
| TVar   : id → ty
| TAll   : ty → ql → ty → ql → ty
deriving DecidableEq

def ty.unfoldable (t: ty) :=
  match t with
  | .TTop | .TBool | .TRef _ _ | .TFun _ _ _ _ | .TVar _ | .TAll _ _ _ _ => True

attribute [simp] ty.unfoldable.eq_1 ty.unfoldable.eq_2 ty.unfoldable.eq_3
attribute [simp] ty.unfoldable.eq_4 ty.unfoldable.eq_5 ty.unfoldable.eq_6

inductive occ_flag where
| none | no_covariant | no_contravariant | noneq
deriving DecidableEq

def occ_flag.flip (f: occ_flag): occ_flag :=
  match f with
  | .no_covariant => .no_contravariant
  | .no_contravariant => .no_covariant
  | _ => f

def occ_flag.tighten (f: occ_flag): occ_flag :=
  match f with
  | .noneq => .noneq
  | _ => .none

attribute [simp] occ_flag.flip.eq_1 occ_flag.flip.eq_2 occ_flag.flip.eq_3
attribute [simp] occ_flag.tighten.eq_1 occ_flag.tighten.eq_2

def occurs (f: occ_flag) (T: ty) (x: id): Prop :=
  match T with
  | .TRef T q =>
    occurs f.tighten T x ∧ x+1 ∉ q
  | .TFun T1 q1 T2 q2 =>
    occurs f.flip T1 (x+1) ∧ (f = .no_covariant ∨ x+1 ∉ q1) ∧
    occurs f T2 (x+2) ∧ (f = .no_contravariant ∨ x+2 ∉ q2)
  | .TVar a =>
    f = .noneq ∨ x ≠ a
  | .TAll T1 q1 T2 q2 =>
    occurs f.flip T1 (x+1) ∧ (f = .no_covariant ∨ x+1 ∉ q1) ∧
    occurs f T2 (x+2) ∧ (f = .no_contravariant ∨ x+2 ∉ q2)
  | .TTop | .TBool => True

def closed_ty (bv fv: Nat): ty → Prop
  | .TTop | .TBool => True
  | .TRef T q =>
    closed_ty bv fv T ∧
    closed_ql false (bv+1) fv q
  | .TFun T1 q1 T2 q2 =>
    closed_ty (bv+1) fv T1 ∧
    closed_ty (bv+2) fv T2 ∧
    closed_ql true (bv+1) fv q1 ∧
    closed_ql true (bv+2) fv q2 ∧
    (#0 ∈ q1 → ✦ ∈ q1) ∧
    occurs .no_covariant T1 #0 ∧
    occurs .no_contravariant T2 #0
  | .TVar x => x ∈ qdom false bv fv
  | .TAll T1 q1 T2 q2 =>
    closed_ty (bv+1) fv T1 ∧
    closed_ty (bv+2) fv T2 ∧
    closed_ql true (bv+1) fv q1 ∧
    closed_ql true (bv+2) fv q2 ∧
    (#0 ∈ q1 → ✦ ∈ q1) ∧
    occurs .no_covariant T1 #0 ∧
    occurs .no_contravariant T2 #0

@[simp]
def ty.open (x x': id) (t: ty): ty :=
  match t with
  | .TRef T q => .TRef (ty.open x x' T) ([x+1 ↦ x'+1] q)
  | .TFun T1 q1 T2 q2 =>
    .TFun (ty.open (x+1) (x'+1) T1) ([x+1 ↦ x'+1] q1)
          (ty.open (x+2) (x'+2) T2) ([x+2 ↦ x'+2] q2)
  | .TVar x0 => .TVar ([x ↦ x'] x0)
  | .TAll T1 q1 T2 q2 =>
    .TAll (ty.open (x+1) (x'+1) T1) ([x+1 ↦ x'+1] q1)
          (ty.open (x+2) (x'+2) T2) ([x+2 ↦ x'+2] q2)
  | .TTop | .TBool => t

instance: Subst ty id where
  subst := ty.open

@[simp low]
lemma ty.open_fold {t: ty} {x x': id}:
  t.open x x' = [x ↦ x'] t :=
by
  simp only [subst]

@[simp]
def ty.open_unfold {t: ty} {x x'} (_: t.unfoldable) :=
  Eq.symm (@ty.open_fold t x x')

@[simp]
def ty.TFun' (n: ℕ) T1 q1 T2 q2 :=
  ty.TFun T1 q1 ([%(n+1) ↦ #1] [%n ↦ #0] T2) ([%(n+1) ↦ #1] [%n ↦ #0] q2)

@[simp]
def ty.TAll' (n: ℕ) T1 q1 T2 q2 :=
  ty.TAll T1 q1 ([%(n+1) ↦ #1] [%n ↦ #0] T2) ([%(n+1) ↦ #1] [%n ↦ #0] q2)

@[simp]
def ty.subst' (x: id) (xt: ty) (xs: ql) (t: ty): ty :=
  match t with
  | .TRef T q => .TRef (ty.subst' x xt xs T) ([x+1 ↦ xs] q)
  | .TFun T1 q1 T2 q2 =>
    .TFun (ty.subst' (x+1) xt xs T1) ([x+1 ↦ xs] q1)
          (ty.subst' (x+2) xt xs T2) ([x+2 ↦ xs] q2)
  | .TAll T1 q1 T2 q2 =>
    .TAll (ty.subst' (x+1) xt xs T1) ([x+1 ↦ xs] q1)
          (ty.subst' (x+2) xt xs T2) ([x+2 ↦ xs] q2)
  | .TVar a => if x = a then xt else .TVar a
  | .TTop | .TBool => t

instance: Subst ty (ty × ql) where
  subst x x' t := ty.subst' x x'.1 x'.2 t

@[simp low]
lemma ty.subst_fold: ty.subst' x xt xs t = [x ↦ (xt, xs)] t := by
  simp only [instSubstTyProdQl]

@[simp]
def ty.subst_unfold {x t' q'} {t: ty} (_: t.unfoldable) :=
  Eq.symm (@ty.subst_fold x t' q' t)

@[simp]
instance: Subst ty ql where
  subst x xs t := [x ↦ (ty.TTop, xs)] t

@[simp]
instance: Subst ty (id × ql) where
  subst x xs t := [x ↦ (ty.TVar xs.1, {xs.1} ∪ xs.2)] t

def ty.splice (t: ty) (n δ: ℕ): ty :=
  match t with
  | .TRef T q => .TRef (T.splice n δ) (q.splice n δ)
  | .TFun T1 q1 T2 q2 =>
    .TFun (T1.splice n δ) (q1.splice n δ) (T2.splice n δ) (q2.splice n δ)
  | .TVar x => .TVar (x.splice n δ)
  | .TAll T1 q1 T2 q2 =>
    .TAll (T1.splice n δ) (q1.splice n δ) (T2.splice n δ) (q2.splice n δ)
  | _ => t

-- typing environment

inductive binding where | var | self | tvar
deriving DecidableEq

abbrev tenv := List (ty × ql × binding)

def telescope (env: tenv) := forall ⦃x T q1 bn⦄,
  env[x]? = some (T, q1, bn) → closed_ty 0 x T ∧ closed_ql true 0 x q1

def vars_trans (env: tenv): ql /- q -/ → ql :=
  -- match env with
  env.reverseRecOn
  -- | [] => q
    (fun q => q)
  -- | env ++ [(_, q')] => vars_trans env q ∪ ?[...] vars_trans env q'
    (fun x (_, q', _) f q => f (q ∪ ?[%‖x‖ ∈ q] q'))

abbrev gfset := Finset ℕ  -- growable selfrefs

def ctx_grow (G G': tenv) (growables: gfset): Prop :=
  ‖G‖ = ‖G'‖ ∧ (∀ i, G[i]? = G'[i]? ∨
    i ∈ growables ∧ ∃ T q q', q ⊆ q' ∧ closed_ql (✦ ∈ q) 0 i q' ∧
      G[i]? = some (T, q, .self) ∧ G'[i]? = some (T, q', .self))

-- term language

inductive tm: Type where
| ttrue
| tfalse
| tvar (x: ℕ)
| tref (t: tm)
| tget (t: tm)
| tput (tr tx: tm)
| tapp (tf tx: tm)
| tabs (t: tm)
| tabsa (T: ty) (q: ql) (t: tm)
| ttapp (tf: tm) (T: ty) (q: ql)
| ttabs (T: ty) (q: ql) (t: tm)
| tanno (t: tm) (T: ty) (q: ql)

@[match_pattern] def tm.tlet t1 t2 := (tm.tabs t2).tapp t1
@[match_pattern] def tm.tlet' t1 T q t2 := tm.tlet (tm.tanno t1 T q) t2

-- semantics

inductive vl: Type where
| vbool (b: Bool)
| vref (l: Nat)
| vabs (H: List vl) (t: tm)
| vtabs (H: List vl) (t: tm)

abbrev venv := List vl
abbrev stor := List vl

def teval (n: Nat) (M: stor) (env: venv) (t: tm): Except String (Nat × stor × vl) := do
  match n, t with
  | 0, _ => throw "timeout"
  | _ + 1, .ttrue => return (1, M, .vbool true)
  | _ + 1, .tfalse => return (1, M, .vbool false)
  | _ + 1, .tvar x =>
    match env[x]? with
    | some v => return (1, M, v)
    | _ => throw "error"
  | n + 1, .tref ex =>
    let (dx, M', vx) ← teval n M env ex
    return (1+dx, M'++[vx], .vref ‖M'‖)
  | n + 1, .tget ex =>
    let (dx, M', vx) ← teval n M env ex
    match vx with
    | .vref x =>
      match M'[x]? with
      | some v => return (1+dx, M', v)
      | _ => throw "error"
    | _ => throw "error"
  | n + 1, .tput er ex =>
    let (dr, M', vr) ← teval n M env er
    match vr with
    | .vref x =>
      let (dx, M'', vx) ← teval n M' env ex
      match M''[x]? with
      | some _ => return (1+dr+dx, M''.set x vx, .vbool true)
      | _ => throw "error"
    | _ => throw "error"
  | _ + 1, .tabs y => return (1, M, .vabs env y)
  | _ + 1, .tabsa _ _ y => return (1, M, .vabs env y)
  | n + 1, .tapp ef ex =>
    let (df, M', vf) ← teval n M env ef
    match vf with
    | .vabs env2 ey =>
      let (dx, M'', vx) ← teval n M' env ex
      let (dy, M''', ry) ← teval n M'' (env2 ++ [.vabs env2 ey, vx]) ey
      return (1+df+dx+dy, M''', ry)
    | _ => throw "error"
  | _ + 1, .ttabs _ _ y => return (1, M, .vtabs env y)
  | n + 1, .ttapp ef _ _ =>
    let (df, M', vf) ← teval n M env ef
    match vf with
    | vf@(.vtabs env2 ey) =>
      let (dy, M'', ry) ← teval n M' (env2 ++ [vf, .vbool false]) ey
      return (1+df+dy, M'', ry)
    | _ => throw "error"
  | n + 1, .tanno t _ _ =>
    let (d, M', vf) ← teval n M env t
    return (1+d, M', vf)
