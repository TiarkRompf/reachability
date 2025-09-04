import Mathlib.Data.Finset.Sort
import Lean4.LangRules

namespace Reachability

-- monadic

instance: Repr IO.RealWorld := ⟨fun _ _ => "(42)"⟩

structure Stat where
  world: IO.RealWorld
  cnt_unify: ℕ
  cnt_growth: ℕ
  cnt_avoid: ℕ
  cnt_inferqf: ℕ
  cnt_sepcheck: ℕ
deriving Repr

abbrev M := EStateM IO.Error Stat

def qtrace (msg: String) (c: M α): M α :=
  c.adaptExcept (fun e => match e with
    | .userError e => .userError (msg ++ "\n" ++ e)
    | _ => e)

instance: MonadLift Option M where
  monadLift
  | some v => pure v
  | none => .error ↑"Option is none."

instance: MonadLift IO M where
  monadLift a s :=
    match a s.world with
    | .ok v w => .ok v { s with world := w }
    | .error e w => .error e { s with world := w }

def qassert (b: Prop) [Decidable b] (msg: String): M Unit :=
  if b then return () else throw ↑msg

instance: MonadEval M IO where
  monadEval a s :=
    match a.run ⟨s, 0, 0, 0, 0, 0⟩ with
    | .ok v s' => .ok v s'.world
    | .error e s' => .error e s'.world

-- printing

def id.format (x: id) (m: List String): String :=
  match x with
  | .fresh => "✦"
  | .bv n => m.getD n s!"#{n}"
  | .fv n => s!"%{n}"

instance: Repr id where
  reprPrec x _ := x.format []

instance: LE id where
  le
  | ✦, _ | #_, %_ => True
  | #n, #m => n ≤ m
  | %n, %m => m ≤ n
  | _, _ => False

instance: LinearOrder id where
  le_refl a := by
    cases a <;> simp [instLEId]
  le_trans a b c := by
    simp [instLEId]; intro h1 h2; split at h1 <;> try trivial
    all_goals split at h2 <;> try trivial
    all_goals rename_i heq; simp at heq; omega
  le_antisymm a b := by
    simp [instLEId]; intro h1 h2; split at h1 <;> try trivial
    all_goals split at h2 <;> try trivial
    all_goals simp at * <;> omega
  le_total a b := by
    simp [instLEId]; split; simp; simp; omega; omega
    split <;> simp at *; cases a <;> simp at * <;> cases b <;> simp at *
  decidableLE a b := by
    simp [instLEId]; split <;> infer_instance

def format_finset [LinearOrder α] (s: Finset α) (f: α → String): Std.Format :=
  if s ⊆ ∅ then "∅" else
  (Std.Format.joinSep ((s.sort (· ≤ ·)).map f) ",").bracket "{" "}"

instance [LinearOrder α] [Repr α]: Repr (Finset α) where
  reprPrec q _ := format_finset q reprStr

instance [Repr (Finset α)]: ToString (Finset α) := ⟨reprStr⟩

def ql.format (q: ql) (m: List String): Std.Format :=
  if q ⊆ ∅ then "ˣ" else "^" ++ format_finset q (id.format · m)

def ty.format (t: ty) (qs: Option Std.Format) (n: ℕ) (m: List String): Std.Format :=
  let m2 := s!"${n}"::s!"${n+1}"::m
  let m1 := s!"${n}"::m
  let m0 := "#0"::m
  match t with
  | .TFun T1 q1 T2 q2 =>
    s!"${n}{qs.getD ""}" ++ (s!"${n+1}: " ++ T1.format (q1.format m0) (n+1) m1).paren ++
    " ->" ++ (T2.format (q2.format m2) (n+2) m2).indentD
  | .TAll T1 q1 T2 q2 =>
    s!"∀${n}{qs.getD ""}" ++ (s!"${n+1} <: " ++ T1.format (q1.format m0) (n+1) m1).sbracket ++
    "." ++ (T2.format (q2.format m2) (n+2) m2).indentD
  | .TBool => "Bool" ++ qs.getD ""
  | .TTop => "⊤" ++ qs.getD ""
  | .TVar x => x.format m ++ qs.getD ""
  | .TRef T q => "Ref" ++ (T.format (q.format m0) n m).sbracket ++ qs.getD ""

def ty.format' := (ty.format · none · [])
instance: Repr ty := ⟨fun T _ => T.format' 0⟩

def tm.format (t: tm) (p n: Nat) (m: List String): Std.Format :=
  let m2 := s!"${n}"::s!"${n+1}"::m
  let m1 := s!"${n}"::m
  let m0 := "#0"::m
  match t, p with
  | .ttrue, _ => "true"
  | .tfalse, _ => "false"
  | .tvar x, _ => s!"%{x}"
  | .tref t, p =>
    let res := (t.format 1 n m).bracket "new Ref(" ")"
    if p > 1 then res.paren else res
  | .tget t, p =>
    let res := "! " ++ t.format 10 n m
    if p > 1 then res.paren else res
  | .tput t1 t2, p =>
    let res := t1.format 10 n m ++ " := " ++ t2.format 1 n m
    if p > 1 then res.paren else res
  | .tlet' t1 T1 q1 t2, p =>
    let prem := (T1.format (q1.format m) n m).bracket s!"val ${n+1}: " " = "
    let res := prem ++ (t1.format 1 n m).group ++ ";" ++ .line ++ t2.format 0 (n+2) m2
    if p > 0 then "{" ++ res.indentD ++ .line ++ "}" else res
  | .tlet t1 t2, p =>
    let prem := s!"val ${n+1} = "
    let res := prem ++ (t1.format 1 n m).group ++ ";" ++ .line ++ t2.format 0 (n+2) m2
    if p > 0 then "{" ++ res.indentD ++ .line ++ "}" else res
  | .tabs t, p =>
    let res := s!"λ${n}(${n+1})." ++ (t.format 1 (n+2) m2).indentD
    if p > 1 then res.paren else res
  | .tabsa T q t, p =>
    let typ := T.format (q.format m0) (n+1) m1
    let res := typ.bracket s!"λ${n}(${n+1}: " ")." ++ (t.format 1 (n+2) m2).indentD
    if p > 1 then res.paren else res
  | .ttabs T q t, p =>
    let typ := T.format (q.format m0) (n+1) m1
    let res := typ.bracket s!"Λ${n}[${n+1} <: " "]." ++ (t.format 1 (n+2) m2).indentD
    if p > 1 then res.paren else res
  | .ttapp t T q, _ => t.format 10 n m ++ (T.format (q.format m) n m).sbracket
  | .tapp t1 t2, _ => t1.format 10 n m ++ (t2.format 1 n m).paren
  | .tanno t T q, _ => (t.format 1 n m ++ " : " ++ T.format (q.format m) n m).paren

def tm.format' := (tm.format · 0 · [])
instance: Repr tm := ⟨(tm.format · · 0 [])⟩

-- decidability of predicates

instance: Decidable (closed_ql fr bv fv q) := by
  simp [closed_ql]; infer_instance

instance: Decidable (occurs f T x) := dec f T x
where
  dec f T x: Decidable (occurs f T x) := by
    cases T <;> simp!; infer_instance; infer_instance
    case TRef T q =>
      have := dec f.tighten T x; infer_instance
    case TFun T1 q1 T2 q2 =>
      have := dec f.flip T1 (x+1); have := dec f T2 (x+2)
      infer_instance
    infer_instance
    case TAll T1 q1 T2 q2 =>
      have := dec f.flip T1 (x+1); have := dec f T2 (x+2)
      infer_instance

instance: Decidable (closed_ty bv fv T) := dec bv fv T
where
  dec bv fv T: Decidable (closed_ty bv fv T) := by
    cases T <;> simp!; infer_instance; infer_instance
    case TRef T q => have := dec bv fv T; infer_instance
    case TFun T1 q1 T2 q2 =>
      have := dec (bv+1) fv T1
      have := dec (bv+2) fv T2; infer_instance
    infer_instance
    case TAll T1 q1 T2 q2 =>
      have := dec (bv+1) fv T1
      have := dec (bv+2) fv T2; infer_instance

-- qualifier checking

def qsatself (G: tenv) (q2: ql): ql :=
  let rec go x1 q2 :=
    match x1 with
    | x + 1 =>
      if let some (_, qx, bn) := G[x]? then
        if %x ∈ q2 then
          go x (q2 ∪ ?[bn = .self] (qx \ {✦}))
        else
          go x q2
      else ∅
    | 0 => q2
  go ‖G‖ q2

def qbounded (G: tenv) (gs: gfset) (q2: ql): ql :=
  let rec go x1 :=
    match x1 with
    | x + 1 =>
      if let some (_, qx, _) := G[x]? then
        let res := go x
        if x ∉ gs ∧ ✦ ∉ qx ∧ qx ⊆ res then res ∪ {%x} else res
      else ∅
    | 0 => q2
  go ‖G‖

def check_qtp0 G gs q1 q2 :=
  closed_ql true 0 ‖G‖ q1 ∧
  closed_ql true 0 ‖G‖ q2 ∧
  q1 ⊆ qbounded G gs (qsatself G q2)

instance: Decidable (check_qtp0 G gs q1 q2) := by
  simp [check_qtp0]; infer_instance

def qunify (G: tenv) (q1 q2: ql) (gs: gfset): M tenv := do
  let q2s := gs.filter (%· ∈ q2)
  let rec go x1 q1 := do
    match x1 with
    | x + 1 =>
      let (_, qx, _) ← G[x]?
      if %x ∉ q1 ∨ %x ∈ q2 then
        go x q1
      else match (q2s.filter (· > x)).min with
      | some f => do
        modify (fun s => { s with cnt_unify := s.cnt_unify + 1 })
        let G' ← go x (q1 \ {%x})
        let (Tf, qf, bn) ← G'[f]?
        qassert (bn = .self) "not a selfref"
        return G'.set f (Tf, qf ∪ {%x}, .self)
      | none => do
        qassert (✦ ∉ qx ∧ x ∉ gs) s!"Fail to unify %{x}."
        go x ([%x ↦ qx] q1)
    | 0 =>
      qassert (q1 ⊆ q2) s!"Fail to unify {q1}."
      return G
  go ‖G‖ q1

def check_qtp (G: tenv) (gs: gfset) (q1 q2: ql): M tenv :=
  qtrace s!"qtp: {q1} <: {q2}" do
    let q2' := qbounded G gs (qsatself G q2)
    qunify G q1 q2' gs  -- q1 ⊆ q2'

def check_app (G: tenv) (gs: gfset) (qf qx q1: ql): M (tenv × ql) :=
  qtrace s!"app: {qf} ⊢ {qx} <: {q1}" do
    if #0 ∈ q1 then
      return (G, ∅)
    else try
      let G' ← check_qtp G gs qx q1
      return (G', ∅)
    catch e =>
      if ✦ ∉ q1 then throw e
      modify (fun s => {s with cnt_sepcheck := s.cnt_sepcheck + 1})
      let qf_ := vars_trans G qf
      let qx_ := vars_trans G qx
      qassert (gs.filter (%· ∈ qf_ ∪ qx_) ⊆ ∅) "Growable in separation."
      let G' ← check_qtp G gs (qf_ ∩ qx_) q1
      return (G', (qf_ ∩ qx_) \ {✦})

-- subtype checking

def sub_size' (G: List ℕ) (T: ty): ℕ :=
  match T with
  | .TRef T _ =>
    1 + sub_size' G T
  | .TFun T1 _ T2 _ =>
    1 + sub_size' (G ++ [0]) [#0 ↦ %‖G‖] T1
      + sub_size' (G ++ [0, 0]) [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2
  | .TAll T1 _ T2 _ =>
    let n1 := sub_size' (G ++ [0]) [#0 ↦ %‖G‖] T1
    1 + sub_size' (G ++ [0, n1]) [#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2
  | .TVar (%x) =>
    1 + G.getD x 0
  | _ => 1
termination_by ty_size T
decreasing_by all_goals simp! <;> omega

def tenv.sub_sizes (G: tenv): List ℕ :=
  G.foldl (fun res (T, _, bn) => res ++ [if bn = .tvar then sub_size' res T else 0]) []

def sub_size (G: tenv) (T: ty): ℕ :=
  sub_size' G.sub_sizes T

def check_stp2 (fuel: ℕ) (G: tenv) (q0: ql) (T1 T2: ty) (gs: gfset): M (ql × tenv) :=
  qtrace s!"stp2: {T1.format' ‖G‖} <: {T2.format' ‖G‖}" do
    let (gr, G') ← go fuel G q0 T1 T2 gs
    modify (fun s => { s with cnt_growth := s.cnt_growth + if gr = ∅ then 0 else 1 })
    return (gr, G')
where go fuel G q0 T1 T2 gs := do
  match fuel, T1, T2 with
  | _ + 1, .TBool, .TBool => return (∅, G)
  | _ + 1, _, .TTop => return (∅, G)
  | fuel + 1, T1@(.TVar (%x)), T2 =>
    if T1 = T2 ∧ x < ‖G‖ then
      return (∅, G)
    else
      let (T1', _, bn) ← G[x]?
      qassert (bn = .tvar) "not a type var"
      check_stp2 fuel G q0 T1' T2 gs
  | fuel + 1, .TRef T1 q1, .TRef T2 q2 =>
    qassert (#0 ∉ q1 ∧ #0 ∉ q2) "Selfref in Refs"
    let ⟨gr1, G1⟩ ← check_stp2 fuel G {✦} T1 T2 gs
    let ⟨gr2, G2⟩ ← check_stp2 fuel G1 {✦} T2 T1 gs
    qassert (gr1 = ∅ ∧ gr2 = ∅) "Unexpected growth"
    let G3 ← check_qtp G2 gs q1 q2
    let G4 ← check_qtp G3 gs q2 q1
    return (∅, G4)
  | fuel + 1, .TFun T1a q1a T2a q2a, .TFun T1b q1b T2b q2b =>
    let gs' := gs ∪ {‖G‖}
    let ⟨g1, G1⟩ ← check_stp2 fuel (G ++ [(.TTop, q0, .self)]) {✦}
      ([#0 ↦ %‖G‖] T1b) ([#0 ↦ %‖G‖] T1a) gs'
    let G2 ← (do
      if {#0, ✦} ⊆ q1a then return G1
      else check_qtp G1 gs' ([#0 ↦ %‖G‖] q1b ∪ g1) ([#0 ↦ %‖G‖] q1a))
    let ⟨g2, G3⟩ ← check_stp2 fuel (G2 ++ [([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .var)]) {✦}
      ([#0 ↦ %‖G‖] [#1 ↦ (%(‖G‖+1), g1)] T2a) ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2b) gs'
    let G4 ← check_qtp G3 gs'
      ([#0 ↦ %‖G‖] [#1 ↦ (%(‖G‖+1), g1)] q2a ∪ g2) ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2b)
    let (_, g, _) ← G4[‖G‖]?
    return (g1 \ {%‖G‖} ∪ g2 \ {%‖G‖, %(‖G‖+1)} ∪ g \ q0, G4.take ‖G‖)
  | fuel + 1, .TAll T1a q1a T2a q2a, .TAll T1b q1b T2b q2b =>
    qassert (T1a = T1b) "Beyond kernel Fsub."
    let gs' := gs ∪ {‖G‖}
    let G1 := G ++ [(.TTop, q0, .self)]
    let G2 ← (do
      if {#0, ✦} ⊆ q1a then return G1
      else check_qtp G1 gs' ([#0 ↦ %‖G‖] q1b) ([#0 ↦ %‖G‖] q1a))
    let ⟨g2, G3⟩ ← check_stp2 fuel (G2 ++ [([#0 ↦ %‖G‖] T1b, [#0 ↦ %‖G‖] q1b, .tvar)]) {✦}
      ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2a) ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2b) gs'
    let G4 ← check_qtp G3 gs'
      ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2a ∪ g2) ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2b)
    let (_, g, _) ← G4[‖G‖]?
    return (g2 \ {%‖G‖, %(‖G‖+1)} ∪ g \ q0, G4.take ‖G‖)
  | _, _, _ =>
    throw ↑s!"Fail with fuel = {fuel}."

def unpack_self (T1: ty) (q0: ql): ty :=
  if ✦ ∈ q0 then T1
  else match T1 with
  | .TFun T1 q1 T2 q2 => .TFun ([#0 ↦ q0] T1) q1 ([#0 ↦ q0] T2) ([#0 ↦ q0] q2)
  | .TAll T1 q1 T2 q2 => .TAll ([#0 ↦ q0] T1) q1 ([#0 ↦ q0] T2) ([#0 ↦ q0] q2)
  | _ => T1

def check_stp (G: tenv) (q0: ql) (T1 T2: ty) (gs: gfset): M (ql × tenv) :=
  qtrace s!"stp: {T1.format' ‖G‖} <: {T2.format' ‖G‖}" do
  let T1' := unpack_self T1 q0
  check_stp2 (sub_size G T1' + sub_size G T2) G q0 T1' T2 gs

def unpack_argself (T1: ty) (qf: ql): M ty := do
  if ✦ ∉ qf then
    return [#0 ↦ qf] T1
  else
    qassert (occurs .none T1 #0) "Selfref in argtype cannot be removed."
    return T1

-- avoidance

def polsub (pol: Bool) (t: ty) (x: id) (y: id): M ty := do
  match t with
  | .TBool | .TTop => return t
  | .TVar x' =>
    qassert (x = y → x ≠ x') "cannot fully remove var"
    return t
  | .TRef T q =>
    let flag := if x = y then .none else .noneq
    qassert (occurs flag T x ∧ (x+1) ∉ q) "cannot fully remove var"
    return .TRef T q
  | .TFun T1 q1 T2 q2 =>
    let T1' ← polsub (!pol) T1 (x+1) (y+1)
    let q1' := [x+1 ↦ ?[!pol] {y+1}] q1
    let T2' ← polsub pol T2 (x+2) (y+2)
    let q2' := [x+2 ↦ ?[pol] {y+2}] q2
    return .TFun T1' q1' T2' q2'
  | .TAll T1 q1 T2 q2 =>
    let T1' ← polsub (!pol) T1 (x+1) (y+1)
    let q1' := [x+1 ↦ ?[!pol] {y+1}] q1
    let T2' ← polsub pol T2 (x+2) (y+2)
    let q2' := [x+2 ↦ ?[pol] {y+2}] q2
    return .TAll T1' q1' T2' q2'

def rm_contravariant (T2: ty) (n: id): M ty :=
  polsub true T2 n n

def avoid (t: ty) (x: id): M (ty × ql) := do
  if occurs .noneq t x then
    return (t, ∅)
  else
    modify (fun s => { s with cnt_avoid := s.cnt_avoid + 1 })
    match t with
    | .TFun T1 q1 T2 q2 =>
      let T1' ← polsub false T1 (x+1) #0
      let q1' := [x+1 ↦ (∅: ql)] q1
      let T2' ← polsub true T2 (x+2) #0
      let q2' := [x+2 ↦ #0] q2
      return (.TFun T1' q1' T2' q2', {x})
    | .TAll T1 q1 T2 q2 =>
      let T1' ← polsub false T1 (x+1) #0
      let q1' := [x+1 ↦ (∅: ql)] q1
      let T2' ← polsub true T2 (x+2) #0
      let q2' := [x+2 ↦ #0] q2
      return (.TAll T1' q1' T2' q2', {x})
    | _ => throw ↑"Unavoidable, probably nested refs."

def avoid_app (T2: ty) (qf qx: ql): M (ty × ql) := do
  let (T2a, gr2a) ← (do if ✦ ∉ qx then return (T2, ∅) else avoid T2 #1)
  let (T2b, gr2b) ← (do if ✦ ∉ qf then return (T2a, ∅) else avoid T2a #0)
  return (T2b, gr2a ∪ gr2b)

-- type variable exposure

def texposure (G: tenv) (t: ty): ty :=
  match t with
  | .TVar (%x) =>
    match h: G[x]? with
    | some (t', _, .tvar) =>
      have := (List.getElem?_eq_some.1 h).1
      texposure (G.take x) t'
    |_ => t
  | _ => t
termination_by ‖G‖

-- bidirectional typing

mutual

def tinfer (G: tenv) (gs: gfset) (t: tm): M (tenv × ql × ty × ql) := do
  match t with
  | .ttrue | .tfalse =>
    return (G, ∅, .TBool, ∅)
  | .tvar x =>
    let (T, _, bn) ← G[x]?
    qassert (bn = .var) "not a variable"
    return (G, {%x}, T, {%x})
  | .tref t =>
    let (G', p, T, q) ← tinfer' G gs t
    qassert (✦ ∉ q) "Ref over fresh."
    return (G', p, .TRef T q, {✦})
  | .tget t =>
    let (G', p, T, _) ← tinfer' G gs t
    if let .TRef T1 q1 := texposure G' T then
      qassert (#0 ∉ q1) "Getting on non-ref."
      return (G', p ∪ q1, T1, q1)
    else throw ↑"Getting on non-ref."
  | .tput t1 t2 =>
    let (G', p1, T, _) ← tinfer' G gs t1
    if let .TRef T1 q1 := texposure G' T then
      qassert (#0 ∉ q1) "Getting on non-ref."
      let (G'', p2) ← tcheckq G' gs t2 T1 q1
      return (G'', p1 ∪ p2, .TBool, ∅)
    else throw ↑"Putting on non-ref."
  | .tabsa T1 q1 t =>
    qassert (closed_ty 1 ‖G‖ T1 ∧
        closed_ql true 1 ‖G‖ q1 ∧
        occurs .no_covariant T1 #0 ∧
        (#0 ∈ q1 → ✦ ∈ q1)) "Ill argument type."
    let (G', qf, T2, q2) ← tinferabs G gs T1 q1 .var t
    return (G', qf, .TFun T1 q1 T2 q2, qf)
  | .ttabs T1 q1 t =>
    qassert (closed_ty 1 ‖G‖ T1 ∧
        closed_ql true 1 ‖G‖ q1 ∧
        occurs .no_covariant T1 #0 ∧
        (#0 ∈ q1 → ✦ ∈ q1)) "Ill argument type."
    let (G', qf, T2, q2) ← tinferabs G gs T1 q1 .tvar t
    return (G', qf, .TAll T1 q1 T2 q2, qf)
  | .tlet t2 t1 =>
    let (G1, p1, Tx, qx) ← tinfer' G gs t2
    let (G2, qf, T2, q2) ← tinferabs G1 gs Tx qx .var t1
    let (T2', gr) ← avoid_app T2 qf qx
    let q2' := q2 ∪ gr
    let p := qf ∪ p1 ∪ q2' \ {✦, #0, #1}
    return (G2, p, [#0 ↦ qf] [#1 ↦ qx] T2', [#0 ↦ qf] [#1 ↦ qx] q2')
  | .tapp t1 t2 =>
    let (G1, p0, Tf, qf) ← tinfer' G gs t1
    if let .TFun T1 q1 T2 q2 := texposure G1 Tf then
      let T1' ← unpack_argself T1 qf
      let (G', p1, qx) ← tcheck' G1 gs t2 T1'
      let (G'', p2) ← check_app G' gs qf qx q1
      let (T2', gr) ← avoid_app T2 qf qx
      let q2' := q2 ∪ gr
      let p := p0 ∪ p1 ∪ p2 ∪ q2' \ {✦, #0, #1}
      return (G'', p, [#0 ↦ qf] [#1 ↦ qx] T2', [#0 ↦ qf] [#1 ↦ qx] q2')
    else throw ↑"Applying non-function."
  | .ttapp t Tx qx =>
    qassert (closed_ty 0 ‖G‖ Tx ∧ closed_ql true 0 ‖G‖ qx) "Type application not closed"
    let (G1, p0, Tf, qf) ← tinfer' G gs t
    if let .TAll T1 q1 T2 q2 := texposure G1 Tf then
      let T1' ← unpack_argself T1 qf
      let (g1, G') ← check_stp G1 {✦} Tx T1' gs
      qassert (g1 = ∅) "TyApp failed."
      let p1 := qx \ {✦}
      let (G'', p2) ← check_app G' gs qf qx q1
      let (T2', gr) ← avoid_app T2 qf qx
      let q2' := q2 ∪ gr
      let p := p0 ∪ p1 ∪ p2 ∪ q2' \ {✦, #0, #1}
      return (G'', p, [#0 ↦ qf] [#1 ↦ (Tx, qx)] T2', [#0 ↦ qf] [#1 ↦ qx] q2')
    else throw ↑"Applying non-function."
  | .tanno t T q =>
    qassert (closed_ty 0 ‖G‖ T ∧ closed_ql true 0 ‖G‖ q) "Annotation not closed."
    let (G', p) ← tcheckq G gs t T q
    return (G', p, T, q)
  | .tabs _ => throw ↑"No inference on abstraction."
termination_by (sizeOf t, 1)

def tinfer' (G: tenv) (gs: gfset) (t: tm) :=
  qtrace s!"infer: {(t.format' ‖G‖).indentD}" (tinfer G gs t)
termination_by (sizeOf t, 2)

def tinferabs (G: tenv) (gs: gfset) (T1: ty) (q1: ql) (bn: binding) (t2: tm): M (tenv × ql × ty × ql) := do
  modify (fun s => { s with cnt_inferqf := s.cnt_inferqf + 1 })
  let G1 := G ++ [(.TTop, ∅, .self), ([#0 ↦ %‖G‖] T1, [#0 ↦ %‖G‖] q1, bn)]
  let (G2, p2, T2a, q2b) ← tinfer' G1 (gs ∪ {‖G‖}) t2
  let T2b ← rm_contravariant T2a %‖G‖
  let (_, q, _) ← G2[‖G‖]?
  let qf := q ∪ p2 \ {%‖G‖, %(‖G‖+1)} ∪ q1 \ {✦, #0}
  return (G2.take ‖G‖, qf, [%(‖G‖+1) ↦ #1] [%‖G‖ ↦ #0] T2b, [%(‖G‖+1) ↦ #1] [%‖G‖ ↦ #0] q2b)
termination_by (sizeOf t2, 3)

def tcheck (G: tenv) (gs: gfset) (t: tm) (T: ty): M (tenv × ql × ql) := do
  match t, T with
  | .tabs t, .TFun T1 q1 T2 q2 =>
    modify (fun s => { s with cnt_inferqf := s.cnt_inferqf + 1 })
    let G' := G ++ [(.TTop, ∅, .self), ([#0 ↦ %‖G‖] T1, [#0 ↦ %‖G‖] q1, .var)]
    let (G'', p0) ← tcheckq G' (gs ∪ {‖G‖}) t ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] T2) ([#0 ↦ %‖G‖] [#1 ↦ %(‖G‖+1)] q2)
    let (_, qf, _) ← G''[‖G‖]?
    let qf' := qf ∪ p0 \ {%‖G‖, %(‖G‖+1)} ∪ q1 \ {✦, #0}
    return (G''.take ‖G‖, qf', qf')
  | .tref t, .TRef T q =>
    qassert (#0 ∉ q) "Selfrefed Ref."
    let (G', p, q') ← tcheck' G gs t T
    let G'' ← check_qtp G' gs q' q
    return (G'', p ∪ q, {✦})
  | t@_, T@_ =>
    let (G', p, T', q') ← tinfer' G gs t
    let (gr, G'') ← check_stp G' q' T' T gs
    return (G'', p ∪ q' \ {✦} ∪ gr, q' ∪ gr)
termination_by (sizeOf t, 3)
decreasing_by (all_goals simp [Prod.lex_def]); subst_vars; simp

def tcheck' (G: tenv) (gs: gfset) (t: tm) (T: ty) :=
  qtrace s!"check: {T.format' ‖G‖} {(t.format' ‖G‖).indentD}" (tcheck G gs t T)
termination_by (sizeOf t, 4)

def tcheckq (G: tenv) (gs: gfset) (t: tm) (T: ty) (q: ql): M (tenv × ql) := do
  let (G', p, q') ← tcheck' G gs t T
  let G'' ← check_qtp G' gs q' q
  return (G'', p ∪ q \ {✦})
termination_by (sizeOf t, 5)

end

-- size counting

structure MCountResult where
  terms: ℕ
  types: ℕ
  quals: ℕ
deriving Repr

instance: Add MCountResult where
  add lhs rhs :=
    let ⟨tm1, tp1, q1⟩ := lhs
    let ⟨tm2, tp2, q2⟩ := rhs
    ⟨tm1 + tm2, tp1 + tp2, q1 + q2⟩

inductive QualPosition where
| unk | arg | ret
deriving DecidableEq

def ql.mcounts (q: ql) (p: QualPosition) (t: ty): MCountResult :=
  if q = ∅ ∧ t = .TBool ∨
     q = {✦, #0} ∧ p = .arg ∨
     q = {#0, #1} ∧ p = .ret
  then ⟨0, 0, 0⟩ else ⟨0, 0, 1⟩

def ty.mcounts (t: ty) (q: ql) (pos: QualPosition): MCountResult :=
  cnt t + q.mcounts pos t
where cnt : ty → MCountResult
  | TRef T q => T.mcounts q .unk + ⟨0, 1, 0⟩
  | TFun T1 q1 T2 q2 => T1.mcounts q1 .arg + T2.mcounts q2 .ret + ⟨0, 1, 0⟩
  | TAll T1 q1 T2 q2 => T1.mcounts q1 .arg + T2.mcounts q2 .ret + ⟨0, 1, 0⟩
  | _ => ⟨0, 1, 0⟩

def tm.mcounts : tm → MCountResult
  | tref t => t.mcounts + ⟨1, 0, 0⟩
  | tget t => t.mcounts + ⟨1, 0, 0⟩
  | tput tr tx => tr.mcounts + tx.mcounts + ⟨1, 0, 0⟩
  | tapp tf tx => tf.mcounts + tx.mcounts + ⟨1, 0, 0⟩
  | tabs t => t.mcounts + ⟨1, 0, 0⟩
  | tabsa T q t => T.mcounts q .arg + t.mcounts + ⟨1, 0, 0⟩
  | ttapp tf T q => tf.mcounts + ⟨1, 0, 0⟩ + T.mcounts q .unk
  | ttabs T q t => T.mcounts q .arg + t.mcounts + ⟨1, 0, 0⟩
  | tanno t T q => t.mcounts + ⟨1, 0, 0⟩ + T.mcounts q .unk
  | _ => ⟨1, 0, 0⟩

namespace embedding

-- check & bench instruments

def check_program (e: ℕ → tm): M Unit :=
  qtrace "Stack trace:" do
    let _ ← tinfer [] ∅ (e 0)
    return ()

def bench_program (label: String) (e: ℕ → tm): M (String × Float × MCountResult × Stat) := do
  let e' := e 0
  let act := fun s0 =>
    match tinfer [] ∅ e' s0 with
    | .ok _ s1 => .ok s1 {s0 with world := s1.world}
    | .error _ s1 => .ok s1 {s0 with world := s1.world}
  let t0 ← IO.monoMsNow
  for _ in [0:20] do
    let _ ← act
  let t1 ← IO.monoMsNow
  return (label, (t1 - t0).toFloat / 20, e'.mcounts, ←act)

-- syntax embedding

syntax rtid := ident <|> hole
syntax "[rtid|" rtid "]": term
macro_rules
| `([rtid| $x:ident]) => `($x)
| `([rtid| _]) => `(_)

declare_syntax_cat rtqual
syntax "[rtqual|" rtqual "]": term
syntax term:max : rtqual
macro_rules | `([rtqual| $q:term]) => `((($q): ql))

declare_syntax_cat rttype
syntax "[rttype|" rttype "]": term
syntax "⟪" term "⟫": rttype
macro_rules
| `([rttype| ⟪ $t ⟫]) => `(fun (n: ℕ) => $t n)

declare_syntax_cat rtterm
syntax "[rtterm|" rtterm "]": term
syntax "⟪" term "⟫": rtterm
syntax "(" rtterm ")": rtterm
macro_rules
| `([rtterm| ⟪ $t ⟫]) => `(fun (n: ℕ) => $t n)
| `([rtterm| ( $t:rtterm )]) => `([rtterm| $t])

instance: Inhabited tm := ⟨tm.ttrue⟩

def tm.tvar!: id → tm
  | %n => tm.tvar n
  | _ => unreachable!
