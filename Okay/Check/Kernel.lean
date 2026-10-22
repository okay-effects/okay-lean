import Okay.Check.Linear

/-!
# okay-proof's kernel, a second time

Each rule of okay-proof's `Kernel.derive`, checked as it checks it, its conclusion built as it builds it. A theorem
here is hypotheses ⊢ conclusion; the hypotheses a set (a list without repeats).
-/

namespace Okay.Check

abbrev Theory := List (String × Formula)

structure Thm where
  hyps : List Formula
  concl : Formula
  deriving Inhabited

inductive Step where
  | assume (f : Formula)
  | axiom (name : String)
  | compute (f : Formula)
  | andI (a b : Thm)
  | andE1 (t : Thm)
  | andE2 (t : Thm)
  | orI1 (t : Thm) (right : Formula)
  | orI2 (left : Formula) (t : Thm)
  | orE (t l r : Thm)
  | impI (f : Formula) (t : Thm)
  | impE (imp arg : Thm)
  | notI (f : Formula) (t : Thm)
  | notE (n t : Thm)
  | classic (t : Thm)
  | falseE (t : Thm) (f : Formula)
  | allI (x : Var) (t : Thm)
  | allE (t : Thm) (by_ : Term)
  | exI (x : Var) (f : Formula) (by_ : Term) (t : Thm)
  | exE (e : Thm) (y : Var) (t : Thm)
  | refl (t : Term)
  | subst (eq : Thm) (x : Var) (f : Formula) (t : Thm)
  | induct (x : Var) (f : Formula) (base step : Thm)
  | norm (f : Formula)
  | linComb (ps : List (Thm × Dec))
  | antisym (le ge : Thm)
  | tighten (t : Thm)
  | mulNonneg (a b : Thm)
  | square (t : Term)

namespace Kernel
open Logic Linear

def union (a b : List Formula) : List Formula := b.foldl (fun acc f => if acc.contains f then acc else acc ++ [f]) a
def unions (xs : List (List Formula)) : List Formula := xs.foldl union []
def minus (a : List Formula) (f : Formula) : List Formula := a.filter (· != f)

private def zero (s : Srt) : Term := if s == .int then .i 0 else .d Dec.zero

private def ok (hyps : List Formula) (concl : Formula) : Except String Thm := .ok ⟨hyps, concl⟩
private def need (b : Bool) (why : String) (k : Unit → Except String Thm) : Except String Thm :=
  if b then k () else .error why

private def holds (d : Lin) (k : Kind) : Bool :=
  let c := d.const.signum
  match k with
  | .equal => c == 0
  | .nonStrict => c ≥ 0
  | .strict => c > 0

private def linComb (ps : List (Thm × Dec)) : Except String Thm := do
  if ps.isEmpty then throw "no premises"
  let rows ← ps.mapM fun (t, c) => match comparison t.concl with
    | some (f, k, s) => pure (t, c, f, k, s)
    | none => throw s!"not a linear comparison over Int or Dec"
  let sorts := rows.foldl (fun acc (_, _, _, _, s) => if acc.contains s then acc else acc ++ [s]) []
  match sorts with
  | [s] =>
    for (_, c, _, k, _) in rows do
      if k != .equal && c.signum < 0 then throw "a negative coefficient"
      if s == .int && !c.isInt then throw "over Int, a coefficient that is not an integer"
    let total := rows.foldl (fun acc (_, c, f, _, _) => acc.plus (f.scale c)) Lin.zero
    let strict := rows.any fun (_, c, _, k, _) => k == .strict && c.signum > 0
    let t := term total s
    pure ⟨unions (rows.map (·.1.hyps)), if strict then .lt (zero s) t else .le (zero s) t⟩
  | _ => throw "premises of two sorts"

def derive (th : Theory) : Step → Except String Thm
  | .assume f => need (wellSorted f) "not well-sorted" fun _ => ok [f] f
  | .axiom n => match th.lookup n with
    | some f => ok [] f
    | none => .error s!"no axiom '{n}'"
  | .compute f =>
    need (wellSorted f && (free f).isEmpty) "not closed and well-sorted" fun _ =>
      match Arithmetic.truth f with
      | some true => ok [] f
      | some false => .error "computed false"
      | none => .error "not computable"
  | .andI a b => ok (union a.hyps b.hyps) (.and a.concl b.concl)
  | .andE1 t => match t.concl with
    | .and a _ => ok t.hyps a
    | _ => .error "not a conjunction"
  | .andE2 t => match t.concl with
    | .and _ b => ok t.hyps b
    | _ => .error "not a conjunction"
  | .orI1 t right => need (wellSorted right) "not well-sorted" fun _ => ok t.hyps (.or t.concl right)
  | .orI2 left t => need (wellSorted left) "not well-sorted" fun _ => ok t.hyps (.or left t.concl)
  | .orE t l r => match t.concl with
    | .or a b => need (alphaEq l.concl r.concl) "two cases, two conclusions" fun _ =>
        ok (union (union t.hyps (minus l.hyps a)) (minus r.hyps b)) l.concl
    | _ => .error "not a disjunction"
  | .impI f t => need (wellSorted f) "not well-sorted" fun _ => ok (minus t.hyps f) (.imp f t.concl)
  | .impE i a => match i.concl with
    | .imp p q => need (alphaEq p a.concl) "the premise is not the implication's" fun _ => ok (union i.hyps a.hyps) q
    | _ => .error "not an implication"
  | .notI f t => need (wellSorted f && t.concl == .ff) "not False" fun _ => ok (minus t.hyps f) (.not f)
  | .notE n t => match n.concl with
    | .not p => need (alphaEq p t.concl) "not the negated formula" fun _ => ok (union n.hyps t.hyps) .ff
    | _ => .error "not a negation"
  | .classic t => match t.concl with
    | .not (.not p) => ok t.hyps p
    | _ => .error "not a double negation"
  | .falseE t f => need (t.concl == .ff && wellSorted f) "not False" fun _ => ok t.hyps f
  | .allI x t => need (!t.hyps.any fun h => (free h).contains x) "free in a hypothesis" fun _ => ok t.hyps (.all x t.concl)
  | .allE t by_ => match t.concl with
    | .all x f => need (sortOf by_ == some x.sort) "not of the variable's sort" fun _ => ok t.hyps (subst f x by_)
    | _ => .error "not universal"
  | .exI x f by_ t =>
    need (wellSorted f && sortOf by_ == some x.sort) "ill-sorted" fun _ =>
      need (alphaEq t.concl (subst f x by_)) "not the instance" fun _ => ok t.hyps (.ex x f)
  | .exE e y t => match e.concl with
    | .ex x f =>
      let inst := subst f x (.v y)
      let rest := minus t.hyps inst
      need (y.sort == x.sort && !(free t.concl).contains y && !(free e.concl).contains y
          && !rest.any (fun h => (free h).contains y) && !e.hyps.any (fun h => (free h).contains y)) "not fresh"
        fun _ => ok (union e.hyps rest) t.concl
    | _ => .error "not existential"
  | .refl t => need (sortOf t).isSome "not well-sorted" fun _ => ok [] (.eq t t)
  | .subst eq x f t => need (wellSorted f) "not well-sorted" fun _ => match eq.concl with
    | .eq s u => need (sortOf s == some x.sort) "not of the variable's sort" fun _ =>
        need (alphaEq t.concl (subst f x s)) "not the formula at s" fun _ => ok (union eq.hyps t.hyps) (subst f x u)
    | _ => .error "not an equation"
  | .induct x f base step =>
    need (x.sort == .int && wellSorted f) "not over the integers" fun _ =>
      need (alphaEq base.concl (subst f x (.i 0))) "not the base" fun _ =>
        let next := subst f x (.ap Fns.add [.v x, .i 1])
        let want := Formula.all x (.imp (.and (.le (.i 0) (.v x)) f) next)
        need (alphaEq step.concl want) "not the step" fun _ =>
          ok (union base.hyps step.hyps) (.all x (.imp (.le (.i 0) (.v x)) f))
  | .norm f =>
    let shape := match f with
      | .eq .. | .le .. | .lt .. => true
      | _ => false
    need (shape && wellSorted f) "not a comparison" fun _ => match comparison f with
      | some (d, k, _) => need (d.isConst) "more than a constant" fun _ => need (holds d k) "false" fun _ => ok [] f
      | none => .error "not a comparison over Int or Dec"
  | .linComb ps => linComb ps
  | .antisym le ge => match le.concl, ge.concl with
    | .le a b, .le b2 a2 => need (a == a2 && b == b2 && (match sortOf a with | some s => numeric s | none => false))
        "not a ≤ b and b ≤ a" fun _ => ok (union le.hyps ge.hyps) (.eq a b)
    | _, _ => .error "not a ≤ b and b ≤ a"
  | .tighten t => match comparison t.concl with
    | some (d, .nonStrict, .int) =>
      need (!d.isConst && integral d) "not 0 ≤ F over Int" fun _ =>
        let g : Int := gcd d
        let c := Int.fdiv d.const.m g
        let scaled : Lin := ⟨d.coeffs.map (fun (m, x) => (m, Dec.ofInt (x.m / g))), Dec.ofInt c⟩
        ok t.hyps (.le (.i 0) (term scaled .int))
    | _ => .error "not 0 ≤ F over Int"
  | .mulNonneg a b => match comparison a.concl, comparison b.concl with
    | some (f, k1, s1), some (g, k2, s2) =>
      need (s1 == s2) "two sorts" fun _ =>
        let p := term (times f g s1) s1
        let c : Formula :=
          if k1 == .equal || k2 == .equal then .eq (zero s1) p
          else if k1 == .strict && k2 == .strict then .lt (zero s1) p
          else .le (zero s1) p
        ok (union a.hyps b.hyps) c
    | _, _ => .error "not two comparisons"
  | .square t => match sortOf t with
    | some s => if numeric s then
        match lin t with
        | some f => ok [] (.le (zero s) (term (times f f s) s))
        | none => .error "not a numeric term"
      else .error "not a numeric term"
    | none => .error "not a numeric term"

end Kernel
end Okay.Check
