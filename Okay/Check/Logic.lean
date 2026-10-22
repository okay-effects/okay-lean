import Okay.Check.Dec

/-!
# okay-proof's logic, read again

Many-sorted first-order logic with equality — the same sorts, terms and formulas as okay-proof's `Logic.scala`, the
same free variables, the same capture-avoiding substitution with the same fresh names, the same alpha-equivalence,
the same KEY of a term (what orders a polynomial's atoms), so that every conclusion this checker derives is, as data,
the one okay-proof's kernel derives.
-/

namespace Okay.Check

inductive Srt where
  | int | dec | str
  | named (n : String)
  deriving BEq, Repr, Inhabited

structure Fn where
  name : String
  args : List Srt
  result : Srt
  deriving BEq, Repr, Inhabited

structure Pred where
  name : String
  args : List Srt
  deriving BEq, Repr, Inhabited

structure Var where
  name : String
  sort : Srt
  deriving BEq, Repr, Inhabited

inductive Term where
  | v (x : Var)
  | i (n : Int)
  | d (x : Dec)
  | s (x : String)
  | ap (fn : Fn) (args : List Term)
  deriving BEq, Repr, Inhabited

inductive Formula where
  | tt | ff
  | eq (a b : Term)
  | lt (a b : Term)
  | le (a b : Term)
  | p (pr : Pred) (args : List Term)
  | not (f : Formula)
  | and (a b : Formula)
  | or (a b : Formula)
  | imp (a b : Formula)
  | all (x : Var) (f : Formula)
  | ex (x : Var) (f : Formula)
  deriving BEq, Repr, Inhabited

namespace Logic

def numeric (s : Srt) : Bool := s == .int || s == .dec

private def dedup (xs : List Var) : List Var := xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

partial def freeT : Term → List Var
  | .v x => [x]
  | .ap _ as => dedup (as.flatMap freeT)
  | _ => []

partial def free : Formula → List Var
  | .eq a b | .lt a b | .le a b => dedup (freeT a ++ freeT b)
  | .p _ as => dedup (as.flatMap freeT)
  | .not f => free f
  | .and a b | .or a b | .imp a b => dedup (free a ++ free b)
  | .all x f | .ex x f => (free f).filter (· != x)
  | _ => []

partial def sortOf : Term → Option Srt
  | .v x => some x.sort
  | .i _ => some .int
  | .d _ => some .dec
  | .s _ => some .str
  | .ap fn as => if fits as fn.args then some fn.result else none
where
  fits : List Term → List Srt → Bool
    | [], [] => true
    | a :: as, s :: ss => sortOf a == some s && fits as ss
    | _, _ => false

partial def wellSorted : Formula → Bool
  | .tt | .ff => true
  | .eq a b => (sortOf a).isSome && sortOf a == sortOf b
  | .lt a b | .le a b => match sortOf a with
    | some s => sortOf b == some s && numeric s
    | none => false
  | .p pr as => sortOf.fits as pr.args
  | .not f => wellSorted f
  | .and a b | .or a b | .imp a b => wellSorted a && wellSorted b
  | .all _ f | .ex _ f => wellSorted f

/-! ## Keys -/

private def named (s : String) : String := toString s.length ++ ":" ++ s

def sortKey : Srt → String
  | .int => "I"
  | .dec => "D"
  | .str => "S"
  | .named n => "N" ++ named n

partial def key : Term → String
  | .v x => "v" ++ named x.name ++ sortKey x.sort
  | .i n => "i" ++ toString n ++ ";"
  | .d x => "d" ++ x.plain ++ ";"
  | .s x => "s" ++ named x
  | .ap fn as =>
    "a" ++ named fn.name ++ toString fn.args.length ++ "(" ++ String.join (fn.args.map sortKey) ++ ")" ++
      sortKey fn.result ++ "[" ++ String.join (as.map key) ++ "]"

/-- terms in the order of their keys, compared by code points -/
def byKey (a b : Term) : Bool := decide (key a ≤ key b)

/-! ## Substitution -/

partial def substT (t : Term) (x : Var) (by_ : Term) : Term :=
  match t with
  | .v y => if y == x then by_ else t
  | .ap fn as => if (freeT t).contains x then .ap fn (as.map (substT · x by_)) else t
  | _ => t

/-- a variable like `y`, its name none of `avoid`'s: `y1`, `y2`, … -/
partial def fresh (y : Var) (avoid : List Var) : Var :=
  go 1
where
  go (i : Nat) : Var :=
    let v : Var := ⟨y.name ++ toString i, y.sort⟩
    if avoid.any (·.name == v.name) then go (i + 1) else v

partial def subst (f : Formula) (x : Var) (by_ : Term) : Formula :=
  if !(free f).contains x then f
  else match f with
    | .eq a b => .eq (substT a x by_) (substT b x by_)
    | .lt a b => .lt (substT a x by_) (substT b x by_)
    | .le a b => .le (substT a x by_) (substT b x by_)
    | .p pr as => .p pr (as.map (substT · x by_))
    | .not g => .not (subst g x by_)
    | .and a b => .and (subst a x by_) (subst b x by_)
    | .or a b => .or (subst a x by_) (subst b x by_)
    | .imp a b => .imp (subst a x by_) (subst b x by_)
    | .all y g => binder y g .all
    | .ex y g => binder y g .ex
    | other => other
where
  binder (y : Var) (g : Formula) (make : Var → Formula → Formula) : Formula :=
    if y == x then make y g
    else if (freeT by_).contains y then
      let y2 := fresh y (freeT by_ ++ free g ++ [x])
      make y2 (subst (subst g y (.v y2)) x by_)
    else make y (subst g x by_)

partial def alphaEq (a b : Formula) : Bool :=
  a == b || match a, b with
    | .all x f, .all y g => x.sort == y.sort && body x f y g
    | .ex x f, .ex y g => x.sort == y.sort && body x f y g
    | .not f, .not g => alphaEq f g
    | .and a1 b1, .and a2 b2 => alphaEq a1 a2 && alphaEq b1 b2
    | .or a1 b1, .or a2 b2 => alphaEq a1 a2 && alphaEq b1 b2
    | .imp a1 b1, .imp a2 b2 => alphaEq a1 a2 && alphaEq b1 b2
    | _, _ => false
where
  body (x : Var) (f : Formula) (y : Var) (g : Formula) : Bool :=
    if x == y then alphaEq f g
    else
      let z := fresh x (free f ++ free g ++ [x, y])
      alphaEq (subst f x (.v z)) (subst g y (.v z))

end Logic
end Okay.Check
