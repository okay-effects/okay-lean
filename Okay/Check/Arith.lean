import Okay.Check.Logic

/-! # The kernel's own functions, computed exactly — okay-proof's `Fns` and `Arithmetic` -/

namespace Okay.Check

namespace Fns
def add : Fn := ⟨"+", [.int, .int], .int⟩
def sub : Fn := ⟨"-", [.int, .int], .int⟩
def mul : Fn := ⟨"*", [.int, .int], .int⟩
def neg : Fn := ⟨"neg", [.int], .int⟩
def div : Fn := ⟨"div", [.int, .int], .int⟩
def mod : Fn := ⟨"mod", [.int, .int], .int⟩
def dec : Fn := ⟨"dec", [.int], .dec⟩
def dadd : Fn := ⟨"d+", [.dec, .dec], .dec⟩
def dsub : Fn := ⟨"d-", [.dec, .dec], .dec⟩
def dmul : Fn := ⟨"d*", [.dec, .dec], .dec⟩
def ddiv : Fn := ⟨"d/", [.dec, .dec, .int], .dec⟩
def round : Fn := ⟨"round", [.dec, .int], .dec⟩
def roundHalfUp : Fn := ⟨"roundHalfUp", [.dec, .int], .dec⟩
def concat : Fn := ⟨"++", [.str, .str], .str⟩
def length : Fn := ⟨"length", [.str], .int⟩
/-- the first `n` characters, all if fewer, none if `n` < 0 -/
def take : Fn := ⟨"take", [.str, .int], .str⟩
/-- the last `n` characters, likewise -/
def takeRight : Fn := ⟨"takeRight", [.str, .int], .str⟩
/-- where `p` first stands in `a`, in characters from 0; -1 if nowhere; 0 for the empty text -/
def indexOf : Fn := ⟨"indexOf", [.str, .str], .int⟩
def all : List Fn := [add, sub, mul, neg, div, mod, dec, dadd, dsub, dmul, ddiv, round, roundHalfUp, concat, length,
  take, takeRight, indexOf]
end Fns

inductive Val where
  | int (n : Int)
  | dec (x : Dec)
  | str (s : String)
  deriving BEq, Inhabited

namespace Arithmetic
open Formula

private def scale (n : Int) : Option Int := if -1000 ≤ n ∧ n ≤ 1000 then some n else none

/-- where `ps` first stands in `cs`, from `i` -/
private def indexFrom (ps : List Char) : List Char → Nat → Int
  | cs, i => if ps.isPrefixOf cs then i else match cs with
    | [] => -1
    | _ :: t => indexFrom ps t (i + 1)

private def apply (fn : Fn) (vs : List Val) : Option Val :=
  match fn.name, vs with
  | "+", [.int a, .int b] => some (.int (a + b))
  | "-", [.int a, .int b] => some (.int (a - b))
  | "*", [.int a, .int b] => some (.int (a * b))
  | "neg", [.int a] => some (.int (-a))
  | "div", [.int a, .int b] => if b != 0 then some (.int (Int.fdiv a b)) else none
  | "mod", [.int a, .int b] => if b != 0 then some (.int (Int.fmod a b)) else none
  | "dec", [.int a] => some (.dec (Dec.ofInt a))
  | "d+", [.dec a, .dec b] => some (.dec (a + b))
  | "d-", [.dec a, .dec b] => some (.dec (a - b))
  | "d*", [.dec a, .dec b] => some (.dec (a * b))
  | "d/", [.dec a, .dec b, .int s] => if b.m == 0 then none else (scale s).map (.dec <| Dec.divScale a b ·)
  | "round", [.dec a, .int s] => (scale s).map (.dec <| a.setScale · .halfEven)
  | "roundHalfUp", [.dec a, .int s] => (scale s).map (.dec <| a.setScale · .halfUp)
  | "++", [.str a, .str b] => some (.str (a ++ b))
  | "length", [.str a] => some (.int a.length)
  | "take", [.str a, .int n] => some (.str (String.ofList (a.toList.take n.toNat)))
  | "takeRight", [.str a, .int n] => some (.str (String.ofList (a.toList.drop (a.length - n.toNat))))
  | "indexOf", [.str a, .str q] => some (.int (indexFrom q.toList a.toList 0))
  | _, _ => none

partial def value : Term → Option Val
  | .i n => some (.int n)
  | .d x => some (.dec x)
  | .s x => some (.str x)
  | .v _ => none
  | .ap fn as =>
    if !Fns.all.contains fn then none
    else match as.mapM value with
      | some vs => apply fn vs
      | none => none

private def compare? : Val → Val → Option Ordering
  | .int a, .int b => some (compare a b)
  | .dec a, .dec b => some (a.cmp b)
  | _, _ => none

/-- a closed, quantifier-free formula's truth, if computable — evaluated as okay-proof's `Arithmetic.truth` -/
partial def truth : Formula → Option Bool
  | .tt => some true
  | .ff => some false
  | .eq a b => do
    let x ← value a
    let y ← value b
    pure (match x, y with
      | .dec u, .dec w => u.cmp w == .eq
      | _, _ => x == y)
  | .lt a b => do let x ← value a; let y ← value b; let c ← compare? x y; pure (c == .lt)
  | .le a b => do let x ← value a; let y ← value b; let c ← compare? x y; pure (c != .gt)
  | .not g => (truth g).map (!·)
  | .and a b => (truth a).bind fun x => if !x then some false else truth b
  | .or a b => (truth a).bind fun x => if x then some true else truth b
  | .imp a b => (truth a).bind fun x => if !x then some true else truth b
  | _ => none

end Arithmetic
end Okay.Check
