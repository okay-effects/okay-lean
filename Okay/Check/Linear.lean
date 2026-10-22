import Okay.Check.Arith

/-! # Polynomial forms — okay-proof's `Linear`: `Σ cᵢ·mᵢ + c`, monomials canonical products of atoms in key order -/

namespace Okay.Check

/-- coefficients by monomial (no zero among them), and the constant -/
structure Lin where
  coeffs : List (Term × Dec)
  const : Dec
  deriving Inhabited

namespace Lin
def zero : Lin := ⟨[], Dec.zero⟩
def ofConst (c : Dec) : Lin := ⟨[], c⟩
def atom (t : Term) : Lin := ⟨[(t, Dec.one)], Dec.zero⟩
def isConst (l : Lin) : Bool := l.coeffs.isEmpty
def get? (l : Lin) (t : Term) : Option Dec := (l.coeffs.find? (·.1 == t)).map (·.2)

/-- `a + k·b`, coefficients that become zero dropped -/
def merge (a : List (Term × Dec)) (b : List (Term × Dec)) (k : Dec) : List (Term × Dec) :=
  b.foldl (fun m (t, c) =>
    let v := (match m.find? (·.1 == t) with | some (_, x) => x | none => Dec.zero) + c * k
    let rest := m.filter (·.1 != t)
    if v.m == 0 then rest else rest ++ [(t, v)]) a

def plus (a b : Lin) : Lin := ⟨merge a.coeffs b.coeffs Dec.one, a.const + b.const⟩
def minus (a b : Lin) : Lin := ⟨merge a.coeffs b.coeffs (Dec.neg Dec.one), a.const - b.const⟩
def scale (a : Lin) (c : Dec) : Lin :=
  if c.m == 0 then zero else ⟨a.coeffs.map (fun (t, x) => (t, x * c)), a.const * c⟩
end Lin

namespace Linear
open Logic

/-- a monomial's atoms -/
partial def factors : Term → List Term
  | .ap fn [a, b] => if fn == Fns.mul || fn == Fns.dmul then factors a ++ factors b else [.ap fn [a, b]]
  | t => [t]

/-- atoms multiplied, in key order -/
def monomial (atoms : List Term) (s : Srt) : Term :=
  let mul := if s == .int then Fns.mul else Fns.dmul
  match atoms.mergeSort byKey with
  | [] => .i 1
  | a :: rest => rest.foldl (fun x y => .ap mul [x, y]) a

def times (x y : Lin) (s : Srt) : Lin :=
  if x.isConst then y.scale x.const
  else if y.isConst then x.scale y.const
  else
    let start := Lin.merge (Lin.merge [] x.coeffs y.const) y.coeffs x.const
    let coeffs := x.coeffs.foldl (fun acc (m, a) =>
      y.coeffs.foldl (fun acc (n, b) => Lin.merge acc [(monomial (factors m ++ factors n) s, a * b)] Dec.one) acc) start
    ⟨coeffs, x.const * y.const⟩

/-- a form as a term of sort `s`: its monomials in key order, then its constant -/
def term (l : Lin) (s : Srt) : Term :=
  let lit (c : Dec) : Term := if s == .int then .i c.m else .d c
  let add := if s == .int then Fns.add else Fns.dadd
  let mul := if s == .int then Fns.mul else Fns.dmul
  let parts := (l.coeffs.mergeSort (fun a b => byKey a.1 b.1)).map fun (a, c) =>
    if c == Dec.one then a else .ap mul [lit c, a]
  let all := if l.const.m != 0 || parts.isEmpty then parts ++ [lit l.const] else parts
  match all with
  | [] => lit Dec.zero
  | x :: rest => rest.foldl (fun a b => .ap add [a, b]) x

mutual
  partial def form (t : Term) (s : Srt) : Lin :=
    let closed := if (freeT t).isEmpty then
        match Arithmetic.value t with
        | some (.int v) => some (Lin.ofConst (Dec.ofInt v))
        | some (.dec v) => some (Lin.ofConst v)
        | _ => none
      else none
    match closed with
    | some l => l
    | none => match t with
      | .i n => Lin.ofConst (Dec.ofInt n)
      | .d x => Lin.ofConst x
      | .ap fn [a, b] =>
        if fn == Fns.add || fn == Fns.dadd then (form a s).plus (form b s)
        else if fn == Fns.sub || fn == Fns.dsub then (form a s).minus (form b s)
        else if fn == Fns.mul || fn == Fns.dmul then times (form a s) (form b s) s
        else Lin.atom (canonical t)
      | .ap fn [a] => if fn == Fns.neg then (form a s).scale (Dec.neg Dec.one) else Lin.atom (canonical t)
      | _ => Lin.atom (canonical t)

  partial def canonical (t : Term) : Term :=
    match t with
    | .ap fn as => .ap fn (as.map fun a => match sortOf a with
        | some s => if numeric s then term (form a s) s else canonical a
        | none => canonical a)
    | other => other
end

def lin (t : Term) : Option Lin := (sortOf t).bind fun s => if numeric s then some (form t s) else none

inductive Kind | nonStrict | strict | equal
  deriving BEq

/-- a comparison as okay-proof reads it: `0 ≤ F`, `0 < F` or `0 = F`, the sort; over `Int` a strict one `F − 1 ≥ 0` -/
def comparison : Formula → Option (Lin × Kind × Srt)
  | .le a b => mk a b .nonStrict
  | .lt a b => mk a b .strict
  | .eq a b => mk a b .equal
  | .not (.le a b) => mk b a .strict
  | .not (.lt a b) => mk b a .nonStrict
  | _ => none
where
  mk (a b : Term) (k : Kind) : Option (Lin × Kind × Srt) := do
    let s ← sortOf a
    if !numeric s || sortOf b != some s then none
    let d := (form b s).minus (form a s)
    if k == .strict && s == .int then some (d.minus (Lin.ofConst Dec.one), .nonStrict, s) else some (d, k, s)

def integral (l : Lin) : Bool := l.const.isInt && l.coeffs.all (·.2.isInt)

def gcd (l : Lin) : Nat := l.coeffs.foldl (fun g (_, c) => Nat.gcd g c.m.natAbs) 0

end Linear
end Okay.Check
