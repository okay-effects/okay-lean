/-!
# Exact decimals, as okay-proof's kernel computes them

`m · 10^(-e)`, kept with no trailing zero, so equal values are equal data. Rounding as `java.math.BigDecimal`'s:
half to even, half up (away from zero), down (floor); a division to a scale, half to even.
-/

namespace Okay.Check

structure Dec where
  m : Int
  e : Nat
  deriving BEq, Repr, Inhabited

namespace Dec

def pow10 (n : Nat) : Int := (10 : Int) ^ n

/-- no trailing zero -/
def norm (m : Int) (e : Nat) : Dec :=
  if m == 0 then ⟨0, 0⟩ else go m e
where
  go (m : Int) : Nat → Dec
    | 0 => ⟨m, 0⟩
    | e + 1 => if m % 10 == 0 then go (m / 10) e else ⟨m, e + 1⟩

def ofInt (i : Int) : Dec := norm i 0
def zero : Dec := ⟨0, 0⟩
def one : Dec := ⟨1, 0⟩

private def align (a b : Dec) : Int × Int × Nat :=
  let e := max a.e b.e
  (a.m * pow10 (e - a.e), b.m * pow10 (e - b.e), e)

def add (a b : Dec) : Dec := let (x, y, e) := align a b; norm (x + y) e
def neg (a : Dec) : Dec := ⟨-a.m, a.e⟩
def sub (a b : Dec) : Dec := add a (neg b)
def mul (a b : Dec) : Dec := norm (a.m * b.m) (a.e + b.e)
def cmp (a b : Dec) : Ordering := let (x, y, _) := align a b; compare x y
def signum (a : Dec) : Int := if a.m > 0 then 1 else if a.m < 0 then -1 else 0
def isInt (a : Dec) : Bool := a.e == 0

instance : Add Dec := ⟨add⟩
instance : Sub Dec := ⟨sub⟩
instance : Mul Dec := ⟨mul⟩
instance : Neg Dec := ⟨neg⟩

inductive Mode | halfEven | halfUp | floor

/-- `n / d`, `d > 0`, to an integer -/
def roundDiv (n d : Int) (mode : Mode) : Int :=
  match mode with
  | .floor => Int.fdiv n d
  | _ =>
    let a := n.natAbs
    let dn := d.natAbs
    let q := a / dn
    let r := a % dn
    let up := match mode with
      | .halfUp => decide (2 * r ≥ dn)
      | _ => 2 * r > dn || (2 * r == dn && q % 2 == 1)
    let qa : Int := if up then q + 1 else q
    if n < 0 then -qa else qa

private def scaled (q : Int) (s : Int) : Dec :=
  if s ≥ 0 then norm q s.toNat else norm (q * pow10 (-s).toNat) 0

/-- the value to `s` places (`s` may be negative), rounded as `mode` says -/
def setScale (a : Dec) (s : Int) (mode : Mode) : Dec :=
  if s ≥ (a.e : Int) then a
  else scaled (roundDiv a.m (pow10 ((a.e : Int) - s).toNat) mode) s

/-- `a / b` to `s` places, half to even; `b ≠ 0` -/
def divScale (a b : Dec) (s : Int) : Dec :=
  let num := a.m * pow10 b.e
  let den := b.m * pow10 a.e
  let (num, den) := if s ≥ 0 then (num * pow10 s.toNat, den) else (num, den * pow10 (-s).toNat)
  let (num, den) := if den < 0 then (-num, -den) else (num, den)
  scaled (roundDiv num den .halfEven) s

/-- the value's text: no trailing zero, no exponent — `java.math.BigDecimal`'s `stripTrailingZeros().toPlainString()` -/
def plain (a : Dec) : String :=
  if a.m == 0 then "0" else
  let ds := (toString a.m.natAbs).toList
  let body :=
    if a.e == 0 then String.ofList ds
    else
      let ds := if ds.length ≤ a.e then List.replicate (a.e + 1 - ds.length) '0' ++ ds else ds
      String.ofList (ds.take (ds.length - a.e)) ++ "." ++ String.ofList (ds.drop (ds.length - a.e))
  (if a.m < 0 then "-" else "") ++ body

/-- a decimal's text: `-12.50`, `3`, `0.05` -/
def parse? (s : String) : Option Dec :=
  let cs := s.toList
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let ip := cs.takeWhile Char.isDigit
  let rest := cs.drop ip.length
  let (fp, rest) := match rest with
    | '.' :: r => (r.takeWhile Char.isDigit, r.drop (r.takeWhile Char.isDigit).length)
    | r => ([], r)
  if !rest.isEmpty || (ip.isEmpty && fp.isEmpty) then none
  else
    let m : Int := (String.ofList (ip ++ fp)).toNat?.getD 0
    some (norm (if neg then -m else m) fp.length)

end Dec
end Okay.Check
