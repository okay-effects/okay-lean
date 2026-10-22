import Okay.Wire.Json

/-!
# A value on okay's wire

What crosses between okay and Lean, and how the wire writes it: an integer past 2^53 `{"t":"int","v":"…"}`, a double
that is a whole number `{"t":"f","v":…}` (so it is read back a double), NaN `{"t":"nan"}`, a record
`{"t":"dict","kv":[[k,v],…]}`, a table `{"t":"frame","cols":…}` — the rules okay's other far sides follow.
-/

namespace Okay.Wire

/-- a value on the wire -/
inductive Value where
  | null
  | bool (b : Bool)
  | int (n : Int)
  | double (d : Float)
  | str (s : String)
  | list (xs : List Value)
  | dict (kv : List (String × Value))
  /-- a TABLE: named columns in order -/
  | table (cols : List (String × List Value))
  deriving Inhabited, Repr

/-- a failure by name, as the host reads it -/
structure Condition where
  kind : String
  message : String
  deriving Inhabited, Repr, BEq

namespace Value

/-- a double's exact decimal: `m · 2^e` written out, so it reads back the same double -/
def floatText (d : Float) : String :=
  if d.isNaN || d.isInf then "0" else
  let (m, e) := d.abs.frExp
  let mant : Nat := (m.scaleB 53).toUInt64.toNat
  let e2 : Int := e - 53
  let body :=
    if e2 ≥ 0 then toString (mant * 2 ^ e2.toNat)
    else
      let k := (-e2).toNat
      let ds := (toString (mant * 5 ^ k)).toList
      let ds := if ds.length ≤ k then List.replicate (k + 1 - ds.length) '0' ++ ds else ds
      let ip := ds.take (ds.length - k)
      let fp := ((ds.drop (ds.length - k)).reverse.dropWhile (· == '0')).reverse
      if fp.isEmpty then String.ofList ip else String.ofList ip ++ "." ++ String.ofList fp
  if d < 0 then "-" ++ body else body

/-- a number's text read as a double -/
def parseFloat (s : String) : Float :=
  let cs := s.toList
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let ip := cs.takeWhile Char.isDigit
  let cs := cs.drop ip.length
  let (fp, cs) := match cs with
    | '.' :: r => let f := r.takeWhile Char.isDigit; (f, r.drop f.length)
    | r => ([], r)
  let e : Int := match cs with
    | c :: r =>
      if c == 'e' || c == 'E' then
        match r with
        | '-' :: d => - ((String.ofList d).toNat?.getD 0 : Int)
        | '+' :: d => (String.ofList d).toNat?.getD 0
        | d => (String.ofList d).toNat?.getD 0
      else 0
    | [] => 0
  let mant := (String.ofList (ip ++ fp)).toNat?.getD 0
  let exp : Int := e - fp.length
  let v := if exp ≥ 0 then Float.ofScientific mant false exp.toNat else Float.ofScientific mant true (-exp).toNat
  if neg then -v else v

private def isIntText (t : String) : Bool :=
  !t.isEmpty && t.toList.all fun c => c.isDigit || c == '-'

private def asDouble : Value → Value
  | int n => double (Float.ofInt n)
  | v => v

/-- a value as the wire writes it -/
partial def enc : Value → Json
  | null => .null
  | bool b => .bool b
  | int n =>
    if n.natAbs < 2 ^ 53 then .num (toString n) else .obj [("t", .str "int"), ("v", .str (toString n))]
  | double d =>
    if d.isNaN then .obj [("t", .str "nan")]
    else if d == d.round && d.abs < 1e15 then .obj [("t", .str "f"), ("v", .num (floatText d))]
    else .num (floatText d)
  | str s => .str s
  | list xs => .arr (xs.map enc)
  | dict kv => .obj [("t", .str "dict"), ("kv", .arr (kv.map fun (k, v) => .arr [.str k, enc v]))]
  | table cs => .obj [("t", .str "frame"), ("cols", .arr (cs.map fun (k, vs) => .arr [.str k, .arr (vs.map enc)]))]

mutual
  /-- a value read off the wire -/
  partial def dec : Json → Value
    | .null => null
    | .bool b => bool b
    | .num t => if isIntText t then int (t.toInt?.getD 0) else double (parseFloat t)
    | .str s => str s
    | .arr xs => list (xs.map dec)
    | .obj fs =>
      match fs.lookup "t" with
      | some (.str "nan") => double (0.0 / 0.0)
      | some (.str "f") => match fs.lookup "v" with
        | some (.num t) => double (parseFloat t)
        | _ => null
      | some (.str "int") => match fs.lookup "v" with
        | some (.str d) => int (d.toInt?.getD 0)
        | _ => null
      | some (.str "dict") => match fs.lookup "kv" with
        | some (.arr ps) => dict (ps.filterMap fun | .arr [.str k, v] => some (k, dec v) | _ => none)
        | _ => dict []
      | some (.str "frame") => match fs.lookup "cols" with
        | some (.arr cs) => table (cs.filterMap column)
        | _ => table []
      | _ => dict (fs.map fun (k, v) => (k, dec v))

  /-- a table's column as the host sends it: its name, a type, the plain values, the absences as index lists — or
   a column of cells -/
  partial def column : Json → Option (String × List Value)
    | .obj o =>
      let name := match o.lookup "name" with | some (.str n) => n | _ => ""
      let list (k : String) : List Json := match o.lookup k with | some (.arr xs) => xs | _ => []
      let isD := match o.lookup "type" with | some (.str "d") => true | _ => false
      match o.lookup "cells" with
      | some (.arr xs) => some (name, xs.map dec)
      | _ =>
        let plain := (list "values").map fun x => if isD then asDouble (dec x) else dec x
        let marks := (list "na").filterMap (fun j => j.nat?.map (·, null))
          ++ (list "nan").filterMap (fun j => j.nat?.map (·, double (0.0 / 0.0)))
        some (name, marks.foldl (fun vs (i, v) => vs.set i v) plain)
    | .arr [.str name, .arr vs] => some (name, vs.map dec)
    | _ => none
end

/-- a number, an integer or a double -/
def toFloat? : Value → Option Float
  | int n => some (Float.ofInt n)
  | double d => some d
  | _ => none

/-- an integer, or a double that is a whole number -/
def toInt? : Value → Option Int
  | int n => some n
  | double d => if d == d.round then some (if d < 0 then -((-d).toUInt64.toNat : Int) else (d.toUInt64.toNat : Int))
    else none
  | _ => none

/-- the named column of a table -/
def col? (name : String) : Value → Option (List Value)
  | table cs => cs.lookup name
  | _ => none

end Value
end Okay.Wire
