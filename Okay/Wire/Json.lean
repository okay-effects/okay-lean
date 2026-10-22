/-!
# JSON, as okay's wire writes it

The far side's own JSON, of no dependency (as okay's Haskell worker has its own): a number is kept as its TEXT, so an
integer of any size crosses exactly, and a value reads it as an integer or a double (`Value.dec`).
-/

namespace Okay.Wire

/-- a JSON tree: a number its text -/
inductive Json where
  | null
  | bool (b : Bool)
  | num (text : String)
  | str (s : String)
  | arr (xs : List Json)
  | obj (fields : List (String × Json))
  deriving Inhabited, Repr

namespace Json

/-- the field `k` of an object -/
def get? (j : Json) (k : String) : Option Json :=
  match j with
  | obj fs => fs.lookup k
  | _ => none

/-- a whole number, from a number's text up to its point -/
def nat? : Json → Option Nat
  | num t => (String.ofList (t.toList.takeWhile (· != '.'))).toNat?
  | _ => none

/-! ## Reading -/

private def isWs (c : Char) : Bool := c == ' ' || c == '\n' || c == '\r' || c == '\t'

private def skip : List Char → List Char
  | c :: r => if isWs c then skip r else c :: r
  | [] => []

private def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def hex4 : List Char → Option (Nat × List Char)
  | a :: b :: c :: d :: r => do
    let x ← hexVal a; let y ← hexVal b; let z ← hexVal c; let w ← hexVal d
    pure (((x * 16 + y) * 16 + z) * 16 + w, r)
  | _ => none

/-- a string's characters after its opening quote, escapes read; a surrogate pair one character -/
private partial def strBody (acc : String) : List Char → Option (String × List Char)
  | '"' :: r => some (acc, r)
  | '\\' :: c :: r =>
    match c with
    | 'n' => strBody (acc.push '\n') r
    | 't' => strBody (acc.push '\t') r
    | 'r' => strBody (acc.push '\r') r
    | 'b' => strBody (acc.push (Char.ofNat 8)) r
    | 'f' => strBody (acc.push (Char.ofNat 12)) r
    | 'u' => do
      let (n, r) ← hex4 r
      if 0xD800 ≤ n ∧ n < 0xDC00 then
        match r with
        | '\\' :: 'u' :: r' => do
          let (m, r'') ← hex4 r'
          strBody (acc.push (Char.ofNat (0x10000 + (n - 0xD800) * 0x400 + (m - 0xDC00)))) r''
        | _ => strBody (acc.push (Char.ofNat n)) r
      else strBody (acc.push (Char.ofNat n)) r
    | c => strBody (acc.push c) r
  | c :: r => strBody (acc.push c) r
  | [] => none

private def numChar (c : Char) : Bool :=
  c.isDigit || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E'

mutual
  private partial def value : List Char → Option (Json × List Char)
    | 'n' :: 'u' :: 'l' :: 'l' :: r => some (.null, skip r)
    | 't' :: 'r' :: 'u' :: 'e' :: r => some (.bool true, skip r)
    | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: r => some (.bool false, skip r)
    | '"' :: r => (strBody "" r).map fun (s, r) => (.str s, skip r)
    | '[' :: r => array [] (skip r)
    | '{' :: r => object [] (skip r)
    | c :: r =>
      if c == '-' || c.isDigit then
        let n := (c :: r).takeWhile numChar
        some (.num (String.ofList n), skip ((c :: r).drop n.length))
      else none
    | [] => none

  private partial def array (acc : List Json) : List Char → Option (Json × List Char)
    | ']' :: r => some (.arr acc.reverse, skip r)
    | r => do
      let (j, r) ← value r
      match r with
      | ',' :: r => array (j :: acc) (skip r)
      | ']' :: r => some (.arr (j :: acc).reverse, skip r)
      | _ => none

  private partial def object (acc : List (String × Json)) : List Char → Option (Json × List Char)
    | '}' :: r => some (.obj acc.reverse, skip r)
    | '"' :: r => do
      let (k, r) ← strBody "" r
      match skip r with
      | ':' :: r => do
        let (v, r) ← value (skip r)
        match r with
        | ',' :: r => object ((k, v) :: acc) (skip r)
        | '}' :: r => some (.obj ((k, v) :: acc).reverse, skip r)
        | _ => none
      | _ => none
    | _ => none
end

/-- a JSON text, whole -/
def parse (s : String) : Except String Json :=
  match value (skip s.toList) with
  | some (j, []) => .ok j
  | some (_, r) => .error s!"text after a JSON value: {String.ofList (r.take 20)}"
  | none => .error "not JSON"

/-! ## Writing -/

private def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

private def escape (s : String) : String :=
  s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\""
    else if c == '\\' then acc ++ "\\\\"
    else if c == '\n' then acc ++ "\\n"
    else if c == '\r' then acc ++ "\\r"
    else if c == '\t' then acc ++ "\\t"
    else if c.toNat < 0x20 then (acc ++ "\\u00").push (hexDigit (c.toNat / 16)) |>.push (hexDigit (c.toNat % 16))
    else acc.push c) ""

/-- one line of JSON: no newline in it, a string's own escaped -/
partial def render : Json → String
  | null => "null"
  | bool b => if b then "true" else "false"
  | num t => t
  | str s => "\"" ++ escape s ++ "\""
  | arr xs => "[" ++ ",".intercalate (xs.map render) ++ "]"
  | obj fs => "{" ++ ",".intercalate (fs.map fun (k, v) => "\"" ++ escape k ++ "\":" ++ render v) ++ "}"

end Json
end Okay.Wire
