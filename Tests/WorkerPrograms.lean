import Okay

/-!
# The conformance programs (okay's `WireConformance`), in Lean

`pairs` two choices; `total` a TYPED effect sent to the host (`Shop`, its `Wire`); `boom` a failure by name; `scale` a
table call; `counter` a value held by the host, `describe` reading it.
-/

open Okay.Effects Okay.Wire

namespace Conformance

def num (v : Value) : Float := v.toFloat?.getD 0
def int (v : Value) : Int := v.toInt?.getD 0

/-- two choices: okay's handler continues each rest twice -/
def pairs : Program := fun _ => do
  let x ← call "choose" [.list [.int 1, .int 2]]
  let y ← call "choose" [.list [.int 10, .int 20]]
  pure (.int (int x + int y))

/-- a typed effect, its operations the host's callbacks -/
inductive Shop : Type → Type
  | priceOf (sku : String) : Shop Float
  | discount (amount : Float) : Shop Float

instance : Wire Shop where
  name := fun op => match op with
    | .priceOf _ => "price_of"
    | .discount _ => "discount"
  args := fun op => match op with
    | .priceOf sku => [.str sku]
    | .discount a => [.double a]
  answer := fun op v => match op with
    | .priceOf _ => match v.toFloat? with | some f => .ok f | none => .error "not a number"
    | .discount _ => match v.toFloat? with | some f => .ok f | none => .error "not a number"

/-- `price_of(sku)`, then `discount(price * qty)`: typed here, sent by `remote` -/
def totalOf (sku : String) (qty : Float) : Float ! [Shop, Host] := do
  let price ← perform (Shop.priceOf sku)
  perform (Shop.discount (price * qty))

def total : Program
  | [.str sku, qty] => Value.double <$> remote (E := Shop) (totalOf sku (num qty))
  | _ => failWith "ValueError" "total takes a sku and a quantity"

def boom : Program := fun _ => failWith "LeanError" "lean says no"

/-- a TABLE call: a program that answers without performing is a function -/
def scale : Program
  | [frame, k] => match frame.col? "x" with
    | some xs => pure (.table [("x", xs.map fun x => .int (int x * int k))])
    | none => failWith "ValueError" "scale takes a frame with a column x"
  | _ => failWith "ValueError" "scale takes a frame and a factor"

/-- a HELD value (the number itself), and a function reading it -/
def counter : Program
  | [n] => pure n
  | _ => failWith "ValueError" "counter takes a number"

def describe : Program
  | [c, k] => pure (.int (int c + int k))
  | _ => failWith "ValueError" "describe takes a held value and a number"

def worker : Worker :=
  ⟨[("pairs", pairs), ("total", total), ("boom", boom), ("scale", scale), ("counter", counter),
    ("describe", describe)]⟩

end Conformance
