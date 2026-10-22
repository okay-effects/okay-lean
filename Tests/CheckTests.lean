import Okay.Check

/-! The second checker: decimals rounded as `java.math.BigDecimal` rounds them, and okay-proof's certificates —
written by okay-proof, kept in `Tests/certificates` — checked again, a tampered one refused. -/

open Okay.Check

namespace CheckTests

def dec (s : String) : Dec := (Dec.parse? s).get!

def checks : IO (List Bool) := do
  let check (name : String) (ok : Bool) (got : String := "") : IO Bool := do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}{if ok || got.isEmpty then "" else s!": got {got}"}"
    pure ok
  let read (f : String) : IO (Except String Certificate.Report) := do
    pure (Certificate.check (← IO.FS.readFile s!"Tests/certificates/{f}.json"))
  let accepted (f : String) : IO Bool := do
    match ← read f with
    | .ok _ => check s!"certificate {f}: checked again" true
    | .error why => check s!"certificate {f}: checked again" false why
  let tampered ← read "tampered"
  let pugh ← read "pugh"
  pure [
    ← check "decimals: half to even, half up away from zero, a negative scale, a division to a scale"
      ((dec "2.345").setScale 2 .halfEven == dec "2.34" && (dec "2.355").setScale 2 .halfEven == dec "2.36"
        && (dec "-2.345").setScale 2 .halfUp == dec "-2.35" && (dec "1250").setScale (-2) .halfEven == dec "1200"
        && Dec.divScale (dec "10") (dec "3") 2 == dec "3.33" && (dec "1000.00").plain == "1000"
        && (dec "-0.050").plain == "-0.05"),
    ← accepted "policy", ← accepted "induction", ← accepted "le-total", ← accepted "products", ← accepted "mod-hat",
    ← check "Pugh's refutation, 1016 steps: checked again"
      (match pugh with | .ok r => r.steps == 1016 | .error _ => false),
    ← check "a tampered certificate (an amount over the limit) is refused"
      (match tampered with | .error why => why.startsWith "step " | .ok _ => false) ]

end CheckTests
