import Okay.Effects.Free
import Okay.Wire.Value

/-!
# The host's operations, and a program stepped

`Host` is the effect of operations BY NAME — what okay's wire carries: a program of Lean performs `call "price_of"
[sku]`, and whoever hosts it answers (okay's handlers across the wire, or a Lean handler). `Wire` gives a typed effect
its names and its answers' reading, `remote` sends it to the host. `step` runs a program of one effect to its value or
its first operation and the rest — okay-kernel's `Done` and `Yield(op, k)`; the rest is a pure function, so it is
resumed any number of times.
-/

namespace Okay.Wire

open Okay.Effects

/-- the operations a host answers by name -/
inductive Host : Type → Type
  /-- the operation `name` with its arguments: the host's answer, or its failure where the operation is -/
  | request (name : String) (args : List Value) : Host (Except Condition Value)
  /-- the program fails, by name: the run ends with the condition — no answer, `Empty`, so nothing goes on after it -/
  | fail (c : Condition) : Host Empty

/-- the operation `name`, its answer or the host's failure -/
def request [In Host R] (name : String) (args : List Value) : (Except Condition Value) ! R :=
  perform (Host.request name args)

/-- the run fails with the condition `c` -/
def failure [In Host R] (c : Condition) : X ! R := do
  let e ← perform (Host.fail c)
  nomatch e

/-- the run fails with a condition by name -/
def failWith [In Host R] (kind message : String) : X ! R := failure ⟨kind, message⟩

/-- the operation `name`, its answer; the host's failure the program's -/
def call [In Host R] (name : String) (args : List Value) : Value ! R := do
  match ← request name args with
  | .ok v => pure v
  | .error c => failure c

/-- an effect whose operations cross the wire: each one's name and arguments, and its answer read back at its type -/
class Wire (E : Effect) where
  name : {X : Type} → E X → String
  args : {X : Type} → E X → List Value
  answer : {X : Type} → E X → Value → Except String X

/-- `E` sent to the host: each operation a request by name, its answer read at its type — one that does not read is
the run's failure, `TypeError`; the host's failure the program's -/
def remote [Wire E] [Split E R Rest] [In Host Rest] : A ! R → A ! Rest :=
  Free.handle (E := E) pure fun op k => do
    match ← request (R := Rest) (Wire.name op) (Wire.args op) with
    | .ok v => match Wire.answer op v with
      | .ok x => k x
      | .error why => failWith "TypeError" s!"{Wire.name op}: {why}"
    | .error c => failure c

/-- a program of the one effect `E`, stepped: its value, or its first operation and the rest -/
inductive Step (E : Effect) (A : Type) : Type 1
  | done (a : A)
  | op {X : Type} (o : E X) (k : X → A ! [E])

/-- an operation of the row `[E]`, at its only place: `E`'s -/
def Step.at : Place E' [E] Rest → E' X → (X → A ! [E]) → Step E A
  | .last, o, k => .op o k
  | .init p, _, _ => nomatch p

/-- `step`, as it runs: the loop of `run`, stopping at an operation -/
unsafe def stepImpl [Inhabited A] : A ! [E] → Step E A
  | .ret a => .done a
  | .delay q => stepImpl (q ())
  | .op pl o => Step.at pl o .ret
  | .impure pl o k => Step.at pl o k
  | .bind m f =>
    match m with
    | .ret x => stepImpl (f x)
    | .delay q => stepImpl (.bind (q ()) f)
    | .bind m2 f2 => stepImpl (.bind m2 fun y => .bind (f2 y) f)
    | .op pl o => Step.at pl o f
    | .impure pl o k => Step.at pl o fun x => (k x).andThen f

/-- a program of one effect, stepped: its normal form's first node -/
@[implemented_by stepImpl]
def step [Inhabited A] (p : A ! [E]) : Step E A :=
  match Free.norm p with
  | .ret a => .done a
  | .impure pl o k => Step.at pl o k
  | .op pl o => Step.at pl o .ret
  | _ => .done default

/-- a program of one effect run in `IO`, each operation answered by `h` -/
partial def runIO [Inhabited A] (h : {X : Type} → E X → IO X) (p : A ! [E]) : IO A := do
  match step p with
  | .done a => pure a
  | .op o k => runIO h (k (← h o))

end Okay.Wire
