import Okay.Wire.Worker

/-!
# Lean as the host: another's program under Lean's handlers

okay-kernel's import: a program of another implementation — a far side over the wire, okay's or Lean's own — run
here as a program of Lean. Its operations are `request`s of the Lean program, answered by Lean's handlers (`answering`
by name), as many times as they resume — `all` resumes a far rest twice, and the far side continues it twice. The wire
itself is the effect `Remote`, run in `IO` over a `Link` by `runRemote`.
-/

namespace Okay.Wire

open Okay.Effects

instance [Inhabited A] : Inhabited (A ! R) := ⟨.ret default⟩

/-- the host's half of the wire, as an effect: a request sent, its answer; a fresh run's number -/
inductive Remote : Type → Type
  | send (req : Json) : Remote Json
  | fresh : Remote Nat

private def num (n : Nat) : Json := .num (toString n)

private def conditionOf (c : Json) : Condition :=
  ⟨(match c.get? "kind" with | some (.str s) => s | _ => "Condition"),
    (match c.get? "message" with | some (.str s) => s | _ => "")⟩

/-- the far side's program `fn`, run as this program: each operation it performs a `request` here, answered by
this program's handlers — its value, or its failure -/
partial def foreign [In Remote R] [In Host R] (fn : String) (args : List Value) : (Except Condition Value) ! R := do
  let run ← perform Remote.fresh
  let reply ← perform (Remote.send (.obj [("op", .str "program"), ("run", num run), ("fn", .str fn),
    ("args", .arr (args.map Value.enc))]))
  walk run reply
where
  walk (run : Nat) (reply : Json) : (Except Condition Value) ! R :=
    match reply.get? "ok", reply.get? "condition" with
    | some ok, _ =>
      match ok.get? "done", ok.get? "perform" with
      | some v, _ => pure (.ok (Value.dec v))
      | none, some (.str n) => do
        let as := match ok.get? "args" with | some (.arr xs) => xs.map Value.dec | _ => []
        let k := (ok.get? "k").getD .null
        let answer ← request n as
        let tail := match answer with
          | .ok v => [("answer", v.enc)]
          | .error c => [("condition", .obj [("kind", .str c.kind), ("message", .str c.message)])]
        let reply ← perform (Remote.send (.obj ([("op", .str "continue"), ("run", num run), ("k", k)] ++ tail)))
        walk run reply
      | _, _ => pure (.error ⟨"ValueError", s!"not a program's node: {ok.render}"⟩)
    | none, some c => pure (.error (conditionOf c))
    | none, none => pure (.error ⟨"ValueError", s!"neither an answer nor a condition: {reply.render}"⟩)

/-- the far side's function `fn` called: its value, which it answers without performing -/
def foreignCall [In Remote R] (fn : String) (args : List Value) : (Except Condition Value) ! R := do
  let reply ← perform (Remote.send (.obj [("op", .str "call"), ("fn", .str fn), ("args", .arr (args.map Value.enc))]))
  match reply.get? "ok", reply.get? "condition" with
  | some v, _ => pure (.ok (Value.dec v))
  | none, some c => pure (.error (conditionOf c))
  | none, none => pure (.error ⟨"ValueError", s!"neither an answer nor a condition: {reply.render}"⟩)

/-- the requests of a program answered here, by name: `f` the answer's program, at the rest of the row; a failure
the program's end -/
def answering [Split Host R Rest] (f : String → List Value → (Except Condition Value) ! Rest) :
    A ! R → (Except Condition A) ! Rest :=
  Free.handle (E := Host) (fun a => pure (.ok a)) fun op k =>
    match op, k with
    | .request n as, k => f n as >>= k
    | .fail c, _ => pure (.error c)

/-- a link to a far side: its hello, one request line out and its answer line in -/
structure Link where
  hello : Json
  roundTrip : String → IO String
  close : IO Unit

/-- a far side started as a child process, its pipes the link; refused if it speaks another wire's version -/
def Link.spawn (cmd : String) (args : Array String := #[]) : IO Link := do
  let child ← IO.Process.spawn { cmd, args, stdin := .piped, stdout := .piped, stderr := .inherit }
  let (stdin, child) ← child.takeStdin
  let hello ← IO.ofExcept (Json.parse (← child.stdout.getLine))
  unless (hello.get? "shim").bind Json.nat? == some shimVersion do
    child.kill
    throw (IO.userError s!"the far side speaks the wire's version {((hello.get? "shim").getD .null).render}, not {shimVersion}")
  let roundTrip (line : String) : IO String := do
    stdin.putStrLn line
    stdin.flush
    let answer ← child.stdout.getLine
    if answer.isEmpty then throw (IO.userError "the far side is gone")
    pure answer
  pure { hello, roundTrip, close := do child.kill; let _ ← child.wait }

/-- a program over a link, in `IO`: each `send` one exchange, its request numbered here; each `fresh` a new run; at
the end each run's rests forgotten on the far side -/
def runRemote [Inhabited A] (link : Link) (p : A ! [Remote]) : IO A := do
  let ids ← IO.mkRef 0
  let runs ← IO.mkRef ([] : List Nat)
  let next : IO Nat := ids.modifyGet fun n => (n + 1, n + 1)
  let exchange (fields : List (String × Json)) : IO Json := do
    let i ← next
    IO.ofExcept (Json.parse (← link.roundTrip (Json.obj (("id", num i) :: fields)).render))
  let h : {X : Type} → Remote X → IO X := fun o =>
    match o with
    | .send (.obj fs) => exchange fs
    | .send j => exchange [("req", j)]
    | .fresh => do let r ← next; runs.modify (r :: ·); pure r
  let a ← runIO h p
  for r in ← runs.get do
    let _ ← exchange [("op", .str "forget"), ("run", num r)]
  pure a

end Okay.Wire
