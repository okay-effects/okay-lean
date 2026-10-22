import Std.Data.HashMap
import Okay.Wire.Host

/-!
# A worker: Lean programs served on okay's wire

okay's host (`ForeignWorker`: over a child's pipes, a socket, or this library in its own process through FFM) starts a
program by name; each operation the program performs goes to the host as `perform`, its rest kept here under an id; the
host runs it under its own handlers and `continue`s that rest — the same one any number of times, the rest being a pure
function; `forget` drops a run's rests. A program's failure (`failWith`) is a condition by name, and the worker lives
on. Also served: a `call` (a program that answers without performing), a value `held` for the host and `release`d, and
`configure` of the wire (JSON lines, no compression — what the hello says).
-/

namespace Okay.Wire

open Okay.Effects

/-- the wire's version this worker speaks; okay's hosts refuse another -/
def shimVersion : Nat := 9

/-- a program the host may start by name: its arguments in, a program over the host's operations out -/
abbrev Program := List Value → Value ! [Host]

/-- a worker: the programs it serves, by name -/
structure Worker where
  programs : List (String × Program)

/-- the rest of a run, kept until the host forgets the run: the host's answer in, the program on -/
abbrev Resumption := Except Condition Value → Value ! [Host]

/-- what a worker keeps between requests -/
structure Worker.State where
  rests : Std.HashMap (Nat × Nat) Resumption := {}
  next : Nat := 0
  held : Std.HashMap Nat Value := {}
  nextRef : Nat := 0

/-- the worker's first line: who it is, what it speaks -/
def hello : Json :=
  .obj [("shim", .num (toString shimVersion)), ("python", .str "lean"),
    ("speaks", .obj [("format", .arr [.str "json"]), ("compress", .arr []), ("frames", .arr [.str "columnar"])])]

private def num (n : Nat) : Json := .num (toString n)

private def condition (rid : Json) (kind message : String) : Json :=
  .obj [("id", rid), ("condition", .obj [("kind", .str kind), ("message", .str message)])]

/-- a program by its name, or by `module:name` -/
def Worker.find? (w : Worker) (fn : String) : Option Program :=
  match w.programs.lookup fn with
  | some p => some p
  | none => w.programs.lookup (String.ofList ((fn.toList.dropWhile (· != ':')).drop 1))

/-- a stepped program as the host reads it: its value, or its operation with the id of its rest, kept here -/
private def node (st : Worker.State) (run : Nat) : Step Host Value → Worker.State × Except Condition Json
  | .done v => (st, .ok (.obj [("done", v.enc)]))
  | .op (Host.request n as) k =>
    let i := st.next + 1
    ({ st with next := i, rests := st.rests.insert (run, i) k },
      .ok (.obj [("perform", .str n), ("args", .arr (as.map Value.enc)), ("k", num i)]))
  | .op (Host.fail c) _ => (st, .error c)

/-- a request's arguments, each ref's held value in its place -/
private def argsOf (st : Worker.State) (req : Json) : Except Condition (List Value) :=
  let xs := match req.get? "args" with | some (.arr xs) => xs | _ => []
  xs.mapM fun j =>
    match j.get? "t" with
    | some (.str "ref") =>
      match (j.get? "id").bind Json.nat? with
      | some i => match st.held[i]? with
        | some v => .ok v
        | none => .error ⟨"LookupError",
            s!"ref {i} is not held by this worker (released, or held by a process that is gone)"⟩
      | none => .error ⟨"LookupError", "a ref with no id"⟩
    | _ => .ok (Value.dec j)

/-- one request, its answer; the worker's state on -/
def Worker.serve1 (w : Worker) (st : Worker.State) (line : String) : Worker.State × Json :=
  match Json.parse line with
  | .error why => (st, condition .null "ValueError" why)
  | .ok req =>
    let rid := (req.get? "id").getD .null
    let reply (r : Worker.State × Except Condition Json) : Worker.State × Json :=
      match r.2 with
      | .ok j => (r.1, .obj [("id", rid), ("ok", j)])
      | .error c => (r.1, condition rid c.kind c.message)
    let refuse (kind msg : String) := reply (st, .error ⟨kind, msg⟩)
    let run? := (req.get? "run").bind Json.nat?
    match req.get? "op" with
    | some (.str "program") =>
      match run?, req.get? "fn" with
      | some run, some (.str fn) =>
        match w.find? fn with
        | some p => match argsOf st req with
          | .ok args => reply (node st run (step (p args)))
          | .error c => reply (st, .error c)
        | none => refuse "LookupError" s!"no program named '{fn}' in this worker"
      | _, _ => refuse "ValueError" "a program request names its run and its fn"
    | some (.str "continue") =>
      match run?, (req.get? "k").bind Json.nat? with
      | some run, some k =>
        match st.rests[(run, k)]? with
        | some rest =>
          let answer : Except Condition Value :=
            match req.get? "condition" with
            | some c@(.obj _) =>
              .error ⟨(match c.get? "kind" with | some (.str s) => s | _ => "Condition"),
                (match c.get? "message" with | some (.str s) => s | _ => "")⟩
            | _ => .ok (Value.dec ((req.get? "answer").getD .null))
          reply (node st run (step (rest answer)))
        | none => refuse "LookupError"
            s!"continuation {k} of run {run} is not held here (forgotten, or another process)"
      | _, _ => refuse "ValueError" "a continue names its run and its k"
    | some (.str "forget") =>
      match run? with
      | some run => reply ({ st with rests := st.rests.filter fun key _ => key.1 != run }, .ok .null)
      | none => refuse "ValueError" "a forget names its run"
    | some (.str "call") =>
      match req.get? "fn" with
      | some (.str fn) =>
        match w.find? fn with
        | some p => match argsOf st req with
          | .ok args => match step (p args) with
            | .done v =>
              if req.get? "held" matches some (.bool true) then
                let i := st.nextRef + 1
                reply ({ st with nextRef := i, held := st.held.insert i v },
                  .ok (.obj [("t", .str "ref"), ("id", num i), ("type", .str "value")]))
              else reply (st, .ok v.enc)
            | .op (Host.request n _) _ =>
              refuse "ValueError" s!"'{fn}' performs '{n}': a call answers a value; run it as a program"
            | .op (Host.fail c) _ => reply (st, .error c)
          | .error c => reply (st, .error c)
        | none => refuse "LookupError" s!"no program named '{fn}' in this worker"
      | _ => refuse "ValueError" "a call names its fn"
    | some (.str "configure") =>
      match req.get? "format", req.get? "compress" with
      | some (.str "json"), some (.str "none") =>
        reply (st, .ok (.obj [("format", .str "json"), ("compress", .str "none")]))
      | some (.str f), some (.str c) =>
        refuse "ValueError" s!"this Lean worker speaks json with no compression; not {f} with {c}"
      | _, _ => refuse "ValueError" "a configure names its format and compression"
    | some (.str "release") =>
      match (req.get? "ref").bind Json.nat? with
      | some i => reply ({ st with held := st.held.erase i }, .ok .null)
      | none => reply (st, .ok .null)
    | some (.str op) => refuse "ValueError" s!"this Lean worker serves programs and calls, not '{op}'"
    | _ => refuse "ValueError" "not a request"

private def chomp (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile (fun c => c == '\n' || c == '\r')).reverse

/-- the worker on stdin/stdout: its hello first, then one line in, one line out, until the input ends -/
partial def Worker.serve (w : Worker) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStrLn hello.render
  stdout.flush
  let rec loop (st : Worker.State) : IO Unit := do
    let line ← stdin.getLine
    if line.isEmpty then return
    let (st, out) := w.serve1 st (chomp line)
    stdout.putStrLn out.render
    stdout.flush
    loop st
  loop {}

/-! ## In-process: the C ABI's Lean half

`ffi/okay_exchange.c` exports okay's in-process ABI, `okay_exchange(req, len, out_len)` and `okay_free`, over these
three; the worker is the library's own, `@[export okay_lean_worker] def worker (_ : Unit) : Worker`. -/

@[export okay_lean_hello] def ffmHello (_ : Unit) : String := hello.render
@[export okay_lean_state0] def ffmState0 (_ : Unit) : Worker.State := {}
@[export okay_lean_exchange] def ffmExchange (w : Worker) (st : Worker.State) (req : String) : Worker.State × String :=
  let (st, j) := w.serve1 st req
  (st, j.render)

end Okay.Wire
