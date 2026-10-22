import Tests.WorkerPrograms

/-!
# The wire, checked: JSON and values; a worker's requests one by one — multi-shot, failures by name, held values; and
Lean as the host of a far side in a child process (this test binary itself, run with `--worker`).
-/

open Okay.Effects Okay.Wire

namespace WireTests

def check (name : String) (ok : Bool) (got : String := "") : IO Bool := do
  IO.println s!"{if ok then "ok  " else "FAIL"} {name}{if ok || got.isEmpty then "" else s!": got {got}"}"
  pure ok

def rt (s : String) : String := match Json.parse s with | .ok j => j.render | .error e => s!"error: {e}"

def encDec (v : Value) : String := (Value.dec (Value.enc v)).enc.render

/-- a sequence of requests to the conformance worker, the answers rendered -/
def converse (reqs : List String) : List String :=
  (reqs.foldl (fun (st, out) r => let (st, j) := Conformance.worker.serve1 st r; (st, j.render :: out))
    (({} : Worker.State), ([] : List String))).2.reverse

/-- the far side's choices answered here: `all` resumes each of its rests twice -/
def chooseHere [Split Host R Rest] [In Choose Rest] (p : A ! R) : (Except Condition A) ! Rest :=
  answering (fun n as => match n, as with
    | "choose", [.list xs] => do let x ← among xs; pure (.ok x)
    | _, _ => pure (.error ⟨"LookupError", s!"no callback {n} here"⟩)) p

def checks (self : String) : IO (List Bool) := do
  let pairsRun := converse [
    "{\"id\":1,\"op\":\"program\",\"run\":7,\"fn\":\"pairs\",\"args\":[]}",
    "{\"id\":2,\"op\":\"continue\",\"run\":7,\"k\":1,\"answer\":1}",
    "{\"id\":3,\"op\":\"continue\",\"run\":7,\"k\":2,\"answer\":10}",
    "{\"id\":4,\"op\":\"continue\",\"run\":7,\"k\":1,\"answer\":2}",
    "{\"id\":5,\"op\":\"continue\",\"run\":7,\"k\":3,\"answer\":20}",
    "{\"id\":6,\"op\":\"forget\",\"run\":7}",
    "{\"id\":7,\"op\":\"continue\",\"run\":7,\"k\":1,\"answer\":1}"]
  let held := converse [
    "{\"id\":1,\"op\":\"call\",\"fn\":\"counter\",\"args\":[10],\"held\":true}",
    "{\"id\":2,\"op\":\"call\",\"fn\":\"describe\",\"args\":[{\"t\":\"ref\",\"id\":1},2]}",
    "{\"id\":3,\"op\":\"release\",\"ref\":1}",
    "{\"id\":4,\"op\":\"call\",\"fn\":\"describe\",\"args\":[{\"t\":\"ref\",\"id\":1},2]}"]
  let typed := converse [
    "{\"id\":1,\"op\":\"program\",\"run\":1,\"fn\":\"total\",\"args\":[\"tea\",3]}",
    "{\"id\":2,\"op\":\"continue\",\"run\":1,\"k\":1,\"answer\":{\"t\":\"f\",\"v\":4.0}}",
    "{\"id\":3,\"op\":\"continue\",\"run\":1,\"k\":2,\"answer\":6.5}",
    "{\"id\":4,\"op\":\"continue\",\"run\":1,\"k\":1,\"answer\":\"four\"}",
    "{\"id\":5,\"op\":\"continue\",\"run\":1,\"k\":1,\"condition\":{\"kind\":\"KeyError\",\"message\":\"no tea\"}}"]
  let others := converse [
    "{\"id\":1,\"op\":\"program\",\"run\":2,\"fn\":\"boom\",\"args\":[]}",
    "{\"id\":2,\"op\":\"program\",\"run\":3,\"fn\":\"nope\",\"args\":[]}",
    "{\"id\":3,\"op\":\"call\",\"fn\":\"pairs\",\"args\":[]}",
    "{\"id\":4,\"op\":\"call\",\"fn\":\"scale\",\"args\":[{\"t\":\"frame\",\"cols\":[{\"name\":\"x\",\"type\":\"i\",\"values\":[1,2]}]},3]}",
    "{\"id\":5,\"op\":\"configure\",\"format\":\"cbor\",\"compress\":\"none\"}",
    "{\"id\":6,\"op\":\"configure\",\"format\":\"json\",\"compress\":\"none\"}",
    "not json"]
  -- Lean as the host: the far side is this very binary, a worker on its pipes
  let link ← Link.spawn self #["--worker"]
  let viaWire ← runRemote link (all (chooseHere (foreign (R := [Host, Choose, Remote]) "pairs" [])))
  let failed ← runRemote link (answering (fun n _ => pure (.error ⟨"LookupError", s!"no callback {n} here"⟩))
    (foreign (R := [Host, Remote]) "boom" []))
  let called ← runRemote link (foreignCall (R := [Remote]) "describe" [.int 40, .int 2])
  link.close
  let shown (r : Except Condition (Except Condition Value)) : String := match r with
    | .ok (.ok v) => v.enc.render
    | .ok (.error c) | .error c => s!"{c.kind}: {c.message}"
  pure [ ← check "JSON: escapes, a surrogate pair, nesting, numbers kept as text"
      (rt "{\"a\" : [1, -2.5e3, true, null, \"q\\\"\\n\\u00e9\\ud83d\\ude00\"]}"
        == "{\"a\":[1,-2.5e3,true,null,\"q\\\"\\né😀\"]}") (rt "{\"a\":[1]}"),
    ← check "a big integer crosses as digits" (encDec (.int (2 ^ 70)) == "{\"t\":\"int\",\"v\":\"1180591620717411303424\"}"),
    ← check "a whole double stays a double; another exactly"
      (encDec (.double 6) == "{\"t\":\"f\",\"v\":6}" && encDec (.double 0.5) == "0.5"),
    ← check "a double read back is the same double" (Value.parseFloat (Value.floatText 0.1) == 0.1),
    ← check "a dict, a list, NaN" (encDec (.dict [("k", .list [.null, .double (0.0/0.0)])])
        == "{\"t\":\"dict\",\"kv\":[[\"k\",[null,{\"t\":\"nan\"}]]]}"),
    ← check "a program performs, its rest kept under k"
      (pairsRun[0]! == "{\"id\":1,\"ok\":{\"perform\":\"choose\",\"args\":[[1,2]],\"k\":1}}") pairsRun[0]!,
    ← check "MULTI-SHOT: the same rest continued twice, each to its own value"
      (pairsRun[2]! == "{\"id\":3,\"ok\":{\"done\":11}}" && pairsRun[4]! == "{\"id\":5,\"ok\":{\"done\":22}}")
      s!"{pairsRun[2]!} {pairsRun[4]!}",
    ← check "a forgotten run's rest is refused by name"
      (pairsRun[6]!.startsWith "{\"id\":7,\"condition\":{\"kind\":\"LookupError\"") pairsRun[6]!,
    ← check "a TYPED effect: its operations by name, its answers read at their types"
      (typed[0]! == "{\"id\":1,\"ok\":{\"perform\":\"price_of\",\"args\":[\"tea\"],\"k\":1}}"
        && typed[1]! == "{\"id\":2,\"ok\":{\"perform\":\"discount\",\"args\":[{\"t\":\"f\",\"v\":12}],\"k\":2}}"
        && typed[2]! == "{\"id\":3,\"ok\":{\"done\":6.5}}") s!"{typed[0]!} {typed[1]!} {typed[2]!}",
    ← check "an answer that does not read at its type is a TypeError"
      (typed[3]!.startsWith "{\"id\":4,\"condition\":{\"kind\":\"TypeError\"") typed[3]!,
    ← check "the host's failure where the operation was: the run's"
      (typed[4]! == "{\"id\":5,\"condition\":{\"kind\":\"KeyError\",\"message\":\"no tea\"}}") typed[4]!,
    ← check "a program's failure is a condition by name"
      (others[0]! == "{\"id\":1,\"condition\":{\"kind\":\"LeanError\",\"message\":\"lean says no\"}}") others[0]!,
    ← check "an unknown program is refused by name" (others[1]!.startsWith "{\"id\":2,\"condition\":{\"kind\":\"LookupError\""),
    ← check "a call that performs is refused by name" (others[2]!.startsWith "{\"id\":3,\"condition\":{\"kind\":\"ValueError\""),
    ← check "a TABLE call: a frame in, a frame out"
      (others[3]! == "{\"id\":4,\"ok\":{\"t\":\"frame\",\"cols\":[[\"x\",[3,6]]]}}") others[3]!,
    ← check "configure: CBOR refused by name, JSON kept"
      (others[4]!.startsWith "{\"id\":5,\"condition\"" && others[5]! == "{\"id\":6,\"ok\":{\"format\":\"json\",\"compress\":\"none\"}}"),
    ← check "a line that is not JSON is refused, and the worker lives on" (others[6]!.startsWith "{\"id\":null,\"condition\""),
    ← check "a HELD value: used by its ref, released, then refused by name"
      (held[0]! == "{\"id\":1,\"ok\":{\"t\":\"ref\",\"id\":1,\"type\":\"value\"}}" && held[1]! == "{\"id\":2,\"ok\":12}"
        && held[3]!.startsWith "{\"id\":4,\"condition\":{\"kind\":\"LookupError\"") s!"{held}",
    ← check "LEAN AS THE HOST: a far side's choices under Lean's `all`, each far rest continued twice"
      (viaWire.map shown == ["11", "21", "12", "22"]) s!"{viaWire.map shown}",
    ← check "a far side's failure, by name, to the Lean host" (shown failed == "LeanError: lean says no") (shown failed),
    ← check "a far side's function called" (shown (.ok called) == "42") (shown (.ok called)) ]

end WireTests
