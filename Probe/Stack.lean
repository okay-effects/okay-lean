import Okay
open Okay.Effects Okay.Effects.Free

def countState [In (State Nat) R] : Nat → Unit ! R
  | 0 => pure ()
  | n+1 => do modify (· + 1); countState n

def countReader [In (Reader Nat) R] : Nat → Nat → Nat ! R
  | 0, acc => pure acc
  | n+1, acc => do let x : Nat ← ask; countReader n (acc + x)

/-- a bind nested to the left `n` deep, built by `Nat.fold`: no list of `n` cells beside it (Scala's `Range` has none) -/
def leftNested [In (State Nat) R] (n : Nat) : Nat ! R :=
  Nat.fold n (fun _ _ p => p >>= fun a => do modify (· + 1); pure (a + 1)) (pure 0)

/-- the outermost node's kind: what forces a program built, and nothing more -/
@[noinline] def kind : A ! R → String
  | .ret _ => "ret" | .bind .. => "bind" | .op .. => "op" | .impure .. => "impure" | .delay _ => "delay"

/-- the left-nested bind timed: the build, then the run (the program dropped after it, so its freeing is the run's) -/
def leftSplit (n : Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let p := leftNested (R := [State Nat]) n
  IO.println s!"built: {kind p}"
  let t1 ← IO.monoNanosNow
  let r := run (state 0 p)
  IO.println s!"ran: {r}"
  let t2 ← IO.monoNanosNow
  IO.println s!"build {(t1 - t0).toFloat / 1e9} s, run {(t2 - t1).toFloat / 1e9} s"

def chain [In Choose R] : Nat → Nat → Nat ! R
  | 0, acc => pure acc
  | n+1, acc => do let x ← among [1]; chain n (acc + x)

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000000
  match args[1]? with
  | some "state" => IO.println (run (state 0 (countState (R := [State Nat]) n))).2
  | some "reader" => IO.println (run (reader 1 (countReader (R := [Reader Nat]) n 0)))
  | some "choose" => IO.println (run (all (chain (R := [Choose]) n 0)))
  | some "leftSplit" => leftSplit n
  | some "left" => IO.println (run (state 0 (leftNested (R := [State Nat]) n)))
  | _ => IO.println "state|reader|left"
