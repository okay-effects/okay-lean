import Okay
open Okay.Effects Okay.Effects.Free

def countState [In (State Nat) R] : Nat → Unit ! R
  | 0 => pure ()
  | n+1 => do modify (· + 1); countState n

def countReader [In (Reader Nat) R] : Nat → Nat → Nat ! R
  | 0, acc => pure acc
  | n+1, acc => do let x : Nat ← ask; countReader n (acc + x)

def leftNested [In (State Nat) R] (n : Nat) : Nat ! R :=
  (List.range n).foldl (fun p _ => p >>= fun a => do modify (· + 1); pure (a + 1)) (pure 0)

def chain [In Choose R] : Nat → Nat → Nat ! R
  | 0, acc => pure acc
  | n+1, acc => do let x ← among [1]; chain n (acc + x)

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000000
  match args[1]? with
  | some "state" => IO.println (run (state 0 (countState (R := [State Nat]) n))).2
  | some "reader" => IO.println (run (reader 1 (countReader (R := [Reader Nat]) n 0)))
  | some "choose" => IO.println (run (all (chain (R := [Choose]) n 0)))
  | some "left" => IO.println (run (state 0 (leftNested (R := [State Nat]) n)))
  | _ => IO.println "state|reader|left"
