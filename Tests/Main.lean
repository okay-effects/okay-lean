import Okay

open Okay.Effects Okay.Effects.Free

/-- in any row that has these three, at any place -/
def greet [In (Reader String) R] [In (Writer String) R] [In (State Nat) R] : Nat ! R := do
  let name : String ← ask
  tell s!"hello, {name}"
  let n : Nat ← get
  put (n + name.length)
  pure n

abbrev Greeting : Row := [Reader String, State Nat, Writer String]

def greeting : Nat × Nat × List String :=
  let (( n, s), ws) := run (writer String (state 10 (reader "Ann" (greet (R := Greeting)))))
  (n, s, ws)

def pythagorean [In Choose R] (n : Nat) : (Nat × Nat × Nat) ! R := do
  let a ← among (List.range n)
  let b ← among (List.range n)
  let c ← among (List.range n)
  guard (0 < a && a ≤ b && a * a + b * b == c * c)
  pure (a, b, c)

def safeDiv [In (Error String) R] (a b : Nat) : Nat ! R :=
  if b == 0 then raise "division by zero" else pure (a / b)

/-- an effect of one's own: the handler sees its operations by dependent matching, nothing else -/
inductive Console : Type → Type
  | readLine : Console String
  | print (s : String) : Console Unit

def echo [In Console R] : Unit ! R := do
  let s ← perform Console.readLine
  perform (Console.print s)

def scripted [Split Console R Rest] (input : String) : A ! R → (A × List String) ! Rest :=
  answerWith (E := Console) (S := List String) (fun a out => pure (a, out.reverse))
    (fun out op => match op with
      | .readLine => (input, out)
      | .print s => ((), s :: out))
    []

/-- a handler resuming many times, and the state under it: each branch its own state -/
def branches [In Choose R] [In (State Nat) R] : Nat ! R := do
  let x ← among [1, 2, 3]
  modify (· + x)
  get (S := Nat)

def check (name : String) (ok : Bool) : IO Bool := do
  IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
  pure ok

def main : IO UInt32 := do
  let rs ← [
    check "greet: reader, state, writer at their places" (greeting == (10, 13, ["hello, Ann"])),
    check "state alone" (run (state 1 (modify (· + 1) >>= fun _ => get (R := [State Nat]))) == (2, 2)),
    check "attempt: a value" (run (attempt String (safeDiv (R := [Error String]) 6 3)) == .inr 2),
    check "attempt: an error" (run (attempt String (safeDiv (R := [Error String]) 6 0)) == .inl "division by zero"),
    check "all: every pythagorean triple under 20"
      (run (all (pythagorean (R := [Choose]) 20)) == [(3, 4, 5), (5, 12, 13), (6, 8, 10), (8, 15, 17), (9, 12, 15)]),
    check "first" (run (first (pythagorean (R := [Choose]) 20)) == some (3, 4, 5)),
    check "first: none" (run (first (pythagorean (R := [Choose]) 3)) == none),
    check "optional: aborted"
      (run (optional ((do let _ ← abort (X := Nat); pure 1) : Nat ! [Abort])) == none),
    check "optional: a value" (run (optional (pure 1 : Nat ! [Abort])) == some 1),
    check "an effect of one's own" (run (scripted "hi" (echo (R := [Console]))) == ((), ["hi"])),
    check "state outside choose: one state across branches"
      (run (state 0 (all (branches (R := [Choose, State Nat])))) == ([1, 3, 6], 6)),
    check "state inside choose: a state per branch"
      (run (all (state 0 (branches (R := [State Nat, Choose])))) == [(1, 1), (2, 2), (3, 3)]),
    check "the error under the state: the state kept"
      (run (state 5 (attempt String (do modify (· + 1); raise "no"; pure 0 : Nat ! [Error String, State Nat])))
        == (.inl "no", 6)),
    check "the state under the error: the state lost"
      (run (attempt String (state 5 (do modify (· + 1); raise "no"; pure 0 : Nat ! [State Nat, Error String])))
        == .inl "no")
  ].mapM id
  if rs.all id then
    IO.println s!"{rs.length} checks passed"
    pure 0
  else
    pure 1
