import Okay

/-!
# Interception and audit, checked: okay-simple's interception programs (`tck`, `Interception.scala`), the trail, a
sensitive effect under its audit with a policy — and, checked as the file is compiled, the programs that must NOT
elaborate: a sensitive effect reached any other way than through its audit.
-/

open Okay.Effects Okay.Effects.Free

namespace InterceptTests

def check (name : String) (ok : Bool) : IO Bool := do
  IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
  pure ok

abbrev SW : Row := [State Nat, Writer String]

def counter [In (State Nat) R] : Nat ! R := do
  put 1
  let n : Nat ← get
  put (n + 10)
  get

def saying [In (Writer String) R] : State Nat X → Unit ! R
  | .get => tell "get"
  | .put s => tell s!"put {s}"

/-- the state's operations told as they go, the state working as it did -/
def observed := run (writer String (state 0 (observe (E := State Nat) saying (counter (R := SW)))))

/-- two interceptors: the inner sees an operation first, then passes it to the outer -/
def nested := run (writer String (state 0
  (observe (E := State Nat) (fun _ => tell "outer")
    (observe (E := State Nat) (fun _ => tell "inner") (put 1 : Unit ! SW)))))

/-- each `ask` answered with the environment outside, doubled: another program in the operation's place -/
def doubling [In (Reader Nat) R] : A ! R → A ! R :=
  around (E := Reader Nat) fun | .ask, proceed => do pure ((← proceed) * 2)

/-- a reader answering by the reader further out, and one more: two handlers of one effect -/
def oneMore [Split (Reader Nat) R Rest] [In (Reader Nat) Rest] : A ! R → A ! Rest :=
  handle (E := Reader Nat) pure fun | .ask, k => do k ((← ask) + 1)

abbrev Two : Row := [Reader Nat, Reader Nat]

/-- no choice among more than three: the operation changed, `all` outside resuming each -/
def firstThree := run (all (around (E := Choose)
  (fun | .among xs, _ => among (xs.take 3)) (among [1, 2, 3, 4, 5, 6] : Nat ! [Choose])))

/-- a general interceptor: an operation answered here, never passed on -/
def answeredHere := run (state 5 (intercept (E := State Nat) pure
  (fun op k => match op with
    | .get => k 100
    | .put _ => k ())
  (get : Nat ! [State Nat])))

def count [In (State Nat) R] : Nat → Nat ! R
  | 0 => get
  | n + 1 => do modify (· + 1); count n

/-- an operation changed on its way: no `put` over 2 gets through -/
def capped := run (state 0 (intercept (E := State Nat) pure
  (fun op k => match op with
    | .put s => put (min s 2) >>= k
    | .get => get >>= k)
  (count (R := [State Nat]) 5)))

def asks [In (Reader Nat) R] : Nat → Nat → Nat ! R
  | 0, acc => pure acc
  | n + 1, acc => do let x : Nat ← ask; asks n (acc + x)

/-- `n` operations through an interceptor that counts them in a state: the stack does not grow -/
def many (n : Nat) := run (state 0 (reader 1
  (observe (E := Reader Nat) (fun _ => modify (· + 1)) (asks (R := [Reader Nat, State Nat]) n 0))))

/-! ## The trail -/

def said : State Nat X → X → String
  | .get, s => s!"get → {s}"
  | .put s, _ => s!"put {s}"

def trailed := run (writer String (state 0 (trail (E := State Nat) said (counter (R := SW)))))

/-- the same by the theorem: the trail is the path's, and the path computes -/
example : trailed = ((11, 11), ["put 1", "get → 1", "put 11", "get → 11"]) := by
  show run (writer String (answerWith _ _ 0 (trail _ counter))) = _
  rw [trail_path]
  rfl

def chosen : Choose X → X → String
  | .among xs, _ => s!"one of {xs.length}"

def pairs [In Choose R] : (Nat × Nat) ! R := do
  let a ← among [1, 2]
  let b ← among [10, 20]
  pure (a, b)

/-- a handler resuming many times: an entry each time a choice is answered — the trail outside `all` -/
def trailedChoices := run (writer String (all (trail (E := Choose) chosen (pairs (R := [Choose, Writer String])))))

/-- and inside `all`: a trail for each path -/
def trailedPaths := run (all (writer String (trail (E := Choose) chosen (pairs (R := [Writer String, Choose])))))

/-! ## A sensitive effect: payments -/

inductive Pay : Type → Type
  | transfer (to : String) (amount : Nat) : Pay String
  | balance : Pay Nat

def transfer [In (Sensitive Pay) R] (to : String) (amount : Nat) : String ! R := sensitive (Pay.transfer to amount)
def balance [In (Sensitive Pay) R] : Nat ! R := sensitive Pay.balance

/-- written over any row with the payments in it: it knows nothing of the audit -/
def payments [In (Sensitive Pay) R] : Nat ! R := do
  let _ ← transfer " acct-1234 " 100
  let b ← balance
  let _ ← transfer "acct-77" 5000
  pure b

def paid : Pay X → X → String
  | .transfer to amount, receipt => s!"transfer {amount} to {to} → {receipt}"
  | .balance, b => s!"balance → {b}"

def banking : Nat → Pay X → X × Nat
  | b, .transfer to amount => (s!"ok:{to}:{amount}", b - amount)
  | b, .balance => (b, b)

/-- an ordinary handler: what it takes is `Audited Pay`, so it stands only outside an audit -/
def bank [Split (Audited Pay) R Rest] (b0 : Nat) : A ! R → A ! Rest :=
  answerWith (E := Audited Pay) (fun a _ => pure a) (fun b a => banking b a.op) b0

abbrev Outside : Row := [Audited Pay, Error String, Writer String]

def audited := run (writer String (attempt String (bank 1000 (audit paid (payments (R := Sensitive Pay :: Outside))))))

/-- the policy: the account written one way, a transfer over the limit refused and told -/
def guarded [In (Error String) Rest] [In (Writer String) Rest] (limit : Nat) :
    {X : Type} → Pay X → ({Y : Type} → Pay Y → Y ! Rest) → (X → A ! Rest) → A ! Rest
  | _, .transfer to amount, pass, k =>
    if amount > limit then do
      let why := s!"refused: {amount} to {to.trimAscii.toString.toUpper} over the limit {limit}"
      tell why
      raise why
    else pass (.transfer to.trimAscii.toString.toUpper amount) >>= k
  | _, .balance, pass, k => pass .balance >>= k

def policed := run (writer String (attempt String (bank 1000
  (auditWith paid pure (guarded 1000) (payments (R := Sensitive Pay :: Outside))))))

/-- by the theorems: a sensitive operation's entry, then the rest's -/
example (g : String → Nat ! [Sensitive Pay, Audited Pay, Writer String]) :
    run (writer String (answerWith (E := Audited Pay) (fun a s => pure (a, s)) (fun b a => banking b a.op) 1000
      (audit paid (sensitive (Pay.transfer "a" 1) >>= g))))
    = told "transfer 1 to a → ok:a:1"
        (run (writer String (answerWith (E := Audited Pay) (fun a s => pure (a, s)) (fun b a => banking b a.op) 999
          (audit paid (g "ok:a:1"))))) :=
  audit_sensitive paid banking 1000 (Pay.transfer "a" 1) g

/-! ## The guarantee, by types: what does not elaborate

Each is a program that reaches a sensitive effect past its audit. `#guard_msgs` fails the build when the error is
not the one written, or is not there. -/

/--
error: failed to synthesize instance of type class
  Split (Audited Pay) [Sensitive Pay] Okay.Effects.Pure

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
-- the handler on a program not audited: no `Audited Pay` in its row
example : Nat := run (bank 1000 (payments (R := [Sensitive Pay])))

/--
error: Application type mismatch: The argument
  payments
has type
  Nat ! [Sensitive Pay]
but is expected to have type
  Nat ! Okay.Effects.Pure
in the application
  payments.run
-/
#guard_msgs in
-- run with the sensitive effect in the row
example : Nat := run (payments (R := [Sensitive Pay]))

/--
error: Type mismatch
  s
has type
  Sensitive Pay X
but is expected to have type
  Pay X
-/
#guard_msgs in
-- a handler reading a sensitive operation: it is no `Pay` to it
example : Nat ! [Sensitive Pay] → Nat ! Pure :=
  handle (E := Sensitive Pay) pure fun {X} s k => k (banking 0 (s : Pay X)).1

/--
error: Invalid `⟨...⟩` notation: The expected type
  Okay.Effects.sealing✝.1 Pay Nat
is not an inductive type

Note: This notation can only be used when the expected type is an inductive type with a single constructor
-/
#guard_msgs in
-- nor a structure to take apart
example (s : Sensitive Pay Nat) : Pay Nat := match s with | ⟨o⟩ => o

example : Sensitive Pay Nat → True := by
  intro s
  fail_if_success cases s
  trivial

/--
error: Application type mismatch: The argument
  Pay.transfer "me" 1000000
has type
  Pay String
but is expected to have type
  Audited Pay String
in the application
  perform (Pay.transfer "me" 1000000)
-/
#guard_msgs in
-- a program asking the handler past the audit: an operation of `Pay` is no `Audited Pay`
example : String ! [Audited Pay] := perform (E := Audited Pay) (Pay.transfer "me" 1000000)

/--
error: Invalid `⟨...⟩` notation: The expected type
  Okay.Effects.sealing✝.2 Pay Nat
is not an inductive type

Note: This notation can only be used when the expected type is an inductive type with a single constructor
-/
#guard_msgs in
-- nor made as one
example (o : Pay Nat) : Audited Pay Nat := ⟨o⟩

example : Audited Pay Nat → True := by
  intro a
  fail_if_success have : Audited Pay Nat := by constructor
  fail_if_success cases a
  trivial

def checks : IO (List Bool) := [
    check "observe: the operations told, passed on, the effect working as it did"
      (observed == ((11, 11), ["put 1", "get", "put 11", "get"])),
    check "observe: two interceptors, the inner first" (nested == (((), 1), ["inner", "outer"])),
    check "around: an operation's answer changed" (run (reader 21 (doubling (ask : Nat ! [Reader Nat]))) == 42),
    check "an interceptor between two handlers of one effect sees what the inner asks of the outer"
      (run (reader 10 (doubling (oneMore (ask : Nat ! Two)))) == 21),
    check "an interceptor inside both: its operation asked again goes to the inner"
      (run (reader 10 (oneMore (doubling (ask : Nat ! Two)))) == 22),
    check "around under all: the choices limited to three" (firstThree == [1, 2, 3]),
    check "intercept: an operation answered here, not passed on" (answeredHere == (100, 5)),
    check "intercept: an operation changed, then asked of the handler outside" (capped == (2, 2)),
    check "intercept in constant stack: 1 000 000 operations" (many 1000000 == (1000000, 1000000)),
    check "trail: each operation and its answer, in order"
      (trailed == ((11, 11), ["put 1", "get → 1", "put 11", "get → 11"])),
    check "trail outside a handler resuming many times: an entry each time an operation is answered"
      (trailedChoices == ([(1, 10), (1, 20), (2, 10), (2, 20)],
        ["one of 2", "one of 2", "one of 2", "one of 2", "one of 2", "one of 2"])),
    check "trail inside it: a trail for each path"
      (trailedPaths == [((1, 10), ["one of 2", "one of 2"]), ((1, 20), ["one of 2", "one of 2"]),
        ((2, 10), ["one of 2", "one of 2"]), ((2, 20), ["one of 2", "one of 2"])]),
    check "audit: a sensitive effect handled under its audit, every operation in the trail"
      (audited == (.inr 900, ["transfer 100 to  acct-1234  → ok: acct-1234 :100", "balance → 900",
        "transfer 5000 to acct-77 → ok:acct-77:5000"])),
    check "auditWith: an operation changed, one refused — told, raised, the rest dropped"
      (policed == (.inl "refused: 5000 to ACCT-77 over the limit 1000",
        ["transfer 100 to ACCT-1234 → ok:ACCT-1234:100", "balance → 900",
          "refused: 5000 to ACCT-77 over the limit 1000"]))
  ].mapM id

end InterceptTests
