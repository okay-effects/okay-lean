import Okay.Effects.Free

/-!
# THE STANDARD EFFECTS, written once on the interface

Each effect a GADT of its operations, indexed by the answer; its words `perform` at any place in the row; each
handler taking its effect from anywhere in the row, `[Split E R Rest]`. The implementation knows nothing of them.
-/
namespace Okay.Effects

/-! ## State -/

inductive State (S : Type) : Type → Type
  | get : State S S
  | put (s : S) : State S Unit

def get [In (State S) R] : S ! R := perform State.get
def put [In (State S) R] (s : S) : Unit ! R := perform (State.put s)
def modify [In (State S) R] (f : S → S) : Unit ! R := do put (f (← get))
def gets [In (State S) R] (f : S → A) : A ! R := do pure (f (← get))

/-- the state from `s0`, the value and the state at the end -/
def state [Split (State S) R Rest] (s0 : S) : A ! R → (A × S) ! Rest :=
  Free.answerWith (E := State S) (fun a s => pure (a, s))
    (fun s op => match op with
      | .get => (s, s)
      | .put s' => ((), s'))
    s0

/-! ## Reader -/

inductive Reader (E : Type) : Type → Type
  | ask : Reader E E

def ask [In (Reader E) R] : E ! R := perform Reader.ask

def reader [Split (Reader E) R Rest] (e : E) : A ! R → A ! Rest :=
  Free.answer (E := Reader E) pure fun | .ask => e

/-! ## Writer -/

inductive Writer (W : Type) : Type → Type
  | tell (w : W) : Writer W Unit

def tell [In (Writer W) R] (w : W) : Unit ! R := perform (Writer.tell w)

/-- the value and what was told, in order -/
def writer (W : Type) [Split (Writer W) R Rest] : A ! R → (A × List W) ! Rest :=
  Free.answerWith (E := Writer W) (S := List W) (fun a ws => pure (a, ws.reverse))
    (fun ws op => match op with | .tell w => ((), w :: ws))
    []

/-! ## Error -/

inductive Error (E : Type) : Type → Type
  | raise {X : Type} (e : E) : Error E X

def raise [In (Error E) R] (e : E) : X ! R := perform (Error.raise e)

/-- the value, or the error raised, the rest dropped -/
def attempt (E : Type) [Split (Error E) R Rest] : A ! R → (E ⊕ A) ! Rest :=
  Free.handle (E := Error E) (fun a => pure (.inr a)) fun | .raise e, _ => pure (.inl e)

/-! ## Choose -/

inductive Choose : Type → Type
  | among {X : Type} (xs : List X) : Choose X

def among [In Choose R] (xs : List X) : X ! R := perform (Choose.among xs)
def fail [In Choose R] : X ! R := among []
def guard [In Choose R] (c : Bool) : Unit ! R := if c then pure () else fail

/-- every value, the rest resumed once per choice -/
def all [Split Choose R Rest] : A ! R → (List A) ! Rest :=
  Free.handle (E := Choose) (fun a => pure [a]) fun | .among xs, k => go xs k
where
  go {X : Type} : List X → (X → (List A) ! Rest) → (List A) ! Rest
    | [], _ => pure []
    | x :: xs, k => do pure ((← k x) ++ (← go xs k))

/-- the first value, the choices tried in order -/
def first [Split Choose R Rest] : A ! R → (Option A) ! Rest :=
  Free.handle (E := Choose) (fun a => pure (some a)) fun | .among xs, k => go xs k
where
  go {X : Type} : List X → (X → (Option A) ! Rest) → (Option A) ! Rest
    | [], _ => pure none
    | x :: xs, k => do
      match ← k x with
      | some a => pure (some a)
      | none => go xs k

/-! ## Abort -/

inductive Abort : Type → Type
  | exit {X : Type} : Abort X

def abort [In Abort R] : X ! R := perform Abort.exit

/-- `some` the value, `none` if aborted -/
def optional [Split Abort R Rest] : A ! R → (Option A) ! Rest :=
  Free.handle (E := Abort) (fun a => pure (some a)) fun | .exit, _ => pure none

/-! ## Laws: what each handler makes of its effect's operations, by computation -/

section Laws
variable {R : Row}

theorem state_get (s : S) : state s (get : S ! [State S]) = pure (s, s) := rfl
theorem state_put (s s' : S) : state s (put s' : Unit ! [State S]) = pure ((), s') := rfl
theorem reader_ask (e : E) : reader e (ask : E ! [Reader E]) = pure e := rfl
theorem writer_tell (w : W) : writer W (tell w : Unit ! [Writer W]) = pure ((), [w]) := rfl
theorem attempt_raise (e : E) : attempt E (raise e : A ! [Error E]) = pure (.inl e) := rfl
theorem optional_abort : optional (abort : A ! [Abort]) = pure none := rfl
theorem first_fail : first (fail : A ! [Choose]) = pure none := rfl

/-- a choice among values is all of them -/
theorem all_among (xs : List A) : all (among xs : A ! [Choose]) = pure xs := by
  show all.go xs _ = pure xs
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [all.go, ih]; rfl

end Laws

end Okay.Effects
