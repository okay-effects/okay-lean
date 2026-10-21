/-!
# THE `Free` MONAD, over rows of typed places

okay-simple's `okay.effects.free.Free` in Lean 4: a program is DATA — a value, or an operation with its rest `k` —
and its handlers interpret it. An effect is a GADT of its operations, indexed by the answer; a row is a list of
effects, the one handled next first; an operation of a row says where in it it is, `At`, so a handler matching the
place learns, by dependent pattern matching, that an operation is its own: no cast, no `Typeable`.
-/

namespace Okay.Effects

/-- an effect: its operations, a GADT indexed by the answer — `State.get : State S S` -/
abbrev Effect := Type → Type
/-- a row of effects: the one handled next first, `[State Nat, Reader String]` -/
abbrev Row := List Effect
/-- the row of no effect -/
abbrev Pure : Row := []

/-- an operation of the row `R`: the operation of an effect, and its place in `R` -/
inductive At : Row → Type → Type 1
  | here  {E : Effect} {R : Row} {X : Type} (op : E X) : At (E :: R) X
  | there {E : Effect} {R : Row} {X : Type} (op : At R X) : At (E :: R) X

/-- a program of the value `A` over the row `R`: a value, or an operation and its rest -/
inductive Free (R : Row) (A : Type) : Type 1
  | ret (a : A) : Free R A
  | impure {X : Type} (op : At R X) (k : X → Free R A) : Free R A

/-- a program of the value `A` over the row `R`: `Nat ! [State Nat, Reader String]` -/
notation:50 A:51 " ! " R:50 => Free R A

namespace Free

def bind : A ! R → (A → B ! R) → B ! R
  | ret a, f => f a
  | impure op k, f => impure op fun x => bind (k x) f

instance : Monad (Free R) where
  pure := ret
  bind := bind

/-- a program of no effect: its value. An operation of it there is none -/
def run : A ! Pure → A
  | ret a => a
  | impure op _ => nomatch op

end Free

/-- the place of `E` in `R`, and `R` without it `Rest`: the first, or one further in -/
inductive Place : Effect → Row → Row → Type 1
  | last {E : Effect} {R : Row} : Place E (E :: R) R
  | init {E G : Effect} {R Rest : Row} (p : Place E R Rest) : Place E (G :: R) (G :: Rest)

namespace Place

/-- `E`'s operation at its place in `R` -/
def inject : Place E R Rest → E X → At R X
  | last, op => .here op
  | init p, op => .there (p.inject op)

/-- an operation of `R` met by the handler of `E` at `p`: `E`'s own, or another's at its place in `Rest` -/
def take : Place E R Rest → At R X → E X ⊕ At Rest X
  | last, .here op => .inl op
  | last, .there o => .inr o
  | init _, .here op => .inr (.here op)
  | init p, .there o =>
    match p.take o with
    | .inl e => .inl e
    | .inr o' => .inr (.there o')

end Place

/-- `E` is in `R`, and `R` without it is `Rest` — found: the first `E` of `R` -/
class Split (E : Effect) (R : Row) (Rest : outParam Row) where
  place : Place E R Rest

instance (priority := high) : Split E (E :: R) R := ⟨.last⟩
instance [s : Split E R Rest] : Split E (G :: R) (G :: Rest) := ⟨.init s.place⟩

/-- `E` is in `R`: an operation of `E` is one of `R` -/
class In (E : Effect) (R : Row) where
  inject {X : Type} : E X → At R X

instance [s : Split E R Rest] : In E R := ⟨s.place.inject⟩

/-- an operation performed: a program of its answer -/
def perform [In E R] (op : E X) : X ! R := .impure (In.inject op) .ret

namespace Free

/-- `E` handled from its place `p` in `R`, deeply: `ret` the value's clause, `clause` an operation's, its `k` the
rest under the same handler, resumable any number of times; an operation of another effect passed on at its place in
`Rest` -/
def handleAt (p : Place E R Rest) (ret : A → B ! Rest)
    (clause : {X : Type} → E X → (X → B ! Rest) → B ! Rest) : A ! R → B ! Rest
  | .ret a => ret a
  | impure op k =>
    match p.take op with
    | .inl e => clause e fun x => handleAt p ret clause (k x)
    | .inr o => impure o fun x => handleAt p ret clause (k x)

/-- `E` handled from wherever it is in `R`, deeply -/
def handle [s : Split E R Rest] (ret : A → B ! Rest)
    (clause : {X : Type} → E X → (X → B ! Rest) → B ! Rest) : A ! R → B ! Rest :=
  handleAt s.place ret clause

/-- `E` answered in place: each operation a program of its answer, the rest going on -/
def answer [Split E R Rest] (ret : A → B ! Rest) (clause : {X : Type} → E X → X ! Rest) : A ! R → B ! Rest :=
  handle ret fun op k => clause op >>= k

/-- `E` handled from its place with a state threaded through, `S`: `ret` of the value and the state at the end,
`clause` of the state, an operation and the rest taking the answer and the new state -/
def handleWith [s : Split E R Rest] (ret : A → S → B ! Rest)
    (clause : {X : Type} → S → E X → (X → S → B ! Rest) → B ! Rest) (s0 : S) (prog : A ! R) : B ! Rest :=
  go prog s0
where
  go : A ! R → S → B ! Rest
    | .ret a, st => ret a st
    | impure op k, st =>
      match s.place.take op with
      | .inl e => clause st e fun x st' => go (k x) st'
      | .inr o => impure o fun x => go (k x) st

end Free
end Okay.Effects
