/-!
# THE `Free` MONAD, over rows of typed places

okay-simple's `okay.effects.free.Free` in Lean 4: a program is DATA — a value, a bind, an operation with its rest
`k`, a program built later — and its handlers interpret it. An effect is a GADT of its operations, indexed by the
answer; a row is a list of effects, the one handled next first; an operation of a row says where in it it is, `At`,
so a handler matching the place learns, by dependent pattern matching, that an operation is its own: no cast.

In constant stack, as okay-simple: a handler is a LOOP over the program (structural recursion, its self calls tail
calls — Lean compiles them to `goto`), binds are followed in continuation-passing style, and every continuation a
clause or a bind gets is a TRAMPOLINE — it gives back the rest delayed, `delay fun _ => ...`, which the loop outside
(the next handler's, or `run`'s) goes on with, not a call into the rest. So a bind nested to the left any depth, or a
clause resuming `k` at once, nests no call per operation. Everything is total: no `partial`, so the laws are proved.
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

/-- a program of the value `A` over the row `R`: a value, a bind, an operation and its rest, a program built when
the run gets to it -/
inductive Free (R : Row) : Type → Type 1
  | ret {A : Type} (a : A) : Free R A
  | bind {X A : Type} (m : Free R X) (f : X → Free R A) : Free R A
  | impure {X A : Type} (op : At R X) (k : X → Free R A) : Free R A
  | delay {A : Type} (p : Unit → Free R A) : Free R A

/-- a program of the value `A` over the row `R`: `Nat ! [State Nat, Reader String]` -/
notation:50 A:51 " ! " R:50 => Free R A

namespace Free

instance : Monad (Free R) where
  pure := ret
  bind := bind

/-- the program `p ()`, built when the run gets to it -/
@[inline] def suspend (p : Unit → A ! R) : A ! R := delay p

/-- THE NORMAL FORM: binds followed, delays forced — a program of values and operations only. `go m k` interprets
`m` and goes on with `k`, each `k` a trampoline -/
def norm (p : A ! R) : A ! R := go p ret
where
  go {X : Type} : X ! R → (X → A ! R) → A ! R
    | .ret x, k => k x
    | .delay q, k => go (q ()) k
    | .bind m f, k => go m fun x => .delay fun _ => go (f x) k
    | .impure op c, k => .impure op fun x => go (c x) k

/-- a program of no effect: its value. An operation of it there is none -/
def run (p : A ! Pure) : A := force (norm p)
where
  force {X : Type} : X ! Pure → X
    | .ret x => x
    | .delay q => force (q ())
    | .impure op _ => nomatch op
    | .bind m f => force (f (force m))

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
rest under the same handler, resumable any number of times — a trampoline, the rest given back delayed; an operation
of another effect passed on at its place in `Rest` -/
def handleAt (p : Place E R Rest) (ret : A → B ! Rest)
    (clause : {X : Type} → E X → (X → B ! Rest) → B ! Rest) (prog : A ! R) : B ! Rest :=
  go prog ret
where
  go {X : Type} : X ! R → (X → B ! Rest) → B ! Rest
    | .ret x, k => k x
    | .delay q, k => go (q ()) k
    | .bind m f, k => go m fun x => .delay fun _ => go (f x) k
    | .impure op c, k =>
      match p.take op with
      | .inl e => clause e fun x => .delay fun _ => go (c x) k
      | .inr o => .impure o fun x => go (c x) k

/-- `E` handled from wherever it is in `R`, deeply -/
def handle [s : Split E R Rest] (ret : A → B ! Rest)
    (clause : {X : Type} → E X → (X → B ! Rest) → B ! Rest) : A ! R → B ! Rest :=
  handleAt s.place ret clause

/-- `E` handled deeply with a state threaded through, `S`: `ret` of the value and the state at the end, `clause` of
the state, an operation and the rest `k` taking the answer and the new state — resumable any number of times -/
def handleWith [s : Split E R Rest] (ret : A → S → B ! Rest)
    (clause : {X : Type} → S → E X → (X → S → B ! Rest) → B ! Rest) (s0 : S) (prog : A ! R) : B ! Rest :=
  go prog s0 ret
where
  go {X : Type} : X ! R → S → (X → S → B ! Rest) → B ! Rest
    | .ret x, st, k => k x st
    | .delay q, st, k => go (q ()) st k
    | .bind m f, st, k => go m st fun x st' => .delay fun _ => go (f x) st' k
    | .impure op c, st, k =>
      match s.place.take op with
      | .inl e => clause st e fun x st' => .delay fun _ => go (c x) st' k
      | .inr o => .impure o fun x => go (c x) st k

/-- `E` answered in place, each operation its answer at once, the rest going on: the loop goes on itself -/
def answer [s : Split E R Rest] (ret : A → B ! Rest) (clause : {X : Type} → E X → X) (prog : A ! R) : B ! Rest :=
  go prog ret
where
  go {X : Type} : X ! R → (X → B ! Rest) → B ! Rest
    | .ret x, k => k x
    | .delay q, k => go (q ()) k
    | .bind m f, k => go m fun x => .delay fun _ => go (f x) k
    | .impure op c, k =>
      match s.place.take op with
      | .inl e => go (c (clause e)) k
      | .inr o => .impure o fun x => go (c x) k

/-- `E` answered in place with a state threaded through, `S`: each operation its answer and the new state at once;
`ret` of the value and the state at the end -/
def answerWith [s : Split E R Rest] (ret : A → S → B ! Rest) (clause : {X : Type} → S → E X → X × S) (s0 : S)
    (prog : A ! R) : B ! Rest :=
  go prog s0 ret
where
  go {X : Type} : X ! R → S → (X → S → B ! Rest) → B ! Rest
    | .ret x, st, k => k x st
    | .delay q, st, k => go (q ()) st k
    | .bind m f, st, k => go m st fun x st' => .delay fun _ => go (f x) st' k
    | .impure op c, st, k =>
      match s.place.take op with
      | .inl e => let (x, st') := clause st e; go (c x) st' k
      | .inr o => .impure o fun x => go (c x) st k

end Free
end Okay.Effects
