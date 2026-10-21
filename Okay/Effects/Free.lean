/-!
# THE `Free` MONAD, over rows of typed places

okay-simple's `okay.effects.free.Free` in Lean 4: a program is DATA — a value, a bind, an operation with its rest
`k`, a program built later — and its handlers interpret it. An effect is a GADT of its operations, indexed by the
answer; a row is a list of effects, the one handled next first; an operation of a row says where in it it is, `At`,
so a handler matching the place learns, by dependent pattern matching, that an operation is its own: no cast.

TWO DEFINITIONS OF EACH INTERPRETER. The reference one is total, structural recursion in continuation-passing
style, `go m k` — what the proofs are about. The one that RUNS, `@[implemented_by]`, is okay-simple's loop: a
bind of a value stepped, a bind nested to the left re-associated as data, `bind (bind m f) g` to
`bind m (fun y => bind (f y) g)`, an operation taken from its place — every step a self tail call, which Lean
compiles to `goto`, so the stack does not grow with the program; it is not structural recursion (the re-associated
term is no subterm), so it is `unsafe`, as Lean's own fast paths are. A deep handler's `k` is a TRAMPOLINE: it gives
the rest back delayed, `delay fun _ => ...`, for the loop outside — the next handler's, or `run`'s — to go on with.
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

/-- THE NORMAL FORM: binds followed, delays forced — a program of values and operations only. `go m k` interprets
`m` and goes on with `k`. The reference for the laws; not what runs -/
def norm (p : A ! R) : A ! R := go p ret
where
  go {X : Type} : X ! R → (X → A ! R) → A ! R
    | .ret x, k => k x
    | .delay q, k => go (q ()) k
    | .bind m f, k => go m fun x => go (f x) k
    | .impure op c, k => .impure op fun x => go (c x) k

/-- `run`, as it runs: the loop -/
unsafe def runImpl : A ! Pure → A
  | .ret a => a
  | .delay q => runImpl (q ())
  | .impure op _ => nomatch op
  | .bind m f =>
    match m with
    | .ret x => runImpl (f x)
    | .delay q => runImpl (.bind (q ()) f)
    | .bind m2 f2 => runImpl (.bind m2 fun y => .bind (f2 y) f)
    | .impure op _ => nomatch op

/-- a program of no effect: its value. An operation of it there is none -/
@[implemented_by runImpl]
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

/-! ## Deep handlers -/

/-- `handleAt`, as it runs: the loop -/
unsafe def handleAtImpl (p : Place E R Rest) (ret : A → B ! Rest)
    (clause : {X : Type} → E X → (X → B ! Rest) → B ! Rest) : A ! R → B ! Rest
  | .ret a => ret a
  | .delay q => handleAtImpl p ret clause (q ())
  | .impure op c =>
    match p.take op with
    | .inl e => clause e fun x => .delay fun _ => handleAtImpl p ret clause (c x)
    | .inr o => .impure o fun x => handleAtImpl p ret clause (c x)
  | .bind m f =>
    match m with
    | .ret x => handleAtImpl p ret clause (f x)
    | .delay q => handleAtImpl p ret clause (.bind (q ()) f)
    | .bind m2 f2 => handleAtImpl p ret clause (.bind m2 fun y => .bind (f2 y) f)
    | .impure op c =>
      match p.take op with
      | .inl e => clause e fun x => .delay fun _ => handleAtImpl p ret clause (.bind (c x) f)
      | .inr o => .impure o fun x => handleAtImpl p ret clause (.bind (c x) f)

/-- `E` handled from its place `p` in `R`, deeply: `ret` the value's clause, `clause` an operation's, its `k` the
rest under the same handler, resumable any number of times — a trampoline, the rest given back delayed; an operation
of another effect passed on at its place in `Rest` -/
@[implemented_by handleAtImpl]
def handleAt (p : Place E R Rest) (ret : A → B ! Rest)
    (clause : {X : Type} → E X → (X → B ! Rest) → B ! Rest) (prog : A ! R) : B ! Rest :=
  go prog ret
where
  go {X : Type} : X ! R → (X → B ! Rest) → B ! Rest
    | .ret x, k => k x
    | .delay q, k => go (q ()) k
    | .bind m f, k => go m fun x => go (f x) k
    | .impure op c, k =>
      match p.take op with
      | .inl e => clause e fun x => .delay fun _ => go (c x) k
      | .inr o => .impure o fun x => go (c x) k

/-- `E` handled from wherever it is in `R`, deeply -/
def handle [s : Split E R Rest] (ret : A → B ! Rest)
    (clause : {X : Type} → E X → (X → B ! Rest) → B ! Rest) : A ! R → B ! Rest :=
  handleAt s.place ret clause

/-- `handleWith`, as it runs: the loop -/
unsafe def handleWithImpl (p : Place E R Rest) (ret : A → S → B ! Rest)
    (clause : {X : Type} → S → E X → (X → S → B ! Rest) → B ! Rest) : S → A ! R → B ! Rest
  | st, .ret a => ret a st
  | st, .delay q => handleWithImpl p ret clause st (q ())
  | st, .impure op c =>
    match p.take op with
    | .inl e => clause st e fun x st' => .delay fun _ => handleWithImpl p ret clause st' (c x)
    | .inr o => .impure o fun x => handleWithImpl p ret clause st (c x)
  | st, .bind m f =>
    match m with
    | .ret x => handleWithImpl p ret clause st (f x)
    | .delay q => handleWithImpl p ret clause st (.bind (q ()) f)
    | .bind m2 f2 => handleWithImpl p ret clause st (.bind m2 fun y => .bind (f2 y) f)
    | .impure op c =>
      match p.take op with
      | .inl e => clause st e fun x st' => .delay fun _ => handleWithImpl p ret clause st' (.bind (c x) f)
      | .inr o => .impure o fun x => handleWithImpl p ret clause st (.bind (c x) f)

/-- `E` handled deeply with a state threaded through, `S`: `ret` of the value and the state at the end, `clause` of
the state, an operation and the rest `k` taking the answer and the new state — resumable any number of times -/
@[implemented_by handleWithImpl]
def handleWithAt (p : Place E R Rest) (ret : A → S → B ! Rest)
    (clause : {X : Type} → S → E X → (X → S → B ! Rest) → B ! Rest) (s0 : S) (prog : A ! R) : B ! Rest :=
  go prog s0 ret
where
  go {X : Type} : X ! R → S → (X → S → B ! Rest) → B ! Rest
    | .ret x, st, k => k x st
    | .delay q, st, k => go (q ()) st k
    | .bind m f, st, k => go m st fun x st' => go (f x) st' k
    | .impure op c, st, k =>
      match p.take op with
      | .inl e => clause st e fun x st' => .delay fun _ => go (c x) st' k
      | .inr o => .impure o fun x => go (c x) st k

/-- `E` handled deeply with a state, from wherever it is in `R` -/
def handleWith [s : Split E R Rest] (ret : A → S → B ! Rest)
    (clause : {X : Type} → S → E X → (X → S → B ! Rest) → B ! Rest) (s0 : S) : A ! R → B ! Rest :=
  handleWithAt s.place ret clause s0

/-! ## Handlers answering in place -/

/-- `answer`, as it runs: the loop -/
unsafe def answerImpl (p : Place E R Rest) (ret : A → B ! Rest) (clause : {X : Type} → E X → X) :
    A ! R → B ! Rest
  | .ret a => ret a
  | .delay q => answerImpl p ret clause (q ())
  | .impure op c =>
    match p.take op with
    | .inl e => answerImpl p ret clause (c (clause e))
    | .inr o => .impure o fun x => answerImpl p ret clause (c x)
  | .bind m f =>
    match m with
    | .ret x => answerImpl p ret clause (f x)
    | .delay q => answerImpl p ret clause (.bind (q ()) f)
    | .bind m2 f2 => answerImpl p ret clause (.bind m2 fun y => .bind (f2 y) f)
    | .impure op c =>
      match p.take op with
      | .inl e => answerImpl p ret clause (.bind (c (clause e)) f)
      | .inr o => .impure o fun x => answerImpl p ret clause (.bind (c x) f)

/-- `E` answered in place from its place `p`, each operation its answer at once, the rest going on -/
@[implemented_by answerImpl]
def answerAt (p : Place E R Rest) (ret : A → B ! Rest) (clause : {X : Type} → E X → X) (prog : A ! R) :
    B ! Rest :=
  go prog ret
where
  go {X : Type} : X ! R → (X → B ! Rest) → B ! Rest
    | .ret x, k => k x
    | .delay q, k => go (q ()) k
    | .bind m f, k => go m fun x => go (f x) k
    | .impure op c, k =>
      match p.take op with
      | .inl e => go (c (clause e)) k
      | .inr o => .impure o fun x => go (c x) k

/-- `E` answered in place, from wherever it is in `R` -/
def answer [s : Split E R Rest] (ret : A → B ! Rest) (clause : {X : Type} → E X → X) : A ! R → B ! Rest :=
  answerAt s.place ret clause

/-- `answerWith`, as it runs: the loop -/
unsafe def answerWithImpl (p : Place E R Rest) (ret : A → S → B ! Rest) (clause : {X : Type} → S → E X → X × S) :
    S → A ! R → B ! Rest
  | st, .ret a => ret a st
  | st, .delay q => answerWithImpl p ret clause st (q ())
  | st, .impure op c =>
    match p.take op with
    | .inl e => let (x, st') := clause st e; answerWithImpl p ret clause st' (c x)
    | .inr o => .impure o fun x => answerWithImpl p ret clause st (c x)
  | st, .bind m f =>
    match m with
    | .ret x => answerWithImpl p ret clause st (f x)
    | .delay q => answerWithImpl p ret clause st (.bind (q ()) f)
    | .bind m2 f2 => answerWithImpl p ret clause st (.bind m2 fun y => .bind (f2 y) f)
    | .impure op c =>
      match p.take op with
      | .inl e => let (x, st') := clause st e; answerWithImpl p ret clause st' (.bind (c x) f)
      | .inr o => .impure o fun x => answerWithImpl p ret clause st (.bind (c x) f)

/-- `E` answered in place from its place `p` with a state threaded through, `S`: each operation its answer and the
new state at once; `ret` of the value and the state at the end -/
@[implemented_by answerWithImpl]
def answerWithAt (p : Place E R Rest) (ret : A → S → B ! Rest) (clause : {X : Type} → S → E X → X × S) (s0 : S)
    (prog : A ! R) : B ! Rest :=
  go prog s0 ret
where
  go {X : Type} : X ! R → S → (X → S → B ! Rest) → B ! Rest
    | .ret x, st, k => k x st
    | .delay q, st, k => go (q ()) st k
    | .bind m f, st, k => go m st fun x st' => go (f x) st' k
    | .impure op c, st, k =>
      match p.take op with
      | .inl e => let (x, st') := clause st e; go (c x) st' k
      | .inr o => .impure o fun x => go (c x) st k

/-- `E` answered in place with a state, from wherever it is in `R` -/
def answerWith [s : Split E R Rest] (ret : A → S → B ! Rest) (clause : {X : Type} → S → E X → X × S) (s0 : S) :
    A ! R → B ! Rest :=
  answerWithAt s.place ret clause s0

end Free
end Okay.Effects
