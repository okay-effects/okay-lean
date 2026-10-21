/-!
# THE `Free` MONAD, over rows of typed places

okay-simple's `okay.effects.free.Free` in Lean 4: a program is DATA — a value, a bind, an operation with its rest
`k`, a program built later — and its handlers interpret it. An effect is a GADT of its operations, indexed by the
answer; a row is a list of effects, the one handled next first; an operation says its place in the row,
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

/-- the place of `E` in `R`, and `R` without it `Rest`: the first, or one further in. A program's operation says
its place; an instance of `Split`/`In` for a concrete row is a closed term, made once -/
inductive Place : Effect → Row → Row → Type 1
  | last {E : Effect} {R : Row} : Place E (E :: R) R
  | init {E G : Effect} {R Rest : Row} (p : Place E R Rest) : Place E (G :: R) (G :: Rest)

/-- a program of the value `A` over the row `R`: a value, a bind, an operation alone (its answer the value) — the
operation of an effect at its place in `R` —, an operation and its rest, a program built when the run gets to it -/
inductive Free (R : Row) : Type → Type 1
  | ret {A : Type} (a : A) : Free R A
  | bind {X A : Type} (m : Free R X) (f : X → Free R A) : Free R A
  | op {E : Effect} {Rest : Row} {X : Type} (pl : Place E R Rest) (o : E X) : Free R X
  | impure {E : Effect} {Rest : Row} {X A : Type} (pl : Place E R Rest) (o : E X) (k : X → Free R A) : Free R A
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
    | .op pl o, k => .impure pl o k
    | .impure pl o c, k => .impure pl o fun x => go (c x) k

/-- `m` then `f`, a bind node unless `m` is a value already: what a loop makes of a rest under a bind -/
@[inline] def andThen (m : X ! R) (f : X → A ! R) : A ! R :=
  match m with
  | .ret x => f x
  | m => .bind m f

/-- `run`, as it runs: the loop -/
@[specialize] unsafe def runImpl : A ! Pure → A
  | .ret a => a
  | .delay q => runImpl (q ())
  | .op pl _ => nomatch pl
  | .impure pl _ _ => nomatch pl
  | .bind m f =>
    match m with
    | .ret x => runImpl (f x)
    | .delay q => runImpl (.bind (q ()) f)
    | .bind m2 f2 => runImpl (.bind m2 fun y => .bind (f2 y) f)
    | .op pl _ => nomatch pl
    | .impure pl _ _ => nomatch pl

/-- a program of no effect: its value. An operation of it there is none -/
@[implemented_by runImpl]
def run (p : A ! Pure) : A := force (norm p)
where
  force {X : Type} : X ! Pure → X
    | .ret x => x
    | .delay q => force (q ())
    | .op pl _ => nomatch pl
    | .impure pl _ _ => nomatch pl
    | .bind m f => force (f (force m))

end Free

namespace Place

/-- an operation at `at` in `R`, met by the handler of `E` at `p` in `R`: `E`'s own — `mine`, so `E2` is `E` —, or
another's, `theirs` its place in `Rest`, the row without `E` -/
inductive Taken (E : Effect) (Rest : Row) : Effect → Type 1
  | mine : Taken E Rest E
  | theirs {E2 : Effect} {Rest2 : Row} (pl : Place E2 Rest Rest2) : Taken E Rest E2

def take : {E : Effect} → {R Rest : Row} → {E2 : Effect} → {Rest2 : Row} →
    Place E R Rest → Place E2 R Rest2 → Taken E Rest E2
  | _, _, _, _, _, last, last => .mine
  | _, _, _, _, _, last, init q => .theirs q
  | _, _, _, _, _, init _, last => .theirs .last
  | _, _, _, _, _, init p, init q =>
    match p.take q with
    | .mine => .mine
    | .theirs r => .theirs (.init r)

/-- `take` in continuation-passing style, inlined: no `Taken` allocated. `mine` gets the operation as `E`'s,
`theirs` the place in `Rest` and the operation -/
@[inline] def taken {β : Type 1} {X : Type} : {E : Effect} → {R Rest : Row} → {E2 : Effect} → {Rest2 : Row} →
    (p : Place E R Rest) → (pl : Place E2 R Rest2) → (o : E2 X) → (mine : E X → β) →
    (theirs : {E3 : Effect} → {Rest3 : Row} → Place E3 Rest Rest3 → E3 X → β) → β
  | _, _, _, _, _, last, last, o, mine, _ => mine o
  | _, _, _, _, _, last, init q, o, _, theirs => theirs q o
  | _, _, _, _, _, init _, last, o, _, theirs => theirs .last o
  | _, _, _, _, _, init p, init q, o, mine, theirs =>
    match p.take q with
    | .mine => mine o
    | .theirs r => theirs (.init r) o

end Place

/-- `E` is in `R`, and `R` without it is `Rest` — found: the first `E` of `R` -/
class Split (E : Effect) (R : Row) (Rest : outParam Row) where
  place : Place E R Rest

instance (priority := high) : Split E (E :: R) R := ⟨.last⟩
instance [s : Split E R Rest] : Split E (G :: R) (G :: Rest) := ⟨.init s.place⟩

/-- `E` is in `R`: at a place -/
class In (E : Effect) (R : Row) where
  Rest : Row
  place : Place E R Rest

instance [s : Split E R Rest] : In E R := ⟨Rest, s.place⟩

/-- an operation performed: a program of its answer, the operation at `E`'s place -/
def perform [i : In E R] (o : E X) : X ! R := .op i.place o

namespace Free

/-! ## Deep handlers -/

/-- `handleAt`, as it runs: the loop -/
@[specialize] unsafe def handleAtImpl (p : Place E R Rest) (ret : A → B ! Rest)
    (clause : {X : Type} → E X → (X → B ! Rest) → B ! Rest) : A ! R → B ! Rest
  | .ret a => ret a
  | .delay q => handleAtImpl p ret clause (q ())
  | .op pl o => p.taken pl o (fun e => clause e ret) (fun pl' o' => .impure pl' o' ret)
  | .impure pl o c =>
    p.taken pl o (fun e => clause e fun x => .delay fun _ => handleAtImpl p ret clause (c x))
      (fun pl' o' => .impure pl' o' fun x => handleAtImpl p ret clause (c x))
  | .bind m f =>
    match m with
    | .ret x => handleAtImpl p ret clause (f x)
    | .delay q => handleAtImpl p ret clause (.bind (q ()) f)
    | .bind m2 f2 => handleAtImpl p ret clause (.bind m2 fun y => .bind (f2 y) f)
    | .op pl o => p.taken pl o (fun e => clause e fun x => .delay fun _ => handleAtImpl p ret clause (f x))
        (fun pl' o' => .impure pl' o' fun x => handleAtImpl p ret clause (f x))
    | .impure pl o c =>
      p.taken pl o (fun e => clause e fun x => .delay fun _ => handleAtImpl p ret clause ((c x).andThen f))
        (fun pl' o' => .impure pl' o' fun x => handleAtImpl p ret clause ((c x).andThen f))

/-- `E` handled from its place `p` in `R`, deeply: `ret` the value's clause, `clause` an operation's, its `k` the
rest under the same handler, resumable any number of times — a trampoline, the rest given back delayed; an operation
of another effect passed on at its place in `Rest` -/
@[implemented_by handleAtImpl, specialize] def handleAt (p : Place E R Rest) (ret : A → B ! Rest)
    (clause : {X : Type} → E X → (X → B ! Rest) → B ! Rest) (prog : A ! R) : B ! Rest :=
  go prog ret
where
  go {X : Type} : X ! R → (X → B ! Rest) → B ! Rest
    | .ret x, k => k x
    | .delay q, k => go (q ()) k
    | .bind m f, k => go m fun x => go (f x) k
    | .op pl o, k => p.taken pl o (fun e => clause e fun x => .delay fun _ => k x) (fun pl' o' => .impure pl' o' k)
    | .impure pl o c, k =>
      p.taken pl o (fun e => clause e fun x => .delay fun _ => go (c x) k)
        (fun pl' o' => .impure pl' o' fun x => go (c x) k)

/-- `E` handled from wherever it is in `R`, deeply -/
@[inline] def handle [s : Split E R Rest] (ret : A → B ! Rest)
    (clause : {X : Type} → E X → (X → B ! Rest) → B ! Rest) : A ! R → B ! Rest :=
  handleAt s.place ret clause

/-- `handleWith`, as it runs: the loop -/
@[specialize] unsafe def handleWithImpl (p : Place E R Rest) (ret : A → S → B ! Rest)
    (clause : {X : Type} → S → E X → (X → S → B ! Rest) → B ! Rest) : S → A ! R → B ! Rest
  | st, .ret a => ret a st
  | st, .delay q => handleWithImpl p ret clause st (q ())
  | st, .op pl o => p.taken pl o (fun e => clause st e ret) (fun pl' o' => .impure pl' o' fun x => ret x st)
  | st, .impure pl o c =>
    p.taken pl o (fun e => clause st e fun x st' => .delay fun _ => handleWithImpl p ret clause st' (c x))
      (fun pl' o' => .impure pl' o' fun x => handleWithImpl p ret clause st (c x))
  | st, .bind m f =>
    match m with
    | .ret x => handleWithImpl p ret clause st (f x)
    | .delay q => handleWithImpl p ret clause st (.bind (q ()) f)
    | .bind m2 f2 => handleWithImpl p ret clause st (.bind m2 fun y => .bind (f2 y) f)
    | .op pl o => p.taken pl o (fun e => clause st e fun x st' => .delay fun _ => handleWithImpl p ret clause st' (f x))
        (fun pl' o' => .impure pl' o' fun x => handleWithImpl p ret clause st (f x))
    | .impure pl o c =>
      p.taken pl o (fun e => clause st e fun x st' => .delay fun _ => handleWithImpl p ret clause st' ((c x).andThen f))
        (fun pl' o' => .impure pl' o' fun x => handleWithImpl p ret clause st (.bind (c x) f))

/-- `E` handled deeply with a state threaded through, `S`: `ret` of the value and the state at the end, `clause` of
the state, an operation and the rest `k` taking the answer and the new state — resumable any number of times -/
@[implemented_by handleWithImpl, specialize] def handleWithAt (p : Place E R Rest) (ret : A → S → B ! Rest)
    (clause : {X : Type} → S → E X → (X → S → B ! Rest) → B ! Rest) (s0 : S) (prog : A ! R) : B ! Rest :=
  go prog s0 ret
where
  go {X : Type} : X ! R → S → (X → S → B ! Rest) → B ! Rest
    | .ret x, st, k => k x st
    | .delay q, st, k => go (q ()) st k
    | .bind m f, st, k => go m st fun x st' => go (f x) st' k
    | .op pl o, st, k => p.taken pl o (fun e => clause st e fun x st' => .delay fun _ => k x st') (fun pl' o' => .impure pl' o' fun x => k x st)
    | .impure pl o c, st, k =>
      p.taken pl o (fun e => clause st e fun x st' => .delay fun _ => go (c x) st' k)
        (fun pl' o' => .impure pl' o' fun x => go (c x) st k)

/-- `E` handled deeply with a state, from wherever it is in `R` -/
@[inline] def handleWith [s : Split E R Rest] (ret : A → S → B ! Rest)
    (clause : {X : Type} → S → E X → (X → S → B ! Rest) → B ! Rest) (s0 : S) : A ! R → B ! Rest :=
  handleWithAt s.place ret clause s0

/-! ## Handlers answering in place -/

/-- `answer`, as it runs: the loop -/
@[specialize] unsafe def answerImpl (p : Place E R Rest) (ret : A → B ! Rest) (clause : {X : Type} → E X → X) :
    A ! R → B ! Rest
  | .ret a => ret a
  | .delay q => answerImpl p ret clause (q ())
  | .op pl o => p.taken pl o (fun e => ret (clause e)) (fun pl' o' => .impure pl' o' ret)
  | .impure pl o c =>
    p.taken pl o (fun e => answerImpl p ret clause (c (clause e)))
      (fun pl' o' => .impure pl' o' fun x => answerImpl p ret clause (c x))
  | .bind m f =>
    match m with
    | .ret x => answerImpl p ret clause (f x)
    | .delay q => answerImpl p ret clause (.bind (q ()) f)
    | .bind m2 f2 => answerImpl p ret clause (.bind m2 fun y => .bind (f2 y) f)
    | .op pl o => p.taken pl o (fun e => answerImpl p ret clause (f (clause e)))
        (fun pl' o' => .impure pl' o' fun x => answerImpl p ret clause (f x))
    | .impure pl o c =>
      p.taken pl o (fun e => answerImpl p ret clause ((c (clause e)).andThen f))
        (fun pl' o' => .impure pl' o' fun x => answerImpl p ret clause (.bind (c x) f))

/-- `E` answered in place from its place `p`, each operation its answer at once, the rest going on -/
@[implemented_by answerImpl, specialize] def answerAt (p : Place E R Rest) (ret : A → B ! Rest) (clause : {X : Type} → E X → X) (prog : A ! R) :
    B ! Rest :=
  go prog ret
where
  go {X : Type} : X ! R → (X → B ! Rest) → B ! Rest
    | .ret x, k => k x
    | .delay q, k => go (q ()) k
    | .bind m f, k => go m fun x => go (f x) k
    | .op pl o, k => p.taken pl o (fun e => k (clause e)) (fun pl' o' => .impure pl' o' k)
    | .impure pl o c, k =>
      p.taken pl o (fun e => go (c (clause e)) k)
        (fun pl' o' => .impure pl' o' fun x => go (c x) k)

/-- `E` answered in place, from wherever it is in `R` -/
@[inline] def answer [s : Split E R Rest] (ret : A → B ! Rest) (clause : {X : Type} → E X → X) : A ! R → B ! Rest :=
  answerAt s.place ret clause

/-- `answerWith`, as it runs: the loop -/
@[specialize] unsafe def answerWithImpl (p : Place E R Rest) (ret : A → S → B ! Rest) (clause : {X : Type} → S → E X → X × S) :
    S → A ! R → B ! Rest
  | st, .ret a => ret a st
  | st, .delay q => answerWithImpl p ret clause st (q ())
  | st, .op pl o => p.taken pl o (fun e => let (x, st') := clause st e; ret x st') (fun pl' o' => .impure pl' o' fun x => ret x st)
  | st, .impure pl o c =>
    p.taken pl o (fun e => let (x, st') := clause st e; answerWithImpl p ret clause st' (c x))
      (fun pl' o' => .impure pl' o' fun x => answerWithImpl p ret clause st (c x))
  | st, .bind m f =>
    match m with
    | .ret x => answerWithImpl p ret clause st (f x)
    | .delay q => answerWithImpl p ret clause st (.bind (q ()) f)
    | .bind m2 f2 => answerWithImpl p ret clause st (.bind m2 fun y => .bind (f2 y) f)
    | .op pl o => p.taken pl o (fun e => let (x, st') := clause st e; answerWithImpl p ret clause st' (f x))
        (fun pl' o' => .impure pl' o' fun x => answerWithImpl p ret clause st (f x))
    | .impure pl o c =>
      p.taken pl o (fun e => let (x, st') := clause st e; answerWithImpl p ret clause st' ((c x).andThen f))
        (fun pl' o' => .impure pl' o' fun x => answerWithImpl p ret clause st (.bind (c x) f))

/-- `E` answered in place from its place `p` with a state threaded through, `S`: each operation its answer and the
new state at once; `ret` of the value and the state at the end -/
@[implemented_by answerWithImpl, specialize] def answerWithAt (p : Place E R Rest) (ret : A → S → B ! Rest) (clause : {X : Type} → S → E X → X × S) (s0 : S)
    (prog : A ! R) : B ! Rest :=
  go prog s0 ret
where
  go {X : Type} : X ! R → S → (X → S → B ! Rest) → B ! Rest
    | .ret x, st, k => k x st
    | .delay q, st, k => go (q ()) st k
    | .bind m f, st, k => go m st fun x st' => go (f x) st' k
    | .op pl o, st, k => p.taken pl o (fun e => let (x, st') := clause st e; k x st') (fun pl' o' => .impure pl' o' fun x => k x st)
    | .impure pl o c, st, k =>
      p.taken pl o (fun e => let (x, st') := clause st e; go (c x) st' k)
        (fun pl' o' => .impure pl' o' fun x => go (c x) st k)

/-- `E` answered in place with a state, from wherever it is in `R` -/
@[inline] def answerWith [s : Split E R Rest] (ret : A → S → B ! Rest) (clause : {X : Type} → S → E X → X × S) (s0 : S) :
    A ! R → B ! Rest :=
  answerWithAt s.place ret clause s0

end Free
end Okay.Effects
