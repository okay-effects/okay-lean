import Okay.Effects.Free

/-!
# THE LAWS, proved

A program is data with `bind` nodes, so the monad laws are not equalities of data: `bind (ret a) f` is a node, `f a`
is not. They are equalities AFTER NORMALIZATION — `norm` follows the binds and forces the delays — each by `rfl`;
and on `run` they are equalities as they stand: `run_ret`, `run_bind`, `run_delay`. The theorems are about the
reference definitions; the loops that run (`@[implemented_by]`) are meant to compute the same, unproved.
-/

namespace Okay.Effects.Free

/-! ## The monad laws, after normalization -/

theorem pure_bind (a : X) (f : X → A ! R) : norm (.bind (.ret a) f) = norm (f a) := rfl

theorem bind_pure (m : A ! R) : norm (.bind m .ret) = norm m := rfl

theorem bind_assoc (m : X ! R) (f : X → Y ! R) (g : Y → A ! R) :
    norm (.bind (.bind m f) g) = norm (.bind m fun x => .bind (f x) g) := rfl

/-- normalizing a normal form changes nothing -/
theorem norm_norm (p : A ! R) : norm (norm p) = norm p := by
  show norm.go (norm.go p ret) ret = norm.go p ret
  suffices h : ∀ {X : Type} (m : X ! R) (k : X → A ! R), norm.go (norm.go m k) ret = norm.go m fun x => norm.go (k x) ret
    from h p ret
  intro X m
  induction m with
  | ret x => intro k; rfl
  | delay q ih => intro k; exact ih () k
  | op _ _ => intro k; rfl
  | impure _ _ c ih => intro k; exact congrArg _ (funext fun x => ih x k)
  | bind m f ihm ihf =>
    intro k
    show norm.go (norm.go m _) ret = norm.go m _
    rw [ihm]
    exact congrArg _ (funext fun x => ihf x k)

/-! ## `run` -/

/-- forcing a normalization with a continuation: the continuation at the value -/
theorem force_go (m : X ! Pure) : ∀ {A : Type} (k : X → A ! Pure),
    run.force (norm.go m k) = run.force (k (run m)) := by
  induction m with
  | ret x => intro A k; rfl
  | delay q ih => intro A k; exact ih () k
  | op pl _ => intro A k; exact nomatch pl
  | impure pl _ _ _ => intro A k; exact nomatch pl
  | bind m f ihm ihf =>
    intro A k
    show run.force (norm.go m _) = run.force (k (run.force (norm.go m _)))
    rw [ihm, ihm]
    exact ihf _ k

@[simp] theorem run_ret (a : A) : run (.ret a : A ! Pure) = a := rfl
@[simp] theorem run_delay (p : Unit → A ! Pure) : run (.delay p) = run (p ()) := rfl
@[simp] theorem run_bind (m : X ! Pure) (f : X → A ! Pure) : run (.bind m f) = run (f (run m)) := by
  show run.force (norm.go m _) = _
  rw [force_go]
  rfl

@[simp] theorem run_pure (a : A) : run (pure a : A ! Pure) = a := rfl
@[simp] theorem run_bind' (m : X ! Pure) (f : X → A ! Pure) : run (m >>= f) = run (f (run m)) := run_bind m f

/-! ## An interpreter sees the normal form

Every `go` of this library follows a program's structure the same way: a FOLD. What is proved of a fold is proved of
them all — `norm`, the four handlers, `interceptAt`. -/

/-- an interpreter of programs over `R`, in continuation-passing style: a value to the continuation, a delay
forced, a bind followed, an operation with its rest as the operation alone and then the rest -/
structure Fold {R : Row} {C : Type 1} (H : {X : Type} → X ! R → (X → C) → C) : Prop where
  ret : ∀ {X : Type} (x : X) (k : X → C), H (.ret x) k = k x
  delay : ∀ {X : Type} (q : Unit → X ! R) (k : X → C), H (.delay q) k = H (q ()) k
  bind : ∀ {X Y : Type} (m : X ! R) (f : X → Y ! R) (k : Y → C), H (.bind m f) k = H m fun x => H (f x) k
  impure : ∀ {E : Effect} {Rest : Row} {X Y : Type} (pl : Place E R Rest) (o : E X) (c : X → Y ! R) (k : Y → C),
    H (.impure pl o c) k = H (.op pl o) fun x => H (c x) k

/-- a fold of a normal form is the fold of the program -/
theorem Fold.norm_go {H : {X : Type} → X ! R → (X → C) → C} (h : Fold H) (m : X ! R) :
    ∀ {Y : Type} (c : X → Y ! R) (k : Y → C), H (norm.go m c) k = H m fun x => H (c x) k := by
  induction m with
  | ret x => intro Y c k; rw [h.ret]; rfl
  | delay q ih => intro Y c k; rw [h.delay]; exact ih () c k
  | op pl o => intro Y c k; exact h.impure pl o c k
  | impure pl o c' ih =>
    intro Y c k
    show H (.impure pl o fun x => norm.go (c' x) c) k = _
    rw [h.impure, h.impure]
    exact congrArg _ (funext fun x => ih x c k)
  | bind m f ihm ihf =>
    intro Y c k
    show H (norm.go m _) k = _
    rw [ihm, h.bind]
    exact congrArg _ (funext fun x => ihf x c k)

/-- programs equal after normalization are equal to every interpreter -/
theorem Fold.congr {H : {X : Type} → X ! R → (X → C) → C} (h : Fold H) {m m' : X ! R} (e : norm m = norm m')
    (k : X → C) : H m k = H m' k := by
  have l := h.norm_go m .ret k
  have r := h.norm_go m' .ret k
  simp only [h.ret] at l r
  rw [← l, ← r]
  exact congrArg (H · k) e

theorem fold_norm : Fold (R := R) (C := A ! R) norm.go :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem fold_handleAt (p : Place E R Rest) (clause : {X : Type} → E X → (X → B ! Rest) → B ! Rest) :
    Fold (handleAt.go p clause) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem fold_handleWithAt {S : Type} (p : Place E R Rest) (clause : {X : Type} → S → E X → (X → S → B ! Rest) → B ! Rest) :
    Fold (C := S → B ! Rest) fun m k st => handleWithAt.go p clause m st k :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem fold_answerAt (p : Place E R Rest) (clause : {X : Type} → E X → X) :
    Fold (C := B ! Rest) (answerAt.go p clause) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem fold_answerWithAt {S : Type} (p : Place E R Rest) (clause : {X : Type} → S → E X → X × S) :
    Fold (C := S → B ! Rest) fun m k st => answerWithAt.go p clause m st k :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem fold_interceptAt (p : Place E R Rest) (clause : {X : Type} → E X → (X → B ! R) → B ! R) :
    Fold (interceptAt.go p clause) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- so a handler makes the same of programs equal after normalization — of the two sides of a monad law, of a
program and the program under an interceptor that passes everything on -/
theorem handleAt_congr (p : Place E R Rest) (ret : A → B ! Rest)
    (clause : {X : Type} → E X → (X → B ! Rest) → B ! Rest) {m m' : A ! R} (e : norm m = norm m') :
    handleAt p ret clause m = handleAt p ret clause m' :=
  (fold_handleAt p clause).congr e ret

theorem handleWithAt_congr {S : Type} (p : Place E R Rest) (ret : A → S → B ! Rest)
    (clause : {X : Type} → S → E X → (X → S → B ! Rest) → B ! Rest) (s0 : S) {m m' : A ! R} (e : norm m = norm m') :
    handleWithAt p ret clause s0 m = handleWithAt p ret clause s0 m' :=
  congrFun ((fold_handleWithAt p clause).congr e ret) s0

theorem answerAt_congr (p : Place E R Rest) (ret : A → B ! Rest) (clause : {X : Type} → E X → X) {m m' : A ! R}
    (e : norm m = norm m') : answerAt p ret clause m = answerAt p ret clause m' :=
  (fold_answerAt p clause).congr e ret

theorem answerWithAt_congr {S : Type} (p : Place E R Rest) (ret : A → S → B ! Rest) (clause : {X : Type} → S → E X → X × S)
    (s0 : S) {m m' : A ! R} (e : norm m = norm m') : answerWithAt p ret clause s0 m = answerWithAt p ret clause s0 m' :=
  congrFun ((fold_answerWithAt p clause).congr e ret) s0

theorem interceptAt_congr (p : Place E R Rest) (ret : A → B ! R) (clause : {X : Type} → E X → (X → B ! R) → B ! R)
    {m m' : A ! R} (e : norm m = norm m') : interceptAt p ret clause m = interceptAt p ret clause m' :=
  (fold_interceptAt p clause).congr e ret

theorem run_congr {m m' : A ! Pure} (e : norm m = norm m') : run m = run m' := congrArg run.force e

end Okay.Effects.Free

namespace Okay.Effects.Place

/-! ## A place met by itself -/

theorem take_self (p : Place E R Rest) : p.take p = .mine := by
  induction p with
  | last => rfl
  | init p ih => simp [take, ih]

/-- a handler meeting an operation at its own place: its own -/
theorem taken_self {β : Type 1} {X : Type} (p : Place E R Rest) (o : E X) (mine : E X → β)
    (theirs : {E3 : Effect} → {Rest3 : Row} → Place E3 Rest Rest3 → E3 X → β) : p.taken p o mine theirs = mine o := by
  induction p with
  | last => rfl
  | init p ih => simp [taken, take_self]

theorem same_self (p : Place E R Rest) : p.same p = .yes := by
  induction p with
  | last => rfl
  | init p ih => simp [same, ih]

/-- an interceptor meeting an operation at its own place: its own -/
theorem own_self {β : Type 1} {X : Type} (p : Place E R Rest) (o : E X) (mine : E X → β) (theirs : Unit → β) :
    p.own p o mine theirs = mine o := by
  simp [own, same_self]

end Okay.Effects.Place
