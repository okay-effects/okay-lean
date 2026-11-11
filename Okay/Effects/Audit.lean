import Okay.Effects.Intercept
import Okay.Effects.Std

namespace Okay.Effects

/-- the trail of `E`'s operations: each asked again as it is, then told with its answer — `describe` says how — to
the `Writer T` of the row. `writer T` outside gives the trail beside the value; where it stands among the other
handlers is what the trail is of -/
def trail [In E R] [In (Writer T) R] (describe : {X : Type} → E X → X → T) : A ! R → A ! R :=
  Free.around (E := E) fun e proceed => do
    let x ← proceed
    tell (describe e x)
    pure x

namespace Free

/-- a trail's entry before the rest's -/
def told (t : T) (r : B × List T) : B × List T := (r.1, t :: r.2)

/-- THE ONE PATH of a program over `[E, Writer T]`, `E` answered in place by `clause` from `s0`: the value and the
state at the end, and what there is to tell on the way, in the order the program asks — each operation of `E`
described with its answer, each `tell` of the program's own as it is -/
def path (describe : {X : Type} → E X → X → T) (clause : {X : Type} → S → E X → X × S) (prog : A ! [E, Writer T])
    (s0 : S) : (A × S) × List T :=
  go prog s0 fun a s => ((a, s), [])
where
  step {X : Type} {E2 : Effect} {Rest2 : Row} (pl : Place E2 [E, Writer T] Rest2) (o : E2 X) (s : S)
      (k : X → S → (A × S) × List T) : (A × S) × List T :=
    match E2, Rest2, pl, o with
    | _, _, .last, e => told (describe e (clause s e).1) (k (clause s e).1 (clause s e).2)
    | _, _, .init .last, o => match X, o, k with | _, .tell w, k => told w (k () s)
  go {X : Type} : X ! [E, Writer T] → S → (X → S → (A × S) × List T) → (A × S) × List T
    | .ret x, s, k => k x s
    | .delay q, s, k => go (q ()) s k
    | .bind m f, s, k => go m s fun x s' => go (f x) s' k
    | .op pl o, s, k => step pl o s k
    | .impure pl o c, s, k => step pl o s fun x s' => go (c x) s' k

/-- the trail's entries are told behind what was told before -/
private def after (ws : List T) (r : B × List T) : B × List T := (r.1, ws.reverse ++ r.2)

/-- `writer`'s clause -/
private def tells {X : Type} (ws : List T) : Writer T X → X × List T
  | .tell w => ((), w :: ws)

private theorem after_told (ws : List T) (t : T) (r : B × List T) : after ws (told t r) = after (t :: ws) r := by
  simp [after, told]

/-- THE TRAIL OF ONE PATH. `E` answered in place and the trail collected outside: the program's value and state
with what its one path tells, operation by operation, in order -/
theorem trail_path {S : Type} (describe : {X : Type} → E X → X → T) (clause : {X : Type} → S → E X → X × S)
    (s0 : S) (prog : A ! [E, Writer T]) :
    run (writer T (answerWith (E := E) (fun a s => pure (a, s)) clause s0 (trail describe prog)))
      = path describe clause prog s0 := by
  suffices h : ∀ {X : Type} (m : X ! [E, Writer T]) (s : S) (ws : List T) {Y : Type} (kI : X → Y ! [E, Writer T])
      (kA : Y → S → (A × S) ! [Writer T]) (kW : A × S → List T → ((A × S) × List T) ! Pure)
      (ks : X → S → (A × S) × List T),
      (∀ x s ws, run (answerWithAt.go .last tells (answerWithAt.go .last clause (kI x) s kA) ws kW) = after ws (ks x s)) →
      run (answerWithAt.go .last tells (answerWithAt.go .last clause
        (interceptAt.go (E := E) .last
          (fun e k => .bind (.bind (perform e) fun x => .bind (tell (describe e x)) fun _ => pure x) k) m kI)
        s kA) ws kW) = after ws (path.go (A := A) describe clause m s ks) by
    have := h prog s0 [] .ret (fun a s => pure (a, s)) (fun a ws => pure (a, ws.reverse))
      (fun a s => ((a, s), [])) (fun x s ws => by simp [after, answerWithAt.go, pure])
    simp only [after, List.reverse_nil, List.nil_append] at this
    exact this
  intro X m
  induction m with
  | ret x => intro s ws Y kI kA kW ks h; exact h x s ws
  | delay q ih => intro s ws Y kI kA kW ks h; exact ih () s ws kI kA kW ks h
  | bind m f ihm ihf =>
    intro s ws Y kI kA kW ks h
    exact ihm s ws _ kA kW _ fun x s ws => ihf x s ws kI kA kW ks h
  | op pl o =>
    intro s ws Y kI kA kW ks h
    cases pl with
    | last => exact (h (clause s o).1 (clause s o).2 (describe o (clause s o).1 :: ws)).trans (after_told ..).symm
    | init pl =>
      cases pl with
      | init pl => exact nomatch pl
      | last => cases o with | tell w => exact (h () s (w :: ws)).trans (after_told ..).symm
  | impure pl o c ih =>
    intro s ws Y kI kA kW ks h
    cases pl with
    | last =>
      exact (ih (clause s o).1 (clause s o).2 (describe o (clause s o).1 :: ws) kI kA kW ks h).trans
        (after_told ..).symm
    | init pl =>
      cases pl with
      | init pl => exact nomatch pl
      | last => cases o with | tell w => exact (ih () s (w :: ws) kI kA kW ks h).trans (after_told ..).symm

/-- the path's value and state are the program's own, with no trail asked for -/
theorem path_value {S : Type} (describe : {X : Type} → E X → X → T) (clause : {X : Type} → S → E X → X × S)
    (s0 : S) (prog : A ! [E, Writer T]) :
    (run (writer T (answerWith (E := E) (fun a s => pure (a, s)) clause s0 prog))).1
      = (path describe clause prog s0).1 := by
  suffices h : ∀ {X : Type} (m : X ! [E, Writer T]) (s : S) (ws : List T) (kA : X → S → (A × S) ! [Writer T])
      (kW : A × S → List T → ((A × S) × List T) ! Pure) (ks : X → S → (A × S) × List T),
      (∀ x s ws, (run (answerWithAt.go .last tells (kA x s) ws kW)).1 = (ks x s).1) →
      (run (answerWithAt.go .last tells (answerWithAt.go .last clause m s kA) ws kW)).1
        = (path.go (A := A) describe clause m s ks).1
    from h prog s0 [] (fun a s => pure (a, s)) (fun a ws => pure (a, ws.reverse)) (fun a s => ((a, s), []))
      (fun _ _ _ => rfl)
  intro X m
  induction m with
  | ret x => intro s ws kA kW ks h; exact h x s ws
  | delay q ih => intro s ws kA kW ks h; exact ih () s ws kA kW ks h
  | bind m f ihm ihf =>
    intro s ws kA kW ks h
    exact ihm s ws _ kW _ fun x s ws => ihf x s ws kA kW ks h
  | op pl o =>
    intro s ws kA kW ks h
    cases pl with
    | last => exact h (clause s o).1 (clause s o).2 ws
    | init pl =>
      cases pl with
      | init pl => exact nomatch pl
      | last => cases o with | tell w => exact h () s (w :: ws)
  | impure pl o c ih =>
    intro s ws kA kW ks h
    cases pl with
    | last => exact ih (clause s o).1 (clause s o).2 ws kA kW ks h
    | init pl =>
      cases pl with
      | init pl => exact nomatch pl
      | last => cases o with | tell w => exact ih () s (w :: ws) kA kW ks h

/-- THE TRAIL CHANGES NOTHING: the value and the state of `E` are what they are with no trail -/
theorem trail_value {S : Type} (describe : {X : Type} → E X → X → T) (clause : {X : Type} → S → E X → X × S)
    (s0 : S) (prog : A ! [E, Writer T]) :
    (run (writer T (answerWith (E := E) (fun a s => pure (a, s)) clause s0 (trail describe prog)))).1
      = (run (writer T (answerWith (E := E) (fun a s => pure (a, s)) clause s0 prog))).1 := by
  rw [trail_path, path_value describe]

/-! ## The trail in any row, under any handlers — a handler resuming many times too -/

theorem trail_ret [In E R] [In (Writer T) R] (describe : {X : Type} → E X → X → T) (a : A) :
    trail (E := E) describe (.ret a : A ! R) = .ret a := rfl

/-- the trail goes through a bind -/
theorem trail_bind [In E R] [In (Writer T) R] (describe : {X : Type} → E X → X → T) (m : X ! R) (g : X → A ! R) :
    norm (trail (E := E) describe (m >>= g)) = norm (trail (E := E) describe m >>= fun x => trail (E := E) describe (g x)) :=
  around_bind _ m g

/-- AN OPERATION AND ITS REST: the operation asked as it is; with each answer the rest is given — by whatever
handler, as many times as it resumes — that answer is told, and the rest goes on, its trail kept. So a trail has an
entry for each time an operation is ANSWERED: one for a program of one path, one per resumption under a handler that
resumes many times -/
theorem trail_step [In E R] [In (Writer T) R] (describe : {X : Type} → E X → X → T) (o : E X) (g : X → A ! R) :
    norm (trail (E := E) describe (perform o >>= g))
      = norm (perform o >>= fun x => tell (describe o x) >>= fun _ => trail (E := E) describe (g x)) := by
  rw [trail_bind]
  exact fold_norm.congr (around_op _ o) _

/-- so for a choice under `all`: an entry for each value chosen, in order -/
theorem trail_among (describe : {X : Type} → Choose X → X → T) (xs : List A) :
    run (writer T (all (trail describe (among xs : A ! [Choose, Writer T])))) = (xs, xs.map (describe (.among xs))) := by
  suffices h : ∀ (ys : List A) (ws : List T) {B : Type} (kW : List A → List T → B ! Pure),
      run (answerWithAt.go .last tells
        (all.go ys fun x => .delay fun _ => .impure .last (.tell (describe (.among xs) x)) fun _ => pure [x]) ws kW)
        = run (kW ys ((ys.map (describe (.among xs))).reverse ++ ws)) by
    have := h xs [] fun a ws => pure (a, ws.reverse)
    simp only [List.append_nil, List.reverse_reverse] at this
    exact this
  intro ys
  induction ys with
  | nil => intro ws B kW; rfl
  | cons y ys ih =>
    intro ws B kW
    cases ys with
    | nil => rfl
    | cons z zs =>
      have := ih (describe (.among xs) y :: ws) fun b ws => kW (y :: b) ws
      simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] at this ⊢
      exact this

end Free

/-! ## Sensitive effects: handled only under their audit

A program asks a sensitive effect `E` as `Sensitive E`; its handler takes it as `Audited E`. The two are SEALED:
outside this file an operation of `Sensitive E` can be made (`sensitive`) and not read, one of `Audited E` read
(`Audited.op`) and not made. So no handler can answer a `Sensitive E` — an answer is of the operation's own type, and
it cannot see the operation —, and no program can ask an `Audited E`. `audit` alone goes from the one to the other,
and it tells each operation it passes on. `run` takes the empty row: a program that asked a sensitive operation and
runs has been audited. -/

/-- the seal: two copies of an effect, and the ways between. An `opaque` constant, private — to the rest of Lean
`Sensitive E X` and `Audited E X` are types it knows nothing of: no constructor, no `cases` -/
private structure Seal where
  Sensitive : Effect → Effect
  Audited : Effect → Effect
  ask : {E : Effect} → {X : Type} → E X → Sensitive E X
  asked : {E : Effect} → {X : Type} → Sensitive E X → E X
  pass : {E : Effect} → {X : Type} → E X → Audited E X
  passed : {E : Effect} → {X : Type} → Audited E X → E X
  asked_ask : ∀ {E : Effect} {X : Type} (o : E X), asked (ask o) = o
  passed_pass : ∀ {E : Effect} {X : Type} (o : E X), passed (pass o) = o

private opaque sealing : Seal := ⟨id, id, id, id, id, id, fun _ => rfl, fun _ => rfl⟩

/-- the sensitive effect `E` as a program asks it: made by `sensitive`, read by its audit alone -/
def Sensitive (E : Effect) : Effect := sealing.Sensitive E

/-- the sensitive effect `E` as its handler takes it: made by its audit alone, read by `Audited.op` -/
def Audited (E : Effect) : Effect := sealing.Audited E

/-- an audited operation: the operation, for its handler -/
def Audited.op (a : Audited E X) : E X := sealing.passed a

/-- a sensitive operation asked -/
def sensitive [In (Sensitive E) R] (o : E X) : X ! R := perform (E := Sensitive E) (sealing.ask o)

/-- an operation past its audit: asked of the handler of `Audited E`, and told with its answer. The audit's only
way on -/
private def passed [In (Audited E) R] [In (Writer T) R] (describe : {X : Type} → E X → X → T) (o : E X) : X ! R :=
  perform (E := Audited E) (sealing.pass o) >>= fun x => tell (describe o x) >>= fun _ => pure x

/-- THE AUDIT of the sensitive effect `E`, with a policy: `clause` gets each operation, the way on `pass`, and the
rest `k`. `pass o` asks `o` — the operation it got, or another in its place — of the handler outside and TELLS it
with its answer (`describe`) to the `Writer T`; there is no other way to that handler. The clause may also answer
itself, refuse (not resume `k`), ask other effects of the row outside -/
def auditWith [Split (Sensitive E) R Rest] [In (Audited E) Rest] [In (Writer T) Rest]
    (describe : {X : Type} → E X → X → T) (ret : A → B ! Rest)
    (clause : {X : Type} → E X → ({Y : Type} → E Y → Y ! Rest) → (X → B ! Rest) → B ! Rest) : A ! R → B ! Rest :=
  Free.handle (E := Sensitive E) ret fun s k => clause (sealing.asked s) (passed describe) k

/-- the audit of the sensitive effect `E`: each operation passed on as it is, and told with its answer -/
def audit [Split (Sensitive E) R Rest] [In (Audited E) Rest] [In (Writer T) Rest]
    (describe : {X : Type} → E X → X → T) : A ! R → A ! Rest :=
  auditWith describe pure fun o pass k => pass o >>= k

/-- an audited operation read: the operation that passed -/
private theorem op_pass (o : E X) : Audited.op (sealing.pass o : Audited E X) = o := sealing.passed_pass o

namespace Free

/-! ### What the audit makes of a program -/

theorem auditWith_ret [Split (Sensitive E) R Rest] [In (Audited E) Rest] [In (Writer T) Rest]
    (describe : {X : Type} → E X → X → T) (ret : A → B ! Rest)
    (clause : {X : Type} → E X → ({Y : Type} → E Y → Y ! Rest) → (X → B ! Rest) → B ! Rest) (a : A) :
    auditWith describe ret clause (.ret a : A ! R) = ret a := rfl

/-- a sensitive operation and its rest: the clause's, with the operation, the way on, and the rest audited -/
theorem auditWith_step [s : Split (Sensitive E) R Rest] [In (Audited E) Rest] [In (Writer T) Rest]
    (describe : {X : Type} → E X → X → T) (ret : A → B ! Rest)
    (clause : {X : Type} → E X → ({Y : Type} → E Y → Y ! Rest) → (X → B ! Rest) → B ! Rest) (o : E X)
    (g : X → A ! R) :
    auditWith describe ret clause (sensitive o >>= g)
      = clause o (passed describe) fun x => .delay fun _ => auditWith describe ret clause (g x) := by
  refine (Place.taken_self s.place (sealing.ask o : Sensitive E X) _ _).trans ?_
  simp only [sealing.asked_ask]
  rfl

/-- under `audit`: the operation passed on and told, then the rest audited -/
theorem audit_step [Split (Sensitive E) R Rest] [In (Audited E) Rest] [In (Writer T) Rest]
    (describe : {X : Type} → E X → X → T) (o : E X) (g : X → A ! R) :
    norm (audit describe (sensitive o >>= g)) = norm (passed describe o >>= fun x => audit describe (g x)) := by
  show norm (auditWith _ _ _ _) = _
  rw [auditWith_step]
  rfl

/-! ### The audit's trail of one path

`E` behind its audit, answered in place by `clause` from a state, the trail collected outside. The program can ask
`E` (`sensitive`) and tell; it cannot make an operation of `Audited E`. So these two equations and `auditWith_ret`
give the trail of any such program: its sensitive operations, each with its answer, and its own tells, in order. -/

/-- a writer that starts from `ws0` told: its trail behind `ws0` -/
private theorem writer_from (m : X ! [Writer T]) : ∀ (ws ws0 : List T) (k : X → List T → (B × List T) ! Pure),
    (∀ x ws ws0, run (k x (ws ++ ws0)) = after ws0 (run (k x ws))) →
    run (answerWithAt.go .last tells m (ws ++ ws0) k) = after ws0 (run (answerWithAt.go .last tells m ws k)) := by
  induction m with
  | ret x => intro ws ws0 k h; exact h x ws ws0
  | delay q ih => intro ws ws0 k h; exact ih () ws ws0 k h
  | bind m f ihm ihf => intro ws ws0 k h; exact ihm ws ws0 _ fun x ws ws0 => ihf x ws ws0 k h
  | op pl o =>
    intro ws ws0 k h
    cases pl with
    | init pl => exact nomatch pl
    | last => cases o with | tell w => exact h () (w :: ws) ws0
  | impure pl o c ih =>
    intro ws ws0 k h
    cases pl with
    | init pl => exact nomatch pl
    | last => cases o with | tell w => exact ih () (w :: ws) ws0 k h

/-- `t` told, then `m`: `t` before `m`'s trail -/
private theorem writer_told (t : T) (m : B ! [Writer T]) :
    run (answerWithAt.go .last tells m [t] fun a ws => pure (a, ws.reverse)) = told t (run (writer T m)) :=
  writer_from m [] [t] _ fun x ws ws0 => by simp [after, pure]

/-- the operation passed on, met by the handler of `Audited E`: answered, and the telling of it left -/
private theorem answer_passed {S : Type} (describe : {X : Type} → E X → X → T)
    (clause : {X : Type} → S → E X → X × S) (ret : A → S → B ! [Writer T]) (s : S) (o : E X)
    (k : X → A ! [Audited E, Writer T]) :
    answerWith (E := Audited E) ret (fun s a => clause s a.op) s (passed describe o >>= k)
      = .impure .last (.tell (describe o (clause s o).1)) fun _ =>
          answerWith (E := Audited E) ret (fun s a => clause s a.op) (clause s o).2 (k (clause s o).1) := by
  show (match clause s (Audited.op (sealing.pass o : Audited E X)) with
    | (x, s') => (Free.impure .last (Writer.tell (describe o x)) fun _ =>
        answerWith (E := Audited E) ret (fun s a => clause s a.op) s' (k x) : B ! [Writer T])) = _
  rw [op_pass]

/-- a sensitive operation: answered by the handler, told with its answer, then the rest from the new state -/
theorem audit_sensitive {S : Type} (describe : {X : Type} → E X → X → T) (clause : {X : Type} → S → E X → X × S)
    (s : S) (o : E X) (g : X → A ! [Sensitive E, Audited E, Writer T]) :
    run (writer T (answerWith (E := Audited E) (fun a s => pure (a, s)) (fun s a => clause s a.op) s
      (audit describe (sensitive o >>= g))))
    = told (describe o (clause s o).1)
        (run (writer T (answerWith (E := Audited E) (fun a s => pure (a, s)) (fun s a => clause s a.op) (clause s o).2
          (audit describe (g (clause s o).1))))) := by
  rw [show answerWith (E := Audited E) (fun a s => pure (a, s)) (fun s a => clause s a.op) s
        (audit describe (sensitive o >>= g))
      = answerWith (E := Audited E) (fun a s => pure (a, s)) (fun s a => clause s a.op) s
        (passed describe o >>= fun x => audit describe (g x))
      from answerWithAt_congr _ _ _ s (audit_step describe o g),
    answer_passed, ← writer_told]
  rfl

/-- a `tell` of the program's own: in the trail as it is -/
theorem audit_tell {S : Type} (describe : {X : Type} → E X → X → T) (clause : {X : Type} → S → E X → X × S)
    (s : S) (w : T) (g : Unit → A ! [Sensitive E, Audited E, Writer T]) :
    run (writer T (answerWith (E := Audited E) (fun a s => pure (a, s)) (fun s a => clause s a.op) s
      (audit describe (tell w >>= g))))
    = told w (run (writer T (answerWith (E := Audited E) (fun a s => pure (a, s)) (fun s a => clause s a.op) s
        (audit describe (g ()))))) :=
  writer_told w _

end Free
end Okay.Effects
