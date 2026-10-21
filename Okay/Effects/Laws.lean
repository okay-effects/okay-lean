import Okay.Effects.Free

/-!
# THE LAWS, proved

A program is data with `bind` and `delay` nodes, so the monad laws are not equalities of data: `bind (ret a) f` is a
node, `f a` is not. They hold UP TO STEPS — `Eqv`, two programs the same but for delays — after normalization:
`norm` follows the binds and forces the delays; associativity is then `rfl`, the unit laws a `delay` apart. And
`run` sees no difference, `run_congr`; on `run` the laws are equalities: `run_ret`, `run_bind`, `run_delay`.
-/

namespace Okay.Effects.Free

/-- the same program but for delays, structurally: values and operations in step, a delay on either side skipped -/
inductive Eqv : A ! R → A ! R → Prop
  | ret (a : A) : Eqv (.ret a) (.ret a)
  | impure (op : At R X) {c c' : X → A ! R} (h : ∀ x, Eqv (c x) (c' x)) : Eqv (.impure op c) (.impure op c')
  | bind {m : X ! R} {f f' : X → A ! R} (h : ∀ x, Eqv (f x) (f' x)) : Eqv (.bind m f) (.bind m f')
  | delayL {p : Unit → A ! R} {q : A ! R} (h : Eqv (p ()) q) : Eqv (.delay p) q
  | delayR {p : A ! R} {q : Unit → A ! R} (h : Eqv p (q ())) : Eqv p (.delay q)

infix:50 " ≋ " => Eqv

theorem Eqv.refl : (p : A ! R) → p ≋ p
  | .ret a => .ret a
  | .impure op c => .impure op fun x => refl (c x)
  | .bind _ f => .bind fun x => refl (f x)
  | .delay p => .delayL (.delayR (refl (p ())))

/-! ## Normalization -/

/-- normalizing goes on the same but for delays when its continuations do -/
theorem norm_go_congr (m : X ! R) {k k' : X → A ! R} (h : ∀ x, k x ≋ k' x) : norm.go m k ≋ norm.go m k' := by
  induction m with
  | ret x => exact h x
  | bind m f ihm ihf => exact ihm fun x => .delayL (.delayR (ihf x h))
  | impure op c ih => exact .impure op fun x => ih x h
  | delay q ih => exact ih () h

/-- normalizing respects `Eqv` -/
theorem norm_go_eqv {m m' : X ! R} (hm : m ≋ m') {k k' : X → A ! R} (hk : ∀ x, k x ≋ k' x) :
    norm.go m k ≋ norm.go m' k' := by
  induction hm with
  | ret a => exact hk a
  | impure op _ ih => exact .impure op fun x => ih x hk
  | bind _ ih => exact norm_go_congr _ fun x => .delayL (.delayR (ih x hk))
  | delayL _ ih => exact ih hk
  | delayR _ ih => exact ih hk

theorem norm_eqv {p q : A ! R} (h : p ≋ q) : norm p ≋ norm q := norm_go_eqv h fun a => .ret a

/-! ## The monad laws, up to steps after normalization -/

theorem pure_bind (a : X) (f : X → A ! R) : norm (.bind (.ret a) f) ≋ norm (f a) :=
  .delayL (Eqv.refl _)

theorem bind_pure (m : A ! R) : norm (.bind m .ret) ≋ norm m :=
  norm_go_congr m fun x => .delayL (.ret x)

theorem bind_assoc (m : X ! R) (f : X → Y ! R) (g : Y → A ! R) :
    norm (.bind (.bind m f) g) = norm (.bind m fun x => .bind (f x) g) := rfl

/-! ## `run` -/

theorem force_eqv {p q : A ! Pure} (h : p ≋ q) : run.force p = run.force q := by
  induction h with
  | ret a => rfl
  | impure op _ _ => exact nomatch op
  | bind _ ih => exact ih _
  | delayL _ ih => exact ih
  | delayR _ ih => exact ih

/-- programs the same but for delays run to the same value -/
theorem run_congr {p q : A ! Pure} (h : p ≋ q) : run p = run q := force_eqv (norm_eqv h)

/-- forcing a normalization with a continuation: the continuation at the value -/
theorem force_go (m : X ! Pure) : ∀ {A : Type} (k : X → A ! Pure),
    run.force (norm.go m k) = run.force (k (run m)) := by
  induction m with
  | ret x => intro A k; rfl
  | delay q ih => intro A k; exact ih () k
  | impure op _ _ => intro A k; exact nomatch op
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

end Okay.Effects.Free
