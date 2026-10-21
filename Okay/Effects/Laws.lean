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
  | op o => intro k; rfl
  | impure op c ih => intro k; exact congrArg _ (funext fun x => ih x k)
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
  | op o => intro A k; exact nomatch o
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
