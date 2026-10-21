import Okay.Effects.Free

/-!
# THE LAWS, proved: `Free R` is a lawful monad; a program of no effect runs to its value
-/
namespace Okay.Effects.Free

@[simp] theorem bind_ret_left (a : A) (f : A → B ! R) : bind (ret a) f = f a := rfl

@[simp] theorem bind_impure (op : At R X) (k : X → A ! R) (f : A → B ! R) :
    bind (impure op k) f = impure op fun x => bind (k x) f := rfl

theorem bind_ret (p : A ! R) : bind p ret = p := by
  induction p with
  | ret a => rfl
  | impure op k ih => simp [ih]

theorem bind_assoc (p : A ! R) (f : A → B ! R) (g : B → C ! R) :
    bind (bind p f) g = bind p fun a => bind (f a) g := by
  induction p with
  | ret a => rfl
  | impure op k ih => simp [ih]

instance : LawfulMonad (Free R) :=
  LawfulMonad.mk' (Free R)
    (id_map := fun p => bind_ret p)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := bind_assoc)

@[simp] theorem run_ret (a : A) : run (ret a : A ! Pure) = a := rfl

end Okay.Effects.Free
