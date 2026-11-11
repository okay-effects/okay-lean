import Okay.Effects.Free
import Okay.Effects.Laws

/-!
# INTERCEPTORS: control of an effect, the program unchanged

okay-simple's `intercept`, `observe`, `around`. An interceptor is a handler whose effect STAYS in the row
(`Free.interceptAt`): every operation of the effect passes it — seen, changed, answered, refused, or asked again, and
then the next handler out answers it. Its laws are proved here: what it makes of a value, of its own operation, of
another's, of a bind; an interceptor that asks everything again is no interceptor; `around` goes through a bind as a
handler does; an observer whose observations come to nothing under an interpreter is not seen by it.
-/

namespace Okay.Effects
namespace Free

/-- around each operation of `E`: `f` gets it and its way on, `proceed` — the operation asked again as it was — and
gives the program in its place: `proceed`, something before or after it, another operation, or an answer of its own
and no `proceed` -/
def around [i : In E R] (f : {X : Type} → E X → X ! R → X ! R) : A ! R → A ! R :=
  intercept (E := E) .ret fun e k => .bind (f e (perform e)) k

/-- each operation of `E` seen by `f`, then asked again as it was: a count, a trace, a check -/
def observe [In E R] (f : {X : Type} → E X → Unit ! R) : A ! R → A ! R :=
  around (E := E) fun e proceed => .bind (f e) fun _ => proceed

/-! ## What an interceptor makes of a program, by computation -/

theorem interceptAt_ret (p : Place E R Rest) (ret : A → B ! R) (clause : {X : Type} → E X → (X → B ! R) → B ! R)
    (a : A) : interceptAt p ret clause (.ret a) = ret a := rfl

/-- its own operation: the clause's, the rest the value's clause -/
theorem interceptAt_op (p : Place E R Rest) (ret : A → B ! R) (clause : {X : Type} → E X → (X → B ! R) → B ! R)
    (o : E A) : interceptAt p ret clause (.op p o) = clause o fun x => .delay fun _ => ret x := by
  simp only [interceptAt, interceptAt.go, Place.own_self]

/-- an operation at another place: passed on where it is -/
theorem interceptAt_other (p : Place E R Rest) (ret : A → B ! R) (clause : {X : Type} → E X → (X → B ! R) → B ! R)
    (pl : Place E2 R Rest2) (o : E2 A) (h : p.same pl = .no) :
    interceptAt p ret clause (.op pl o) = .impure pl o ret := by
  simp only [interceptAt, interceptAt.go, Place.own, h]

/-- a bind: the first part intercepted, its value's clause the rest intercepted — as a deep handler's -/
theorem interceptAt_bind (p : Place E R Rest) (ret : A → B ! R) (clause : {X : Type} → E X → (X → B ! R) → B ! R)
    (m : X ! R) (f : X → A ! R) :
    interceptAt p ret clause (.bind m f) = interceptAt p (fun x => interceptAt p ret clause (f x)) clause m := rfl

/-! ## The interceptor that asks everything again is none -/

/-- every operation asked again as it is, at its place: the program, after normalization -/
theorem interceptAt_pass (p : Place E R Rest) (prog : A ! R) :
    norm (interceptAt p .ret (fun e k => .bind (.op p e) k) prog) = norm prog := by
  suffices h : ∀ {X : Type} (m : X ! R) {Y : Type} (k : X → Y ! R) (c : Y → A ! R),
      norm.go (interceptAt.go p (fun e k => .bind (.op p e) k) m k) c = norm.go m fun x => norm.go (k x) c
    from h prog .ret .ret
  intro X m
  induction m with
  | ret x => intro Y k c; rfl
  | delay q ih => intro Y k c; exact ih () k c
  | op pl o =>
    intro Y k c
    simp only [interceptAt.go, Place.own]
    cases p.same pl <;> rfl
  | impure pl o c' ih =>
    intro Y k c
    simp only [interceptAt.go, Place.own]
    cases p.same pl <;> exact congrArg _ (funext fun x => ih x k c)
  | bind m f ihm ihf =>
    intro Y k c
    show norm.go (interceptAt.go p _ m _) c = norm.go m _
    rw [ihm]
    exact congrArg _ (funext fun x => ihf x k c)

theorem intercept_pass [In E R] (prog : A ! R) :
    norm (intercept (E := E) pure (fun e k => perform e >>= k) prog) = norm prog :=
  interceptAt_pass _ prog

/-- `around` whose `f` proceeds: the program -/
theorem around_proceed [In E R] (prog : A ! R) : norm (around (E := E) (fun _ proceed => proceed) prog) = norm prog :=
  interceptAt_pass _ prog

/-! ## `around` and a bind -/

/-- `around` with a rest: `around` to a value, then the rest — the clause keeps nothing of `k` but its bind -/
theorem around_go [i : In E R] (f : {X : Type} → E X → X ! R → X ! R) (m : X ! R) :
    ∀ {Y : Type} (k : X → Y ! R) {A : Type} (c : Y → A ! R),
      norm.go (interceptAt.go i.place (fun e k => .bind (f e (perform e)) k) m k) c
        = norm.go (interceptAt.go i.place (fun e k => .bind (f e (perform e)) k) m .ret) fun x => norm.go (k x) c := by
  induction m with
  | ret x => intro Y k A c; rfl
  | delay q ih => intro Y k A c; exact ih () k c
  | op pl o =>
    intro Y k A c
    simp only [interceptAt.go, Place.own]
    cases i.place.same pl <;> rfl
  | impure pl o c' ih =>
    intro Y k A c
    simp only [interceptAt.go, Place.own]
    cases i.place.same pl <;> exact congrArg _ (funext fun x => ih x k c)
  | bind m g ihm ihg =>
    intro Y k A c
    show norm.go (interceptAt.go i.place _ m _) c = norm.go (interceptAt.go i.place _ m _) _
    rw [ihm, ihm (fun x => interceptAt.go i.place _ (g x) .ret)]
    exact congrArg _ (funext fun x => ihg x k c)

theorem around_ret [In E R] (f : {X : Type} → E X → X ! R → X ! R) (a : A) :
    around (E := E) f (.ret a : A ! R) = .ret a := rfl

/-- an operation of `E`: what `f` puts in its place -/
theorem around_op [In E R] (f : {X : Type} → E X → X ! R → X ! R) (o : E A) :
    norm (around (E := E) f (perform o)) = norm (f o (perform o)) := by
  show norm (interceptAt _ _ _ (.op _ o)) = _
  rw [interceptAt_op]
  rfl

/-- `around` goes through a bind: the two parts, each around -/
theorem around_bind [In E R] (f : {X : Type} → E X → X ! R → X ! R) (m : X ! R) (g : X → A ! R) :
    norm (around (E := E) f (.bind m g)) = norm (.bind (around (E := E) f m) fun x => around (E := E) f (g x)) :=
  around_go f m (fun x => interceptAt.go _ _ (g x) .ret) .ret

/-! ## An observer does not change the program -/

/-- to an interpreter `H` under which each observation comes to nothing — its value `()`, no other trace — the
observed program is the program -/
theorem observe_unseen [i : In E R] {H : {X : Type} → X ! R → (X → C) → C} (h : Fold H)
    (f : {X : Type} → E X → Unit ! R) (hf : ∀ {X : Type} (e : E X) (k : Unit → C), H (f e) k = k ())
    (prog : A ! R) (k : A → C) : H (observe (E := E) f prog) k = H prog k := by
  suffices g : ∀ {X : Type} (m : X ! R) {Y : Type} (kI : X → Y ! R) (k : Y → C),
      H (interceptAt.go i.place (fun e k => .bind (.bind (f e) fun _ => perform e) k) m kI) k
        = H m fun x => H (kI x) k by
    have := g prog .ret k
    simp only [h.ret] at this
    exact this
  intro X m
  induction m with
  | ret x => intro Y kI k; rw [h.ret]; rfl
  | delay q ih => intro Y kI k; rw [h.delay]; exact ih () kI k
  | op pl o =>
    intro Y kI k
    simp only [interceptAt.go, Place.own]
    cases i.place.same pl with
    | yes => simp only [h.bind, hf, h.delay]; rfl
    | no => exact h.impure pl o kI k
  | impure pl o c ih =>
    intro Y kI k
    simp only [interceptAt.go, Place.own]
    cases i.place.same pl with
    | yes => simp only [h.bind, hf, h.delay, h.impure, ih]; rfl
    | no => simp only [h.impure, ih]
  | bind m g ihm ihg =>
    intro Y kI k
    show H (interceptAt.go i.place _ m _) k = _
    rw [ihm, h.bind]
    exact congrArg _ (funext fun x => ihg x kI k)

/-- an observer that only looks: the program, after normalization -/
theorem observe_pure [In E R] (prog : A ! R) : norm (observe (E := E) (fun _ => pure ()) prog) = norm prog :=
  observe_unseen fold_norm _ (fun _ _ => rfl) prog .ret

/-- an observer that tells a handler answering in place — `w e`, an operation of `W` at `pw` — is not in what that
handler makes of the program: the observations are answered, and nothing of them is left -/
theorem answerAt_observe [In E R] (pw : Place W R Rest) (ret : A → B ! Rest) (clause : {X : Type} → W X → X)
    (w : {X : Type} → E X → W Unit) (prog : A ! R) :
    answerAt pw ret clause (observe (E := E) (fun e => .op pw (w e)) prog) = answerAt pw ret clause prog :=
  observe_unseen (fold_answerAt pw clause) _ (fun e k => by simp only [answerAt.go, Place.taken_self]) prog ret

end Free
end Okay.Effects
