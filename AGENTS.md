# okay-lean — notes for agents

- Lean 4, `v4.35.0` pinned in `lean-toolchain`; no dependencies. `lake build` builds the library and checks the
  proofs; `lake test` runs `Tests/Main.lean` (the `test` executable, lake's test driver). Both must pass before a
  commit; no `sorry` — Lean only warns about it, so grep the build output.
- The specification is okay-simple (`~/work/my/okay-simple`, `core/free/.../Free.scala`, `Places.scala`, `Std.scala`):
  a program is data (`Free.ret`, `Free.bind`, `Free.impure op k`, `Free.delay`), the row a `List Effect` with the handled-next effect FIRST
  (okay-simple's `R + E` has it last), places typed (`Place`, `Split` with `Rest` an `outParam`, `In`), handlers
  `handle` / `answer` / `handleWith` / `handleAt`. Port the next pieces the same way: `Delimited` (shift and
  reset), `Sub`/`embed`, `Yield`, `Fresh`, `Random`, `Store` are not here yet.
- Lean's universes: `Free R A : Type 1` (the existential `X` in `impure`), so `At`, `Place` are `Type 1` too; effects
  are `Type → Type`. An effect carrying a program as an answer would need a universe bump — not done.
- Notation `A ! R` is `Free R A`; application binds tighter, so write `(List A) ! R`. A handler of a parameterized
  effect whose parameter the value does not fix takes it explicitly: `writer String`, `attempt String`; a word whose
  parameter the row does not fix needs an ascription: `let name : String ← ask`.
- The stack, as okay-simple: a program has `bind` and `delay` nodes; every interpreter (`norm`, `handleAt`,
  `handleWith`, `answer`, `answerWith`) is a structural loop `go m k` in continuation-passing style, its self calls
  tail calls (Lean compiles them to `goto _start`), and every continuation it hands out — to a bind's `f` or a
  clause's `k` — is a TRAMPOLINE returning `delay fun _ => go ...` at once, forced by the loop outside (the next
  handler's, or `run.force`). No `partial`: everything total, so provable. Measured (`Probe/Stack.lean`,
  `lake build stack`, `.lake/build/bin/stack <n> state|reader|left|choose`, `ulimit -s 8192`): 10^7 operations
  under `state`, `reader`, a left-nested bind (`foldl`), a chain of choice points under `all` — all linear, 0.4–2 s.
  Before the trampolines a clause resuming `k` through a closure overflowed near 3·10^6, and the left-nested bind was
  quadratic.
- Laws: the monad laws hold up to STEPS after normalization — `Eqv` (`≋`), two programs the same but for delays;
  `bind_assoc` is `rfl`, `pure_bind` and `bind_pure` a delay apart; on `run` they are equalities (`run_ret`,
  `run_bind`, `run_delay`, `run_congr`). A standard handler's single-operation law is `rfl` (`state_get`...);
  one with binds in it goes through `run` and `simp` (`all_among`).
- Commits: no Co-Authored-By lines.
