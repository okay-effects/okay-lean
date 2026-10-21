# okay-lean — notes for agents

- Lean 4, `v4.35.0` pinned in `lean-toolchain`; no dependencies. `lake build` builds the library and checks the
  proofs; `lake test` runs `Tests/Main.lean` (the `test` executable, lake's test driver). Both must pass before a
  commit; no `sorry` — Lean only warns about it, so grep the build output.
- The specification is okay-simple (`~/work/my/okay-simple`, `core/free/.../Free.scala`, `Places.scala`, `Std.scala`):
  a program is data (`Free.ret`, `Free.bind`, `Free.impure op k`), the row a `List Effect` with the handled-next effect FIRST
  (okay-simple's `R + E` has it last), places typed (`Place`, `Split` with `Rest` an `outParam`, `In`), handlers
  `handle` / `answer` / `handleWith` / `handleAt`. Port the next pieces the same way: `Delimited` (shift and
  reset), `Sub`/`embed`, `Yield`, `Fresh`, `Random`, `Store` are not here yet.
- Lean's universes: `Free R A : Type 1` (the existential `X` in `impure`), so `At`, `Place` are `Type 1` too; effects
  are `Type → Type`. An effect carrying a program as an answer would need a universe bump — not done.
- Notation `A ! R` is `Free R A`; application binds tighter, so write `(List A) ! R`. A handler of a parameterized
  effect whose parameter the value does not fix takes it explicitly: `writer String`, `attempt String`; a word whose
  parameter the row does not fix needs an ascription: `let name : String ← ask`.
- The stack: a program has `bind` nodes, NO `delay` (the user's decision, 2026-10-21: laws as equalities over a
  trampoline). Every interpreter (`norm`, `handleAt`, `handleWith`, `answer`, `answerWith`) is a total structural
  loop `go m k` in continuation-passing style; its self calls are tail calls (`goto _start` in C), the continuation
  call `k x` a tail branch too (`b _lean_apply_2`). But Lean's runtime `lean_apply_N` calls the closure's function
  with `blr` on some paths, so a chain of continuations still grows the stack, slowly: measured
  (`Probe/Stack.lean`, `lake build stack`, `.lake/build/bin/stack <n> state|reader|left|choose`) 6*10^6 operations
  pass, 8*10^6 overflow, for `state`, a left-nested bind and a chain of choices alike; `ulimit -s` does not move
  the threshold. With a `delay` node and trampolined continuations (commit 6868b74) 10^8 passed; that design is in
  git if the limit ever matters. All four shapes are linear in time (10^6 in 0.2-0.5 s).
- Laws: the monad laws are equalities after normalization, each `rfl` (`pure_bind`, `bind_pure`, `bind_assoc`),
  `norm_norm`; on `run` as they stand (`run_ret`, `run_bind`). A standard handler's single-operation law is `rfl` (`state_get`...);
  one with binds in it goes through `run` and `simp` (`all_among`).
- Commits: no Co-Authored-By lines.
