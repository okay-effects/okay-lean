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
- TWO DEFINITIONS OF EACH INTERPRETER (`run`, `handleAt`, `handleWithAt`, `answerAt`, `answerWithAt`): the
  reference, total structural recursion in CPS (`go m k`) — what every theorem is about — and the one that RUNS,
  `@[implemented_by]`, `unsafe`: okay-simple's loop, a bind of a value stepped, a left-nested bind re-associated as
  DATA (`bind (bind m f) g` to `bind m fun y => bind (f y) g`), every step a self tail call (`goto _start` in C).
  It cannot be structural (the re-associated term is no subterm), hence `unsafe`, as Lean's own fast paths. Binds are
  not delayed; a deep handler's `k` is a trampoline, `delay fun _ => loop ...`, forced by the loop outside (as in
  okay-simple). Change the reference and the loop TOGETHER; the loop is unproved against the reference.
- Measured (`Probe/Stack.lean`, `lake build stack`, `.lake/build/bin/stack <n> state|reader|left|choose`,
  `ulimit -s 8192`): 10^8 operations under `state` (11.5 s), `reader` (3.6 s), a left-nested bind of 10^8 layers
  (17 s), a chain of 10^8 choice points under `all` (18 s) — linear, no stack growth. Before: CPS with closures grew
  the stack through Lean's `lean_apply_N` (not always a tail call), overflowing near 7*10^6.
- Laws: the monad laws are equalities after normalization, each `rfl` (`pure_bind`, `bind_pure`, `bind_assoc`),
  `norm_norm`; on `run` as they stand (`run_ret`, `run_bind`, `run_delay`). A standard handler's single-operation law is `rfl` (`state_get`...);
  one with binds in it goes through `run` and `simp` (`all_among`).
- Commits: no Co-Authored-By lines.
