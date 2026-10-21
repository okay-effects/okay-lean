# okay-lean — notes for agents

- Lean 4, `v4.35.0` pinned in `lean-toolchain`; no dependencies. `lake build` builds the library and checks the
  proofs; `lake test` runs `Tests/Main.lean` (the `test` executable, lake's test driver). Both must pass before a
  commit; no `sorry` — Lean only warns about it, so grep the build output.
- The specification is okay-simple (`~/work/my/okay-simple`, `core/free/.../Free.scala`, `Places.scala`, `Std.scala`):
  a program is data (`Free.ret`, `Free.bind`, `Free.op o` — an operation alone, what `perform` makes, okay-simple's `Perform` —
  `Free.impure op k`, `Free.delay`), the row a `List Effect` with the handled-next effect FIRST
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
  `ulimit -s 8192`): 10^8 operations under `state` (10 s), `reader` (2.6 s), a left-nested bind of 10^8 layers
  (14.6 s), a chain of 10^8 choice points under `all` (16 s) — linear, no stack growth. Before: CPS with closures grew
  the stack through Lean's `lean_apply_N` (not always a tail call), overflowing near 7*10^6.
- AGAINST okay-simple's Free (Scala 3, JVM, `Probe/StackProbe.scala`, the same four shapes; JVM's second round,
  warmed): n = 10^7 — `state` Lean 1.00 s / Scala 0.26 s, `reader` 0.27 / 0.06, left-nested bind 1.46 / 1.28,
  chain of choices under `all` 1.29 / 8.14. n = 10^8 — `state` 10.0 / 2.96, `reader` 2.6 / 0.67, left 14.6 / 11.4,
  choices 16.2 / OutOfMemory (12 GB heap). So: 4x behind on the sequential shapes (allocation: mimalloc + reference
  counts against a bump allocator and a JIT inlining the clause), level on the left-nested bind, 6x ahead on the
  deep handler, and no memory cliff.
- Performance (2026-10-21, `sample` of `state`): ~45% allocation and freeing of the program's nodes (`At.here`,
  `op`, `bind`, a closure per step), ~14% `lean_apply_1` (a bind's `f`), ~6% `lean_apply_3` (the clause — the
  specialized loop still calls it, 4 call sites), ~18% the loop itself. Done: `op` (no `ret` closure, no call, no
  bind re-association per `perform`: -25..35%); `Place.taken` (take in CPS, no `Sum`), `andThen` (no bind node for
  a value rest), `@[specialize]` on the loops — these three measured nothing. Next, if ever: fewer nodes per
  operation (an `At` path folded into `op`, a one-call-site clause so it inlines); ~100 ns per `state` operation
  against okay-simple's ~15 ns on the JVM — allocation is the gap, not the loop.
- Laws: the monad laws are equalities after normalization, each `rfl` (`pure_bind`, `bind_pure`, `bind_assoc`),
  `norm_norm`; on `run` as they stand (`run_ret`, `run_bind`, `run_delay`). A standard handler's single-operation law is `rfl` (`state_get`...);
  one with binds in it goes through `run` and `simp` (`all_among`).
- Commits: no Co-Authored-By lines.
