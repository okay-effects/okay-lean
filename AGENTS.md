# okay-lean — notes for agents

- Lean 4, `v4.35.0` pinned in `lean-toolchain`; no dependencies. `lake build` builds the library and checks the
  proofs; `lake test` runs `Tests/Main.lean` (the `test` executable, lake's test driver). Both must pass before a
  commit; no `sorry` — Lean only warns about it, so grep the build output.
- The specification is okay-simple (`~/work/my/okay-simple`, `core/free/.../Free.scala`, `Places.scala`, `Std.scala`):
  a program is data (`Free.ret`, `Free.bind`, `Free.op pl o` — an operation alone at its place, what `perform` makes,
  okay-simple's `Perform` —, `Free.impure pl o k`, `Free.delay`); an operation carries its `Place` and the effect's
  operation, no `At` path (folded in, 2026-10-21); a handler meets it with `Place.taken` (okay-simple's `Taken.Mine`/`Theirs`), the row a `List Effect` with the handled-next effect FIRST
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
- AGAINST okay-simple (Scala 3, JDK 26, okay-simple edf1938), its MACHINE and its `Free`, each as it is
  (`Probe/StackProbe.scala`: `<machine|free> <n> <shape>`, each pair in its OWN JVM — run in one sbt JVM the shapes
  pollute each other's JIT profile and Free looked 2x slower — 5 rounds, median of rounds 2–5; Lean 5 runs, median).
  n = 10^8, seconds:

  | shape | Lean Free | Scala machine | Scala Free |
  |---|---|---|---|
  | `state` | 8.62 | 1.70 | 1.93 |
  | `reader` | 2.36 | 0.79 | 0.85 |
  | left-nested bind | 13.84 | 8.9 | 13.3 |
  | chain of choices under `all` | 4.07 | 1.45 (was 2.85) | 1.29 |

  Lean is 4.5–5x behind on `state`, ~3x on `reader` and the choices against the faster of the two, level with Scala's
  Free on the left-nested bind and 1.6x behind the machine there. Lean's runs vary under 2%, the JVM's up to 30%.
  The machine's choices were 2.85 s until okay-simple 2026-10-22: a handler of a one-effect row was moved to the end
  by a `Remap` level crossed and rebuilt per operation, and `k` resumed through a step record; fixed there (the
  handler holds its `Place`, `take` as in Free; `Resume` in the hot loop).
- THE LEFT-NESTED BIND (2026-10-22, `stack <n> leftSplit`, Scala `<impl> <n> leftSplit`: build and run timed
  apart). The program — 10^8 binds — is built whole before it runs and lives whole while it runs (~7.5 GB), unlike
  the other shapes, made as they go. Lean: build ~8 ns, run ~127 ns a layer, the same from 10^4 to 10^8 — pure work,
  no memory effect: `state`'s ~86 ns plus a bind and its re-association (a bind node and a closure per layer). The
  JVM: ~50–80 ns a layer (machine), ~70–120 (Free) at 10^6, in the young generation; at 10^8 the live structure
  makes it GC-bound — stop-the-world pauses 39% of the wall time (machine), 56% (Free), on G1, plus concurrent
  marking on other cores — and the GC chosen moves it 2x (Free: G1 ~11.5 s, ParallelGC ~14.5 s, ParallelGC with an
  8 GB young generation ~25 s). So "level with Free" at 10^8 is the JVM's GC, not Lean catching up: in work alone
  Lean is ~1.5–2.5x behind here too. `List.range` is gone from the probe (`Nat.fold`): it cost nothing measurable.
- `all` and `first` resume the LAST choice in tail position (`| [x], k => k x`): no frame per choice point when
  there is one choice, so a chain of 10^8 choices runs in 4 MB (before: 11.4 GB, 16 s). okay-simple's `all`/`first`
  got the same fix (a2d9216): 10^8 choices were OutOfMemory on a 12 GB heap, 1.1 s after.
- Performance (2026-10-21, `sample` of `state`): ~45% allocation and freeing of the program's nodes (`op`, `bind`, the
  effect's operation, a closure per step), ~7% `lean_apply_1` (a bind's `f`), ~15% the loop itself. Done: `op`
  (-25..35%); the clause inlined into the loop — `@[specialize]` on BOTH the reference (next to `implemented_by`) and
  the loop, `@[inline]` on the `Split` wrappers (`handle`, `answer`, ...) so the call site in `state` is direct —
  `lean_apply_3` gone, -11..18%; `At` folded into `op`, `Place.taken` (CPS, no `Taken` allocated), `andThen` —
  measured nothing, kept. Left: fewer nodes per operation is all there is; ~90 ns per `state` operation.
- Laws: the monad laws are equalities after normalization, each `rfl` (`pure_bind`, `bind_pure`, `bind_assoc`),
  `norm_norm`; on `run` as they stand (`run_ret`, `run_bind`, `run_delay`). A standard handler's single-operation law is `rfl` (`state_get`...);
  one with binds in it goes through `run` and `simp` (`all_among`).
- Commits: no Co-Authored-By lines.
- THE WIRE (`Okay/Wire/`, 2026-10-22): okay's wire, the protocol of its far sides (okay's specs/remote-foreign.md,
  polyglot-one-wire.md; the reference far side for pure rests is okay's Haskell `okay-py/src/main/resources/okay/hs/
  Okay.hs` — follow it: its requests, conditions' kinds, hello). Own JSON (`Json`, a number its text), `Value` with
  okay's tags (int past 2^53, a whole double `t:f`, nan, dict, frame), `Host` (requests by name; `fail` answers `Empty`:
  Lean refuses `{X} : Host X` beside a constructor of a compound index), `Wire` + `remote` for typed effects, `step`
  (reference + `@[implemented_by]` loop, like `run`), `Worker.serve1` (pure: state in, state out — `Free` is `Type 1`,
  so the worker's state cannot live in an `IO.Ref`; the stdio loop passes it, the C shim keeps it), `foreign` /
  `answering` / `runRemote` / `Link.spawn` for Lean as the host.
- FFM: `scripts/ffm-worker.sh [Module]` — the module's import closure by its `import` lines, Lean's C by `leanc -c
  -fPIC` (with the system's macOS version: leanc's says 99.0), the shim by the system's `cc` (leanc's clang has no
  pthread.h), linked by `cc -shared` against Lean's STATIC archives (leanc -shared links @rpath libLake_shared, which a
  JVM cannot find). Lean 4.35's module initializer is `initialize_<pkg>_<Module>(uint8_t builtin)`, no world; a
  foreign thread must `lean_initialize_thread()` first (the shim does, per thread).
- Conformance: `conformance/TestLeanLinks.scala` into okay's `okay-rust/.jvm/src/test/scala/okay/rust/`, then
  `sbt "okayRustJVM/testOnly okay.rust.TestLean*"` (OKAY_LEAN = this directory). Do not commit it into okay unless
  asked: okay is another repository.
