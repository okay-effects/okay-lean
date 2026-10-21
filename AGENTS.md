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
- AGAINST okay-simple's Free (Scala 3, JVM, `Probe/StackProbe.scala`, the same four shapes; JVM's second round,
  warmed; okay-simple at a2d9216, after `all`'s fix): n = 10^7 — `state` Lean 0.87 s / Scala 0.26 s, `reader`
  0.23 / 0.06, left-nested bind 1.5 / 1.28, chain of choices under `all` 0.4 / 0.11. n = 10^8 — `state` 8.7 / 2.96,
  `reader` 2.4 / 0.67, left 15.0 / 11.4, choices 4.1 / 1.1. So 3–4x behind on every shape but the left-nested bind
  (level): allocation — mimalloc + reference counts against a bump allocator — and the JIT. Memory: Lean 4 MB on the
  sequential shapes at any n (nodes freed as the loop goes), the left-nested bind holds its 10^8 nodes (7.4 GB).
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
