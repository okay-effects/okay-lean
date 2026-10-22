# okay-lean — notes for agents

## Working here

- Lean 4, `v4.35.0` pinned in `lean-toolchain`; no dependencies; elan in `~/.elan` (not on PATH by default:
  `export PATH=$HOME/.elan/bin:$PATH`). `lake build` builds the library and checks the proofs; `lake test` runs
  `Tests/Main.lean` (lake's test driver: the effects' checks and the wire's). Both must pass before a commit; no
  `sorry` — Lean only warns about it, so grep the build output. README's Lean blocks are compiled by hand
  (`LEAN_PATH=.lake/build/lib/lean lean block.lean`): keep them compiling.
- Commits: no Co-Authored-By lines. Public at github.com/okay-effects/okay-lean, `master`, its remote over HTTPS
  (this machine has no SSH key for GitHub). Listed in okay-simple's `docs/family.md`.
- The specification is okay-simple (`~/work/my/okay-simple`: `core/free/.../Free.scala`, `Places.scala`, `Std.scala`).
  Not ported yet: delimited control, `Sub`/`embed`, interception, `Yield`, `Fresh`, `Random`, `Store`, `Lift` — port
  them the same way.

## The design

- A program is data: `Free.ret`, `Free.bind`, `Free.op pl o` (an operation alone, what `perform` makes, okay-simple's
  `Perform`), `Free.impure pl o k`, `Free.delay`. An operation carries its `Place` in the row and the effect's
  operation; a handler meets it with `Place.taken` (okay-simple's `Taken.Mine`/`Theirs`, in CPS, nothing allocated).
  The row is a `List Effect` with the handled-next effect FIRST (okay-simple's `R + E` has it last); `Split` with
  `Rest` an `outParam`, `In`; handlers `handle` / `answer` / `handleWith` / `answerWith`, each at a place too (`…At`).
- Universes: `Free R A : Type 1` (an operation's effect is existential), so `Place` and every program are `Type 1`;
  effects are `Type → Type`. Consequences: an effect answering a program needs a universe more (not done); a value of
  `Type 1` cannot live in an `IO.Ref` (the wire's worker passes its state along instead).
- Notation `A ! R` is `Free R A`; application binds tighter, so `(List A) ! R`. A handler of a parameterized effect
  whose parameter the value does not fix takes it explicitly (`writer String`, `attempt String`); a word whose
  parameter the row does not fix needs an ascription (`let name : String ← ask`).
- TWO DEFINITIONS OF EACH INTERPRETER (`run`, `handleAt`, `handleWithAt`, `answerAt`, `answerWithAt`, the wire's
  `step`): the reference, total structural recursion in CPS (`go m k`) — what every theorem is about — and the one
  that RUNS, `@[implemented_by]`, `unsafe`: okay-simple's loop, a bind of a value stepped, a left-nested bind
  re-associated as DATA, every step a self tail call (`goto _start` in C). It cannot be structural (the re-associated
  term is no subterm), hence `unsafe`, as Lean's own fast paths. Binds are not delayed; a deep handler's `k` is a
  trampoline, `delay fun _ => loop …`, forced by the loop outside. Change the reference and the loop TOGETHER; the
  loop is unproved against the reference. `@[specialize]` on both (beside `implemented_by`: `@[implemented_by f,
  specialize]`) and `@[inline]` on the `Split` wrappers put the clause inline into the loop.
- Laws: the monad laws are equalities after normalization, each `rfl` (`pure_bind`, `bind_pure`, `bind_assoc`),
  `norm_norm`; on `run` as they stand (`run_ret`, `run_bind`, `run_delay`). A standard handler's single-operation law
  is `rfl` (`state_get` …); one with binds in it goes through `run` and `simp` (`all_among`).
- `all` and `first` resume the LAST choice in tail position (`| [x], k => k x`): no frame kept per choice point when
  there is one choice, so a chain of 10^8 choices runs in 4 MB (before: 11.4 GB). okay-simple got the same (a2d9216).

## The wire (`Okay/Wire/`)

- okay's wire, the protocol of its far sides: okay's `specs/remote-foreign.md`, `specs/polyglot-one-wire.md`; the
  reference far side for pure rests is okay's Haskell worker, `okay-py/src/main/resources/okay/hs/Okay.hs` — follow it
  (requests, conditions' kinds, the hello). The wire's version is 9 (`shimVersion`).
- Own JSON (`Json`, a number its text); `Value` with okay's tags (an int past 2^53, a whole double `t:f`, nan, dict,
  frame); `Host` (requests by name; `fail` answers `Empty` — Lean refuses `fail {X} : Host X` beside a constructor of
  a compound index such as `Except …`); `Wire` + `remote` for typed effects; `step` and `runIO`; `Worker.serve1`
  (pure: state in, state out), `Worker.serve` (stdio); `foreign` / `foreignCall` / `answering` / `runRemote` /
  `Link.spawn` for Lean as the host.
- FFM: `scripts/ffm-worker.sh [Module]` — the module's import closure by its `import` lines; Lean's C by `leanc -c
  -fPIC` with the system's macOS version (leanc's own says 99.0); the shim `ffi/okay_exchange.c` by the system's `cc`
  (leanc's clang has no `pthread.h`); linked by `cc -shared` against Lean's STATIC archives (`leanc -shared` links
  `@rpath/libLake_shared.dylib`, which a JVM cannot find). Lean 4.35's module initializer is
  `initialize_<package>_<Module>(uint8_t builtin)`, no world argument; a foreign thread calls
  `lean_initialize_thread()` before Lean code (the shim does, once per thread); calls are one at a time (a mutex).
- Conformance, okay's ONE body over every link (`WireConformance`), tagged `Live` and so excluded by okay's default
  test options — include the tag:

      okay-lean$ lake build lean-worker && scripts/ffm-worker.sh
      okay$ cp ../okay-lean/conformance/TestLeanLinks.scala okay-rust/.jvm/src/test/scala/okay/rust/
      okay$ sbt "set every Test / testOptions := Seq(Tests.Argument(TestFrameworks.MUnit, \"--include-tags=Live\"))" \
                "okayRustJVM/testOnly okay.rust.TestLean*"
      okay$ rm okay-rust/.jvm/src/test/scala/okay/rust/TestLeanLinks.scala

  12 pass on each link (pipes, FFM); direct style, mux and streams are skipped, as for Haskell. Do not commit the test
  into okay unless asked: okay is another repository.

## Measuring

- `lake build stack`, then `.lake/build/bin/stack <n> state|reader|left|leftSplit|choose` under `ulimit -s 8192`;
  `Probe/StackProbe.scala` is the same on okay-simple (`<machine|free> <n> <shape>`): drop it into okay-simple's
  `bench/src/main/scala-3/okay/effects/bench/`, export the bench's classpath, and run EACH PAIR IN ITS OWN JVM (in one
  sbt JVM the shapes pollute each other's JIT profile: Free looked 2x slower), 5 rounds, the median of rounds 2–5;
  remove it after. Lean's runs vary under 2%, the JVM's up to 30%.
- 2026-10-22, n = 10^8, seconds:

  | shape | Lean | Scala machine | Scala Free |
  |---|---|---|---|
  | `state` | 8.62 | 1.70 | 1.93 |
  | `reader` | 2.36 | 0.79 | 0.85 |
  | left-nested bind | 13.84 | 8.9 | 13.3 |
  | chain of choices under `all` | 4.07 | 1.45 | 1.29 |

- Where Lean's time goes (`sample` of `state`): ~45% allocating and freeing the program's nodes (`op`, `bind`, the
  effect's operation, a closure per step), ~7% `lean_apply_1` (a bind's `f`), ~15% the loop; ~90 ns a `state`
  operation. Done: `op` (−25..35%), the clause inlined into the loop (−11..18%); measured nothing, kept: `Place.taken`,
  `andThen`, `At` folded into `op`. What is left is fewer nodes per operation.
- The left-nested bind (`leftSplit`: build and run timed apart): the program, 10^8 binds, lives whole while it runs
  (~7.5 GB). Lean: build ~8 ns, run ~127 ns a layer at any size — work, no memory effect. The JVM at 10^8 is GC-bound
  (pauses 39% of the time on the machine, 56% on Free, with G1; ParallelGC moves Free from ~11.5 s to ~14.5 s, with an
  8 GB young generation to ~25 s): "level with Free" there is the JVM's collector, not Lean catching up.

## Lean's pitfalls met here

- `at` and `show` are keywords; `String.mk` is deprecated (`String.ofList`); `List.lookup key list` reads as
  `list.lookup key`.
- Modules under `Tests/` imported by an executable need a `lean_lib` (`Tests`, `globs = ["Tests.+"]`).
- `partial def` needs `Inhabited` of its result: `instance [Inhabited A] : Inhabited (A ! R)` is in `Okay.Wire.Client`.
- BSD `sed` has no `\b`: rename with Python.
