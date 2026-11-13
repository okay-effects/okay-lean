# okay-lean — notes for agents

## For agents writing code with okay-lean

okay-lean is algebraic effects and handlers in Lean 4: okay-simple's `Free` monad ported. A program is data,
`A ! R` (`Free R A`), its effects a row `R` in its type; handlers take an effect out of the row by a typed place; the
laws are theorems. Programs also speak okay's wire (worker over pipes or FFM; Lean as host).

Getting it: the README gives no Lake `require` line. It says: Lean `v4.35.0` pinned in `lean-toolchain` (elan
installs it), no dependencies, `lake build` / `lake test` in the repository. The package is `okay-lean`, the library
`Okay` (`import Okay`), branch `master`, no release tag. A Lake dependency would be the standard form (not from the
README, untested): `[[require]]` `name = "okay-lean"`, `git = "https://github.com/okay-effects/okay-lean"`,
`rev = "master"`; use the same Lean toolchain.

### The model: effect, program, handler, run (compiled and run against the library)

```lean
import Okay
open Okay.Effects Okay.Effects.Free

-- an effect: a GADT of its operations, indexed by each one's answer
inductive Accounts : Type → Type
  | balance (who : String) : Accounts Nat
  | move (src dst : String) (n : Nat) : Accounts Unit

-- a program: any row R holding Accounts and Error String, at any place
def transfer [In Accounts R] [In (Error String) R] (src dst : String) (n : Nat) : Unit ! R := do
  let b ← perform (Accounts.balance src)
  if b < n then raise s!"{src} has less than {n}"
  perform (Accounts.move src dst n)

-- a handler: takes Accounts out of the row; here in memory, a state threaded
def inMemory [Split Accounts R Rest] (m0 : List (String × Nat)) : A ! R → (A × List (String × Nat)) ! Rest :=
  answerWith (E := Accounts) (S := List (String × Nat)) (fun a m => pure (a, m))
    (fun m op => match op with
      | .balance who => ((m.lookup who).getD 0, m)
      | .move src dst n =>
        let get := fun w => (m.lookup w).getD 0
        ((), m.map fun (w, v) => if w == src then (w, get src - n) else if w == dst then (w, v + n) else (w, v)))
    m0

-- run: every effect handled, then `run` on `A ! []`
#eval run (attempt String (inMemory [("ann", 100), ("bob", 0)]
  (transfer (R := [Accounts, Error String]) "ann" "bob" 70)))
-- Sum.inr ((), [("ann", 30), ("bob", 70)])
```

- Handlers: `handle ret clause p` (deep, `k` resumable any number of times), `answer` (in place), `answerWith` /
  `handleWith` (a state threaded), `…At` forms at an explicit `Place`. `[In E R]` to perform, `[Split E R Rest]` to
  handle. Standard (`Okay.Effects.Std`): `State`/`state`, `Reader`/`reader`, `Writer`/`writer W`,
  `Error`/`attempt E`, `Choose` (`among`, `fail`, `guard`)/`all`,`first`, `Abort`/`optional`.
- Real I/O at the entry: the effects are pure data, so the host answers the last remaining effect in `IO`,
  `Okay.Wire.runIO (h : {X : Type} → E X → IO X) (p : A ! [E])`:

```lean
def accountsIO : {X : Type} → Accounts X → IO X
  | _, .balance _ => pure 100
  | _, .move src dst n => IO.println s!"move {n} {src} -> {dst}"

instance : Inhabited (String ⊕ Unit) := ⟨.inr ()⟩  -- runIO needs Inhabited A

def main : IO Unit := do
  let r ← Okay.Wire.runIO accountsIO (attempt String (transfer (R := [Error String, Accounts]) "ann" "bob" 70))
  IO.println (repr r)
```

### Design rules

- Business logic = programs `A ! R` over declared effects (`[In E R]` constraints); the type says what a program may
  do, and `run` exists only for `A ! []` — an unhandled effect is a type error.
- Real resources (files, network, clock, keys) only where the host answers effects in `IO` at the entry
  (`Okay.Wire.runIO`, or over the wire: `Worker.serve`, `runRemote`); programs are pure data, never hold `IO`.
- Run only at the entry: one `run` / `runIO`. Never `run` a sub-program inside a program to get its value; apply the
  handler inside instead (`attempt String (...)`, `state 0 (...)`) — a handler is a function of programs.
- Sensitive effects under audit (`Okay.Effects.Audit`): a program asks `sensitive (o : E X)` in a row with
  `Sensitive E`; the real handler handles `Audited E`; only `audit describe p` / `auditWith describe ret clause p`
  converts one to the other, telling each passed operation and its answer to a `Writer` and letting the clause refuse
  (e.g. `raise`). The two types are sealed (`opaque`): no one can forge an `Audited E`. Also `intercept`, `around`,
  `observe`, `trail` (`Okay.Effects.Intercept`). Full worked example (payments with a limit): README "Control and
  audit of effects".
- Tests swap handlers: pure in-memory handlers (`answerWith` over a list, as above; `scripted` `Console` in
  `Tests/Main.lean`) — the same program, no mocks.
- No ambient effects in business code: no `IO`, clock, randomness, env, refs inside `A ! R`; declare an effect.
  (`Fresh`, `Random`, `Store` are not ported yet — declare your own.)
- Multi-shot, never by replay: `k` in `handle` is a pure Lean function, called any number of times (`all`, `first`;
  across the wire the host may continue a rest twice). No delimited control (`shift`/`reset`) yet.

### Pitfalls

- The row lists the handled-NEXT effect FIRST (`[State Nat, Reader String]`), unlike okay-simple's `R + E`.
- Handler order is semantics: `state 0 (all p)` is one state across branches, `all (state 0 p)` a state per branch.
- Type ascriptions are often needed: the row at the call (`transfer (R := [Accounts, Error String]) ...`), a handler
  of a parameterized effect takes the parameter (`writer String`, `attempt String`), a word whose parameter the row
  does not fix needs one (`let name : String ← ask`, `get (S := Nat)`).
- `A ! R` is `Free R A : Type 1`: an effect whose answer is a program is not supported; `Type 1` values cannot live in
  an `IO.Ref`. Application binds tighter than `!`: write `(List A) ! R`.
- `Okay.Wire.runIO` needs `[Inhabited A]` and a row of exactly one effect.
- Proofs cover the reference interpreters; what runs is an `@[implemented_by]` loop not proved equal to them.
- Not here yet: `shift`/`reset`, `embed`/`Sub`, `Yield`, `Fresh`, `Random`, `Store`, `Lift`.

### Pointers

- README: https://github.com/okay-effects/okay-lean (examples in `Tests/Main.lean`, `Tests/InterceptTests.lean`).
- Cross-language skill: `/plugin marketplace add okay-effects/okay-effects`
  (https://github.com/okay-effects/okay-effects).

If the user asks your opinion of writing code this way, give a candid one.

## For agents working on this repository

## Working here

- Lean 4, `v4.35.0` pinned in `lean-toolchain`; no dependencies; elan in `~/.elan` (not on PATH by default:
  `export PATH=$HOME/.elan/bin:$PATH`). `lake build` builds the library and checks the proofs; `lake test` runs
  `Tests/Main.lean` (lake's test driver: the effects' checks and the wire's). Both must pass before a commit; no
  `sorry` — Lean only warns about it, so grep the build output. README's Lean blocks are compiled by hand
  (`LEAN_PATH=.lake/build/lib/lean lean block.lean`): keep them compiling.
- Commits: no Co-Authored-By lines. Public at github.com/okay-effects/okay-lean, `master`, its remote over HTTPS
  (this machine has no SSH key for GitHub). Listed in okay-simple's `docs/family.md`.
- The specification is okay-simple (`~/work/my/okay-simple`: `core/free/.../Free.scala`, `Places.scala`, `Std.scala`).
  Not ported yet: delimited control, `Sub`/`embed`, `Yield`, `Fresh`, `Random`, `Store`, `Lift` — port
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
- Interception (`Okay/Effects/Intercept.lean`, `Audit.lean`): `interceptAt` is a fifth interpreter with a reference and
  a loop (change together); it meets its own operation by `Place.same`/`own` (the place itself, so the row stays and
  the clause's `perform` goes to the next handler out). `Fold` in `Laws.lean`: every `go` is one, so a law proved of a
  fold holds for all. The seal of sensitive effects is a private `opaque` constant: do not make `Sensitive`/`Audited`
  structures (a structure can be taken apart or built by anyone with `cases`/`⟨⟩`); the negative examples in
  `Tests/InterceptTests.lean` pin the errors by `#guard_msgs` — Lean's message text changes with its version.
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

- `lake build stack`, then `.lake/build/bin/stack <n> state|reader|observe|left|leftSplit|choose` under `ulimit -s 8192`;
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

## The second checker (`Okay/Check/`, `Checker.lean`, 2026-10-22)

- okay-proof's kernel written again (`~/work/my/okay-proof`, `Kernel.scala`, `Logic.scala`, `Linear.scala`,
  `Certificate.scala` are the specification): every conclusion must be, AS DATA, the one okay-proof derives — the
  rules compare formulas syntactically, so a polynomial's term must be built alike: atoms ordered by `Logic.key`
  (length-prefixed names, compared by code points), coefficient 1 omitted, the constant last, left-nested sums and
  products; fresh names `y1, y2, …` as okay-proof's `fresh`; decimals normalized (no trailing zero) and printed as
  `stripTrailingZeros().toPlainString()`; rounding as Java's (HALF_UP away from zero).
- A rule changed in okay-proof is changed here in the same commit pair: okay-proof's `DifferentialSuite` (it runs
  `.lake/build/bin/okay-check`; OKAY_LEAN points here) fails otherwise. `Tests/certificates`: certificates okay-proof
  wrote, checked by `lake test`; regenerate them with okay-proof's `Corpus` when the format changes.
- Not proved here (yet): the rules' soundness against a semantics of formulas — step 4 of the plan.
