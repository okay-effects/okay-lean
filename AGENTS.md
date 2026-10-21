# okay-lean — notes for agents

- Lean 4, `v4.35.0` pinned in `lean-toolchain`; no dependencies. `lake build` builds the library and checks the
  proofs; `lake test` runs `Tests/Main.lean` (the `test` executable, lake's test driver). Both must pass before a
  commit; no `sorry` — Lean only warns about it, so grep the build output.
- The specification is okay-simple (`~/work/my/okay-simple`, `core/free/.../Free.scala`, `Places.scala`, `Std.scala`):
  a program is data (`Free.ret`, `Free.impure op k`), the row a `List Effect` with the handled-next effect FIRST
  (okay-simple's `R + E` has it last), places typed (`Place`, `Split` with `Rest` an `outParam`, `In`), handlers
  `handle` / `answer` / `handleWith` / `handleAt`. Port the next pieces the same way: `Delimited` (shift and
  reset), `Sub`/`embed`, `Yield`, `Fresh`, `Random`, `Store` are not here yet.
- Lean's universes: `Free R A : Type 1` (the existential `X` in `impure`), so `At`, `Place` are `Type 1` too; effects
  are `Type → Type`. An effect carrying a program as an answer would need a universe bump — not done.
- Notation `A ! R` is `Free R A`; application binds tighter, so write `(List A) ! R`. A handler of a parameterized
  effect whose parameter the value does not fix takes it explicitly: `writer String`, `attempt String`; a word whose
  parameter the row does not fix needs an ascription: `let name : String ← ask`.
- The stack (measured, `Probe/Stack.lean`, `lake build stack`, then `.lake/build/bin/stack <n> state|reader|left|choose`
  under `ulimit -s 8192`): `answer`/`answerWith` are LOOPS — the rest is resumed by a self tail call of `go`, which
  Lean compiles to `goto _start` — so `state`, `reader`, `writer` run 10^8 operations on 8 MB. A deep handler
  (`handle`, `handleWith`) resumes `k` from inside its clause: a call through a closure, no tail call, so the
  stack grows per resumption; `all` over a chain of 10^6 choice points still passes. NOT solved: a left-nested bind
  (`foldl (· >>= ·)`) is QUADRATIC — `bind` rewraps every `k` once per layer (10^4: 2 s, 2·10^4: 7.6 s, 4·10^4: 31 s).
  okay-simple fixes both with `Bind` and `Delay` nodes re-associated in the interpreter; here that would make the
  monad laws hold only up to interpretation, not `rfl` — the user's decision, not taken yet.
- Laws: every handler of a standard effect gets its equations in `Std.lean`'s `Laws` section, `rfl` where it
  computes, induction where it does not (`all_among`). `Free R` is a `LawfulMonad` (`Laws.lean`).
- Commits: no Co-Authored-By lines.
