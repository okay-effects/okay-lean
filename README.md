# okay-lean

okay-simple's `Free` monad in Lean 4: algebraic effects and handlers, a program DATA — a value, or an operation with
its rest `k` — its effects a ROW in its type, a handler a function of a program to a program, taking its effect from
anywhere in the row by a TYPED PLACE: no cast, no `Typeable`, dependent pattern matching tells a handler an operation
is its own. And, Lean being Lean, the laws are theorems: the monad laws up to delays, `run`'s equations, and what each standard
handler makes of its operations.

```lean
import Okay
open Okay.Effects Okay.Effects.Free

-- in any row that has these three, at any place
def greet [In (Reader String) R] [In (Writer String) R] [In (State Nat) R] : Nat ! R := do
  let name : String ← ask
  tell s!"hello, {name}"
  let n : Nat ← get
  put (n + name.length)
  pure n

#eval run (writer String (state 10 (reader "Ann" (greet (R := [Reader String, State Nat, Writer String])))))
-- ((10, 13), ["hello, Ann"])
```

`run` exists only for a program of no effect, `A ! []`: an effect not handled is a type error.

## The words

| | |
|---|---|
| an effect | a GADT of its operations indexed by the answer: `inductive State (S : Type) : Type → Type \| get : State S S \| put (s : S) : State S Unit` |
| a row | a list of effects, the one handled next first: `[State Nat, Reader String]`; `Pure` is `[]` |
| a program of the value `A` over the row `R` | `A ! R`, that is `Free R A`. Application binds tighter: `(List A) ! R` |
| `E` is in `R` | `[In E R]`: `perform op` an operation of `E` as a program at `E`'s place |
| `E` is in `R`, and `R` without it is `Rest` | `[Split E R Rest]`: what a handler takes, finding the first `E` of `R` |
| a deep handler | `handle ret clause p`: the value's clause, an operation's with its rest `k` — resumable any number of times |
| answering in place | `answer ret clause p`: each operation its answer at once — a loop, the stack constant |
| with a state threaded | `answerWith ret clause s0 p`, a loop; `handleWith` the deep form, `k` resumable |
| at an explicit place | `handleAt place ret clause p` |
| the value | `run p` for `p : A ! Pure` |

The standard effects, `Okay.Effects.Std`: `State` (`get`, `put`, `modify`, `gets`; `state s0`), `Reader` (`ask`;
`reader e`), `Writer` (`tell`; `writer W`), `Error` (`raise`; `attempt E`), `Choose` (`among`, `fail`, `guard`;
`all`, `first`), `Abort` (`abort`; `optional`). Each handler takes its effect from anywhere in the row. The order of
handlers is the semantics: `state 0 (all p)` is one state across the branches, `all (state 0 p)` a state per branch —
`Tests/Main.lean` shows both, and an effect of one's own, `Console`, with its handler.

## The stack

As okay-simple: a program has `bind` and `delay` nodes; a handler is a loop over it in continuation-passing style,
and every continuation it hands out is a trampoline, giving the rest back delayed for the loop outside to go on with.
So 10^7 operations under `state`, a left-nested bind of 10^7 layers, a chain of 10^7 choice points under `all` all run
on an 8 MB stack, in about a second each (`Probe/Stack.lean`). Nothing is `partial`.

## The laws

`Okay/Effects/Laws.lean`: the monad laws up to steps after normalization — `Eqv`, two programs the same but for
delays: `bind_assoc` by `rfl`, `pure_bind`, `bind_pure`; on `run` as equalities: `run_ret`, `run_bind`, `run_delay`,
and `run_congr`. In `Std`: `state_get`, `state_put`, `reader_ask`, `writer_tell`, `attempt_raise`, `optional_abort`,
`first_fail`, `all_among`. No `sorry` anywhere; the build is the check.

## Build and test

Lean `v4.35.0` pinned in `lean-toolchain` ([elan](https://github.com/leanprover/elan) installs it).

```
lake build   # the library and the proofs
lake test    # Tests/Main.lean: 14 checks
```

## The family

One of the [okay-effects](https://github.com/okay-effects) family; the specification is okay-simple's
`okay.effects.free.Free` and its `Effectful` interface, in Scala. The differences are Lean's: an operation's answer
type is the GADT's index, not an `answer` continuation in the operation; a row is a list, the handled-next effect at
its head, where okay-simple's `R + E` puts it last; the laws are proved, not tested; every interpreter is total, a structural loop in continuation-passing style with
trampolined continuations, where okay-simple's loop re-associates binds as data.

License: Apache 2.0.
