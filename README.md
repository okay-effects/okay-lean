# okay-lean

okay-simple's `Free` monad in Lean 4: algebraic effects and handlers, a program DATA — a value, or an operation with
its rest `k` — its effects a ROW in its type, a handler a function of a program to a program, taking its effect from
anywhere in the row by a TYPED PLACE: no cast, no `Typeable`, dependent pattern matching tells a handler an operation
is its own. And, Lean being Lean, the laws are theorems: the monad laws after normalization by `rfl`, `run`'s equations, and what
each standard handler makes of its operations.

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
| `E` is in `R` | `[In E R]`: `perform op` an operation of `E` as a program, at `E`'s place in `R` |
| `E` is in `R`, and `R` without it is `Rest` | `[Split E R Rest]`: what a handler takes, finding the first `E` of `R` |
| a deep handler | `handle ret clause p`: the value's clause, an operation's with its rest `k` — resumable any number of times |
| answering in place | `answer ret clause p`: each operation its answer at once — a loop, the stack constant |
| with a state threaded | `answerWith ret clause s0 p`, a loop; `handleWith` the deep form, `k` resumable |
| at an explicit place | `handleAt`, `handleWithAt`, `answerAt`, `answerWithAt` with the `Place` |
| the value | `run p` for `p : A ! Pure` |

The standard effects, `Okay.Effects.Std`: `State` (`get`, `put`, `modify`, `gets`; `state s0`), `Reader` (`ask`;
`reader e`), `Writer` (`tell`; `writer W`), `Error` (`raise`; `attempt E`), `Choose` (`among`, `fail`, `guard`;
`all`, `first`), `Abort` (`abort`; `optional`). Each handler takes its effect from anywhere in the row. The order of
handlers is the semantics: `state 0 (all p)` is one state across the branches, `all (state 0 p)` a state per branch —
`Tests/Main.lean` shows both, and an effect of one's own, `Console`, with its handler.

## The stack

Each interpreter is defined twice: a total reference in continuation-passing style, which the theorems are about,
and the loop that runs it (`@[implemented_by]`), okay-simple's — a left-nested bind re-associated as data, every
step a jump, a deep handler's `k` a trampoline. So 10^8 operations under `state`, a left-nested bind of 10^8 layers,
a chain of 10^8 choice points under `all` all run on an 8 MB stack, in 2.4 to 15 seconds, the sequential shapes in
4 MB of memory (`Probe/Stack.lean`; `Probe/StackProbe.scala` is the same on okay-simple's Free, 3–4x faster on the
JVM but for the left-nested bind, level).

## The laws

`Okay/Effects/Laws.lean`: the monad laws as equalities after normalization, each by `rfl`: `pure_bind`,
`bind_pure`, `bind_assoc`, and `norm_norm`; on `run` as they stand: `run_ret`, `run_bind`, `run_delay`. In `Std`: `state_get`,
`state_put`, `reader_ask`, `writer_tell`, `attempt_raise`, `optional_abort`, `first_fail`, `all_among`. No `sorry`
anywhere; the build is the check.

## The wire: okay, okay-kernel's protocol, other languages

`Okay.Wire` puts Lean's effects on okay's wire — the protocol okay's far sides speak (Python, R, TypeScript, Haskell,
Go, Rust), okay-kernel's `Done` / `Yield(op, k)` across a process or into the JVM's own:

- **A worker** (`Worker`): Lean programs served by name. An operation a program performs with `call` — or a typed
  effect sent with `remote` (`Wire` gives its operations' names and reads their answers) — goes to the host, which runs
  it under its own handlers and continues the rest. The rest is a pure Lean function, so the host may continue it any
  number of times (a `Choice` resumed twice), in this process or in another. A failure is a condition by name.
- **Over pipes**: `def main := worker.serve` — okay's `ForeignWorker.speaking(Seq(binary))`.
- **In the JVM's process, through FFM**: `scripts/ffm-worker.sh` links the worker's module, Lean's runtime and
  `ffi/okay_exchange.c` into one library of okay's C ABI (`okay_exchange`, `okay_free`) — okay's
  `ForeignWorker.inProcess(path)`. The worker is the library's `@[export okay_lean_worker] def worker (_ : Unit)`.
- **Lean as the host** (`foreign`, `answering`, `runRemote`, `Link.spawn`): another's program run as a Lean program,
  its operations answered by Lean's handlers — `all` over a far side's choices continues each far rest twice.

```lean
import Okay
open Okay.Effects Okay.Wire

inductive Shop : Type → Type
  | priceOf (sku : String) : Shop Float
  | discount (amount : Float) : Shop Float

instance : Wire Shop where
  name := fun op => match op with | .priceOf _ => "price_of" | .discount _ => "discount"
  args := fun op => match op with | .priceOf sku => [.str sku] | .discount a => [.double a]
  answer := fun op v => match op with
    | .priceOf _ | .discount _ => match v.toFloat? with | some f => .ok f | none => .error "not a number"

def total : Program
  | [.str sku, qty] => Value.double <$> remote (E := Shop) (R := [Shop, Host]) (do
      let price ← perform (Shop.priceOf sku)
      perform (Shop.discount (price * (qty.toFloat?.getD 0))))
  | _ => failWith "ValueError" "total takes a sku and a quantity"

def main : IO Unit := Worker.serve ⟨[("total", total)]⟩
```

Checked by okay's own conformance body (`WireConformance`: multi-shot across the link, typed callbacks under the
caller's `Reader`, a table call, a held value, a failure by name and the worker living on), over pipes and over FFM:
`conformance/TestLeanLinks.scala`, run from okay's `okay-rust` tests. Not served: direct style and streams (a muxed
worker's, as for Haskell), CBOR and compression (the hello says so, and okay keeps the plain wire). TCP: through okay's
gateway, which puts a stdio worker on the network.

## Build and test

Lean `v4.35.0` pinned in `lean-toolchain` ([elan](https://github.com/leanprover/elan) installs it).

```
lake build   # the library and the proofs
lake build lean-worker      # the conformance worker, on pipes
scripts/ffm-worker.sh       # the same worker as an FFM library: .lake/build/lib/libokay-lean-worker.dylib
lake test    # Tests/Main.lean: the effects' checks and the wire's, Lean as host of itself included
```

## The family

One of the [okay-effects](https://github.com/okay-effects) family; the specification is okay-simple's
`okay.effects.free.Free` and its `Effectful` interface, in Scala. The differences are Lean's: an operation's answer
type is the GADT's index, not an `answer` continuation in the operation; a row is a list, the handled-next effect at
its head, where okay-simple's `R + E` puts it last; the laws are proved, not tested; each interpreter is a total reference in continuation-passing style for the proofs, and
okay-simple's re-associating loop for running (`@[implemented_by]`).

License: Apache 2.0.
