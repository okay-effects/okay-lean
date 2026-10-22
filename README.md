# okay-lean

Algebraic effects and handlers in Lean 4: [okay-simple](https://github.com/okay-effects/okay-simple)'s `Free` monad,
ported. A program is DATA — a value, a bind, an operation, an operation with its rest `k`, a program built later — its
effects a ROW in its type, a handler a function of a program to a program that takes its effect from anywhere in the
row by a TYPED PLACE: dependent pattern matching tells a handler an operation is its own, no cast. Lean being Lean, the
laws are theorems; and the programs speak okay's wire, so a Lean program runs under another language's handlers —
okay's, in a child process or in the JVM's own process through FFM — and the other way round.

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
| a deep handler | `handle ret clause p`: the value's clause, an operation's with its rest `k`, resumable any number of times |
| answering in place | `answer ret clause p`: each operation its answer at once |
| with a state threaded | `answerWith ret clause s0 p` in place; `handleWith`, the deep form |
| at an explicit place | `handleAt`, `handleWithAt`, `answerAt`, `answerWithAt`, given the `Place` |
| the value | `run p` for `p : A ! Pure` |

The standard effects, `Okay.Effects.Std`: `State` (`get`, `put`, `modify`, `gets`; `state s0`), `Reader` (`ask`;
`reader e`), `Writer` (`tell`; `writer W`), `Error` (`raise`; `attempt E`), `Choose` (`among`, `fail`, `guard`;
`all`, `first`), `Abort` (`abort`; `optional`). Each handler takes its effect from anywhere in the row. The order of
handlers is the semantics: `state 0 (all p)` is one state across the branches, `all (state 0 p)` a state per branch —
`Tests/Main.lean` shows both, and an effect of one's own, `Console`, with its handler.

## The laws

`Okay/Effects/Laws.lean`: the monad laws as equalities after normalization, each by `rfl` — `pure_bind`,
`bind_pure`, `bind_assoc` — and `norm_norm`; on `run` as they stand: `run_ret`, `run_bind`, `run_delay`. In
`Okay/Effects/Std.lean`, what each standard handler makes of its operations: `state_get`, `state_put`, `reader_ask`,
`writer_tell`, `attempt_raise`, `optional_abort`, `first_fail`, `all_among`. No `sorry` anywhere; the build is the
check.

The theorems are about each interpreter's REFERENCE definition, total. What runs is another definition of it
(below), `unsafe` and not proved equal to the reference: the two are changed together, and the tests run the second.

## Running: the stack and the speed

Each interpreter is defined twice: the reference, structural recursion in continuation-passing style, and the loop
that runs it (`@[implemented_by]`), okay-simple's — a bind of a value stepped, a left-nested bind re-associated as
data, every step a jump in the C Lean emits, a deep handler's `k` a trampoline. So no shape of program grows the stack:
10^8 operations run on an 8 MB stack, the sequential shapes in 4 MB of memory. Against okay-simple on the JVM
(Scala 3, JDK 26; each shape in its own JVM, the median of five runs), seconds at 10^8:

| shape | okay-lean | okay-simple's machine | okay-simple's `Free` |
|---|---|---|---|
| `state` | 8.6 | 1.7 | 1.9 |
| `reader` | 2.4 | 0.8 | 0.9 |
| a bind nested to the left | 13.8 | 8.9 | 13.3 |
| a chain of choices under `all` | 4.1 | 1.5 | 1.3 |

Lean is 3–5x behind: about half its time is allocating and freeing the program's nodes, by reference counts, where
the JVM bumps a pointer. The left-nested bind looks level only because the JVM is busy collecting the 10^8 nodes it
holds at once (its pauses 40–55% of the time, and the collector chosen moves it 2x); in work alone Lean is
1.5–2.5x behind there too. `Probe/Stack.lean` and `Probe/StackProbe.scala` are the measurements (AGENTS.md, how).

## The wire: okay, okay-kernel's protocol, other languages

`Okay.Wire` puts Lean's effects on okay's wire — the protocol okay's far sides speak (Python, R, TypeScript, Haskell,
Go, Rust), okay-kernel's `Done` / `Yield(op, k)` across a process or into the JVM's own:

- **A worker** (`Worker`): Lean programs served by name. An operation a program performs with `call` — or a typed
  effect sent with `remote` (`Wire` gives its operations' names and reads their answers at their types) — goes to the
  host, which runs it under its own handlers and continues the rest. The rest is a pure Lean function, so the host may
  continue it any number of times (a `Choice` resumed twice), in another process or in its own. A program's failure
  (`failWith`) is a condition by name, and the worker lives on. Also served: a `call` (a function, which answers
  without performing), a table call, a value held for the host and released.
- **Over pipes**: `def main := worker.serve` — okay's `ForeignWorker.speaking(Seq(binary))`.
- **In the JVM's process, through FFM**: `scripts/ffm-worker.sh` links the worker's module, Lean's runtime and
  `ffi/okay_exchange.c` into one library of okay's C ABI (`okay_exchange`, `okay_free`) — okay's
  `ForeignWorker.inProcess(path)`, JDK 22 or later. The worker is the library's
  `@[export okay_lean_worker] def worker (_ : Unit) : Worker`.
- **Lean as the host** (`foreign`, `foreignCall`, `answering`, `runRemote`, `Link.spawn`): another side's program run
  as a Lean program, its operations answered by Lean's handlers — `all` over a far side's choices continues each of
  its rests twice.

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
`conformance/TestLeanLinks.scala`, run in okay's `okay-rust` tests. Not served: direct style and streams (a muxed
worker's, as for Haskell's), CBOR and compression (the hello says so, and okay keeps the plain wire). TCP: through
okay's gateway, which puts a stdio worker on the network.

## A second checker of okay-proof's certificates

[okay-proof](https://github.com/okay-effects/okay-proof)'s certificates — a proof as JSON, its theory carried by value
with a digest — are checked here a second time, by a kernel written again in Lean (`Okay.Check`): the same logic,
the same exact decimals (rounded as `java.math.BigDecimal` rounds), the same polynomial forms, each of its 28 rules
checked as okay-proof checks it, every step derived again, the theory's digest recomputed from the axioms as read
here, the claimed conclusion and hypotheses the result.

```
lake build okay-check
.lake/build/bin/okay-check cert.json …     # one JSON line a file: ok, the theory, its digest, the conclusion — or why not
```

Two independent kernels, one in Scala, one in Lean, agree on every certificate okay-proof's differential test makes:
806 of them — its proofs, from transfer decisions to the Omega test's 1016-step refutation, and their mutants —
140 accepted and 666 refused by both. `Tests/certificates` keeps a few for this repository's own tests.

## Build and test

Lean `v4.35.0`, pinned in `lean-toolchain` ([elan](https://github.com/leanprover/elan) installs it). No dependencies.

```
lake build                  # the library and the proofs
lake test                   # Tests/Main.lean: the effects' checks and the wire's, Lean hosting itself included
lake build lean-worker      # the conformance worker, on pipes: .lake/build/bin/lean-worker
scripts/ffm-worker.sh       # the same worker as an FFM library: .lake/build/lib/libokay-lean-worker.dylib (.so)
lake build stack            # the measurements: .lake/build/bin/stack <n> state|reader|left|leftSplit|choose
lake build okay-check       # okay-proof's certificates, checked a second time
```

The FFM library is built with the system's C compiler (`cc`) beside `leanc`; macOS and Linux.

## Not here yet

okay-simple's delimited control (`shift`, `reset`), `embed` and `Sub`, interception (`observe`, `around`), and the
effects `Yield`, `Fresh`, `Random`, `Store`, `Lift`. An effect whose answer is a program needs a universe more:
`Free R A` is in `Type 1`.

## The family

One of the [okay-effects](https://github.com/okay-effects) family ([the family](https://github.com/okay-effects/okay-simple/blob/master/docs/family.md)).
The specification is okay-simple's `okay.effects.free.Free`. The differences are Lean's: an operation's answer type
is its GADT's index, not an `answer` function in the operation; a row is a list with the handled-next effect at its
head, where okay-simple's `R + E` puts it last; the laws are proved, not tested; each interpreter is a total reference
for the proofs and okay-simple's loop for running. It meets the family on okay's wire, as a far side and as a host.

License: Apache 2.0.
