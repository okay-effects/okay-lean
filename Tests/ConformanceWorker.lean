import Tests.WorkerPrograms

/-! The conformance worker: on stdin/stdout (`lake build lean-worker`), and in-process — the same module linked with
`ffi/okay_exchange.c` into a library (`scripts/ffm-worker.sh`) — its worker exported for the C ABI. -/

open Okay.Wire

@[export okay_lean_worker] def leanWorker (_ : Unit) : Worker := Conformance.worker

def main : IO Unit := Conformance.worker.serve
