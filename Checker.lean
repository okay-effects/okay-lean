import Okay.Check

/-! `okay-check FILE…`: each of okay-proof's certificates checked a second time — one JSON line a file:
`{"file": …, "ok": true, "theory": …, "digest": …, "steps": n, "conclusion": …, "hypotheses": n}` or
`{"file": …, "ok": false, "why": …}`; the exit code 0 if every one checks, 1 if one does not. -/

open Okay.Check Okay.Wire

def main (files : List String) : IO UInt32 := do
  let mut allOk := true
  for f in files do
    let text ← IO.FS.readFile f
    let result := Certificate.check text
    if result matches .error _ then allOk := false
    let line : Json := match result with
      | .ok r => .obj [("file", .str f), ("ok", .bool true), ("theory", .str r.theory), ("digest", .str r.digest),
          ("steps", .num (toString r.steps)), ("conclusion", Codec.formula r.thm.concl),
          ("hypotheses", .num (toString r.thm.hyps.length))]
      | .error why => .obj [("file", .str f), ("ok", .bool false), ("why", .str why)]
    IO.println line.render
  return if allOk then 0 else 1
