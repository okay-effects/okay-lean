import Okay.Check.Kernel
import Okay.Wire.Json

/-!
# A certificate of okay-proof's, checked a second time

The certificate's JSON (okay-proof's `Certificate.of`): its theory by value (`axioms`) with a DIGEST — FNV-1a, 64 bits,
of the axioms' JSON — its steps in order, each a rule and the earlier steps it uses, the conclusion and hypotheses it
claims. Checked here by re-deriving every step with this kernel: the digest recomputed from the axioms as read here
(so the two codecs are one), the axioms closed and well-sorted, each premise an earlier step, the claim the result.
-/

namespace Okay.Check

open Okay.Wire (Json)

namespace Codec

def sort : Srt → Json
  | .int => .str "Int"
  | .dec => .str "Dec"
  | .str => .str "Str"
  | .named n => .str ("#" ++ n)

def sort? : Json → Except String Srt
  | .str "Int" => .ok .int
  | .str "Dec" => .ok .dec
  | .str "Str" => .ok .str
  | .str n => if n.startsWith "#" then .ok (.named (String.ofList (n.toList.drop 1))) else .error s!"not a sort: {n}"
  | j => .error s!"not a sort: {j.render}"

def var (x : Var) : Json := .arr [.str "v", .str x.name, sort x.sort]

partial def term : Term → Json
  | .v x => var x
  | .i n => .arr [.str "i", .str (toString n)]
  | .d x => .arr [.str "d", .str x.plain]
  | .s x => .arr [.str "s", .str x]
  | .ap fn as => .arr [.str "ap", .str fn.name, .arr (fn.args.map sort), sort fn.result, .arr (as.map term)]

partial def term? : Json → Except String Term
  | .arr [.str "v", .str n, s] => do pure (.v ⟨n, ← sort? s⟩)
  | .arr [.str "i", .str v] => match v.toInt? with
    | some n => .ok (.i n)
    | none => .error s!"not an integer: {v}"
  | .arr [.str "d", .str v] => match Dec.parse? v with
    | some x => .ok (.d x)
    | none => .error s!"not a decimal: {v}"
  | .arr [.str "s", .str v] => .ok (.s v)
  | .arr [.str "ap", .str n, .arr ss, r, .arr as] => do
    pure (.ap ⟨n, ← ss.mapM sort?, ← sort? r⟩ (← as.mapM term?))
  | j => .error s!"not a term: {j.render}"

def var? (j : Json) : Except String Var := do
  match ← term? j with
  | .v x => pure x
  | _ => throw s!"not a variable: {j.render}"

partial def formula : Formula → Json
  | .tt => .arr [.str "true"]
  | .ff => .arr [.str "false"]
  | .eq a b => .arr [.str "=", term a, term b]
  | .lt a b => .arr [.str "<", term a, term b]
  | .le a b => .arr [.str "<=", term a, term b]
  | .p pr as => .arr [.str "p", .str pr.name, .arr (pr.args.map sort), .arr (as.map term)]
  | .not f => .arr [.str "not", formula f]
  | .and a b => .arr [.str "and", formula a, formula b]
  | .or a b => .arr [.str "or", formula a, formula b]
  | .imp a b => .arr [.str "imp", formula a, formula b]
  | .all x f => .arr [.str "all", var x, formula f]
  | .ex x f => .arr [.str "ex", var x, formula f]

partial def formula? : Json → Except String Formula
  | .arr [.str "true"] => .ok .tt
  | .arr [.str "false"] => .ok .ff
  | .arr [.str "=", a, b] => do pure (.eq (← term? a) (← term? b))
  | .arr [.str "<", a, b] => do pure (.lt (← term? a) (← term? b))
  | .arr [.str "<=", a, b] => do pure (.le (← term? a) (← term? b))
  | .arr [.str "p", .str n, .arr ss, .arr as] => do pure (.p ⟨n, ← ss.mapM sort?⟩ (← as.mapM term?))
  | .arr [.str "not", f] => do pure (.not (← formula? f))
  | .arr [.str "and", a, b] => do pure (.and (← formula? a) (← formula? b))
  | .arr [.str "or", a, b] => do pure (.or (← formula? a) (← formula? b))
  | .arr [.str "imp", a, b] => do pure (.imp (← formula? a) (← formula? b))
  | .arr [.str "all", x, f] => do pure (.all (← var? x) (← formula? f))
  | .arr [.str "ex", x, f] => do pure (.ex (← var? x) (← formula? f))
  | j => .error s!"not a formula: {j.render}"

end Codec

namespace Certificate
open Kernel

/-- the axioms as the certificate carries them, by name in code-point order -/
def axiomsJson (th : Theory) : Json :=
  .arr ((th.mergeSort fun a b => decide (a.1 ≤ b.1)).map fun (n, f) => .arr [.str n, Codec.formula f])

/-- FNV-1a, 64 bits, of the axioms' JSON: okay-proof's `Certificate.digest` -/
def digest (th : Theory) : String :=
  let h := (axiomsJson th).render.toUTF8.foldl (fun (h : UInt64) b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037
  let hex := String.ofList ((Nat.toDigits 16 h.toNat))
  String.ofList (List.replicate (16 - hex.length) '0') ++ hex

/-- what a check finds: the theorem, under the theory -/
structure Report where
  theory : String
  digest : String
  steps : Nat
  thm : Thm

private def field (j : Json) (k : String) : Except String Json :=
  match j.get? k with
  | some v => .ok v
  | none => .error s!"no '{k}'"

private def premise (done : Array Thm) : Json → Except String Thm
  | .num t => match t.toNat? with
    | some i => if h : i < done.size then .ok done[i] else .error s!"a premise {i} not proved before"
    | none => .error s!"not a premise: {t}"
  | j => .error s!"not a premise: {j.render}"

private def step (s : Json) (done : Array Thm) : Except String Step := do
  let ofs ← match ← field s "of" with
    | .arr xs => xs.mapM (premise done)
    | _ => throw "'of' not a list"
  let fm (k : String) : Except String Formula := do Codec.formula? (← field s k)
  let tm (k : String) : Except String Term := do Codec.term? (← field s k)
  let vr (k : String) : Except String Var := do Codec.var? (← field s k)
  match ← field s "rule", ofs with
  | .str "Assume", [] => pure (.assume (← fm "f"))
  | .str "Axiom", [] => match ← field s "name" with
    | .str n => pure (.axiom n)
    | _ => throw "an axiom's name not a string"
  | .str "Compute", [] => pure (.compute (← fm "f"))
  | .str "AndI", [a, b] => pure (.andI a b)
  | .str "AndE1", [a] => pure (.andE1 a)
  | .str "AndE2", [a] => pure (.andE2 a)
  | .str "OrI1", [a] => pure (.orI1 a (← fm "right"))
  | .str "OrI2", [a] => pure (.orI2 (← fm "left") a)
  | .str "OrE", [a, b, c] => pure (.orE a b c)
  | .str "ImpI", [a] => pure (.impI (← fm "f") a)
  | .str "ImpE", [a, b] => pure (.impE a b)
  | .str "NotI", [a] => pure (.notI (← fm "f") a)
  | .str "NotE", [a, b] => pure (.notE a b)
  | .str "Classic", [a] => pure (.classic a)
  | .str "FalseE", [a] => pure (.falseE a (← fm "f"))
  | .str "AllI", [a] => pure (.allI (← vr "x") a)
  | .str "AllE", [a] => pure (.allE a (← tm "by"))
  | .str "ExI", [a] => pure (.exI (← vr "x") (← fm "f") (← tm "by") a)
  | .str "ExE", [a, b] => pure (.exE a (← vr "y") b)
  | .str "Refl", [] => pure (.refl (← tm "t"))
  | .str "Subst", [a, b] => pure (.subst a (← vr "x") (← fm "f") b)
  | .str "Induct", [a, b] => pure (.induct (← vr "x") (← fm "f") a b)
  | .str "Norm", [] => pure (.norm (← fm "f"))
  | .str "LinComb", ps => do
    let cs ← match ← field s "by" with
      | .arr cs => cs.mapM fun c => match c with
        | .str v => match Dec.parse? v with
          | some d => pure d
          | none => throw s!"not a coefficient: {v}"
        | _ => throw "a coefficient that is not a string"
      | _ => throw "'by' not a list"
    if cs.length != ps.length || ps.isEmpty then throw "as many coefficients as premises"
    pure (.linComb (ps.zip cs))
  | .str "Antisym", [a, b] => pure (.antisym a b)
  | .str "Tighten", [a] => pure (.tighten a)
  | .str "MulNonneg", [a, b] => pure (.mulNonneg a b)
  | .str "Square", [] => pure (.square (← tm "t"))
  | r, _ => throw s!"not a step: {r.render} of {ofs.length} premises"

private def sameSet (a b : List Formula) : Bool := a.all b.contains && b.all a.contains

/-- the certificate, every step derived again under the theory it carries -/
def check (text : String) : Except String Report := do
  let json ← Json.parse text
  match json.get? "version" with
  | some (.num "1") => pure ()
  | _ => throw "not a certificate of version 1"
  let name ← match ← field json "theory" with
    | .str n => pure n
    | _ => throw "the theory's name not a string"
  let th : Theory ← match ← field json "axioms" with
    | .arr xs => xs.mapM fun x => match x with
      | .arr [.str n, f] => do pure (n, ← Codec.formula? f)
      | _ => throw s!"not an axiom: {x.render}"
    | _ => throw "'axioms' not a list"
  for (n, f) in th do
    if !(Logic.free f).isEmpty then throw s!"axiom {n} is not closed"
    if !Logic.wellSorted f then throw s!"axiom {n} is not well-sorted"
    if th.any fun (m, g) => m == n && g != f then throw s!"axiom {n} given twice, two formulas"
  let d := digest th
  match ← field json "digest" with
  | .str given => if given != d then throw s!"the digest {given} is not the axioms' {d}"
  | _ => throw "the digest not a string"
  let steps ← match ← field json "steps" with
    | .arr xs => pure xs
    | _ => throw "'steps' not a list"
  let mut done : Array Thm := #[]
  for (s, i) in steps.zipIdx do
    let r ← (step s done).mapError (s!"step {i}: " ++ ·)
    let t ← (derive th r).mapError (s!"step {i}: " ++ ·)
    done := done.push t
  let last ← match done.back? with
    | some t => pure t
    | none => throw "an empty proof"
  let claimed ← Codec.formula? (← field json "conclusion")
  if last.concl != claimed then throw s!"the proof proves {(Codec.formula last.concl).render}, not the claimed {(Codec.formula claimed).render}"
  let hyps ← match ← field json "hypotheses" with
    | .arr xs => xs.mapM Codec.formula?
    | _ => throw "'hypotheses' not a list"
  if !sameSet last.hyps hyps then throw "the proof rests on other hypotheses than the claimed"
  pure ⟨name, d, steps.length, last⟩

end Certificate
end Okay.Check
