/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.SMTEmitter
meta import Strata.Languages.Core.Verifier

meta section

/-! # Tests for `Core.SMT.Emitter` -/

namespace Core.SMT.EmitterTest
open Core Core.SMT Core.SMT.Emitter Lambda Strata.SMT
open Imperative (PathConditionEntry)

private def boolTy : LMonoTy := .tcons "bool" []

/-- An `.assumption` entry asserting the boolean variable `v`. -/
private def assm (label v : String) : PathConditionEntry Expression :=
  .assumption label (.fvar () v (.some boolTy))

private def mkCaptured (entries : List (PathConditionEntry Expression))
    (declText : String := "") (assertText : String := "") : CapturedFrame :=
  { entries := entries.toArray, declText, assertText,
    estateBefore := .init, dctxBefore := SMT.Context.default,
    ctxCapturedBefore := SMT.Context.default }

private def mkFold (entries : List (PathConditionEntry Expression)) :
    FoldFrame :=
  { entries := entries.toArray,
    baseCheckpoint := { ctx := SMT.Context.default }, output := {} }

private def mkState (frames : List CapturedFrame)
    (discovered : List String := []) : EmitterState :=
  { estate := .init, sstate := .init, headerPreText := "", headerPostText := "",
    dctx := SMT.Context.default, ctxCaptured := SMT.Context.default,
    frames, managedNames := {},
    discoveredNames := discovered.foldl (·.insert ·) ∅,
    basePreDeclared := SMT.Context.default.preDeclaredNames, baseAxmCount := 0 }

/-! ## SMT-LIB text is not sharable by prefix

The same term renders differently under different `EncoderState`s
(uniquify), and a term's `declare-fun` is emitted only on its first
rendering. Text is therefore only sharable under one state lineage, which
is what `EmitterState` maintains. -/

private def renderFrom (estate : Strata.SMT.EncoderState) :
    IO (String × Strata.SMT.EncoderState) := do
  let act : Strata.SMT.EncoderM Unit := do
    let t ← Strata.SMT.Encoder.encodeTerm
      (.app (.uf ⟨"v", [], .bool⟩) [] .bool)
    Solver.assert t
  let (((), estate), text, _) ← Solver.recordToString (act.run estate)
  return (text, estate)

-- Same term, different states: a state that has already used the name `v`
-- renders the term as `v@1`, not `v`.
/--
info: ; v
(declare-const v Bool)
(assert v)
---
; v
(declare-const v@1 Bool)
(assert v@1)
-/
#guard_msgs in
#eval show IO _ from do
  let (fresh, _) ← renderFrom .init
  let (collided, _) ← renderFrom (.initWithNames {("v" : String)})
  IO.print fresh; IO.println "---"; IO.print collided

-- The declaration is emitted only on the term's first rendering: a second
-- rendering from the advanced state is just the assert. Pasted into a fresh
-- file, it would reference an undeclared symbol.
/--
info: (assert v)
-/
#guard_msgs in
#eval show IO _ from do
  let (_, estate) ← renderFrom .init
  let (second, _) ← renderFrom estate
  IO.print second

/-! ## Captured files contain exactly `encodeCore`'s commands -/

/-- Sorted non-empty lines, for order-insensitive file comparison. -/
private def sortedLines (s : String) : List String :=
  (((s.splitOn "\n").filter (· ≠ "")).toArray.qsort (· < ·)).toList

/-- An obligation with goal `true`. `assumptions` is oldest `PathCondition`
    first for readability; `ProofObligation` stores newest first. -/
private def ob (label : String)
    (assumptions : List (List (PathConditionEntry Expression))) :
    Imperative.ProofObligation Expression :=
  { label, property := .assert, assumptions := assumptions.reverse,
    obligation := .boolConst () true, metadata := {} }

/-- Run the fold and emission over `obs` (`true` marks a pruned obligation),
    printing per obligation the frame count after sync, whether a captured
    file was produced, and whether its sorted lines equal `encodeCore`'s
    output for the same obligation. -/
private def runScenario
    (obs : List (Imperative.ProofObligation Expression × Bool)) : IO Unit := do
  let mut encState : SMTEncodeState := .init { ctx := SMT.Context.default }
  let mut es ← EmitterState.init SMT.Context.default (pure ())
  for (ob, pruned) in obs do
    match encodeObligationToSMT Core.Factory encState ob with
    | .error e => IO.println s!"{ob.label}: encode error {e}"
    | .ok (res, encState') =>
      encState := encState'
      let managed : Std.HashSet String :=
        (res.varDefs.map (·.name) ++ res.varDecls.map (·.name)).foldl
          (·.insert ·) ∅
      let (es', cf?) ← es.syncAndEmit Core.Factory encState'.frames
        encState'.current.ctx pruned res.ctx res.goal {} ob.label managed
        (satisfiabilityCheck := false) (validityCheck := true)
      es := es'
      match cf? with
      | none =>
        IO.println s!"{ob.label}: frames={es.frames.length} captured=no"
      | some cf =>
        let pctx ← Strata.Pipeline.PipelineContext.create
          (outputMode := .quiet) (profilePipeline := false)
        let (_, coreText, _) ← Solver.recordToString
          (Strata.SMT.Encoder.encodeCore res.ctx (pure ()) res.assumptions
            res.goal {} (satisfiabilityCheck := false) (validityCheck := true)
            (label := ob.label) (varDefinitions := res.varDefs)
            (varDeclarations := res.varDecls) (pctx := pctx))
        let same := sortedLines (String.join cf.pieces) == sortedLines coreText
        IO.println
          s!"{ob.label}: frames={es.frames.length} captured=yes matchesEncodeCore={same}"

-- The module header's A1–A4 scenario: capture ⟨h0⟩, extend to ⟨h0, h1⟩,
-- push ⟨c⟩, rewind ⟨c⟩ and capture ⟨c2⟩.
/--
info: A1: frames=1 captured=yes matchesEncodeCore=true
A2: frames=1 captured=yes matchesEncodeCore=true
A3: frames=2 captured=yes matchesEncodeCore=true
A4: frames=2 captured=yes matchesEncodeCore=true
-/
#guard_msgs in
#eval runScenario [
  (ob "A1" [[assm "h0" "p"]], false),
  (ob "A2" [[assm "h0" "p", assm "h1" "q"]], false),
  (ob "A3" [[assm "h0" "p", assm "h1" "q"], [assm "c" "r"]], false),
  (ob "A4" [[assm "h0" "p", assm "h1" "q"], [assm "c2" "s"]], false)]

-- Rewind forgets the dropped frame's names: both branch frames mention the
-- same fresh variable `t`; a leaked name would render `t@1` in R2 and break
-- the `encodeCore` comparison.
/--
info: R1: frames=2 captured=yes matchesEncodeCore=true
R2: frames=2 captured=yes matchesEncodeCore=true
-/
#guard_msgs in
#eval runScenario [
  (ob "R1" [[assm "h0" "p"], [assm "c" "t"]], false),
  (ob "R2" [[assm "h0" "p"], [assm "c2" "t"]], false)]

-- Managed variables (declaration and definition) round-trip through capture.
/--
info: B1: frames=1 captured=yes matchesEncodeCore=true
B2: frames=1 captured=yes matchesEncodeCore=true
-/
#guard_msgs in
#eval runScenario [
  (ob "B1" [[.varDecl ⟨"x", ()⟩ (.forAll [] boolTy) .nondet,
             assm "h0" "x"]], false),
  (ob "B2" [[.varDecl ⟨"x", ()⟩ (.forAll [] boolTy) .nondet,
             assm "h0" "x",
             .varDecl ⟨"y", ()⟩ (.forAll [] boolTy)
               (.det (.fvar () "x" (.some boolTy))),
             assm "h1" "y"]], false)]

-- A pruned obligation gets no captured file, but its frames still sync,
-- keeping the next obligation on the fast path.
/--
info: A1: frames=1 captured=yes matchesEncodeCore=true
A2: frames=1 captured=no
A3: frames=2 captured=yes matchesEncodeCore=true
-/
#guard_msgs in
#eval runScenario [
  (ob "A1" [[assm "h0" "p"]], false),
  (ob "A2" [[assm "h0" "p", assm "h1" "q"]], true),
  (ob "A3" [[assm "h0" "p", assm "h1" "q"], [assm "c" "r"]], false)]

-- Managed-name collision: C1 references `v` before any frame declares it
-- (capture declares it on the fly); C2's frame then declares `v` as a
-- `varDecl`. `disabled` is set and the environment's remaining obligations
-- fall back.
/--
info: C1: frames=1 captured=yes matchesEncodeCore=true
C2: frames=2 captured=no
C3: frames=2 captured=no
-/
#guard_msgs in
#eval runScenario [
  (ob "C1" [[assm "h" "v"]], false),
  (ob "C2" [[assm "h" "v"],
            [.varDecl ⟨"v", ()⟩ (.forAll [] boolTy) .nondet]], false),
  (ob "C3" [[assm "h" "v"],
            [.varDecl ⟨"v", ()⟩ (.forAll [] boolTy) .nondet]], false)]

-- Empty first frame (a program with no global axioms): captured, then
-- extended in place.
/--
info: E1: frames=1 captured=yes matchesEncodeCore=true
E2: frames=1 captured=yes matchesEncodeCore=true
-/
#guard_msgs in
#eval runScenario [
  (ob "E1" [[]], false),
  (ob "E2" [[assm "h0" "p"]], false)]

/-! ## Frame alignment -/

/-- info: (Bool.true, Bool.false, Bool.true, Bool.false, Bool.false) -/
#guard_msgs in
#eval
  let a := #[assm "h0" "p", assm "h1" "q"]
  let b := #[assm "h0" "p", assm "h1" "q"]
  let c := #[assm "h0" "p", assm "h1" "q", assm "h2" "r"]
  (entriesEq a b, entriesEq a c,
   entriesProperPrefix a c, entriesProperPrefix a b, entriesProperPrefix c a)

-- Empty-array boundary: `entriesAgreeFrom`'s base case at index 0.
/-- info: (Bool.true, Bool.false, Bool.true) -/
#guard_msgs in
#eval (entriesEq #[] #[], entriesProperPrefix #[] #[],
       entriesProperPrefix #[] #[assm "x" "p"])

-- Full match.
/-- info: (2, Bool.false) -/
#guard_msgs in
#eval alignMirror
  [mkCaptured [assm "a" "p"], mkCaptured [assm "b" "q"]]
  [mkFold [assm "a" "p"], mkFold [assm "b" "q"]] 0

-- The top frame is a proper prefix of its target: extendable in place.
/-- info: (1, Bool.true) -/
#guard_msgs in
#eval alignMirror
  [mkCaptured [assm "a" "p"], mkCaptured [assm "b" "q"]]
  [mkFold [assm "a" "p"], mkFold [assm "b" "q", assm "c" "r"]] 0

-- Divergence: keep the common prefix, not extendable.
/-- info: (1, Bool.false) -/
#guard_msgs in
#eval alignMirror
  [mkCaptured [assm "a" "p"], mkCaptured [assm "b" "q"]]
  [mkFold [assm "a" "p"], mkFold [assm "b'" "q2"]] 0

-- Catch-all arm: empty mirror, and mirror outliving a rewound target.
/-- info: ((0, Bool.false), 1, Bool.false) -/
#guard_msgs in
#eval (alignMirror [] [mkFold [assm "a" "p"]] 0,
       alignMirror [mkCaptured [assm "a" "p"], mkCaptured [assm "b" "q"]]
                   [mkFold [assm "a" "p"]] 0)

/-! ## `deltaItems` selects the delta's items by kind -/

/-- info: (["y"], ["x"], ["h1"], ["d1"]) -/
#guard_msgs in
#eval
  let t : Term := .prim (.bool true)
  let out : SMTEncodedPathCondition :=
    { assumptionsRev := [⟨"h1", .ok (t, {})⟩, ⟨"h0", .ok (t, {})⟩],
      distinctsRev := [⟨"d1", .ok (t, {})⟩, ⟨"d0", .ok (t, {})⟩],
      varDefsRev := [(⟨"y", .bool, t⟩, {}), (⟨"y0", .bool, t⟩, {})],
      varDeclsRev := [⟨"x", .bool⟩, ⟨"x0", .bool⟩] }
  -- The delta: one entry of each kind (the newest of each Rev list).
  let items := deltaItems out
    #[assm "h1" "p", .distinct "d1" [], .varDecl ⟨"y", ()⟩ (.forAll [] boolTy)
        (.det (.boolConst () true)), .varDecl ⟨"x", ()⟩ (.forAll [] boolTy) .nondet]
  (items.varDefs.map (·.1.name), items.varDecls.map (·.name),
   items.assumptions.map (·.1), items.distincts.map (·.1))

/-! ## `declPieces`/`assertPieces` are oldest frame first -/

/-- info: (["d-old", "d-new"], ["a-old", "a-new"]) -/
#guard_msgs in
#eval
  let es := mkState
    [mkCaptured [assm "b" "q"] "d-new" "a-new",
     mkCaptured [assm "a" "p"] "d-old" "a-old"]
  (es.declPieces, es.assertPieces)

/-! ## `usableFor` -/

-- A context sort named like a discovered name is rejected; an unrelated sort
-- is accepted; `disabled` rejects everything; base-pre-declared names pass
-- even when discovered.
/-- info: (Bool.false, Bool.true, Bool.false, Bool.true) -/
#guard_msgs in
#eval
  let ctxT := SMT.Context.default.addSort { name := "T", arity := 0 }
  let esBaseHasT := { mkState [] ["T"] with
    basePreDeclared := SMT.Context.default.preDeclaredNames.insert "T" }
  ((mkState [] ["T"]).usableFor ctxT,
   (mkState [] ["U"]).usableFor ctxT,
   { mkState [] ["U"] with disabled := true }.usableFor ctxT,
   esBaseHasT.usableFor ctxT)

end Core.SMT.EmitterTest
