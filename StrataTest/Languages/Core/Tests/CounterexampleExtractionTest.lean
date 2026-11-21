/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataTest.Languages.Core.Tests.CounterexampleTestUtils
meta import Strata.Languages.Core.InterpreterReplay
meta import Strata.Languages.Core.ObligationExtraction
meta import Strata.Languages.Core.Counterexample.ValuationToRunProducer

/-! # Linked obligation extraction and `(b) → (a)` reconstruction unit tests

Small synthetic Core units exercising the extraction of obligations together with their
back-links (`extractLinkedFromStatements`: target labels, oracle events in execution
order, agreement with plain extraction), the split of a level-`(b)` valuation into an
entry store and an oracle (`valuationToEnv`), and the `(b) → (a)` producer
`reconstructAssertionFromCexValuation` on claimed, unclaimed and replayed counterexamples. -/

meta section

namespace CounterexampleExtractionTest

open Core Lambda Imperative Core.ObligationExtraction
open Core.CexTestUtils

private def id (name : String) : CoreIdent := ⟨name, ()⟩
private def intTy : Lambda.LTy := .forAll [] .int
private def assertFalse (label : String) : Statement :=
  .cmd (.cmd (.assert label Core.false md))
private def coverTrue (label : String) : Statement :=
  .cmd (.cmd (.cover label Core.true md))

/-- The linked obligations extracted from `statements` under an empty path condition. -/
private def linked (statements : Statements) :=
  extractLinkedFromStatements (⟨[[]]⟩ : RevPathConditions Expression) statements

/-- The target label of a linked obligation's back-link. -/
private def linkLabel : LinkedObligation → String
  | (_, link) => link.targetLabel

-- Every obligation, assertion or cover, carries exactly one adjacent link naming its own target.
#guard match linked [assertFalse "a", coverTrue "c"] with
  | .ok results => match results.toList with
    | [assertion, cover] => linkLabel assertion == "a" && linkLabel cover == "c"
    | _ => false
  | .error _ => false

-- Deterministic initialization is replayed and does not enter the oracle.
private def detInit : Statement :=
  .cmd (.cmd (.init (id "x") intTy (.det (int 1)) md))
#guard match linked [detInit, assertFalse "a"] with
  | .ok results => match results.toList with
    | [(_, link)] => link.events.isEmpty
    | _ => false
  | .error _ => false

-- Nondeterministic writes and branch trails are retained in execution order.
private def nondetInit (name : String) : Statement :=
  .cmd (.cmd (.init (id name) intTy .nondet md))
private def branched : Statements :=
  [nondetInit "x",
   .ite .nondet [nondetInit "t", assertFalse "then"]
                [nondetInit "e", assertFalse "else"] md]

#guard match linked branched with
  | .ok results =>
    match results.toList with
    | [(_, thenLink), (_, elseLink)] =>
      thenLink.events == [.nondetWrite (id "x") (some intTy), .branch true,
                          .nondetWrite (id "t") (some intTy)] &&
      elseLink.events == [.nondetWrite (id "x") (some intTy), .branch false,
                          .nondetWrite (id "e") (some intTy)]
    | _ => false
  | .error _ => false

-- Assertions after a nondeterministic join retain a deterministic completion
-- path through the preceding branch, preventing oracle desynchronization.
private def postJoin : Statements :=
  [.ite .nondet [] [nondetInit "joined"] md, assertFalse "after"]
#guard match linked postJoin with
  | .ok results => match results.toList with
    | [(_, link)] => link.events ==
        [.branch false, .nondetWrite (id "joined") (some intTy)]
    | _ => false
  | .error _ => false

/-- Whether linked extraction yields the same obligations as plain extraction on
    `statements` (both succeeding). -/
private def preservesForwardExtraction (statements : Statements) : Bool :=
  let pc := (⟨[[]]⟩ : RevPathConditions Expression)
  match extractFromStatements pc statements, extractLinkedFromStatements pc statements with
  | .ok original, .ok linked => original == linked.map Prod.fst
  | _, _ => false

#guard preservesForwardExtraction branched
#guard preservesForwardExtraction postJoin

/-- The validation failure reason of a result, `none` on success. -/
private def reason? : Except ValidationReason α → Option ValidationReason
  | .error reason => some reason
  | .ok _ => none

private def modelLink : ExtractBackLink := {
  entryStatements := branched
  targetLabel := "then"
  events := [.nondetWrite (id "x") (some intTy), .branch true,
             .nondetWrite (id "t") (some intTy)] }

private def obligation : ProofObligation Expression := {
  label := "then"
  property := .assert
  assumptions := []
  obligation := Core.false
  metadata := md }

private def unit : PassiveUnit := {
  inputs := [(id "input", .int)]
  statements := branched }

-- The (b)→(a) split reads from a level-(b) valuation: only true entry inputs are
-- prebound (init targets stay undefined), and oracle values interleave with branches.
private def valn : RStore Expression := fun name =>
  if name == id "input" then some (int 4)
  else if name == id "x" then some (int 5)
  else if name == id "t" then some (int 6)
  else none
#guard match valuationToEnv Core.Factory unit obligation modelLink valn with
  | .ok (env, oracle) =>
    env.store.get (id "input") == some (int 4) &&
    env.store.get (id "x") == none && env.store.get (id "t") == none &&
    oracle == [int 5, Core.true, int 6]
  | .error _ => false

-- A wrong-typed nondet value is rejected as ill-typed.
#guard reason? (valuationToEnv Core.Factory unit obligation modelLink
  (fun name => if name == id "t" then some Core.true else valn name)) == some .illTypedValue

-- End-to-end extraction replay executes deterministic initialization before the
-- failing assertion instead of prebinding its target.
private def detStatements : Statements := [detInit, assertFalse "det"]
private def detLink : ExtractBackLink := {
  entryStatements := detStatements
  targetLabel := "det"
  events := [] }
private def detObligation : ProofObligation Expression :=
  { obligation with label := "det" }
private def detUnit : PassiveUnit := { inputs := [], statements := detStatements }

/-- The runtime `Fail` verdict: a lone claim, no unconfirmed slices. -/
private def isProvedTop (o : BackLinkOutcome Expression Command) : Bool := o.isFail

/-- The `(b) → (a)` producer, at an empty valuation.  `fuel := some 0` makes the
    level-`(b)` claim *present*, so a shape-passing unit still mints a lone claim and an
    ill-shaped one still falls through to replay. -/
private def reconstructAt (unit : PassiveUnit) (obl : ProofObligation Expression)
    (link : ExtractBackLink) : BackLinkOutcome Expression Command :=
  reconstructAssertionFromCexValuation Core.Factory unit obl link (fun _ => none) 10000
    { valuation := fun _ => none, fuel := some 0 }

#guard isProvedTop (reconstructAt detUnit detObligation detLink)
#guard summary (reconstructAt detUnit detObligation detLink) ==
  ([], some (some detStatements, 9, []))

-- **Non-vacuity of the `(b)→(a)` contract's `cex.fuel = none` case.**  A `CexValuation` with
-- `fuel := none` makes no level-`(b)` claim (`CexValuationValid` is `True` there), so the
-- producer may not take the no-replay claim shortcut: it runs the level-`(a)`
-- replay at the default fuel instead.  On this shape-passing, genuinely failing
-- obligation the replay succeeds, so the branch really reaches a lone claim (not
-- merely the trivially valid unconfirmed slice); the claim records exactly the fuel
-- replayed at (`10000`), and replaying the claimed slice at that fuel is genuine.
private def noFuelCexValuation : Core.CexValuation := { valuation := fun _ => none, fuel := none }
#guard match reconstructAssertionFromCexValuation Core.Factory detUnit detObligation detLink
    (fun _ => none) 10000 noFuelCexValuation with
  | ⟨[], some (cex, f)⟩ =>
    (match cex.cfg with
      | .stmts ss _ => ss == detStatements
      | _ => false) && f == 10000 &&
      (match replayWithM cex
          { label := detObligation.label, md := detObligation.metadata }
          f (fun _ => none) with
        | .genuine => true
        | _ => false)
  | _ => false

-- Reconstruction handles assertions only: covers have no reconstruction entry point.

-- Reconstruction seeks the linked assertion and clears an earlier assertion
-- failure, so the produced top-level CEX (the whole passive unit) validates and
-- is attributed to the target (not the earlier assertion).
private def focusedLabel : IConfig Expression Command → Option String
  | .stmt (.cmd (.cmd (.assert label _ _))) _ => some label
  | .seq inner _ | .block _ _ inner => focusedLabel inner
  | _ => none
private def twoAssertStatements : Statements :=
  [assertFalse "earlier", assertFalse "target"]
private def targetLink : ExtractBackLink := {
  entryStatements := twoAssertStatements
  targetLabel := "target"
  events := [] }
private def targetObligation : ProofObligation Expression :=
  { obligation with label := "target" }
private def targetUnit : PassiveUnit := { inputs := [], statements := twoAssertStatements }
#guard summary (reconstructAt targetUnit targetObligation targetLink) ==
  ([], some (some twoAssertStatements, 10000, []))

#guard match linked [coverTrue "only-cover"] with
  | .ok results => match results.toList with
    | [cover] => linkLabel cover == "only-cover"
    | _ => false
  | .error _ => false

private def passingTargetStatements : Statements :=
  [.cmd (.cmd (.assert "pass" Core.true md)), assertFalse "later"]
private def passingTargetLink : ExtractBackLink := {
  entryStatements := passingTargetStatements
  targetLabel := "pass"
  events := [] }

private def passingTargetObligation : ProofObligation Expression :=
  { obligation with label := "pass" }
private def passingTargetUnit : PassiveUnit := {
  inputs := [], statements := passingTargetStatements }
-- A passing target does not reach a failure, so the producer carries an
-- unconfirmed top-level slice (no claim), not a claimed one.
#guard summary (reconstructAt passingTargetUnit passingTargetObligation passingTargetLink) ==
  ([some passingTargetStatements], none)

private def postJoinLink : ExtractBackLink := {
  entryStatements := postJoin
  targetLabel := "after"
  events := [.branch false, .nondetWrite (id "joined") (some intTy)] }
private def postJoinObligation : ProofObligation Expression :=
  { obligation with label := "after" }
private def postJoinUnit : PassiveUnit := { inputs := [], statements := postJoin }
#guard isProvedTop (reconstructAssertionFromCexValuation Core.Factory postJoinUnit
  postJoinObligation postJoinLink (fun _ => none) 10000
  { valuation := fun name => if name == id "joined" then some (int 8) else none, fuel := some 0 })
#guard summary (reconstructAssertionFromCexValuation Core.Factory postJoinUnit postJoinObligation
  postJoinLink (fun _ => none) 10000
  { valuation := fun name => if name == id "joined" then some (int 8) else none, fuel := some 0 })
  == ([], some (some postJoin, 10000, [Core.false, int 8]))

end CounterexampleExtractionTest

end -- meta section
