/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.BackLinkTarget
public import Strata.Languages.Core.Counterexample.BackLinkExactInsert
public import Strata.Transform.PrecondElim
public import Strata.Languages.Core.ObligationIds
public import Strata.Transform.TerminationCheck
import all Strata.DL.Imperative.Counterexample.Run
import all Strata.DL.Imperative.Counterexample.BackLink
import all Strata.Languages.Core.Counterexample.BackLinkExact
import all Strata.Languages.Core.Counterexample.BackLinkExactInsert
import all Strata.Languages.Core.Counterexample.BackLinkTarget
import Strata.DL.Imperative.Counterexample.Tactics

/-! # Back-links and target rewrites for non-assertion targets

The back-links that carry a loop-VC or point-check target across the exact phases, and
the target rewrites of the phases that generate assertions for such targets.

* `ExactCert.liftChecked`: an exact phase's certificate translates the incoming chain as for an
  assertion target, and the translated claim is kept only when a decision procedure accepts it
  (`loopVCRun` for a loop VC, `pointRun` for a point check), whose acceptance is claim validity
  (`genuineFeasibleT`).  `exactCheckedTargetLink` and `exactTargetBackLink` are the exact
  back-links of a phase at a target.
* `ExactCert.ofUnchangedUnitT`, `ExactCert.idT`: the unchanged-unit and identity certificates at
  `genuineFeasibleT`, whose translated claim is the incoming one.  `exactTransportTargetLink`
  carries a loop-VC or point-check claim through such a certificate without running the walk.
* `insertLoopInvUpstreamTarget`, `precondElimUpstreamTarget`, `termCheckUpstreamTarget`: the
  target rewrites of `insertLoopInvariantAsserts` (an inserted assertion names the loop VC of the
  loop next to it), `precondElim` (an inserted call-site check names a point check) and
  `termCheck` (every target kept).  The loop or check is found in the body of the obligation's
  procedure, whose name is passed up from downstream.

The validity of the back-links is proved in `BackLinkTargetLinksProps`. -/

namespace Core

open Imperative

public section

/-- The fuel a walk-decided claim (a loop VC or a point check) lifted from a claim at fuel
    `f` is decided at: the upstream run reaches the check a few administrative steps after
    the downstream run reaches the inserted assertion, so it is given at least the shared
    replay fuel. -/
@[expose] def walkClaimFuel (f : Nat) : Nat := max f replayFuelGuess

/-! ## Checked translation through an exact certificate -/

namespace ExactCert

variable {T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))}
  {Tgt : Type} {V' V : CexValidity Tgt}

/-- The certificate's maps, at the trivial validity predicate. -/
@[expose] def forget (cert : ExactCert T V' V) :
    ExactCert T (fun (_ : Unit) _ _ => True) (fun _ _ _ => True) where
  backCfg := cert.backCfg
  backOracle := cert.backOracle
  backTarget := id
  backFuel := cert.backFuel
  top_back := cert.top_back
  nontop_back := cert.nontop_back
  wf_back := cert.wf_back
  claim_back := fun _ _ _ _ _ _ _ _ _ _ _ => trivial

/-- Translate an outcome with the certificate's maps, then keep the translated claim, at
    fuel `fuel f` for a translated fuel `f`, only if `check` accepts it there; a rejected
    claim is dropped. -/
@[expose] def liftChecked (cert : ExactCert T V' V) (fuel : Nat → Nat)
    (check : Nat → CexA Expression Command → Bool) (st : List (Stmt Expression Command))
    (o : BackLinkOutcome Expression Command) : BackLinkOutcome Expression Command :=
  let r := cert.liftOutcome st o
  match r.claim with
  | none => r
  | some (c, f) =>
    if check (fuel f) c then ⟨r.slices, some (c, fuel f)⟩
    else match r.slices with
      | [] => .empty
      | s :: rest => ⟨s :: rest, none⟩

end ExactCert

/-- The checked back-link of an exact certificate. -/
@[expose] def checkedExactBackLink {T : List (Stmt Expression Command) → Option (List (Stmt
    Expression Command))}
    {Tgt : Type} {V' V : CexValidity Tgt} (name : String) (cert : ExactCert T V' V)
    (fuel : Nat → Nat) (check : Nat → CexA Expression Command → Bool) :
    BackLink Expression Command Command where
  name := name
  lift := cert.liftChecked fuel check

/-- **The walk-decided back-link of an exact phase**: its certificate's translation
    checked by `check` (at `walkClaimFuel` of the translated fuel), guarded at an empty
    unit; `fallback` (the direct back-link, deciding from the top of the unit) where the
    certificate translates nothing, or where the checked translation keeps no claim and
    the fallback finds one. -/
@[expose] def exactCheckedBackLink {T : List (Stmt Expression Command) → Option (List (Stmt
    Expression Command))}
    {Tgt : Type} {V' V : CexValidity Tgt} (name : String) (cert : ExactCert T V' V)
    (check : Nat → CexA Expression Command → Bool)
    (fallback : BackLink Expression Command Command) : BackLink Expression Command Command :=
  ((checkedExactBackLink name cert walkClaimFuel check).guardEmptyUnit.orElseIfEmpty
    fallback).preferClaim fallback

/-- **The exact back-link of a phase at a target its certificate's claim transport does
    not cover**: a loop VC or a point check by the certificate's checked translation; an
    assertion or a declaration check by the direct back-link (a declaration check's unit
    is its derived unit, which the phase does not change). -/
@[expose] def exactCheckedTargetLink {T : List (Stmt Expression Command) → Option (List (Stmt
    Expression Command))}
    {Tgt : Type} {V' V : CexValidity Tgt} (π : String → Option Procedure) (name : String)
    (cert : ExactCert T V' V) : Target → BackLink Expression Command Command
  | .loopVC id => exactCheckedBackLink name cert (loopVCRun π id) (directLoopVCBackLink π id name)
  | .atPoint id => exactCheckedBackLink name cert (pointRun π id) (directPointBackLink π id name)
  | t => directTargetBackLink π name t

/-- **The exact back-link of a phase at a target**: the replay-free certificate link for an
    assertion (with the direct link where it translates nothing), `exactCheckedTargetLink`
    otherwise. -/
@[expose] def exactTargetBackLink {T : List (Stmt Expression Command) → Option (List (Stmt
    Expression Command))}
    (π : String → Option Procedure) (name : String)
    (cert : ExactCert T (genuineFeasible π) (genuineFeasible π)) :
    Target → BackLink Expression Command Command
  | .assert a =>
    (exactBackLink name cert).guardEmptyUnit.orElseIfEmpty (directAssertionBackLink π a name)
  | t => exactCheckedTargetLink π name cert t

/-! ## Translation without re-checking, through a certificate over targets -/

/-- The unchanged-unit certificate (`ExactCert.ofUnchangedUnit`) at claim validity over
    targets (`genuineFeasibleT π` on both sides, one procedure table): a slice start is kept as
    it is when this is consistent with the input unit, so a translated claim is the incoming
    claim itself, at the same fuel, oracle and target. -/
@[expose] def ExactCert.ofUnchangedUnitT (π : String → Option Procedure)
    (T : List Statement → Option (List Statement)) :
    ExactCert T (genuineFeasibleT π) (genuineFeasibleT π) where
  backCfg := unchangedBackCfg
  backOracle := fun _ _ o => o
  backTarget := id
  backFuel := fun _ => id
  top_back := (ExactCert.ofUnchangedUnit (π' := π) (π := π)
    (isReplaySimulation_of_sub fun _ _ h => h) T).top_back
  nontop_back := (ExactCert.ofUnchangedUnit (π' := π) (π := π)
    (isReplaySimulation_of_sub fun _ _ h => h) T).nontop_back
  wf_back := (ExactCert.ofUnchangedUnit (π' := π) (π := π)
    (isReplaySimulation_of_sub fun _ _ h => h) T).wf_back
  claim_back := fun _ _ _ _ _ _ _ _ _ hg hc => by
    obtain ⟨rfl, -⟩ := unchangedBackCfg_eq_some hc
    exact hg

/-- The identity certificate at claim validity over targets (`genuineFeasibleT π` on both
    sides, one procedure table), for a phase that leaves every unit unchanged: all four maps
    are identities, so a translated claim is the incoming claim itself. -/
@[expose] def ExactCert.idT (π : String → Option Procedure) :
    ExactCert (fun st => some st) (genuineFeasibleT π) (genuineFeasibleT π) where
  backCfg := fun _ _ c => some c
  backOracle := fun _ _ o => o
  backTarget := id
  backFuel := fun _ => id
  top_back := fun _ _ hT _ _ htop hc _ => by cases hT; cases hc; exact htop
  nontop_back := fun _ _ hT _ _ htop hc _ => by cases hT; cases hc; exact htop
  wf_back := fun _ _ _ _ _ _ hw hc => by cases hc; exact hw
  claim_back := fun _ _ _ _ _ _ _ _ hw hg hc => by cases hc; exact hg

/-- **The translating back-link of an exact phase at a loop VC or a point check**: the
    certificate's translation over targets (`certT`), whose claim transport needs no decision
    procedure, guarded at an empty unit; `fallback` (the direct back-link, deciding from the
    top of the unit) where the certificate translates nothing, or where the translation keeps
    no claim and the fallback finds one. -/
@[expose] def exactTransportBackLink {T : List (Stmt Expression Command) → Option (List (Stmt
    Expression Command))} (π : String → Option Procedure) (name : String)
    (certT : ExactCert T (genuineFeasibleT π) (genuineFeasibleT π))
    (fallback : BackLink Expression Command Command) : BackLink Expression Command Command :=
  ((exactBackLink name certT).guardEmptyUnit.orElseIfEmpty fallback).preferClaim fallback

/-- **The exact back-link of a phase at a target, with replay-free claims at every target its
    certificates cover**: the certificate link of `cert` for an assertion (with the direct link
    where it translates nothing), the translation of `certT` for a loop VC or a point check
    (`exactTransportBackLink`, with the direct link of the target as fallback), and the direct
    link for a declaration check (its unit is its derived unit, which the phase does not
    change). -/
@[expose] def exactTransportTargetLink {T : List (Stmt Expression Command) → Option (List (Stmt
    Expression Command))}
    (π : String → Option Procedure) (name : String)
    (cert : ExactCert T (genuineFeasible π) (genuineFeasible π))
    (certT : ExactCert T (genuineFeasibleT π) (genuineFeasibleT π)) :
    Target → BackLink Expression Command Command
  | .assert a =>
    (exactBackLink name cert).guardEmptyUnit.orElseIfEmpty (directAssertionBackLink π a name)
  | .loopVC id => exactTransportBackLink π name certT (directLoopVCBackLink π id name)
  | .atPoint id => exactTransportBackLink π name certT (directPointBackLink π id name)
  | t => directTargetBackLink π name t

/-! ## `insertLoopInvariantAsserts`: from an inserted assertion to its loop VC -/

/-- The label of an `assert` command. -/
@[expose] def assertLabel? : Statement → Option String
  | .cmd (.cmd (.assert l _ _)) => some l
  | _ => none

/-- The label of an `assert` or `assume` command. -/
@[expose] def checkLabel? : Statement → Option String
  | .cmd (.cmd (.assert l _ _)) | .cmd (.cmd (.assume l _ _)) => some l
  | _ => none

/-- The id (label and metadata) of an `assert` command. -/
@[expose] def assertId? : Statement → Option (AssertId Expression)
  | .cmd (.cmd (.assert l _ md)) => some { label := l, md := md }
  | _ => none

/-- Is `s` a check the phase inserted: an `assert` or `assume` with a label the phase reserves,
    which, for an `assert`, is not an obligation of the phase's input (`isInput`, by id)? -/
@[expose] def insertedCheck (isInput : AssertId Expression → Bool) (s : Statement) : Bool :=
  (checkLabel? s).any loopInvExt && !(assertId? s).any isInput

/-- The entry-invariant assertions directly before a loop, in order: the asserts with the
    entry prefix in the maximal run of inserted checks (`insertedCheck isInput`) ending just
    before the loop (`pre` is the statement list before the loop). -/
@[expose] def entryAssertsBefore (isInput : AssertId Expression → Bool) (pre : List Statement) :
    List String :=
  ((pre.reverse.takeWhile (insertedCheck isInput)).reverse.filterMap assertLabel?).filter
    (·.startsWith loopInvEntryPrefix)

/-- The loop VC an inserted assertion `label` in a bare loop's body checks, if any. -/
@[expose] def bodyLoopVC (label : String) (md : MetaData Expression) (body : List Statement) :
    Option LoopVCId :=
  let asserts := body.filterMap assertLabel?
  if asserts.contains label then
    if label.startsWith loopInvMeasureLbPrefix then some ⟨md, .measureLowerBound⟩
    else if label.startsWith loopInvMeasureDecPrefix then some ⟨md, .measureDecrease⟩
    else ((asserts.filter (·.startsWith loopInvMaintainPrefix)).idxOf? label).map
      fun i => ⟨md, .maintainInvariant i⟩
  else none

mutual
/-- The loop VC the inserted assertion `label` checks, found in a statement list (`pre`:
    the statements of the list before the current one; `isInput`: is an id an obligation of
    the phase's input). -/
@[expose] def loopVCInStmts (isInput : AssertId Expression → Bool) (label : String)
    (pre : List Statement) : List Statement → Option LoopVCId
  | [] => none
  | s :: rest => (loopVCInStmt isInput label pre s).orElse fun _ =>
    loopVCInStmts isInput label (pre ++ [s]) rest

/-- The loop VC the inserted assertion `label` checks, found at or inside one statement
    (`pre`: the statements before it in its list). -/
@[expose] def loopVCInStmt (isInput : AssertId Expression → Bool) (label : String)
    (pre : List Statement) : Statement → Option LoopVCId
  | .loop _ _ _ body md =>
    ((entryAssertsBefore isInput pre).idxOf? label |>.map fun i => ⟨md, .entryInvariant i⟩).orElse
      fun _ => (bodyLoopVC label md body).orElse fun _ => loopVCInStmts isInput label [] body
  | .block _ b _ => loopVCInStmts isInput label [] b
  | .ite _ t e _ =>
    (loopVCInStmts isInput label [] t).orElse fun _ => loopVCInStmts isInput label [] e
  | _ => none
end

/-- **The target rewrite of `insertLoopInvariantAsserts`**: an assertion the phase
    inserted in the procedure `n` (the obligation's procedure, passed up from downstream)
    for a loop VC names, upstream, that loop VC (found in `n`'s body in the phase's output
    `output`, among the checks that are not obligations of its input `input`); every other
    target is unchanged. -/
@[expose] def insertLoopInvUpstreamTarget (input output : Program) :
    Target → Option String → Target
  | .assert a, some n =>
    if loopInvExt a.label then
      let obls := ObligationIds.programObls input
      match (output.decls.findSome? (Decl.bodyNamed n)).bind
          (loopVCInStmts (fun i => obls.any (ObligationIds.sameId i)) a.label []) with
      | some id => .loopVC id
      | none => .assert a
    else .assert a
  | t, _ => t

/-! ## `precondElim` and `termCheck`: from an inserted check to its point

`precondElim` inserts, before each statement, the preconditions of the partial functions
its expressions call (a *point check* of that statement).  An assertion it inserted in a
procedure names, upstream, the point check of the statement it precedes (the first
following statement that is not an inserted check; at the end of a loop body, where the
guard and measure are re-checked, the loop).  The well-formedness checks of contracts and
functions, and the termination checks of `termCheck`, are lemmas, not assertions of a
procedure, so no target rewrite maps to them. -/

/-- The expression of an `assert` command. -/
@[expose] def assertExpr? : Statement → Option Expression.Expr
  | .cmd (.cmd (.assert _ e _)) => some e
  | _ => none

/-- The metadata of the statement the inserted assertion `label` checks, and the assertion's
    expression, in a statement list (`loopMd?`: the enclosing loop's metadata, the point of a
    check at the end of its body). -/
@[expose] def pointInStmts (label : String) (loopMd? : Option (MetaData Expression)) :
    List Statement → Option (MetaData Expression × Expression.Expr)
  | [] => none
  | s :: rest =>
    if assertLabel? s = some label then
      (assertExpr? s).bind fun e =>
        (match rest.find? fun s' => !((assertLabel? s').any precondElimExt) with
         | some s' => some s'.getMetaData
         | none => loopMd?).map (·, e)
    else (pointInStmt label s).orElse fun _ => pointInStmts label loopMd? rest
where
  /-- The point and expression of the check `label` inside one statement. -/
  pointInStmt (label : String) : Statement → Option (MetaData Expression × Expression.Expr)
    | .block _ b _ => pointInStmts label none b
    | .ite _ t e _ => (pointInStmts label none t).orElse fun _ => pointInStmts label none e
    | .loop _ _ _ body md => pointInStmts label (some md) body
    | _ => none

/-- **The target rewrite of `precondElim`**: a check the phase inserted in the procedure `n`
    (the obligation's procedure, passed up from downstream) names, upstream, the point check
    of the statement it precedes in `n`'s body in the phase's output; every other target is
    unchanged. -/
@[expose] def precondElimUpstreamTarget (output : Program) : Target → Option String → Target
  | .assert a, some n =>
    if precondElimExt a.label then
      match (output.decls.findSome? (Decl.bodyNamed n)).bind (pointInStmts a.label none) with
      | some (md, e) => .atPoint { stmtMd := md, expr := e }
      | none => .assert a
    else .assert a
  | t, _ => t

/-- **The target rewrite of `termCheck`**: the phase adds functions, axioms and lemmas
    but no assertion, so every target is unchanged. -/
@[expose] def termCheckUpstreamTarget (_input _output : Program) :
    Target → Option String → Target := fun target _ => target

end -- public section

end Core
