/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Env
public import Strata.Languages.Core.Options
public import Strata.DL.Imperative.SMTUtils
public import Strata.DL.Imperative.PathConditionsFold

/-! # The results the evaluator decides without a solver

Before an obligation reaches the solver, the discharge decides what it can from the obligation
alone (`evaluatorResults`): a goal that is literally `true` or `false`, a goal that is, up to
metadata, one of the assumptions of its own path condition or refuted by them, and a path
condition with a literally `false` assumption or with only definitions. The facts it reads of
the path condition come from an index of its metadata-erased assumptions (`assumptionIndex`)
or, along the discharge's obligations, from a trail advanced along their shared prefixes
(`EvalTrail`, `evaluatorResultsTrail`); `evaluatorResultsWith` decides from those facts.

Key definitions: `Core.SMT.Result`, `PathConditionShape`, `pathConditionShape`,
`usesSatisfiablePathsPremise`, `MetaFreeExpr`, `AssumptionIndex`, `assumptionIndex`,
`goalIsAssumed`, `goalIsRefuted`, `evaluatorResultsWith`, `evaluatorResults`, `EvalCounts`,
`evalCountsFold`, `EvalTrail`, `evaluatorResultsTrail`. -/

namespace Core.SMT

public section

/-- The result of an SMT check on a Core obligation. -/
abbrev Result := Imperative.SMT.Result (Core.Expression.Ident)

end -- public section

end Core.SMT

namespace Core
open Imperative Lambda Strata.SMT

public section

/-- What `evaluatorResults` needs to know about a path condition, read in one pass over it. -/
inductive PathConditionShape where
  /-- Every entry only declares or defines a variable. Such a path condition is satisfiable: each
      entry is sent to the solver as a `declare-fun` or a non-recursive `define-fun`, which some
      model always satisfies.

      The solver also receives axioms that are not entries of the path condition: those of the
      built-in functions the definitions use, such as `mapConst`'s, and those attached to the
      program's own functions (`func.axioms`, and the per-constructor axioms of recursive
      functions). Taking the path condition to be satisfiable therefore assumes that these
      axioms are satisfiable together. If they are not, an assertion the solver would pass
      vacuously is reported failing; no assertion is ever reported passing because of this.
      `Core.factoryInterp_axiomsSatisfied` proves that the axioms of the polymorphic built-ins
      (`Core.Factory`) hold together in one model. Two steps are assumed rather than proved:
      that the specialized copies `MonomorphizeFunctions` makes of these built-ins, whose axioms
      are what the solver receives, inherit that model; and that the axioms of the program's own
      functions are satisfiable.
      The evaluator also decides before encoding, so a definition the encoder cannot encode is
      reported as this failure rather than as an analysis error. -/
  | onlyDefinitions
  /-- Some assumption is literally `false`: the evaluator already knows the path is dead. -/
  | hasFalseAssumption
  /-- Anything else. -/
  | other
  deriving DecidableEq

/-- The shape of `obligation`'s path condition, read in one pass over its entries. -/
def pathConditionShape (obligation : ProofObligation Expression) : PathConditionShape :=
  obligation.assumptions.foldl (init := .onlyDefinitions) fun shape pc =>
    pc.foldl (init := shape) fun shape entry =>
      match shape, entry with
      | .hasFalseAssumption, _ => .hasFalseAssumption
      | _, .assumption _ e => if e.isFalse then .hasFalseAssumption else .other
      | _, .distinct .. => .other
      | shape, .varDecl .. => shape

/-- Whether the premise of `deductiveAssumingSatisfiablePaths`, that every path to an assertion
    can be taken, lets the evaluator decide that `obligation`, whose goal is literally `false`
    and whose path condition has shape `shape`, fails: its path condition, whatever it holds, is
    taken to be satisfiable without asking a solver. Covers are left to the solver, so they are
    reported as in `deductive`, and so is a path condition with a literally false assumption,
    which the evaluator already knows is dead. -/
def usesSatisfiablePathsPremise (obligation : ProofObligation Expression)
    (checkMode : VerificationMode) (shape : PathConditionShape) : Bool :=
  checkMode == .deductiveAssumingSatisfiablePaths && obligation.property.passWhenUnreachable &&
    shape != .hasFalseAssumption

/-! ## Goals an obligation's own assumptions decide

An *assumption index* holds, once per obligation, the assumptions of its path condition with
their metadata erased (`LExpr.eraseMetadata`, which `LExpr.eqModuloMeta` compares), and the
arguments of the assumptions that are negations. Deciding whether the goal is an assumption, or
the negation of one, is then one hash-set lookup instead of a comparison with every assumption. -/

/-- A Core expression with its metadata erased, as a hash-set key: two keys are equal exactly
    when the expressions are equal up to metadata (`LExpr.eqModuloMeta`). -/
structure MetaFreeExpr where
  expr : Lambda.LExpr ⟨⟨Unit, CoreLParams.IDMeta⟩, Lambda.LMonoTy⟩
  deriving DecidableEq

instance : Hashable MetaFreeExpr := ⟨fun k => Lambda.LExpr.hashExpr k.expr⟩

instance : LawfulHashable MetaFreeExpr where
  hash_eq a b h := by cases eq_of_beq h; rfl

/-- The key of `e`: `e` with its metadata erased. -/
@[expose] def MetaFreeExpr.of (e : Expression.Expr) : MetaFreeExpr := ⟨e.eraseMetadata⟩

/-- The argument `x` of a negation `Bool.Not(x)` at `bool → bool`, with metadata erased. -/
@[expose] def negArg? : Lambda.LExpr ⟨⟨Unit, CoreLParams.IDMeta⟩, Lambda.LMonoTy⟩ →
    Option (Lambda.LExpr ⟨⟨Unit, CoreLParams.IDMeta⟩, Lambda.LMonoTy⟩)
  | .app _ (.op _ o (some ty)) x =>
    if o.name == "Bool.Not" && ty == Lambda.LMonoTy.arrow .bool .bool then some x else none
  | _ => none

/-- Whether `p` is, up to metadata, the negation `Bool.Not(q)` of `q`. -/
@[expose] def isNegationOf (p q : Expression.Expr) : Bool :=
  decide (negArg? p.eraseMetadata = some q.eraseMetadata)

/-- The assumptions of a path condition (`pos`) and the arguments of those that are negations
    (`neg`), with metadata erased. -/
structure AssumptionIndex where
  pos : Std.HashSet MetaFreeExpr := {}
  neg : Std.HashSet MetaFreeExpr := {}

/-- Add the assumption `a` to the index. -/
@[expose] def AssumptionIndex.add (idx : AssumptionIndex) (a : Expression.Expr) :
    AssumptionIndex :=
  let k := MetaFreeExpr.of a
  { pos := idx.pos.insert k
    neg := match negArg? k.expr with
      | some x => idx.neg.insert ⟨x⟩
      | none => idx.neg }

/-- Add the assumption of one path-condition entry, if it is one. -/
@[expose] def AssumptionIndex.addEntry (idx : AssumptionIndex) :
    PathConditionEntry Expression → AssumptionIndex
  | .assumption _ a => idx.add a
  | _ => idx

/-- The assumption index of `obligation`'s path condition, built in one pass over its entries. -/
@[expose] def assumptionIndex (obligation : ProofObligation Expression) : AssumptionIndex :=
  obligation.assumptions.foldl (fun idx pc => pc.foldl AssumptionIndex.addEntry idx) {}

/-- Whether the goal of `obligation` is, up to metadata, one of the assumptions of its own path
    condition (in the index `idx` of that path condition): it then holds wherever the path
    condition holds. -/
@[expose] def goalIsAssumed (idx : AssumptionIndex) (obligation : ProofObligation Expression) :
    Bool :=
  idx.pos.contains (MetaFreeExpr.of obligation.obligation)

/-- Whether the goal of `obligation` is, up to metadata, the negation of one of the assumptions
    of its own path condition, or an assumption is the negation of the goal (in the index `idx`
    of that path condition): the goal is then false wherever the path condition holds. -/
@[expose] def goalIsRefuted (idx : AssumptionIndex) (obligation : ProofObligation Expression) :
    Bool :=
  let g := MetaFreeExpr.of obligation.obligation
  idx.neg.contains g || match negArg? g.expr with
    | some x => idx.pos.contains ⟨x⟩
    | none => false

/-- The results the evaluator decides without a solver, for satisfiability and validity, from
    three facts of the obligation's path condition: whether the goal is, up to metadata, one of
    its assumptions (`assumed`), whether the goal is refuted by one (`refuted`: it is the
    negation of an assumption, or an assumption is its negation), and its shape (`shape`).
    `some r` when the obligation alone settles that check, `none` when a solver is needed. A
    check not asked for is `unknown`. -/
def evaluatorResultsWith (assumed refuted : Bool) (shape : PathConditionShape)
    (obligation : ProofObligation Expression) (checkMode : VerificationMode)
    (satisfiabilityCheck validityCheck : Bool) : Option SMT.Result × Option SMT.Result :=
  -- Satisfiability is settled (unsat) if the obligation is literally false, if its path
  -- condition has a literally false assumption, or if it is a cover whose goal is refuted by
  -- its path's assumptions.
  let sat : Option SMT.Result :=
    if !satisfiabilityCheck then some .unknown
    else if obligation.obligation.isFalse then some .unsat
    else if shape == .hasFalseAssumption then some .unsat
    else if obligation.property == .cover && refuted then some .unsat
    else none
  -- Validity is settled if the obligation is literally true or is one of its own path's
  -- assumptions (valid = unsat), or literally false with a path condition known to be
  -- satisfiable (invalid = sat): one that only declares or defines variables, or one that
  -- `usesSatisfiablePathsPremise` takes to be satisfiable.
  let valid : Option SMT.Result :=
    if !validityCheck then some .unknown
    else if obligation.obligation.isTrue then some .unsat
    else if assumed then some .unsat
    else if obligation.obligation.isFalse then
      if shape == .onlyDefinitions || usesSatisfiablePathsPremise obligation checkMode shape then
        some (.sat [])
      else none
    else none
  (sat, valid)

/-- The results the evaluator decides without a solver, for satisfiability and validity
    (`evaluatorResultsWith`), reading the facts of `obligation`'s path condition from its
    assumption index. -/
def evaluatorResults (obligation : ProofObligation Expression) (checkMode : VerificationMode)
    (satisfiabilityCheck validityCheck : Bool) : Option SMT.Result × Option SMT.Result :=
  let idx := assumptionIndex obligation
  evaluatorResultsWith (goalIsAssumed idx obligation) (goalIsRefuted idx obligation)
    (pathConditionShape obligation) obligation checkMode satisfiabilityCheck validityCheck

/-! ## The evaluator's assumption facts, incrementally

`evaluatorResultsWith` reads two facts of an obligation's assumptions: whether its goal is, up to
metadata, one of them, and whether it is refuted by one. Successive obligations share long
prefixes of their entries (taken oldest first), and an obligation extracted from a branch shares
with the previous one only part of a path condition. The discharge therefore keeps, per
metadata-erased key, the number of assumptions with that key (`EvalCounts`), in an undo fold
(`Imperative.PathConditions.UndoFold`) whose undo step decrements the counts: advancing it to an
obligation undoes the entries past the common prefix and processes only the new ones, updating
the counts in place. -/

/-- The keys an entry adds to the assumption index: its metadata-erased assumption and, for a
    negation, the metadata-erased argument (`AssumptionIndex.add`). -/
@[expose] def entryKeys : PathConditionEntry Expression → Option MetaFreeExpr × Option MetaFreeExpr
  | .assumption _ a =>
    let k := MetaFreeExpr.of a
    (some k, (negArg? k.expr).map (⟨·⟩))
  | _ => (none, none)

/-- Count the key `k`, if any, once more. -/
@[expose] def bumpKey (m : Std.HashMap MetaFreeExpr Nat) : Option MetaFreeExpr →
    Std.HashMap MetaFreeExpr Nat
  | none => m
  | some k => m.insert k (m.getD k 0 + 1)

/-- Count the key `k`, if any, once less. -/
@[expose] def unbumpKey (m : Std.HashMap MetaFreeExpr Nat) : Option MetaFreeExpr →
    Std.HashMap MetaFreeExpr Nat
  | none => m
  | some k => m.insert k (m.getD k 0 - 1)

/-- Per metadata-erased key, how many of the processed assumptions have it (`pos`) and how many
    are negations of it (`neg`). -/
structure EvalCounts where
  pos : Std.HashMap MetaFreeExpr Nat := {}
  neg : Std.HashMap MetaFreeExpr Nat := {}

/-- The undo fold of the counts: an entry's keys are counted once more, and once less when the
    entry is undone. -/
@[expose] def evalCountsFold : PathConditions.UndoFold EvalCounts Expression where
  step c e := let ks := entryKeys e; { pos := bumpKey c.pos ks.1, neg := bumpKey c.neg ks.2 }
  undo c e := let ks := entryKeys e; { pos := unbumpKey c.pos ks.1, neg := unbumpKey c.neg ks.2 }

/-- The discharge's trail: the entries processed, oldest first, and their counts. -/
abbrev EvalTrail := PathConditions.UndoFoldState EvalCounts Expression

/-- Whether the goal of `obligation` is, up to metadata, one of the trail's assumptions. -/
@[expose] def EvalTrail.goalAssumed (t : EvalTrail) (obligation : ProofObligation Expression) :
    Bool :=
  t.current.pos.getD (MetaFreeExpr.of obligation.obligation) 0 != 0

/-- Whether the goal of `obligation` is, up to metadata, the negation of one of the trail's
    assumptions, or one of them is the negation of the goal. -/
@[expose] def EvalTrail.goalRefuted (t : EvalTrail) (obligation : ProofObligation Expression) :
    Bool :=
  let g := MetaFreeExpr.of obligation.obligation
  t.current.neg.getD g 0 != 0 || match negArg? g.expr with
    | some x => t.current.pos.getD ⟨x⟩ 0 != 0
    | none => false

/-- `evaluatorResults` from the trail advanced to `obligation`'s entries, oldest first
    (`evaluatorResultsTrail_eq`), and that trail. -/
def evaluatorResultsTrail (t : EvalTrail) (obligation : ProofObligation Expression)
    (checkMode : VerificationMode) (satisfiabilityCheck validityCheck : Bool) :
    (Option SMT.Result × Option SMT.Result) × EvalTrail :=
  let t : EvalTrail := evalCountsFold.advance t obligation.assumptions.reverse.flatten
  (evaluatorResultsWith (t.goalAssumed obligation) (t.goalRefuted obligation)
    (pathConditionShape obligation) obligation checkMode satisfiabilityCheck validityCheck, t)

end -- public section

end Core
