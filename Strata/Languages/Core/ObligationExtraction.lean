/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.EvalContext
public import Strata.DL.Imperative.Counterexample.Run
public import Strata.DL.Imperative.Counterexample.BackLink
import all Strata.DL.Imperative.EvalContext
public import Strata.Languages.Core.Program
/-! # Proof Obligation Extraction

A Core-to-obligations pass that walks a post-PE program and extracts
proof obligations with their path conditions reconstructed from the program
structure.

The input is a body satisfying `Statements.hasObligationForm`, the pipeline fact
`ProgramFact.hasObligationForm`: only `assume` (path conditions), `assert` and
`cover` (proof obligations), and `init` (from CSE or global initialization),
nested under `if *` to any depth.

This pass reconstructs path conditions by tracking `assume` statements
encountered on the path to each `assert`/`cover`.

The linked extraction (`extractGoLinked`, `extractLinkedObligations`) takes its obligations
from `extractGo` and `extractDecl` and computes only the back-links itself. Its properties are
in `ObligationExtractionProps.lean`.
-/

public section

namespace Core.ObligationExtraction

open Lambda Imperative

/-- Oracle-relevant event on the path from a passive unit entry to one
    extracted assertion. -/
inductive ExtractReplayEvent where
  | branch (takeThen : Bool)
  | nondetWrite (name : CoreIdent) (expectedType : Option Lambda.LTy)
  deriving Repr, BEq, DecidableEq

/-- Thin, reified (b)→(a) link emitted adjacent to a proof obligation.
    It stores no source locator: the entry statements are the replay focus and
    `events` is exactly the nondeterministic path to the target (assert or cover).
    `targetLabel` is the obligation's label; the kind (assert vs cover) is carried
    by the obligation's `property`, not by the link. -/
structure ExtractBackLink where
  entryStatements : Statements
  targetLabel : String
  events : List ExtractReplayEvent

/-- Every obligation — assert *and* cover — carries a reconstruction link. -/
abbrev LinkedObligation := ProofObligation Expression × ExtractBackLink

mutual
/-- Core recursive worker for `extractFromStatements`. Walks the statement list,
    accumulating path conditions in a `RevPathConditions` (newest scope stored
    most-recent-first for O(1) growth) and collecting proof obligations. Each
    captured obligation restores natural order via `RevPathConditions.consume`. -/
def extractGo (pc : RevPathConditions Expression) : Statements →
    Array (ProofObligation Expression) →
    Except String (Array (ProofObligation Expression))
  | [], acc => .ok acc
  | s :: rest, acc =>
    match s with
    | .cmd (.cmd (.assert label e md)) =>
      let propType := convertMetaDataPropertyType md
      extractGo pc rest (acc.push (ProofObligation.mk label propType pc.consume e md))

    | .cmd (.cmd (.cover label e md)) =>
      extractGo pc rest (acc.push (ProofObligation.mk label .cover pc.consume e md))

    | .cmd (.cmd (.assume label e _md)) =>
      extractGo (pc.prepend (.assumption label e)) rest acc

    | .ite .nondet thenSs elseSs _md => do
      let thenObs ← extractFromStatements pc thenSs
      let elseObs ← extractFromStatements pc elseSs
      extractGo pc rest (acc ++ thenObs ++ elseObs)

    | .cmd (.cmd (.init name ty e _md)) =>
      extractGo (pc.prepend (.varDecl name ty e)) rest acc

    | _other =>
      .error s!"ObligationExtraction: unsupported statement"

/-- Extract proof obligations from a procedure body, reconstructing path
    conditions from the program structure.

    `pathConditions` accumulates the current path conditions (from `assume`
    statements and `var` definitions) as we walk the statement tree.

    Returns the extracted obligations. -/
def extractFromStatements
    (pathConditions : RevPathConditions Expression)
    (ss : Statements) : Except String (Array (ProofObligation Expression)) :=
  extractGo pathConditions ss #[]
end

/-- Give every parameter of `proc` whose name is in `taken` a fresh name in its body.

    A body's parameters reach the obligations as free variables under their own
    names. One named like a function or constant would be read as that function,
    constrained by its axioms, so a check on the parameter could hold for the
    constant's value instead. Each clashing parameter is renamed to `x@n`, the first
    such name that no function, constant, parameter, variable of the body or
    earlier fresh name has.

    This matters only for a program whose procedures still carry their parameters, as
    in a pipeline that runs `simplify` in place of symbolic evaluation. The obligation
    program symbolic evaluation builds has procedures without parameters, its former
    parameters renamed apart already, so there the rename does nothing. -/
def renameShadowingParams (taken : List String) (proc : Procedure) (ss : Statements) :
    Statements :=
  let params := proc.header.inputs ++ proc.header.outputs
  let used := taken ++ params.map (·.1.name) ++ Statements.varNames ss
  let fresh (used : List String) (x : String) : String :=
    let rec go (n : Nat) (fuel : Nat) : String :=
      match fuel with
      | 0 => s!"{x}@{n}"
      | fuel + 1 =>
        let c := s!"{x}@{n}"
        if used.contains c then go (n + 1) fuel else c
    go 1 (used.length + 1)
  (params.foldl (init := (ss, used)) fun (ss, used) (x, ty) =>
    if taken.contains x.name then
      let name := fresh used x.name
      let x' : Expression.Ident := ⟨name, x.metadata⟩
      (Block.renameLhs (Block.substFvar ss x (.fvar valueLoc x' (some ty))) x x', name :: used)
    else (ss, used)).1

mutual
/-- Deterministic completion path through a statement, used when an assertion is after a
    nondeterministic join: choose else at each nested branch and retain all choices needed
    to reach the continuation. -/
def completionEventsForStatement : Statement → List ExtractReplayEvent
  | .cmd (.cmd (.init name ty .nondet _)) => [.nondetWrite name (some ty)]
  | .ite .nondet _ elseBody _ =>
    .branch false :: completionEventsForStatements elseBody
  | .block _ body _ => completionEventsForStatements body
  | _ => []

/-- Deterministic completion path through a statement list: the completion paths of its
    statements in order (`completionEventsForStatement`). -/
def completionEventsForStatements : Statements → List ExtractReplayEvent
  | [] => []
  | statement :: rest =>
    completionEventsForStatement statement ++ completionEventsForStatements rest
end

/-- The back-link events of the obligations `extractGo` emits from `ss`, one per obligation
    and in the same order. `events` is the path of oracle-relevant events up to `ss`: an
    `assert` or `cover` gets the path itself, a nondeterministic `init` extends it with its
    write, a nondeterministic `if` extends it with the branch taken inside each branch and with
    the else-branch completion path after the join. -/
def linkEventsGo (events : List ExtractReplayEvent) : Statements → Array (List ExtractReplayEvent)
  | [] => #[]
  | s :: rest =>
    match s with
    | .cmd (.cmd (.assert ..)) | .cmd (.cmd (.cover ..)) => #[events] ++ linkEventsGo events rest
    | .ite .nondet thenSs elseSs _ =>
      linkEventsGo (events ++ [.branch true]) thenSs ++
        linkEventsGo (events ++ [.branch false]) elseSs ++
        linkEventsGo (events ++ [.branch false] ++ completionEventsForStatements elseSs) rest
    | .cmd (.cmd (.init name ty value _)) =>
      let events := match value with
        | .det _ => events
        | .nondet => events ++ [.nondetWrite name (some ty)]
      linkEventsGo events rest
    | _ => linkEventsGo events rest

/-- Pair each obligation of `obs` with its back-link: entry statements `entry`, the
    obligation's label as target, and the entry of `events` at the obligation's index (empty
    past the end of `events`). -/
def attachLinks (entry : Statements) (obs : Array (ProofObligation Expression))
    (events : Array (List ExtractReplayEvent)) : Array LinkedObligation :=
  obs.mapIdx fun i ob =>
    (ob, { entryStatements := entry, targetLabel := ob.label, events := events.getD i [] })

/-- `extractGo` that also emits, with each obligation, its reconstruction link: the
    obligations are those of `extractGo pc ss`, appended to `acc`; `entry` is the unit's
    statements and `events` the oracle-relevant events on the path to `ss`. -/
def extractGoLinked (entry : Statements) (pc : RevPathConditions Expression)
    (events : List ExtractReplayEvent) (ss : Statements) (acc : Array LinkedObligation) :
    Except String (Array LinkedObligation) :=
  (extractGo pc ss #[]).map fun obs => acc ++ attachLinks entry obs (linkEventsGo events ss)

/-- Extract obligations and their reconstruction links. -/
def extractLinkedFromStatements (pathConditions : RevPathConditions Expression)
    (statements : Statements) : Except String (Array LinkedObligation) :=
  extractGoLinked statements pathConditions [] statements #[]

/-- The statements a procedure's obligations are read from: its structured body, with the
    parameters named like a function in `funcNames` renamed apart. A procedure that still
    carries a contract is refused, since only the body is read: an `ensures` would be left
    unchecked and a `requires` missing from the path condition. So is a CFG body, which
    cannot be walked: returning no obligations would report success on a procedure whose
    assertions were never checked. -/
def procedureStatements (funcNames : List String) (proc : Procedure) :
    Except String Statements := do
  if !(proc.spec.preconditions.isEmpty && proc.spec.postconditions.isEmpty) then
    throw ("ObligationExtraction: procedure '" ++ toString proc.header.name ++
      "' still carries a requires or ensures clause; obligations can only be " ++
      "extracted from procedures without a contract")
  match proc.body with
  | .structured ss _ => .ok (renameShadowingParams funcNames proc ss)
  | .cfg _ _ =>
    .error ("ObligationExtraction: procedure '" ++ toString proc.header.name ++
      "' has a CFG body; obligations can only be extracted from " ++
      "structured bodies")
  | .abstract => .ok []

/-- One step of `extractObligations`: read the declaration `decl`, given the global
    path-condition facts declared before it (newest first) and the obligations found so far. -/
private def extractDecl (funcNames : List String) :
    PathCondition Expression × Array (ProofObligation Expression) → Decl →
    Except String (PathCondition Expression × Array (ProofObligation Expression))
  | (globalPc, allObs), decl =>
    match decl with
    | .ax a _ =>
      .ok (.assumption a.name a.e :: globalPc, allObs)
    | .distinct name es _ =>
      .ok (.distinct (toString name) es :: globalPc, allObs)
    | .func func _ =>
      -- A surviving function precondition is an obligation nobody generates,
      -- and the encoder emits total `SafeDiv`, `SafeMod` and safe bitvector
      -- operations on the strength of those preconditions having been checked.
      if func.preconditions.isEmpty then .ok (globalPc, allObs)
      else
        .error ("ObligationExtraction: function '" ++ toString func.name ++
          "' still carries a precondition; run precondition elimination before " ++
          "extracting obligations")
    | .recFuncBlock funcs _ =>
      match funcs.find? (fun f => !f.preconditions.isEmpty) with
      | some f =>
        .error ("ObligationExtraction: function '" ++ toString f.name ++
          "' still carries a precondition; run precondition elimination before " ++
          "extracting obligations")
      | none => .ok (globalPc, allObs)
    | .proc proc _md => do
      let ss ← procedureStatements funcNames proc
      -- `globalPC` is accumulated newest-first (via ::) which
      -- is what RevPathConditions expects.
      let obs ← extractFromStatements ⟨[globalPc]⟩ ss
      .ok (globalPc, allObs ++ obs)
    | .lemma l md =>
      -- The verifier never reaches this case: symbolic evaluation turns each
      -- lemma into an obligation over fresh free variables, and the program it
      -- hands here holds none. A lemma passed in directly keeps its `forall`s,
      -- since this pass tracks no names to make fresh variables from; the
      -- obligation is equivalent, but a failure shows no counterexample.
      let ob := ProofObligation.mk (toString l.name) (convertMetaDataPropertyType md)
        (RevPathConditions.consume (P := Expression) ⟨[globalPc]⟩) l.e md
      .ok (globalPc, allObs.push ob)
    | _ => .ok (globalPc, allObs)

/-- Extract proof obligations from a program. Axioms become global assumptions
    and `distinct` declarations become distinctness facts. -/
def extractObligations (p : Program) : Except String (ProofObligations Expression) := do
  -- Accumulate global path-condition facts (axioms and distinct groups) and
  -- obligations as we walk declarations in order.
  let (_, allObs) ← p.decls.foldlM (extractDecl p.funcNames)
    (([] : PathCondition Expression), (#[] : Array (ProofObligation Expression)))
  return allObs

/-- One step of `extractLinkedObligations`: `extractDecl` on the declaration `decl`, the
    obligations it adds paired with their back-links into the procedure body they come from.
    A lemma is refused: symbolic evaluation turns each lemma into an obligation, so a lemma
    reaching this pass was never checked, and its obligation would carry no back-link. -/
def extractLinkedDecl (funcNames : List String) :
    PathCondition Expression × Array LinkedObligation → Decl →
    Except String (PathCondition Expression × Array LinkedObligation)
  | _, .lemma l _ => .error ("ObligationExtraction: lemma '" ++ toString l.name ++
      "' reached linked obligation extraction; lemmas must be turned into \
      obligations before extraction")
  | (globalPc, allObs), decl => do
    let (globalPc', obs) ← extractDecl funcNames (globalPc, #[]) decl
    let entry ← match decl with
      | .proc proc _ => procedureStatements funcNames proc
      | _ => pure []
    pure (globalPc', allObs ++ attachLinks entry obs (linkEventsGo [] entry))

/-- Program-level extraction retaining one adjacent link for every assertion and cover. -/
def extractLinkedObligations (p : Program) : Except String (Array LinkedObligation) := do
  let (_, allObs) ← p.decls.foldlM (extractLinkedDecl p.funcNames)
    (([] : PathCondition Expression), (#[] : Array LinkedObligation))
  return allObs

end Core.ObligationExtraction

end -- public section
