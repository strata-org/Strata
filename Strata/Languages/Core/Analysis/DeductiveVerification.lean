/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Analysis.ProcedureCorrectness
public import Strata.DL.Imperative.Analysis.DeductiveVerification
public import Strata.DL.Imperative.Analysis.Definitions
public import Strata.DL.Imperative.Logic.ProgramEntries
public import Strata.Languages.Core.CallGraph
public import Strata.Transform.FilterProcedures
public import Strata.Languages.Core.Logic.TraceInterpUsingDenote
public import Strata.Languages.Core.IncrementalSolve
public import Strata.Languages.Core.InstExprTyping
public import Strata.DL.Imperative.BigStep.Sem

/-! # Deductive verification of Core programs

Instantiates the language-generic deductive verification for Core:
`coreEntries` gives the entries of a Core program, entry procedures with values
for their variables, each starting a run of Core's statement or CFG semantics.
Conditions are read under their own runtime factory
(`Imperative.BigStep.evalInterp`): a condition holds when it evaluates to `true`
in the model its runtime factory carries. An entry's runtime factory is over the
factory visible before its procedure (`ProcEntryEnv`), which differs between
entry procedures, so no single factory fits every entry; on each entry this
reading agrees with `DenoteBasedInterp` over that entry's factory. Deductive
verification is asked of every entry environment, so of every model.
`DeductiveVerificationOnCore` reads the results of Core's verifier as per-assertion verdicts (`vcResultsVerdict`) and says they
are deductive verification of the program the user wrote, for every entry
point's body, structured or CFG.

On top of it, `CoreVerifyIsDeductive` states that `Core.verify` is a deductive
verifier for every valid configuration, one whose pipeline phases each
preserve deductive verification. A phase that overapproximates the runs of
every entry point (`PhaseOverapproximates`) is one of them; `runPhases` and
`pipelineVerify` model a pipeline of such phases followed by an abstract back
end.
-/

public section

namespace Core.Specification

open Core Core.Logic Imperative Strata.Logic Imperative.Logic

namespace Analysis

/-- The verdict a `VCResults` array reports about assertion `a`: `valid` when
    some result is for an obligation labeled `a.label` and every result passes,
    `unknown` otherwise. Every result has to pass, not only those labeled
    `a.label`: labels are chosen by the user and need not be unique, and a
    procedure is verified against its callees' contracts, which hold on runs
    only when the callees' own obligations pass too. Together with
    `VerifyConfig.verify` verifying every reachable procedure, one failing
    obligation anywhere makes every verdict `unknown`. The results carry no
    entry or model, so they never claim `failed`. -/
@[expose] def vcResultsVerdict {Entry : Type _} (results : VCResults)
    (a : Imperative.AssertId Expression) : Strata.Analysis.Verdict Entry :=
  if results.any (·.obligation.label == a.label) && results.all (·.isSuccess) then .valid
  else .unknown none

/-! ### The entries of a Core program -/

/-- The event languages Core runs a procedure body in, for the procedures of a
    program: the statement semantics for a structured body (`true`), and the
    CFG semantics for a CFG body (`false`). -/
@[expose] def coreEventLang : Program × Bool → EventLang Expression (Event Expression)
  | (p, Bool.true) => Core.Logic.EventLang.core p.findProcByString?
  | (p, Bool.false) => Core.Logic.EventLang.coreCFG p.findProcByString?

/-- An entry of a Core program: an entry procedure and the values of the
    variables at its entry. -/
structure CoreEntry where
  procName : String
  proc : Procedure
  ρ₀ : Imperative.Env Expression

/-- The configuration a run from entry `w` of program `p` starts from: the
    procedure's body, structured or CFG, in the entry environment. -/
@[expose] def coreStart (p : Program) (w : CoreEntry) :
    (i : Program × Bool) × (coreEventLang i).CfgT :=
  match w.proc.body with
  | .structured ss =>
    ⟨(p, true), (Core.Logic.EventLang.core p.findProcByString?).stmtCfg (Stmt.block "" ss #[]) w.ρ₀⟩
  | .cfg c =>
    ⟨(p, false), (Core.Logic.EventLang.coreCFG p.findProcByString?).stmtCfg c w.ρ₀⟩

/-- `w` is an entry of `p`: it names a procedure of `p` and an environment its
    body may start from (under some `InitEnvWFParams`). -/
@[expose] def IsCoreEntry (p : Program) (w : CoreEntry) : Prop :=
  p.findProcByString? w.procName = some w.proc ∧
    ∃ params, ProcEntryEnv params w.procName p w.proc w.ρ₀

/-- **The entries of a Core program.** A program is a Core program with the
    entry points to consider, an entry is one of them with values for its
    variables, and a run starts from that procedure's body. -/
@[expose] def coreEntries : ProgramEntries coreEventLang where
  Program := CoreVerifierInput
  Entry := CoreEntry
  entries input w := w.procName ∈ input.entryPoints ∧ IsCoreEntry input.prog w
  start input w := coreStart input.prog w

/-- **Deductive verification of a Core program.** The report read from `results`
    by `vcResultsVerdict` is deductive verification of `input`, with conditions
    read under their own runtime factory: each `valid` verdict holds on every
    bounded run from every entry, whose runtime factory may carry any model of the
    factory visible before the entry procedure. -/
@[expose] def DeductiveVerificationOnCore
    (input : CoreVerifierInput) (results : VCResults) : Prop :=
  Strata.Analysis.DeductiveVerification Imperative.BigStep.evalInterp coreEntries input
    (vcResultsVerdict results)

/-- `analyze` is a deductive verifier for Core: on every input, its results are
    deductive verification of the input program. -/
@[expose] def IsDeductiveVerifier (analyze : CoreVerifierInput → VCResults) : Prop :=
  Imperative.Analysis.MatchesAnalysis analyze DeductiveVerificationOnCore

/-! ### Pipelines

Strata's verifier runs a pipeline of program-to-program phases and then a final
phase that generates and discharges verification conditions. The definitions
below model the phases as partial functions on programs, so that a pipeline is
a deductive verifier when each phase overapproximates the runs of every entry
point and the final phase is a deductive verifier
(`isDeductiveVerifier_pipelineVerify`). -/

/-- **`phase` overapproximates the runs of every entry point.** Whenever it
    relates `p` to the program `p'` it produces, each entry of `p` has an entry
    of `p'` for the same procedure name whose runs overapproximate its own, for
    assertion validity. Either body may be structured or a CFG,
    so a phase that lowers structured bodies to CFGs is covered. -/
@[expose] def PhaseOverapproximates (phase : Program → Program → Prop) : Prop :=
  ∀ p p', phase p p' → ∀ w, IsCoreEntry p w →
    ∃ w', w'.procName = w.procName ∧ IsCoreEntry p' w' ∧
      (coreEventLang (coreStart p w).1).RunsOverapproximate
        (Strata.Analysis.ValidityReflected Imperative.BigStep.evalInterp)
        (coreEventLang (coreStart p' w').1) (coreStart p w).2 (coreStart p' w').2

/-- Run the phases in order, stopping at the first that fails. -/
@[expose] def runPhases : List (Program → Option Program) → Program → Option Program
  | [], p => some p
  | phase :: rest, p => (phase p).bind (runPhases rest)

/-- The verifier that runs `phases` and then `vcg` on the result, keeping the
    entry points. A pipeline that fails produces no result, so every verdict is
    `unknown`. -/
@[expose] def pipelineVerify (phases : List (Program → Option Program))
    (vcg : CoreVerifierInput → VCResults) (input : CoreVerifierInput) : VCResults :=
  match runPhases phases input.prog with
  | some p' => vcg ⟨input.entryPoints, p'⟩
  | none => #[]

/-! ### Strata's verifier

`Core.verify` runs the phases of a pipeline it is given and then a back end that
generates verification conditions and discharges them with an external solver.
Whether its results are deductive verification depends on the pipeline, so the
statement below is for every valid configuration, one whose phases each
preserve deductive verification. -/

/-- `phase` produces `p'` from `p`, from some transformation state. -/
@[expose] def _root_.Core.PipelinePhase.Transforms (phase : PipelinePhase) (p p' : Program) :
    Prop :=
  ∃ s changed s', (phase.transform p).run.run s = (.ok (changed, p'), s')

/-- **`phase` preserves deductive verification backwards**: whenever it turns
    `p` into `p'`, results that are deductive verification of `p'` are
    deductive verification of `p`, for the same entry points. A
    phase that overapproximates the runs of every entry point has this
    property; a phase that does not can establish it some other way. -/
@[expose] def PhasePreservesDeductiveVerification (phase : PipelinePhase) : Prop :=
  ∀ p p', phase.Transforms p p' → ∀ entryPoints results,
    DeductiveVerificationOnCore ⟨entryPoints, p'⟩ results →
    DeductiveVerificationOnCore ⟨entryPoints, p⟩ results

/-- What `Core.verify` is run with besides the program, for the configurations
    the statement below covers: a given pipeline, Core's own factory, solver
    and discharge function, no external phases and no assumed entry facts.
    Running with `pipeline := none`, a custom discharge function or assumed
    facts, and front ends that call `Core.verify` differently, are not covered. -/
structure VerifyConfig where
  tempDir : System.FilePath
  options : VerifyOptions
  pipeline : ValidatedPipeline ProgramFactSet.empty

/-- `cfg` is valid for deductive verification: every phase of its pipeline
    preserves deductive verification backwards, and none restricts the program
    to some of its procedures. `Core.verify` reads `proceduresToVerify` only
    when it builds its own pipeline, so the procedures a given pipeline verifies
    are those its filter phases keep; a filter built for the entry points alone
    would drop the obligations of their callees, whose contracts the entry
    points are verified against. -/
@[expose] def ValidConfig (cfg : VerifyConfig) : Prop :=
  (∀ phase ∈ cfg.pipeline.phases, PhasePreservesDeductiveVerification phase) ∧
  ∀ phase ∈ cfg.pipeline.phases, phase.phase.name ≠ (filterProceduresPipelinePhase []).phase.name

/-- The entry points of `input` and every procedure reachable from them through
    calls. Verifying only the entry points checks each of them against its
    callees' contracts, which says something about runs only once those
    callees are verified against their contracts too. -/
def CoreVerifierInput.reachableProcedures (input : CoreVerifierInput) : List String :=
  input.entryPoints ++ input.prog.toProcedureCG.getAllCalleesClosure input.entryPoints

/-- `Core.verify` under `cfg`, on the entry points of `input` and every
    procedure they reach, discharging every obligation of those procedures.
    `vcResultsVerdict` reads `valid` only when every result passes, so an
    obligation skipped by `obligationsToVerify` would make it miss a failing
    one; this resets that option. With a given pipeline, `proceduresToVerify`
    is not read, and `ValidConfig` requires the pipeline to filter no
    procedure, so every procedure is verified. With `options.incremental` set,
    and neither `vcDirectory` nor `alwaysGenerateSMT`, `verifyPipeline`
    discharges the obligations by walking the obligation tree
    (`IncrementalSolve`), except for goals alone in their session, and for
    every goal when no solver session can be started, which go one solver
    per obligation. -/
def VerifyConfig.verify (cfg : VerifyConfig) (input : CoreVerifierInput) :=
  Core.verify input.prog cfg.tempDir
    { cfg.options with
      proceduresToVerify := some input.reachableProcedures
      obligationsToVerify := none }
    (pipeline := some cfg.pipeline)

/-- **`Core.verify` is a deductive verifier on the configurations `VerifyConfig`
    covers.** For every valid configuration, one whose pipeline phases each
    preserve deductive verification and filter no procedure, every `VCResults`
    that `Core.verify` returns is deductive verification of the program the
    user wrote, for runtime factories over the factory visible before each entry procedure,
    with any model. It covers both ways
    `verifyPipeline` can discharge the obligations: one solver per obligation,
    and, with `options.incremental` set and neither `vcDirectory` nor
    `alwaysGenerateSMT`, the obligation-tree walk of `IncrementalSolve`.
    This is the statement, not yet a theorem: proving it needs the
    correctness of the back end, symbolic evaluation and obligation extraction,
    and the soundness of the solver.  On a program with an operator that carries no
    type, the statement constrains nothing: such an expression has no value, so a run
    stops at it and every verdict is deductive verification.  `TypeCheckAnnotates`
    states the obligation that rules this out for the type-checked program. -/
@[expose] def CoreVerifyIsDeductive : Prop :=
  ∀ cfg : VerifyConfig, ValidConfig cfg →
    Imperative.Analysis.MatchesAnalysisWhenOk cfg.verify DeductiveVerificationOnCore

/-- **Type inference annotates every expression.**  `Expression.eval` gives an expression
    a value only when it type checks once its free variables are annotated, and
    `Lambda.LExpr.typeCheck` rejects an operator that carries no type.  The translator from
    the Strata dialect (`strataProgramToCore`) emits the map operators `Select` and
    `Update` and `Sequence.length` without a type, so on a translated program that uses
    them `CoreVerifyIsDeductive` holds of every verdict (`TypeCheckAnnotatesTest` checks
    an instance).  The statement: every expression of
    a program `Core.typeCheck` accepts carries a type on each operator and free variable.
    This is the statement, not yet a theorem.  It says that the annotations are present,
    not that they are right: an annotated but ill-typed expression still has no value.
    Deductive verification of the type-checked program constrains the verifier only with
    `TypeCheckWellTypes` as well, which covers monomorphic programs. -/
@[expose] def TypeCheckAnnotates : Prop :=
  ∀ (options : VerifyOptions) (program program' : Program)
    (factory : Lambda.Factory CoreLParams),
    Core.typeCheck options program factory = .ok program' →
      program'.allExprs Lambda.LExpr.fullyAnnotated = Bool.true

/-- **Type inference produces expressions that evaluate.**  `Expression.HasType`
    (`Core.InstExprTyping`) is the condition under which `Expression.eval` gives a well-typed
    expression a value of its type in a store conforming to its typing
    (`Core.eval_of_hasType`); nothing yet connects it to `Core.typeCheck`.  The statement:
    every statement expression of a monomorphic program `Core.typeCheck` accepts has a type
    under the typing its own free-variable annotations give.  This is the statement, not yet
    a theorem; with a store whose values have the annotated types, it says a type-checked
    program does not get stuck evaluating an expression. -/
@[expose] def TypeCheckWellTypes : Prop :=
  ∀ (options : VerifyOptions) (program program' : Program)
    (factory : Lambda.Factory CoreLParams),
    Core.typeCheck options program factory = .ok program' →
    program'.noPolymorphicProcedures = Bool.true →
    ∀ d ∈ program'.decls, ∀ e ∈ Statements.allExprs d.statements,
      ∃ ty, Core.Expression.HasType (Core.Expression.annotationTyping e) e ty

/-- **Type inference agrees with its annotations.**  The well-formedness condition of an entry
    (`InitEnvWF.fvarTypesOk`) asks for a typing of the entry store that the annotations of the
    body agree with (`Block.fvarTypesWellAnnotated`).  The statement: the body of every
    procedure of a program `Core.typeCheck` accepts passes the check under the types of the
    procedure's parameters, so an entry store whose parameters hold values of their declared
    types has such a typing.  This is the statement, not yet a theorem.

    A related gap has no statement yet: a call writes back only values of the types of the
    caller's variables (`Imperative.Calls.CallExit`), so a run stops at a call whose callee
    output has another type.  Stating that type-checked programs never reach such a call needs
    the typing at each program point, which no definition provides yet. -/
@[expose] def TypeCheckAnnotationsAgree : Prop :=
  ∀ (options : VerifyOptions) (program program' : Program)
    (factory : Lambda.Factory CoreLParams),
    Core.typeCheck options program factory = .ok program' →
    ∀ q md, Decl.proc q md ∈ program'.decls →
      Block.fvarTypesWellAnnotated (fun x => q.paramTys.lookup x) q.body.statements

end Analysis

end Core.Specification

end -- public section
