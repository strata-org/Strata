/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Analysis.ProcedureCorrectness
public import Strata.Languages.Core.DeclFormulas
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

`coreEntriesFrom base` extends these entries with one declarations entry per model of
the program's functions, whose run walks the declarations in order, assuming each axiom
and `distinct` declaration and asserting each lemma, which it never assumes afterwards
(`declsLang`). Its runtime factory is `base` extended with all of the declarations
(`runtimeFactoryOf`), with any model of it. Procedure entries are the entries above
(`IsCoreEntry`), whose factory is Core's extended with the functions declared before the
procedure, without `base` or the functions generated for datatypes. Conditions are read
under the factory and store they were captured with (`Imperative.BigStep.evalInterp`).
`DeductiveVerificationOnCoreWith base` says results are deductive verification of a
program over `base`, and `PhasePreservesDeductiveVerificationFrom` says a pipeline phase,
run from a transform state, carries it back from its output to its input. A phase that
overapproximates the runs of every entry (`PhaseOverapproximatesFrom`) does.

These are the definitions later correctness proofs build on. The earlier ones
(`DeductiveVerificationOnCore`, `PhaseOverapproximates`, `CoreVerifyIsDeductive`) stay for
the statements that use them, and are to be retired: deductive verification over a base
implies the earlier reading (`deductiveVerificationOnCore_of_with`). `PhasesRun` and
`PipelinePhase.Runs` are the stateful counterparts of `runPhases` and
`PipelinePhase.Transforms`, which hides the states (`PipelinePhase.transforms_iff_runs`).
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
    Deductive verification of the type-checked program constrains the verifier only when
    its expressions also have values: for statement expressions, `TypeCheckWellTypes` states
    that type checking ensures this on monomorphic programs; for the axiom, lemma and
    `distinct` formulas, theorems take the per-program `declFormulasTyped` or
    `Program.formulasTypedB` (`TypeCheckDeclFormulasTyped` is false today). -/
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

/-- **Type inference gives declaration formulas a value.**  The statement: every axiom,
    lemma and `distinct` formula of a program `Core.typeCheck` accepts is a closed Boolean
    expression, and a `distinct` declaration's expressions have one type
    (`declFormulasTyped`), so each has a value at the declarations entry.  This is the
    statement, not yet a theorem, and it is false until type checking requires one type for
    a `distinct` declaration's expressions: `Core.typeCheck` accepts `distinct [mix]: [c, b]`
    with `c : int` and `b : bool`, which `declFormulasTyped` rejects (`CoreEntriesTests` pins
    this). So no theorem takes it as a hypothesis yet; theorems take the per-program
    `declFormulasTyped`, or `Program.formulasTypedB`, which only excludes the programs it
    rejects. -/
@[expose] def TypeCheckDeclFormulasTyped : Prop :=
  ∀ (options : VerifyOptions) (program program' : Program)
    (factory : Lambda.Factory CoreLParams),
    Core.typeCheck options program factory = .ok program' →
    ∀ d ∈ program'.decls, declFormulasTyped d = Bool.true

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

/-! ### The entries of a Core program, with its declarations -/


/-! #### The functions a run evaluates with

A program's expressions mention Core's built-in operators, the functions the program
declares, and the constructors, testers, destructors and eliminators of the datatypes it
declares. Runs evaluate them under a runtime factory, a factory with a model of it, so an
entry fixes that factory to the program's own: the `base` factory (Core's built-ins, or
what earlier pipeline phases made of them) extended with the declarations before the
entry. The model is any consistent one, so verifying an entry means verifying it in
every model of the program's functions and axioms. -/

/-- The factory a run evaluates with after `decls`: `base` extended with the functions
    `decls` declare, in order. -/
@[expose] def runtimeFactoryOf (base : Lambda.Factory CoreLParams) (decls : List Decl) :
    Lambda.Factory CoreLParams :=
  decls.foldl Decl.addToRuntimeFactory base

/-! #### The declarations entry

A program's declarations are read in order, as Core's program evaluator reads them: an
axiom is assumed, a `distinct` declaration assumes that its expressions are pairwise
different, and a lemma is asserted under the assumptions before it and is never assumed
afterwards. The other declarations only extend the factory. A lemma whose formula has no
value in the model is not asserted, so a verdict on it claims nothing. A `distinct`
declaration whose expressions have different sorts is assumed as false, since equality
across sorts has no value, so the declarations after it are never reached and verdicts on
the lemmas after it claim nothing. Neither happens when every declaration's formulas are
closed Boolean expressions (`declFormulasTyped`), one sort for a `distinct` declaration's
expressions included; theorems take that per-program fact as a hypothesis
(see `TypeCheckDeclFormulasTyped` for why they do not rely on type checking).

A known divergence from `Core.verify`: this entry assumes a `distinct` declaration only for
the lemmas after it, as the language reference states (`LangDefDoc.lean`: each lemma is
checked under the axioms and `distinct` facts declared before it). `Core.verify` instead
hoists every `distinct` declaration into every lemma's obligation (`Program.eval` keeps
them apart from the path condition, and `evalProgramDecls` emits all of them ahead of the
obligations), while axioms keep declaration order. So a lemma before a `distinct` it needs
is reported proved, and this entry says nothing about it (`CoreEntriesTests` pins it).
Until `Core.verify` scopes `distinct` declarations by position for lemmas, a theorem that
reads its lemma verdicts takes `Program.distinctsBeforeLemmasB` as a hypothesis. -/

/-- The condition of a declaration's event, captured in `ρ`. -/
@[expose] def declArg (ρ : Imperative.Env Expression) (label : String) (e : Expression.Expr)
    (md : Imperative.MetaData Expression) : EventArg Expression :=
  { factory := ρ.factory, store := ρ.store, label := label, expr := e, metadata := md }

/-- The assertion of lemma `l`, captured in `ρ`. -/
@[expose] def lemmaEvent (l : Lemma) (md : Imperative.MetaData Expression)
    (ρ : Imperative.Env Expression) : EventArg Expression :=
  declArg ρ l.name l.e md

/-- The conditions declaration `d` assumes, captured in `ρ`: an axiom's formula, and the
    pairwise disequalities of a `distinct` declaration's expressions. -/
@[expose] def declAssumes (ρ : Imperative.Env Expression) : Decl → List (EventArg Expression)
  | .ax a md => [declArg ρ a.name a.e md]
  | .distinct n es md => es.orderedPairs.map fun (a, b) =>
      declArg ρ (toString n) (distinctPairExpr a b) md
  | _ => []

/-- The events declaration `d` raises in `ρ`: its assumptions, or, for a lemma whose
    formula has a value, its assertion. A lemma whose formula has no value raises no event,
    so a verdict on it claims nothing. -/
@[expose] noncomputable def declEvents (ρ : Imperative.Env Expression) (d : Decl) :
    List (Event Expression) :=
  match d with
  | .lemma l md =>
    if (Expression.eval ρ.factory ρ.store l.e).isSome then [.assert (lemmaEvent l md ρ)] else []
  | d => (declAssumes ρ d).map .assume

/-- Every condition the declarations of `decls` assume holds in `ρ`. -/
@[expose] def DeclsFactsHold (decls : List Decl) (ρ : Imperative.Env Expression) : Prop :=
  ∀ d ∈ decls, ∀ c ∈ declAssumes ρ d, Imperative.BigStep.evalInterp.holds () c

/-- A configuration of a run over declarations: the declarations left to read, or the
    end of the run. -/
inductive DeclsCfg where
  | run (ρ : Imperative.Env Expression) (rest : List Decl)
  | terminal (ρ : Imperative.Env Expression)

/-- One step of a run over declarations reads one declaration and raises its events. -/
inductive DeclsStep : DeclsCfg → List (Event Expression) → DeclsCfg → Prop
  | decl {ρ : Imperative.Env Expression} {d : Decl} {rest : List Decl} :
      DeclsStep (.run ρ (d :: rest)) (declEvents ρ d) (.run ρ rest)
  | done {ρ : Imperative.Env Expression} : DeclsStep (.run ρ []) [] (.terminal ρ)

/-- **The event language of a program's declarations**: a run reads them in order, in a
    fixed environment. -/
@[expose] def declsLang : EventLang Expression (Event Expression) where
  StmtT := List Decl
  CfgT := DeclsCfg
  step := DeclsStep
  stmtCfg ds ρ := .run ρ ds
  terminalCfg := .terminal
  exitingCfg _ ρ := .terminal ρ
  terminal_no_step := by intro _ _ _ h; cases h
  exiting_no_step := by intro _ _ _ _ h; cases h
  getEnv
    | .run ρ _ | .terminal ρ => ρ
  InitEnvWFParamsTy := Unit
  initEnvWF _ _ _ := True

/-- The event languages Core runs an entry in: those of a procedure body
    (`coreEventLang`), and the language of declarations. -/
inductive CoreLangIdx where
  | proc (i : Program × Bool)
  | decls

/-- The event language of each index. -/
@[expose] def coreEventLangWithDecls : CoreLangIdx → EventLang Expression (Event Expression)
  | .proc i => coreEventLang i
  | .decls => declsLang

/-! #### Entries -/

/-- An entry of a Core program: a run starts either from the body of an entry
    procedure, with values for its variables (`CoreEntry`), or from the program's
    declarations, in an environment with a model of all of them. -/
inductive CoreEntryWithDecls where
  | proc (w : CoreEntry)
  | decls (ρ₀ : Imperative.Env Expression)

/-- The configuration a run from entry `w` of program `p` starts from: the
    procedure's body, structured or CFG, or the program's declarations, in the entry
    environment. -/
@[expose] def coreStartWithDecls (p : Program) (w : CoreEntryWithDecls) :
    (i : CoreLangIdx) × (coreEventLangWithDecls i).CfgT :=
  match w with
  | .proc w => ⟨.proc (coreStart p w).1, (coreStart p w).2⟩
  | .decls ρ₀ => ⟨.decls, DeclsCfg.run ρ₀ p.decls⟩

/-- `w` is an entry of `p` over the factory `base`.

    - A procedure entry is an entry of mainline's procedure entries (`IsCoreEntry`): it
      names a procedure of `p` and an environment its body may start from
      (`ProcEntryEnv`), whose factory is Core's extended with the functions declared
      before the procedure (`Program.factoryBeforeProcedure`). That factory has neither
      `base` nor the functions generated for datatypes, so a body that evaluates a
      datatype's constructor, tester or destructor gets stuck there, and deductive
      verification says nothing about the assertions after it. Giving procedure entries
      the runtime factory over `base` is follow-up work.
    - The declarations entry starts from the empty store, with a runtime factory that is
      `base` extended with all of `p`'s declarations, and any model of it. A lemma refers
      to no variable. -/
@[expose] def IsCoreEntryAt (base : Lambda.Factory CoreLParams) (p : Program) :
    CoreEntryWithDecls → Prop
  | .proc w => IsCoreEntry p w
  | .decls ρ₀ =>
    ρ₀.factory.factory = runtimeFactoryOf base p.decls ∧ ρ₀.store = (fun _ => none)

/-- **The entries of a Core program**, over the factory `base`: a program is a Core
    program with the entry points to consider, and its entries are those entry points,
    with values for their variables, and its declarations. -/
@[expose] def coreEntriesFrom (base : Lambda.Factory CoreLParams) :
    ProgramEntries coreEventLangWithDecls where
  Program := CoreVerifierInput
  Entry := CoreEntryWithDecls
  entries input w := match w with
    | .proc w' => w'.procName ∈ input.entryPoints ∧ IsCoreEntryAt base input.prog w
    | .decls .. => IsCoreEntryAt base input.prog w
  start input w := coreStartWithDecls input.prog w

/-- **Deductive verification of a Core program over the factory `base`.** The report
    read from `results` by `vcResultsVerdict` is deductive verification of `input`, with
    each condition read under the runtime factory and store it was captured with
    (`Imperative.BigStep.evalInterp`): each `valid` verdict holds on every bounded run from
    every entry, whose runtime factory carries any model of `base` and the program's
    functions.

    Every condition is read the same way whatever its runtime factory, so two programs
    whose runs carry different factories (a phase that adds, specializes or rewrites
    functions) are compared under one reading. What a condition may mean is fixed by the
    entries the run starts from, which pin the runtime factory. -/
@[expose] def DeductiveVerificationOnCoreWith (base : Lambda.Factory CoreLParams)
    (input : CoreVerifierInput) (results : VCResults) : Prop :=
  Strata.Analysis.DeductiveVerification Imperative.BigStep.evalInterp (coreEntriesFrom base) input
    (vcResultsVerdict results)

/-- **Deductive verification of a Core program.** A program as written need not carry
    the type annotations its expressions need for a value (a program parsed from text
    carries none), so it means what its elaboration means: the program `Core.typeCheck`
    produces, over Core's own factory. The report read from `results` is deductive
    verification of that program. A program that does not type check claims nothing. -/
@[expose] def DeductiveVerificationOnElaborated
    (input : CoreVerifierInput) (results : VCResults) : Prop :=
  ∀ prog', Core.typeCheck .default input.prog Core.Factory = .ok prog' →
    DeductiveVerificationOnCoreWith Core.Factory ⟨input.entryPoints, prog'⟩ results

/-- `analyze` is a deductive verifier for Core: on every input, its results are
    deductive verification of the input program. -/
@[expose] def IsDeductiveVerifierOnElaborated (analyze : CoreVerifierInput → VCResults) : Prop :=
  Imperative.Analysis.MatchesAnalysis analyze DeductiveVerificationOnElaborated

/-! ### Pipelines

Strata's verifier runs a pipeline of program-to-program phases and then a back end
that generates and discharges verification conditions. The phases share one
transform state, whose factory holds the functions a phase may rely on besides the
program's own (`Transform.CoreTransformState.factory`), so a program means something
only together with that factory: an intermediate program is read over the factory of
the state it is in. -/

/-- A run of `phases` in order, each phase succeeding, from state `s` and program `p`
    to state `s'` and program `p'`. -/
inductive PhasesRun : List PipelinePhase → Transform.CoreTransformState → Program →
    Transform.CoreTransformState → Program → Prop
  | nil {s p} : PhasesRun [] s p s p
  | cons {phase rest s p s₁ p₁ s' p'} :
      phase.Runs s p s₁ p₁ → PhasesRun rest s₁ p₁ s' p' →
      PhasesRun (phase :: rest) s p s' p'

/-- **`phase` preserves deductive verification backwards from what `pre` admits**:
    whenever it turns `p` into `p'` from a state and program `pre` admits, results
    that are deductive verification of `p'`, over the factory of the state it ends in,
    are deductive verification of `p`, over the factory of the state it starts in, for
    the same entry points. A phase that overapproximates the runs of every entry
    (`PhaseOverapproximatesFrom`) has this property; a phase that does not can establish
    it some other way. -/
@[expose] def PhasePreservesDeductiveVerificationFrom
    (pre : Transform.CoreTransformState → Program → Prop) (phase : PipelinePhase) : Prop :=
  ∀ s p s' p', pre s p → phase.Runs s p s' p' → ∀ entryPoints results,
    DeductiveVerificationOnCoreWith s'.factory ⟨entryPoints, p'⟩ results →
    DeductiveVerificationOnCoreWith s.factory ⟨entryPoints, p⟩ results

/-- An entry `w'` of a transformed program stands for the entry `w` of the original:
    a procedure entry for the same procedure name, a declarations entry for a
    declarations entry. -/
@[expose] def CoreEntryWithDecls.Corresponds : CoreEntryWithDecls → CoreEntryWithDecls → Prop
  | .proc w, .proc w' => w'.procName = w.procName
  | .decls _, .decls _ => True
  | _, _ => False

/-- **`phase` overapproximates the runs of every entry, from what `pre` admits.**
    Whenever it turns `p` into `p'`, each entry of `p` has a corresponding entry of
    `p'` whose runs overapproximate its own, for assertion validity. Either body may
    be structured or a CFG, so a phase that lowers structured bodies to CFGs is
    covered. -/
@[expose] def PhaseOverapproximatesFrom
    (pre : Transform.CoreTransformState → Program → Prop) (phase : PipelinePhase) : Prop :=
  ∀ s p s' p', pre s p → phase.Runs s p s' p' → ∀ w, IsCoreEntryAt s.factory p w →
    ∃ w', w.Corresponds w' ∧ IsCoreEntryAt s'.factory p' w' ∧
      (coreEventLangWithDecls (coreStartWithDecls p w).1).RunsOverapproximate
        (Strata.Analysis.ValidityReflected Imperative.BigStep.evalInterp)
        (coreEventLangWithDecls (coreStartWithDecls p' w').1)
          (coreStartWithDecls p w).2 (coreStartWithDecls p' w').2


/-! ### Phases that reflect the declarations entry -/

/-- The events of a run over all of `ds`, in `ρ`. -/
@[expose] noncomputable def declsTrace (ρ : Imperative.Env Expression) (ds : List Decl) :
    List (Event Expression) :=
  ds.flatMap (declEvents ρ)

/-- **The declarations `ds'`, read in `ρ'`, reflect the declarations `ds`, read in `ρ`.**
    Every lemma of `ds` that is asserted (its formula has a value), whenever the conditions
    the declarations before it assume hold, has a lemma of `ds'`, with the same name and
    metadata, that is asserted, such that the conditions the declarations before it assume
    hold, and the second lemma's truth implies the first's. The output lemma is chosen
    under the input's facts: it need only exist, and be asserted, when the conditions the
    declarations before the input lemma assume hold. A rewrite under those conditions (as
    equality simplification does) gives a formula with a value only then.

    The output's assumptions need only follow from the input's so far: it may drop, merge
    or rewrite axioms and `distinct` declarations, and it may add lemmas.

    Each input lemma maps to one output lemma, with the same name and metadata. A phase that
    splits a lemma into several, none of which alone implies it, or that changes a lemma's
    metadata, is outside this statement. -/
@[expose] def DeclsReflect (ρ : Imperative.Env Expression) (ds : List Decl)
    (ρ' : Imperative.Env Expression) (ds' : List Decl) : Prop :=
  ∀ i l md, ds[i]? = some (.lemma l md) → (Expression.eval ρ.factory ρ.store l.e).isSome →
    DeclsFactsHold (ds.take i) ρ →
    ∃ j l', ds'[j]? = some (.lemma l' md) ∧ l'.name = l.name ∧
      (Expression.eval ρ'.factory ρ'.store l'.e).isSome ∧
      DeclsFactsHold (ds'.take j) ρ' ∧
      (Imperative.BigStep.evalInterp.holds () (lemmaEvent l' md ρ') →
        Imperative.BigStep.evalInterp.holds () (lemmaEvent l md ρ))

/-- `p` declares no procedure, so its only entry is its declarations. -/
@[expose] def NoProcedures (p : Program) : Prop :=
  ∀ d ∈ p.decls, d.kind ≠ .proc

/-- **`phase` reflects the declarations entry, from what `pre` admits.** Whenever it turns
    `p` into `p'`, the declarations of each declarations entry of `p`, over the factory of
    the state the phase starts in, are reflected by those of a declarations entry of `p'`,
    over the factory of the state it ends in (`DeclsReflect`). -/
@[expose] def PhaseReflectsLemmas
    (pre : Transform.CoreTransformState → Program → Prop) (phase : PipelinePhase) : Prop :=
  ∀ s p s' p', pre s p → phase.Runs s p s' p' →
    ∀ ρ, IsCoreEntryAt s.factory p (.decls ρ) →
      ∃ ρ', IsCoreEntryAt s'.factory p' (.decls ρ') ∧ DeclsReflect ρ p.decls ρ' p'.decls

end Analysis

end Core.Specification

end -- public section
