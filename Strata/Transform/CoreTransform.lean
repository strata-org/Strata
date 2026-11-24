/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.Languages.Core.CallGraph
public import Strata.Languages.Core.CoreGen
public import Strata.Languages.Core.NameSets
public import Strata.Languages.Core.Typing.Spec.ProcedureTypeSpec
public import Strata.DL.Lambda.LTyMatch
public import Strata.Util.Statistics

/-! # Utility functions for program transformation in Strata Core -/

public section

namespace Core
namespace Transform

open LabelGen
open Strata.Util (HMap)

/-- Prefix of the temporary holding the value of `old id` at a call, under the prefix `pfx` of
    the pass's names (call elimination's is `CallElim.callElimPrefix`). -/
def oldVarPrefix (pfx id : String) : String := s!"{pfx}Old_{id}"
/-- Prefix of the temporary holding a call's argument (`id` is `arg`) or the value of its output
    `id` before the call, under the prefix `pfx` of the pass's names. -/
def tmpVarPrefix (pfx id : String) : String := s!"{pfx}Tmp_{id}"

def createHavoc (ident : Expression.Ident)
    (md : Imperative.MetaData Expression)
  : Statement := Statement.havoc ident md

@[expose]
def createHavocs (ident : List Expression.Ident) (md : (Imperative.MetaData Expression))
  : List Statement := ident.map (createHavoc · md)

@[expose]
def createFvars (ident : List Expression.Ident)
  : List Expression.Expr
  := ident.map (createFvar ·)

/-- References to the variables `vs`, each annotated with its monotype. -/
def createTypedFvars (vs : List (Expression.Ident × Expression.Ty)) : List Expression.Expr :=
  vs.map fun (v, ty) => createFvar v ty.toMonoType?

def genIdent (ident : Expression.Ident) (pf : String → String)
  : CoreGenM Expression.Ident :=
    CoreGenState.gen (pf ident.name)

/-- A fresh variable named after `pf ident`, drawn from the generator's counter, and not in
    `taken`. The counter alone keeps it apart from the names it generated before; `taken` must
    hold the program's own variable names, which the counter does not know. -/
def genTempIdent (taken : Std.HashSet String) (ident : Expression.Ident)
    (pf : String → String) : CoreGenM Expression.Ident :=
  CoreGenState.genAvoiding taken ⟨pf ident.name, ()⟩

/-- A fresh temporary `<pfx>Tmp_arg_N`, not in `taken`, to hold an argument expression. -/
def genArgExprIdent (pfx : String) (taken : Std.HashSet String)
  : CoreGenM Expression.Ident :=
    genTempIdent taken "arg" (tmpVarPrefix pfx)

/-- `n` fresh argument temporaries (`genArgExprIdent`). -/
def genArgExprIdents (pfx : String) (taken : Std.HashSet String) (n : Nat)
  : CoreGenM (List Expression.Ident) :=
  List.mapM (fun _ => genArgExprIdent pfx taken) (List.replicate n ())

/-- A fresh temporary `<pfx>Tmp_<ident>_N`, not in `taken`, to hold the value of the output
    variable `ident` before the call. -/
def genOutExprIdent (pfx : String) (taken : Std.HashSet String) (ident : Expression.Ident)
  : CoreGenM Expression.Ident :=
    genTempIdent taken ident (tmpVarPrefix pfx)

/-- One fresh output temporary (`genOutExprIdent`) per identifier of `idents`. -/
def genOutExprIdents (pfx : String) (taken : Std.HashSet String) (idents : List Expression.Ident)
  : CoreGenM (List Expression.Ident)
  := List.mapM (genOutExprIdent pfx taken) idents

/-- A fresh variable `<pfx>Old_<ident>_N`, not in `taken`, to hold the value of `ident` that
    `old ident` denotes. -/
def genOldExprIdent (pfx : String) (taken : Std.HashSet String) (ident : Expression.Ident)
  : CoreGenM Expression.Ident :=
    genTempIdent taken ident (oldVarPrefix pfx)

/-- One fresh `old` variable (`genOldExprIdent`) per identifier of `idents`. -/
def genOldExprIdents (pfx : String) (taken : Std.HashSet String) (idents : List Expression.Ident)
  : CoreGenM (List Expression.Ident)
  := List.mapM (genOldExprIdent pfx taken) idents

/-- Generate one fresh type name (`TyIdentifier = String`) from the
    shared `CoreGenState` counter — the same monotonic counter that backs the
    term-temp generators — so names are deterministic, resume-safe, and unique
    across call sites without adding any new state; a name in `taken` is drawn again
    (`CoreGenState.genAvoiding`). Mirrors `genTempIdent`.

    NOTE: `CoreGenState.gen` records every generated name in `γ.generated`,
    including generated type names, which, unlike term temporaries, never get a
    store binding. Call elimination keeps its temporaries apart from the program's
    variables by `taken`, not by `generated`, so the extra
    names are harmless. -/
def genTyVarName (prefixStr : String) (taken : Std.HashSet String) :
    CoreGenM Lambda.TyIdentifier := do
  let id ← CoreGenState.genAvoiding taken ⟨prefixStr, ()⟩
  return id.name

/-- `n` fresh type names at `prefixStr`, none of them in `taken`. -/
def genTyVarNames (prefixStr : String) (taken : Std.HashSet String) (n : Nat) :
    CoreGenM (List Lambda.TyIdentifier) :=
  List.mapM (fun _ => genTyVarName prefixStr taken) (List.replicate n ())

/-- Build a one-scope type substitution mapping each declared type variable of a
    polymorphic callee to a fresh nullary type constant named at `prefixStr`
    (the caller supplies its reserved prefix, e.g. `callElimTyPrefix`) and not in
    `taken` (the program's type names with that prefix), for per-call-site contract
    instantiation. Returns the empty substitution (a verified
    identity for `LMonoTy.subst`/`LExpr.applyTypeSubst`, which short-circuit on
    `Subst.hasEmptyScopes`) when `typeArgs` is empty — so the transform is an
    exact no-op for monomorphic procedures. -/
def freshenTypeArgsSubst (prefixStr : String) (taken : Std.HashSet String)
    (typeArgs : List Lambda.TyIdentifier) : CoreGenM Lambda.Subst := do
  if typeArgs.isEmpty then
    return Lambda.Subst.empty
  else
    let fresh ← genTyVarNames prefixStr taken typeArgs.length
    return Lambda.Subst.ofNullaryConsts (typeArgs.zip fresh)

/-- The type of a call argument: the declared type of an unannotated variable, otherwise the
    type its annotations give it; `none` when neither is known. -/
def callArgType? (vt : TypeSpec.TypeScopes) : Expression.Expr → Option Lambda.LMonoTy
  | .fvar _ x none => vt.monoType? x
  | e => e.typeCheck []

/-- The type instance of a call to `proc` whose stored type arguments are `tyArgs`: the instance
    `Procedure.callTypeArgs` gives; every other parameter gets a fresh opaque type at
    `prefixStr` that is not in `taken`, and so does every parameter when the matching fails. On a
    type-checked program the matching cannot fail, and the checker rejects a call that leaves a
    callee type parameter undetermined (`ProcWellTyped.annotTyVarsBound`), so the fresh opaque
    types serve only programs that were not type-checked. An error means the stored `tyArgs`
    disagree with the argument types. -/
def callTypeSubst (prefixStr : String) (taken : Std.HashSet String) (vt : TypeSpec.TypeScopes)
    (proc : Procedure) (callArgs : List (Imperative.CallArg Expression))
    (tyArgs : Option (List Expression.Ty)) : CoreGenM (Except String Lambda.Subst) := do
  let typeArgs := proc.header.typeArgs
  let argTy : Imperative.CallArg Expression → Option Lambda.LMonoTy
    | .inArg e => callArgType? vt e
    | .inoutArg x | .outArg x => vt.monoType? x
  match proc.callTypeArgs tyArgs ((Imperative.CallArg.inputArgs callArgs).map argTy)
      ((Imperative.CallArg.resultArgs callArgs).map argTy) with
  | .error msg => return .error msg
  | .ok none =>
    -- TODO: prove that the transformations preserve typing; then this branch is provably
    -- unreachable on pipeline input.
    return .ok (← freshenTypeArgsSubst prefixStr taken typeArgs)
  | .ok (some S) =>
    let fresh ← freshenTypeArgsSubst prefixStr taken
      (typeArgs.filter fun a => (S.find? a).isNone)
    return .ok (fresh ++ [S])

/-- Cached results of program analyses that are helpful for program
    transformation.

    Invariant: When `callGraph` is `some cg`, `cg` must reflect the current
    program's procedure call structure. Every procedure in the program must
    have an entry in `cg.callees`, and every call edge must be accounted for.
    Transforms that add, remove, or modify procedures must update the call
    graph accordingly (or set it to `.none` to invalidate it). -/
structure CachedAnalyses where
  callGraph: Option CallGraph := .none

@[simp]
def CachedAnalyses.emp : CachedAnalyses := {}

/-- Define the state of transformation in Strata Core.
  It is the duty of the transformation to update the analysis cache to keep the
  correct information after code transformation, or one can simply drop the
  cached result.
-/
structure CoreTransformState where
  genState: CoreGenState
  -- The program that is being transformed. This is handy for statement-level
  -- transforms which need to get information about the transforming top-level program.
  -- The definition of "current" may vary depending on the transformation.
  -- If the transformation is implemented with runProgram or runProgramUntil,
  -- the currentProgram field will store the latest versions of finished
  -- procedures, but the procedure that is being updated might have stale
  -- statements.
  -- When a program-level transformation is finished, currentProgram must contain the
  -- program that is fully updated (or it has to be .none).
  -- Using runProgram/runProgramUntil enforces that currentProgram of this
  -- CoreTransformState is updated to be the updated program.
  currentProgram: Option Program
  currentProcedureName: Option String -- TOOD: currentFunctionName, etc?
  cachedAnalyses: CachedAnalyses
  -- Factory for transformations. This should not include any function that is
  -- directly defined in the input program or derived from the datatype defined in
  -- the input program.
  -- This can diverge from Core's built-in Factory after transformations.
  factory: @Lambda.Factory CoreLParams
  -- Per-transform statistics counters, keyed by string names.
  statistics: Statistics := {}
  -- Per-transform run counters, keyed by string names. Used to generate unique
  -- fresh-name prefixes across repeated passes.
  passCounter : HMap String Nat := {}
  -- Warnings the transformations report, in order. `runTransforms` returns them in the final
  -- state; the caller prints them (`verifyPipeline` does unless the options are quiet).
  warnings : Array Strata.Message := #[]
  -- Whether the input program's recorded `$__` prefixes (`Program.usedIdentPrefixes`) may be
  -- trusted to cover its `$__` names. `runTransformsRecording` sets it before each phase: not for
  -- the pipeline's input, which the caller may have changed after the record was computed, nor
  -- after a phase that does not maintain the record (`PipelinePhase.maintainsIdentPrefixes`),
  -- until a phase's output is found covered (`Program.identPrefixesCovered`). When it is false,
  -- `withClaimedPrefixes` collects the program's prefixes instead of reading the record. A state
  -- built without it does not trust the record either.
  identPrefixesTrusted : Bool := false

@[simp]
def CoreTransformState.emp : CoreTransformState :=
  { genState := .emp, currentProgram := .none,
    currentProcedureName := .none, cachedAnalyses := .emp,
    factory := Lambda.Factory.default }

/-- A transform state exists: the empty one. -/
instance : Nonempty CoreTransformState := ⟨.emp⟩

abbrev Err := Strata.Message

abbrev CoreTransformM := ExceptT Err (StateM CoreTransformState)

/-- A lifter from CoreGenM to (StateM CoreTransformState) -/
def liftCoreGenM {α : Type} (cgm : CoreGenM α) : StateM CoreTransformState α :=
  fun coreTransformState =>
    let res := cgm coreTransformState.genState
    (res.1, { coreTransformState with genState := res.2 })

instance : MonadLift CoreGenM (StateM CoreTransformState) where
  monadLift := liftCoreGenM

/-- Lift an `Except Message` into `CoreTransformM`. -/
def liftDiag {α : Type} (e : Except Strata.Message α) : CoreTransformM α :=
  match e with
  | .ok a => pure a
  | .error dm => throw dm

/-- `callTypeSubst`, with an error reported as a breach of the well-formed-calls requirement
    of the pass named `pass`. -/
def callTypeSubstOrBreach (pass : String) (md : Imperative.MetaData Expression)
    (prefixStr : String) (taken : Std.HashSet String) (vt : TypeSpec.TypeScopes)
    (proc : Procedure) (callArgs : List (Imperative.CallArg Expression))
    (tyArgs : Option (List Expression.Ty)) : CoreTransformM Lambda.Subst := do
  match ← callTypeSubst prefixStr taken vt proc callArgs tyArgs with
  | .ok S => pure S
  | .error msg => throw (wellFormedCallsBreach pass md msg)

/-- Get the factory from state. -/
def getFactory : CoreTransformM (@Lambda.Factory CoreLParams) := do
  return (← get).factory

/-- Update the factory in state. -/
def setFactory (F : @Lambda.Factory CoreLParams) : CoreTransformM Unit :=
  modify fun σ => { σ with factory := F }

/-- Increment a statistics counter by `n` (default 1), initializing if absent. -/
def incrementStat (key : String) (n : Nat := 1) : CoreTransformM Unit :=
  modify fun σ => { σ with statistics := σ.statistics.increment key n }

/-- The warning the pass `pass` reports when the known prefixes `known` of its input
    (`Program.knownIdentPrefixes`) are comparable with the prefixes `pfxs` of the names it
    generates: one message naming every such prefix of `known` and every prefix of `pfxs` it
    overlaps. -/
@[expose] def identPrefixConflictWarning (pass : String) (pfxs known : List String) :
    Strata.Message :=
  let used := known.filter fun q => pfxs.any (Strata.Name.prefixesComparable q)
  let ours := pfxs.filter fun pfx => used.any (Strata.Name.prefixesComparable pfx)
  let quote (l : List String) := ", ".intercalate (l.map fun x => s!"'{x}'")
  Strata.Message.fromString (kind := .warning)
    s!"{pass}: the program uses names starting with {quote used}, which overlaps the \
      prefixes {quote ours} this pass generates; it checks its generated names against the \
      program's (slower)."

/-- Run `t`, a pass on `p` whose generated names have the prefixes `pfxs`, and add the known
    prefixes of `p` (`Program.knownIdentPrefixes`) and `pfxs` to those of its output
    (`Program.addIdentPrefixes`), so that the output's recorded prefixes keep covering its
    internal names (`Program.identPrefixesCovered`), also when `t` builds its output from
    scratch. It does not look at whether `p` already uses `pfxs`: a pass that numbers its names
    without looking at the program's uses it, with a TODO saying where it must generate them
    freshly instead. -/
@[expose] def recordIdentPrefixes (pfxs : List String) (p : Program)
    (t : CoreTransformM (Bool × Program)) : CoreTransformM (Bool × Program) := do
  let (changed, p') ← t
  return (changed, p'.addIdentPrefixes (p.knownIdentPrefixes ++ pfxs))

/-- Run `t`, a pass on `p` whose output may carry internal names its own code does not choose (a
    symbolic evaluator's, for instance), and give the output the known prefixes of `p` together
    with the prefixes of the output's internal names (`Program.withCollectedIdentPrefixes`), which
    costs a walk over the output. Each expression is walked as a tree into one set of names,
    unless its tree is large (`Program.InternalNames.treeWalkFuel`); then it shares subterms, as
    a symbolic evaluator's output may, and is walked visiting each physically distinct
    subexpression once (`Program.InternalNames.exprNamesPtrCache`). -/
@[expose] def recollectIdentPrefixes (p : Program) (t : CoreTransformM (Bool × Program)) :
    CoreTransformM (Bool × Program) := do
  let (changed, p') ← t
  return (changed, (p'.addIdentPrefixes p.knownIdentPrefixes).withCollectedIdentPrefixes)

/-- Does `p` declare, at the top level, a name starting with `pfx`? The opaque types the passes
    generate are top-level declarations, so this tells, without walking the program, whether a
    pass declared one. -/
@[expose] def declaresWithPrefix (p : Program) (pfx : String) : Bool :=
  p.decls.any (·.name.name.startsWith pfx)

/-- Run the pass `pass`, `t`, on `p`, claiming the prefixes `pfxs` of the names it generates, for
    a pass that already generates names avoiding the program's. Its output records the prefixes
    as `recordIdentPrefixes` does.

    `t` is told whether the prefixes are free in `p` (`Program.identPrefixesFree`). When they are,
    and the known prefixes of `p` cover its internal names, no name of `p` starts with one of
    `pfxs` (`Program.not_startsWith_of_noConflict`), so `t` may skip collecting the program's
    names to avoid. A program that records no prefixes, or whose record the transform state does
    not trust (`CoreTransformState.identPrefixesTrusted`), has them collected here, which covers
    its internal names (`Program.identPrefixesCovered_of_none`), so it is taken as free only when
    it really has no name with `pfxs`. Otherwise one warning names the conflicts, and `t` avoids
    the program's names as before.

    The output records `recorded changed out` of the prefixes, where `changed` and `out` are what
    `t` returns; by default all of `pfxs`. A pass that may claim a prefix without generating a
    name with it records it only when it did, so that running it again does not find its own
    prefix recorded and warn: call elimination generates names only when it eliminates a call,
    and procedure inlining, call elimination and `genOpaqueTypeParams` declare their opaque types
    (`declaresWithPrefix`) only when they need them. `recorded changed out` must hold every
    prefix of `pfxs` that a new name of `out` starts with.

    The known prefixes of `p` are computed once, so a program that records none is walked once. -/
@[expose] def withClaimedPrefixes (pass : String) (pfxs : List String) (p : Program)
    (t : Bool → CoreTransformM (Bool × Program))
    (recorded : Bool → Program → List String := fun _ _ => pfxs) :
    CoreTransformM (Bool × Program) := do
  let known := if (← get).identPrefixesTrusted then p.knownIdentPrefixes
    else p.collectIdentPrefixes
  let free := Strata.Name.prefixesFree known pfxs
  unless free do
    modify fun σ =>
      { σ with warnings := σ.warnings.push (identPrefixConflictWarning pass pfxs known) }
  let (changed, p') ← t free
  return (changed, p'.addIdentPrefixes (known ++ recorded changed p'))

/-- Fresh counter for `key`, starting at 1. -/
def bumpCounter (key : String) : CoreTransformM Nat := do
  let σ ← get
  let n := (σ.passCounter.find? key).getD 0 + 1
  set { σ with passCounter := σ.passCounter.insert key n }
  return n

/-- Runs `t`, then declares at the start of its output a nullary type for
    each name the generator drew at `prefixStr` during the run (the opaque
    types of `callTypeSubst`), except the names in `taken`, which the generator drew and
    skipped. `taken` is the input program's type names with `prefixStr`; `t` must keep the
    program's type names. -/
def declareGeneratedTypes (prefixStr : String) (taken : Std.HashSet String)
    (t : CoreTransformM (Bool × Program)) :
    CoreTransformM (Bool × Program) := do
  let before := (← get).genState.generated.length
  let (changed, p) ← t
  let generated := (← get).genState.generated
  let names := (generated.take (generated.length - before)).reverse.filter
    fun n => n.name.startsWith (prefixStr ++ "_") && !taken.contains n.name
  if names.isEmpty then
    return (changed, p)
  let p' : Program :=
    { p with decls := names.map (fun n => Decl.opaqueType n.name)
        ++ p.decls }
  modify fun σ => { σ with currentProgram := some p' }
  return (true, p')



/--
returned list has the shape
((generated_name, ty), original_expr)
Only types of the 'inputs' parameter are used. The generated names start with `pfx` and avoid
`taken`.
-/
def genArgExprIdentsTrip (pfx : String) (taken : Std.HashSet String)
  (inputs : @Lambda.LTySignature Visibility)
  (args : List Expression.Expr)
  : CoreTransformM (List ((Expression.Ident × Lambda.LTy) × Expression.Expr))
  := do
  if inputs.length ≠ args.length then throw (Strata.Message.fromString "input length and args length mismatch")
  else let gen_idents ← genArgExprIdents pfx taken args.length
       return (gen_idents.zip inputs.unzip.2).zip args

/--
returned list has the shape
`((generated_name, ty), original_name)`
Only types of the 'outputs' parameter are used. The generated names start with `pfx` and avoid
`taken`.
-/
def genOutExprIdentsTrip (pfx : String) (taken : Std.HashSet String)
  (outputs : @Lambda.LTySignature Visibility)
  (lhs : List Expression.Ident)
  : CoreTransformM (List ((Expression.Ident × Expression.Ty) × Expression.Ident)) := do
  if outputs.length ≠ lhs.length then throw (Strata.Message.fromString "output length and lhs length mismatch")
  else let gen_idents ← genOutExprIdents pfx taken lhs
       return (gen_idents.zip outputs.unzip.2).zip lhs

/--
Generate an init statement with rhs as expression
-/
def createInit (trip : (Expression.Ident × Expression.Ty) × Expression.Expr)
    (md:Imperative.MetaData Expression)
  : Statement :=
  match trip with
  | ((v', ty), e) => Statement.init v' ty (.det e) md

def createInits (trips : List ((Expression.Ident × Expression.Ty) × Expression.Expr))
    (md: (Imperative.MetaData Expression))
  : List Statement :=
  trips.map (createInit · md)

/--
Generate an init statement with rhs as a free variable reference
-/
def createInitVar (trip : (Expression.Ident × Expression.Ty) × Expression.Ident)
    (md:Imperative.MetaData Expression)
  : Statement :=
  match trip with
  | ((v', ty), v) => Statement.init v' ty (.det (createFvar v ty.toMonoType?)) md

def createInitVars (trips : List ((Expression.Ident × Expression.Ty) × Expression.Ident))
    (md : (Imperative.MetaData Expression))
  : List Statement :=
  trips.map (createInitVar · md)

/-- turns a list of preconditions into assert commands with substitution -/
def createAssertCmds
    (conds : ListMap CoreLabel Procedure.Check)
    (subst : Map Expression.Ident Expression.Expr)
    (md : (Imperative.MetaData Expression))
    (labelPrefix : String := "assert_")
    : CoreTransformM (List Command)
    := conds.mapM (fun (l, check) => do
          let newLabel ← genIdent l (fun s => s!"{labelPrefix}{s}")
          -- Non-lifting: the replacement expressions must be closed (no dangling bvars).
          -- Use the call site as the primary file range, preserving the requires
          -- clause location as a related file range for richer diagnostics.
          let assertMd := check.md.setCallSiteFileRange md
          return .cmd (.assert newLabel.toPretty (Lambda.LExpr.substFvars check.expr subst)
            assertMd))

/-- turns a list of preconditions into asserts with substitution -/
def createAsserts
    (conds : ListMap CoreLabel Procedure.Check)
    (subst : Map Expression.Ident Expression.Expr)
    (md : (Imperative.MetaData Expression))
    (labelPrefix : String := "assert_")
    : CoreTransformM (List Statement)
    := (·.map .cmd) <$> createAssertCmds conds subst md labelPrefix

/-- turns a list of postconditions into assume commands with substitution -/
def createAssumeCmds
    (conds : ListMap CoreLabel Procedure.Check)
    (subst : Map Expression.Ident Expression.Expr)
    (md : (Imperative.MetaData Expression))
    (labelPrefix : String := "assume_")
    : CoreTransformM (List Command)
    :=
    conds.mapM (fun (l, check) => do
      let newLabel ← genIdent l (fun s => s!"{labelPrefix}{s}")
      -- Non-lifting: the replacement expressions must be closed (no dangling bvars).
      -- Use the call site as the primary file range, preserving the ensures
      -- clause location as a related file range for richer diagnostics.
      let assumeMd := check.md.setCallSiteFileRange md
      return .cmd (.assume newLabel.toPretty (Lambda.LExpr.substFvars check.expr subst)
        assumeMd))

/-- turns a list of postconditions into assumes with substitution -/
def createAssumes
    (conds : ListMap CoreLabel Procedure.Check)
    (subst : Map Expression.Ident Expression.Expr)
    (md : (Imperative.MetaData Expression))
    (labelPrefix : String := "assume_")
    : CoreTransformM (List Statement)
    := (·.map .cmd) <$> createAssumeCmds conds subst md labelPrefix

/-! ## Command-level builders

`Command` counterparts of the statement builders above, for transforms that rewrite one command
into a sequence of commands in a structured body or a CFG block. Each statement builder is the
corresponding command builder followed by `.cmd` (`createHavocs_eq_cmds`, `createInits_eq_cmds`,
`createInitVars_eq_cmds`, in `CoreTransformProps.lean`). -/

/-- A command that havocs `ident`. -/
def createHavocCmd (ident : Expression.Ident) (md : Imperative.MetaData Expression) : Command :=
  .cmd (.set ident .nondet md)

/-- Commands that havoc each of `ident`. -/
def createHavocCmds (ident : List Expression.Ident) (md : Imperative.MetaData Expression) :
    List Command :=
  ident.map (createHavocCmd · md)

/-- A command that declares `v'` of type `ty` with value `e`, for `((v', ty), e)`. -/
def createInitCmd (trip : (Expression.Ident × Expression.Ty) × Expression.Expr)
    (md : Imperative.MetaData Expression) : Command :=
  match trip with
  | ((v', ty), e) => .cmd (.init v' ty (.det e) md)

/-- `createInitCmd` on each of `trips`. -/
def createInitCmds (trips : List ((Expression.Ident × Expression.Ty) × Expression.Expr))
    (md : Imperative.MetaData Expression) : List Command :=
  trips.map (createInitCmd · md)

/-- A command that declares `v'` of type `ty` with the value of variable `v`, for
    `((v', ty), v)`. -/
def createInitVarCmd (trip : (Expression.Ident × Expression.Ty) × Expression.Ident)
    (md : Imperative.MetaData Expression) : Command :=
  match trip with
  | ((v', ty), v) => .cmd (.init v' ty (.det (createFvar v ty.toMonoType?)) md)

/-- `createInitVarCmd` on each of `trips`. -/
def createInitVarCmds (trips : List ((Expression.Ident × Expression.Ty) × Expression.Ident))
    (md : Imperative.MetaData Expression) : List Command :=
  trips.map (createInitVarCmd · md)

/-- `g` with `decls` at the start of its entry, where they dominate every block.
    When the entry is a branch target (a loop header), declarations there would run
    again on every iteration, so they go in a fresh entry block (labelled from
    `base`) that falls through to the old one. The block holding the declarations is
    listed first: in the concrete syntax a declaration is in scope only in the blocks
    listed after it. -/
def declareAtEntry (g : DetCFG) (decls : List Command) (base : String) : DetCFG :=
  if decls.isEmpty then g
  else if g.blocks.any fun (_, b) => b.transfer.targets.contains g.entry then
    let entry := Strata.Name.freshName (Std.HashSet.ofList g.labels) base
    { entry, blocks := (entry, { cmds := decls, transfer := .goto g.entry .empty }) :: g.blocks }
  else
    let (entryBlocks, rest) := g.blocks.partition (·.1 == g.entry)
    let entryBlocks := entryBlocks.map fun (lbl, blk) =>
      (lbl, { blk with cmds := decls ++ blk.cmds })
    { g with blocks := entryBlocks ++ rest }

/--
Generate the substitution pairs needed for the body of the procedure
-/
def createOldVarsSubst
  (trips : List ((Expression.Ident × Expression.Ty) × Expression.Ident))
  : Map Expression.Ident Expression.Expr :=
    trips.map go where go
    | ((v', ty), v) => (v, createFvar v' ty.toMonoType?)


/- Generic runner functions. -/

/-- `runStmtsRec`, also passing `f` the declared types of the variables in scope before each
    statement, starting from `vt`. -/
def runStmtsRecTyped
    (f : TypeSpec.TypeScopes → Statement → CoreTransformM (Option (List Statement)))
    (vt : TypeSpec.TypeScopes) (ss : List Statement)
    : CoreTransformM (Bool × List Statement) := do
  match ss with
  | [] => return (false, [])
  | s :: ss' =>
    -- Transform the head (and, when `f` declines, its sub-statements) before
    -- recursing into the tail, so effects of `f` — e.g. freshly generated loop
    -- numbers — follow source order.
    let (changed, sres) ← (do
      match ← f vt s with
      | .some s' => return (true, s')
      | .none =>
        match s with
        | .cmd _ => return (false, [s])
        | .block lbl b md => do
          let (changed, b') ← runStmtsRecTyped f (vt.push .empty) b
          return (changed, [.block lbl b' md])
        | .ite c thenb elseb md => do
          let (changed, thenb') ← runStmtsRecTyped f (vt.push .empty) thenb
          let (changed', elseb') ← runStmtsRecTyped f (vt.push .empty) elseb
          return (changed || changed', [.ite c thenb' elseb' md])
        | .loop guard measure invariant body md => do
          let (changed, body') ← runStmtsRecTyped f (vt.push .empty) body
          return (changed, [.loop guard measure invariant body' md])
        | .typeDecl _ _ =>
          return (false, [s])  -- Type declarations pass through unchanged
        | .exit _ _ =>
          return (false, [s]))
    let (changed0, ss'') ← (runStmtsRecTyped f (vt.addInits sres) ss')
    return ⟨changed || changed0, (sres ++ ss'')⟩

/--
Recursively visit all statements and run `f`.

For each statement `s`, `f s` is applied exactly once:
- if `f s` returns `some s'`, then `s'` replaces `s` and is not traversed
  any further. Either the top-level transform must invoke `runProgramUntil`,
  or `f` itself must process the subtree.
- if `f s` returns `none`, then `s` is left unmodified and `runStmtsRec`
  traverses into its sub-statements (block/ite/loop bodies), giving `f` a
  chance to act on nested statements.

Requirements on `f`:
- `f s` should return `.none` if it confirmed that `s` is not a target of
  its transformation. This will help `runProgramUntil` converge.
- `f s` should return `.some [s]` even if it didn't transform `s` at all,
  if it modified `factory` of `CoreTransformState`. Otherwise, the updated
  `factory` can be silently skipped by `runProgramUntil`.
- `f s` can return `.none` if the `s` wasn't transformed and `factory` wasn't
  modified, even when it modified generator or analysis cache of `CoreTransformState`.

Returned value:
- The returned boolean value is true if `f` has been applied at least once.
  It returns true even if `f s` returned an identical statement `.some [s]`,
  and didn't modify `CoreTransformState.factory`, to avoid expensive comparison.
- Then returned statement list is a concat map of `f` to the input `ss`.

NOTE: please use runProgram if possible since CoreTransformState might result
in an inconsistent state. This function is for partial implementation.
-/
def runStmtsRec (f : Statement → CoreTransformM (Option (List Statement)))
    (ss : List Statement)
    : CoreTransformM (Bool × List Statement) :=
  runStmtsRecTyped (fun _ => f) [] ss

/--
Run `f vt` on each command of each block of `g`, in the order of `g.blocks`. `vt` is passed
unchanged to every command, so callers pass the types of the variables in scope at every
command (for a CFG, the parameters plus the initializations of every block). When `f vt c`
returns `some cs`, `cs` replaces `c` in its block; when it returns `none`, `c` is kept.
Labels, transfers and branch conditions are kept: a branch condition is an expression, and holds
no command. The returned boolean is true if `f` returned `some` for at least one command.
-/
def runCFGCmdsTyped (f : TypeSpec.TypeScopes → Command → CoreTransformM (Option (List Command)))
    (vt : TypeSpec.TypeScopes) (g : DetCFG)
    : CoreTransformM (Bool × DetCFG) := do
  let mut changed := false
  let mut blocks := #[]
  for (lbl, b) in g.blocks do
    let mut cmds : Array Command := #[]
    for c in b.cmds do
      match ← f vt c with
      | some cs =>
        changed := true
        cmds := cmds ++ cs.toArray
      | none => cmds := cmds.push c
    blocks := blocks.push (lbl, { b with cmds := cmds.toList })
  return (changed, { g with blocks := blocks.toList })

/-- `runCFGCmdsTyped` with an `f` that ignores the variable types. -/
def runCFGCmds (f : Command → CoreTransformM (Option (List Command))) (g : DetCFG)
    : CoreTransformM (Bool × DetCFG) :=
  runCFGCmdsTyped (fun _ => f) [] g

/--
Run f on each statement of the program, passing it the declared types of the variables in
scope, starting from the procedure's parameters. A command of a CFG body is passed the
variables of the procedure's parameters and of every initialization in the CFG.
Returns (has the program updated?, the updated program).
If targetProcList is .none, apply f to all statements in every procedure.
If targetProcList is .some l, apply f to statements that are in procedures
listed in l only.
A CFG body is rewritten whole by `cfgBody` when it is `some k` (`k proc g` returns whether it
changed `g` and the new graph), else command by command by `cfgCmd` when it is `some h` (`h`
is run on each command of its blocks, `runCFGCmds`), with the current procedure and program set
as for a structured body; `cfgCmd` is not used when `cfgBody` is given. When both are `none`, a
CFG body in a listed procedure is an error. An abstract body has no statements and is left
unchanged.

The returned boolean is false if neither `f`, `cfgCmd` nor `cfgBody` reported a change in any
procedure of `p` that is a member of `targetProcList` (if it is `.some ..`). The requirement on
`f` is exactly equivalent to the requirement on `f` of `runStmtsRecTyped`. If the returned
boolean is `false`, the returned `Program` and `CoreTransformState.factory` are the input `p` and
that of the input state, provided each of `f`, `cfgCmd` and `cfgBody` reports a change whenever
it makes one. `runProgram` can still return `true` for a rewrite that reports a change
conservatively.
-/
def runProgramTyped
    (f : TypeSpec.TypeScopes → Statement → CoreTransformM (Option (List Statement)))
    (p : Program)
    (targetProcList : Option (List String) := .none)
    (cfgCmd : Option (TypeSpec.TypeScopes → Command → CoreTransformM (Option (List Command))) :=
      none)
    (cfgBody : Option (Procedure → DetCFG → CoreTransformM (Bool × DetCFG)) := none)
  : CoreTransformM (Bool × Program) := do
  modify (fun σ => { σ with currentProgram := .some p })

  let mut anyChanged := false
  let mut newDecls := p.decls
  for (decl, i) in p.decls.zipIdx do
    match decl with
    | .proc proc md =>
      let isTargetProc := match targetProcList with
         | .none => true
         | .some pl => proc.header.name.1 ∈ pl

      if isTargetProc then
        -- Initialize CoreTransformState
        modify (fun σ => { σ with
          currentProcedureName := .some proc.header.name.1
        })

        let (changed, newBody) ← match proc.body, cfgBody, cfgCmd with
          | .structured ss o, _, _ => do
            let (changed, ss') ← runStmtsRecTyped f (TypeSpec.procBodyScopes [] proc) ss
            pure (changed, Procedure.Body.structured ss' o)
          | .cfg g o, some k, _ => do
            let (changed, g') ← k proc g
            pure (changed, Procedure.Body.cfg g' o)
          | .cfg _ _, none, none => throw (Strata.Message.fromString
              s!"runProgram: cannot apply statement-level transform to CFG body (procedure '{proc.header.name.1}')")
          | .cfg g o, none, some h => do
            let (changed, g') ← runCFGCmdsTyped h
              ((TypeSpec.procBodyScopes [] proc).addCFGInits g) g
            pure (changed, Procedure.Body.cfg g' o)
          | .abstract, _, _ => pure (false, Procedure.Body.abstract)

        if changed then
          newDecls := newDecls.set i (Decl.proc { proc with body := newBody } md)
          anyChanged := true
          modify (fun σ => { σ with
            currentProgram := .some { p with decls := newDecls }
          })
    | _ => pure ()

  let newProg : Program := { p with decls := newDecls }
  modify (fun σ => { σ with
    currentProcedureName := .none
  })
  return (anyChanged, newProg)

/-- `runProgramTyped` with an `f` that ignores the variable types. -/
def runProgram
    (f : Statement → CoreTransformM (Option (List Statement)))
    (p : Program)
    (targetProcList : Option (List String) := .none)
    (cfgCmd : Option (Command → CoreTransformM (Option (List Command))) := none)
    (cfgBody : Option (Procedure → DetCFG → CoreTransformM (Bool × DetCFG)) := none)
  : CoreTransformM (Bool × Program) :=
  runProgramTyped (fun _ => f) p targetProcList (cfgCmd.map fun h _ => h) cfgBody

/-- Repeatedly apply a statement-level transformation until no more changes occur
    or the iteration limit is reached.
    - `maxIters = none`: repeat until a fixed point (no changes).
    - `maxIters = some n`: run up to `n` iterations, stopping early if no change.

    The requirement on `f`, the treatment of CFG bodies (`cfgCmd`) and the meaning of the
    returned boolean value are exactly those of `runProgram`.
-/
def runProgramUntilTyped
    (f : TypeSpec.TypeScopes → Statement → CoreTransformM (Option (List Statement)))
    (p : Program)
    (maxIters : Option Nat := none)
    (targetProcList : Option (List String) := .none)
    (cfgCmd : Option (TypeSpec.TypeScopes → Command → CoreTransformM (Option (List Command))) :=
      none)
  : CoreTransformM (Bool × Program) := do
  match maxIters with
  | some n =>
    let mut prog := p
    let mut anyChanged := false
    for _ in List.range n do
      let (changed, prog') ← runProgramTyped f prog targetProcList cfgCmd
      prog := prog'
      if changed then anyChanged := true
      if !changed then break
    return (anyChanged, prog)
  | none =>
    let mut prog := p
    let mut anyChanged := false
    repeat
      let (changed, prog') ← runProgramTyped f prog targetProcList cfgCmd
      prog := prog'
      if changed then anyChanged := true
      if !changed then break
    return (anyChanged, prog)

/-- `runProgramUntilTyped` with an `f` that ignores the variable types. -/
def runProgramUntil
    (f : Statement → CoreTransformM (Option (List Statement)))
    (p : Program)
    (maxIters : Option Nat := none)
    (targetProcList : Option (List String) := .none)
    (cfgCmd : Option (Command → CoreTransformM (Option (List Command))) := none)
  : CoreTransformM (Bool × Program) :=
  runProgramUntilTyped (fun _ => f) p maxIters targetProcList (cfgCmd.map fun h _ => h)

@[expose, simp]
def runWith {α : Type} (p : α) (f : α → CoreTransformM β)
    (s : CoreTransformState):
  Except Err β × CoreTransformState :=
  (StateT.run (f p) s)

@[simp]
def run {α : Type} (p : α) (f : α → CoreTransformM β)
      (s : CoreTransformState := .emp):
  Except Err β :=
  (runWith p f s).fst

end Transform

end Core

end -- public section
