/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.Languages.Core.SMTEncoder
public import Strata.DL.Lambda.RecursiveAxioms
public import Strata.Languages.Core.PipelinePhase
import Strata.Transform.UnrollBoundedQuantifiers
import Strata.Transform.BetaReduce
import Strata.Transform.CallElim
import Strata.Transform.CommonSubexprElim
import Strata.Transform.FilterProcedures
import Strata.Transform.FunctionInlining
import Strata.Transform.InsertLoopInvariantAsserts
import Strata.Transform.LoopElim
import Strata.Transform.GenOpaqueTypeParams
import Strata.Transform.MonomorphizeFunctions
import Strata.Transform.NondetElim
import Strata.Transform.PrecondElim
public import Strata.Transform.RecursiveFunctionAxioms
import Strata.Transform.TerminationCheck
import Strata.Languages.Core.ObligationExtraction
import Strata.DL.SMT.StringLit
public import Strata.Languages.Core.SMTEmitter
public import Strata.Transform.IrrelevantAxioms
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Strata.Languages.Core.DDMTransform.ASTtoCST -- shake: keep
public import Strata.Languages.Core.DDMTransform.Translate -- shake: keep
public import Strata.Languages.Core.Statistics -- shake: keep
public import Strata.Languages.Core.Env
public import Strata.Languages.Core.Options
public import Strata.Languages.Core.ProgramEval
import Strata.Languages.Core.ProgramType
import Strata.Util.Tactics

open Strata.Pipeline (PipelineContext)

/-- The names the obligation's variable definitions give a `define-fun`. -/
private def definedNameSet (varDefinitions : List Core.VarDefinition) : Std.HashSet String :=
  varDefinitions.foldl (fun s d => s.insert d.name) ∅

/-- The obligation's managed names — every define-fun/declare-fun name from its
    variable definitions and declarations — as a hash set for O(1) membership.
    Defined at the root namespace so it is visible unqualified from both the
    `Strata.SMT.Encoder` and `Core` namespaces. -/
private def managedNameSet (varDefinitions : List Core.VarDefinition)
    (varDeclarations : List Core.VarDeclaration) : Std.HashSet String :=
  varDeclarations.foldl (fun s d => s.insert d.name) (definedNameSet varDefinitions)

---------------------------------------------------------------------

namespace Strata.SMT.Encoder

open Strata.SMT.Encoder
open Strata

public section

/-- Encoder state for the abstract solver backend. Extends `EncoderState` with
    a cache of `τ` handles for declared variables, so that `encodeTerm` can
    look up handles by name instead of requiring a `mkVar` method on the solver. -/
structure AbstractEncoderState (τ : Type) where
  /-- The underlying encoder state (UF name mappings). -/
  base : EncoderState
  /-- Maps declared variable/function names to their solver handles.
      Populated by `encodeUF` / `declareFun`; looked up by `encodeTerm`. -/
  varHandles : Std.HashMap String τ := {}

/-- Encoder monad over an abstract solver backend.
    Parameterized by the underlying monad `m` and the solver's term type `τ`
    so the encoder is not tied to any particular solver backend. -/
abbrev AbstractEncoderM (τ : Type) (m : Type → Type) := StateT (AbstractEncoderState τ) m

namespace AbstractEncoder

variable {τ σ : Type} {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m]

/-- Convert a `TermType` to the solver's sort type `σ` by dispatching on
    the sort primitives provided by the solver. This is the sort-level
    counterpart of `encodeTerm`: both convert a Strata representation to a
    solver-native handle by pattern-matching on constructors. Keeping this
    logic in the encoder (rather than in `AbstractSolver`) means backends
    only need to implement the one-liner sort primitives, not a full
    dispatching method. -/
def termTypeToSort (solver : AbstractSolver τ σ m) (ty : TermType) : m σ := do
  match ty with
  | .prim .bool => solver.boolSort
  | .prim .int => solver.intSort
  | .prim .real => solver.realSort
  | .prim .string => solver.stringSort
  | .prim .regex => solver.regexSort
  | .prim (.bitvec n) => solver.bitvecSort n
  | .option inner => do
    let s ← termTypeToSort solver inner
    solver.constrSort "Option" [s]
  | .constr name args => do
    if name == "Array" then
      match args with
      | [k, v] => do
        let ks ← termTypeToSort solver k
        let vs ← termTypeToSort solver v
        solver.arraySort ks vs
      | _ => solver.constrSort name []
    else
      let argSorts ← args.attach.mapM fun ⟨t, _⟩ => termTypeToSort solver t
      solver.constrSort name argSorts
termination_by sizeOf ty
decreasing_by
  all_goals simp_wf
  all_goals (try omega) <;> (have := List.sizeOf_lt_of_mem ‹_›; omega)

/-- Allocate a globally unique SMT-LIB identifier within the abstract encoder.
    Mirrors `Encoder.uniquify` but operates on `AbstractEncoderState`. -/
private def uniquify (baseName : String) : AbstractEncoderM τ m String := do
  let id := Strata.Name.findUnique baseName 1 (← get).base.usedNames
  modify fun st => { st with base.usedNames := st.base.usedNames.insert id }
  return id

def encodeUF (solver : AbstractSolver τ σ m) (uf : UF) : AbstractEncoderM τ m String := do
  if let .some enc := (← get).base.functions.get? uf then return enc
  let id ← uniquify uf.id
  liftM (solver.comment uf.id)
  let argSorts ← uf.args.mapM (fun ty => liftM (termTypeToSort solver ty))
  let outSort ← liftM (termTypeToSort solver uf.out)
  let handle ← liftM (solver.declareFun id argSorts outSort)
  modify fun st => { st with varHandles := st.varHandles.insert id handle }
  modifyGet fun state => (id, { state with
    base.functions := state.base.functions.insert uf id
    base.isFunUninterp := state.base.isFunUninterp.insert uf true })

private def defineApp (solver : AbstractSolver τ σ m) (retSort : σ) (op : Op) (tEncs : List τ) : AbstractEncoderM τ m τ := do
  -- Pattern: `liftM` lifts solver calls from `m` into `StateT`.
  match op, tEncs with
  -- Boolean operations
  | .and, _         => liftM (solver.mkAnd tEncs)
  | .or, _          => liftM (solver.mkOr tEncs)
  | .not, [t]       => liftM (solver.mkNot t)
  | .implies, [a,b] => liftM (solver.mkImplies a b)
  | .eq, _          => liftM (solver.mkEq tEncs)
  | .ite, [c,t,f]   => liftM (solver.mkIte c t f)
  -- Arithmetic operations
  | .add, _         => liftM (solver.mkAdd tEncs)
  | .sub, _         => liftM (solver.mkSub tEncs)
  | .mul, _         => liftM (solver.mkMul tEncs)
  | .div, [a, b]    => liftM (solver.mkDiv a b)
  | .mod, [a, b]    => liftM (solver.mkMod a b)
  | .neg, [t]       => liftM (solver.mkNeg t)
  | .abs, [t]       => liftM (solver.mkAbs t)
  -- Comparison operations
  | .lt, _          => liftM (solver.mkLt tEncs)
  | .le, _          => liftM (solver.mkLe tEncs)
  | .gt, _          => liftM (solver.mkGt tEncs)
  | .ge, _          => liftM (solver.mkGe tEncs)
  -- Array operations
  | .select, [a, i]  => liftM (solver.mkSelect a i)
  | .store, [a,i,v]  => liftM (solver.mkStore a i v)
  -- Uninterpreted functions: declare and apply
  | .uf f, _ =>
    let ufName ← encodeUF solver f
    let ufRef : UF := { id := ufName, args := f.args, out := f.out }
    let outSort ← liftM (termTypeToSort solver ufRef.out)
    let handle ← liftM (solver.mkAppOp (.uf ufRef) [] outSort)
    liftM (solver.mkApp handle tEncs)
  -- Datatype operations: build handle and apply
  | .datatype_op kind name, _ =>
    let handle ← liftM (solver.mkAppOp (.datatype_op kind name) [] retSort)
    liftM (solver.mkApp handle tEncs)
  -- All other operations (bitvectors, strings, etc.): route through mkAppOp
  | _, _ => liftM (solver.mkAppOp op tEncs retSort)

private def defineQuantifierHelper (solver : AbstractSolver τ σ m) (qk : QuantifierKind)
    (args : List TermVar)
    (encodeBody : AbstractEncoderM τ m τ)
    (encodeTriggers : AbstractEncoderM τ m (List (List τ)))
    : AbstractEncoderM τ m τ := do
  let bindings ← args.mapM fun v => do
    let s ← liftM (termTypeToSort solver v.ty)
    return (v.id, s)
  let mkQuant := match qk with
    | .all => solver.mkForall
    | .exist => solver.mkExists
  -- Capture the encoder state so the callback can encode the body and
  -- triggers with the bound variable handles in scope.  The inner state
  -- is intentionally not propagated back: bound variable handles are scoped
  -- to the quantifier, and free variables in the body are already declared
  -- before the quantifier is encoded.
  let st ← get
  liftM (mkQuant bindings (fun vars => do
    let stWithVars := { st with
      varHandles := args.zip vars |>.foldl
        (fun m (v, h) => m.insert v.id h) st.varHandles }
    let (bodyEnc, st') ← encodeBody.run stWithVars
    let (trEncs, _) ← encodeTriggers.run st'
    return (bodyEnc, trEncs)))

def encodeTerm (solver : AbstractSolver τ σ m) (t : Term) : AbstractEncoderM τ m τ := do
  match t with
  | .var v =>
    -- Look up the τ handle cached when the variable was declared via declareFun/declareNew
    match (← get).varHandles.get? v.id with
    | .some handle => return handle
    | .none =>
      -- Variable not yet declared — declare it now via declareNew
      let s ← liftM (termTypeToSort solver v.ty)
      let handle ← liftM (solver.declareNew v.id s)
      modify fun st => { st with varHandles := st.varHandles.insert v.id handle }
      return handle
  | .prim p => liftM (solver.mkPrim p)
  | .none ty =>
    -- Option none: use the datatype constructor via mkAppOp
    let retSort ← liftM (termTypeToSort solver (.option ty))
    liftM (solver.mkAppOp (.datatype_op .constructor "none") [] retSort)
  | .some t₁ =>
    -- Option some: encode the inner term and apply the constructor via mkAppOp
    let t₁Enc ← encodeTerm solver t₁
    let retSort ← liftM (termTypeToSort solver (.option t₁.typeOf))
    let handle ← liftM (solver.mkAppOp (.datatype_op .constructor "some") [] retSort)
    liftM (solver.mkApp handle [t₁Enc])
  | .app .re_allchar [] .regex =>
    let s ← liftM (termTypeToSort solver .regex)
    liftM (solver.mkAppOp .re_allchar [] s)
  | .app .re_all     [] .regex =>
    let s ← liftM (termTypeToSort solver .regex)
    liftM (solver.mkAppOp .re_all [] s)
  | .app .re_none    [] .regex =>
    let s ← liftM (termTypeToSort solver .regex)
    liftM (solver.mkAppOp .re_none [] s)
  | .app .bvnego [inner] .bool =>
    match inner.typeOf with
    | .bitvec n =>
      let innerEnc ← encodeTerm solver inner
      let minVal ← liftM (solver.mkPrim (.bitvec (BitVec.intMin n)))
      let retSort ← liftM (termTypeToSort solver .bool)
      defineApp solver retSort .eq [innerEnc, minVal]
    | _ => liftM (solver.mkBool false)
  | .app op ts _ =>
    let retSort ← liftM (termTypeToSort solver t.typeOf)
    defineApp solver retSort op (← mapM₁ ts (fun ⟨tᵢ, _⟩ => encodeTerm solver tᵢ))
  | .quant qk qargs tr body =>
    defineQuantifierHelper solver qk qargs
      (encodeTerm solver body)
      (mapM₁ tr (fun ⟨ts, _⟩ => mapM₁ ts (fun ⟨ti, _⟩ => encodeTerm solver ti)))
termination_by sizeOf t
decreasing_by
  all_goals first
    | term_by_mem
    | add_mem_size_lemmas
      have h1 := List.sizeOf_lt_of_mem ‹_ ∈ tr›
      have h2 := List.sizeOf_lt_of_mem ‹_ ∈ _›
      simp_all; omega

def encodeFunctionDef (solver : AbstractSolver τ σ m) (f : IF) : AbstractEncoderM τ m String := do
  let uf := f.toUF
  if let .some enc := (← get).base.functions.get? uf then
    -- See `Strata.SMT.Encoder.encodeFunctionDef`: a function already emitted as an
    -- uninterpreted `declare-fun` (because it was referenced before its
    -- definition was reached) would silently lose its `define-fun`. Fail loudly
    -- rather than emit an unsound query.
    if ((← get).base.isFunUninterp.get? uf).getD false then
      throw (IO.userError s!"encodeFunctionDef: function '{uf.id}' was already \
                declared as uninterpreted before its definition was encoded; \
                function definitions must be ordered callee-before-caller.")
    else
      return enc
  let id ← uniquify (ufId (← get).base.functions.size)
  liftM (solver.comment uf.id)
  let argPairs ← f.args.mapM fun v => do
    let s ← liftM (termTypeToSort solver v.ty)
    return (v.id, s)
  let outSort ← liftM (termTypeToSort solver uf.out)
  -- The body is written over the parameters themselves. Left to `encodeTerm`, a parameter
  -- would be declared as a global constant, which `declareNew` renames once the name is
  -- taken, by an earlier function's parameter for instance: the body would then read that
  -- constant in place of its argument. Bindings the parameters shadow are put back after.
  let outer := (← get).varHandles
  for (v, (n, s)) in f.args.zip argPairs do
    let h ← liftM (solver.mkParam n s)
    modify fun st => { st with varHandles := st.varHandles.insert v.id h }
  let restore (m : Std.HashMap String τ) (v : TermVar) : Std.HashMap String τ :=
    match outer.get? v.id with
    | some h => m.insert v.id h
    | none => m.erase v.id
  if f.isRec then
    -- Register the name before encoding the body, so the self-call inside it
    -- encodes to `id` instead of lazily declaring an uninterpreted twin.
    modify fun state => { state with
      base.functions := state.base.functions.insert uf id
      base.isFunUninterp := state.base.isFunUninterp.insert uf false }
    let bodyEnc ← encodeTerm solver f.body
    modify fun st => { st with varHandles := f.args.foldl restore st.varHandles }
    liftM (solver.defineFunRec id argPairs outSort bodyEnc)
    return id
  let bodyEnc ← encodeTerm solver f.body
  modify fun st => { st with varHandles := f.args.foldl restore st.varHandles }
  liftM (solver.defineFun id argPairs outSort bodyEnc)
  modifyGet fun state => (id, { state with
    base.functions := state.base.functions.insert uf id
    base.isFunUninterp := state.base.isFunUninterp.insert uf false })

end AbstractEncoder

/-- Build constructor declarations for a datatype, lowering field types as the batch path does
    (`datatypeConstructorsToSMT`) and converting them through the solver's `termTypeToSort`. -/
private def datatypeConstrsM [Monad m] [MonadExceptOf IO.Error m] (solver : AbstractSolver τ σ m)
    (useArrayTheory : Bool) (d : Lambda.LDatatype Core.CoreLParams.IDMeta)
    : m (List (String × List (String × σ))) :=
  (Core.datatypeConstructorsToSMT d useArrayTheory).mapM fun c => do
    let fields ← c.args.mapM fun (name, fieldTy) => do
      pure (name, ← AbstractEncoder.termTypeToSort solver fieldTy)
    pure (c.name, fields)

/-- Emit datatype declarations through the `AbstractSolver` API. -/
def emitDatatypesAbstract [Monad m] [MonadExceptOf IO.Error m]
    (solver : AbstractSolver τ σ m) (ctx : Core.SMT.Context) : m Unit := do
  -- Validate that no datatype has arrow-typed fields (same check as batch path)
  match Core.validateDatatypesForSMT ctx.datatypes.factory ctx.seenDatatypes with
  | .error msg => throw (IO.userError (toString msg))
  | .ok () => pure ()
  for block in ctx.datatypes.factory.toList do
    let usedBlock := block.filter (fun d => ctx.seenDatatypes.contains d.name)
    match usedBlock with
    | [] => pure ()
    | [d] =>
      let constrs ← datatypeConstrsM solver ctx.useArrayTheory d
      let _ ← solver.declareDatatype d.name d.typeArgs
        fun _ _ => .ok constrs
    | _ =>
      let dtHeaders := usedBlock.map fun d => (d.name, d.typeArgs)
      let allConstrs ← usedBlock.mapM (datatypeConstrsM solver ctx.useArrayTheory)
      let _ ← solver.declareDatatypes dtHeaders
        fun _ _ => .ok allConstrs

/-- Send part of an encoding context to a solver: the given sorts, datatypes, uninterpreted
    and defined functions, and axioms, in that order: sorts come first since a datatype's
    constructors may mention them (a heap holds a `Map`). A one-shot solve sends the whole context;
    a long-lived session sends only what it has not sent before.

    A sort that `ctx` declares as a datatype is left to the datatype declaration, since strict
    solver APIs (e.g. cvc5 FFI) reject a redefinition. A function named in `managed` is a
    program variable: it is only registered here, because the caller declares or defines it
    with the rest of its path. -/
def declareContextAbstract [Monad m] [MonadExceptOf IO.Error m]
    (solver : AbstractSolver τ σ m) (ctx : Core.SMT.Context)
    (sorts : List Strata.DL.SMT.Sort) (datatypes : Std.HashSet String)
    (ufs : List UF) (ifs : List IF) (axms : List Term) (managed : Std.HashSet String) :
    AbstractEncoderM τ m Unit := do
  for s in sorts do
    if !ctx.seenDatatypes.contains s.name then
      let _ ← liftM (solver.declareSort s.name s.arity)
  if !datatypes.isEmpty then
    liftM (emitDatatypesAbstract solver { ctx with seenDatatypes := datatypes })
  for uf in ufs do
    if !managed.contains uf.id then
      let _ ← AbstractEncoder.encodeUF solver uf
  -- Registering a variable lets `encodeTerm` recognize it without declaring it.
  for uf in ufs do
    if managed.contains uf.id then
      modify fun st => { st with base := seedManagedName st.base uf }
  for fn in ifs do
    let _ ← AbstractEncoder.encodeFunctionDef solver fn
  let axmIds ← axms.mapM (AbstractEncoder.encodeTerm solver)
  for id in axmIds do
    liftM (solver.assert id)

/-- Encode declarations and assertions through the `AbstractSolver` API.
    Replaces `encodeDeclarations` for the incremental path — all commands
    go through `AbstractSolver` methods instead of `SolverM`.

    Parameterized by the solver backend monad `m` and the solver's term/sort
    types `τ`/`σ` so any implementation of `AbstractSolver τ σ m` can be used
    (e.g. incremental SMT-LIB, cvc5 FFI).

    `prelude` is a deferred monadic action (e.g. solver option settings)
    executed after `setLogic` but before declarations. The caller constructs
    it inside the solver session and passes it in as a callback. -/
def encodeDeclarationsAbstract [Monad m] [MonadExceptOf IO.Error m]
    (solver : AbstractSolver τ σ m)
    (ctx : Core.SMT.Context)
    (prelude : m Unit)
    (assumptionTerms : List Term) (obligationTerm : Term)
    (varDefinitions : List Core.VarDefinition := [])
    (varDeclarations : List Core.VarDeclaration := [])
    : m (τ × List String × EncoderState) := do
  solver.setLogic "ALL"
  prelude
  -- Pre-populate usedNames with sort/datatype names already emitted to the solver
  let initState : AbstractEncoderState τ :=
    { base := EncoderState.initWithNames ctx.preDeclaredNames }
  let managedNames := managedNameSet varDefinitions varDeclarations
  let ((), estate) ← (declareContextAbstract solver ctx ctx.sorts.toArray.toList ctx.seenDatatypes
    ctx.ufs.toArray.toList ctx.ifs.toArray.toList ctx.axms.toArray.toList managedNames).run
      initState
  -- Emit variable declarations as declareFun
  for decl in varDeclarations do
    let sort ← AbstractEncoder.termTypeToSort solver decl.ty
    let _ ← solver.declareFun decl.name [] sort
  -- Emit variable definitions as defineFun
  let estate ← varDefinitions.foldlM (init := estate) fun estate def_ => do
    let (bodyEnc, estate) ← (AbstractEncoder.encodeTerm solver def_.body) |>.run estate
    let sort ← AbstractEncoder.termTypeToSort solver def_.ty
    solver.defineFun def_.name [] sort bodyEnc
    pure estate
  let (assumptionIds, estate) ← assumptionTerms.mapM (AbstractEncoder.encodeTerm solver) |>.run estate
  for id in assumptionIds do
    solver.assert id
  let (obligationId, estate) ← (AbstractEncoder.encodeTerm solver obligationTerm) |>.run estate
  let definedNames := definedNameSet varDefinitions
  let ids := estate.base.functions.toList.filterMap fun (uf, id) =>
    if uf.args.isEmpty && Core.SMT.isReportedName definedNames uf.id then some id else none
  return (obligationId, ids, estate.base)

/-- Encode a verification condition into SMT-LIB format, including check-sat
    commands. Used by the batch pipeline. -/
def encodeCore (ctx : Core.SMT.Context) (prelude : SolverM Unit)
    (assumptionTerms : List Term) (obligationTerm : Term)
    (md : Imperative.MetaData Core.Expression)
    (satisfiabilityCheck validityCheck : Bool)
    (label : String)
    (varDefinitions : List Core.VarDefinition := [])
    (varDeclarations : List Core.VarDeclaration := [])
    (pctx : PipelineContext) :
    SolverEncodingM (List String × EncoderState) := do
  -- Phase naming convention: `build*` is the Term-to-Term rewrite pass (no SMT
  -- text produced), `write*` renders terms to SMT-LIB text and writes them.
  -- Though a `write*` phase may also rewrite in the same loop.
  let phase {α} (name : String) (action : SolverEncodingM α) : SolverEncodingM α :=
    pctx.withRepeatedPhase name action
  Solver.setLogic "ALL"
  phase "prelude" do
    prelude

  phase "writeSorts" do
    Core.SMT.writeSortsAndDatatypes ctx
  let managedNames := managedNameSet varDefinitions varDeclarations

  -- Pre-populate usedNames with sort/datatype names already emitted to the solver
  let preDeclaredNames := ctx.preDeclaredNames

  let (_, estate) ← phase "writeDeclarations" do
    (Core.SMT.writeContextDeclarations ctx managedNames).run
      (EncoderState.initWithNames preDeclaredNames)

  let (_, estate) ← phase "writeAxioms" do
    (Strata.SMT.Encoder.encodeAxioms ctx.axms.toArray).run estate
  -- Emit variable declarations as declare-fun
  phase "writeVarDecls" do
    for decl in varDeclarations do
      Solver.declareFun decl.name [] decl.ty

  -- Emit variable definitions as define-fun (macro expansions, not constraints)
  let estate ← phase "writeVarDefs" do
    varDefinitions.foldlM (init := estate) fun estate def_ => do
      let (bodyEnc, estate) ← (encodeTerm def_.body) |>.run estate
      Solver.defineFunTerm def_.name [] def_.ty bodyEnc
      pure estate

  let (assumptionIds, estate) ← phase "buildAssumptions" do
    assumptionTerms.mapM (encodeTerm) |>.run estate

  phase "writeAssumptions" do
    for id in assumptionIds do
      Solver.assert id

  let (obligationId, estate) ← phase "buildObligation" do
    (encodeTerm obligationTerm) |>.run estate

  let ids ← phase "writeObligation" do
    Core.SMT.writeCheckSatBlock obligationId obligationTerm md satisfiabilityCheck validityCheck
      label (definedNameSet varDefinitions) |>.run' estate

  return (ids, estate)

end -- public section
end Strata.SMT.Encoder

---------------------------------------------------------------------

namespace Core.SMT
open Std (ToFormat Format format)
open Lambda Strata.SMT

public section

/-- Replace characters that are problematic on common filesystems
    (parens, quotes, spaces, path separators, and Windows-invalid characters
    such as `< > : | ? *`) with underscores or remove them.
    Single-pass over the string. -/
def sanitizeFilename (s : String) : String :=
  String.ofList <| s.toList.filterMap fun c =>
    if c == '"' || c == '\'' then none
    else if c == '(' || c == ')' || c == ' ' || c == '/' || c == '\\'
         || c == '<' || c == '>' || c == ':' || c == '|' || c == '?' || c == '*' then some '_'
    else some c

/-- Filesystem-safe filename component derived from an obligation label.
    First sanitizes illegal characters, then caps length: labels within
    `maxLen` pass through unchanged; longer ones are truncated to `maxLen`
    characters with a hex hash of the *full* label appended, so generated
    filenames stay within `NAME_MAX` while remaining unique and stable per
    label. Used only for filename derivation, never for report text. -/
def sanitizeFilenameCapped (s : String) (maxLen : Nat := 128) : String :=
  let sanitized := sanitizeFilename s
  if sanitized.length ≤ maxLen then sanitized
  else
    let hexHash := String.ofList (Nat.toDigits 16 (hash s).toNat)
    String.ofList (sanitized.toList.take maxLen) ++ "_" ++ hexHash

/-- Map a Core typed identifier to its SMT name and sort. -/
def typedVarToSMTFn (ctx : SMT.Context) (id : Core.Expression.Ident)
  (ty : Core.Expression.Ty) := do
    -- Type of identifier has to be monotye
    let some mty := LTy.toMonoType? ty | .error s!"not monotype: {id}"
    let (ty', _) ← LMonoTy.toSMTType mty ctx
    return (id.name, ty')

abbrev Result := Imperative.SMT.Result (Core.Expression.Ident)

/-- The `set-option`s every solver starts from. -/
def solverPreludeOptions (solver : String) (solverOptions : Array (String × String)) :
    Array (String × String) :=
  -- These options are set by the standard Boogie implementation and are
  -- generally good for the Boogie dialect, too, though we may want to
  -- have more fine-grained criteria for when to use them.
  let tuning := match solver with
    | "z3" => #[("smt.mbqi", "false"), ("auto_config", "false")]
    | _ => #[]
  -- Apply caller-supplied `--set-option NAME=VALUE`s last, so they override the
  -- built-in prelude (e.g. `--set-option smt.mbqi=true` for quantified lemmas).
  tuning ++ solverOptions

def setSolverPrelude (solver : String) (solverOptions : Array (String × String)) :
    SolverM Unit := do
  (solverPreludeOptions solver solverOptions).forM fun (name, value) => Solver.setOption name value

@[deprecated setSolverPrelude (since := "2026-10-27")]
abbrev getSolverPrelude := @setSolverPrelude

def getSolverFlags (options : VerifyOptions) : Array String :=
  let produceModels :=
    match options.solver with
    | "cvc5" => #["--produce-models"]
    -- No need to specify -model for Z3 because we already have `get-value`
    -- in the generated SMT file.
    | _ => #[]
  let setTimeout :=
    match options.solver with
    | "cvc5" => #[s!"--tlimit={options.solverTimeout*1000}"]
    | "z3" => #[s!"-T:{options.solverTimeout}"]
    | _ => #[]
  produceModels ++ setTimeout

/-- How a live solver is started for `--incremental`, and what it is told once started. The tree
    walk and the one-shot incremental discharge both start their solvers from this, so a goal
    gets the same time limit, and an `unknown` at that limit the same reading, whichever of the two
    sends it. -/
structure IncrementalLaunch where
  /-- The command-line flags. -/
  flags : Array String
  /-- The `set-option`s sent after the solver starts, and again after every `(reset)`. -/
  prelude : Array (String × String)
  /-- The limit, in milliseconds, at which a check's `unknown` reads as a timeout; 0 for never. -/
  timeLimitMs : Nat

/-- Launch flags per backend for a live solver. Model generation is requested on the command line,
    because a session resets its solver to cross to a branch it cannot extend, and `(reset)`
    clears options while launch flags survive it. Without it cvc5 answers `(get-model)` with
    "cannot get model unless model generation is enabled"; z3 produces models by default.

    The timeout is per check: cvc5's `--tlimit` and z3's `-T` bound a whole run, which for a
    session shared by many checks would make a later check fail for having been preceded by others,
    so the verdict would depend on how many goals its worker happened to take. An obligation that
    asks both checks, satisfiability and validity, so gets up to twice `--solver-timeout` here,
    where the path that writes the query to a file gives both together one limit.

    A solver started with a per-check limit (cvc5 and z3) keeps that limit as a bound. The user's
    own time option for that solver replaces it, so only the last such value is sent, and only when
    it is a positive number below the limit; the limit is sent in its place otherwise. A smaller
    user limit makes the solver give up first, so its `unknown` stands as on the per-obligation
    path; otherwise an `unknown` at the limit is a timeout. Without a limit (`--solver-timeout 0`)
    the user's options are sent as given. -/
def incrementalLaunch (options : VerifyOptions) : IncrementalLaunch :=
  let limitMs := options.solverTimeout * 1000
  let flags := match options.solver with
    | "cvc5" =>
      #["--quiet", "--lang", "smt", "--incremental", "--produce-models", s!"--tlimit-per={limitMs}"]
    | "z3" => #["-in", s!"-t:{limitMs}"]
    | _ => #[]
  let timeKey : Option String := match options.solver with
    | "z3" => some "timeout" | "cvc5" => some "tlimit-per" | _ => none
  let (userOptions, ownLimit) := match timeKey with
    | some key =>
      if limitMs == 0 then (options.solverOptions, true) else
      let opts : Array (String × String) := options.solverOptions
      let given : Option (Option Nat) :=
        (opts.filter (fun (p : String × String) => p.1 == key)).back?.map
          fun (p : String × String) => p.2.trimAscii.toString.toNat?
      let mine : Option Nat := given.bind fun v => v.filter fun n => 0 < n && n < limitMs
      let rest := opts.filter (fun (p : String × String) => p.1 != key)
      match given, mine with
      | none, _ => (rest, false)
      | some _, some n => (rest.push (key, toString n), true)
      | some _, none => (rest.push (key, toString limitMs), false)
    | none => (options.solverOptions, true)
  { flags, prelude := solverPreludeOptions options.solver userOptions,
    timeLimitMs := if ownLimit then 0 else limitMs }

def dischargeObligation
  (options : VerifyOptions)
  (vars : List Expression.TypedIdent)
  (md : Imperative.MetaData Expression)
  (filename : String)
  (assumptionTerms : List Term)
  (obligationTerm : Term)
  (ctx : SMT.Context)
  (satisfiabilityCheck validityCheck : Bool)
  (label : String)
  (varDefinitions : List VarDefinition := [])
  (varDeclarations : List VarDeclaration := [])
  (termCache : Option (IO.Ref (Std.HashMap Term String)) := none)
  (captured : Option Core.SMT.Emitter.CapturedFile := none)
  (pctx : PipelineContext)
  : IO (Except Imperative.SMT.SolverError (SMT.Result × SMT.Result × EncoderState)) := do
  -- CVC5 requires --incremental for multiple (check-sat) commands
  let baseFlags := getSolverFlags options
  let needsIncremental := satisfiabilityCheck && validityCheck
  let solverFlags :=
    if needsIncremental && options.solver == "cvc5" && !baseFlags.contains "--incremental" then
      baseFlags ++ #["--incremental"]
    else
      baseFlags
  -- With a pre-assembled file (env-scoped capture), writing it is the
  -- encoding; its `ids`/`estate` keep result parsing unchanged.
  let encodeAct : SolverEncodingM (List String × EncoderState) :=
    match captured with
    | some cf => do
      Core.SMT.Emitter.emitPrerendered cf.pieces
      pure (cf.ids, cf.estate)
    | none =>
      Strata.SMT.Encoder.encodeCore ctx (setSolverPrelude options.solver options.solverOptions)
        assumptionTerms obligationTerm md satisfiabilityCheck validityCheck
        (label := label) (varDefinitions := varDefinitions) (varDeclarations := varDeclarations)
        (pctx := pctx)
  Imperative.SMT.dischargeObligation
    (P := Core.Expression)
    encodeAct
    (typedVarToSMTFn ctx)
    vars
    options.solver
    filename
    solverFlags (options.verbose > .normal)
    satisfiabilityCheck validityCheck
    (skipSolver := options.skipSolver)
    (termCache := termCache)
    (pctx := pctx)

/-- Discharge a proof obligation using the incremental solver backend.
    Spawns a live solver process, sends commands via stdin/stdout, and
    reads results interactively. Returns the same result triple as the
    batch `dischargeObligation`. -/
def dischargeObligationIncremental
  (options : VerifyOptions)
  (vars : List Expression.TypedIdent)
  (_md : Imperative.MetaData Expression)
  (assumptionTerms : List Term)
  (obligationTerm : Term)
  (ctx : SMT.Context)
  (satisfiabilityCheck validityCheck : Bool)
  (_label : String)
  (varDefinitions : List VarDefinition := [])
  (varDeclarations : List VarDeclaration := [])
  : IO (Except Imperative.SMT.SolverError (SMT.Result × SMT.Result × EncoderState)) := do
  let launch := incrementalLaunch options
  let encodeDecl (solver : Strata.SMT.AbstractSolver Term TermType
                            Strata.SMT.IncrementalEncodingM) :
      Strata.SMT.IncrementalEncodingM Imperative.SMT.EncodedObligation := do
    let prelude : Strata.SMT.IncrementalEncodingM Unit :=
      launch.prelude.forM fun (name, value) => solver.setOption name value
    let (obligationId, ids, estate) ←
      _root_.Strata.SMT.Encoder.encodeDeclarationsAbstract solver ctx prelude
        assumptionTerms obligationTerm
        (varDefinitions := varDefinitions) (varDeclarations := varDeclarations)
    return { obligationId, assumptionIds := ids, estate }
  Imperative.SMT.dischargeObligationIncremental (P := Core.Expression)
    encodeDecl (typedVarToSMTFn ctx) vars options.solver launch.flags
    satisfiabilityCheck validityCheck (timeLimitMs := launch.timeLimitMs)

end -- public section
end Core.SMT
---------------------------------------------------------------------

namespace Core
open Imperative Lambda Strata.SMT
open Std (ToFormat Format format)
open Strata

public section

def typeCheck (options : VerifyOptions) (program : Program)
    (factory : Lambda.Factory CoreLParams := Core.Factory) :
    Except Message Program := do
  let T := Lambda.TEnv.default
  -- Callers past `MonomorphizeFunctions` pass the transformed factory (poly
  -- Factory originals dropped, specialized copies added) rather than the default.
  let C := { Lambda.LContext.default with
                functions := factory,
                knownTypes := Core.KnownTypes }
  match Factory.typeCheck C T with
  | .error k =>
    -- TODO: Message for functions defined in Factory?
    throw (Message.fromFormat k)
  | .ok T =>
    let (program, _T) ← Program.typeCheck C T program
    -- dbg_trace f!"[Strata.Core] Annotated program:\n{program}"
    if options.verbose >= .normal then dbg_trace f!"[Strata.Core] Type checking succeeded.\n"
    return program

def formatProofObligation (ob : Imperative.ProofObligation Expression) :
    Std.Format :=
  let flatEntries := ob.assumptions.flatten
  let assumptionFmt := flatEntries.filterMap fun
    | .assumption label expr => some f!"{label}: {Core.formatExprs [expr]}"
    | _ => none
  let assumptionLine := if assumptionFmt.isEmpty then f!""
                        else f!"\nAssumptions:\n{Std.Format.joinSep assumptionFmt "\n"}"
  f!"Label: {ob.label}\n\
     Property: {ob.property}{assumptionLine}\n\
     Obligation:\n{Core.formatExprs [ob.obligation]}\n"

def formatProofObligations (obs : Array (Imperative.ProofObligation Expression)) :
    Std.Format :=
  Std.Format.joinSep (obs.toList.map formatProofObligation) "\n"

/-- Build an evaluation environment from a program.
    Loads the factory, datatypes, and processes all declarations.
    When `registerCustomFunctions` is true, also loads function declarations
    and distinct constraints into the factory (needed for SMT encoding). -/
def buildEnv (options : VerifyOptions) (program : Program)
    (factory : Lambda.Factory CoreLParams)
    (registerCustomFunctions : Bool := false) :
    Except Message (Env × Statistics) := do
  let σ ← (Lambda.LState.init).addFactory factory
  let datatypes := program.decls.filterMap fun decl =>
    match decl with | .type (.data d) _ => some d | _ => none
  let mut E : Env := { Env.init with exprEnv := σ, program := program, pathCap := options.pathCap }
  E ← E.addDatatypes datatypes

  if registerCustomFunctions then
    for decl in program.decls do
      match decl with
      | .func func _ => E ← E.addFactoryFunc func.toLFunc
      | .recFuncBlock funcs _ =>
        validateCasesTypes funcs E.datatypes
        for func in funcs do E ← E.addFactoryFunc func.toLFunc
      | .distinct _ es _ => E := { E with distinct := es :: E.distinct }
      | _ => pure ()

  -- Collect declaration statistics
  let stats := program.decls.foldl (fun s d =>
    match d with
    | .type _ _          => s.increment s!"{Evaluator.Stats.typeDecls}"
    | .ax _ _            => s.increment s!"{Evaluator.Stats.axioms}"
    | .lemma _ _         => s.increment s!"{Evaluator.Stats.lemmas}"
    | .distinct _ _ _    => s.increment s!"{Evaluator.Stats.distincts}"
    | .proc _ _          => s.increment s!"{Evaluator.Stats.procedures}"
    | .func _ _          => s.increment s!"{Evaluator.Stats.functions}"
    | .recFuncBlock fs _ => s.increment s!"{Evaluator.Stats.recursiveFunctions}" fs.length)
    ({} : Statistics)
  let stats := stats.increment s!"{Evaluator.Stats.factoryOps}" factory.toArray.size
  return (E, stats)

/-- Proof obligation program construction: Program → Program.
    Runs symbolic execution and converts obligations to a program
    suitable for downstream phases (CSE, SMT encoding). -/
def toCoreProofObligationProgram (options : VerifyOptions) (program : Program)
    (moreFns : Lambda.Factory CoreLParams := Lambda.Factory.default) :
    Except Message (Program × Statistics) := do
  let factory ← Core.Factory.addFactory moreFns
  -- Precondition: nondeterministic `if *` / `while *` guards must have been
  -- eliminated (by `nondetElim`) first. `Core.Statement.eval` rejects such a
  -- guard per-path, but `Program.eval` isolates per-procedure `Env.error`, so
  -- that rejection would not surface here and its path's obligations would be
  -- dropped silently. Check the input structurally and fail loudly instead.
  match program.decls.findSome? (fun d => match d with
    | .proc proc _ => (match proc.body with
        | .structured ss => if Imperative.Block.noNondetGuards ss then none else some proc.header.name.1
        | .cfg _ => none)
    | _ => none) with
  | some name => throw (Message.fromString
      s!"toCoreProofObligationProgram: procedure '{name}' contains a \
         nondeterministic if/loop guard; run nondetElim before symbolic evaluation.")
  | none => pure ()
  -- Symbolic evaluation gets both the factory and the program without the unconditional
  -- `inline` attribute, so expanding such a call is the Simplify phase's decision.
  --
  -- `inline` is kept on a function whose expansion is the only thing that removes a lambda,
  -- since SMT cannot encode one. Pruning the program matters as much as pruning the factory:
  -- `Program.eval` registers each function it walks, so a declaration's attribute would
  -- otherwise reach the evaluator untouched.
  let carriers := Core.Simplify.lambdaCarriers program
  let evalFactory := Core.Simplify.withoutInline carriers factory
  let evalProgram := Core.Simplify.withoutInlineProgramWith carriers program
  let (E, declStats) ← buildEnv options evalProgram evalFactory
  let (pEs, evalStats) ← Program.eval E
  -- Note: all .program fields in pEs will have identical values, because
  -- Program.eval does not modify the program. The Program field is
  -- kept for convenience.
  let stats := declStats.merge evalStats
  let stats := stats.increment s!"{Evaluator.Stats.verificationEnvironments}" pEs.length

  -- Convert the evaluation Env's deferred obligations into a procedure body.
  -- Program.eval accumulates all procedures into a single Env, so pEs
  -- is always a single-element list. We extract the single Env and build
  -- one obligation procedure containing all deferred obligations.
  -- Type/datatype declarations come from the original program.
  let typeDecls := program.decls.filter fun d =>
    match d with | .type _ _ => true | _ => false
  let postEvalEnv ← match pEs with
    | [e] => pure e
    | _ => throw (Message.fromString s!"toCoreProofObligationProgram: expected exactly 1 evaluation Env, got {pEs.length}")
  -- The procedure name is only used for the obligation procedure header;
  -- downstream phases (ObligationExtraction) walk the body and ignore it.
  -- We pick the first procedure name as a representative label, or the first
  -- lemma name when a program has lemmas but no procedure.
  let procName := program.decls.findSome? fun
    | .proc p _ => some p.header.name | _ => none
  let procName := procName <|> program.decls.findSome? fun
    | .lemma l _ => some (⟨l.name, ()⟩ : CoreIdent) | _ => none
  let blocks := postEvalEnv.deferred.toList.map fun ob =>
    let assumes := ob.assumptions.reverse.flatten.filterMap fun
      | .assumption label e =>
        some (Imperative.Stmt.cmd (CmdExt.cmd (Imperative.Cmd.assume label e ob.metadata)))
      | _ => none
    let assertStmt := Imperative.Stmt.cmd (CmdExt.cmd (
      if ob.property == .cover
      then Imperative.Cmd.cover ob.label ob.obligation ob.metadata
      else Imperative.Cmd.assert ob.label ob.obligation ob.metadata))
    assumes ++ [assertStmt]
  let body := match blocks with
    | [] => []
    | [b] => b
    | b :: rest => rest.foldl (fun acc block =>
        [Imperative.Stmt.ite .nondet acc block .empty]) b
  let oblProcs := match procName with
    | some name => [Decl.proc {
        header := { name := name, typeArgs := [], inputs := [], outputs := [] },
        spec := { preconditions := [], postconditions := [] },
        body := .structured body
      } .empty]
    | none => []

  -- Include function declarations and distinct constraints from the
  -- evaluation environment so the obligations program is self-contained
  -- for downstream phases (CSE, SMT encoding).
  -- Get functions added during evaluation (not in the initial factory)
  let initialFactorySize := E.exprEnv.config.factory.toArray.size
  let evalFuncs := postEvalEnv.exprEnv.config.factory.toArray.toList.drop initialFactorySize
  -- Pre-compute per-constructor axioms for recursive `@[cases]` functions so
  -- the SMT encoder can consume them directly (via `func.axioms`) instead of
  -- regenerating them on the fly with an expression evaluator.
  -- With `recursiveFnsAsDefineFunRec` the definition itself is emitted, so
  -- the per-constructor axioms are not generated.
  let evalFuncs ← if options.recursiveFnsAsDefineFunRec then pure evalFuncs else
    evalFuncs.mapM (generateRecursiveAxioms postEvalEnv.datatypes postEvalEnv.exprEval)
  -- `.toFunc` drops only `concreteEval`; all other data survives into the
  -- obligation program and the SMT factory built by `buildEnv`.
  --
  -- Attributes come from the program as written, not from the pruned copy symbolic
  -- evaluation walked: withholding `inline` governs how this function evaluates, and
  -- a program it emits should still describe the declarations the input had.
  let declaredAttrs := program.funcAttrs
  let funcDecls := evalFuncs.map fun func =>
    let f := func.toFunc
    match declaredAttrs[f.name.name]? with
    | some attr => Decl.func { f with attr := attr } .empty
    | none => Decl.func f .empty
  let distinctDecls := postEvalEnv.distinct.mapIdx fun i es =>
    Decl.distinct s!"distinct_{i}" es .empty
  let oblProgram : Program := { decls := typeDecls ++ funcDecls ++ distinctDecls ++ oblProcs }

  if options.verbose >= .normal then do
    dbg_trace f!"{Std.Format.line}VCs:"
    dbg_trace f!"{formatProofObligations postEvalEnv.deferred}"
  return (oblProgram, stats)


/-- Convenience: type check then build obligation program. -/
def typeCheckAndBuildObligationProgram (options : VerifyOptions) (program : Program)
    (moreFns : Lambda.Factory CoreLParams := Lambda.Factory.default) :
    Except Message (Program × Statistics) := do
  let factory ← Core.Factory.addFactory moreFns
  let program ← typeCheck options program factory
  toCoreProofObligationProgram options program moreFns

/-- Convenience: type check then symbolic eval. Returns the list of
    evaluation environments and statistics. -/
def typeCheckAndEval (options : VerifyOptions) (program : Program)
    (moreFns : Lambda.Factory CoreLParams := Lambda.Factory.default) :
    Except Message ((List Env) × Statistics) := do
  let factory ← Core.Factory.addFactory moreFns
  let program ← typeCheck options program factory
  let (E, declStats) ← buildEnv options program factory
  let (pEs, evalStats) ← Program.eval E
  let stats := declStats.merge evalStats
  let stats := stats.increment s!"{Evaluator.Stats.verificationEnvironments}" pEs.length
  return (pEs, stats)

/-- A solver log entry recording the SMT result after a specific pipeline phase. -/
structure SolverPhaseLog where
  /-- Name of the pipeline phase that produced this entry. -/
  phase : String
  /-- The SMT result after this phase's validation. -/
  result : SMT.Result
  deriving Repr, BEq

/-- Validate a model against all phases for a given obligation. Phases are
    recorded top-down, so we reverse them to validate from the last
    (innermost) phase first. Returns the adjusted result and a log of
    intermediate results per phase, ordered outermost-first (deepest phase
    closest to SMT at the end).

    Each phase independently validates the model when it has a validator.
    A phase with `modelToValidate` can demote `.sat m` to `.unknown (some m)`
    (when the model fails validation) or promote `.unknown (some m)` back to
    `.sat m` (when the model passes validation against the pre-phase
    semantics). This means phases are not cascading — each validating
    phase makes its own decision based on the model. -/
def AbstractedPhase.validateModel (phases : List AbstractedPhase)
    (result : SMT.Result)
    (obligation : ProofObligation Expression)
    : SMT.Result × List SolverPhaseLog :=
  -- Process phases innermost-first; accumulate log entries in reverse
  let (finalResult, revLog) := phases.reverse.foldl (init := (result, [])) fun (r, log) p =>
    let validation := p.getValidation obligation
    let r' := match r, validation with
      | .sat m, .modelToValidate f => if f m then .sat m else .unknown (some m)
      | .unknown (some m), .modelToValidate f => if f m then .sat m else .unknown (some m)
      -- .unknown none or .modelPreserving: pass through unchanged
      | _, _ => r
    (r', { phase := p.name, result := r' } :: log)
  -- Reverse log so outermost is first, deepest is last
  (finalResult, revLog.reverse)

/--
Analysis outcome of a verification condition based on two SMT queries:
  - satisfiabilityProperty: result of checking P ∧ Q  (is the property satisfiable given the path condition?)
  - validityProperty:       result of checking P ∧ ¬Q (can the property be false given the path condition?)

The 9 possible outcomes and their interpretations.
For cover statements, any outcome where P ∧ Q is sat displays as ✅ (cover satisfied).
Unreachable covers display as ❌ (error) instead of ⛔ (warning).

  Emoji  Label                                          P ∧ Q    P ∧ ¬Q   Reachable  Deductive  BugFinding  BugFinding+Complete  Meaning
  -----  ---------------------------------------------  -------  -------  ---------  ---------  ----------  -------------------  -------
  ✅     always true and is reachable                   sat      unsat    yes        pass       pass        pass                 Property always true, reachable from declaration entry
  ❌     always false and is reachable                  unsat    sat      yes        error      error       error                Property always false, reachable from declaration entry
  🔶     can be both true and false and is reachable    sat      sat      yes        error      note        error                Reachable, solver found models for both the property and its negation
  ⛔     unreachable in this context                    unsat    unsat    no         warning    error       error                Dead code, unreachable in this context
  ➕     can be true and is reachable                   sat      unknown  yes        error      note        note                 Property can be true and is reachable, unknown if always true
  ✖️     always false if reached                        unsat    unknown  unknown    error      error       error                Property always false if reached, unknown if reachable
  ➖     can be false and is reachable                  unknown  sat      yes        error      note        error                Property can be false and is reachable, unknown if always false
  ✔️     always true if reached                         unknown  unsat    unknown    pass       pass        pass                 Property always true if reached, unknown if reachable
  ❓     unknown                                        unknown  unknown  unknown    error      note        note                 Both checks inconclusive
-/
structure VCOutcome where
  satisfiabilityProperty : SMT.Result
  validityProperty : SMT.Result
  /-- Ordered log of solver results per path. Each inner array is one path's
      log: the raw solver results followed by per-phase adjusted results
      (e.g. sat→unknown when a phase cannot validate the model).
      When outcomes from multiple paths are merged, each path's log is
      preserved as a separate entry in the outer array. Consumed by future
      diagnostic and traceability tooling. -/
  solverLog : Array (Array SolverPhaseLog) := #[]
  /-- When this outcome was produced by merging multiple paths, stores the
      pre-merge per-path outcomes. Empty for unmerged (single-path) results.
      Used by the rendering phase to compute per-path classification summaries
      without storing rendering-mode-dependent strings. -/
  mergedFrom : Array VCOutcome := #[]
  /-- Set when `directed` pruning dropped axioms from the query; a `sat` then
      reports as `unknown`, see `VCOutcome.withAxiomsDropped`. -/
  axiomsDropped : Bool := false
  deriving Repr

instance : Inhabited VCOutcome where
  default := { satisfiabilityProperty := .unknown, validityProperty := .unknown }

namespace VCOutcome

-- Nine base outcome cases (one per combination)

def passAndReachable (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .sat _, .unsat => true
  | _, _ => false

def alwaysFalseAndReachable (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .unsat, .sat _ => true
  | _, _ => false

def canBeTrueOrFalseAndIsReachable (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .sat _, .sat _ => true
  | _, _ => false

def unreachable (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .unsat, .unsat => true
  | _, _ => false

def satisfiableValidityUnknown (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .sat _, .unknown _ => true
  | _, _ => false

def alwaysFalseReachabilityUnknown (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .unsat, .unknown _ => true
  | _, _ => false

def canBeFalseAndIsReachable (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .unknown _, .sat _ => true
  | _, _ => false

def passReachabilityUnknown (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .unknown _, .unsat => true
  | _, _ => false

def unknown (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .unknown _, .unknown _ => true
  | _, _ => false

/-- True when either SMT property is `.err` (solver returned an error on
    a specific check, as opposed to the outer `VCResult.outcome` being
    `.error` due to an encoding failure). -/
def hasSMTError (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .err _, _ | _, .err _ => true
  | _,      _             => false

-- Derived predicates (cross-cutting, mode-agnostic building blocks)

/-- The assertion's validity is proven (validity = unsat). True for `passAndReachable`,
    `unreachable`, and `passReachabilityUnknown`. Note: this does NOT distinguish
    reachable passes from unreachable (dead-code) passes. -/
def isPass (o : VCOutcome) : Bool :=
  match o.validityProperty with
  | .unsat => true
  | _ => false

/-- The assertion can be true (satisfiability = sat). True for `passAndReachable`,
    `canBeTrueOrFalseAndIsReachable`, and `satisfiableValidityUnknown`. -/
def isSatisfiable (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty with
  | .sat _ => true
  | _ => false

def isAlwaysFalse (o : VCOutcome) : Bool :=
  o.alwaysFalseAndReachable || o.alwaysFalseReachabilityUnknown

def isAlwaysTrue (o : VCOutcome) : Bool :=
  o.isPass

def isReachable (o : VCOutcome) : Bool :=
  o.passAndReachable || o.alwaysFalseAndReachable || o.canBeTrueOrFalseAndIsReachable

-- Mode-specific success/failure predicates

/-- Success in bug-finding mode: the assertion is satisfiable (can be true on some
    reachable path), or provably always true with unknown reachability. Does NOT
    include unreachable paths — dead code in agent-generated code is worth flagging
    as a potential issue. -/
def bugFindingSuccess (o : VCOutcome) : Bool :=
  o.isSatisfiable || o.passReachabilityUnknown

/-- Failure in bug-finding mode: the assertion is always false (a definite bug),
    or the path is unreachable (dead code). -/
def bugFindingFailure (o : VCOutcome) : Bool :=
  o.alwaysFalseAndReachable || o.alwaysFalseReachabilityUnknown || o.unreachable

-- Backward compatibility aliases (old names with "is" prefix)
def isPassAndReachable := passAndReachable
def isRefutedAndReachable := alwaysFalseAndReachable
def isCanBeTrueOrFalseAndIsReachable := canBeTrueOrFalseAndIsReachable
def isUnreachable := unreachable
def isSatisfiableValidityUnknown := satisfiableValidityUnknown
def isAlwaysFalseReachabilityUnknown := alwaysFalseReachabilityUnknown
def isCanBeFalseAndReachable := canBeFalseAndIsReachable
def isPassReachabilityUnknown := passReachabilityUnknown
def isUnknown := unknown
def isRefuted := alwaysFalseAndReachable
def isRefutedIfReachable := alwaysFalseReachabilityUnknown
def isCanBeTrueOrFalse := canBeTrueOrFalseAndIsReachable
def isAlwaysTrueIfReachable := passReachabilityUnknown
def isPassIfReachable := passReachabilityUnknown
def isAlwaysFalseIfReachable := alwaysFalseReachabilityUnknown
def isReachableAndCanBeFalse := canBeFalseAndIsReachable

/-- Select the pass or fail message based on check mode and property type.
    In deductive mode, unreachable paths pass or fail depending on the property;
    in other modes, unreachable always fails. -/
private def unreachableMsg (checkMode : VerificationMode) (passWhenUnreachable : Bool)
    (passMsg failMsg : α) : α :=
  if checkMode.isDeductive && passWhenUnreachable then passMsg else failMsg

def label (o : VCOutcome) (property : Imperative.PropertyType)
    (checkLevel : CheckLevel) (checkMode : VerificationMode) : String :=
  -- Unreachable is detected when both checks ran (via fullCheck annotation or full level)
  if o.unreachable then
    unreachableMsg checkMode property.passWhenUnreachable
      "pass (❗unreachable in this context)" "fail (❗unreachable in this context)"
  -- Simplified labels for minimal check level
  else if checkLevel == .minimal then
    if property.passWhenUnreachable then
      -- Assert-like property (i.e. passes vacuously on unreachable paths).
      if checkMode.isDeductive then
        match o.validityProperty with
        | .unsat => "pass"
        | .sat _ => "fail"
        | .unknown _ | .err _ => "unknown"
      else if checkMode == .bugFinding then
        -- `bugFinding` runs the satisfiability check only (see the check
        -- selection at `verifySingleEnv`), so matching on
        -- `satisfiabilityProperty` had no case that could report a
        -- non-bug: every goal came out `satisfiable` or `unknown` and was
        -- then counted as failed. Classify with the mode-aware predicates
        -- instead. `bugFindingAssumingCompleteSpec` runs both checks and
        -- keeps its existing labels, because `bugFindingSuccess` encodes
        -- only the `bugFinding` column of docs/VerificationModes.md.
        if o.bugFindingFailure then "fail"
        else if o.bugFindingSuccess then "no definite bug"
        else "unknown"
      else
        match o.satisfiabilityProperty with
        | .sat _ => "satisfiable"
        | .unsat => "fail"
        | .unknown _ | .err _ => "unknown"
    else
      -- Cover property
      match o.satisfiabilityProperty with
      | .sat _ => "pass"
      | .unsat => "fail"
      | .unknown _ | .err _ => "unknown"
  else
    -- For cover: satisfiability sat means the cover is satisfied (pass)
    if property == .cover && o.isSatisfiable then "satisfiable and reachable from declaration entry"
    else if o.passAndReachable then "always true and is reachable from declaration entry"
    else if o.alwaysFalseAndReachable then "always false and is reachable from declaration entry"
    else if o.canBeTrueOrFalseAndIsReachable then "can be both true and false and is reachable from declaration entry"
    else if o.satisfiableValidityUnknown then "can be true and is reachable from declaration entry"
    else if o.alwaysFalseReachabilityUnknown then "always false if reached"
    else if o.canBeFalseAndIsReachable then "can be false and is reachable from declaration entry"
    else if o.passReachabilityUnknown then "always true if reached"
    else "unknown"

def emoji (o : VCOutcome) (property : Imperative.PropertyType)
    (checkLevel : CheckLevel) (checkMode : VerificationMode) : String :=
  -- Unreachable is detected when both checks ran
  if o.unreachable then
    unreachableMsg checkMode property.passWhenUnreachable "✅" "❌"
  -- Simplified emojis for minimal check level
  else if checkLevel == .minimal then
    if property.passWhenUnreachable then
      if checkMode.isDeductive then
        match o.validityProperty with
        | .unsat => "✅"
        | .sat _ => "❌"
        | .unknown _ | .err _ => "❓"
      else if checkMode == .bugFinding then
        -- See the matching comment in `label` above.
        if o.bugFindingFailure then "❌"
        else if o.bugFindingSuccess then "✅"
        else "❓"
      else
        match o.satisfiabilityProperty with
        | .sat _ => "❓"
        | .unsat => "❌"
        | .unknown _ | .err _ => "❓"
    else
      match o.satisfiabilityProperty with
      | .sat _ => "✅"
      | .unsat => "❌"
      | .unknown _ | .err _ => "❓"
  -- MinimalVerbose and Full: detailed emojis
  else
    if property == .cover && o.isSatisfiable then "✅"
    else if o.passAndReachable then "✅"
    else if o.alwaysFalseAndReachable then "❌"
    else if o.canBeTrueOrFalseAndIsReachable then "🔶"
    else if o.satisfiableValidityUnknown then "➕"
    else if o.alwaysFalseReachabilityUnknown then "✖️"
    else if o.canBeFalseAndIsReachable then "➖"
    else if o.passReachabilityUnknown then "✔️"
    else "❓"

/-- Compute a per-path classification summary for a merged outcome.
    Returns a parenthesized string like "(always true if reached on 1 path,
    always false if reached on 1 path)" when the merged result differs from
    individual paths. Returns the empty string for unmerged results or when
    all paths have the same classification as the merged result. -/
def pathSummary (o : VCOutcome) (property : Imperative.PropertyType)
    (checkLevel : CheckLevel) (checkMode : VerificationMode) : String :=
  if o.mergedFrom.isEmpty then ""
  else
    let mergedLabel := o.label property checkLevel checkMode
    -- Count per-path classifications
    let counts := o.mergedFrom.foldl (init := Std.HashMap.emptyWithCapacity (α := String) (β := Nat))
      fun acc pathOutcome =>
        let pathLabel := pathOutcome.label property checkLevel checkMode
        acc.insert pathLabel ((acc.getD pathLabel 0) + 1)
    -- If all paths have the same label as the merged result, no extra info needed
    if counts.size == 1 && counts.contains mergedLabel then ""
    else
      let parts := counts.toList.mergeSort (fun a b => a.1 < b.1)
        |>.map fun (lbl, n) =>
          s!"{lbl} on {n} path{if n > 1 then "s" else ""}"
      s!" ({", ".intercalate parts})"

end VCOutcome

/-- Merge two SMT results, where `err` dominates `sat` dominates `unknown` dominates `unsat`.
    If either result is an error, the merged result is an error.
    If either result is `sat`, the merged result is `sat` (keeping the first model).
    If either is `unknown`, the merged result is `unknown`.
    Only if both are `unsat` is the merged result `unsat`. -/
def SMT.Result.merge (a b : SMT.Result) : SMT.Result :=
  match a, b with
  | .err e, _ => .err e
  | _, .err e => .err e
  | .sat m, _ => .sat m
  | _, .sat m => .sat m
  | .unknown (some m), .unknown _ => .unknown (some m)
  | .unknown _,        .unknown (some m) => .unknown (some m)
  | .unknown m, _ => .unknown m
  | _, .unknown m => .unknown m
  | .unsat, .unsat => .unsat

/-- Merge two `VCOutcome`s from different paths to the same assertion.
    For each SMT check (satisfiability and validity), `sat` dominates:
    if the assertion is satisfiable on any path, the merged result is sat.
    Each path's `solverLog` is preserved as a separate entry.
    Pre-merge per-path outcomes are stored in `mergedFrom` for rendering. -/
def VCOutcome.merge (a b : VCOutcome) : VCOutcome :=
  let aPaths := if a.mergedFrom.isEmpty then #[a] else a.mergedFrom
  let bPaths := if b.mergedFrom.isEmpty then #[b] else b.mergedFrom
  { satisfiabilityProperty := a.satisfiabilityProperty.merge b.satisfiabilityProperty
    validityProperty := a.validityProperty.merge b.validityProperty
    solverLog := a.solverLog ++ b.solverLog
    mergedFrom := aPaths ++ bPaths }

/--
A model with values lifted to LExpr for display purposes.
This is used for formatting models in a human-readable way
using Core's expression formatter and for future use as program metadata.
-/
abbrev LExprModel := List (Expression.Ident × LExpr CoreLParams.mono)

/-- Format a model value using the Core DDM formatter.
    Renders constructors, applications, and primitives with Core syntax
    (e.g. `Cons(0, Nil)`, `Right(true)`). -/
private def formatModelValue (e : LExpr CoreLParams.mono) : Format :=
  Core.formatExprs [e]

def LExprModel.format (model : LExprModel) : Format :=
  match model with
  | [] => ""
  | [(id, e)] => f!"({id}, {formatModelValue e})"
  | (id, e) :: rest =>
    let first := f!"({id}, {formatModelValue e}) "
    rest.foldl (fun acc (id', e') => acc ++ f!"({id'}, {formatModelValue e'}) ") first

instance : ToFormat LExprModel where
  format := LExprModel.format

/-- Classifies errors that prevent a verification condition from being resolved. -/
inductive VCError where
  | encoding (msg : String)
  | solverTimeout (msg : String)
  | solverCrash (msg : String)
  deriving Repr, BEq

instance : ToString VCError where
  toString
    | .encoding msg      => s!"SMT Encoding Error! {msg}"
    | .solverTimeout msg => s!"Solver Timeout! {msg}"
    | .solverCrash msg   => s!"SMT Solver Crash! {msg}"

/--
A collection of all information relevant to a verification condition's
analysis.
-/
structure VCResult where
  obligation : Imperative.ProofObligation Expression
  outcome : Except VCError VCOutcome
  estate : EncoderState := EncoderState.init
  verbose : VerboseMode := .normal
  checkLevel : CheckLevel := .minimal
  checkMode : VerificationMode := .deductive
  /-- model with values converted from `SMT.Term` to Core `LExpr`.
      The contents must be consistent with the outcome, if the outcome was a failure. -/
  lexprModel : LExprModel := []

/-- Mask outcome properties that were not requested.
    When the evaluator resolves a check that wasn't requested by the
    check mode/level, we set it to `.unknown` so the label function displays
    the appropriate message for the checks that were actually requested.
    For example, in minimal deductive mode we only request validity, so if evaluator
    also determined satisfiability, we mask it to `.unknown`. -/
def maskOutcome (outcome : VCOutcome) (satisfiabilityCheck validityCheck : Bool) : VCOutcome :=
  if satisfiabilityCheck && validityCheck then
    outcome
  else if validityCheck && !satisfiabilityCheck then
    -- Mask to .unknown none — the solverLog preserves the original result
    { outcome with satisfiabilityProperty := .unknown }
  else if satisfiabilityCheck && !validityCheck then
    { outcome with validityProperty := .unknown }
  else
    { outcome with satisfiabilityProperty := .unknown, validityProperty := .unknown }

instance : ToFormat VCResult where
  format r :=
    match r.outcome with
    | .error e =>
      let prop := r.obligation.property
      f!"Obligation: {r.obligation.label}\nProperty: {prop}\nResult: 🚨 {toString e}"
    | .ok outcome =>
      let modelFmt :=
        if r.verbose >= .models && !r.lexprModel.isEmpty then
          f!"\nModel:\n{r.lexprModel}"
        else f!""
      let prop := r.obligation.property
      f!"Obligation: {r.obligation.label}\nProperty: {prop}\nResult: {outcome.emoji prop r.checkLevel r.checkMode} {outcome.label prop r.checkLevel r.checkMode}{modelFmt}"

/-- Compact single-line outcome string: emoji + label
    (e.g. "✅ pass", "❌ fail"). Uses the property, check level,
    and check mode stored in the result. -/
def VCResult.formatOutcome (r : VCResult) : String :=
  let prop := r.obligation.property
  match r.outcome with
  | .ok o =>
    let suffix := o.pathSummary prop r.checkLevel r.checkMode
    s!"{o.emoji prop r.checkLevel r.checkMode} \
       {o.label prop r.checkLevel r.checkMode}{suffix}"
  | .error e => s!"🚨 {toString e}"

/-- Deductive-mode success: the assertion's validity is proven (`isPass`).
    Includes unreachable paths (vacuously true). For bug-finding mode,
    use `isBugFindingSuccess` instead. -/
def VCResult.isSuccess (vr : VCResult) : Bool :=
  match vr.outcome with
  | .ok o => o.isPass
  | .error _ => false

/-- Deductive-mode failure: the assertion can be false on some reachable path.
    For bug-finding mode, use `isBugFindingFailure` instead. -/
def VCResult.isFailure (vr : VCResult) : Bool :=
  match vr.outcome with
  | .ok o => o.alwaysFalseAndReachable || o.alwaysFalseReachabilityUnknown || o.canBeTrueOrFalseAndIsReachable || o.canBeFalseAndIsReachable
  | .error _ => false

def VCResult.isUnknown (vr : VCResult) : Bool :=
  match vr.outcome with
  | .ok o => o.isUnknown
  | .error _ => false

def VCResult.isImplementationError (vr : VCResult) : Bool :=
  match vr.outcome with
  | .error (.encoding _) | .error (.solverCrash _) => true
  | _ => false

def VCResult.isTimeout (vr : VCResult) : Bool :=
  match vr.outcome with
  | .error (.solverTimeout _) => true
  | _ => false

def VCResult.isNotSuccess (vcResult : Core.VCResult) :=
  !Core.VCResult.isSuccess vcResult

def VCResult.isUnreachable (vr : VCResult) : Bool :=
  match vr.outcome with
  | .ok o => o.unreachable
  | .error _ => false

def VCResult.isBugFindingSuccess (vr : VCResult) : Bool :=
  match vr.outcome with
  | .ok o => o.bugFindingSuccess
  | .error _ => false

def VCResult.isBugFindingFailure (vr : VCResult) : Bool :=
  match vr.outcome with
  | .ok o => o.bugFindingFailure
  | .error _ => false

/-- Weaker gate than `VCResult.isUnknown`: triggers when the *validity* component is
    unknown, regardless of satisfiability.  Used by `requeryDropAxioms` because nat
    VCs with bridge axioms land in `satisfiableValidityUnknown` (sat + unknown
    validity), which `VCResult.isUnknown` — requiring both components unknown — does
    not catch. -/
def VCResult.hasValidityUnknown (vr : VCResult) : Bool :=
  match vr.outcome with
  | .ok o => match o.validityProperty with | .unknown _ => true | _ => false
  | .error _ => false

/-- True when either SMT property inside a successful outcome is `.err`.
    Complements `isImplementationError`, which covers the outer `.error` case. -/
def VCResult.hasSMTError (vr : VCResult) : Bool :=
  match vr.outcome with
  | .ok o => o.hasSMTError
  | .error _ => false

abbrev VCResults := Array VCResult

def VCResults.format (rs : VCResults) : Format :=
  let rsf := rs.map (fun r => f!"{Format.line}{r}")
  Format.joinSep rsf.toList Format.line

instance : ToFormat VCResults where
  format := VCResults.format

instance : ToString VCResults where
  toString rs := toString (VCResults.format rs)

/-- Merge two `VCResult`s from different paths to the same assertion.
    Outcomes are merged at the `VCOutcome` level (sat dominates).
    The first result's obligation metadata is preserved.
    The model from the result with a sat outcome is preferred. -/
def VCResult.merge (a b : VCResult) : VCResult :=
  match a.outcome, b.outcome with
  | .error _, _ => a  -- preserve errors
  | _, .error _ => b
  | .ok oa, .ok ob =>
    let merged := oa.merge ob
    -- Keep the model from whichever result had a sat satisfiability or validity
    let model := if oa.satisfiabilityProperty.isSat || oa.validityProperty.isSat
                 then a.lexprModel else b.lexprModel
    { a with outcome := .ok merged, lexprModel := model }

/-- Compute a grouping key for a VCResult based on its source location.
    Uses the display label (property summary) combined with the primary FileRange
    and related FileRanges (from inlining). When the file range is unknown,
    returns `none` so the result is not merged with others. -/
private def vcResultGroupKey (r : VCResult) (uid : Nat) : String × Nat :=
  let displayLabel := r.obligation.metadata.getPropertySummary.getD r.obligation.label
  match Imperative.getFileRange r.obligation.metadata with
  | some fr =>
    if fr.range.isNone then (s!"{displayLabel}@__unique_{uid}", uid + 1)
    else
      let related := Imperative.getRelatedFileRanges r.obligation.metadata
      let relatedKey := related.foldl (fun acc r => s!"{acc}+{repr r}") ""
      (s!"{displayLabel}@{repr fr}{relatedKey}", uid)
  | none => (s!"{displayLabel}@__unique_{uid}", uid + 1)

/-- Merge `VCResults` that originate from the same assertion (identified by
    source location + related locations from inlining). Outcomes are merged
    at the `VCOutcome` level: if a proposition is sat on any path, the merged
    result is sat. Preserves first-occurrence order.
    When the file range is unknown, each VCResult is kept as-is. -/
def VCResults.mergeByAssertion (rs : VCResults) : VCResults :=
  let (resultsByKey, order, _) := rs.foldl
    (init := (Std.HashMap.emptyWithCapacity (α := String) (β := VCResult),
              (#[] : Array String),
              (0 : Nat)))
    fun (resultsByKey, order, uid) r =>
      let (k, uid) := vcResultGroupKey r uid
      match resultsByKey.get? k with
      | some existing =>
        (resultsByKey.insert k (existing.merge r), order, uid)
      | none =>
        (resultsByKey.insert k r, order.push k, uid)
  order.filterMap fun k => resultsByKey.get? k

/-- The counterexample a pair of check results carries: the satisfiability check's model first,
    then the validity check's, a candidate model from `unknown` counting too. -/
def modelOfResults (ctx : SMT.Context) (satResult validityResult : SMT.Result) : LExprModel :=
  match satResult, validityResult with
  | .sat m, _ | _, .sat m | .unknown (some m), _ | _, .unknown (some m) =>
    convertModel m (SMT.Context.getConstructorNames ctx)
  | _, _ => []

/-- Which of the two solver checks an obligation needs, shared by every back end so they agree on
    what a verdict means. It is asked per obligation: an obligation
    annotated for a full check always gets both, and in deductive mode a property that passes when
    unreachable is checked only for validity while one that does not is checked only for
    satisfiability. -/
def checksFor (property : Imperative.PropertyType)
    (md : Imperative.MetaData Expression) (options : VerifyOptions) : Bool × Bool :=
  if Imperative.MetaData.hasFullCheck md then (true, true)
  else
    match options.checkMode, options.checkLevel with
    | _, .full => (true, true)
    | .bugFindingAssumingCompleteSpec, _ => (true, true)
    | .deductive, _ | .deductiveAssumingSatisfiablePaths, _ =>
      if property.passWhenUnreachable then (false, true) else (true, false)
    | .bugFinding, _ => (true, false)

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
      `Core.factoryInterp` models the built-ins' bodies and evaluators but not their axioms.
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

/-- The results the evaluator decides without a solver, for satisfiability and validity: `some r`
    when the obligation alone settles that check, `none` when a solver is needed. A check not
    asked for is `unknown`. -/
def evaluatorResults (obligation : ProofObligation Expression) (checkMode : VerificationMode)
    (satisfiabilityCheck validityCheck : Bool) : Option SMT.Result × Option SMT.Result :=
  -- Satisfiability is settled if the obligation is literally false (unsat).
  let sat : Option SMT.Result :=
    if !satisfiabilityCheck then some .unknown
    else if obligation.obligation.isFalse then some .unsat
    else none
  -- Validity is settled if the obligation is literally true (valid = unsat), or literally false
  -- with a path condition known to be satisfiable (invalid = sat): one that only declares or
  -- defines variables, or one that `usesSatisfiablePathsPremise` takes to be satisfiable.
  let valid : Option SMT.Result :=
    if !validityCheck then some .unknown
    else if obligation.obligation.isTrue then some .unsat
    else if obligation.obligation.isFalse then
      let shape := pathConditionShape obligation
      if shape == .onlyDefinitions || usesSatisfiablePathsPremise obligation checkMode shape then
        some (.sat [])
      else none
    else none
  (sat, valid)

/-- The axiom-relevance cache that `mode` needs for `prog`, or `none` when
    pruning is off. -/
def axiomCacheFor (mode : IrrelevantAxiomsMode) (prog : Program) :
    Option IrrelevantAxioms.Cache :=
  if mode == .Off then none
  else some (IrrelevantAxioms.Cache.build prog
    (directed := mode == .Directed))

/--
Preprocess a proof obligation using symbolic simulation.
Returns the symbolic results for satisfiability and validity independently
(`some r` if the evaluator can determine it, `none` if the solver is needed),
plus the labels of axiom assumptions found irrelevant to this obligation
(empty when pruning is off or inapplicable). The returned obligation has the
pruned axioms removed from its assumptions; the labels let a caller that
needs the *original* assumptions (e.g. for cross-obligation sharing) apply
the pruning at emission time instead.
-/
def preprocessObligation (obligation : ProofObligation Expression) (p : Program)
    (options : VerifyOptions) (satisfiabilityCheck validityCheck : Bool)
    (axiomCache : Option IrrelevantAxioms.Cache := .none)
    -- Names of axiom assumptions, excluded from the relevance seeds.
    (axiomNames : List String := [])
    -- The program the non-directed relevance query runs against; defaults
    -- to `p`.
    (axiomProgram : Option Program := .none)
    : EIO Message (ProofObligation Expression × Option SMT.Result × Option SMT.Result × List String) := do
  let (peSatResult, peValResult) :=
    evaluatorResults obligation options.checkMode satisfiabilityCheck validityCheck
  -- If evaluator resolved both, log for the assert(false) case
  if let (some _, some (.sat _)) := (peSatResult, peValResult) then
    if obligation.property == .assert then
      let prog := f!"\n\n[DEBUG] Evaluated program:\n{Core.formatProgram p}"
      dbg_trace f!"\n\nObligation {obligation.label}: failed!\
                   \n\nResult obtained during evaluation.\
                   {if options.verbose >= .debug then prog else ""}"
  -- Apply axiom pruning if needed.
  -- Axiom removal is unsound for cover obligations (removing axioms weakens
  -- path conditions, potentially making unreachable paths appear satisfiable).
  let (obligation, prunedAxiomLabels) ←
    match options.removeIrrelevantAxioms, axiomCache, obligation.property with
    | .Off, _, _ | _, .none, _ | _, _, .cover => pure (obligation, [])
    | mode, .some cache, _ => -- All property types except `.cover`.
      if peSatResult.isSome && peValResult.isSome then pure (obligation, [])
      else do
        -- The obligation is post-`MonomorphizeFunctions`, so its function
        -- references carry mangled names (`$__mono#f#int`), whereas the axiom
        -- program / cache / call-graph the relevance query runs against is the
        -- pre-pipeline program naming the base `f`.  Demangle the seed names so
        -- both sides agree; otherwise a specialized function's axiom is wrongly
        -- deemed irrelevant and pruned, turning a valid goal into a false alarm.
        -- (Unmangled names are returned unchanged, so non-monomorphized programs
        -- are unaffected.)
        let opName := fun (op : CoreIdent) => Core.NameMangling.demangledBaseName op.toPretty
        let consequentFns := obligation.obligation.getOps.map opName
        -- Seeding from axioms would keep every axiom.
        let axiomSet := Std.HashSet.ofList axiomNames
        let antecedentFns := fun () =>
          obligation.assumptions.flatten.flatMap
            (fun entry =>
              match entry with
              | .assumption label e =>
                if axiomSet.contains label then []
                else (Lambda.LExpr.getOps e).map opName
              | .varDecl _ _ (.det e) => (Lambda.LExpr.getOps e).map opName
              | .varDecl _ _ .nondet => []
              | .distinct _ exprs =>
                exprs.flatMap (fun e => (Lambda.LExpr.getOps e).map opName))
        let seeds := match cache with
          | .directed _ => consequentFns ++ antecedentFns ()
          | .callGraph .. =>
            if mode == .Precise then (consequentFns ++ antecedentFns ()).uniq
            else consequentFns
        let irrelevantAxioms :=
          IrrelevantAxioms.getIrrelevantAxioms (axiomProgram.getD p) cache seeds
        let newAssumptions :=
          Imperative.PathConditions.removeByNames obligation.assumptions irrelevantAxioms
        pure ({ obligation with assumptions := newAssumptions }, irrelevantAxioms)
  return (obligation, peSatResult, peValResult, prunedAxiomLabels)

/-- The Core verification pipeline phases. Each entry pairs a program
    transformation with its per-obligation model validation. The pipeline
    extracts transforms from this list, and the validation extracts phases,
    ensuring they stay in sync.

    Call elimination always runs as a standalone program-to-program pass.
    When `procs` is provided (targeted verification), `filterProcedures`
    appears twice, as an ordinary phase each time: a caller who does not
    filter simply leaves both out. All filter phases are model-preserving
    since they only remove information without introducing
    over-approximations.

    The two occurrences do different work. The first restricts the program to
    the requested procedures, keeping their transitive callees because
    `CallElim` still needs the callees' contracts. The second, after
    `CallElim`, `TermCheck` and `PrecondElim`, discards those callees now that
    their contracts have been inlined; it names the requested procedures and
    drops the lemmas no declaration lists. The well-formedness and termination lemmas of a
    requested procedure or function survive because it lists them in its
    `lemmas`; those of other functions are pruned.

    A single filter would suffice if the first pass kept each callee as its
    contract alone, with the body removed: `CallElim` would consume those
    declarations and they would fall away, leaving nothing for a second pass to
    collect. That requires changing what the filter produces.

    `loopElimPipelinePhase` is placed last because loop elimination happens
    during evaluation (not as a program-to-program pass), making it the
    closest phase to SMT.

    `assertWellFormedCalls` comes first, so an ill-formed call is reported in
    every procedure, including ones the procedure filter then drops. The filter
    follows, and then `assertNoCFGBodies`, which turns a throw from inside
    `runProgram` into a rejection naming the fact, so every statement-level
    transform after it may rely on structured bodies. -/
def transformPipelinePhases (options : VerifyOptions := VerifyOptions.default) :
    List PipelinePhase :=
  let procs := options.proceduresToVerify
  let filterPhases := match procs with
    | some ps => [filterProceduresPipelinePhase ps]
    | none => []
  let postFilterPhases := match procs with
    | some ps =>
      [filterProceduresPipelinePhase ps (keepUnlistedLemmas := false)]
    | none => []
  -- The filter runs before `assertNoCFGBodies`, so a caller naming structured
  -- procedures to verify is not refused for an excluded CFG body.
  [ProgramFact.assertPhase .wellFormedCalls] ++ filterPhases ++
    [ProgramFact.assertPhase .noCFGBodies,
      callElimPipelinePhase, termCheckPipelinePhase, precondElimPipelinePhase]
    ++ postFilterPhases ++ [insertLoopInvariantAssertsPipelinePhase, loopElimPipelinePhase]

/-- Type-checking pipeline phase: runs `Core.typeCheck` on the program against
    `factory` (the full function set to type-check against; defaults to the
    pristine `Core.Factory`). -/
def typeCheckPipelinePhase
    (options : VerifyOptions := VerifyOptions.default)
    (factory : @Lambda.Factory CoreLParams := Core.Factory) : PipelinePhase :=
  -- Type checking annotates expressions and leaves every statement where it
  -- is, so it carries all facts across. Annotation does not change which
  -- constructor an expression is, so a redex-free program stays redex-free.
  modelPreservingPipelinePhase "typeCheck"
    (establishes := factSet![.typeAnnotated])
    (preserves := factSet![.noCFGBodies, .noCalls, .noLoops, .noLoopInvariants,
                         .noLoopMeasures, .staticSingleAssignment, .noBetaRedexes,
                         .noPrecondsFromFuncs, .noNondetGuards, .noProcedureContracts,
                         .noPolymorphicProcedures,
                         .noPolymorphicFunctions])
    fun prog => do
      match Core.typeCheck options prog factory with
      | .ok prog' => return (true, prog')
      | .error err => throw { err with message := s!"❌ Type checking error.\n{err.message}" }

/-- Symbolic-evaluation pipeline phase: partially evaluates the program into
    the passive proof-obligation form consumed by obligation extraction.

    Requires `noNondetGuards`, which `NondetElim.nondetElimPipelinePhase` establishes:
    `Core.Statement.eval` rejects a surviving nondeterministic guard. -/
def symbolicEvalPipelinePhase
    (options : VerifyOptions := VerifyOptions.default)
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default) : PipelinePhase :=
  -- `noBetaRedexes` is the one fact this phase cannot claim: partial-evaluation
  -- inlining introduces redexes. It requires `noLoops`, so the loop facts it
  -- carries forward were established upstream; it preserves rather than
  -- re-establishes them. `noNondetGuards` is not preserved: the output separates
  -- obligations with `ite *`.
  modelPreservingPipelinePhase "symbolicEval"
    (requires := factSet![.noCFGBodies, .noLoops, .noNondetGuards])
    (establishes := factSet![.noCalls, .staticSingleAssignment, .hasObligationForm,
                             .noProcedureContracts])
    (preserves := factSet![.noCFGBodies, .noLoops, .noLoopInvariants, .noLoopMeasures,
                         .noPrecondsFromFuncs,
                         .noPolymorphicProcedures,
                         .noPolymorphicFunctions, .typeAnnotated])
    fun prog => do
      let (prog', stats) ← Transform.liftDiag (Core.toCoreProofObligationProgram options prog moreFns |>.mapError
        fun err => { err with message := s!"❌ Symbolic evaluation error.\n{err.message}" })
      modify fun σ => { σ with statistics := σ.statistics.merge stats }
      return (true, prog')


/-- The phases that run between `transformPipelinePhases` and `symbolicEvalPipelinePhase`:
    replace procedure and lemma type parameters by opaque types, type-check, monomorphize functions, and eliminate
    nondeterminism.

    Factored out so `genVCs` in `MetaVerifier` can reuse them without pulling in
    the full `transformPipelinePhases` prefix (call elimination, precondition
    lifting, etc.), which is unnecessary for programs that already arrive
    call-free from the Boole→Core translation. -/
def preSymbolicEvalPipelinePhases (options : VerifyOptions := .default)
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default) : List PipelinePhase :=
  -- `verify` pre-validates `Core.Factory.addFactory moreFns`, so the `getD`
  -- fallback here is only a totality safety net.
  let typeCheckFactory := (Core.Factory.addFactory moreFns).toOption.getD Core.Factory
  [genOpaqueTypeParamsPipelinePhase,
   typeCheckPipelinePhase options typeCheckFactory,
   monomorphizeFunctionsPipelinePhase,
   simplifyPhase,
   NondetElim.nondetElimPipelinePhase]

/-- The full pipeline phases for program-to-program transforms, including
    type checking, symbolic evaluation, and common subexpression elim.
    CSE runs after symbolic evaluation to extract common
    subexpressions introduced by partial evaluation inlining; it is
    model-preserving (a pipeline that omits it is still sound,
    though solver outcomes may differ on individual obligations). -/
def corePipelinePhases
    (options : VerifyOptions := VerifyOptions.default)
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default) : List PipelinePhase :=
  transformPipelinePhases options
    ++ preSymbolicEvalPipelinePhases options moreFns
    ++ [symbolicEvalPipelinePhase options moreFns]
    ++ [betaReducePipelinePhase, commonSubexprElimPhase]

/-- What the back end needs of the program the pipeline hands it, as opposed to
    what one phase asks of another. A phase list that does not deliver these is
    rejected the same way as one whose phases do not fit.

    A CFG body is worse than an unsupported statement: obligation extraction
    returns *no obligations at all* for one, so every assertion in it would go
    unchecked and unreported.

    `noNondetGuards` is absent because obligation extraction accepts `ite *`;
    `hasObligationForm` states what it does require.

    `noLoopInvariants` and `noLoopMeasures` are absent because `noLoops` covers
    them; they are required by `LoopElim`, which is where they matter. -/
def backEndRequiredFacts : ProgramFactSet :=
  factSet![.noCFGBodies, .noCalls, .noLoops, .staticSingleAssignment,
           .noBetaRedexes, .noPrecondsFromFuncs, .hasObligationForm, .noProcedureContracts,
           .noPolymorphicProcedures, .noPolymorphicFunctions,
           .typeAnnotated]

/-- The Core pipeline, checked as it is assembled: the phase list built from
    `options`, validated against the phases' contracts and against what the back
    end requires. A phase list that does not compose never becomes a pipeline, so
    callers cannot run one.

    A caller wanting a different order builds one with `Core.validatePipeline`
    (or `Core.validatePipelineFrom`) over a phase list of its own and passes the
    result to `verify`. -/
def coreValidatedPipeline
    (options : VerifyOptions := VerifyOptions.default)
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default) :
    Except String (ValidatedPipeline ProgramFactSet.empty) :=
  ValidatedPipeline.ofListDelivering "the verification back end" backEndRequiredFacts
    (corePipelinePhases options moreFns)

/-- The abstracted phases derived from the Core pipeline phases.

    Must be called with the same `options` as the corresponding
    `corePipelinePhases` run: the phase list's membership is
    options-dependent (`proceduresToVerify`), so a list computed
    with different options describes phases that did not actually run. -/
def coreAbstractedPhases
    (options : VerifyOptions := VerifyOptions.default)
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default) : List AbstractedPhase :=
  (corePipelinePhases options moreFns).map (·.phase)

/-- Build the solver log from raw results and phase validation logs. -/
private def buildSolverLog (satResult valResult : SMT.Result)
    (satisfiabilityCheck validityCheck : Bool)
    (satPhaseLog valPhaseLog : List SolverPhaseLog) : Array SolverPhaseLog :=
  let sat : Array SolverPhaseLog :=
    if satisfiabilityCheck then #[{ phase := "solver.sat", result := satResult }] else #[]
  let val : Array SolverPhaseLog :=
    if validityCheck then #[{ phase := "solver.val", result := valResult }] else #[]
  sat ++ val ++ satPhaseLog.toArray ++ valPhaseLog.toArray

/-- Adjust an SMT result through pipeline phase validation. A `.sat` result
    may be demoted to `.unknown` if a phase cannot validate the model, and
    an `.unknown` result may be promoted back to `.sat` if a phase can
    validate the model. Returns the adjusted result and a log of
    intermediate results per phase. -/
def SMT.Result.adjustForPhases (r : SMT.Result)
    (phases : List AbstractedPhase)
    (obligation : ProofObligation Expression) : SMT.Result × List SolverPhaseLog :=
  match r with
  | .sat _ | .unknown _ => AbstractedPhase.validateModel phases r obligation
  | other => (other, [])

/-- The outcome as reported. When `axiomsDropped` is set, a `sat` becomes
    `unknown`, keeping its model, because the model may violate a dropped
    axiom, so a real violation found this way also reports as `unknown`. An
    `unsat` stands: adding the dropped axioms back keeps the query
    unsatisfiable. -/
def VCOutcome.withAxiomsDropped (o : VCOutcome) : VCOutcome :=
  if !o.axiomsDropped then o else
  let demote : SMT.Result → SMT.Result
    | .sat m => .unknown (some m)
    | r => r
  { o with satisfiabilityProperty := demote o.satisfiabilityProperty,
           validityProperty := demote o.validityProperty }

/-- The outcome of a query from which pruning in `mode` dropped the axioms
    `dropped`. In `directed` mode it is marked and reported as
    `withAxiomsDropped` says; other modes keep the solver's answer. -/
def VCOutcome.afterPruning (mode : IrrelevantAxiomsMode)
    (dropped : List String) (o : VCOutcome) : VCOutcome :=
  let dropsHere := mode == .Directed && !dropped.isEmpty
  { o with axiomsDropped := o.axiomsDropped || dropsHere }.withAxiomsDropped

/-- Pass a result's two verdicts through the phases' model validation, as the default back end
    does for each obligation it discharges, and record what each phase decided. -/
def VCResult.validateModels (r : VCResult) (phases : List AbstractedPhase) : VCResult :=
  match r.outcome with
  | .error _ => r
  | .ok o =>
    let (sat, satLog) := o.satisfiabilityProperty.adjustForPhases phases r.obligation
    let (valid, validLog) := o.validityProperty.adjustForPhases phases r.obligation
    -- A model a phase accepts may still violate an axiom pruning dropped.
    { r with outcome := .ok ({ o with
        satisfiabilityProperty := sat, validityProperty := valid,
        solverLog := o.solverLog.push (satLog ++ validLog).toArray }
        |>.withAxiomsDropped) }

/-- A discharge function encapsulates the solver backend. It takes assumption
    terms, the obligation term, the SMT context, and the satisfiability/validity
    check flags, and returns the solver results. The pipeline is parametrized
    by this function so it does not know about SMT-LIB or any specific solver. -/
abbrev DischargeFn :=
  List Term → Term → SMT.Context → Bool → Bool → List VarDefinition → List VarDeclaration →
  IO (Except Imperative.SMT.SolverError (SMT.Result × SMT.Result × EncoderState))

/-- A `CoreSMTSolver` encapsulates the strategy for discharging all proof
    obligations extracted from a CoreSMT program. The pipeline is parametrized
    by this function so that the solver backend can be swapped — e.g. for a
    parallel solver that dispatches obligations concurrently, or an incremental
    solver that shares path-condition state across assertions.

    The solver receives the fully-built factory (Core's built-ins plus any
    custom functions from external phases, e.g. `RuntimeFactory`, already
    threaded through the transformation pipeline) and the obligation program
    (in CoreSMT format after all pipeline transformations), and returns
    verification results together with statistics. Because the factory is
    already complete, a custom solver must pass it to `buildEnv` as-is and must
    NOT call `Core.Factory.addFactory` on it — doing so would re-add Core's
    built-ins and fail with duplicate-function errors. -/
abbrev CoreSMTSolver :=
  @Lambda.Factory CoreLParams → Program → EIO Message (VCResults × Statistics)

/-- Factory for discharge functions. Called once per obligation with the
    obligation's typed variables, metadata, and label. A custom implementation
    can replace the default (batch/incremental SMT-LIB) backend. -/
abbrev MkDischargeFn :=
  VerifyOptions → IO.Ref Nat → System.FilePath →
  List Expression.TypedIdent → Imperative.MetaData Expression → String →
  -- Term→SMT-LIB string cache; `none` on the parallel path.
  Option (IO.Ref (Std.HashMap Term String)) →
  -- Pre-assembled file from env-scoped capture; `none` selects
  -- per-obligation encoding. Ignored by the incremental backend.
  Option Core.SMT.Emitter.CapturedFile →
  PipelineContext → DischargeFn

/-- Construct a `DischargeFn` from verification options. Selects the incremental
    (abstract solver) backend or the batch (SMT-LIB file) backend based on
    `options.incremental` and `options.alwaysGenerateSMT`. -/
def mkDischargeFn : MkDischargeFn := fun (options : VerifyOptions) (counter : IO.Ref Nat)
    (tempDir : System.FilePath)
    (vars : List Expression.TypedIdent)
    (md : Imperative.MetaData Expression)
    (label : String)
    (termCache : Option (IO.Ref (Std.HashMap Term String)))
    (captured : Option Core.SMT.Emitter.CapturedFile)
    (pctx : PipelineContext) =>
  fun assumptionTerms obligationTerm ctx satisfiabilityCheck validityCheck
      varDefinitions varDeclarations => do
    if options.incremental && !options.alwaysGenerateSMT then
      -- `captured` does not apply: the incremental backend writes no files.
      SMT.dischargeObligationIncremental options vars md
        assumptionTerms obligationTerm ctx satisfiabilityCheck validityCheck label
        (varDefinitions := varDefinitions) (varDeclarations := varDeclarations)
    else
      -- Claim the number atomically: under `--parallel N` several worker tasks call this
      -- concurrently with the same `counter`, and a separate `get`/`set` lets two of them
      -- read the same value, write the same file and solve each other's query.
      let counterVal ← counter.modifyGet fun n => (n, n + 1)
      let filename := tempDir / s!"{SMT.sanitizeFilenameCapped label}_{counterVal}.smt2"
      SMT.dischargeObligation options vars md filename.toString
        assumptionTerms obligationTerm ctx satisfiabilityCheck validityCheck
        (label := label) (varDefinitions := varDefinitions) (varDeclarations := varDeclarations)
        (termCache := termCache)
        (captured := captured)
        (pctx := pctx)

open CSE (isCSEGeneratedName)

/--
Invoke a backend engine and get the analysis result for a
given proof obligation.
-/
def getObligationResult (assumptionTerms : List Term) (obligationTerm : Term)
    (ctx : SMT.Context)
    (obligation : ProofObligation Expression) (p : Program)
    (options : VerifyOptions)
    (discharge : DischargeFn)
    (satisfiabilityCheck validityCheck : Bool)
    (phases : List AbstractedPhase)
    (varDefinitions : List VarDefinition := [])
    (varDeclarations : List VarDeclaration := [])
    -- Labels of the axioms pruning dropped from this query.
    (prunedAxiomLabels : List String := [])
    : EIO Message VCResult := do
  -- Formatting the whole program is costly on a large one, so it is done only when the debug
  -- trace below shows it.
  let prog : Unit → Format := fun _ => f!"\n\n[DEBUG] Evaluated program:\n{Core.formatProgram p}"
  let ans ← IO.toEIO
      (fun e => Message.fromFormat f!"{e}")
      (discharge assumptionTerms obligationTerm ctx satisfiabilityCheck validityCheck
        varDefinitions varDeclarations)
  match ans with
  | .error solverError =>
    let vcError : VCError := match solverError with
      | .encoding e => .encoding (toString e)
      | .timeout d => .solverTimeout d
      | .crash d   => .solverCrash d
    let traceInQuiet := match solverError with
      | .encoding _ => false
      | _ => true
    if traceInQuiet || options.verbose >= VerboseMode.debug then
      dbg_trace f!"\n\nObligation {obligation.label}: {vcError}\
                   {if options.verbose >= VerboseMode.debug then prog () else ""}"
    return { obligation := obligation,
             outcome := Except.error vcError,
             verbose := options.verbose,
             checkLevel := options.checkLevel,
             checkMode := options.checkMode,
             lexprModel := [] }
  | .ok (satResult, validityResult, estate) =>
    -- Convert unvalidated sat results to unknown when phases require validation
    let (adjSat, satPhaseLog) := satResult.adjustForPhases phases obligation
    let (adjVal, valPhaseLog) := validityResult.adjustForPhases phases obligation
    -- Build solver log: raw solver results followed by phase validation logs
    let smtLog := buildSolverLog satResult validityResult
      satisfiabilityCheck validityCheck satPhaseLog valPhaseLog
    let rawOutcome : VCOutcome := {
      satisfiabilityProperty := adjSat,
      validityProperty := adjVal,
      solverLog := #[smtLog] }
    let outcome := maskOutcome rawOutcome satisfiabilityCheck validityCheck
      |>.afterPruning options.removeIrrelevantAxioms prunedAxiomLabels
    -- Extract model from sat or unknown-with-candidate results.
    -- unknown (some m) arises when the solver returns a candidate model it cannot
    -- certify (e.g. cvc5 with quantified bridge axioms). Phases may promote it
    -- to sat; we still want the model available for display.
    let model := modelOfResults ctx satResult validityResult
    -- A counterexample reports the variables `Core.SMT.isReportedName` names.
    let definedNames := definedNameSet varDefinitions
    let model := model.filter fun (name, _) => Core.SMT.isReportedName definedNames name.name
    let result := { obligation,
                    outcome := .ok outcome,
                    estate,
                    verbose := options.verbose,
                    checkLevel := options.checkLevel,
                    checkMode := options.checkMode,
                    lexprModel := model }
    return result

/-- Data needed to dispatch a single obligation to the solver. Produced by the
    sequential preprocessing phase and consumed by the (potentially parallel)
    solver dispatch phase. -/
private structure SolverJob where
  obligation : ProofObligation Expression
  assumptionTerms : List Term
  obligationTerm : Term
  ctx : SMT.Context
  needSatCheck : Bool
  needValCheck : Bool
  peSatResult? : Option SMT.Result
  peValResult? : Option SMT.Result
  typedVarsInObligation : List Expression.TypedIdent
  varDefs : List VarDefinition := []
  varDecls : List VarDeclaration := []
  /-- Labels of the axioms irrelevant-axiom removal dropped from this query. -/
  prunedAxiomLabels : List String := []

/-- Disposition of one obligation coming out of the `smtDischarge` phase: either
    solved inline with a ready `VCResult` (`resolved` -- also used for encoding
    errors), or only prepared as a `SolverJob` that the parallel dispatch pass
    solves later (`deferred`). -/
private inductive ObligationDisposition where
  | resolved (result : VCResult)
  | deferred (job : SolverJob)

/-- Dispatch a single solver job. Spawns a solver process and reads the result. -/
private def dispatchSolverJob (job : SolverJob) (p : Program)
    (options : VerifyOptions) (counter : IO.Ref Nat) (tempDir : System.FilePath)
    (phases : List AbstractedPhase)
    (mkDischarge : MkDischargeFn := mkDischargeFn)
    (pctx : PipelineContext)
    : IO (Except Message VCResult) := do
  -- Parallel path: no shared term cache (workers must not share a mutable
  -- ref) and no captured file (see `useCapture` in `verifySingleEnv`).
  let discharge := mkDischarge options counter tempDir
    job.typedVarsInObligation job.obligation.metadata job.obligation.label none none pctx
  let resultOrErr ← (getObligationResult job.assumptionTerms job.obligationTerm job.ctx
    job.obligation p options discharge job.needSatCheck job.needValCheck phases
    (varDefinitions := job.varDefs) (varDeclarations := job.varDecls)
    (prunedAxiomLabels := job.prunedAxiomLabels)).toBaseIO
  match resultOrErr with
  | .error diag => return .error diag
  | .ok result =>
    let result := match result.outcome with
      | .ok solverOutcome =>
        let satResult := job.peSatResult?.getD solverOutcome.satisfiabilityProperty
        let valResult := job.peValResult?.getD solverOutcome.validityProperty
        { result with outcome := .ok { solverOutcome with
            satisfiabilityProperty := satResult,
            validityProperty := valResult } }
      | .error _ => result
    return .ok result

/-- Dispatch solver jobs using a bounded worker pool. Workers pull from a shared
    queue; results returned in original order.

    Each worker task gets its own `PipelineContext.fork` of `pctx`: the context's
    phase-tracking refs are not thread-safe (see `Strata/Pipeline/Context.lean`),
    so sharing `pctx` itself lets concurrent `withPhase` calls corrupt its phase
    stack. A fork shares `pctx`'s messages and metrics handle, so diagnostics and
    JSONL metrics from discharge still reach the caller, tagged with the caller's
    phase path. Forks do not print phase lines, so per-obligation phases are not
    printed under `--profile` (a `--verbose` caller still sees worker diagnostics
    on stderr). After the pool finishes, `joinForks` credits the pool's
    wall-clock time to the caller's enclosing phase (`vcDischarge`), so its
    metrics have the same shape as a sequential run's. -/
private def dispatchJobsParallel (jobs : List SolverJob) (p : Program)
    (options : VerifyOptions) (counter : IO.Ref Nat) (tempDir : System.FilePath)
    (phases : List AbstractedPhase) (workers : Nat)
    (mkDischarge : MkDischargeFn := mkDischargeFn)
    (pctx : PipelineContext)
    : IO (List (Option (Except Message VCResult))) := do
  let queue ← IO.mkRef (jobs.zipIdx : List (SolverJob × Nat))
  let resultMap ← IO.mkRef ({} : Std.HashMap Nat (Except Message VCResult))
  let shouldStop ← IO.mkRef false
  let workerFn (workerCtx : PipelineContext) : IO Unit := do
    let mut running := true
    while running do
      if ← shouldStop.get then break
      let entry ← queue.modifyGet fun q =>
        match q with
        | [] => (none, [])
        | hd :: tl => (some hd, tl)
      match entry with
      | none => running := false
      | some (job, idx) =>
        let result ← dispatchSolverJob job p options counter tempDir phases mkDischarge workerCtx
        resultMap.modify (·.insert idx result)
        if options.stopOnFirstError then
          match result with
          | .ok r => if r.isNotSuccess then shouldStop.set true
          | .error _ => shouldStop.set true
  let numWorkers := min workers jobs.length
  -- Fork on this thread, before any worker starts, so the forks see a stable
  -- phase on `pctx`.
  let workerCtxs ← (List.range numWorkers).mapM fun _ => (pctx.fork : BaseIO _)
  let poolStartNs ← IO.monoNanosNow
  let workerTasks ← workerCtxs.mapM fun workerCtx =>
    IO.asTask (prio := .dedicated) (workerFn workerCtx)
  -- Join all tasks before throwing to prevent orphaned processes
  let mut firstError : Option IO.Error := none
  for task in workerTasks do
    match task.get with
    | .ok () => pure ()
    | .error e => if firstError.isNone then firstError := some e
  let poolElapsedNs := (← IO.monoNanosNow) - poolStartNs
  pctx.joinForks workerCtxs poolElapsedNs
  if let some e := firstError then throw e
  let rmap ← resultMap.get
  let mut results : List (Option (Except Message VCResult)) := []
  for idx in (List.range jobs.length).reverse do
    results := rmap[idx]? :: results
  return results

private
def addCSEReferences (refs : Std.HashSet String) (e : Expression.Expr) :
    Std.HashSet String :=
  (Lambda.LExpr.freeVars e).foldl (fun refs (id, _) =>
    if isCSEGeneratedName id.name then refs.insert id.name else refs) refs

private
def addFreeVarNames (refs : Std.HashSet String) (e : Expression.Expr) :
    Std.HashSet String :=
  (Lambda.LExpr.freeVars e).foldl (fun refs (id, _) => refs.insert id.name) refs

/-- The names `roots` reach through `definitions`: the least set that contains `roots` and, for
    every definition whose name it contains, the names `refs` returns for that definition's body.
    A worklist expands each defined name once, so the cost is linear in the size of the
    definitions, whatever their order and however long their chains. -/
private
def defClosure (refs : Expression.Expr → List String)
    (definitions : List (String × Expression.Expr)) (roots : Std.HashSet String) :
    Std.HashSet String :=
  let bodies : Std.HashMap String (List Expression.Expr) :=
    definitions.foldl (fun m (n, e) => m.insert n (e :: m.getD n [])) {}
  -- A name enters the worklist once, when it is first reached, and only if it is defined, so
  -- the fuel `definitions.length` never runs out.
  go bodies definitions.length (roots.toList.filter bodies.contains) roots
where
  go (bodies : Std.HashMap String (List Expression.Expr)) :
      Nat → List String → Std.HashSet String → Std.HashSet String
    | 0, _, reached | _, [], reached => reached
    | fuel + 1, n :: pending, reached =>
      let (pending, reached) := (bodies.getD n []).foldl (fun acc e =>
        (refs e).foldl (fun (pending, reached) v =>
          if reached.contains v then (pending, reached)
          else (if bodies.contains v then v :: pending else pending, reached.insert v)) acc)
        (pending, reached)
      go bodies fuel pending reached

/-- The variables a counterexample for `obligation` should report: those its goal and
    assumptions reach, through the managed definitions they use, that
    `Core.SMT.isReportedName` names. A variable the passive program declares (`var x`) is
    reported; one it defines (`init x := e`) is not, since its value follows from the others. -/
def collectModelVars
    (obligation : Imperative.ProofObligation Expression)
    (varDefinitions : List VarDefinition)
    (varDeclarations : List VarDeclaration) :
    List (Lambda.IdentT Lambda.LMonoTy Unit) :=
  let managedNames := managedNameSet varDefinitions varDeclarations
  let definitions := obligation.assumptions.flatMap fun pathCondition =>
    pathCondition.filterMap fun
      | .varDecl name _ (.det rhs) =>
        if managedNames.contains name.name then some (name.name, rhs) else none
      | _ => none
  let rootRefs := obligation.assumptions.foldl (fun refs pathCondition =>
    pathCondition.foldl (fun refs entry =>
      match entry with
      | .assumption _ e => addFreeVarNames refs e
      | .distinct _ es => es.foldl addFreeVarNames refs
      | .varDecl name _ (.det rhs) =>
        if managedNames.contains name.name then refs else addFreeVarNames refs rhs
      | .varDecl _ _ .nondet => refs) refs)
    (addFreeVarNames {} obligation.obligation)
  let relevantNames :=
    defClosure (fun e => (Lambda.LExpr.freeVars e).map (·.1.name)) definitions rootRefs
  let definedNames := definedNameSet varDefinitions
  (ProofObligation.getVars obligation).filter fun (v, _) =>
    relevantNames.contains v.name && Core.SMT.isReportedName definedNames v.name

private
def containsUnsupportedSMTString : Expression.Expr → Bool
  | .const _ (.strConst s) =>
    match SMT.StringLit.validate s with
    | .ok () => false
    | .error _ => true
  | .const _ _ | .op .. | .bvar .. | .fvar .. => false
  | .abs _ _ _ body => containsUnsupportedSMTString body
  | .quant _ _ _ _ trigger body =>
    containsUnsupportedSMTString trigger || containsUnsupportedSMTString body
  | .app _ fn arg =>
    containsUnsupportedSMTString fn || containsUnsupportedSMTString arg
  | .ite _ c t e =>
    containsUnsupportedSMTString c ||
      containsUnsupportedSMTString t ||
      containsUnsupportedSMTString e
  | .eq _ lhs rhs =>
    containsUnsupportedSMTString lhs || containsUnsupportedSMTString rhs

def hasUnsupportedStringCSEDefinition
    (obligation : Imperative.ProofObligation Expression) : Bool :=
  obligation.assumptions.any fun pathCondition =>
    pathCondition.any fun
      | .varDecl name _ (.det rhs) =>
        isCSEGeneratedName name.name && containsUnsupportedSMTString rhs
      | _ => false

/-- Remove CSE-generated definitions that cannot affect this obligation.

Symbolic evaluation combines every deferred obligation into one synthetic
procedure before CSE runs. CSE may therefore hoist a repeated expression above
all obligation branches, making its `init $__cse.*` entry appear in every
obligation even when only one branch references it. Besides producing needless
SMT, an unencodable literal in such a definition would then prevent unrelated
obligations from reaching the solver.

This pruning is applied only when the extracted obligation set contains an
SMT-unrepresentable string inside a CSE definition. Ordinary CSE definitions
remain shared across obligations, preserving the fold and emitter's
shared-prefix reuse. On the exceptional path, start from CSE variables
referenced by the obligation and by non-CSE path-condition entries, close
transitively over CSE definition bodies, and retain only those definitions.
The original entry ordering is preserved, so every retained dependency is
still emitted before its users. -/
def pruneUnusedCSEDefinitions
    (obligation : Imperative.ProofObligation Expression) :
    Imperative.ProofObligation Expression :=
  let definitions := obligation.assumptions.flatMap fun pathCondition =>
    pathCondition.filterMap fun
      | .varDecl name _ (.det rhs) =>
        if isCSEGeneratedName name.name then some (name.name, rhs) else none
      | _ => none
  if definitions.isEmpty then
    obligation
  else
    let rootRefs := obligation.assumptions.foldl (fun refs pathCondition =>
      pathCondition.foldl (fun refs entry =>
        match entry with
        | .assumption _ e => addCSEReferences refs e
        | .distinct _ es => es.foldl addCSEReferences refs
        | .varDecl name _ (.det rhs) =>
          if isCSEGeneratedName name.name then refs
          else addCSEReferences refs rhs
        | .varDecl _ _ .nondet => refs) refs)
      (addCSEReferences {} obligation.obligation)
    let needed := defClosure (fun e => (Lambda.LExpr.freeVars e).filterMap fun (id, _) =>
      if isCSEGeneratedName id.name then some id.name else none) definitions rootRefs
    let assumptions := obligation.assumptions.map fun pathCondition =>
      pathCondition.filter fun
        | .varDecl name _ (.det _) =>
          !isCSEGeneratedName name.name || needed.contains name.name
        | _ => true
    { obligation with assumptions }

/-- Discharge `obligations`, in order, against the environment `E` built for the program they
    come from: each is asked of the solver `mkDischarge` gives, after the evaluator and the
    pruning the options ask for. `verifySingleEnv` sends a whole program's obligations through
    here; a back end that has already read the obligations sends one at a time. -/
def dischargeObligations (E : Env) (obligations : ProofObligations Expression)
    (options : VerifyOptions)
    (counter : IO.Ref Nat) (tempDir : System.FilePath)
    (axiomCache : Option IrrelevantAxioms.Cache := .none)
    (axiomNames : List String := [])
    (axiomProgram : Option Program := .none)
    (externalPhases : List AbstractedPhase := [])
    (corePhases : List AbstractedPhase := coreAbstractedPhases)
    (mkDischarge : MkDischargeFn := mkDischargeFn)
    (pctx : PipelineContext) :
    EIO Message (VCResults × Statistics) := do
  let p := E.program
  -- Note: the encoder below reuses shared path-condition prefixes only between
  -- consecutive obligations.
  let mut stats : Statistics := ({} : Statistics)
    |>.increment s!"{Evaluator.Stats.verify_numObligations}" obligations.size
  let mut results := (#[] : VCResults)
  let mut solverJobs : List SolverJob := []
  let mut solverJobIndices : List Nat := []
  let useParallel := options.parallelWorkers > 1
  let datatypes := SMT.Datatypes.ofFactory E.datatypes
  -- Term→SMT-LIB string cache shared across this procedure's obligations, which
  -- often share many assumption terms. Sequential path only; parallel passes `none`.
  let termCache ← IO.toEIO (fun e => Message.fromFormat f!"{e}")
    (IO.mkRef (∅ : Std.HashMap Term String))
  -- The encoder, threaded across this env's obligations: shared
  -- path-condition history is encoded once and reused; each obligation's
  -- result is forked from the current position.
  -- Tracks the last SMT-encoded obligation, not the loop index: the evaluator
  -- fast-path and encoding failures leave it unchanged. `advance` recomputes
  -- reuse against whatever frames are present, so correctness
  -- (`PathConditions.Fold.advance_eq_reference`) is independent of which
  -- obligations advanced it; skipping only affects how much prefix is reused
  -- next.
  let smtCtx := { SMT.Context.default with
    datatypes,
    useArrayTheory := options.useArrayTheory,
    recFnsAsDefineFunRec := options.recursiveFnsAsDefineFunRec }
  let mut encState : SMTEncodeState := .init { ctx := smtCtx }
  -- Pointer-memoized snapshot assembly, threaded like `encState`
  -- (see `Strata.PtrCache`).
  let mut snapCache : Strata.PtrCache.PtrCache1 Core.EncodeResult.Assembly.ofFrames := .empty
  -- Env-scoped emission (`Core.SMT.Emitter`), for the sequential batch path
  -- only: the parallel path defers file writing to its dispatch phase, and
  -- the incremental backend does not write files.
  let useCapture := !useParallel && !(options.incremental && !options.alwaysGenerateSMT)
  let emStateInit : Option Core.SMT.Emitter.EmitterState ←
    if useCapture then
      IO.toEIO (fun e => Message.fromFormat f!"{e}")
        (some <$> Core.SMT.Emitter.EmitterState.init smtCtx
          (SMT.setSolverPrelude options.solver options.solverOptions))
    else pure none
  let mut emState := emStateInit
  for obligation in obligations do
    -- `obligationsToVerify`: obligations not listed are skipped entirely.
    if let some labels := options.obligationsToVerify then
      if !labels.contains obligation.label then continue
    -- Determine which checks to perform based on metadata or check mode/amount
    let (satisfiabilityCheck, validityCheck) :=
      checksFor obligation.property obligation.metadata options
    -- The state encodes the *original* assumptions; `prunedAxiomLabels` applies
    -- the pruning as an emission-time label filter instead.
    let origObligation := obligation
    let (obligation, peSatResult?, peValResult?, prunedAxiomLabels) ← pctx.withRepeatedPhase "evalDischarge" do
      preprocessObligation obligation p options satisfiabilityCheck validityCheck axiomCache axiomNames axiomProgram
    -- If evaluator resolved both checks, we're done, unless we always want to generate SMT queries
    if not options.alwaysGenerateSMT then
      if let (some peSat, some peVal) := (peSatResult?, peValResult?) then
        let phases := externalPhases ++ corePhases
        let (adjPeSat, satPhaseLog) := peSat.adjustForPhases phases obligation
        let (adjPeVal, valPhaseLog) := peVal.adjustForPhases phases obligation
        let peLog := buildSolverLog peSat peVal
          satisfiabilityCheck validityCheck satPhaseLog valPhaseLog
        let outcome : VCOutcome := {
          satisfiabilityProperty := adjPeSat,
          validityProperty := adjPeVal,
          solverLog := #[peLog] }
        let result : VCResult := { obligation, outcome := .ok outcome, verbose := options.verbose,
                                    checkLevel := options.checkLevel, checkMode := options.checkMode, lexprModel := [] }
        results := results.push result
        if result.isFailure || result.isImplementationError || result.isTimeout then
          if options.verbose >= .debug then
            let prog := f!"\n\n[DEBUG] Evaluated program:\n{Core.formatProgram p}"
            dbg_trace f!"\n\nResult: {result}\n{prog}"
          if options.stopOnFirstError then break
        -- Evaluator resolved both checks: skip SMT, leaving `encState` unadvanced.
        continue
    -- Need the solver for at least one check
    let needSatCheck := satisfiabilityCheck && peSatResult?.isNone
    let needValCheck := validityCheck && peValResult?.isNone
    -- `smtDischarge`: the whole SMT path for one obligation.
    -- The action returns an `ObligationDisposition` plus the encoding statistics to merge;
    -- On the parallel path this phase wraps only `coreToSMT`/`collectVars`;
    -- the solver phases then run in the phase-2 dispatch and are recorded there.
    -- Snapshot the state for the phase closures (`mut` variables cannot be
    -- captured); the phase returns the advanced state to thread forward.
    let encState0 := encState
    let snapCache0 := snapCache
    let emState0 := emState
    let dischargeResult ←
      (pctx.withRepeatedPhase (m := EIO Message) "smtDischarge" do
      -- `encodeObligationToSMT` is pure, so it must go through the `*Pure` helper
      -- otherwise the compiler will evaluate it before the phase is entered.
      -- It advances over the obligation's history (encoding only the delta
      -- detection reports) and forks this obligation's result.
      let maybeTerms ← pctx.withRepeatedPhasePure "coreToSMT" fun _ =>
        encodeObligationToSMTCached E.factory encState0 origObligation prunedAxiomLabels snapCache0
      match maybeTerms with
      | .error err =>
        let result := { obligation,
                        outcome := .error (.encoding (toString err)),
                        verbose := options.verbose,
                        checkLevel := options.checkLevel,
                        checkMode := options.checkMode,
                        lexprModel := [] }
        -- Encoding failed mid-advance; the surviving snapshot keeps the state
        -- at its last good position (the next obligation re-detects from there).
        pure (ObligationDisposition.resolved result, (default : Statistics), encState0,
              snapCache0, emState0)
      | .ok ({ assumptions := assumptionTerms, varDefs, varDecls,
               goal := obligationTerm, ctx, stats := encStats }, encState', snapCache') =>
        -- Shared managed definitions can mention variables from unrelated
        -- obligations. Follow only the definitions reachable from this
        -- obligation before deciding which user variables to request in a
        -- counterexample.
        let varsInObligation ← pctx.withRepeatedPhasePure "collectVars" fun _ =>
          collectModelVars obligation varDefs varDecls
        let typedVarsInObligation ← varsInObligation.mapM
          (fun (v,ty) => do
            match ty with
            | .some ty => return (v,LTy.forAll [] ty)
            | .none => throw (Message.fromString s!"{v} untyped"))
        if useParallel then
          -- Prepared only; the phase-2 dispatch solves it later.
          let job : SolverJob := {
            obligation, assumptionTerms, obligationTerm, ctx,
            needSatCheck, needValCheck, peSatResult?, peValResult?,
            typedVarsInObligation, varDefs, varDecls, prunedAxiomLabels }
          -- Capture is sequential-path only; `emState0` is left untouched.
          pure (ObligationDisposition.deferred job, encStats, encState', snapCache', emState0)
        else
          let (emState1, captured) ← pctx.withRepeatedPhase "renderSMTText" do
            match emState0 with
            | none => pure (none, none)
            | some es => IO.toEIO (fun e => Message.fromFormat f!"{e}") do
              let (es, cf) ← es.syncAndEmit E.factory encState'.frames
                encState'.current.ctx (pruned := !prunedAxiomLabels.isEmpty)
                ctx obligationTerm obligation.metadata obligation.label
                (managedNameSet varDefs varDecls) (definedNameSet varDefs) needSatCheck
                needValCheck
              pure (some es, cf)
          let discharge := mkDischarge options counter tempDir
            typedVarsInObligation obligation.metadata obligation.label (some termCache)
            captured pctx
          let result ← getObligationResult assumptionTerms obligationTerm ctx obligation p options
                        discharge needSatCheck needValCheck (externalPhases ++ corePhases)
                        (varDefinitions := varDefs) (varDeclarations := varDecls)
                        (prunedAxiomLabels := prunedAxiomLabels)
          -- Merge evaluator results with solver results
          let result := match result.outcome with
            | .ok solverOutcome =>
              let satResult := peSatResult?.getD solverOutcome.satisfiabilityProperty
              let valResult := peValResult?.getD solverOutcome.validityProperty
              { result with outcome := .ok { solverOutcome with
                  satisfiabilityProperty := satResult,
                  validityProperty := valResult } }
            | .error _ => result
          pure (ObligationDisposition.resolved result, encStats, encState', snapCache', emState1)
      ).toBaseIO
    let (disposition, encStats, encStateNext, snapCacheNext, emStateNext) ←
      match dischargeResult with
      | .ok result => pure result
      | .error err => throw err
    encState := encStateNext
    snapCache := snapCacheNext
    emState := emStateNext
    stats := stats.merge encStats
    match disposition with
    | .resolved result =>
      results := results.push result
      if result.isNotSuccess then
        if options.verbose >= .debug then
          let prog := f!"\n\n[DEBUG] Evaluated program:\n{Core.formatProgram p}"
          dbg_trace f!"\n\nResult: {result}\n{prog}"
        if options.stopOnFirstError then break
    | .deferred job =>
      solverJobs := job :: solverJobs
      solverJobIndices := results.size :: solverJobIndices
      results := results.push { obligation, outcome := .error (.encoding "pending parallel dispatch"),
                                verbose := options.verbose, checkLevel := options.checkLevel,
                                checkMode := options.checkMode, lexprModel := [] }
  -- Phase 2: Parallel solver dispatch
  if useParallel && !solverJobs.isEmpty then
    let phases := externalPhases ++ corePhases
    let jobResults ← IO.toEIO (fun e => Message.fromFormat f!"{e}")
      (dispatchJobsParallel solverJobs.reverse p options counter tempDir phases options.parallelWorkers mkDischarge pctx)
    let mut firstError : Option Message := none
    for (jobResult?, jobIdx) in jobResults.zip solverJobIndices.reverse do
      match jobResult? with
      | some (.ok result) =>
        results := results.setIfInBounds jobIdx result
      | some (.error diag) =>
        if firstError.isNone then firstError := some diag
      | none => pure ()
    if let some diag := firstError then throw diag
  return (results, stats)

/-- The obligations `extractObligations` reads from a program, with the unused CSE definitions
    dropped from every one of them when one holds a string literal SMT-LIB cannot spell. -/
def obligationsOf (oblProgram : Program) :
    Except Message (ProofObligations Expression) :=
  match Core.ObligationExtraction.extractObligations oblProgram with
  | .ok obs =>
    -- Per-obligation pruning changes the shared oldest frame and defeats
    -- prefix reuse. Pay that cost only when it isolates a CSE definition
    -- whose string literal cannot be serialized for SMT-LIB.
    if obs.any hasUnsupportedStringCSEDefinition
    then .ok (obs.map pruneUnusedCSEDefinitions)
    else .ok obs
  | .error e => .error (Message.fromFormat f!"ObligationExtraction error: {e}")

private
def verifySingleEnv (oblProgram : Program)
    (factory : @Lambda.Factory CoreLParams)
    (options : VerifyOptions)
    (counter : IO.Ref Nat) (tempDir : System.FilePath)
    (axiomCache : Option IrrelevantAxioms.Cache := .none)
    (axiomNames : List String := [])
    (axiomProgram : Option Program := .none)
    (externalPhases : List AbstractedPhase := [])
    (corePhases : List AbstractedPhase := coreAbstractedPhases)
    (mkDischarge : MkDischargeFn := mkDischargeFn)
    (pctx : PipelineContext) :
    EIO Message (VCResults × Statistics) := do
  -- Build SMT encoding context from the obligations program itself
  let E ← EIO.ofExcept
    (Core.buildEnv options oblProgram factory (registerCustomFunctions := true) |>.map (·.1))
  let obligations ← EIO.ofExcept (obligationsOf oblProgram)
  dischargeObligations E obligations options counter tempDir axiomCache axiomNames axiomProgram
    externalPhases corePhases mkDischarge pctx

/-- Construct the default `CoreSMTSolver` that discharges obligations
    sequentially using the batch or incremental SMT-LIB backend (selected
    by `options.incremental`). This is the standard solver used by
    `verifyPipeline` when no custom solver is provided. -/
def mkDefaultCoreSMTSolver
    (options : VerifyOptions)
    (counter : IO.Ref Nat) (tempDir : System.FilePath)
    (axiomCache : Option IrrelevantAxioms.Cache := .none)
    (axiomNames : List String := [])
    (axiomProgram : Option Program := .none)
    (externalPhases : List AbstractedPhase := [])
    (corePhases : List AbstractedPhase := coreAbstractedPhases)
    (mkDischarge : MkDischargeFn := mkDischargeFn)
    (pctx : PipelineContext) :
    CoreSMTSolver :=
  fun factory oblProgram =>
    verifySingleEnv oblProgram factory options counter tempDir axiomCache
      axiomNames axiomProgram externalPhases corePhases
      (mkDischarge := mkDischarge) pctx

/-- Run the Strata Core verification pipeline on a program: transform,
type-check, partially evaluate, and discharge proof obligations via SMT, on
`solver` when given and otherwise one obligation at a time. `Core.verify` chooses
`solver`, the obligation-tree walk under `--incremental`, and calls this.
All program-wide transformations that occur before any analyses
(including type inference) should be placed here.

When `options.keepAllFilesPrefix` is set, the program state after each pipeline
phase is written to `{prefix}.{n}.{phaseName}.core.st` (numbered from 1).

When `pipelineCtx` is provided, its `outputMode` — not `options.profile` —
drives all profiling output. Callers that want profiling should supply a context whose `outputMode`
`showsProfiling`; `options.profile` only decides the `outputMode` of the
context created internally when `pipelineCtx` is `none`. -/
def verifyPipeline (program : Program)
    (tempDir : System.FilePath)
    (options : VerifyOptions := VerifyOptions.default)
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default)
    (externalPhases : List AbstractedPhase := [])
    (entryFacts : ProgramFactSet := ProgramFactSet.empty)
    (pipeline : Option (ValidatedPipeline entryFacts) := none)
    (entryFactsHold : entryFacts.holds program :=
      by exact _root_.Core.ProgramFactSet.empty_holds _)
    (solver : Option CoreSMTSolver := none)
    (mkDischarge : MkDischargeFn := mkDischargeFn)
    (pipelineCtx : Option PipelineContext := none)
    : EIO Message VCResults := do
  -- `entryFactsHold` is the caller's proof that `entryFacts` holds of `program`.
  -- It carries the soundness obligation for an assumed-facts pipeline and has no
  -- runtime role, so it is not referenced below.
  let _ := entryFactsHold
  let pctx ← match pipelineCtx with
    | some ctx => pure ctx
    | none =>
      let mode := if options.profile then Strata.Pipeline.OutputMode.profile else .quiet
      (PipelineContext.create (outputMode := mode) : BaseIO _)
  let profile := pctx.outputMode.showsProfiling

  let factory ← EIO.ofExcept (Core.Factory.addFactory moreFns)
  -- The transforms that run and the phases that adjust solver results both come
  -- from the validated pipeline, so the two cannot drift apart. A pipeline's type
  -- carries only that its phases compose, not what they deliver, so what the back
  -- end needs is checked here for every pipeline, however it was built.
  let pipelinePhases ← match pipeline with
    | some vp =>
      match Strata.Pipeline.missingFacts backEndRequiredFacts vp.establishes with
      | [] => pure vp.phases
      | missing =>
        throw (Message.fromFormat f!"❌ This pipeline does not deliver what the \
          verification back end requires.\nMissing: \
          {", ".intercalate (missing.map (·.name))}")
    | none =>
      match coreValidatedPipeline options moreFns with
      | .ok vp => pure vp.phases
      | .error err =>
        throw (Message.fromFormat f!"❌ Cannot assemble a verification pipeline.\n{err}")
  -- `recursiveAxioms` decides from `recursiveFnsAsDefineFunRec` whether the back end needs
  -- the axioms, so it must read the options the back end runs with, whatever options the
  -- caller built the phase with. Otherwise the solver could get neither the axioms nor a
  -- `define-fun-rec` definition. Its contract does not depend on the options, so the
  -- rebuilt phase composes exactly as the one it replaces.
  let pipelinePhases := pipelinePhases.map fun p =>
    if p.phase.name == (recursiveAxiomsPhase).phase.name then recursiveAxiomsPhase options
    else p
  let phases := pipelinePhases.map (·.phase)
  let (oblProgram, factory, pipelineStats) ← pctx.withPhase "programTransformations" do
    let (prog, state) ← runTransforms program pipelinePhases
      (initState := { Transform.CoreTransformState.emp with factory := factory })
      (pipelineCtx := some pctx)
      (keepAllFilesPrefix := options.keepAllFilesPrefix)
    pure (prog, state.factory, state.statistics)
  let allStats := pipelineStats
  let axiomNames := program.decls.filterMap fun decl =>
    match decl with | .ax a _ => some a.name | _ => none
  let axiomCache? ← pctx.withPhasePure "buildAxiomCache" fun _ =>
    axiomCacheFor options.removeIrrelevantAxioms program
  let counter ← IO.toEIO (fun e => Message.fromFormat f!"{e}") (IO.mkRef 0)
  let VCss ← pctx.withPhase "vcDischarge" do
    if options.checkOnly then
      pure []
    else
      match solver with
      | none =>
        let coreSMTSolver := mkDefaultCoreSMTSolver options counter tempDir axiomCache?
          axiomNames (axiomProgram := program) externalPhases phases
          (mkDischarge := mkDischarge) pctx
        pure [← coreSMTSolver factory oblProgram]
      | some coreSMTSolver =>
        -- A back end passed in does not know which phases produced the program it is given,
        -- so its models are validated here, against the phases the default back end validates
        -- them against, so a `sat` a phase cannot vouch for reports as `unknown`.
        let (results, stats) ← coreSMTSolver factory oblProgram
        pure [(results.map (·.validateModels (externalPhases ++ phases)), stats)]
  let allStats := VCss.foldl (fun acc (_, s) => acc.merge s) allStats
  if profile then
    let _ ← (IO.println allStats.format |>.toBaseIO)
  let results : VCResults := (VCss.map (·.fst)).toArray.flatten
  return results.mergeByAssertion

end -- public section
end Core
---------------------------------------------------------------------

namespace Strata

open Lean.Parser
open Strata (Message FileRange)
open StrataDDM (Program)

public section

def typeCheck (ictx : InputContext) (env : Program) (options : Core.VerifyOptions := Core.VerifyOptions.default)
    (moreFns : @Lambda.Factory Core.CoreLParams := Lambda.Factory.default) :
  Except Message Core.Program := do
  let (program, errors) := TransM.run ictx (translateProgram env)
  if errors.isEmpty then
    Core.Factory.addFactory moreFns >>= (Core.typeCheck options program ·)
  else
    .error <| Message.fromFormat s!"DDM Transform Error: {repr errors}"

def Core.getProgram
  (p : StrataDDM.Program)
  (ictx : InputContext := Inhabited.default) : Core.Program × Array String :=
  TransM.run ictx (translateProgram p)

def toMessage (vcr : Core.VCResult)
    (phases : List Core.AbstractedPhase := []) : Option Message :=
  let fileRange := (Imperative.getFileRange vcr.obligation.metadata).getD default
  match vcr.outcome with
  | .error err =>
    let diagType := match err with
      | .solverTimeout _ => MessageKind.warning
      | _ => MessageKind.strataBug
    some { fileRange, message := s!"analysis error: {err}", kind := diagType }
  | .ok outcome =>
    let message? : Option String :=
      if vcr.obligation.property == .cover then
        let description := vcr.obligation.metadata.getPropertySummary.getD "cover property"
        if outcome.isSatisfiable || outcome.passReachabilityUnknown then none
        else if outcome.unreachable then some s!"{description} is unreachable in this context"
        else if outcome.isPass then none
        else some s!"{description} is not satisfiable"
      else
        let phaseDescription := phases.findSome? (·.getAssertDescription vcr.obligation.label)
        let description := vcr.obligation.metadata.getPropertySummary.getD
          (phaseDescription.getD "assertion")
        if outcome.unreachable then some s!"{description} holds vacuously (unreachable in this context)"
        else if outcome.isPass || outcome.isSatisfiable || outcome.passReachabilityUnknown then none
        else if outcome.alwaysFalseAndReachable || outcome.canBeTrueOrFalseAndIsReachable || outcome.canBeFalseAndIsReachable then
          some s!"{description} does not hold"
        else some s!"{description} could not be proved"
    message?.map fun message => { fileRange, message, kind := MessageKind.userError }

structure Diagnostic where
  start : Lean.Position
  ending : Lean.Position
  message : String
  type : MessageKind
  deriving Repr, BEq, Lean.ToExpr

def Pipeline.Message.toDiagnostic (files: Map Strata.Uri Lean.FileMap) (dm: Message): Diagnostic :=
  let fileMap := (files.find? dm.fileRange.file).getD
    (dbg_trace s!"Could not find {repr dm.fileRange.file} in {repr files.keys} when converting model '{dm}' to a diagnostic"; default)
  let startPos := fileMap.toPosition dm.fileRange.range.start
  let endPos := fileMap.toPosition dm.fileRange.range.stop
  {
    start := { line := startPos.line, column := startPos.column }
    ending := { line := endPos.line, column := endPos.column }
    message := dm.message
    type := dm.kind
  }

end -- public section
end Strata

---------------------------------------------------------------------
