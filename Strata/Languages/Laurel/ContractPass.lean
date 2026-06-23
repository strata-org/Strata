/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.LaurelPass
import Strata.Languages.Laurel.EliminateReturnStatements
import Strata.Util.Tactics

/-!
## Contract Pass (Laurel → Laurel)

Removes pre- and postconditions from all procedures and replaces them with
explicit precondition/postcondition helper procedures, assumptions, and
assertions.

For each procedure with contracts:
- Generate a separate precondition procedure (`foo$pre0`, `foo$pre1`, ...) for each precondition.
- Generate a separate postcondition procedure (`foo$post0`, `foo$post1`, ...) for each postcondition.
  Each takes all inputs and all outputs as parameters and returns the condition.
- Insert `assume foo$pre0(inputs); assume foo$pre1(inputs); ...` at the start of the body.
- Insert `assert foo$post0(inputs, outputs); assert foo$post1(inputs, outputs); ...` at the end of the body.

For each call to a contracted procedure:
- Assign all input arguments to temporary variables before the call.
- Insert `assert foo$pre0(temps); assert foo$pre1(temps); ...` before the call.
- After the call, insert `assume foo$post0(temps, outputs); assume foo$post1(temps, outputs); ...`.
-/

namespace Strata.Laurel

public section

private def mkMd (e : StmtExpr) : StmtExprMd := { val := e, source := none }
private def mkVarMd (v : Variable) : VariableMd := { val := v, source := none }

/-- Name for the i-th precondition helper procedure. -/
def preCondProcName (procName : String) (i : Nat) : String := s!"{procName}$pre{i}"

/-- Name for the i-th postcondition helper procedure. -/
def postCondProcName (procName : String) (i : Nat) : String := s!"{procName}$post{i}"

/-- Get postconditions from a procedure body. -/
private def getPostconditions (body : Body) : List Condition :=
  match body with
  | .Opaque postconds _ _ => postconds
  | .Abstract postconds => postconds
  | _ => []

/-- Build a call expression. -/
private def mkCall (callee : String) (args : List StmtExprMd) : StmtExprMd :=
  mkMd (.StaticCall (mkId callee) args)

/-- Convert parameters to identifier expressions. -/
private def paramsToArgs (params : List Parameter) : List StmtExprMd :=
  params.map fun p => mkMd (.Var (.Local p.name))

/-- Build a helper function for a single condition over the given parameters.
    Preconditions pass `proc.inputs`; postconditions use `mkPostConditionProc`. -/
private def mkConditionProc (name : String) (params : List Parameter)
    (condition : Condition) : Procedure :=
  { name := mkId name
    inputs := params
    outputs := [⟨mkId "$result", { val := .TBool, source := none }⟩]
    preconditions := []
    decreases := none
    body := .Transparent condition.condition }

/-- Suffix appended to a procedure's output-parameter names when they are lowered
    into a postcondition helper *function*.

    A postcondition helper takes both the procedure's inputs and outputs as plain
    function parameters. When an output shares a name with an input (e.g. an inout
    `$heap`, which the heap-parameterization pass lists in both `inputs` and
    `outputs`), the two would collide in the helper's single parameter scope and
    produce "Duplicate definition '…' is already defined in this scope". Suffixing
    every output keeps the two distinct. The choice is heap-agnostic: it applies to
    all outputs, not just `$heap`. -/
public def outParamSuffix : String := "$out"

/-- Rewrite a postcondition body so it refers to the renamed output parameters.

    In a postcondition, a bare reference to an output parameter denotes its
    post-state value, while `old(x)` denotes the pre-state value of an inout
    parameter (the corresponding *input*). The helper is a pure function with two
    distinct parameters, so:
    - bare `Var (Local n)` where `n` is an output → suffixed name (`n ++ outParamSuffix`)
    - `old(Var (Local n))` → `Var (Local n)`, i.e. strip `old` and keep the
      un-suffixed name so it resolves to the input parameter (functions have no
      two-state semantics, so an unstripped `old` would later be rejected).

    `pushOldInward` guarantees every `old` immediately wraps a local variable. -/
private def renameOutputsInPostExpr (outputNames : List String) (expr : StmtExprMd) : StmtExprMd :=
  let suffixIfOutput (n : Identifier) : Identifier :=
    if outputNames.contains n.text then mkId (n.text ++ outParamSuffix) else n
  mapStmtExprPrePostM (m := Id)
    (fun e =>
      match e.val with
      | .Old value =>
        match value.val with
        | .Var (.Local _) => some value
        | _ => none
      | _ => none)
    (fun e =>
      match e.val with
      | .Var (.Local n) => ⟨.Var (.Local (suffixIfOutput n)), e.source⟩
      | _ => e)
    expr

/-- Build a postcondition helper function over the procedure's inputs and outputs.
    Output parameters are renamed (see `outParamSuffix`) to avoid colliding with
    identically-named inputs, and the condition body is rewritten to match. -/
private def mkPostConditionProc (name : String) (inputs outputs : List Parameter)
    (condition : Condition) : Procedure :=
  let outputNames := outputs.map (·.name.text)
  let renamedOutputs := outputs.map (fun p => { p with name := mkId (p.name.text ++ outParamSuffix) })
  { name := mkId name
    inputs := inputs ++ renamedOutputs
    outputs := [⟨mkId "$result", { val := .TBool, source := none }⟩]
    preconditions := []
    decreases := none
    body := .Transparent (renameOutputsInPostExpr outputNames condition.condition) }

/-- Information about a procedure's contracts. -/
private structure ContractInfo where
  preNames : List (String × Option String)  -- (procName, summary) for each precondition
  postNames : List (String × Option String) -- (procName, summary) for each postcondition
  inputParams : List Parameter
  outputParams : List Parameter

private def ContractInfo.hasPreCondition (info : ContractInfo) : Bool := !info.preNames.isEmpty
private def ContractInfo.hasPostCondition (info : ContractInfo) : Bool := !info.postNames.isEmpty

/-- Collect contract info for all procedures with contracts. -/
private def collectContractInfo (procs : List Procedure) : Std.HashMap String ContractInfo :=
  procs.foldl (fun m proc =>
    let postconds := getPostconditions proc.body
    let hasPre := !proc.preconditions.isEmpty
    let hasPost := !postconds.isEmpty
    if hasPre || hasPost then
      let preNames := proc.preconditions.zipIdx.map fun (c, i) =>
        (preCondProcName proc.name.text i, c.summary)
      let postNames := postconds.zipIdx.map fun (c, i) =>
        (postCondProcName proc.name.text i, c.summary)
      m.insert proc.name.text {
        preNames := preNames
        postNames := postNames
        inputParams := proc.inputs
        outputParams := proc.outputs
      }
    else m) {}

/-- Transform a procedure body to add assume/assert for its own contracts. -/
private def transformProcBody (proc : Procedure) (info : ContractInfo) : Body :=
  let inputArgs := paramsToArgs proc.inputs
  let postconds := getPostconditions proc.body
  let preAssumes : List StmtExprMd :=
    proc.preconditions.zip info.preNames |>.map fun (pc, name, _) =>
      ⟨.Assume (mkCall name inputArgs), pc.condition.source⟩
  let postAsserts : List StmtExprMd :=
    postconds.zip info.postNames |>.map fun (pc, _name, _summary) =>
      let summary := pc.summary.getD "postcondition"
      ⟨.Assert { condition := pc.condition, summary := some summary }, pc.condition.source⟩
  match proc.body with
  | .Transparent body =>
    .Transparent ⟨.Block (preAssumes ++ [body] ++ postAsserts) none, body.source⟩
  | .Opaque _ (some impl) _ =>
    .Opaque [] (some ⟨.Block (preAssumes ++ [impl] ++ postAsserts) none, impl.source⟩) []
  | .Opaque _ none mods =>
    .Opaque [] none mods
  | .Abstract _ =>
    .Abstract []
  | b => b

/-- Monad used by the contract-pass rewriter; carries a global counter for
    generating fresh temporary variable names. -/
private abbrev ContractM := StateM Nat

/-- Allocate a fresh temporary name with the `$cp_` prefix.  The global counter
    guarantees uniqueness across the entire pass. -/
private def freshTemp : ContractM String := do
  let n ← get
  set (n + 1)
  return s!"$cp_{n}"

/-- Generate temporary variable assignments for input arguments at a call site.
    Returns (temp declarations+assignments, temp variable references). -/
private def mkTempAssignments (args : List StmtExprMd)
    (inputParams : List Parameter) (src : Option FileRange)
    : ContractM (List StmtExprMd × List StmtExprMd) := do
  let mut decls : List StmtExprMd := []
  let mut refs : List StmtExprMd := []
  for arg in args, i in List.range args.length do
    let tempName ← freshTemp
    let paramType := match inputParams[i]? with
      | some p => p.type
      | none => { val := .Unknown, source := none }
    let param : Parameter := { name := mkId tempName, type := paramType }
    decls := decls ++ [⟨StmtExpr.Assign [mkVarMd (.Declare param)] arg, src⟩]
    refs := refs ++ [mkMd (.Var (.Local (mkId tempName)))]
  return (decls, refs)

/-- Generate precondition checks (one per precondition) for a call site. -/
private def mkPreChecks (info : ContractInfo)
    (tempRefs : List StmtExprMd) (src : Option FileRange) : List StmtExprMd :=
  if !info.hasPreCondition then []
  else info.preNames.map fun (name, summary) =>
    let call := mkCall name tempRefs
    ⟨.Assert { condition := call, summary := some (summary.getD "precondition") }, src⟩

/-- Generate postcondition assumes (one per postcondition) for a call site. -/
private def mkPostAssumes (info : ContractInfo)
    (tempRefs : List StmtExprMd) (outputArgs : List StmtExprMd) (src : Option FileRange) : List StmtExprMd :=
  if !info.hasPostCondition then []
  else info.postNames.map fun (name, _) =>
    ⟨.Assume (mkCall name (tempRefs ++ outputArgs)), src⟩

/-- Names of the callee's inout parameters: those appearing in both the input and
    output lists. By the Laurel inout convention an inout is declared by giving the
    input and output the same name, so at a call site the inout argument is the same
    variable as the corresponding output target — and the Core lowering relies on
    that identity. -/
private def ContractInfo.inoutNames (info : ContractInfo) : List String :=
  info.inputParams.filterMap fun p =>
    if info.outputParams.any (·.name.text == p.name.text) then some p.name.text else none

/-- Build the positional argument list for the rewritten call.

    Ordinary inputs are passed via their snapshot temp (so pre/postconditions can
    reference the pre-call value). Inout inputs, however, are passed as the
    *original* argument variable rather than the temp: the call mutates that
    variable in place, so it must coincide with the corresponding output target
    (the Laurel inout invariant). The temp is still created and used by
    `mkPostAssumes` to supply the inout's pre-state to `$post*`. -/
private def mkCallArgs (info : ContractInfo) (origArgs tempRefs : List StmtExprMd) : List StmtExprMd :=
  let inout := info.inoutNames
  tempRefs.zipIdx.map fun (tempRef, i) =>
    match info.inputParams[i]? with
    | some p => if inout.contains p.name.text then origArgs[i]?.getD tempRef else tempRef
    | none => tempRef

/-- Rewrite call sites in a statement/expression tree. -/
private def rewriteCallSites (contractInfoMap : Std.HashMap String ContractInfo)
    (expr : StmtExprMd) : ContractM StmtExprMd := do
  let rewriteStaticCall (callee : Identifier) (args : List StmtExprMd)
      (info : ContractInfo) (src : Option FileRange)
      : ContractM (List StmtExprMd) := do
    let (tempDecls, tempRefs) ← mkTempAssignments args info.inputParams src
    let preCheck := mkPreChecks info tempRefs src
    let (callStmt, postAssume, returnValue) ←
      if info.hasPostCondition && !info.outputParams.isEmpty then do
        let mut outputTempDecls : List VariableMd := []
        let mut outputRefs : List StmtExprMd := []
        for p in info.outputParams do
          let tempName ← freshTemp
          outputTempDecls := outputTempDecls ++ [mkVarMd (.Declare { name := mkId tempName, type := p.type })]
          outputRefs := outputRefs ++ [mkMd (.Var (.Local (mkId tempName)))]
        let callWithOutputs : StmtExprMd :=
          ⟨.Assign outputTempDecls ⟨.StaticCall callee tempRefs, src⟩, src⟩
        let assume := mkPostAssumes info tempRefs outputRefs src
        let retVal : List StmtExprMd := match outputRefs with
          | [single] => [single]
          | _ => []
        pure (callWithOutputs, assume, retVal)
      else
        pure (⟨.StaticCall callee tempRefs, src⟩, [], [])
    return tempDecls ++ preCheck ++ [callStmt] ++ postAssume ++ returnValue
  let result ←
    mapStmtExprFlattenM (m := ContractM)
      -- Pre: intercept Assign targets (StaticCall ...) before recursion
      (fun e => do
        match e.val with
        | .Assign targets (.mk (.StaticCall callee args) callSrc) =>
          match contractInfoMap.get? callee.text with
          | some info =>
            let src := e.source
            -- Recurse into arguments
            let args' ← args.mapM (mapStmtExprM (m := ContractM) (fun e' => do
              match e'.val with
              | .StaticCall callee' args' =>
                match contractInfoMap.get? callee'.text with
                | some info' =>
                  let stmts ← rewriteStaticCall callee' args' info' e'.source
                  return ⟨.Block stmts none, e'.source⟩
                | none => return e'
              | _ => return e'))
            let (tempDecls, tempRefs) ← mkTempAssignments args' info.inputParams src
            let callArgs := mkCallArgs info args' tempRefs
            let callWithTemps : StmtExprMd := ⟨.Assign targets ⟨.StaticCall callee callArgs, callSrc⟩, src⟩
            let preCheck := mkPreChecks info tempRefs src
            let outputArgs := targets.filterMap fun t =>
              match t.val with
              | .Local name => some (mkMd (.Var (.Local name)))
              | .Declare param => some (mkMd (.Var (.Local param.name)))
              | _ => none
            let postAssume := mkPostAssumes info tempRefs outputArgs src
            return some (tempDecls ++ preCheck ++ [callWithTemps] ++ postAssume)
          | none => return none
        | _ => return none)
      -- Post: handle bare StaticCall
      (fun e => do
        match e.val with
        | .StaticCall callee args =>
          match contractInfoMap.get? callee.text with
          | some info =>
            let stmts ← rewriteStaticCall callee args info e.source
            return stmts
          | none => return [e]
        | _ => return [e]) expr
  return result

/-- Rewrite call sites in all bodies of a procedure. -/
private def rewriteCallSitesInProc (contractInfoMap : Std.HashMap String ContractInfo)
    (proc : Procedure) : ContractM Procedure := do
  let rw := rewriteCallSites contractInfoMap
  match proc.body with
  | .Transparent body =>
    let body' ← rw body
    return { proc with body := .Transparent body' }
  | .Opaque posts impl mods =>
    let posts' ← posts.mapM (·.mapM rw)
    let impl' ← impl.mapM rw
    let mods' ← mods.mapM rw
    return { proc with body := Body.Opaque posts' impl' mods' }
  | _ => return proc

/-- Conjoin a list of conditions into a single expression with `&&`. -/
private def conjoin (conds : List Condition) : Option StmtExprMd :=
  match conds.map (·.condition) with
  | [] => none
  | e :: rest => some (rest.foldl (fun acc x => mkMd (.PrimitiveOp .And [acc, x])) e)

/-- Build an axiom expression from `invokeOn` trigger and ensures clauses.
    Produces `∀ p1, ∀ p2, ..., ∀ pn :: { trigger } (preconds => ensures)`.
    The trigger controls when the SMT solver instantiates the axiom. -/
private def mkInvokeOnAxiom (params : List Parameter) (trigger : StmtExprMd)
    (preconds : List Condition) (postconds : List Condition) : StmtExprMd :=
  let ensures := (conjoin postconds).getD (mkMd (.LiteralBool true))
  let body := match conjoin preconds with
    | some pre => mkMd (.PrimitiveOp .Implies [pre, ensures])
    | none => ensures
  -- Wrap in nested Forall from last param (innermost) to first (outermost).
  -- The trigger is placed on the innermost quantifier.
  params.foldr (init := (body, true)) (fun p (acc, isInnermost) =>
    let trig := if isInnermost then some trigger else none
    (mkMd (.Quantifier .Forall p trig acc), false)) |>.1

/-- Check whether a `StmtExprMd` tree mentions a local variable by name. -/
private def exprMentions (name : String) (expr : StmtExprMd) : Bool :=
  match expr with
  | AstNode.mk val _ =>
  match val with
  | .Var (.Local id) => id.text == name
  | .StaticCall _ args => args.attach.any (fun x => exprMentions name x.val)
  | .PrimitiveOp _ args _ => args.attach.any (fun x => exprMentions name x.val)
  | .IfThenElse c t e => exprMentions name c || exprMentions name t ||
      match e with | some el => exprMentions name el | none => false
  | .Block stmts _ => stmts.attach.any (fun x => exprMentions name x.val)
  | .Quantifier _ _ trigger body => exprMentions name body ||
      match trigger with | some t => exprMentions name t | none => false
  | .ReferenceEquals l r => exprMentions name l || exprMentions name r
  | .Assign _ v => exprMentions name v
  | .Old v => exprMentions name v
  | .Fresh v => exprMentions name v
  | .Assume c => exprMentions name c
  | .Assert c => exprMentions name c.condition
  | .Return (some v) => exprMentions name v
  | .InstanceCall t _ args => exprMentions name t || args.attach.any (fun x => exprMentions name x.val)
  | .AsType t _ => exprMentions name t
  | .IsType t _ => exprMentions name t
  | .PureFieldUpdate t _ v => exprMentions name t || exprMentions name v
  | .ProveBy v p => exprMentions name v || exprMentions name p
  | .ContractOf _ f => exprMentions name f
  | .Assigned n => exprMentions name n
  | _ => false
  termination_by expr
  decreasing_by
    all_goals (try cases x)
    all_goals (try simp_all)
    all_goals (try have := Condition.sizeOf_condition_lt ‹_›)
    all_goals (try term_by_mem)
    all_goals omega

/-- Emit a diagnostic if an `invokeOn` procedure has postconditions referencing
    output parameters (which are not quantified in the axiom). -/
private def invokeOnOutputRefError (proc : Procedure) : Option DiagnosticModel :=
  if proc.invokeOn.isNone then none else
    let postconds := getPostconditions proc.body
    let referenced := proc.outputs.filterMap (fun out =>
      if postconds.any (fun c => exprMentions out.name.text c.condition)
      then some out.name.text else none)
    match referenced with
    | [] => none
    | names => some (diagnosticFromSource proc.name.source
        s!"'invokeOn' procedure '{proc.name.text}' has an ensures referencing its output(s) ({String.intercalate ", " names}); the auto-invocation axiom is quantified over inputs only."
        DiagnosticType.UserError)

/-- Run the contract pass on a Laurel program.
    All procedures with contracts are transformed. -/
def lowerContracts (program : Program) : Program × List DiagnosticModel :=
  let contractInfoMap := collectContractInfo program.staticProcedures

  -- Check for output-referencing ensures in invokeOn procedures
  let diagnostics := program.staticProcedures.filterMap invokeOnOutputRefError

  -- Generate helper procedures for all procedures with contracts
  let helperProcs := program.staticProcedures.flatMap fun proc =>
    let postconds := getPostconditions proc.body
    let preProcs := proc.preconditions.zipIdx.map fun (c, i) =>
      mkConditionProc (preCondProcName proc.name.text i) proc.inputs c
    let postProcs := postconds.zipIdx.map fun (c, i) =>
      mkPostConditionProc (postCondProcName proc.name.text i) proc.inputs proc.outputs c
    preProcs ++ postProcs

  -- Transform procedures: strip contracts, add assume/assert, rewrite call sites
  -- Run all call-site rewriting in a single ContractM to share the global counter.
  let (transformedProcs, _) := (program.staticProcedures.mapM fun (proc : Procedure) => do
    let proc : Procedure := match proc.invokeOn with
      | some trigger =>
        let postconds := getPostconditions proc.body
        if postconds.isEmpty then { proc with invokeOn := none }
        else if invokeOnOutputRefError proc |>.isSome then
          -- Skip axiom generation; diagnostic already emitted
          { proc with invokeOn := none }
        else { proc with
          axioms := [mkInvokeOnAxiom proc.inputs trigger proc.preconditions postconds]
          invokeOn := none }
      | none => proc
    let proc : Procedure := match contractInfoMap.get? proc.name.text with
      | some info =>
        { proc with
          preconditions := []
          body := transformProcBody proc info }
      | none => proc
    -- Rewrite call sites in the procedure body
    rewriteCallSitesInProc contractInfoMap proc).run 0

  ({ program with staticProcedures := helperProcs ++ transformedProcs }, diagnostics)

public def contractPass : LoweringPass where
  name := "ContractPass"
  documentation := "Lowers pre and postcondition to assertions and assumptions around call-sites and procedure bodies"
  comesAfter := [⟨ eliminateReturnStatementsPass.meta, "The contract pass wraps the body of procedures to get: `assume preconditions; body; assert postconditions`. Eliminating returns first means that the postcondition assertions are guaranteed to execute."⟩ ]
  needsResolves := true
  run := fun p _m _ =>
    let (p', diags) := lowerContracts p
    (p', diags, {})

end -- public section
end Strata.Laurel
