/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr

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

/-- Build a helper function for a single condition. -/
private def mkConditionProc (name : String) (params : List Parameter)
    (condition : Condition) : Procedure :=
  { name := mkId name
    inputs := params
    outputs := [⟨mkId "$result", { val := .TBool, source := none }⟩]
    preconditions := []
    decreases := none
    isFunctional := true
    body := .Transparent condition.condition }

/-- Build a postcondition function for a single condition that takes all inputs
    and all outputs as parameters. -/
private def mkPostConditionProc (name : String)
    (inputParams : List Parameter) (outputParams : List Parameter)
    (condition : Condition) : Procedure :=
  let allParams := inputParams ++ outputParams
  { name := mkId name
    inputs := allParams
    outputs := [⟨mkId "$result", { val := .TBool, source := none }⟩]
    preconditions := []
    decreases := none
    isFunctional := true
    body := .Transparent condition.condition }

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
    if !proc.isFunctional && (hasPre || hasPost) then
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
  match proc.body with
  | .Transparent body =>
    let postAsserts : List StmtExprMd :=
      postconds.zip info.postNames |>.map fun (pc, _name, _summary) =>
        let summary := pc.summary.getD "postcondition"
        ⟨.Assert { condition := pc.condition, summary := some summary }, pc.condition.source⟩
    .Transparent ⟨.Block (preAssumes ++ [body] ++ postAsserts) none, body.source⟩
  | .Opaque _ (some impl) _ =>
    .Opaque postconds (some ⟨.Block (preAssumes ++ [impl]) none, impl.source⟩) []
  | .Opaque _ none mods =>
    .Opaque postconds none mods
  | .Abstract _ =>
    .Abstract postconds
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
private def mkPreChecks (info : ContractInfo) (isFunctional : Bool)
    (tempRefs : List StmtExprMd) (src : Option FileRange) : List StmtExprMd :=
  if !info.hasPreCondition then []
  else info.preNames.map fun (name, summary) =>
    let call := mkCall name tempRefs
    if isFunctional then
      ⟨.Assume call, src⟩
    else
      ⟨.Assert { condition := call, summary := some (summary.getD "precondition") }, src⟩

/-- Generate postcondition assumes (one per postcondition) for a call site. -/
private def mkPostAssumes (info : ContractInfo)
    (tempRefs : List StmtExprMd) (outputArgs : List StmtExprMd) (src : Option FileRange) : List StmtExprMd :=
  if !info.hasPostCondition then []
  else info.postNames.map fun (name, _) =>
    ⟨.Assume (mkCall name (tempRefs ++ outputArgs)), src⟩

/-- Rewrite call sites in a statement/expression tree. -/
private def rewriteCallSites (contractInfoMap : Std.HashMap String ContractInfo)
    (isFunctional : Bool) (expr : StmtExprMd) : ContractM StmtExprMd := do
  let rewriteStaticCall (callee : Identifier) (args : List StmtExprMd)
      (info : ContractInfo) (src : Option FileRange)
      : ContractM (List StmtExprMd) := do
    let (tempDecls, tempRefs) ← mkTempAssignments args info.inputParams src
    let preCheck := mkPreChecks info isFunctional tempRefs src
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
            let callWithTemps : StmtExprMd := ⟨.Assign targets ⟨.StaticCall callee tempRefs, callSrc⟩, src⟩
            let preCheck := mkPreChecks info isFunctional tempRefs src
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
  let rw := rewriteCallSites contractInfoMap proc.isFunctional
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

/-- Build an axiom expression from `invokeOn` trigger and ensures clauses.
    Produces `∀ p1, ∀ p2, ..., ∀ pn :: { trigger } (ensures1 && ensures2 && ...)`.
    The trigger controls when the SMT solver instantiates the axiom. -/
private def mkInvokeOnAxiom (params : List Parameter) (trigger : StmtExprMd)
    (postconds : List Condition) : StmtExprMd :=
  let body := match postconds.map (·.condition) with
    | [] => mkMd (.LiteralBool true)
    | [e] => e
    | e :: rest => rest.foldl (fun acc x => mkMd (.PrimitiveOp .And [acc, x])) e
  -- Wrap in nested Forall from last param (innermost) to first (outermost).
  -- The trigger is placed on the innermost quantifier.
  params.foldr (init := (body, true)) (fun p (acc, isInnermost) =>
    let trig := if isInnermost then some trigger else none
    (mkMd (.Quantifier .Forall p trig acc), false)) |>.1

/-- Run the contract pass on a Laurel program.
    All procedures with contracts are transformed. -/
def contractPass (program : Program) : Program :=
  let contractInfoMap := collectContractInfo program.staticProcedures

  -- Generate helper procedures for all procedures with contracts
  let helperProcs := (program.staticProcedures.filter (fun proc => !proc.isFunctional)).flatMap fun proc =>
    let postconds := getPostconditions proc.body
    let preProcs := proc.preconditions.zipIdx.map fun (c, i) =>
      mkConditionProc (preCondProcName proc.name.text i) proc.inputs c
    let postProcs := postconds.zipIdx.map fun (c, i) =>
      mkPostConditionProc (postCondProcName proc.name.text i)
        proc.inputs proc.outputs c
    preProcs ++ postProcs

  -- Transform procedures: strip contracts, add assume/assert, rewrite call sites
  -- Run all call-site rewriting in a single ContractM to share the global counter.
  let (transformedProcs, _) := (program.staticProcedures.mapM fun (proc : Procedure) => do
    if proc.isFunctional then
      return proc
    else
      let proc : Procedure := match proc.invokeOn with
        | some trigger =>
          let postconds := getPostconditions proc.body
          if postconds.isEmpty then { proc with invokeOn := none }
          else { proc with
            axioms := [mkInvokeOnAxiom proc.inputs trigger postconds]
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

  { program with staticProcedures := helperProcs ++ transformedProcs }

end -- public section
end Strata.Laurel
