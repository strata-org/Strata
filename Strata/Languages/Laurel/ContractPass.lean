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
- Generate a precondition procedure (`foo$pre`) returning the conjunction of preconditions.
- Generate a postcondition procedure (`foo$post`) that takes all inputs and all
  outputs as parameters and returns the conjunction of postconditions. It is
  marked as functional and does not call the original procedure.
- Insert `assume foo$pre(inputs)` at the start of the body.
- Insert `assert foo$post(inputs, outputs)` at the end of the body.

For each call to a contracted procedure:
- Assign all input arguments to temporary variables before the call.
- Insert `assert foo$pre(temps)` before the call (precondition check).
- After the call, insert `assume foo$post(temps, outputs)` (postcondition assumption).
-/

namespace Strata.Laurel

public section

private def mkMd (e : StmtExpr) : StmtExprMd := { val := e, source := none }
private def mkVarMd (v : Variable) : VariableMd := { val := v, source := none }

/-- Build a conjunction of expressions. Returns `LiteralBool true` for an empty list. -/
private def conjoin (exprs : List StmtExprMd) : StmtExprMd :=
  match exprs with
  | [] => mkMd (.LiteralBool true)
  | [e] => e
  | e :: rest => rest.foldl (fun acc x =>
      mkMd (.PrimitiveOp .And [acc, x])) e

/-- Name for the precondition helper procedure. -/
def preCondProcName (procName : String) : String := s!"{procName}$pre"

/-- Name for the postcondition helper procedure. -/
def postCondProcName (procName : String) : String := s!"{procName}$post"

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

/-- Build a helper function that returns the conjunction of the given conditions. -/
private def mkConditionProc (name : String) (params : List Parameter)
    (conditions : List Condition) : Procedure :=
  { name := mkId name
    inputs := params
    outputs := [⟨mkId "$result", { val := .TBool, source := none }⟩]
    preconditions := []
    decreases := none
    isFunctional := true
    body := .Transparent (conjoin (conditions.map (·.condition))) }

/-- Build a postcondition function that takes all inputs and all outputs as
    parameters and returns the conjunction of postconditions. The function is
    marked as functional and does not call the original procedure.

    For a procedure `foo(a, b) returns (x, y)` with postcondition `P(a, b, x, y)`,
    generates:
    ```
    function foo$post(a, b, x, y) returns ($result : bool) {
      P(a, b, x, y)
    }
    ```
-/
private def mkPostConditionProc (name : String)
    (inputParams : List Parameter) (outputParams : List Parameter)
    (conditions : List Condition) : Procedure :=
  let allParams := inputParams ++ outputParams
  { name := mkId name
    inputs := allParams
    outputs := [⟨mkId "$result", { val := .TBool, source := none }⟩]
    preconditions := []
    decreases := none
    isFunctional := false
    body := .Transparent (conjoin (conditions.map (·.condition))) }

/-- Extract a combined summary from a list of conditions. -/
private def combinedSummary (clauses : List Condition) : Option String :=
  let summaries := clauses.filterMap (·.summary)
  match summaries with
  | [] => none
  | [s] => some s
  | ss => some (String.intercalate ", " ss)

/-- Information about a procedure's contracts. -/
private structure ContractInfo where
  hasPreCondition : Bool
  hasPostCondition : Bool
  preName : String
  postName : String
  preSummary : Option String
  postSummary : Option String
  inputParams : List Parameter
  outputParams : List Parameter

/-- Collect contract info for all procedures with contracts. -/
private def collectContractInfo (procs : List Procedure) : Std.HashMap String ContractInfo :=
  procs.foldl (fun m proc =>
    let postconds := getPostconditions proc.body
    let hasPre := !proc.preconditions.isEmpty
    let hasPost := !postconds.isEmpty
    if !proc.isFunctional && (hasPre || hasPost) then
      m.insert proc.name.text {
        hasPreCondition := hasPre
        hasPostCondition := hasPost
        preName := preCondProcName proc.name.text
        postName := postCondProcName proc.name.text
        preSummary := combinedSummary proc.preconditions
        postSummary := combinedSummary postconds
        inputParams := proc.inputs
        outputParams := proc.outputs
      }
    else m) {}

/-- Transform a procedure body to add assume/assert for its own contracts. -/
private def transformProcBody (proc : Procedure) (info : ContractInfo) : Body :=
  let inputArgs := paramsToArgs proc.inputs
  let postconds := getPostconditions proc.body
  let preAssume : List StmtExprMd :=
    if info.hasPreCondition then
      let preSrc := match proc.preconditions.head? with
        | some pc => pc.condition.source
        | none => none
      [⟨.Assume (mkCall info.preName inputArgs), preSrc⟩]
    else []
  let postAssert : List StmtExprMd :=
    if info.hasPostCondition then
      postconds.map fun pc =>
        let summary := pc.summary.getD "postcondition"
        ⟨.Assert { condition := pc.condition, summary := some summary }, pc.condition.source⟩
    else []
  match proc.body with
  | .Transparent body =>
    .Transparent ⟨.Block (preAssume ++ [body] ++ postAssert) none, body.source⟩
  | .Opaque _ (some impl) _ =>
    .Opaque [] (some ⟨.Block (preAssume ++ [impl] ++ postAssert) none, impl.source⟩) []
  | .Opaque _ none mods =>
    .Opaque [] none mods
  | .Abstract _ =>
    .Abstract []
  | b => b

/-- Generate temporary variable assignments for input arguments at a call site.
    Returns (temp declarations+assignments, temp variable references).
    Uses the parameter types from the procedure's contract info so that
    resolution can type-check the generated temporaries.
    `callIdx` distinguishes multiple calls to the same procedure. -/
private def mkTempAssignments (args : List StmtExprMd) (calleeName : String)
    (inputParams : List Parameter) (callIdx : Nat) (src : Option FileRange)
    : List StmtExprMd × List StmtExprMd :=
  let indexed := args.zipIdx
  let decls := indexed.map fun (arg, i) =>
    let tempName := s!"${calleeName}${callIdx}$arg{i}"
    let paramType := match inputParams[i]? with
      | some p => p.type
      | none => { val := .Unknown, source := none }
    let param : Parameter := { name := mkId tempName, type := paramType }
    ⟨StmtExpr.Assign [mkVarMd (.Declare param)] arg, src⟩
  let refs := indexed.map fun (_, i) =>
    let tempName := s!"${calleeName}${callIdx}$arg{i}"
    mkMd (.Var (.Local (mkId tempName)))
  (decls, refs)

/-- Rewrite a single statement that may be a call to a contracted procedure.
    Returns a list of statements (the original plus any inserted assert/assume).
    Takes and returns a call counter for generating unique temp variable names.
    When `isFunctional` is true, precondition checks use `assume` instead of
    `assert` since asserts are not supported in functions during Core translation.

    At call sites:
    1. Assign input arguments to temporary variables.
    2. Assert precondition using temps.
    3. Execute the call using temps as arguments.
    4. Assume postcondition using temps + output variables. -/
private def rewriteStmt (contractInfoMap : Std.HashMap String ContractInfo)
    (isFunctional : Bool) (callCounter : Nat) (e : StmtExprMd) : List StmtExprMd × Nat :=
  let src := e.source
  let mkWithSrc (se : StmtExpr) : StmtExprMd := ⟨se, src⟩
  match e.val with
  | .Assign targets (.mk (.StaticCall callee args) callSrc) =>
    match contractInfoMap.get? callee.text with
    | some info =>
      let (tempDecls, tempRefs) := mkTempAssignments args callee.text info.inputParams callCounter src
      let callWithTemps : StmtExprMd := ⟨.Assign targets ⟨.StaticCall callee tempRefs, callSrc⟩, src⟩
      let preCheck := if info.hasPreCondition then
        if isFunctional then
          [mkWithSrc (.Assume (mkCall info.preName tempRefs))]
        else
          [mkWithSrc (.Assert { condition := mkCall info.preName tempRefs, summary := some (info.preSummary.getD "precondition") })]
        else []
      -- After the call, assume postcondition with temps (inputs) + output variables
      let outputArgs := targets.filterMap fun t =>
        match t.val with
        | .Local name => some (mkMd (.Var (.Local name)))
        | .Declare param => some (mkMd (.Var (.Local param.name)))
        | _ => none
      let postAssume := if info.hasPostCondition
        then [mkWithSrc (.Assume (mkCall info.postName (tempRefs ++ outputArgs)))] else []
      (tempDecls ++ preCheck ++ [callWithTemps] ++ postAssume, callCounter + 1)
    | none => ([e], callCounter)
  | .StaticCall callee args =>
    match contractInfoMap.get? callee.text with
    | some info =>
      let (tempDecls, tempRefs) := mkTempAssignments args callee.text info.inputParams callCounter src
      let preCheck := if info.hasPreCondition then
        if isFunctional then
          [mkWithSrc (.Assume (mkCall info.preName tempRefs))]
        else
          [mkWithSrc (.Assert { condition := mkCall info.preName tempRefs, summary := some (info.preSummary.getD "precondition") })]
        else []
      -- For bare calls with postconditions, capture outputs in temp variables
      -- so we can pass them to the $post function.
      let (callStmt, postAssume, returnValue) :=
        if info.hasPostCondition && !info.outputParams.isEmpty then
          let outputTempDecls := info.outputParams.zipIdx.map fun (p, i) =>
            let tempName := s!"${callee.text}${callCounter}$out{i}"
            mkVarMd (.Declare { name := mkId tempName, type := p.type })
          let callWithOutputs : StmtExprMd :=
            ⟨.Assign outputTempDecls ⟨.StaticCall callee tempRefs, src⟩, src⟩
          let outputRefs := info.outputParams.zipIdx.map fun (_, i) =>
            let tempName := s!"${callee.text}${callCounter}$out{i}"
            mkMd (.Var (.Local (mkId tempName)))
          let assume := [mkWithSrc (.Assume (mkCall info.postName (tempRefs ++ outputRefs)))]
          -- If the procedure has a single output, append the output variable
          -- reference so the expanded block evaluates to the call result
          -- (needed when the call appears in expression position).
          let retVal : List StmtExprMd := match outputRefs with
            | [single] => [single]
            | _ => []
          (callWithOutputs, assume, retVal)
        else
          (mkWithSrc (.StaticCall callee tempRefs), [], [])
      (tempDecls ++ preCheck ++ [callStmt] ++ postAssume ++ returnValue, callCounter + 1)
    | none => ([e], callCounter)
  | _ => ([e], callCounter)

/-- Rewrite call sites in a statement/expression tree. Uses `mapStmtExprFlattenM`:
    - `pre` intercepts `Assign targets (StaticCall ...)` to a contracted procedure,
      handling it directly so the assignment targets are used as output variables
      for the postcondition assume.
    - `post` handles bare `StaticCall` to a contracted procedure anywhere in the
      tree, returning the expanded list of statements (argument assignments,
      precondition assert, call, postcondition assume, output variable reference).
      For Block parents the list is flattened; for other parents it is wrapped
      in a Block. -/
private def rewriteCallSites (contractInfoMap : Std.HashMap String ContractInfo)
    (isFunctional : Bool) (expr : StmtExprMd) : StmtExprMd :=
  let rewriteStaticCall (counter : Nat) (callee : Identifier) (args : List StmtExprMd)
      (info : ContractInfo) (src : Option FileRange)
      : List StmtExprMd × Nat :=
    let mkWithSrc (se : StmtExpr) : StmtExprMd := ⟨se, src⟩
    let (tempDecls, tempRefs) := mkTempAssignments args callee.text info.inputParams counter src
    let preCheck := if info.hasPreCondition then
      if isFunctional then
        [mkWithSrc (.Assume (mkCall info.preName tempRefs))]
      else
        [mkWithSrc (.Assert { condition := mkCall info.preName tempRefs, summary := some (info.preSummary.getD "precondition") })]
      else []
    let (callStmt, postAssume, returnValue) :=
      if info.hasPostCondition && !info.outputParams.isEmpty then
        let outputTempDecls := info.outputParams.zipIdx.map fun (p, i) =>
          let tempName := s!"${callee.text}${counter}$out{i}"
          mkVarMd (.Declare { name := mkId tempName, type := p.type })
        let callWithOutputs : StmtExprMd :=
          ⟨.Assign outputTempDecls ⟨.StaticCall callee tempRefs, src⟩, src⟩
        let outputRefs := info.outputParams.zipIdx.map fun (_, i) =>
          let tempName := s!"${callee.text}${counter}$out{i}"
          mkMd (.Var (.Local (mkId tempName)))
        let assume := [mkWithSrc (.Assume (mkCall info.postName (tempRefs ++ outputRefs)))]
        let retVal : List StmtExprMd := match outputRefs with
          | [single] => [single]
          | _ => []
        (callWithOutputs, assume, retVal)
      else
        (mkWithSrc (.StaticCall callee tempRefs), [], [])
    (tempDecls ++ preCheck ++ [callStmt] ++ postAssume ++ returnValue, counter + 1)
  let (result, _) := StateT.run (s := (0 : Nat)) <|
    mapStmtExprFlattenM (m := StateM Nat)
      -- Pre: intercept Assign targets (StaticCall ...) before recursion
      (fun e => do
        match e.val with
        | .Assign targets (.mk (.StaticCall callee args) callSrc) =>
          match contractInfoMap.get? callee.text with
          | some info =>
            let counter ← get
            let src := e.source
            let mkWithSrc (se : StmtExpr) : StmtExprMd := ⟨se, src⟩
            -- Recurse into arguments using mapStmtExprM with the post logic
            let args' ← args.mapM (mapStmtExprM (m := StateM Nat) (fun e' => do
              match e'.val with
              | .StaticCall callee' args' =>
                match contractInfoMap.get? callee'.text with
                | some info' =>
                  let counter' ← get
                  let (stmts, counter'') := rewriteStaticCall counter' callee' args' info' e'.source
                  set counter''
                  return ⟨.Block stmts none, e'.source⟩
                | none => return e'
              | _ => return e'))
            let (tempDecls, tempRefs) := mkTempAssignments args' callee.text info.inputParams counter src
            let callWithTemps : StmtExprMd := ⟨.Assign targets ⟨.StaticCall callee tempRefs, callSrc⟩, src⟩
            let preCheck := if info.hasPreCondition then
              if isFunctional then
                [mkWithSrc (.Assume (mkCall info.preName tempRefs))]
              else
                [mkWithSrc (.Assert { condition := mkCall info.preName tempRefs, summary := some (info.preSummary.getD "precondition") })]
              else []
            let outputArgs := targets.filterMap fun t =>
              match t.val with
              | .Local name => some (mkMd (.Var (.Local name)))
              | .Declare param => some (mkMd (.Var (.Local param.name)))
              | _ => none
            let postAssume := if info.hasPostCondition
              then [mkWithSrc (.Assume (mkCall info.postName (tempRefs ++ outputArgs)))] else []
            set (counter + 1)
            return some (tempDecls ++ preCheck ++ [callWithTemps] ++ postAssume)
          | none => return none
        | _ => return none)
      -- Post: handle bare StaticCall (not direct RHS of Assign to contracted proc)
      (fun e => do
        match e.val with
        | .StaticCall callee args =>
          match contractInfoMap.get? callee.text with
          | some info =>
            let counter ← get
            let (stmts, counter') := rewriteStaticCall counter callee args info e.source
            set counter'
            return stmts
          | none => return [e]
        | _ => return [e]) expr
  result

/-- Rewrite call sites in all bodies of a procedure. -/
private def rewriteCallSitesInProc (contractInfoMap : Std.HashMap String ContractInfo)
    (proc : Procedure) : Procedure :=
  let rw := rewriteCallSites contractInfoMap proc.isFunctional
  match proc.body with
  | .Transparent body =>
    { proc with body := .Transparent (rw body) }
  | .Opaque posts impl mods =>
    let body := Body.Opaque (posts.map (·.mapCondition rw)) (impl.map rw) (mods.map rw)
    { proc with body := body }
  | _ => proc

/-- Build an axiom expression from `invokeOn` trigger and ensures clauses.
    Produces `∀ p1, ∀ p2, ..., ∀ pn :: { trigger } (ensures1 && ensures2 && ...)`.
    The trigger controls when the SMT solver instantiates the axiom. -/
private def mkInvokeOnAxiom (params : List Parameter) (trigger : StmtExprMd)
    (postconds : List Condition) : StmtExprMd :=
  let body := conjoin (postconds.map (·.condition))
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
    let preProc :=
      if proc.preconditions.isEmpty then []
      else [mkConditionProc (preCondProcName proc.name.text) proc.inputs proc.preconditions]
    let postProc :=
      if postconds.isEmpty then []
      else [mkPostConditionProc (postCondProcName proc.name.text)
              proc.inputs proc.outputs postconds]
    preProc ++ postProc

  -- Transform procedures: strip contracts, add assume/assert, rewrite call sites
  let transformedProcs := program.staticProcedures.map fun proc =>
    if proc.isFunctional then
      proc
    else
      let proc := match proc.invokeOn with
        | some trigger =>
          let postconds := getPostconditions proc.body
          if postconds.isEmpty then { proc with invokeOn := none }
          else { proc with
            axioms := [mkInvokeOnAxiom proc.inputs trigger postconds]
            invokeOn := none }
        | none => proc
      let proc := match contractInfoMap.get? proc.name.text with
        | some info =>
          { proc with
            preconditions := []
            body := transformProcBody proc info }
        | none => proc
      -- Rewrite call sites in the procedure body
      rewriteCallSitesInProc contractInfoMap proc

  { program with staticProcedures := helperProcs ++ transformedProcs }

end -- public section
end Strata.Laurel
