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
- Generate a postcondition procedure (`foo$post`) that takes only the *input*
  parameters, internally calls the original procedure to obtain the outputs,
  and returns the conjunction of postconditions.
- Insert `assume foo$pre(inputs)` at the start of the body.
- Insert `assert foo$post(inputs)` at the end of the body.

For each call to a contracted procedure:
- Insert `assert foo$pre(args)` before the call (precondition check).
- Insert `assume foo$post(args)` after the call (postcondition assumption).

The postcondition procedure calls the original procedure internally so that
the `assume` at call sites only references pre-call arguments. This avoids
a soundness issue where mutable variables (e.g. `$heap`) are overwritten by
the call's result destructuring before the `assume` is evaluated.
-/

namespace Strata.Laurel

public section

private def emptyMd : MetaData := .empty

private def mkMd (e : StmtExpr) : StmtExprMd := { val := e, source := none }

/-- Create a `StmtExprMd` with a property summary in its metadata. -/
private def mkMdWithSummary (e : StmtExpr) (summary : String) : StmtExprMd :=
  ⟨e, none, emptyMd.withPropertySummary summary⟩

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
private def getPostconditions (body : Body) : List StmtExprMd :=
  match body with
  | .Opaque postconds _ _ => postconds
  | .Abstract postconds => postconds
  | _ => []

/-- Build a call expression. -/
private def mkCall (callee : String) (args : List StmtExprMd) : StmtExprMd :=
  mkMd (.StaticCall (mkId callee) args)

/-- Convert parameters to identifier expressions. -/
private def paramsToArgs (params : List Parameter) : List StmtExprMd :=
  params.map fun p => mkMd (.Identifier p.name)

/-- Build a helper function that returns the conjunction of the given conditions. -/
private def mkConditionProc (name : String) (params : List Parameter)
    (conditions : List StmtExprMd) : Procedure :=
  -- Use "$result" as the output name to avoid clashing with user-defined
  -- parameter names (user names cannot contain '$').
  { name := mkId name
    inputs := params
    outputs := [⟨mkId "$result", { val := .TBool, source := none }⟩] -- TODO, enable anonymous output parameters
    preconditions := []
    decreases := none
    isFunctional := true
    body := .Transparent (conjoin conditions) }

/-- Build a postcondition procedure that takes only the *input* parameters
    and internally calls the original procedure to obtain the outputs.

    For a procedure `foo(a, b) returns (x, y)` with postcondition `P(a, b, x, y)`,
    generates:
    ```
    procedure foo$post(a, b) returns ($result : bool) {
      var x, y : Tx := foo(a, b);
      P(a, b, x, y)
    }
    ```

    This ensures the `assume` at call sites only references pre-call arguments,
    avoiding a soundness issue where mutable variables (e.g. `$heap`) are
    overwritten by the call's result destructuring before the `assume` is
    evaluated. -/
private def mkPostConditionProc (name : String) (originalProcName : String)
    (inputParams : List Parameter) (outputParams : List Parameter)
    (conditions : List StmtExprMd) : Procedure :=
  let inputArgs := paramsToArgs inputParams
  let callExpr := mkMd (.StaticCall (mkId originalProcName) inputArgs)
  let localVarStmt := mkMd (.LocalVariable outputParams (some callExpr))
  -- Body: single initialized local variable, then postcondition conjunction
  let bodyStmts := [localVarStmt, conjoin conditions]
  let body := mkMd (.Block bodyStmts none)
  { name := mkId name
    inputs := inputParams
    outputs := [⟨mkId "$result", { val := .TBool, source := none }⟩]
    preconditions := []
    decreases := none
    isFunctional := false
    body := .Transparent body }

/-- Extract a combined summary from a list of contract clauses. -/
private def combinedSummary (clauses : List StmtExprMd) : Option String :=
  let summaries := clauses.filterMap fun c => c.md.getPropertySummary
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
  /-- The original procedure's input parameters (needed for postcondition generation). -/
  inputParams : List Parameter
  /-- The original procedure's output parameters (needed for postcondition generation). -/
  outputParams : List Parameter

/-- Collect contract info for all procedures with contracts. -/
private def collectContractInfo (procs : List Procedure) : Std.HashMap String ContractInfo :=
  procs.foldl (fun m proc =>
    let postconds := getPostconditions proc.body
    let hasPre := !proc.preconditions.isEmpty
    let hasPost := !postconds.isEmpty
    if hasPre || hasPost then
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
    if info.hasPreCondition then [mkMd (.Assume (mkCall info.preName inputArgs))]
    else []
  let postAssert : List StmtExprMd :=
    if info.hasPostCondition then
      -- Use the metadata from the first postcondition so the diagnostic
      -- carries the source location of the `ensures` clause.
      let baseMd := match postconds.head? with
        | some pc => pc.md
        | none => emptyMd
      let summary := info.postSummary.getD "postcondition"
      -- Directly assert the postcondition conjunction rather than calling $post.
      -- The $post procedure re-invokes the original (opaque) procedure to obtain
      -- outputs, which is correct at *call sites* but wrong inside the body:
      -- here the output variables (e.g. $heap) are already in scope with their
      -- actual values, so we assert the postcondition directly.
      [⟨.Assert (conjoin postconds),
        none, baseMd.withPropertySummary summary⟩]
    else []
  match proc.body with
  | .Transparent body =>
    .Transparent (mkMd (.Block (preAssume ++ [body] ++ postAssert) none))
  | .Opaque _ (some impl) _ =>
    .Opaque [] (mkMd (.Block (preAssume ++ [impl] ++ postAssert) none)) []
  | .Opaque _ none _ | .Abstract _ =>
    .Opaque [] (mkMd (.Block [] none)) []
  | b => b

/-- Rewrite a single statement that may be a call to a contracted procedure.
    Returns a list of statements (the original plus any inserted assert/assume).
    Uses the call site's metadata for generated assert/assume nodes.
    The postcondition assume passes only the call arguments (not the results),
    since the $post procedure internally calls the original to obtain outputs. -/
private def rewriteStmt (contractInfoMap : Std.HashMap String ContractInfo)
    (e : StmtExprMd) : List StmtExprMd :=
  let md := e.md
  let src := e.source
  let mkWithMd (se : StmtExpr) : StmtExprMd := ⟨se, src, md⟩
  let mkWithMdSummary (se : StmtExpr) (summary : String) : StmtExprMd :=
    ⟨se, src, md.withPropertySummary summary⟩
  match e.val with
  | .Assign _targets (.mk (.StaticCall callee args) ..) =>
    match contractInfoMap.get? callee.text with
    | some info =>
      let preAssert := if info.hasPreCondition
        then [mkWithMdSummary (.Assert (mkCall info.preName args)) (info.preSummary.getD "precondition")] else []
      -- Pass only call args; $post internally calls the procedure to get outputs.
      let postAssume := if info.hasPostCondition
        then [mkWithMd (.Assume (mkCall info.postName args))] else []
      preAssert ++ [e] ++ postAssume
    | none => [e]
  | .LocalVariable _params (some (.mk (.StaticCall callee args) ..)) =>
    match contractInfoMap.get? callee.text with
    | some info =>
      let preAssert := if info.hasPreCondition
        then [mkWithMdSummary (.Assert (mkCall info.preName args)) (info.preSummary.getD "precondition")] else []
      -- Pass only call args; $post internally calls the procedure to get outputs.
      let postAssume := if info.hasPostCondition
        then [mkWithMd (.Assume (mkCall info.postName args))] else []
      preAssert ++ [e] ++ postAssume
    | none => [e]
  | .StaticCall callee args =>
    match contractInfoMap.get? callee.text with
    | some info =>
      let preAssert := if info.hasPreCondition
        then [mkWithMdSummary (.Assert (mkCall info.preName args)) (info.preSummary.getD "precondition")] else []
      preAssert ++ [e]
    | none => [e]
  | _ => [e]

/-- Rewrite call sites in a statement/expression tree. Processes Block children
    at the statement level to avoid interfering with expression-level calls.
    For each statement-level call to a contracted procedure, inserts
    `assert pre(args)` before and `assume post(args)` after. -/
private def rewriteCallSites (contractInfoMap : Std.HashMap String ContractInfo)
    (expr : StmtExprMd) : StmtExprMd :=
  let result := mapStmtExpr (fun e =>
    match e.val with
    | .Block stmts label =>
      let stmts' := stmts.flatMap (rewriteStmt contractInfoMap)
      if stmts'.length == stmts.length then e
      else ⟨.Block stmts' label, e.source, e.md⟩
    | _ => e) expr
  -- Handle top-level non-Block statements (e.g., bare Assign or StaticCall)
  let expanded := rewriteStmt contractInfoMap result
  match expanded with
  | [single] => single
  | many => mkMd (.Block many none)

/-- Rewrite call sites in all bodies of a procedure. -/
private def rewriteCallSitesInProc (contractInfoMap : Std.HashMap String ContractInfo)
    (proc : Procedure) : Procedure :=
  let rw := rewriteCallSites contractInfoMap
  match proc.body with
  | .Transparent body =>
    { proc with body := .Transparent (rw body) }
  | .Opaque posts impl mods =>
    let body := Body.Opaque (posts.map rw) (impl.map rw) (mods.map rw)
    { proc with body := body }
  | _ => proc

/-- Run the contract pass on a Laurel program.
    All procedures with contracts are transformed. -/
def contractPass (program : Program) : Program :=
  let contractInfoMap := collectContractInfo program.staticProcedures

  -- Generate helper procedures for all procedures with contracts
  let helperProcs := program.staticProcedures.flatMap fun proc =>
    let postconds := getPostconditions proc.body
    let preProc :=
      if proc.preconditions.isEmpty then []
      else [mkConditionProc (preCondProcName proc.name.text) proc.inputs proc.preconditions]
    let postProc :=
      if postconds.isEmpty then []
      else [mkPostConditionProc (postCondProcName proc.name.text) proc.name.text
              proc.inputs proc.outputs postconds]
    preProc ++ postProc

  -- Transform procedures: strip contracts, add assume/assert, rewrite call sites
  let transformedProcs := program.staticProcedures.map fun proc =>
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
