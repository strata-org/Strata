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
- Generate a postcondition procedure (`foo$post`) returning the conjunction of postconditions.
- Insert `assume foo$pre(inputs)` at the start of the body.
- Insert `assert foo$post(inputs, outputs)` at the end of the body.

For each call to a contracted procedure:
- Insert `assert foo$pre(args)` before the call (precondition check).
- Insert `assume foo$post(args, results)` after the call (postcondition assumption).
-/

namespace Strata.Laurel

public section

private def emptyMd : MetaData := .empty

private def mkMd (e : StmtExpr) : StmtExprMd := ⟨e, emptyMd⟩

/-- Create a `StmtExprMd` with a property summary in its metadata. -/
private def mkMdWithSummary (e : StmtExpr) (summary : String) : StmtExprMd :=
  ⟨e, emptyMd.withPropertySummary summary⟩

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

/-- Build a helper function that returns the conjunction of the given conditions. -/
private def mkConditionProc (name : String) (params : List Parameter)
    (conditions : List StmtExprMd) : Procedure :=
  -- Use "$result" as the output name to avoid clashing with user-defined
  -- parameter names (user names cannot contain '$').
  { name := mkId name
    inputs := params
    outputs := [⟨mkId "$result", ⟨.TBool, emptyMd⟩⟩] -- TODO, enable anonymous output parameters
    preconditions := []
    decreases := none
    isFunctional := true
    body := .Transparent (conjoin conditions) }

/-- Build a call expression. -/
private def mkCall (callee : String) (args : List StmtExprMd) : StmtExprMd :=
  mkMd (.StaticCall (mkId callee) args)

/-- Convert parameters to identifier expressions. -/
private def paramsToArgs (params : List Parameter) : List StmtExprMd :=
  params.map fun p => mkMd (.Identifier p.name)

/-- Information about a procedure's contracts. -/
private structure ContractInfo where
  hasPreCondition : Bool
  hasPostCondition : Bool
  preName : String
  postName : String

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
      }
    else m) {}

/-- Transform a procedure body to add assume/assert for its own contracts. -/
private def transformProcBody (proc : Procedure) (info : ContractInfo) : Body :=
  let inputArgs := paramsToArgs proc.inputs
  let outputArgs := paramsToArgs proc.outputs
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
      [⟨.Assert (mkCall info.postName (inputArgs ++ outputArgs)),
        baseMd.withPropertySummary "postcondition"⟩]
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
    Uses the call site's metadata for generated assert/assume nodes. -/
private def rewriteStmt (contractInfoMap : Std.HashMap String ContractInfo)
    (e : StmtExprMd) : List StmtExprMd :=
  let md := e.md
  let mkWithMd (se : StmtExpr) : StmtExprMd := ⟨se, md⟩
  let mkWithMdSummary (se : StmtExpr) (summary : String) : StmtExprMd :=
    ⟨se, md.withPropertySummary summary⟩
  match e.val with
  | .Assign targets (.mk (.StaticCall callee args) _) =>
    match contractInfoMap.get? callee.text with
    | some info =>
      let resultArgs := targets.map fun t => ⟨t.val, t.md⟩
      let preAssert := if info.hasPreCondition
        then [mkWithMdSummary (.Assert (mkCall info.preName args)) "precondition"] else []
      let postAssume := if info.hasPostCondition
        then [mkWithMd (.Assume (mkCall info.postName (args ++ resultArgs)))] else []
      preAssert ++ [e] ++ postAssume
    | none => [e]
  | .LocalVariable name _ty (some (.mk (.StaticCall callee args) _)) =>
    match contractInfoMap.get? callee.text with
    | some info =>
      let resultArgs := [mkMd (.Identifier name)]
      let preAssert := if info.hasPreCondition
        then [mkWithMdSummary (.Assert (mkCall info.preName args)) "precondition"] else []
      let postAssume := if info.hasPostCondition
        then [mkWithMd (.Assume (mkCall info.postName (args ++ resultArgs)))] else []
      preAssert ++ [e] ++ postAssume
    | none => [e]
  | .StaticCall callee args =>
    match contractInfoMap.get? callee.text with
    | some info =>
      let preAssert := if info.hasPreCondition
        then [mkWithMdSummary (.Assert (mkCall info.preName args)) "precondition"] else []
      preAssert ++ [e]
    | none => [e]
  | _ => [e]

/-- Rewrite call sites in a statement/expression tree. Processes Block children
    at the statement level to avoid interfering with expression-level calls.
    For each statement-level call to a contracted procedure, inserts
    `assert pre(args)` before and `assume post(args, results)` after. -/
private def rewriteCallSites (contractInfoMap : Std.HashMap String ContractInfo)
    (expr : StmtExprMd) : StmtExprMd :=
  let result := mapStmtExpr (fun e =>
    match e.val with
    | .Block stmts label =>
      let stmts' := stmts.flatMap (rewriteStmt contractInfoMap)
      if stmts'.length == stmts.length then e
      else ⟨.Block stmts' label, e.md⟩
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
      else [mkConditionProc (postCondProcName proc.name.text) (proc.inputs ++ proc.outputs) postconds]
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
