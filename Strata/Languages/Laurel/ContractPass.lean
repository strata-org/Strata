/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr

/-!
## Contract Pass (Laurel → Laurel)

Removes pre- and postconditions from non-functional procedures and replaces
them with explicit precondition/postcondition helper procedures, assumptions,
and assertions.

For each non-functional procedure with contracts:
- Generate a precondition procedure (`foo$pre`) returning the conjunction of preconditions.
- Generate a postcondition procedure (`foo$post`) returning the conjunction of postconditions.
- Insert `assume foo$pre(inputs)` at the start of the body.
- Insert `assert foo$post(inputs, outputs)` at the end of the body.

For each call to a contracted procedure (in non-functional procedure bodies):
- Insert `assert foo$pre(args)` before the call (precondition check).
- Insert `assume foo$post(args, results)` after the call (postcondition assumption).

Functional procedures are left unchanged — their contracts are handled
directly by the Core function translation.
-/

namespace Strata.Laurel

public section

private def emptyMd : MetaData := .empty

private def mkMd (e : StmtExpr) : StmtExprMd := ⟨e, emptyMd⟩

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
  { name := mkId name
    inputs := params
    outputs := [⟨mkId "result", ⟨.TBool, emptyMd⟩⟩]
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

/-- Collect contract info for non-functional procedures. -/
private def collectContractInfo (procs : List Procedure) : Std.HashMap String ContractInfo :=
  procs.foldl (fun m proc =>
    if proc.isFunctional then m  -- skip functional procedures
    else
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

/-- Transform a non-functional procedure body to add assume/assert for its own contracts. -/
private def transformProcBody (proc : Procedure) (info : ContractInfo) : Body :=
  let inputArgs := paramsToArgs proc.inputs
  let outputArgs := paramsToArgs proc.outputs
  let preAssume : List StmtExprMd :=
    if info.hasPreCondition then [mkMd (.Assume (mkCall info.preName inputArgs))]
    else []
  let postAssert : List StmtExprMd :=
    if info.hasPostCondition then [mkMd (.Assert (mkCall info.postName (inputArgs ++ outputArgs)))]
    else []
  match proc.body with
  | .Transparent body =>
    .Transparent (mkMd (.Block (preAssume ++ [body] ++ postAssert) none))
  | .Opaque _ (some impl) _ =>
    .Transparent (mkMd (.Block (preAssume ++ [impl] ++ postAssert) none))
  | .Opaque _ none _ | .Abstract _ =>
    -- Bodiless: assume postconditions
    let postAssume := if info.hasPostCondition
      then [mkMd (.Assume (mkCall info.postName (inputArgs ++ outputArgs)))]
      else []
    .Transparent (mkMd (.Block (preAssume ++ postAssume) none))
  | b => b

/-- Run the contract pass on a Laurel program.
    Only non-functional procedures with contracts are transformed. -/
def contractPass (program : Program) : Program :=
  let contractInfoMap := collectContractInfo program.staticProcedures

  -- Generate helper procedures for non-functional procedures with contracts
  let helperProcs := program.staticProcedures.flatMap fun proc =>
    if proc.isFunctional then []
    else
      let postconds := getPostconditions proc.body
      let preProc :=
        if proc.preconditions.isEmpty then []
        else [mkConditionProc (preCondProcName proc.name.text) proc.inputs proc.preconditions]
      let postProc :=
        if postconds.isEmpty then []
        else [mkConditionProc (postCondProcName proc.name.text) (proc.inputs ++ proc.outputs) postconds]
      preProc ++ postProc

  -- Transform non-functional procedures: strip contracts, add assume/assert
  let transformedProcs := program.staticProcedures.map fun proc =>
    if proc.isFunctional then proc
    else
      match contractInfoMap.get? proc.name.text with
      | some info =>
        { proc with
          preconditions := []
          body := transformProcBody proc info }
      | none => proc

  { program with staticProcedures := helperProcs ++ transformedProcs }

end -- public section
end Strata.Laurel
