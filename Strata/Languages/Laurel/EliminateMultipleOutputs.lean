/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.TransparencyPass

/-!
# Eliminate Multiple Outputs

Transforms bodiless functions with multiple outputs into functions that return
a single synthesized result datatype. Call sites are rewritten to destructure
the result using the generated accessors.

This pass operates on `UnorderedCoreWithLaurelTypes → UnorderedCoreWithLaurelTypes`.
-/

namespace Strata.Laurel

public section


private def mkMd (e : StmtExpr) : StmtExprMd := { val := e, source := none }
private def mkVarMd (v : Variable) : VariableMd := { val := v, source := none }
private def mkTy (t : HighType) : HighTypeMd := { val := t, source := none }

/-- Info about a function whose multiple outputs have been collapsed into a result datatype. -/
private structure MultiOutInfo where
  funcName : String
  resultTypeName : String
  constructorName : String
  /-- Original output parameters (name, type). -/
  outputs : List Parameter
  /-- Number of input parameters (used to detect implicit heap args at call sites). -/
  inputCount : Nat

/-- Identify bodiless functions with multiple outputs and build info records. -/
private def collectMultiOutFunctions (funcs : List Procedure) : List MultiOutInfo :=
  funcs.filterMap fun f =>
    if f.outputs.length > 1 && !f.body.isTransparent then
      some {
        funcName := f.name.text
        resultTypeName := s!"{f.name.text}$result"
        constructorName := s!"{f.name.text}$result$mk"
        outputs := f.outputs
        inputCount := f.inputs.length
      }
    else none

/-- Generate a result datatype for a multi-output function. -/
private def mkResultDatatype (info : MultiOutInfo) : DatatypeDefinition :=
  let args := info.outputs.zipIdx.map fun (p, i) =>
    { name := mkId s!"out{i}", type := p.type : Parameter }
  { name := mkId info.resultTypeName
    typeArgs := []
    constructors := [{ name := mkId info.constructorName, args := args }] }

/-- Transform a multi-output function to return the result datatype. -/
private def transformFunction (info : MultiOutInfo) (proc : Procedure) : Procedure :=
  let resultOutput : Parameter :=
    { name := mkId "$result", type := mkTy (.UserDefined (mkId info.resultTypeName)) }
  { proc with outputs := [resultOutput] }

/-- Destructor name for field `outN` of the result datatype. -/
private def destructorName (info : MultiOutInfo) (idx : Nat) : String :=
  s!"{info.resultTypeName}..out{idx}"

/-- Check whether a statement is an Assume node. -/
private def isAssume (stmt : StmtExprMd) : Bool :=
  match stmt.val with
  | .Assume _ => true
  | _ => false

/-- Rewrite a single multi-output Assign into a temp declaration + destructuring
    assignments. Any `Assume` statements from `following` that appear immediately
    after the call are collected and placed after the destructuring assignments,
    so they observe the post-call variable values.
    Returns the rewritten statements and the number of consumed following statements. -/
private def rewriteAssign (infoMap : Std.HashMap String MultiOutInfo)
    (targets : List VariableMd) (callee : Identifier) (args : List StmtExprMd)
    (callSrc : Option FileRange)
    (following : List StmtExprMd) (counter : Nat) : Option (List StmtExprMd × Nat) :=
  match infoMap.get? callee.text with
  | some info =>
    if targets.length ≤ info.outputs.length then
      let tempName := s!"${callee.text}$temp{counter}"
      let fullArgs := args
      let tempDecl := mkMd (.Assign [mkVarMd (.Declare ⟨mkId tempName, mkTy (.UserDefined (mkId info.resultTypeName))⟩)]
          ⟨.StaticCall callee fullArgs, callSrc⟩)
      let assigns := targets.zipIdx.map fun (tgt, i) =>
        mkMd (.Assign [tgt]
          (mkMd (.StaticCall (mkId (destructorName info i))
            [mkMd (.Var (.Local (mkId tempName)))])))
      -- Collect any Assume statements that immediately follow the call.
      -- These are placed after the destructuring assignments so they
      -- observe the post-call values of output variables.
      let assumes := following.takeWhile isAssume
      let consumed := assumes.length
      some (tempDecl :: assigns ++ assumes, consumed)
    else none
  | none => none

/-- Rewrite a statement list, replacing multi-output call patterns.
    When a multi-output Assign is followed by Assume statements (inserted by
    the contract pass), the Assumes are placed after the destructuring
    assignments so they reference post-call variable values. -/
private def rewriteStmts (infoMap : Std.HashMap String MultiOutInfo)
    (stmts : List StmtExprMd) : List StmtExprMd :=
  let rec go (remaining : List StmtExprMd) (acc : List StmtExprMd) (counter : Nat) : List StmtExprMd :=
    match remaining with
    | [] => acc.reverse
    | stmt :: rest =>
      match stmt.val with
      | .Assign targets ⟨.StaticCall callee args, callSrc⟩ =>
        match rewriteAssign infoMap targets callee args callSrc rest counter with
        | some (expanded, consumed) => go (rest.drop consumed) (expanded.reverse ++ acc) (counter + 1)
        | none => go rest (stmt :: acc) counter
      | _ => go rest (stmt :: acc) counter
  termination_by remaining.length
  go stmts [] 0

/-- Rewrite blocks in a StmtExprMd tree to handle multi-output calls. -/
private def rewriteExpr (infoMap : Std.HashMap String MultiOutInfo)
    (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun e =>
    match e.val with
    | .Block stmts label => ⟨.Block (rewriteStmts infoMap stmts) label, e.source⟩
    | _ => e) expr

/-- Rewrite all procedure bodies. -/
private def rewriteProcedure (infoMap : Std.HashMap String MultiOutInfo)
    (proc : Procedure) : Procedure :=
  match proc.body with
  | .Transparent b =>
    -- Wrap in a block so rewriteStmts can process top-level statements
    let wrapped := mkMd (.Block [b] none)
    let rewritten := rewriteExpr infoMap wrapped
    { proc with body := .Transparent rewritten }
  | .Opaque posts (some impl) mods =>
    let wrapped := mkMd (.Block [impl] none)
    let rewritten := rewriteExpr infoMap wrapped
    { proc with body := .Opaque posts (some rewritten) mods }
  | _ => proc

/-- Eliminate multiple outputs from a UnorderedCoreWithLaurelTypes. -/
def eliminateMultipleOutputs (program : UnorderedCoreWithLaurelTypes)
    : UnorderedCoreWithLaurelTypes :=
  let infos := collectMultiOutFunctions program.functions
  if infos.isEmpty then program else
  let infoMap : Std.HashMap String MultiOutInfo :=
    infos.foldl (fun m info => m.insert info.funcName info) {}
  let newDatatypes := infos.map mkResultDatatype
  let functions := program.functions.map fun f =>
    match infoMap.get? f.name.text with
    | some info => rewriteProcedure infoMap (transformFunction info f)
    | none => rewriteProcedure infoMap f
  let coreProcedures := program.coreProcedures.map fun p => rewriteProcedure infoMap p
  { program with
    functions := functions
    coreProcedures := coreProcedures
    datatypes := program.datatypes ++ newDatatypes }

end -- public section
end Strata.Laurel
