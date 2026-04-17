/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.FunctionsAndProofs

/-!
# Eliminate Multiple Outputs

Transforms bodiless functions with multiple outputs into functions that return
a single synthesized result datatype. Call sites are rewritten to destructure
the result using the generated accessors.

This pass operates on `FunctionsAndProofsProgram → FunctionsAndProofsProgram`.
-/

namespace Strata.Laurel

public section

private def emptyMd : MetaData := .empty
private def mkMd (e : StmtExpr) : StmtExprMd := { val := e, source := none }
private def mkTy (t : HighType) : HighTypeMd := { val := t, source := none }

/-- Info about a function whose multiple outputs have been collapsed into a result datatype. -/
private structure MultiOutInfo where
  funcName : String
  resultTypeName : String
  constructorName : String
  /-- Original output parameters (name, type). -/
  outputs : List Parameter

/-- Identify bodiless functions with multiple outputs and build info records. -/
private def collectMultiOutFunctions (funcs : List Procedure) : List MultiOutInfo :=
  funcs.filterMap fun f =>
    if f.outputs.length > 1 && !f.body.isTransparent then
      some {
        funcName := f.name.text
        resultTypeName := s!"{f.name.text}$result"
        constructorName := s!"{f.name.text}$result$mk"
        outputs := f.outputs
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

/-- Rewrite a statement list, replacing multi-output call patterns. -/
private def rewriteStmts (infoMap : Std.HashMap String MultiOutInfo)
    (stmts : List StmtExprMd) : List StmtExprMd :=
  stmts.flatMap fun stmt =>
    match stmt.val with
    | .Assign targets ⟨.StaticCall callee args, callSrc, callMd⟩ =>
      match infoMap.get? callee.text with
      | some info =>
        if targets.length == info.outputs.length then
          let tempName := s!"${callee.text}$temp"
          let tempDecl := mkMd (.LocalVariable [mkId tempName]
            (mkTy (.UserDefined (mkId info.resultTypeName)))
            (some ⟨.StaticCall callee args, callSrc, callMd⟩))
          let assigns := targets.zipIdx.map fun (tgt, i) =>
            mkMd (.Assign [tgt]
              (mkMd (.StaticCall (mkId (destructorName info i))
                [mkMd (.Identifier (mkId tempName))])))
          tempDecl :: assigns
        else [stmt]
      | none => [stmt]
    | .LocalVariable names _ty (some ⟨.StaticCall callee args, callSrc, callMd⟩) =>
      match infoMap.get? callee.text with
      | some info =>
        if info.outputs.length > 1 then
          let tempName := s!"${callee.text}$temp"
          let tempDecl := mkMd (.LocalVariable [mkId tempName]
            (mkTy (.UserDefined (mkId info.resultTypeName)))
            (some ⟨.StaticCall callee args, callSrc, callMd⟩))
          let name := names.head!
          let assign := mkMd (.Assign [mkMd (.Identifier name)]
            (mkMd (.StaticCall (mkId (destructorName info 0))
              [mkMd (.Identifier (mkId tempName))])))
          [tempDecl, assign]
        else [stmt]
      | none => [stmt]
    | _ => [stmt]

/-- Rewrite blocks in a StmtExprMd tree to handle multi-output calls. -/
private def rewriteExpr (infoMap : Std.HashMap String MultiOutInfo)
    (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun e =>
    match e.val with
    | .Block stmts label => ⟨.Block (rewriteStmts infoMap stmts) label, e.source, e.md⟩
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

/-- Eliminate multiple outputs from a FunctionsAndProofsProgram. -/
def eliminateMultipleOutputs (program : FunctionsAndProofsProgram)
    : FunctionsAndProofsProgram :=
  let infos := collectMultiOutFunctions program.functions
  if infos.isEmpty then program else
  let infoMap : Std.HashMap String MultiOutInfo :=
    infos.foldl (fun m info => m.insert info.funcName info) {}
  let newDatatypes := infos.map mkResultDatatype
  let functions := program.functions.map fun f =>
    match infoMap.get? f.name.text with
    | some info => rewriteProcedure infoMap (transformFunction info f)
    | none => rewriteProcedure infoMap f
  let proofs := program.proofs.map (rewriteProcedure infoMap)
  { program with
    functions := functions
    proofs := proofs
    datatypes := program.datatypes ++ newDatatypes }

end -- public section
end Strata.Laurel
