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

/-- Check whether a statement is an Assume node. -/
private def isAssume (stmt : StmtExprMd) : Bool :=
  match stmt.val with
  | .Assume _ => true
  | _ => false

/-- Rewrite a single multi-output Assign into a temp declaration + destructuring
    assignments. Any `Assume` statements from `following` that appear immediately
    after the call are collected and placed between the temp declaration and the
    destructuring assignments, so they observe the pre-call variable values.
    Returns the rewritten statements and the number of consumed following statements. -/
private def rewriteAssign (infoMap : Std.HashMap String MultiOutInfo)
    (targets : List StmtExprMd) (callee : Identifier) (args : List StmtExprMd)
    (callSrc : Option FileRange) (callMd : MetaData)
    (following : List StmtExprMd) : Option (List StmtExprMd × Nat) :=
  match infoMap.get? callee.text with
  | some info =>
    if targets.length == info.outputs.length then
      let tempName := s!"${callee.text}$temp"
      let tempParam : Parameter := { name := mkId tempName, type := mkTy (.UserDefined (mkId info.resultTypeName)) }
      let tempDecl := mkMd (.LocalVariable [tempParam]
        (some ⟨.StaticCall callee args, callSrc, callMd⟩))
      let assigns := targets.zipIdx.map fun (tgt, i) =>
        mkMd (.Assign [tgt]
          (mkMd (.StaticCall (mkId (destructorName info i))
            [mkMd (.Identifier (mkId tempName))])))
      -- Collect any Assume statements that immediately follow the call.
      -- These must be placed before the destructuring assignments so they
      -- observe the pre-call values of variables like $heap.
      let assumes := following.takeWhile isAssume
      let consumed := assumes.length
      some (tempDecl :: assumes ++ assigns, consumed)
    else none
  | none => none

/-- Rewrite a statement list, replacing multi-output call patterns.
    When a multi-output Assign is followed by Assume statements (inserted by
    the contract pass), the Assumes are hoisted before the destructuring
    assignments so they reference pre-call variable values. -/
private def rewriteStmts (infoMap : Std.HashMap String MultiOutInfo)
    (stmts : List StmtExprMd) : List StmtExprMd :=
  let rec go (remaining : List StmtExprMd) (acc : List StmtExprMd) : List StmtExprMd :=
    match remaining with
    | [] => acc.reverse
    | stmt :: rest =>
      match stmt.val with
      | .Assign targets ⟨.StaticCall callee args, callSrc, callMd⟩ =>
        match rewriteAssign infoMap targets callee args callSrc callMd rest with
        | some (expanded, consumed) => go (rest.drop consumed) (expanded.reverse ++ acc)
        | none => go rest (stmt :: acc)
      | .LocalVariable params (some ⟨.StaticCall callee args, callSrc, callMd⟩) =>
        match infoMap.get? callee.text with
        | some info =>
          if info.outputs.length > 1 then
            let tempName := s!"${callee.text}$temp"
            let tempParam : Parameter := { name := mkId tempName, type := mkTy (.UserDefined (mkId info.resultTypeName)) }
            let tempDecl := mkMd (.LocalVariable [tempParam]
              (some ⟨.StaticCall callee args, callSrc, callMd⟩))
            -- Collect any Assume statements that immediately follow the call.
            let assumes := rest.takeWhile isAssume
            let consumed := assumes.length
            -- Declare each original output parameter as a local variable initialized
            -- from the corresponding destructor of the result datatype.
            let localDecls := params.zipIdx.map fun (p, i) =>
              mkMd (.LocalVariable [p]
                (some (mkMd (.StaticCall (mkId (destructorName info i))
                  [mkMd (.Identifier (mkId tempName))]))))
            go (rest.drop consumed) ((assumes ++ localDecls).reverse ++ (tempDecl :: acc))
          else go rest (stmt :: acc)
        | none => go rest (stmt :: acc)
      | _ => go rest (stmt :: acc)
  termination_by remaining.length
  go stmts []

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
