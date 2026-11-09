/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.LaurelPass
public import StrataLaurel.Implementation.CoreWithLaurelTypes
import StrataLaurel.Implementation.TransparencyPass
import StrataLaurel.Implementation.FunctionalRewrite
import StrataLaurel.Implementation.EliminateReturnStatements
import StrataLaurel.Implementation.MapStmtExpr

namespace Strata.Laurel

public section

private def outputsToPackage (proc : Procedure) : Option (List Parameter) :=
  match proc.outputs with
  | outputs@(_ :: _ :: _) => some outputs
  | _ => none

private def outputDatatype (proc : Procedure) (outputs : List Parameter)
    : DatatypeDefinition :=
  { name := mkId (multiOutputDatatypeName proc.name.text)
    typeArgs := proc.typeArgs
    constructors :=
      [{ name := mkId (multiOutputCtorName proc.name.text)
         args := outputs }] }

private def packedType (proc : Procedure) : HighTypeMd :=
  let src := proc.name.source
  let base : HighTypeMd :=
    ⟨.UserDefined (mkId (multiOutputDatatypeName proc.name.text)), src⟩
  if proc.typeArgs.isEmpty then base
  else ⟨.Applied base (proc.typeArgs.map fun t => ⟨.TVar t, src⟩), src⟩

private structure RewriteState where
  diagnostics : List Message := []
  callSites : Nat := 0

private abbrev RewriteM := StateM RewriteState

private def nextCallSite : RewriteM Nat :=
  modifyGet fun st => (st.callSites, { st with callSites := st.callSites + 1 })

private def rewriteMultiOutputCalls (packagedFunctions : List (String × List Parameter))
    (body : StmtExprMd) : RewriteM StmtExprMd :=
  mapStmtExprFlattenM (fun _ _ => pure none) (fun _ e =>
    match e.val with
    | .Assign targets ⟨.StaticCall callee args tyArgs, callSrc⟩ =>
      if targets.length < 2 then pure [e]
      else match packagedFunctions.find? (·.1 == callee.text) with
        | none => pure [e]
        | some (_, outputs) =>
          if outputs.length != targets.length then pure [e]
          else do
            let site ← nextCallSite
            let tempName := mkId (multiOutputCallTempName site)
            let src := e.source
            let bind : StmtExprMd :=
              ⟨.Assign [⟨.Declare ⟨tempName, none⟩, src⟩]
                 ⟨.StaticCall callee args tyArgs, callSrc⟩, src⟩
            let projections : List StmtExprMd := (targets.zip outputs).map fun (t, out) =>
              ⟨.Assign [t]
                 ⟨.StaticCall (mkId (multiOutputDestructorName callee.text out.name.text))
                    [⟨.Var (.Local tempName), src⟩] [], src⟩, src⟩
            return bind :: projections
    | _ => pure [e]) true body

private def unbindableOutputs (packagedFunctions : List (String × List Parameter))
    (body : StmtExprMd) : List Message :=
  collectStmtExprList (fun n => match n.val with
    | .Assign targets ⟨.StaticCall callee _ _, _⟩ =>
      if targets.length < 2 then []
      else match packagedFunctions.find? (·.1 == callee.text) with
        | none => []
        | some (_, outputs) =>
          if outputs.length == targets.length then []
          else [diagnosticFromSource n.source
            s!"'{callee.text}' yields {outputs.length} values but the assignment binds {targets.length}; a callee that gained outputs after resolution should have been rejected before the output-packaging passes"
            MessageKind.strataBug]
    | _ => []) body

private def outputDeclarations (proc : Procedure) (outputs : List Parameter)
    : List StmtExprMd :=
  outputs.filterMap fun output =>
    if proc.inputs.any (·.name.text == output.name.text) then none
    else some ⟨.Var (.Declare ⟨output.name, some output.type⟩), output.name.source⟩

/-- Put `decls` at the front of the body's statements, inside the `$return`-labelled
    block `EliminateReturnStatements` wrapped it in. A *user* label is not a wrapper —
    an `exit` inside it needs that label — so such a block is left intact and the
    declarations go around it. -/
private def prependDeclarations (decls : List StmtExprMd) (body : StmtExprMd)
    : StmtExprMd :=
  match body with
  | ⟨.Block [single] label [] none, src⟩ =>
    if label.all (· == returnLabel) then
      ⟨.Block [prependDeclarations decls single] label [] none, src⟩
    else ⟨.Block (decls ++ [body]) none [] none, src⟩
  | ⟨.Block stmts label [] none, src⟩ =>
    if label.all (· == returnLabel) then ⟨.Block (decls ++ stmts) label [] none, src⟩
    else ⟨.Block (decls ++ [body]) none [] none, src⟩
  | _ => ⟨.Block (decls ++ [body]) none [] none, body.source⟩

private def rewriteExprCalls (packagedFunctions : List (String × List Parameter))
    (expr : StmtExprMd) : RewriteM StmtExprMd := do
  modify fun st => { st with diagnostics := st.diagnostics ++ unbindableOutputs packagedFunctions expr }
  rewriteMultiOutputCalls packagedFunctions expr

/-- Rewrite the multi-output call sites of a procedure, and nothing else. -/
private def rewriteCallsOnly (packagedFunctions : List (String × List Parameter))
    (proc : Procedure) : Procedure × List Message :=
  let (proc, st) := (mapProcedureM (rewriteExprCalls packagedFunctions) proc).run {}
  (proc, st.diagnostics)

private def packageProcedure (packagedFunctions : List (String × List Parameter))
    (proc : Procedure) : Procedure × List Message :=
  let (proc, diags) := rewriteCallsOnly packagedFunctions proc
  match outputsToPackage proc with
  | none => (proc, diags)
  | some outputs =>
    let body := match proc.body, outputDeclarations proc outputs with
      | .Transparent body, decls@(_ :: _) => .Transparent (prependDeclarations decls body)
      | body, _ => body
    ({ proc with
       outputs := [{ name := mkId multiOutputPackedName, type := packedType proc }],
       body := body },
     diags)

private def packageFunctionOutputs (uc : LaurelProgram)
    : LaurelProgram × List Message :=
  let packaged := uc.staticFunctions.filterMap fun p => (outputsToPackage p).map (p, ·)
  if packaged.isEmpty then (uc, [])
  else
    let packagedFunctions := packaged.map fun (p, outputs) => (p.name.text, outputs)
    let results := uc.staticFunctions.map (packageProcedure packagedFunctions)
    let procResults := uc.staticProcedures.map (rewriteCallsOnly packagedFunctions)
    ({ uc with
       types := uc.types ++ packaged.map fun (p, outputs) => .Datatype (outputDatatype p outputs)
       staticFunctions := results.map (·.1)
       staticProcedures := procResults.map (·.1) },
     results.flatMap (·.2) ++ procResults.flatMap (·.2))

public def packageFunctionOutputsPass : LaurelPass := .onUnordered {
  name := "PackageFunctionOutputsPass"
  creates := [NodeKind.StmtExpr.Assign, NodeKind.StmtExpr.StaticCall]
  documentation := "Rewrites a function that yields several outputs into one that yields a single value of a generated datatype holding all of them: it declares the datatype, holding all of that function's outputs in a single constructor, replaces the output list with a single output of that datatype's type, declares each output it drops as a bare local at the top of the body (reusing that output's uniqueId, and skipping an inout, which shares an input's binding), and rewrites a call filling several targets into one call binding the packaged value plus one projection per target. Runs before FunctionalRewrite, which rejects an assignment to several targets, and which places the constructor call the body evaluates to — reading the outputs' names, types and order back off the datatype declared here."
  needsResolves := true }
  fun _ uc _model =>
    let (uc', diags) := packageFunctionOutputs uc
    (uc', diags, {})

end -- public section

end Strata.Laurel
