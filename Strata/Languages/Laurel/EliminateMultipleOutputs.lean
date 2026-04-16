/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.FunctionsAndProofs
import Strata.Util.Tactics

/-!
# Eliminate Multiple Outputs

Transforms functions with multiple output parameters into functions that return
a single synthesized datatype containing all outputs. Call sites that destructure
multiple outputs are rewritten to use the datatype's destructors.

This pass operates on `FunctionsAndProofsProgram` → `FunctionsAndProofsProgram`.
Currently only supports functions without a body (opaque/abstract).
-/

namespace Strata.Laurel

public section

/-- Name of the synthesized result datatype for a multi-output function. -/
private def resultTypeName (procName : String) : String :=
  s!"{procName}$result"

/-- Name of the single constructor for the result datatype. -/
private def resultCtorName (procName : String) : String :=
  s!"{procName}$result$mk"

/-- Name of the i-th output field in the result datatype. -/
private def resultFieldName (i : Nat) : String :=
  s!"out{i}"

/-- Destructor name following the `DatatypeDefinition..field` convention. -/
private def resultDestructorName (procName : String) (i : Nat) : String :=
  s!"{resultTypeName procName}..{resultFieldName i}"

private def emptyMd : MetaData := .empty
private def mkMd (e : StmtExpr) : StmtExprMd := ⟨e, emptyMd⟩

/-- Check if a procedure is a multi-output function that needs transformation.
    Only applies to bodiless functions (opaque without implementation, or abstract). -/
private def needsTransform (proc : Procedure) : Bool :=
  proc.isFunctional && proc.outputs.length > 1 && !proc.body.isExternal &&
  match proc.body with
  | .Opaque _ none _ => true
  | .Abstract _ => true
  | _ => false

/-- Generate a datatype definition for a multi-output function's results. -/
private def mkResultDatatype (proc : Procedure) : DatatypeDefinition :=
  let fields := proc.outputs.mapIdx fun i p =>
    { name := mkId (resultFieldName i), type := p.type : Parameter }
  { name := mkId (resultTypeName proc.name.text)
    typeArgs := []
    constructors := [{ name := mkId (resultCtorName proc.name.text), args := fields }] }

/-- Transform a multi-output function to return the synthesized result type. -/
private def transformFunction (proc : Procedure) : Procedure :=
  let retType : HighTypeMd := ⟨.UserDefined (mkId (resultTypeName proc.name.text)), emptyMd⟩
  let singleOutput : Parameter := { name := mkId "$result", type := retType }
  { proc with outputs := [singleOutput] }

/-- Counter state for generating fresh temp variable names. -/
private abbrev FreshM := StateM Nat

private def freshTemp : FreshM String := do
  let n ← get
  set (n + 1)
  return s!"$multi_out_{n}"

/-- Rewrite a single statement, expanding multi-output calls. Returns a list
    because one statement may expand to multiple. Recurses into nested blocks. -/
private def rewriteStmt (multiOutFuncs : Std.HashMap String Procedure)
    (stmt : StmtExprMd) : FreshM (List StmtExprMd) := do
  let md := stmt.md
  match _h : stmt.val with
  | .Assign targets (⟨.StaticCall callee args, callMd⟩) =>
    match multiOutFuncs.get? callee.text with
    | some proc =>
      if targets.length > 1 then
        let tempName ← freshTemp
        let tempId := mkId tempName
        let retType : HighTypeMd := ⟨.UserDefined (mkId (resultTypeName proc.name.text)), emptyMd⟩
        let tempDecl := ⟨.LocalVariable tempId retType
          (some ⟨.StaticCall callee args, callMd⟩), md⟩
        let destructures := targets.mapIdx fun i target =>
          let destructorId := mkId (resultDestructorName proc.name.text i)
          let destructorCall := mkMd (.StaticCall destructorId [mkMd (.Identifier tempId)])
          ⟨.Assign [target] destructorCall, md⟩
        return [tempDecl] ++ destructures
      else return [stmt]
    | none => return [stmt]
  | .Block stmts label => do
    let stmts' ← stmts.attach.flatMapM fun ⟨s, hmem⟩ =>
      have : sizeOf s < sizeOf stmt := by
        have := WithMetadata.sizeOf_val_lt stmt; term_by_mem
      rewriteStmt multiOutFuncs s
    return [⟨.Block stmts' label, md⟩]
  | .IfThenElse cond th el => do
    have : sizeOf th < sizeOf stmt := by
      have := WithMetadata.sizeOf_val_lt stmt; cases stmt; simp_all; omega
    let thResult ← rewriteStmt multiOutFuncs th
    let th' := match thResult with | [s] => s | many => ⟨.Block many none, th.md⟩
    let el' ← el.attach.mapM fun ⟨e, hmem⟩ => do
      have : sizeOf e < sizeOf stmt := by
        have := WithMetadata.sizeOf_val_lt stmt; cases stmt; simp_all
        cases el <;> simp_all; omega
      let result ← rewriteStmt multiOutFuncs e
      return match result with | [s] => s | many => ⟨.Block many none, e.md⟩
    return [⟨.IfThenElse cond th' el', md⟩]
  | .While cond invs dec body => do
    have : sizeOf body < sizeOf stmt := by
      have := WithMetadata.sizeOf_val_lt stmt; cases stmt; simp_all; omega
    let bodyResult ← rewriteStmt multiOutFuncs body
    let body' := match bodyResult with | [s] => s | many => ⟨.Block many none, body.md⟩
    return [⟨.While cond invs dec body', md⟩]
  | _ => return [stmt]
termination_by sizeOf stmt

/-- Rewrite a procedure's body to transform multi-output call sites. -/
private def rewriteProcBody (multiOutFuncs : Std.HashMap String Procedure)
    (proc : Procedure) : FreshM Procedure := do
  match proc.body with
  | .Transparent b =>
    let stmts ← rewriteStmt multiOutFuncs b
    let b' := match stmts with
      | [s] => s
      | _ => ⟨.Block stmts none, b.md⟩
    return { proc with body := .Transparent b' }
  | .Opaque posts impl mods =>
    let impl' ← impl.mapM fun b => do
      let stmts ← rewriteStmt multiOutFuncs b
      return match stmts with
        | [s] => s
        | _ => ⟨.Block stmts none, b.md⟩
    return { proc with body := .Opaque posts impl' mods }
  | _ => return proc

/-- Main pass: eliminate multiple outputs from functions in a FunctionsAndProofsProgram. -/
def eliminateMultipleOutputs (program : FunctionsAndProofsProgram)
    : FunctionsAndProofsProgram :=
  -- Collect functions that need transformation
  let multiOutFuncs : Std.HashMap String Procedure :=
    program.functions.foldl (fun acc proc =>
      if needsTransform proc then acc.insert proc.name.text proc else acc) {}

  if multiOutFuncs.isEmpty then program else

  -- Generate result datatypes
  let newDatatypes := program.functions.filterMap fun proc =>
    if needsTransform proc then some (mkResultDatatype proc) else none

  -- Transform functions
  let functions' := program.functions.map fun proc =>
    if needsTransform proc then transformFunction proc else proc

  -- Rewrite call sites in all procedures (both functions and proofs)
  let (functions'', counter) := functions'.mapM (rewriteProcBody multiOutFuncs) |>.run 0
  let (proofs', _) := program.proofs.mapM (rewriteProcBody multiOutFuncs) |>.run counter

  { program with
    functions := functions''
    proofs := proofs'
    datatypes := program.datatypes ++ newDatatypes }

end -- public section
end Strata.Laurel
