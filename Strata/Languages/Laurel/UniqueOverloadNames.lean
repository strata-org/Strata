/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.Resolution
public import Strata.Languages.Laurel.LaurelPass
import Strata.Languages.Laurel.ContractPass
import Strata.Languages.Laurel.TransparencyPass

/-!
# Unique Overload Names

Gives every overloaded static procedure a unique top-level name so that
downstream passes that key on `proc.name.text` never see two procedures
sharing a name. Non-overloaded names are left untouched.
-/

namespace Strata.Laurel

private def mangledOverloadName (name : Identifier) (uniqueId : Nat) : Identifier :=
  { name with text := s!"$ov{uniqueId}${name.text}" }
private def rewriteCallNode (renames : Std.HashMap Nat Identifier)
    (overloadedNames : Std.HashSet String) (expr : StmtExprMd) : StmtExprMd :=
  match expr.val with
  | .StaticCall callee args =>
    match callee.uniqueId.bind renames.get? with
    | some mangled => { expr with val := .StaticCall { mangled with source := callee.source } args }
    | none =>
      -- Unresolved (`uniqueId := none`) call to an overloaded name → mark it so
      -- re-resolution doesn't mistake it for an undefined reference.
      if callee.uniqueId.isNone && overloadedNames.contains callee.text then
        { expr with val := .StaticCall (overloadFailureName callee) args }
      else expr
  | _ => expr

private def uniqueOverloadNames (program : Program) (model : SemanticModel) : Program :=
  -- A name is overloaded when more than one static procedure declares it.
  let nameCounts : Std.HashMap String Nat :=
    program.staticProcedures.foldl (init := {}) fun acc p =>
      acc.insert p.name.text (acc.getD p.name.text 0 + 1)
  -- Build the rename map (definition-site uniqueId → mangled name) and the
  -- renamed procedure list in one pass over the static procedures.
  let init : Std.HashMap Nat Identifier × List Procedure := ({}, [])
  let (renames, renamedProcs) :=
    program.staticProcedures.foldl (init := init) fun (renames, procs) p =>
      match p.name.uniqueId with
      | some id =>
        if nameCounts.getD p.name.text 0 > 1 && !model.conflictingOverloads.contains id then
          let mangled := mangledOverloadName p.name id
          (renames.insert id mangled, procs ++ [{ p with name := mangled }])
        else (renames, procs ++ [p])
      | none => (renames, procs ++ [p])

  if renames.isEmpty then program else

  -- The set of overloaded `text` names, used to recognize call sites whose
  -- overload resolution failed (so they carry no `uniqueId`) and mark them for
  -- re-resolution rather than leaving a now-dangling original name.
  let overloadedNames : Std.HashSet String :=
    nameCounts.fold (init := {}) fun acc name count =>
      if count > 1 then acc.insert name else acc

  -- Rewrite call sites everywhere expressions can appear (procedure bodies and
  -- contracts, constrained-type constraint/witness, constant initializers).
  mapProgramStmtExpr (rewriteCallNode renames overloadedNames)
    { program with staticProcedures := renamedProcs }

public def uniqueOverloadNamesPass : LoweringPass where
  name := "UniqueOverloadNames"
  documentation := "Renames overloaded static procedures to unique names so downstream name-keyed passes don't see collisions."
  needsResolves := true
  run := fun _ p model => (uniqueOverloadNames p model, [], {})
  comesBefore := [
    ⟨ contractPass.meta, "ContractPass derives helper names ($pre/$post) from the procedure's text name, so overloaded names must be made unique first." ⟩,
    ⟨ transparencyPass.meta, "TransparencyPass derives $asFunction twins from the procedure's text name, so overloaded names must be made unique first." ⟩]

end Strata.Laurel
