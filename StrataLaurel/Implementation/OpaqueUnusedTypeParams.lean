/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.LaurelPass
import StrataLaurel.Implementation.MapStmtExpr
import StrataLaurel.Implementation.Resolution

/-!
# Opaque Unused Type Parameters

Replaces each procedure type parameter that occurs in no input, output, or
thrown type by a fresh opaque type, since a call could not determine it.
-/

namespace Strata.Laurel

public section

/-- Replaces each type parameter of `proc` that occurs in neither an input type
    nor an output type by a new opaque type named
    `<procedure>$<parameter>$opaque`, avoiding the names in `taken`. The thrown
    type counts as an output. Returns the rewritten procedure and the new
    types. -/
private def opaqueUnusedTypeParamsOf (taken : Std.HashSet String)
    (proc : Procedure) : Procedure × List OpaqueTypeDefinition :=
  let signatureVars :=
    (proc.inputs ++ proc.outputs).flatMap (tvarNames ·.type.val)
    ++ (proc.throwsType.map (tvarNames ·.val)).getD []
  let (kept, unused) := proc.typeArgs.partition (signatureVars.contains ·.text)
  if unused.isEmpty then (proc, []) else
  let (decls, _) := unused.foldl (init := ([], taken))
    fun (decls, taken) param =>
    let name :=
      freshNameAvoiding s!"{proc.name.text}${param.text}$opaque" taken
    let decl : OpaqueTypeDefinition :=
      { name := { text := name, source := param.source } }
    (decls ++ [decl], taken.insert name)
  let subst : Std.HashMap String HighTypeMd :=
    (unused.zip decls).foldl (init := {}) fun m (param, decl) =>
      m.insert param.text ⟨.UserDefined (mkId decl.name.text), param.source⟩
  let proc :=
    mapProcedureHighTypesM (m := Id) (pure ∘ substTypeVars subst) proc
  ({ proc with typeArgs := kept }, decls)

/-- Applies `opaqueUnusedTypeParamsOf` to every non-external procedure and
    declares the new opaque types, whose names are distinct from each other
    and from every name the program declares. -/
def opaqueUnusedTypeParams (program : LaurelProgram) : LaurelProgram :=
  let taken := declaredNameSet program
  let (procs, decls, _) :=
    program.staticProcedures.foldl (init := ([], [], taken))
    fun (procs, decls, taken) proc =>
      if proc.body.isExternal then (procs ++ [proc], decls, taken) else
      let (proc', added) := opaqueUnusedTypeParamsOf taken proc
      (procs ++ [proc'], decls ++ added,
        added.foldl (·.insert ·.name.text) taken)
  { program with
    staticProcedures := procs
    types := program.types ++ decls.map .Opaque }

public def opaqueUnusedTypeParamsPass : LaurelPass := .onUnordered {
  name := "OpaqueUnusedTypeParams"
  unsupported := [
      NodeKind.LaurelProgram.staticFunctions.cons
    ]
  documentation := "Replaces each procedure type parameter that occurs in \
    neither an input type nor an output type by a fresh opaque type, \
    declared in the program, and drops it from the procedure's type \
    parameters. The thrown type counts as an output. A call could not \
    determine such a parameter."
  needsResolves := true }
  fun _ p _ => (opaqueUnusedTypeParams p, [], {})

end -- public section

end Strata.Laurel
