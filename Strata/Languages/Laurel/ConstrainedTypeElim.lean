/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Resolution

/-!
# Constrained Type Elimination

A Laurel-to-Laurel pass that eliminates constrained types by:
1. Generating a constraint function per constrained type (e.g. `nat$constraint(x: int): bool`)
2. Adding `requires constraintFunc(param)` for constrained-typed inputs
3. Adding `ensures constraintFunc(result)` for constrained-typed outputs
   - Skipped for `isFunctional` procedures since the Laurel translator does not yet support
     function postconditions. Constrained return types on functions are not checked.
4. Inserting `assert constraintFunc(var)` for local variable init and reassignment
5. Assuming the constraint for uninitialized constrained-typed variables (havoc + assume)
6. Adding a synthetic witness-validation procedure per constrained type
7. Injecting constraint function calls into quantifier bodies (`forall` → `implies`, `exists` → `and`)
8. Resolving all constrained type references to their base types
-/

namespace Strata.Laurel

open Strata

abbrev ConstrainedTypeMap := Std.HashMap String ConstrainedType
/-- Map from variable name to its constrained HighType (e.g. UserDefined "nat") -/
abbrev PredVarMap := Std.HashMap String HighType

def buildConstrainedTypeMap (types : List TypeDefinition) : ConstrainedTypeMap :=
  types.foldl (init := {}) fun m td =>
    match td with | .Constrained ct => m.insert ct.name.text ct | _ => m

partial def resolveBaseType (ptMap : ConstrainedTypeMap) (ty : HighType) : HighType :=
  match ty with
  | .UserDefined name => match ptMap.get? name.text with
    | some ct => resolveBaseType ptMap ct.base.val | none => ty
  | .Applied ctor args =>
    .Applied ctor (args.map fun a => ⟨resolveBaseType ptMap a.val, a.md⟩)
  | _ => ty

def resolveType (ptMap : ConstrainedTypeMap) (ty : HighTypeMd) : HighTypeMd :=
  ⟨resolveBaseType ptMap ty.val, ty.md⟩

def isConstrainedType (ptMap : ConstrainedTypeMap) (ty : HighType) : Bool :=
  match ty with | .UserDefined name => ptMap.contains name.text | _ => false

/-- Build a call to the constraint function for a constrained type, or `none` if not constrained -/
def constraintCallFor (ptMap : ConstrainedTypeMap) (ty : HighType)
    (varName : Identifier) (md : Imperative.MetaData Core.Expression) : Option StmtExprMd :=
  match ty with
  | .UserDefined name => if ptMap.contains name.text then
      some ⟨.StaticCall (mkId s!"{name.text}$constraint") [⟨.Identifier varName, md⟩], md⟩
    else none
  | _ => none

/-- Generate a constraint function for a constrained type.
    For nested types, the function calls the parent's constraint function. -/
def mkConstraintFunc (ptMap : ConstrainedTypeMap) (ct : ConstrainedType) : Procedure :=
  let md : Imperative.MetaData Core.Expression := #[]
  let baseType := resolveType ptMap ct.base
  let bodyExpr := match ct.base.val with
    | .UserDefined parent =>
      if ptMap.contains parent.text then
        let parentCall : StmtExprMd :=
          ⟨.StaticCall (mkId s!"{parent.text}$constraint") [⟨.Identifier { ct.valueName with uniqueId := none }, md⟩], md⟩
        ⟨.PrimitiveOp .And [ct.constraint, parentCall], md⟩
      else ct.constraint
    | _ => ct.constraint
  { name := mkId s!"{ct.name.text}$constraint"
    inputs := [{ name := ct.valueName, type := { baseType with md := #[] } }]
    outputs := [{ name := mkId "result", type := ⟨.TBool, #[]⟩ }]
    body := .Transparent ⟨.Block [bodyExpr] none, #[]⟩
    isFunctional := true
    determinism := .deterministic none
    decreases := none
    preconditions := []
    md := #[] }

private def wrap (stmts : List StmtExprMd) (md : Imperative.MetaData Core.Expression)
    : StmtExprMd :=
  match stmts with | [s] => s | ss => ⟨.Block ss none, md⟩

/-- Resolve constrained types in all type positions of an expression,
    and inject constraint function calls into quantifier bodies -/
def resolveExpr (ptMap : ConstrainedTypeMap) : StmtExprMd → StmtExprMd
  | ⟨.LocalVariable n ty (some init), md⟩ =>
    ⟨.LocalVariable n (resolveType ptMap ty) (some (resolveExpr ptMap init)), md⟩
  | ⟨.LocalVariable n ty none, md⟩ =>
    ⟨.LocalVariable n (resolveType ptMap ty) none, md⟩
  | ⟨.Forall param body, md⟩ =>
    let body' := resolveExpr ptMap body
    let param' := { param with type := resolveType ptMap param.type }
    let injected := match constraintCallFor ptMap param.type.val param.name md with
      | some c => ⟨.PrimitiveOp .Implies [c, body'], md⟩
      | none => body'
    ⟨.Forall param' injected, md⟩
  | ⟨.Exists param body, md⟩ =>
    let body' := resolveExpr ptMap body
    let param' := { param with type := resolveType ptMap param.type }
    let injected := match constraintCallFor ptMap param.type.val param.name md with
      | some c => ⟨.PrimitiveOp .And [c, body'], md⟩
      | none => body'
    ⟨.Exists param' injected, md⟩
  | ⟨.AsType t ty, md⟩ => ⟨.AsType (resolveExpr ptMap t) (resolveType ptMap ty), md⟩
  | ⟨.IsType t ty, md⟩ => ⟨.IsType (resolveExpr ptMap t) (resolveType ptMap ty), md⟩
  | ⟨.PrimitiveOp op args, md⟩ =>
    ⟨.PrimitiveOp op (args.attach.map fun ⟨a, _⟩ => resolveExpr ptMap a), md⟩
  | ⟨.StaticCall c args, md⟩ =>
    ⟨.StaticCall c (args.attach.map fun ⟨a, _⟩ => resolveExpr ptMap a), md⟩
  | ⟨.Block ss sep, md⟩ =>
    ⟨.Block (ss.attach.map fun ⟨s, _⟩ => resolveExpr ptMap s) sep, md⟩
  | ⟨.IfThenElse c t (some el), md⟩ =>
    ⟨.IfThenElse (resolveExpr ptMap c) (resolveExpr ptMap t) (some (resolveExpr ptMap el)), md⟩
  | ⟨.IfThenElse c t none, md⟩ =>
    ⟨.IfThenElse (resolveExpr ptMap c) (resolveExpr ptMap t) none, md⟩
  | ⟨.While c inv dec body, md⟩ =>
    ⟨.While (resolveExpr ptMap c) (inv.attach.map fun ⟨i, _⟩ => resolveExpr ptMap i)
            dec (resolveExpr ptMap body), md⟩
  | ⟨.Assign ts v, md⟩ =>
    ⟨.Assign (ts.attach.map fun ⟨t, _⟩ => resolveExpr ptMap t) (resolveExpr ptMap v), md⟩
  | ⟨.Return (some v), md⟩ => ⟨.Return (some (resolveExpr ptMap v)), md⟩
  | ⟨.Return none, md⟩ => ⟨.Return none, md⟩
  | ⟨.Assert c, md⟩ => ⟨.Assert (resolveExpr ptMap c), md⟩
  | ⟨.Assume c, md⟩ => ⟨.Assume (resolveExpr ptMap c), md⟩
  | e => e
termination_by e => sizeOf e
decreasing_by all_goals (have := WithMetadata.sizeOf_val_lt ‹_›; term_by_mem)

abbrev ElimM := StateM PredVarMap

private def inScope (action : ElimM α) : ElimM α := do
  let saved ← get
  let result ← action
  set saved
  return result

def elimStmt (ptMap : ConstrainedTypeMap)
    (stmt : StmtExprMd) : ElimM (List StmtExprMd) := do
  let md := stmt.md
  match _h : stmt.val with
  | .LocalVariable name ty init =>
    let callOpt := constraintCallFor ptMap ty.val name md
    if callOpt.isSome then modify fun pv => pv.insert name.text ty.val
    let (init', check) : Option StmtExprMd × List StmtExprMd := match init with
      | none => match callOpt with
        | some c => (none, [⟨.Assume c, md⟩])
        | none => (none, [])
      | some _ => (init, callOpt.toList.map fun c => ⟨.Assert c, md⟩)
    pure ([⟨.LocalVariable name ty init', md⟩] ++ check)

  | .Assign [target] _ => match target.val with
    | .Identifier name => do
      match (← get).get? name.text with
      | some ty =>
        let assert := (constraintCallFor ptMap ty name md).toList.map
          fun c => ⟨.Assert c, md⟩
        pure ([stmt] ++ assert)
      | none => pure [stmt]
    | _ => pure [stmt]

  | .Block stmts sep =>
    let stmtss ← inScope (stmts.mapM (elimStmt ptMap))
    pure [⟨.Block stmtss.flatten sep, md⟩]

  | .IfThenElse cond thenBr (some elseBr) =>
    let thenSs ← inScope (elimStmt ptMap thenBr)
    let elseSs ← inScope (elimStmt ptMap elseBr)
    pure [⟨.IfThenElse cond (wrap thenSs md) (some (wrap elseSs md)), md⟩]
  | .IfThenElse cond thenBr none =>
    let thenSs ← inScope (elimStmt ptMap thenBr)
    pure [⟨.IfThenElse cond (wrap thenSs md) none, md⟩]

  | .While cond inv dec body =>
    let bodySs ← inScope (elimStmt ptMap body)
    pure [⟨.While cond inv dec (wrap bodySs md), md⟩]

  | _ => pure [stmt]
termination_by sizeOf stmt
decreasing_by
  all_goals simp_wf
  all_goals (try have := WithMetadata.sizeOf_val_lt stmt)
  all_goals (try term_by_mem)
  all_goals omega

def elimProc (ptMap : ConstrainedTypeMap) (proc : Procedure) : Procedure :=
  let inputRequires := proc.inputs.filterMap fun p =>
    constraintCallFor ptMap p.type.val p.name p.type.md
  let outputEnsures := if proc.isFunctional then [] else proc.outputs.filterMap fun p =>
    (constraintCallFor ptMap p.type.val p.name p.type.md).map
      fun c => ⟨c.val, p.type.md⟩
  let initVars : PredVarMap := proc.inputs.foldl (init := {}) fun s p =>
    if isConstrainedType ptMap p.type.val then s.insert p.name.text p.type.val else s
  let body' := match proc.body with
  | .Transparent bodyExpr =>
    let (stmts, _) := (elimStmt ptMap bodyExpr).run initVars
    let body := wrap stmts bodyExpr.md
    if outputEnsures.isEmpty then .Transparent body
    else
      let retBody := if proc.isFunctional then ⟨.Return (some body), bodyExpr.md⟩ else body
      .Opaque outputEnsures (some retBody) []
  | .Opaque postconds impl modif =>
    let impl' := impl.map fun b => wrap ((elimStmt ptMap b).run initVars).1 b.md
    .Opaque (postconds ++ outputEnsures) impl' modif
  | .Abstract postconds => .Abstract (postconds ++ outputEnsures)
  | .External => .External
  let resolve := resolveExpr ptMap
  let resolveBody : Body → Body := fun body => match body with
    | .Transparent b => .Transparent (resolve b)
    | .Opaque ps impl modif => .Opaque (ps.map resolve) (impl.map resolve) (modif.map resolve)
    | .Abstract ps => .Abstract (ps.map resolve)
    | .External => .External
  { proc with
    body := resolveBody body'
    inputs := proc.inputs.map fun p => { p with type := resolveType ptMap p.type }
    outputs := proc.outputs.map fun p => { p with type := resolveType ptMap p.type }
    preconditions := (proc.preconditions ++ inputRequires).map resolve }

private def mkWitnessProc (ptMap : ConstrainedTypeMap) (ct : ConstrainedType) : Procedure :=
  let md := ct.witness.md
  let witnessId : Identifier := mkId "$witness"
  let witnessInit : StmtExprMd :=
    ⟨.LocalVariable witnessId (resolveType ptMap ct.base) (some ct.witness), md⟩
  let assert : StmtExprMd :=
    ⟨.Assert (constraintCallFor ptMap (.UserDefined ct.name) witnessId md).get!, md⟩
  { name := mkId s!"$witness_{ct.name.text}"
    inputs := []
    outputs := []
    body := .Transparent ⟨.Block [witnessInit, assert] none, md⟩
    preconditions := []
    isFunctional := false
    determinism := .deterministic none
    decreases := none
    md := md }

public def constrainedTypeElim (_model : SemanticModel) (program : Program) : Program × Array DiagnosticModel :=
  let ptMap := buildConstrainedTypeMap program.types
  if ptMap.isEmpty then (program, #[]) else
  let constraintFuncs := program.types.filterMap fun
    | .Constrained ct => some (mkConstraintFunc ptMap ct) | _ => none
  let witnessProcedures := program.types.filterMap fun
    | .Constrained ct => some (mkWitnessProc ptMap ct) | _ => none
  let funcDiags := program.staticProcedures.foldl (init := #[]) fun acc proc =>
    if proc.isFunctional && proc.outputs.any (fun p => isConstrainedType ptMap p.type.val) then
      acc.push (proc.md.toDiagnostic "constrained return types on functions are not yet supported")
    else acc
  ({ program with
    staticProcedures := constraintFuncs ++ program.staticProcedures.map (elimProc ptMap)
                        ++ witnessProcedures
    types := program.types.filter fun | .Constrained _ => false | _ => true },
   funcDiags)

end Strata.Laurel
