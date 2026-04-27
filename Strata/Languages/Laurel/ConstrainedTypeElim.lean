/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr
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
    .Applied ctor (args.map fun a => ⟨resolveBaseType ptMap a.val, a.source, a.md⟩)
  | _ => ty

def resolveType (ptMap : ConstrainedTypeMap) (ty : HighTypeMd) : HighTypeMd :=
  ⟨resolveBaseType ptMap ty.val, ty.source, ty.md⟩

def isConstrainedType (ptMap : ConstrainedTypeMap) (ty : HighType) : Bool :=
  match ty with | .UserDefined name => ptMap.contains name.text | _ => false

/-- Build a call to the constraint function for a constrained type, or `none` if not constrained -/
def constraintCallFor (ptMap : ConstrainedTypeMap) (ty : HighType)
    (varName : Identifier) (md : Imperative.MetaData Core.Expression) (src : Option FileRange := none) : Option StmtExprMd :=
  match ty with
  | .UserDefined name => if ptMap.contains name.text then
      some ⟨.StaticCall (mkId s!"{name.text}$constraint") [⟨.Identifier varName, src, md⟩], src, md⟩
    else none
  | _ => none

/-- Generate a constraint function for a constrained type.
    For nested types, the function calls the parent's constraint function. -/
def mkConstraintFunc (ptMap : ConstrainedTypeMap) (ct : ConstrainedType) : Procedure :=
  let baseType := resolveType ptMap ct.base
  let bodyExpr := match ct.base.val with
    | .UserDefined parent =>
      if ptMap.contains parent.text then
        let paramId := { ct.valueName with uniqueId := none }
        let paramRef : StmtExprMd :=
          { val := .Identifier paramId, source := none }
        let parentCall : StmtExprMd :=
          { val := .StaticCall (mkId s!"{parent.text}$constraint") [paramRef], source := none }
        { val := .PrimitiveOp .And [ct.constraint, parentCall], source := none }
      else ct.constraint
    | _ => ct.constraint
  { name := mkId s!"{ct.name.text}$constraint"
    inputs := [{ name := ct.valueName, type := { baseType with md := #[] } }]
    outputs := [{ name := mkId "result", type := { val := .TBool, source := none } }]
    body := .Transparent { val := .Block [bodyExpr] none, source := none }
    isFunctional := true
    decreases := none
    preconditions := [] }

private def wrap (stmts : List StmtExprMd) (src : Option FileRange) (md : Imperative.MetaData Core.Expression := .empty)
    : StmtExprMd :=
  match stmts with | [s] => s | ss => ⟨.Block ss none, src, md⟩

/-- Resolve constrained types in type positions and inject constraint calls into quantifier bodies.
    Recursion into StmtExprMd children is handled by `mapStmtExpr`. -/
def resolveExprNode (ptMap : ConstrainedTypeMap) (expr : StmtExprMd) : StmtExprMd :=
  let source := expr.source
  let md := expr.md
  match expr.val with
  | .LocalVariable n ty init =>
    ⟨.LocalVariable n (resolveType ptMap ty) init, source, md⟩
  | .Quantifier mode param trigger body =>
    let param' := { param with type := resolveType ptMap param.type }
    -- With bottom-up traversal, `body` is already recursed into. The newly
    -- created `PrimitiveOp` won't be visited again, which is safe because
    -- `c` (from `constraintCallFor`) is a StaticCall with Identifier leaves
    -- that don't need further resolution.
    let combiner := match mode with | .Forall => Operation.Implies | .Exists => Operation.And
    let injected := match constraintCallFor ptMap param.type.val param.name md (src := source) with
      | some c => ⟨.PrimitiveOp combiner [c, body], source, md⟩
      | none => body
    ⟨.Quantifier mode param' trigger injected, source, md⟩
  | .AsType t ty => ⟨.AsType t (resolveType ptMap ty), source, md⟩
  | .IsType t ty => ⟨.IsType t (resolveType ptMap ty), source, md⟩
  | _ => expr

abbrev ElimM := StateM PredVarMap

private def inScope (action : ElimM α) : ElimM α := do
  let saved ← get
  let result ← action
  set saved
  return result

def elimStmt (ptMap : ConstrainedTypeMap)
    (stmt : StmtExprMd) : ElimM (List StmtExprMd) := do
  let source := stmt.source
  let md := stmt.md
  match _h : stmt.val with
  | .LocalVariable name ty init =>
    let callOpt := constraintCallFor ptMap ty.val name md (src := source)
    if callOpt.isSome then modify fun pv => pv.insert name.text ty.val
    let (init', check) : Option StmtExprMd × List StmtExprMd := match init with
      | none => match callOpt with
        | some c => (none, [⟨.Assume c, source, md⟩])
        | none => (none, [])
      | some _ => (init, callOpt.toList.map fun c => ⟨.Assert { condition := c }, source, md⟩)
    pure ([⟨.LocalVariable name ty init', source, md⟩] ++ check)

  | .Assign [target] _ => match target.val with
    | .Identifier name => do
      match (← get).get? name.text with
      | some ty =>
        let assert := (constraintCallFor ptMap ty name md (src := source)).toList.map
          fun c => ⟨.Assert { condition := c }, source, md⟩
        pure ([stmt] ++ assert)
      | none => pure [stmt]
    | _ => pure [stmt]

  | .Block stmts sep =>
    let stmtss ← inScope (stmts.mapM (elimStmt ptMap))
    pure [⟨.Block stmtss.flatten sep, source, md⟩]

  | .IfThenElse cond thenBr (some elseBr) =>
    let thenSs ← inScope (elimStmt ptMap thenBr)
    let elseSs ← inScope (elimStmt ptMap elseBr)
    pure [⟨.IfThenElse cond (wrap thenSs source md) (some (wrap elseSs source md)), source, md⟩]
  | .IfThenElse cond thenBr none =>
    let thenSs ← inScope (elimStmt ptMap thenBr)
    pure [⟨.IfThenElse cond (wrap thenSs source md) none, source, md⟩]

  | .While cond inv dec body =>
    let bodySs ← inScope (elimStmt ptMap body)
    pure [⟨.While cond inv dec (wrap bodySs source md), source, md⟩]

  | _ => pure [stmt]
termination_by sizeOf stmt
decreasing_by
  all_goals simp_wf
  all_goals (try have := AstNode.sizeOf_val_lt stmt)
  all_goals (try term_by_mem)
  all_goals omega

def elimProc (ptMap : ConstrainedTypeMap) (proc : Procedure) : Procedure :=
  let inputRequires : List Condition := proc.inputs.filterMap fun p =>
    (constraintCallFor ptMap p.type.val p.name p.type.md (src := p.type.source)).map
      fun c => { condition := c }
  let outputEnsures : List Condition := if proc.isFunctional then [] else proc.outputs.filterMap fun p =>
    (constraintCallFor ptMap p.type.val p.name p.type.md (src := p.type.source)).map
      fun c => { condition := ⟨c.val, p.type.source, p.type.md⟩ }
  let initVars : PredVarMap := proc.inputs.foldl (init := {}) fun s p =>
    if isConstrainedType ptMap p.type.val then s.insert p.name.text p.type.val else s
  let body' := match proc.body with
  | .Transparent bodyExpr =>
    let (stmts, _) := (elimStmt ptMap bodyExpr).run initVars
    let body := wrap stmts bodyExpr.source bodyExpr.md
    if outputEnsures.isEmpty then .Transparent body
    else
      let retBody := if proc.isFunctional then ⟨.Return (some body), bodyExpr.source, bodyExpr.md⟩ else body
      .Opaque outputEnsures (some retBody) []
  | .Opaque postconds impl modif =>
    let impl' := impl.map fun b => wrap ((elimStmt ptMap b).run initVars).1 b.source b.md
    .Opaque (postconds ++ outputEnsures) impl' modif
  | .Abstract postconds => .Abstract (postconds ++ outputEnsures)
  | .External => .External
  let resolve := mapStmtExpr (resolveExprNode ptMap)
  let resolveBody : Body → Body := fun body => match body with
    | .Transparent b => .Transparent (resolve b)
    | .Opaque ps impl modif => .Opaque (ps.map (·.mapCondition resolve)) (impl.map resolve) (modif.map resolve)
    | .Abstract ps => .Abstract (ps.map (·.mapCondition resolve))
    | .External => .External
  { proc with
    body := resolveBody body'
    inputs := proc.inputs.map fun p => { p with type := resolveType ptMap p.type }
    outputs := proc.outputs.map fun p => { p with type := resolveType ptMap p.type }
    preconditions := (proc.preconditions ++ inputRequires).map (·.mapCondition resolve) }

private def mkWitnessProc (ptMap : ConstrainedTypeMap) (ct : ConstrainedType) : Procedure :=
  let src := ct.witness.source
  let md := ct.witness.md
  let witnessId : Identifier := mkId "$witness"
  let witnessInit : StmtExprMd :=
    ⟨.LocalVariable witnessId (resolveType ptMap ct.base) (some ct.witness), src, md⟩
  let assert : StmtExprMd :=
    ⟨.Assert { condition := (constraintCallFor ptMap (.UserDefined ct.name) witnessId md (src := src)).get! }, src, md⟩
  { name := mkId s!"$witness_{ct.name.text}"
    inputs := []
    outputs := []
    body := .Transparent ⟨.Block [witnessInit, assert] none, src, md⟩
    preconditions := []
    isFunctional := false
    decreases := none }

public def constrainedTypeElim (_model : SemanticModel) (program : Program)
    : Program × List DiagnosticModel :=
  let ptMap := buildConstrainedTypeMap program.types
  if ptMap.isEmpty then (program, []) else
  let constraintFuncs := program.types.filterMap fun
    | .Constrained ct => some (mkConstraintFunc ptMap ct) | _ => none
  let witnessProcedures := program.types.filterMap fun
    | .Constrained ct => some (mkWitnessProc ptMap ct) | _ => none
  let funcDiags := program.staticProcedures.foldl (init := []) fun acc proc =>
    if proc.isFunctional && proc.outputs.any (fun p => isConstrainedType ptMap p.type.val) then
      acc.cons (proc.name.md.toDiagnostic "constrained return types on functions are not yet supported")
    else acc
  ({ program with
    staticProcedures := constraintFuncs ++ program.staticProcedures.map (elimProc ptMap)
                        ++ witnessProcedures
    types := program.types.filter fun | .Constrained _ => false | _ => true },
   funcDiags)

end Strata.Laurel
