/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Resolution
import Strata.Languages.Laurel.MapStmtExpr

/-!
# Type Alias Elimination

A Laurel-to-Laurel pass that eliminates type aliases by replacing all
`UserDefined` references to alias names with their resolved target types.
Chained aliases are resolved transitively. Runs after the first resolution.
-/

namespace Strata.Laurel

private abbrev AliasMap := Std.HashMap String HighTypeMd

/-- Build a map from alias name to target type. -/
def buildAliasMap (types : List TypeDefinition) : AliasMap :=
  types.foldl (init := {}) fun m td =>
    match td with | .Alias ta => m.insert ta.name.text ta.target | _ => m

/-- Transitively resolve a HighType through the alias map.
    A visited set guards against infinite loops on cyclic aliases.

    Key invariant: for a non-cyclic alias map, the result contains no
    `UserDefined` references whose name is a key in `amap`. -/
partial def resolveAliasType (amap : AliasMap) (ty : HighTypeMd)
    (visited : Std.HashSet String := {}) : HighTypeMd :=
  match ty.val with
  | .UserDefined name =>
    if visited.contains name.text then ty
    else match amap.get? name.text with
      | some target => resolveAliasType amap target (visited.insert name.text)
      | none => ty
  | .TTypedField vt => { val := .TTypedField (resolveAliasType amap vt visited), source := ty.source }
  | .TSet et => { val := .TSet (resolveAliasType amap et visited), source := ty.source }
  | .TMap kt vt =>
    { val := .TMap (resolveAliasType amap kt visited) (resolveAliasType amap vt visited), source := ty.source }
  | .Applied base args =>
    let base' := resolveAliasType amap base visited
    let args' := args.map (resolveAliasType amap · visited)
    { val := .Applied base' args', source := ty.source }
  | .Pure base => { val := .Pure (resolveAliasType amap base visited), source := ty.source }
  | .Intersection tys =>
    { val := .Intersection (tys.map (resolveAliasType amap · visited)), source := ty.source }
  | _ => ty

/-- Resolve aliases in expression type positions. -/
def resolveAliasExprNode (amap : AliasMap) (expr : StmtExprMd) : StmtExprMd :=
  match expr.val with
  | .LocalVariable n ty init =>
    { val := .LocalVariable n (resolveAliasType amap ty) init, source := expr.source }
  | .Quantifier mode param trigger body =>
    { val := .Quantifier mode { param with type := resolveAliasType amap param.type } trigger body, source := expr.source }
  | .AsType t ty => { val := .AsType t (resolveAliasType amap ty), source := expr.source }
  | .IsType t ty => { val := .IsType t (resolveAliasType amap ty), source := expr.source }
  | _ => expr

def resolveAliasInProc (amap : AliasMap) (proc : Procedure) : Procedure :=
  let resolve := mapStmtExpr (resolveAliasExprNode amap)
  let resolveBody : Body → Body := fun body => match body with
    | .Transparent b => .Transparent (resolve b)
    | .Opaque ps impl modif => .Opaque (ps.map (·.mapCondition resolve)) (impl.map resolve) (modif.map resolve)
    | .Abstract ps => .Abstract (ps.map (·.mapCondition resolve))
    | .External => .External
  { proc with
    body := resolveBody proc.body
    inputs := proc.inputs.map fun p => { p with type := resolveAliasType amap p.type }
    outputs := proc.outputs.map fun p => { p with type := resolveAliasType amap p.type }
    preconditions := proc.preconditions.map (·.mapCondition resolve)
    decreases := proc.decreases.map resolve
    invokeOn := proc.invokeOn.map resolve }

def resolveAliasInType (amap : AliasMap) (td : TypeDefinition) : TypeDefinition :=
  match td with
  | .Composite ct =>
    .Composite { ct with
      fields := ct.fields.map fun f => { f with type := resolveAliasType amap f.type }
      instanceProcedures := ct.instanceProcedures.map (resolveAliasInProc amap) }
  | .Constrained ct =>
    let resolve := mapStmtExpr (resolveAliasExprNode amap)
    .Constrained { ct with
      base := resolveAliasType amap ct.base
      constraint := resolve ct.constraint
      witness := resolve ct.witness }
  | .Datatype dt =>
    .Datatype { dt with
      constructors := dt.constructors.map fun ctor =>
        { ctor with args := ctor.args.map fun p => { p with type := resolveAliasType amap p.type } } }
  | .Alias _ => td  -- will be removed

/-- Eliminate all type aliases from a program. Replaces `UserDefined` references
    with the alias target (transitively) and removes `.Alias` entries from `program.types`. -/
public def typeAliasElim (_model : SemanticModel) (program : Program) : Program :=
  let amap := buildAliasMap program.types
  if amap.isEmpty then program else
  { program with
    staticProcedures := program.staticProcedures.map (resolveAliasInProc amap)
    staticFields := program.staticFields.map fun f => { f with type := resolveAliasType amap f.type }
    types := (program.types.filter fun | .Alias _ => false | _ => true).map (resolveAliasInType amap)
    constants := program.constants.map fun c => { c with
      type := resolveAliasType amap c.type
      initializer := c.initializer.map (mapStmtExpr (resolveAliasExprNode amap)) } }

end Strata.Laurel
