/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.Resolution

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
  | .TTypedField vt => ⟨.TTypedField (resolveAliasType amap vt visited), ty.source, ty.md⟩
  | .TSet et => ⟨.TSet (resolveAliasType amap et visited), ty.source, ty.md⟩
  | .TMap kt vt =>
    ⟨.TMap (resolveAliasType amap kt visited) (resolveAliasType amap vt visited), ty.source, ty.md⟩
  | .Applied base args =>
    ⟨.Applied (resolveAliasType amap base visited)
      (args.map (resolveAliasType amap · visited)), ty.source, ty.md⟩
  | .Pure base => ⟨.Pure (resolveAliasType amap base visited), ty.source, ty.md⟩
  | .Intersection tys =>
    ⟨.Intersection (tys.map (resolveAliasType amap · visited)), ty.source, ty.md⟩
  | _ => ty

/-- Resolve aliases in expression type positions. -/
def resolveAliasExprNode (amap : AliasMap) (expr : StmtExprMd) : StmtExprMd :=
  match expr.val with
  | .LocalVariable n ty init =>
    ⟨.LocalVariable n (resolveAliasType amap ty) init, expr.source, expr.md⟩
  | .Quantifier mode param trigger body =>
    ⟨.Quantifier mode { param with type := resolveAliasType amap param.type } trigger body, expr.source, expr.md⟩
  | .AsType t ty => ⟨.AsType t (resolveAliasType amap ty), expr.source, expr.md⟩
  | .IsType t ty => ⟨.IsType t (resolveAliasType amap ty), expr.source, expr.md⟩
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
