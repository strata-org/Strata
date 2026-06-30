/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Resolution
public import Strata.Languages.Laurel.LaurelPass
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
  | .TSet et => { val := .TSet (resolveAliasType amap et visited), source := ty.source }
  | .TSeq et => { val := .TSeq (resolveAliasType amap et visited), source := ty.source }
  | .TArray et => { val := .TArray (resolveAliasType amap et visited), source := ty.source }
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

/-- Eliminate all type aliases from a program. Replaces every `UserDefined`
    reference (in any type position, via `mapProgramHighTypes`) with the alias
    target (transitively) and removes `.Alias` entries from `program.types`. -/
public def typeAliasElim (_model : SemanticModel) (program : Program) : Program :=
  let amap := buildAliasMap program.types
  if amap.isEmpty then program else
  let program := mapProgramHighTypes (resolveAliasType amap) program
  { program with types := program.types.filter fun | .Alias _ => false | _ => true }

/-- Pipeline pass: type alias elimination. -/
public def typeAliasElimPass : LoweringPass where
  name := "TypeAliasElim"
  documentation := "Eliminates type aliases by replacing all UserDefined references to alias names with their resolved target types. Chained aliases are resolved transitively. Alias entries are removed from the type list."
  needsResolves := true
  run := fun _ p m => (typeAliasElim m p, [], {})

end Strata.Laurel
