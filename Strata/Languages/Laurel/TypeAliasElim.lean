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

-- An alias entry: its type parameters (empty for a monomorphic alias) and target type.
private abbrev AliasMap := Std.HashMap String (List Identifier × HighTypeMd)

/-- Build a map from alias name to `(typeArgs, target)`. -/
def buildAliasMap (types : List TypeDefinition) : AliasMap :=
  types.foldl (init := {}) fun m td =>
    match td with | .Alias ta => m.insert ta.name.text (ta.typeArgs, ta.target) | _ => m

/-- Transitively resolve a HighType through the alias map.
    A visited set guards against infinite loops on cyclic aliases.

    For a GENERIC alias (`type Pair<A,B> = …`), a reference is `.Applied (UserDefined Pair) [τ…]`:
    bind the alias's `typeArgs ↦ τ…` and substitute into the target (via `substTypeVars`) before
    recursing — so `Pair<int,bool>` expands to the target with `A↦int, B↦bool`. A bare
    `.UserDefined` reference to a generic alias (no args) is left unfolded (an arity mismatch
    handled upstream); substitution fires only when args are present and the arity matches.

    Key invariant: for a non-cyclic alias map, the result contains no `UserDefined` references
    whose name is a key in `amap` (modulo arity-mismatched references, left for an upstream error). -/
partial def resolveAliasType (amap : AliasMap) (ty : HighTypeMd)
    (visited : Std.HashSet String := {}) : HighTypeMd :=
  match ty.val with
  | .UserDefined name =>
    if visited.contains name.text then ty
    else match amap.get? name.text with
      | some ([], target) => resolveAliasType amap target (visited.insert name.text)
      | _ => ty   -- not an alias, or a generic alias used without args (upstream arity error)
  | .TSet et => { val := .TSet (resolveAliasType amap et visited), source := ty.source }
  | .TMap kt vt =>
    { val := .TMap (resolveAliasType amap kt visited) (resolveAliasType amap vt visited), source := ty.source }
  | .Applied base args =>
    let args' := args.map (resolveAliasType amap · visited)
    match base.val with
    | .UserDefined name =>
      match (if visited.contains name.text then none else amap.get? name.text) with
      | some (params, target) =>
        -- Shared `applyAliasArgs` (LaurelAST) binds params↦args + substitutes — the SAME kernel
        -- `TypeLattice.unfold` uses, so the consistency relation agrees with elimination.
        match applyAliasArgs params args' target with
        | some t => resolveAliasType amap t (visited.insert name.text)
        | none => { val := .Applied base args', source := ty.source }   -- arity mismatch → upstream error
      | none => { val := .Applied base args', source := ty.source }
    | _ => { val := .Applied (resolveAliasType amap base visited) args', source := ty.source }
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
