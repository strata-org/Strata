/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.Resolution
public import StrataLaurel.Implementation.LaurelPass
import StrataLaurel.Implementation.MapStmtExpr

/-!
# Type Alias Elimination

A Laurel-to-Laurel pass that eliminates type aliases by replacing all
`UserDefined` references to alias names with their resolved target types.
Chained aliases are resolved transitively. Runs after the first resolution.
-/

namespace Strata.Laurel

-- An alias entry: its type parameters (empty for a monomorphic alias) and target type.
public abbrev AliasMap := Std.HashMap String (List Identifier × HighTypeMd)

/-- Build a map from alias name to `(typeArgs, target)`. -/
@[expose] public def buildAliasMap (types : List TypeDefinition) : AliasMap :=
  types.foldl (init := {}) fun m td =>
    match td with | .Alias ta => m.insert ta.name.text (ta.typeArgs, ta.target) | _ => m

/-- Transitively resolve a HighType through the alias map.
    A visited set guards against infinite loops on cyclic aliases.

    For a GENERIC alias (`type Pair<A,B> = …`), a reference is `.Applied (UserDefined Pair) [τ…]`:
    bind the alias's `typeArgs ↦ τ…` and substitute into the target (via `substTypeVars`) — so
    `Pair<int,bool>` expands with `A↦int, B↦bool`. Substitution fires only when args are present
    and the arity matches; an arity-wrong reference is left unfolded and rejected downstream
    (fail-loud, never a wrong-accept): `Pair<int>` cleanly by `resolveHighType`'s `.Applied`
    arity check, a bare `Pair` (zero args, which that check can't see — see the `Resolution.lean`
    NOTE) as a `'Pair' is not defined` StrataBug at re-resolution.

    Key invariant: for a non-cyclic alias map, the result contains no `UserDefined` reference
    whose name is a key in `amap`, except an arity-wrong one (left unfolded, per above). -/
@[expose] public def resolveAliasType (amap : AliasMap) (ty : HighTypeMd)
    (visited : Std.HashSet String := {}) (fuel : Nat := amap.size) : HighTypeMd :=
  match ty with
  | ⟨.UserDefined name, _⟩ =>
    if visited.contains name.text then ty
    else match amap.get? name.text, fuel with
      | some ([], target), fuel + 1 => resolveAliasType amap target (visited.insert name.text) fuel
      | _, _ => ty
  | ⟨.TSet et, src⟩ => { val := .TSet (resolveAliasType amap et visited fuel), source := src }
  | ⟨.TMap kt vt, src⟩ =>
    { val := .TMap (resolveAliasType amap kt visited fuel) (resolveAliasType amap vt visited fuel), source := src }
  | ⟨.Applied base args, src⟩ =>
    let args' := args.attach.map fun ⟨a, _⟩ => resolveAliasType amap a visited fuel
    match base.val with
    | .UserDefined name =>
      match (if visited.contains name.text then none else amap.get? name.text), fuel with
      | some (params, target), fuel + 1 =>
        match applyAliasArgs params args' target with
        | some t => resolveAliasType amap t (visited.insert name.text) fuel
        | none => { val := .Applied base args', source := src }
      | _, _ => { val := .Applied base args', source := src }
    | _ => { val := .Applied (resolveAliasType amap base visited fuel) args', source := src }
  | ⟨.Intersection tys, src⟩ =>
    { val := .Intersection (tys.attach.map fun ⟨t, _⟩ => resolveAliasType amap t visited fuel), source := src }
  | _ => ty
termination_by (fuel, ty)

@[expose] public def unaliasWith (amap : AliasMap) (t : HighType) : HighType :=
  (resolveAliasType amap { val := t, source := default }).val

/-- Eliminate all type aliases from a program. Replaces every `UserDefined`
    reference (in any type position, via `mapLaurelProgramHighTypes`) with the alias
    target (transitively) and removes `.Alias` entries from `program.types`. -/
@[expose] public def typeAliasElim (_model : SemanticModel) (program : LaurelProgram) : LaurelProgram :=
  let amap := buildAliasMap program.types
  if amap.isEmpty then program else
  let program := mapLaurelProgramHighTypes (resolveAliasType amap) program
  { program with types := program.types.filter fun | .Alias _ => false | _ => true }

/-- Pipeline pass: type alias elimination. -/
public def typeAliasElimPass : LaurelPass := .onUnordered {
  name := "TypeAliasElim"
  unsupported := [
      NodeKind.LaurelProgram.staticFunctions.cons
    ]
  removes := [NodeKind.TypeDefinition.Alias]
  documentation := "Eliminates type aliases by replacing all UserDefined references to alias names with their resolved target types. Chained aliases are resolved transitively. Alias entries are removed from the type list."
  needsResolves := true }
  fun _ p m => (typeAliasElim m p, [], {})

end Strata.Laurel
