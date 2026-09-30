/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Lean.Elab.Term.TermElabM
public meta import Init.Data.String.Legacy
public import StrataDDM.Util.Decimal

open Lean Meta Elab Term

/-!
# Language-Neutral Type Shape Analysis

Shared front end for the Ion serializer generators (`getIonSerializer%` for Java
in `Strata.Java.Gen`, `getIonGoSerializer%` for Go in `Strata.Go.Gen`).

Every such generator needs the same answer to the same question: *what shape does
this Lean type have, and what is in each of its fields?* That answer depends only
on the Lean environment, not on the target language, so it lives here and each
backend consumes it. Only the naming, type mapping and code emission are
language-specific and stay in the backends.

## What a shape is

`analyzeType` reduces a Lean declaration to one of three `TypeShape`s, matching
the three Ion encodings the deserializer understands:

| `TypeShape` | Lean declaration | Ion encoding |
|-------------|------------------|--------------|
| `.struct` | a `structure` | Ion struct, keys = field names |
| `.singleCtor` | an `inductive` with one constructor | Ion struct, keys `_0`, `_1`, … |
| `.multiCtor` | an `inductive` with zero or 2+ constructors | Ion sexp `(ctorName arg …)` |

Deliberately, a `TypeShape` carries **no target-language name**: the Lean `Name`
is the only identity it records, and each backend derives its own identifier from
it (`Strata.Java.javaClassName`, `Strata.Go.goTypeName`). A single shared name
would have to pick one language's escaping rules, and the two disagree — Java
reserves `String` and `record`, Go reserves `string` and `range`.

## Supported field types

Leaves are `Nat`, `Int`, `Float`, `String`, `Bool` and `StrataDDM.Decimal`;
containers are `List α` and `Option α`, nestable to any depth; anything else that
is a structure or an inductive is a `.compound` reference that pulls that type
into the generated closure (see `collectNestedTypes`).
-/

namespace Strata.CodeGen

/-! ## Name utilities -/

/--
Convert a Lean identifier to PascalCase: split on `_`, drop empty segments,
upcase the first character of each remaining segment, and concatenate.

Used for both type and member names, so `my_ctor` and `myCtor` both land on
`MyCtor` — see `disambiguate` for why that is safe.
-/
public meta def toPascalCase (s : String) : String :=
  s.splitOn "_"
  |>.filter (!·.isEmpty)
  |>.map (fun part => match part.toList with
    | [] => ""
    | c :: cs => .ofList (c.toUpper :: cs))
  |> String.intercalate ""

/--
Return a variant of `base` that is not already in `usedNames`, adding a `_`
(then `_2`, `_3`, …) suffix on collision, along with the extended set.

Escaping is not injective: a backend's escape function strips characters the
target language does not allow in identifiers and `toPascalCase` upcases segment
heads, so distinct Lean names can fold to one target identifier (`foo` and `Foo`
both become `Foo`; so do `myCtor` and `my_ctor`). Emitting the folded name twice
would declare the same type or the same field twice, which does not compile.

Comparison is case-insensitive because members that differ only in case are still
confusable, and because each generated type becomes a file on a possibly
case-insensitive filesystem.
-/
public meta partial def disambiguate (base : String) (usedNames : Std.HashSet String) :
    String × Std.HashSet String :=
  let rec findUnused (n : Nat) : String :=
    let suffix := if n == 0 then "" else if n == 1 then "_" else s!"_{n}"
    let candidate := base ++ suffix
    if usedNames.contains candidate.toLower then findUnused (n + 1) else candidate
  let name := findUnused 0
  (name, usedNames.insert name.toLower)

/-- Disambiguate a whole list of names left to right, so earlier names keep their
unsuffixed form and only later collisions are renamed. -/
public meta def disambiguateAll (names : List String) : List String :=
  (names.foldl (init := (#[], ∅)) fun (acc, used) n =>
    let (name, used') := disambiguate n used
    (acc.push name, used')).1.toList

/-! ## Leaf and compound type detection -/

/-- The Lean types that serialize directly to an Ion scalar. Everything else is
either a container (`List`/`Option`) or a `.compound` reference. -/
public meta def isLeafTypeName (name : Name) : Bool :=
  name == ``Nat || name == ``Int || name == ``String || name == ``Bool || name == ``Float ||
  name == ``StrataDDM.Decimal

/-! ## Shape description -/

/-- What a single field's Lean type maps to, stripped of everything a code
generator does not need to know. -/
public inductive FieldTypeInfo where
  /-- One of the scalar leaf types (see `isLeafTypeName`). An unrecognised type
  also lands here, with a name the backends map to their "unknown" type. -/
  | leaf (name : Name)
  /-- A reference to another structure or inductive, with its type arguments. -/
  | compound (name : Name) (typeArgs : Array FieldTypeInfo)
  /-- A type parameter of the enclosing type; generates a target-language generic. -/
  | typeParam (paramName : String)
  /-- `List α`. -/
  | list (elem : FieldTypeInfo)
  /-- `Option α`; `none` serializes to an Ion null. -/
  | option (elem : FieldTypeInfo)

/-- One field of a structure, or one argument of a constructor. `name` is the
*Lean* name and stays the Ion key; the backend derives its own identifier. -/
public structure FieldShape where
  name : String
  /-- The field's analyzed type. -/
  typeInfo : FieldTypeInfo

private meta instance : Inhabited FieldShape := ⟨{ name := "", typeInfo := .leaf `unknown }⟩

/-- One constructor of an inductive. -/
public structure CtorShape where
  /-- The fully qualified constructor name. -/
  name : Name
  /-- The last component of `name`, which is the Ion sexp tag for `.multiCtor`. -/
  shortName : String
  /-- The constructor's arguments, in declaration order. -/
  fields : Array FieldShape

private meta instance : Inhabited CtorShape := ⟨{ name := `unknown, shortName := "", fields := #[] }⟩

/-- The analyzed shape of a Lean type: which of the three Ion encodings it uses
and what it contains. Carries no target-language name by design — see the module
docstring. -/
public inductive TypeShape where
  /-- A `structure`: Ion struct keyed by field name. -/
  | struct (name : Name) (fields : Array FieldShape) (typeParams : Array String := #[])
  /-- An `inductive` with exactly one constructor: Ion struct keyed `_0`, `_1`, …. -/
  | singleCtor (name : Name) (ctor : CtorShape) (typeParams : Array String := #[])
  /-- An `inductive` with zero or 2+ constructors: Ion sexp tagged by ctor name. -/
  | multiCtor (name : Name) (ctors : Array CtorShape) (typeParams : Array String := #[])

/-- The Lean type this shape was derived from. -/
private meta def TypeShape.typeName : TypeShape → Name
  | .struct n _ _ | .singleCtor n _ _ | .multiCtor n _ _ => n

/-- Whether `name` names a type the generator should emit a declaration for, as
opposed to a leaf it maps to a built-in. -/
public meta def isCompoundType (env : Environment) (name : Name) : Bool :=
  !isLeafTypeName name &&
    ((getStructureInfo? env name).isSome ||
      match env.find? name with | some (.inductInfo _) => true | _ => false)

/-! ## Type parameter tagging

Lean constructor types are `forallE` telescopes whose leading binders are the
type's parameters. To see which *fields* mention which parameter, the parameters
have to be instantiated with something recognisable before the field types are
inspected. `extractCtorFields` substitutes a `Sort` whose universe is a `Level`
parameter tagged with `typeParamPlaceholderPrefix`, and `extractTypeParamName`
recovers the parameter name from it.

This is a marker, not a real universe parameter: nothing ever elaborates these
levels, they only survive long enough for `classifyFieldType` to read them back.
-/

/-- Prefix that tags a placeholder `Level` parameter as standing for a Lean type
parameter. Deliberately unlikely to collide with a real universe name. -/
private meta def typeParamPlaceholderPrefix : String := "__strataTypeParam_"

/-- Recover the type parameter name from a tagged placeholder level, if it is one. -/
private meta def extractTypeParamName : Level → Option String
  | .param n =>
    let s := n.toString (escape := false)
    if s.startsWith typeParamPlaceholderPrefix then
      some (s.drop typeParamPlaceholderPrefix.length).toString
    else none
  | _ => none

/-! ## Analysis -/

/-- Classify one field's Lean type into a `FieldTypeInfo`. -/
private meta partial def classifyFieldType (env : Environment) (ty : Expr)
    (paramNames : Array String := #[]) : MetaM FieldTypeInfo := do
  let ty ← whnf ty
  -- Strip optParam/autoParam wrappers (fields with default values)
  let ty := match ty.getAppFn.constName? with
    | some ``optParam =>
      let args := ty.getAppArgs
      if h : args.size > 0 then args[0] else ty
    | some ``autoParam =>
      let args := ty.getAppArgs
      if h : args.size > 0 then args[0] else ty
    | _ => ty
  let name := ty.getAppFn.constName?
  match name with
  | some ``List =>
    let args := ty.getAppArgs
    if h : args.size > 0 then return .list (← classifyFieldType env args[0] paramNames)
    else return .leaf `unknown
  | some ``Option =>
    let args := ty.getAppArgs
    if h : args.size > 0 then return .option (← classifyFieldType env args[0] paramNames)
    else return .leaf `unknown
  | some n =>
    if isCompoundType env n then
      -- Collect type arguments as FieldTypeInfo
      let args := ty.getAppArgs
      let numParams := match env.find? n with
        | some (.inductInfo indInfo) => indInfo.numParams
        | _ => args.size
      let typeArgs ← args[:numParams].toArray.mapM (classifyFieldType env · paramNames)
      return .compound n typeArgs
    else return .leaf n
  | none =>
    -- Check for tagged type parameter sorts
    if let .sort level := ty then
      if let some pName := extractTypeParamName level then
        return .typeParam pName
    if ty.isSort || ty.isFVar then return .typeParam "T"
    return .leaf `unknown

/--
Extract a constructor's type parameter names and its fields.

`fieldNames?` overrides the binder names, which is how structures get their real
field names: a structure's `mk` binders carry them already, but passing
`StructureInfo.fieldNames` keeps the order authoritative. For inductive
constructors the binder name is used directly, except that Lean's anonymous
binders (`_`, `_x✝`, …) are replaced with `field<i>` so the backend has something
to call them.
-/
private meta def extractCtorFields (env : Environment) (ctorName : Name)
    (fieldNames? : Option (Array Name) := none) : MetaM (Array String × Array FieldShape) := do
  let some (.ctorInfo ci) := env.find? ctorName
    | throwError "Cannot find constructor {ctorName}"
  let mut ty := ci.type
  -- Collect parameter names and substitute with unique level-tagged sorts
  let mut paramNames : Array String := #[]
  for _ in List.range ci.numParams do
    match ty with
    | .forallE n dom b _ =>
      let pName := n.toString (escape := false)
      let tpName := toPascalCase pName
      paramNames := paramNames.push tpName
      -- Use a tagged sort as placeholder; only substitute Type-valued params
      let placeholder := if dom.isSort then
        mkSort (mkLevelParam (Name.mkStr .anonymous s!"{typeParamPlaceholderPrefix}{tpName}"))
      else
        mkSort Level.zero
      ty := b.instantiate1 placeholder
    | _ => break
  let mut fields := #[]
  for i in List.range ci.numFields do
    match ty with
    | .forallE n t b _ =>
      let typeInfo ← classifyFieldType env t paramNames
      let name := match fieldNames? with
        | some names => names[i]!.toString (escape := false)
        | none =>
          let s := n.toString (escape := false)
          if s.startsWith "_" && s.length > 1 then s!"field{i}" else s
      fields := fields.push { name, typeInfo }
      ty := b.instantiate1 (mkSort Level.zero)
    | _ => break
  return (paramNames, fields)

/-- Reduce a Lean type declaration to its `TypeShape`. Throws if `typeName` is
neither a structure nor an inductive. -/
public meta def analyzeType (env : Environment) (typeName : Name) : MetaM TypeShape := do
  if let some sinfo := getStructureInfo? env typeName then
    let (paramNames, fields) ← extractCtorFields env (sinfo.structName ++ `mk) (some sinfo.fieldNames)
    return .struct typeName fields paramNames
  let some (.inductInfo indInfo) := env.find? typeName
    | throwError "{typeName} is not an inductive or structure type"
  let mut typeParams : Array String := #[]
  let mut ctors : Array CtorShape := #[]
  for ctorName in indInfo.ctors do
    let (paramNames, fields) ← extractCtorFields env ctorName
    typeParams := paramNames
    ctors := ctors.push { name := ctorName, shortName := ctorName.getString!, fields }
  if ctors.size == 1 then
    return .singleCtor typeName ctors[0]! typeParams
  return .multiCtor typeName ctors typeParams

/-- Every compound type mentioned by `t`, including inside containers and type
arguments. Used to walk the reachable closure of a root type. -/
private meta partial def extractCompoundNamesFromExpr (env : Environment) (t : Expr) :
    MetaM (Array Name) := do
  let t ← whnf t
  -- Strip optParam/autoParam wrappers
  let t := match t.getAppFn.constName? with
    | some ``optParam =>
      let args := t.getAppArgs
      if h : args.size > 0 then args[0] else t
    | some ``autoParam =>
      let args := t.getAppArgs
      if h : args.size > 0 then args[0] else t
    | _ => t
  let name := t.getAppFn.constName?
  match name with
  | some ``List | some ``Option =>
    let args := t.getAppArgs
    if h : args.size > 0 then extractCompoundNamesFromExpr env args[0]
    else return #[]
  | some n =>
    let mut result := #[]
    if isCompoundType env n then result := result.push n
    -- Also recurse into type arguments to find nested compound types
    for arg in t.getAppArgs do
      result := result ++ (← extractCompoundNamesFromExpr env arg)
    return result
  | none => return #[]

/-- Breadth-first closure of the compound types reachable from `rootName`,
starting with `rootName` itself. This is the set of types a generator must emit. -/
public meta def collectNestedTypes (env : Environment) (rootName : Name) : MetaM (Array Name) := do
  let mut visited : Std.HashSet Name := {}
  let mut queue := #[rootName]
  let mut result := #[]
  while h : queue.size > 0 do
    let name := queue[0]
    queue := queue.extract 1 queue.size
    if visited.contains name then continue
    visited := visited.insert name
    result := result.push name
    let ctors := if let some sinfo := getStructureInfo? env name then
      [sinfo.structName ++ `mk]
    else match env.find? name with
      | some (.inductInfo indInfo) => indInfo.ctors
      | _ => []
    for ctorName in ctors do
      let some (.ctorInfo ci) := env.find? ctorName | continue
      let mut ty := ci.type
      for _ in List.range ci.numParams do
        match ty with
        | .forallE _ _ b _ => ty := b.instantiate1 (mkSort Level.zero)
        | _ => break
      for _ in List.range ci.numFields do
        match ty with
        | .forallE _ t b _ =>
          for n in ← extractCompoundNamesFromExpr env t do
            if !visited.contains n then queue := queue.push n
          ty := b.instantiate1 (mkSort Level.zero)
        | _ => break
  return result

end Strata.CodeGen
