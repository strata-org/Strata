/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelTypes
import Strata.DL.Imperative.MetaData
import Strata.Util.Tactics

namespace Strata.Laurel

open Strata

/--
Compute the flattened set of ancestors for a composite type, including itself.
Traverses the `extending` list transitively.
-/
def computeAncestors (types : List TypeDefinition) (name : Identifier) : List Identifier :=
  let rec go (fuel : Nat) (current : Identifier) : List Identifier :=
    match fuel with
    | 0 => [current]
    | fuel' + 1 =>
      current :: (types.foldl (fun acc td =>
        match td with
        | .Composite ct =>
          if ct.name == current then
            ct.extending.foldl (fun acc2 parent => acc2 ++ go fuel' parent) acc
          else acc
        | _ => acc) [])
  (go types.length name).eraseDups

private def mkMd (e : StmtExpr) : StmtExprMd := ⟨e, #[]⟩

/--
Generate Laurel constant definitions for the type hierarchy:
- A `ancestorsFor<Type>` constant per composite type with the inner ancestor map
- A `ancestorsPerType` constant combining the per-type constants

Uses `StaticCall` to reference map operations (`Map.const`, `update`) and TypeTag constructors.
-/
def generateTypeHierarchyDecls (types : List TypeDefinition) : List Constant :=
  let composites := types.filterMap fun td => match td with
    | .Composite ct => some ct
    | _ => none
  if composites.isEmpty then [] else
  let typeTagTy : HighTypeMd := ⟨.TCore "TypeTag", #[]⟩
  let boolTy : HighTypeMd := ⟨.TBool, #[]⟩
  let innerMapTy : HighTypeMd := ⟨.TMap typeTagTy boolTy, #[]⟩
  let outerMapTy : HighTypeMd := ⟨.TMap typeTagTy innerMapTy, #[]⟩
  -- Helper: build an inner map (Map TypeTag bool) for a given composite type
  -- Start with Map.const(false), then update each composite type's entry
  let mkInnerMap (ct : CompositeType) : StmtExprMd :=
    let ancestors := computeAncestors types ct.name
    let falseConst := mkMd (.LiteralBool false)
    let emptyInner := mkMd (.StaticCall "Map.const" [falseConst])
    composites.foldl (fun acc otherCt =>
      let otherConst := mkMd (.StaticCall (otherCt.name ++ "_TypeTag") [])
      let isAncestor := ancestors.contains otherCt.name
      let boolVal := mkMd (.LiteralBool isAncestor)
      mkMd (.StaticCall "update" [acc, otherConst, boolVal])
    ) emptyInner
  -- Generate a separate constant `ancestorsFor<Type>` for each composite type
  let ancestorsForDecls := composites.map fun ct =>
    { name := s!"ancestorsFor{ct.name}"
      type := innerMapTy
      initializer := some (mkInnerMap ct) : Constant }
  -- Build ancestorsPerType by referencing the individual ancestorsFor<Type> constants
  let falseConst := mkMd (.LiteralBool false)
  let emptyInner := mkMd (.StaticCall "Map.const" [falseConst])
  let emptyOuter := mkMd (.StaticCall "Map.const" [emptyInner])
  let outerMapExpr := composites.foldl (fun acc ct =>
    let typeConst := mkMd (.StaticCall (ct.name ++ "_TypeTag") [])
    let innerMapRef := mkMd (.StaticCall s!"ancestorsFor{ct.name}" [])
    mkMd (.StaticCall "update" [acc, typeConst, innerMapRef])
  ) emptyOuter
  let ancestorsDecl : Constant :=
    { name := "ancestorsPerType"
      type := outerMapTy
      initializer := some outerMapExpr }
  ancestorsForDecls ++ [ancestorsDecl]

/--
Check if a field can be reached through a given type (directly declared or inherited).
Returns true if the type or any of its ancestors declares the field.
-/
def canReachField (types : List TypeDefinition) (typeName : Identifier) (fieldName : Identifier) : Bool :=
  let rec go (fuel : Nat) (current : Identifier) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      types.any fun td =>
        match td with
        | .Composite ct =>
          ct.name == current &&
          (ct.fields.any (·.name == fieldName) ||
           ct.extending.any (go fuel'))
        | _ => false
  go types.length typeName

/--
Check if a field is inherited through multiple parent paths (diamond inheritance).
Returns true if more than one direct parent of the given type can reach the field.
-/
def isDiamondInheritedField (types : List TypeDefinition) (typeName : Identifier) (fieldName : Identifier) : Bool :=
  let findComposite := types.findSome? fun td =>
    match td with
    | .Composite ct => if ct.name == typeName then some ct else none
    | _ => none
  match findComposite with
  | none => false
  | some ct =>
    -- If the field is directly declared on this type, it's not a diamond
    if ct.fields.any (·.name == fieldName) then false
    else
      -- Count how many direct parents can reach this field
      let parentsWithField := ct.extending.filter (canReachField types · fieldName)
      parentsWithField.length > 1

/--
Walk a StmtExpr AST and collect DiagnosticModel errors for diamond-inherited field accesses.
-/
def collectDiamondFieldErrors (uri : Uri) (types : List TypeDefinition) (env : TypeEnv)
    (expr : StmtExprMd) : List DiagnosticModel :=
  match _h : expr.val with
  | .FieldSelect target fieldName =>
    let targetErrors := collectDiamondFieldErrors uri types env target
    let fieldError := match (computeExprType env types target).val with
      | .UserDefined typeName =>
        if isDiamondInheritedField types typeName fieldName then
          let fileRange := (Imperative.getFileRange expr.md).getD FileRange.unknown
          [DiagnosticModel.withRange fileRange s!"fields that are inherited multiple times can not be accessed."]
        else []
      | _ => []
    targetErrors ++ fieldError
  | .Block stmts _ =>
    (stmts.attach.foldl (fun (acc, env') ⟨s, _⟩ =>
      let env'' := match s.val with
        | .LocalVariable name ty _ => (name, ty) :: env'
        | _ => env'
      (acc ++ collectDiamondFieldErrors uri types env' s, env'')) ([], env)).1
  | .Assign targets value =>
    let targetErrors := targets.attach.foldl (fun acc ⟨t, _⟩ => acc ++ collectDiamondFieldErrors uri types env t) []
    targetErrors ++ collectDiamondFieldErrors uri types env value
  | .IfThenElse c t e =>
    let errs := collectDiamondFieldErrors uri types env c ++
                collectDiamondFieldErrors uri types env t
    match e with
    | some eb => errs ++ collectDiamondFieldErrors uri types env eb
    | none => errs
  | .LocalVariable _ _ (some init) =>
    collectDiamondFieldErrors uri types env init
  | .While c invs _ b =>
    let errs := collectDiamondFieldErrors uri types env c ++
                collectDiamondFieldErrors uri types env b
    invs.attach.foldl (fun acc ⟨inv, _⟩ => acc ++ collectDiamondFieldErrors uri types env inv) errs
  | .Assert cond => collectDiamondFieldErrors uri types env cond
  | .Assume cond => collectDiamondFieldErrors uri types env cond
  | .PrimitiveOp _ args =>
    args.attach.foldl (fun acc ⟨a, _⟩ => acc ++ collectDiamondFieldErrors uri types env a) []
  | .StaticCall _ args =>
    args.attach.foldl (fun acc ⟨a, _⟩ => acc ++ collectDiamondFieldErrors uri types env a) []
  | .Return (some v) => collectDiamondFieldErrors uri types env v
  | _ => []
  termination_by sizeOf expr
  decreasing_by all_goals (have := WithMetadata.sizeOf_val_lt expr; term_by_mem)

/--
Validate a Laurel program for diamond-inherited field accesses.
Returns an array of DiagnosticModel errors.
-/
def validateDiamondFieldAccesses (uri : Uri) (program : Program) : Array DiagnosticModel :=
  let errors := program.staticProcedures.foldl (fun acc proc =>
    let env : TypeEnv := proc.inputs.map (fun p => (p.name, p.type)) ++
                         proc.outputs.map (fun p => (p.name, p.type))
    let bodyErrors := match proc.body with
      | .Transparent bodyExpr => collectDiamondFieldErrors uri program.types env bodyExpr
      | .Opaque postconds impl _ =>
        let postErrors := postconds.foldl (fun acc2 pc => acc2 ++ collectDiamondFieldErrors uri program.types env pc) []
        let implErrors := match impl with
          | some implExpr => collectDiamondFieldErrors uri program.types env implExpr
          | none => []
        postErrors ++ implErrors
      | .Abstract postcond => collectDiamondFieldErrors uri program.types env postcond
    acc ++ bodyErrors) []
  errors.toArray

end Laurel
