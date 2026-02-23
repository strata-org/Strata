/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Program
import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelTypes
import Strata.DL.Lambda.LExpr
import Strata.DL.Imperative.MetaData
import Strata.Util.Tactics

namespace Strata.Laurel

open Strata
open Lambda (LMonoTy LExpr)

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

/--
Generate Core declarations for the type hierarchy:
- A `ancestorsFor<Type>` constant per composite type with the inner ancestor map
- A `ancestorsPerType` constant combining the per-type constants

Note: TypeTag constants and their distinctness are now handled by the TypeTag datatype
generated in HeapParameterization. Datatype constructors are automatically distinct.
-/
def generateTypeHierarchyDecls (types : List TypeDefinition) : List Core.Decl :=
  let composites := types.filterMap fun td => match td with
    | .Composite ct => some ct
    | _ => none
  if composites.isEmpty then [] else
  -- Build a separate ancestorsFor<Type> constant for each composite type
  let typeTagTy := LMonoTy.tcons "TypeTag" []
  let innerMapTy := Core.mapTy typeTagTy .bool
  let outerMapTy := Core.mapTy typeTagTy innerMapTy
  -- Helper: build an inner map (Map TypeTag bool) for a given composite type
  -- Start with Map.empty(false), then update each composite type's entry
  let mkInnerMap (ct : CompositeType) : Core.Expression.Expr :=
    let ancestors := computeAncestors types ct.name
    let falseConst := LExpr.const () (.boolConst false)
    let emptyInner := LExpr.mkApp () Core.mapConstOp [falseConst]
    composites.foldl (fun acc otherCt =>
      let otherConst := LExpr.op () (Core.CoreIdent.unres (otherCt.name ++ "_TypeTag")) none
      let isAncestor := ancestors.contains otherCt.name
      let boolVal := LExpr.const () (.boolConst isAncestor)
      LExpr.mkApp () Core.mapUpdateOp [acc, otherConst, boolVal]
    ) emptyInner
  -- Generate a separate constant `ancestorsFor<Type>` for each composite type
  let ancestorsForDecls := composites.map fun ct =>
    Core.Decl.func {
      name := Core.CoreIdent.unres (s!"ancestorsFor{ct.name}")
      typeArgs := []
      inputs := []
      output := innerMapTy
      body := some (mkInnerMap ct)
    }
  -- Build ancestorsPerType by referencing the individual ancestorsFor<Type> constants
  let falseConst := LExpr.const () (.boolConst false)
  let emptyInner := LExpr.mkApp () Core.mapConstOp [falseConst]
  let emptyOuter := LExpr.mkApp () Core.mapConstOp [emptyInner]
  let outerMapExpr := composites.foldl (fun acc ct =>
    let typeConst := LExpr.op () (Core.CoreIdent.unres (ct.name ++ "_TypeTag")) none
    let innerMapRef := LExpr.op () (Core.CoreIdent.unres (s!"ancestorsFor{ct.name}")) (some innerMapTy)
    LExpr.mkApp () Core.mapUpdateOp [acc, typeConst, innerMapRef]
  ) emptyOuter
  -- Generate ancestorsPerType as a 0-ary function (constant) combining the per-type constants
  let ancestorsDecl := Core.Decl.func {
    name := Core.CoreIdent.unres "ancestorsPerType"
    typeArgs := []
    inputs := []
    output := outerMapTy
    body := some outerMapExpr
  }
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
