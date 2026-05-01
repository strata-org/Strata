/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.LaurelTypes
public import Strata.DL.Imperative.MetaData
import Strata.Util.Tactics

public section

namespace Strata.Laurel

open Strata

/--
Compute the flattened set of ancestors for a composite type, including itself.
Traverses the `extending` list transitively.
-/
def computeAncestors (model: SemanticModel) (name : Identifier) : List CompositeType :=
  let rec go (fuel : Nat) (current : Identifier) : List CompositeType :=
    match fuel with
    | 0 =>
      match model.get current with
      | .compositeType (ty : CompositeType) => [ty]
      | _ => []
    | fuel' + 1 =>
      match model.get current with
        | .compositeType (ty : CompositeType) =>
          [ty] ++ ty.extending.flatMap (fun parent => go fuel' parent)
        | _ => []
  let seen : List Identifier := []
  (go model.compositeCount name).foldl (fun (acc, seen) ct =>
    if seen.contains ct.name then (acc, seen)
    else (acc ++ [ct], seen ++ [ct.name])) ([], seen) |>.1

private def mkMd (e : StmtExpr) : StmtExprMd := ⟨e, none⟩
private def mkVarMd (v : Variable) : VariableMd := ⟨v, none⟩

/--
Generate Laurel constant definitions for the type hierarchy:
- A `ancestorsFor<Type>` constant per composite type.
It enables checking for `<Type>` whether it is assignable to another type using a Map lookup.
- A `ancestorsPerType` constant combining the per-type constants.
It enables checking for any type whether it is assignable to any other type using two Map lookups.
We use this to translate `<value> is <Type>`.
The runtime type of `<value>` is used for the outer Map lookup while `<Type>` for the inner one.

-/
def generateTypeHierarchyDecls (model : SemanticModel) (program: Program) : List Constant :=
  let composites := program.types.filterMap fun td => match td with
    | .Composite ct => some ct
    | _ => none
  if composites.isEmpty then [] else
  let typeTagTy : HighTypeMd := ⟨.UserDefined "TypeTag", none⟩
  let boolTy : HighTypeMd := ⟨.TBool, none⟩
  let innerMapTy : HighTypeMd := ⟨.TMap typeTagTy boolTy, none⟩
  let outerMapTy : HighTypeMd := ⟨.TMap typeTagTy innerMapTy, none⟩
  -- Helper: build an inner map (Map TypeTag bool) for a given composite type
  -- Start with const(false), then update each composite type's entry
  let mkInnerMap (ct : CompositeType) : StmtExprMd :=
    let ancestors := computeAncestors model ct.name
    let falseConst := mkMd (.LiteralBool false)
    let emptyInner := mkMd (.StaticCall "const" [falseConst])
    composites.foldl (fun acc otherCt =>
      let isAncestor := ancestors.any (·.name == otherCt.name)
      if isAncestor then
        let otherConst := mkMd (.StaticCall (mkId $ otherCt.name.text ++ "_TypeTag") [])
        let boolVal := mkMd (.LiteralBool true)
        mkMd (.StaticCall "update" [acc, otherConst, boolVal])
      else acc
    ) emptyInner
  -- Generate a separate constant `ancestorsFor<Type>` for each composite type
  let ancestorsForDecls := composites.map fun ct =>
    { name := s!"ancestorsFor{ct.name.text}"
      type := innerMapTy
      initializer := some (mkInnerMap ct) : Constant }
  -- Build ancestorsPerType by referencing the individual ancestorsFor<Type> constants
  let falseConst := mkMd (.LiteralBool false)
  let emptyInner := mkMd (.StaticCall "const" [falseConst])
  let emptyOuter := mkMd (.StaticCall "const" [emptyInner])
  let outerMapExpr := composites.foldl (fun acc ct =>
    let typeConst := mkMd (.StaticCall (mkId $ ct.name.text ++ "_TypeTag") [])
    let innerMapRef := mkMd (.StaticCall s!"ancestorsFor{ct.name.text}" [])
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
def canReachField (model : SemanticModel) (typeName : Identifier) (fieldName : Identifier) : Bool :=
  match model.get fieldName with
  | .field owner _ => ((computeAncestors model typeName).find? (fun t => t.name == owner)).isSome
  | _ => false -- recover from a resolution error

/--
Check if a field is inherited through multiple parent paths (diamond inheritance).
Returns true if more than one direct parent of the given type can reach the field.
-/
def isDiamondInheritedField (model : SemanticModel) (typeName : Identifier) (fieldName : Identifier) : Bool :=
  match model.get typeName with
  | .compositeType ct =>
    -- If the field is directly declared on this type, it's not a diamond
    if ct.fields.any (·.name == fieldName) then false
    else
      -- Count how many direct parents can reach this field
      let parentsWithField := ct.extending.filter (canReachField model · fieldName)
      parentsWithField.length > 1
  | _ => false

/--
Walk a StmtExpr AST and collect DiagnosticModel errors for diamond-inherited field accesses.
-/
def validateDiamondFieldAccessesForStmtExpr (model : SemanticModel)
    (expr : StmtExprMd) : List DiagnosticModel :=
  match _h : expr.val with
  | .Var (.Field target fieldName) =>
    let targetErrors := validateDiamondFieldAccessesForStmtExpr model target
    let fieldError := match (computeExprType model target).val with
      | .UserDefined typeName =>
        if isDiamondInheritedField model typeName fieldName then
          let fileRange := expr.source.getD FileRange.unknown
          [DiagnosticModel.withRange fileRange s!"fields that are inherited multiple times can not be accessed."]
        else []
      | _ => []
    targetErrors ++ fieldError
  | .Block stmts _ =>
    stmts.flatMap (fun s => validateDiamondFieldAccessesForStmtExpr model s)
  | .Assign targets value =>
    let targetErrors := targets.attach.foldl (fun acc ⟨t, _⟩ =>
      match _hv : t.val with
      | .Field target fieldName =>
        let innerErrors := validateDiamondFieldAccessesForStmtExpr model target
        let fieldError := match (computeExprType model target).val with
          | .UserDefined typeName =>
            if isDiamondInheritedField model typeName fieldName then
              let fileRange := t.source.getD FileRange.unknown
              [DiagnosticModel.withRange fileRange s!"fields that are inherited multiple times can not be accessed."]
            else []
          | _ => []
        acc ++ innerErrors ++ fieldError
      | .Local _ | .Declare _ => acc) []
    targetErrors ++ validateDiamondFieldAccessesForStmtExpr model value
  | .IfThenElse c t e =>
    let errs := validateDiamondFieldAccessesForStmtExpr model c ++
                validateDiamondFieldAccessesForStmtExpr model t
    match e with
    | some eb => errs ++ validateDiamondFieldAccessesForStmtExpr model eb
    | none => errs
  | .While c invs _ b =>
    let errs := validateDiamondFieldAccessesForStmtExpr model c ++
                validateDiamondFieldAccessesForStmtExpr model b
    invs.attach.foldl (fun acc ⟨inv, _⟩ => acc ++ validateDiamondFieldAccessesForStmtExpr model inv) errs
  | .Assert cond => validateDiamondFieldAccessesForStmtExpr model cond.condition
  | .Assume cond => validateDiamondFieldAccessesForStmtExpr model cond
  | .PrimitiveOp _ args =>
    args.attach.foldl (fun acc ⟨a, _⟩ => acc ++ validateDiamondFieldAccessesForStmtExpr model a) []
  | .StaticCall _ args =>
    args.attach.foldl (fun acc ⟨a, _⟩ => acc ++ validateDiamondFieldAccessesForStmtExpr model a) []
  | .Return (some v) => validateDiamondFieldAccessesForStmtExpr model v
  | _ => []
  termination_by sizeOf expr
  decreasing_by
    all_goals simp_wf
    all_goals (try have := AstNode.sizeOf_val_lt expr)
    all_goals (try have := AstNode.sizeOf_val_lt t)
    all_goals (try have := Condition.sizeOf_condition_lt ‹_›)
    all_goals (try term_by_mem)
    all_goals (try omega)
    -- For nested Variable.Field in Var (.Field ..) case
    all_goals (cases expr; rename_i val _ _ _h; subst _h; simp_all; omega)

/--
Validate a Laurel program for diamond-inherited field accesses.
Returns an array of DiagnosticModel errors.
-/
def validateDiamondFieldAccesses (model: SemanticModel) (program : Program) : List DiagnosticModel :=
  let errors := program.staticProcedures.foldl (fun acc proc =>
    let bodyErrors := match proc.body with
      | .Transparent bodyExpr => validateDiamondFieldAccessesForStmtExpr model bodyExpr
      | .Opaque postconds impl _ =>
        let postErrors := postconds.foldl (fun acc2 pc => acc2 ++ validateDiamondFieldAccessesForStmtExpr model pc.condition) []
        let implErrors := match impl with
          | some implExpr => validateDiamondFieldAccessesForStmtExpr model implExpr
          | none => []
        postErrors ++ implErrors
      | .Abstract postconds => postconds.foldl (fun acc p => acc ++ validateDiamondFieldAccessesForStmtExpr model p.condition) []
      | .External => []
    acc ++ bodyErrors) []
  errors

/--
Lower `IsType target ty` to Laurel-level map lookups:
  `select(select(ancestorsPerType(), Composite..typeTag!(target)), TypeName_TypeTag())`
-/
def lowerIsType (target : StmtExprMd) (ty : HighTypeMd) (source : Option FileRange) : StmtExprMd :=
  match ty.val with
    | .UserDefined name => let typeName := name.text
        let typeTag := mkMd (.StaticCall "Composite..typeTag!" [target])
        let ancestorsPerType := mkMd (.StaticCall "ancestorsPerType" [])
        let innerMap := mkMd (.StaticCall "select" [ancestorsPerType, typeTag])
        let typeConst := mkMd (.StaticCall (mkId $ typeName ++ "_TypeTag") [])
        ⟨.StaticCall "select" [innerMap, typeConst], source⟩
    | _ => { val := .Hole, source := source }

/-- State for the type hierarchy rewrite monad -/
structure THState where
  freshCounter : Nat := 0

@[expose] abbrev THM := StateM THState

private def freshVarName : THM Identifier := do
  let s ← get
  set { s with freshCounter := s.freshCounter + 1 }
  return s!"$th_tmp{s.freshCounter}"

/--
Lower `New name` to a block that:
1. Reads the current heap counter via `Heap..nextReference($heap)`
2. Increments the heap via `$heap := increment($heap)`
3. Constructs a `MkComposite(counter, name_TypeTag())` value
-/
def lowerNew (name : Identifier) (source : Option FileRange) : THM StmtExprMd := do
  let heapVar : Identifier := "$heap"
  let freshVar ← freshVarName
  let getCounter := mkMd (.StaticCall "Heap..nextReference!" [mkMd (.Var (.Local heapVar))])
  let saveCounter := mkMd (.Assign [mkVarMd (.Declare ⟨freshVar, ⟨.TInt, none⟩⟩)] getCounter)
  let newHeap := mkMd (.StaticCall "increment" [mkMd (.Var (.Local heapVar))])
  let updateHeap := mkMd (.Assign [mkVarMd (.Local heapVar)] newHeap)
  let compositeResult := mkMd (.StaticCall "MkComposite" [mkMd (.Var (.Local freshVar)), mkMd (.StaticCall (name.text ++ "_TypeTag") [])])
  return { val := .Block [saveCounter, updateHeap, compositeResult] none, source := source }

/-- Local rewrite of `IsType` and `New` nodes. Recursion is handled by `mapStmtExprM`. -/
private def rewriteTypeHierarchyNode (exprMd : StmtExprMd) : THM StmtExprMd := do
  match exprMd.val with
  | .New name => lowerNew name exprMd.source
  | .IsType target ty => return lowerIsType target ty exprMd.source
  | _ => return exprMd

/--
Type hierarchy transformation pass (Laurel → Laurel).

1. Rewrites `IsType target ty` into `select(select(ancestorsPerType(), Composite..typeTag!(target)), TypeName_TypeTag())`
2. Rewrites `New name` into heap allocation + `MkComposite` construction
3. Generates the `TypeTag` datatype with one constructor per composite type
4. Generates type hierarchy constants (`ancestorsFor<Type>`, `ancestorsPerType`)
-/
def typeHierarchyTransform (model: SemanticModel) (program : Program) : Program :=
  let compositeNames := program.types.filterMap fun td =>
    match td with
    | .Composite ct => some ct.name.text
    | _ => none
  let typeTagDatatype : TypeDefinition :=
    .Datatype { name := "TypeTag", typeArgs := [], constructors := compositeNames.map fun n => { name := (mkId $ n ++ "_TypeTag"), args := [] } }
  let typeHierarchyConstants := generateTypeHierarchyDecls model program
  let (procs', _) := (program.staticProcedures.mapM (mapProcedureM (mapStmtExprM rewriteTypeHierarchyNode))).run {}
  -- Update the Composite datatype to include the typeTag field (introduced in this phase)
  let typeTagTy : HighTypeMd := ⟨.UserDefined "TypeTag", none⟩
  let remainingTypes := program.types.map fun td =>
    match td with
    | .Datatype dt =>
      if dt.name.text == "Composite" then
        .Datatype { dt with constructors := dt.constructors.map fun c =>
          if c.name.text == "MkComposite" then
            { c with args := c.args ++ [{ name := ("typeTag" : Identifier), type := typeTagTy }] }
          else c }
      else td
    | _ => td
  { program with
    staticProcedures := procs',
    types := [typeTagDatatype] ++ remainingTypes,
    constants := program.constants ++ typeHierarchyConstants }

end Strata.Laurel

end -- public section
