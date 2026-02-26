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
def computeAncestors (types : List TypeDefinition) (name : Identifier) : List CompositeType :=
  let rec go (fuel : Nat) (current : Identifier) : List CompositeType :=
    match fuel with
    | 0 =>
      types.filterMap fun td => match td with
        | .Composite ct => if ct.name == current then some ct else none
        | _ => none
    | fuel' + 1 =>
      let self := types.filterMap fun td => match td with
        | .Composite ct => if ct.name == current then some ct else none
        | _ => none
      self ++ (types.foldl (fun acc td =>
        match td with
        | .Composite ct =>
          if ct.name == current then
            ct.extending.foldl (fun acc2 parent => acc2 ++ go fuel' parent) acc
          else acc
        | _ => acc) [])
  let seen : List Identifier := []
  (go types.length name).foldl (fun (acc, seen) ct =>
    if seen.contains ct.name then (acc, seen)
    else (acc ++ [ct], seen ++ [ct.name])) ([], seen) |>.1

private def mkMd (e : StmtExpr) : StmtExprMd := ⟨e, #[]⟩

/--
Generate Laurel constant definitions for the type hierarchy:
- A `ancestorsFor<Type>` constant per composite type.
It enables checking for `<Type>` whether it is assignable to another type using a Map lookup.
- A `ancestorsPerType` constant combining the per-type constants.
It enables checking for any type whether it is assignable to any other type using two Map lookups.
We use this to translate `<value> is <Type>`.
The runtime type of `<value>` is used for the outer Map lookup while `<Type>` for the inner one.

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
      let isAncestor := ancestors.any (·.name == otherCt.name)
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
def validateDiamondFieldAccessesForStmtExpr (uri : Uri) (types : List TypeDefinition) (env : TypeEnv)
    (expr : StmtExprMd) : List DiagnosticModel :=
  match _h : expr.val with
  | .FieldSelect target fieldName =>
    let targetErrors := validateDiamondFieldAccessesForStmtExpr uri types env target
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
      (acc ++ validateDiamondFieldAccessesForStmtExpr uri types env' s, env'')) ([], env)).1
  | .Assign targets value =>
    let targetErrors := targets.attach.foldl (fun acc ⟨t, _⟩ => acc ++ validateDiamondFieldAccessesForStmtExpr uri types env t) []
    targetErrors ++ validateDiamondFieldAccessesForStmtExpr uri types env value
  | .IfThenElse c t e =>
    let errs := validateDiamondFieldAccessesForStmtExpr uri types env c ++
                validateDiamondFieldAccessesForStmtExpr uri types env t
    match e with
    | some eb => errs ++ validateDiamondFieldAccessesForStmtExpr uri types env eb
    | none => errs
  | .LocalVariable _ _ (some init) =>
    validateDiamondFieldAccessesForStmtExpr uri types env init
  | .While c invs _ b =>
    let errs := validateDiamondFieldAccessesForStmtExpr uri types env c ++
                validateDiamondFieldAccessesForStmtExpr uri types env b
    invs.attach.foldl (fun acc ⟨inv, _⟩ => acc ++ validateDiamondFieldAccessesForStmtExpr uri types env inv) errs
  | .Assert cond => validateDiamondFieldAccessesForStmtExpr uri types env cond
  | .Assume cond => validateDiamondFieldAccessesForStmtExpr uri types env cond
  | .PrimitiveOp _ args =>
    args.attach.foldl (fun acc ⟨a, _⟩ => acc ++ validateDiamondFieldAccessesForStmtExpr uri types env a) []
  | .StaticCall _ args =>
    args.attach.foldl (fun acc ⟨a, _⟩ => acc ++ validateDiamondFieldAccessesForStmtExpr uri types env a) []
  | .Return (some v) => validateDiamondFieldAccessesForStmtExpr uri types env v
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
      | .Transparent bodyExpr => validateDiamondFieldAccessesForStmtExpr uri program.types env bodyExpr
      | .Opaque postconds impl _ =>
        let postErrors := postconds.foldl (fun acc2 pc => acc2 ++ validateDiamondFieldAccessesForStmtExpr uri program.types env pc) []
        let implErrors := match impl with
          | some implExpr => validateDiamondFieldAccessesForStmtExpr uri program.types env implExpr
          | none => []
        postErrors ++ implErrors
      | .Abstract postconds => postconds.foldl (fun acc p => acc ++ validateDiamondFieldAccessesForStmtExpr uri program.types env p) []
    acc ++ bodyErrors) []
  errors.toArray

/--
Lower `IsType target ty` to Laurel-level map lookups:
  `select(select(ancestorsPerType(), Composite..typeTag(target)), TypeName_TypeTag())`
-/
def lowerIsType (target : StmtExprMd) (ty : HighTypeMd) (md : Imperative.MetaData Core.Expression) : StmtExprMd :=
  let typeName := match ty.val with
    | .UserDefined name => name
    | _ => panic! s!"IsType: expected UserDefined type"
  let typeTag := mkMd (.StaticCall "Composite..typeTag" [target])
  let ancestorsPerType := mkMd (.StaticCall "ancestorsPerType" [])
  let innerMap := mkMd (.StaticCall "select" [ancestorsPerType, typeTag])
  let typeConst := mkMd (.StaticCall (typeName ++ "_TypeTag") [])
  ⟨.StaticCall "select" [innerMap, typeConst], md⟩

/-- State for the type hierarchy rewrite monad -/
structure THState where
  freshCounter : Nat := 0

abbrev THM := StateM THState

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
def lowerNew (name : Identifier) (md : Imperative.MetaData Core.Expression) : THM StmtExprMd := do
  let heapVar := "$heap"
  let freshVar ← freshVarName
  let getCounter := mkMd (.StaticCall "Heap..nextReference" [mkMd (.Identifier heapVar)])
  let saveCounter := mkMd (.LocalVariable freshVar ⟨.TInt, #[]⟩ (some getCounter))
  let newHeap := mkMd (.StaticCall "increment" [mkMd (.Identifier heapVar)])
  let updateHeap := mkMd (.Assign [mkMd (.Identifier heapVar)] newHeap)
  let compositeResult := mkMd (.StaticCall "MkComposite" [mkMd (.Identifier freshVar), mkMd (.StaticCall (name ++ "_TypeTag") [])])
  return ⟨ .Block [saveCounter, updateHeap, compositeResult] none, md ⟩

/--
Walk a StmtExpr AST and rewrite `IsType` and `New` nodes.
-/
def rewriteTypeHierarchyExpr (exprMd : StmtExprMd) : THM StmtExprMd :=
  match exprMd with
  | WithMetadata.mk expr md =>
  match expr with
  | .New name => lowerNew name md
  | .IsType target ty => do
      let target' ← rewriteTypeHierarchyExpr target
      return lowerIsType target' ty md
  | .IfThenElse c t e => do
      let e' ← match e with | some x => some <$> rewriteTypeHierarchyExpr x | none => pure none
      return ⟨.IfThenElse (← rewriteTypeHierarchyExpr c) (← rewriteTypeHierarchyExpr t) e', md⟩
  | .Block stmts label => do
      let stmts' ← stmts.attach.mapM fun ⟨s, _⟩ => rewriteTypeHierarchyExpr s
      return ⟨.Block stmts' label, md⟩
  | .LocalVariable n ty i => do
      let i' ← match i with | some x => some <$> rewriteTypeHierarchyExpr x | none => pure none
      return ⟨.LocalVariable n ty i', md⟩
  | .While c invs d b => do
      let d' ← match d with | some x => some <$> rewriteTypeHierarchyExpr x | none => pure none
      let invs' ← invs.attach.mapM fun ⟨inv, _⟩ => rewriteTypeHierarchyExpr inv
      return ⟨.While (← rewriteTypeHierarchyExpr c) invs' d' (← rewriteTypeHierarchyExpr b), md⟩
  | .Return v => do
      let v' ← match v with | some x => some <$> rewriteTypeHierarchyExpr x | none => pure none
      return ⟨.Return v', md⟩
  | .Assign targets v => do
      let targets' ← targets.attach.mapM fun ⟨t, _⟩ => rewriteTypeHierarchyExpr t
      return ⟨.Assign targets' (← rewriteTypeHierarchyExpr v), md⟩
  | .FieldSelect t f => do return ⟨.FieldSelect (← rewriteTypeHierarchyExpr t) f, md⟩
  | .PureFieldUpdate t f v => do return ⟨.PureFieldUpdate (← rewriteTypeHierarchyExpr t) f (← rewriteTypeHierarchyExpr v), md⟩
  | .StaticCall callee args => do
      let args' ← args.attach.mapM fun ⟨a, _⟩ => rewriteTypeHierarchyExpr a
      return ⟨.StaticCall callee args', md⟩
  | .PrimitiveOp op args => do
      let args' ← args.attach.mapM fun ⟨a, _⟩ => rewriteTypeHierarchyExpr a
      return ⟨.PrimitiveOp op args', md⟩
  | .ReferenceEquals l r => do return ⟨.ReferenceEquals (← rewriteTypeHierarchyExpr l) (← rewriteTypeHierarchyExpr r), md⟩
  | .AsType t ty => do return ⟨.AsType (← rewriteTypeHierarchyExpr t) ty, md⟩
  | .InstanceCall t callee args => do
      let args' ← args.attach.mapM fun ⟨a, _⟩ => rewriteTypeHierarchyExpr a
      return ⟨.InstanceCall (← rewriteTypeHierarchyExpr t) callee args', md⟩
  | .Forall n ty b => do return ⟨.Forall n ty (← rewriteTypeHierarchyExpr b), md⟩
  | .Exists n ty b => do return ⟨.Exists n ty (← rewriteTypeHierarchyExpr b), md⟩
  | .Assigned n => do return ⟨.Assigned (← rewriteTypeHierarchyExpr n), md⟩
  | .Old v => do return ⟨.Old (← rewriteTypeHierarchyExpr v), md⟩
  | .Fresh v => do return ⟨.Fresh (← rewriteTypeHierarchyExpr v), md⟩
  | .Assert c => do return ⟨.Assert (← rewriteTypeHierarchyExpr c), md⟩
  | .Assume c => do return ⟨.Assume (← rewriteTypeHierarchyExpr c), md⟩
  | .ProveBy v p => do return ⟨.ProveBy (← rewriteTypeHierarchyExpr v) (← rewriteTypeHierarchyExpr p), md⟩
  | .ContractOf ty f => do return ⟨.ContractOf ty (← rewriteTypeHierarchyExpr f), md⟩
  | _ => return exprMd
  termination_by sizeOf exprMd
  decreasing_by all_goals (simp_all; try term_by_mem)

def rewriteTypeHierarchyProcedure (proc : Procedure) : THM Procedure := do
  let preconditions' ← proc.preconditions.mapM rewriteTypeHierarchyExpr
  let body' ← match proc.body with
    | .Transparent b => pure (.Transparent (← rewriteTypeHierarchyExpr b))
    | .Opaque postconds impl modif =>
        let postconds' ← postconds.mapM rewriteTypeHierarchyExpr
        let impl' ← match impl with
          | some x => pure (some (← rewriteTypeHierarchyExpr x))
          | none => pure none
        let modif' ← modif.mapM rewriteTypeHierarchyExpr
        pure (.Opaque postconds' impl' modif')
    | .Abstract postconds => pure (.Abstract (← postconds.mapM rewriteTypeHierarchyExpr))
  return { proc with preconditions := preconditions', body := body' }

/--
Type hierarchy transformation pass (Laurel → Laurel).

1. Rewrites `IsType target ty` into `select(select(ancestorsPerType(), Composite..typeTag(target)), TypeName_TypeTag())`
2. Rewrites `New name` into heap allocation + `MkComposite` construction
3. Generates the `TypeTag` datatype with one constructor per composite type
4. Generates type hierarchy constants (`ancestorsFor<Type>`, `ancestorsPerType`)
-/
def typeHierarchyTransform (program : Program) : Program :=
  let compositeNames := program.types.filterMap fun td =>
    match td with
    | .Composite ct => some ct.name
    | _ => none
  let typeTagDatatype : TypeDefinition :=
    .Datatype { name := "TypeTag", typeArgs := [], constructors := compositeNames.map fun n => { name := n ++ "_TypeTag", args := [] } }
  let typeHierarchyConstants := generateTypeHierarchyDecls program.types
  let (procs', _) := (program.staticProcedures.mapM rewriteTypeHierarchyProcedure).run {}
  { program with
    staticProcedures := procs',
    types := program.types ++ [typeTagDatatype],
    constants := program.constants ++ typeHierarchyConstants }

end Laurel
