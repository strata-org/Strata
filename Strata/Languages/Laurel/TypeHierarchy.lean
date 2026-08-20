/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

import Strata.Languages.Laurel.HeapParameterizationConstants
import Strata.Util.Tactics
public import Strata.Languages.Laurel.LaurelPass
public import Strata.Languages.Laurel.Resolution
import Std.Tactic.BVDecide.Normalize.Prop
import Strata.Languages.Laurel.HeapParameterization
import Strata.Languages.Laurel.LaurelTypes
import Strata.Languages.Laurel.MapStmtExpr

public section

namespace Strata.Laurel

open Strata

private def mkMd (e : StmtExpr) (source : FileRange) : StmtExprMd := ⟨e, source⟩
private def mkVarMd (v : Variable) (source : FileRange) : VariableMd := ⟨v, source⟩

/-- Synthetic source location for compiler-generated type hierarchy nodes. -/
private def syntheticSource : FileRange :=
  { file := .file "Strata/Languages/Laurel/TypeHierarchy.lean", range := SourceRange.none }

/--
Generate Laurel constant definitions for the type hierarchy:
- A `ancestorsFor<Type>` constant per composite type.
It enables checking for `<Type>` whether it is assignable to another type using a TotalMap lookup.
- A `ancestorsPerType` constant combining the per-type constants.
It enables checking for any type whether it is assignable to any other type using two TotalMap lookups.
We use this to translate `<value> is <Type>`.
The runtime type of `<value>` is used for the outer TotalMap lookup while `<Type>` for the inner one.

-/
def generateTypeHierarchyDecls (model : SemanticModel) (program: Program) : Except String (List Constant) := do
  let composites := program.types.filterMap fun td => match td with
    | .Composite ct => some ct
    | _ => none
  if composites.isEmpty then return [] else
  let typeTagTy : HighTypeMd := ⟨.UserDefined "TypeTag", syntheticSource⟩
  let boolTy : HighTypeMd := ⟨.TBool, syntheticSource⟩
  let innerMapTy : HighTypeMd := ⟨.TMap typeTagTy boolTy, syntheticSource⟩
  let outerMapTy : HighTypeMd := ⟨.TMap typeTagTy innerMapTy, syntheticSource⟩
  -- Helper: build an inner map (TotalMap TypeTag bool) for a given composite type
  -- Start with mapConst(false), then update each composite type's entry
  let mkInnerMap (ct : CompositeType) : Except String StmtExprMd := do
    let ancestors ← computeAncestors model ct.name
    let falseConst := mkMd (.LiteralBool false) syntheticSource
    let emptyInner := mkMd (.StaticCall "mapConst" [falseConst]) syntheticSource
    composites.foldlM (init := emptyInner) fun acc otherCt => do
      let isAncestor ← ancestors.anyM (fun anc => otherCt.name.sameId anc.name)
      if isAncestor then
        let otherConst := mkMd (.StaticCall (mkId $ otherCt.name.text ++ "_TypeTag") []) syntheticSource
        let boolVal := mkMd (.LiteralBool true) syntheticSource
        pure (mkMd (.StaticCall "update" [acc, otherConst, boolVal]) syntheticSource)
      else pure acc
  -- Generate a separate constant `ancestorsFor<Type>` for each composite type
  let ancestorsForDecls : List Constant ← composites.mapM fun ct => do
    let innerMap ← mkInnerMap ct
    pure { name := s!"ancestorsFor{ct.name.text}", type := innerMapTy, initializer := some innerMap }
  -- Build ancestorsPerType by referencing the individual ancestorsFor<Type> constants
  let falseConst := mkMd (.LiteralBool false) syntheticSource
  let emptyInner := mkMd (.StaticCall "mapConst" [falseConst]) syntheticSource
  let emptyOuter := mkMd (.StaticCall "mapConst" [emptyInner]) syntheticSource
  let outerMapExpr := composites.foldl (fun acc ct =>
    let typeConst := mkMd (.StaticCall (mkId $ ct.name.text ++ "_TypeTag") []) syntheticSource
    let innerMapRef := mkMd (.StaticCall s!"ancestorsFor{ct.name.text}" []) syntheticSource
    mkMd (.StaticCall "update" [acc, typeConst, innerMapRef]) syntheticSource
  ) emptyOuter
  let ancestorsDecl : Constant :=
    { name := "ancestorsPerType"
      type := outerMapTy
      initializer := some outerMapExpr }
  pure (ancestorsForDecls ++ [ancestorsDecl])

/--
Lower `IsType target ty` to Laurel-level map lookups:
  `select(select(ancestorsPerType(), Composite..typeTag!(target)), TypeName_TypeTag())`
-/
def lowerIsType (target : StmtExprMd) (ty : HighTypeMd) (source : FileRange) : StmtExprMd :=
  match ty.val with
    | .UserDefined name => let typeName := name.text
        let typeTag := mkMd (.StaticCall "Composite..typeTag!" [target]) source
        let ancestorsPerType := mkMd (.StaticCall "ancestorsPerType" []) source
        let innerMap := mkMd (.StaticCall "select" [ancestorsPerType, typeTag]) source
        let typeConst := mkMd (.StaticCall (mkId $ typeName ++ "_TypeTag") []) source
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
def lowerNew (name : Identifier) (source : FileRange) : THM StmtExprMd := do
  let heapVar := heapVarName
  let freshVar ← freshVarName
  let getCounter := mkMd (.StaticCall "Heap..nextReference!" [mkMd (.Var (.Local heapVar)) source]) source
  let saveCounter := mkMd (.Assign [mkVarMd (.Declare ⟨freshVar, some ⟨.TInt, source⟩⟩) source] getCounter) source
  let newHeap := mkMd (.StaticCall "increment" [mkMd (.Var (.Local heapVar)) source]) source
  let updateHeap := mkMd (.Assign [mkVarMd (.Local heapVar) source] newHeap) source
  let compositeResult := mkMd (.StaticCall "MkComposite" [mkMd (.Var (.Local freshVar)) source, mkMd (.StaticCall (name.text ++ "_TypeTag") []) source]) source
  return { val := .Block [saveCounter, updateHeap, compositeResult] none, source := source }

/-- Local rewrite of `IsType` and `New` nodes. Recursion is handled by `mapStmtExprM`. -/
private def rewriteTypeHierarchyNode (exprMd : StmtExprMd) : THM StmtExprMd := do
  match exprMd.val with
  -- Type args are already stripped by MonomorphizeComposites (`new C<τ>` → `new C$…`),
  -- so lowering keys off the concrete name and the residual `_` is safely ignored.
  | .New name _ => lowerNew name exprMd.source
  | .IsType target ty => return lowerIsType target ty exprMd.source
  | _ => return exprMd

/--
Rewrite a type so that every reference to a composite type (a name in
`composites`) becomes the flattened `Composite` datatype. After the type
hierarchy pass all composite values are represented by `Composite` references,
so their *static* types must follow suit; otherwise re-resolution sees a
`Pixel`-typed value flowing into a `Composite`-typed slot (`readField`,
`Composite..ref!`, an allocation `new C`, …). Recurses through compound types. -/
def compositeRefToComposite (composites : Std.HashSet String) (ty : HighTypeMd) : HighTypeMd :=
  match _h : ty.val with
  | .UserDefined name =>
    if composites.contains name.text then { ty with val := .UserDefined "Composite" } else ty
  | .TSet et => { ty with val := .TSet (compositeRefToComposite composites et) }
  | .TMap kt vt =>
    { ty with val := .TMap (compositeRefToComposite composites kt) (compositeRefToComposite composites vt) }
  | .Applied base args =>
    { ty with val := .Applied (compositeRefToComposite composites base) (args.attach.map (fun ⟨a, _⟩ => compositeRefToComposite composites a)) }
  | .Intersection tys => { ty with val := .Intersection (tys.attach.map (fun ⟨t, _⟩ => compositeRefToComposite composites t)) }
  | _ => ty
  termination_by ty
  decreasing_by ast_recursion_decreasing

/--
Type hierarchy transformation pass (Laurel → Laurel).

1. Rewrites `IsType target ty` into `select(select(ancestorsPerType(), Composite..typeTag!(target)), TypeName_TypeTag())`
2. Rewrites `New name` into heap allocation + `MkComposite` construction
3. Generates the `TypeTag` datatype with one constructor per composite type
4. Generates type hierarchy constants (`ancestorsFor<Type>`, `ancestorsPerType`)
-/
def typeHierarchyTransform (model: SemanticModel) (program : Program) : Except String Program := do
  let compositeNames := program.types.filterMap fun td =>
    match td with
    | .Composite ct => some ct.name.text
    | _ => none
  let typeTagDatatype : TypeDefinition :=
    .Datatype { name := "TypeTag", typeArgs := [], constructors := compositeNames.map fun n => { name := (mkId $ n ++ "_TypeTag"), args := [] } }
  let typeHierarchyConstants ← generateTypeHierarchyDecls model program
  let (procs', _) := (program.staticProcedures.mapM (mapProcedureM (mapStmtExprM rewriteTypeHierarchyNode))).run {}
  -- Update the Composite datatype to include the typeTag field (introduced in this phase)
  let typeTagTy : HighTypeMd := ⟨.UserDefined "TypeTag", syntheticSource⟩
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
  let transformed : Program :=
    { program with
      staticProcedures := procs',
      types := [typeTagDatatype] ++ remainingTypes,
      constants := program.constants ++ typeHierarchyConstants }
  -- Now that `New`/`IsType` have been lowered (they needed the original
  -- composite names), flatten every remaining composite reference type to the
  -- `Composite` datatype so the program re-resolves consistently. The
  -- program-wide `HighType` traversal lives in `MapStmtExpr` so that every
  -- type position is covered uniformly.
  let compositeSet : Std.HashSet String :=
    compositeNames.foldl (init := {}) (·.insert ·)
  pure (mapProgramHighTypes (compositeRefToComposite compositeSet) transformed)

/-- Pipeline pass: type hierarchy transform. -/
public def typeHierarchyTransformPass : LoweringPass where
  name := "TypeHierarchyTransform"
  documentation := "Encodes the object-oriented type hierarchy (inheritance, dynamic dispatch, type tests, and casts) into explicit operations on a flat representation. Composite types with parents are flattened, and dynamic dispatch is resolved through type-test chains."
  needsResolves := false -- Only resolve again after completing HeapParam, ModifiesClauses and TypeHierarchy. These are logically one pass.
  comesAfter := [⟨ heapParameterizationPass.meta, "the type hierarchy pass modifies the 'Composite' datatype that is introduced by this pass."⟩]
  run := fun _ p m =>
    match typeHierarchyTransform m p with
    | .ok p' => (p', [], {})
    | .error e => (p, [Message.fromString e .strataBug], {})

end Strata.Laurel

end -- public section
