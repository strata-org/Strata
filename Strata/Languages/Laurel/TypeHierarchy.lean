/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Laurel.HeapParameterizationConstants
import Strata.Util.Tactics
public import Strata.Languages.Laurel.LaurelPass
public import Strata.Languages.Laurel.Resolution
import Std.Tactic.BVDecide.Normalize.Prop
import Strata.Languages.Laurel.LaurelTypes
import Strata.Languages.Laurel.MapStmtExpr

public section

namespace Strata.Laurel

open Strata

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
  let heapVar := heapVarName
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
Rewrite a type so that every reference to a composite type (a name in
`composites`) becomes the flattened `Composite` datatype. After the type
hierarchy pass all composite values are represented by `Composite` references,
so their *static* types must follow suit; otherwise re-resolution sees a
`Pixel`-typed value flowing into a `Composite`-typed slot (`readField`,
`Composite..ref!`, an allocation `new C`, …). Recurses through compound types. -/
partial def compositeRefToComposite (composites : Std.HashSet String) (ty : HighTypeMd) : HighTypeMd :=
  match ty.val with
  | .UserDefined name =>
    if composites.contains name.text then { ty with val := .UserDefined "Composite" } else ty
  | .TSet et => { ty with val := .TSet (compositeRefToComposite composites et) }
  | .TMap kt vt =>
    { ty with val := .TMap (compositeRefToComposite composites kt) (compositeRefToComposite composites vt) }
  | .Applied base args =>
    { ty with val := .Applied (compositeRefToComposite composites base) (args.map (compositeRefToComposite composites ·)) }
  | .Pure base => { ty with val := .Pure (compositeRefToComposite composites base) }
  | .Intersection tys => { ty with val := .Intersection (tys.map (compositeRefToComposite composites ·)) }
  | _ => ty

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
  mapProgramHighTypes (compositeRefToComposite compositeSet) transformed

/-- Pipeline pass: type hierarchy transform. -/
public def typeHierarchyTransformPass : LaurelPass where
  name := "TypeHierarchyTransform"
  documentation := "Encodes the object-oriented type hierarchy (inheritance, dynamic dispatch, type tests, and casts) into explicit operations on a flat representation. Composite types with parents are flattened, and dynamic dispatch is resolved through type-test chains."
  needsResolves := false -- Only resolve again after completing HeapParam, ModifiesClauses and TypeHierarchy. These are logically one pass.
  run := fun p m =>
    (typeHierarchyTransform m p, [], {})

end Strata.Laurel

end -- public section
