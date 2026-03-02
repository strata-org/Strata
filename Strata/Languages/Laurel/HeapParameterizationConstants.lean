/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel

namespace Strata.Laurel

/--
The Laurel Core prelude defines the heap model types and operations
used by the Laurel-to-Core translator. These declarations are expressed
as Laurel AST and prepended to the source program during the
HeapParameterization phase.

The heap model uses:
- `Composite` - datatype with a reference (int) and a runtime type tag
- `Field` - abstract type for field names (zero-constructor datatype)
- `TypeTag` - abstract type for type tags (zero-constructor datatype)
- `Box` - tagged union for field values (int, bool, float64, Composite)
- `Heap` - datatype with a `data` map and a `nextReference` for allocation
- `readField` / `updateField` / `increment` - heap access functions
-/

private def md : Imperative.MetaData Core.Expression := #[]
private def mkTy (t : HighType) : HighTypeMd := ⟨t, md⟩
private def mkE (e : StmtExpr) : StmtExprMd := ⟨e, md⟩

-- Shorthand types
private def intTy := mkTy .TInt
private def boolTy := mkTy .TBool
private def float64Ty := mkTy .TFloat64
private def compositeTy := mkTy (.UserDefined "Composite")
private def fieldTy := mkTy (.UserDefined "Field")
private def boxTy := mkTy (.UserDefined "Box")
private def heapTy := mkTy (.UserDefined "Heap")
private def typeTagTy := mkTy (.UserDefined "TypeTag")
private def mapFieldBox := mkTy (.TMap fieldTy boxTy)
private def mapCompositeInner := mkTy (.TMap compositeTy mapFieldBox)

-- Composite: datatype with a reference (int) and a runtime type tag
def compositeDatatype : TypeDefinition :=
  .Datatype { name := "Composite", typeArgs := [], constructors := [
    { name := "MkComposite", args := [
      { name := "ref", type := intTy }
    ]}
  ]}

-- Box: tagged union for field values
private def boxDatatype : TypeDefinition :=
  .Datatype { name := "Box", typeArgs := [], constructors := [
    { name := "BoxInt", args := [{ name := "intVal", type := intTy }] },
    { name := "BoxBool", args := [{ name := "boolVal", type := boolTy }] },
    { name := "BoxFloat64", args := [{ name := "float64Val", type := float64Ty }] },
    { name := "BoxComposite", args := [{ name := "compositeVal", type := compositeTy }] }
  ]}

-- Heap: contains the data map and a nextReference for allocation
private def heapDatatype : TypeDefinition :=
  .Datatype { name := "Heap", typeArgs := [], constructors := [
    { name := "MkHeap", args := [
      { name := "data", type := mapCompositeInner },
      { name := "nextReference", type := intTy }
    ]}
  ]}
-- readField(heap, obj, field) = Heap..data(heap)[obj][field]
private def readFieldFn : Procedure :=
  { name := "readField"
    inputs := [
      { name := "heap", type := heapTy },
      { name := "obj", type := compositeTy },
      { name := "field", type := fieldTy }
    ]
    outputs := [{ name := "result", type := boxTy }]
    preconditions := []
    determinism := .deterministic none
    decreases := none
    isFunctional := true
    body := .Transparent (mkE (.StaticCall "select"
      [mkE (.StaticCall "select"
        [mkE (.StaticCall "Heap..data" [mkE (.Identifier "heap")]),
         mkE (.Identifier "obj")]),
       mkE (.Identifier "field")]))
    md := md }

-- updateField(heap, obj, field, val) =
--   MkHeap(Heap..data(heap)[obj := Heap..data(heap)[obj][field := val]], Heap..nextReference(heap))
private def updateFieldFn : Procedure :=
  { name := "updateField"
    inputs := [
      { name := "heap", type := heapTy },
      { name := "obj", type := compositeTy },
      { name := "field", type := fieldTy },
      { name := "val", type := boxTy }
    ]
    outputs := [{ name := "result", type := heapTy }]
    preconditions := []
    determinism := .deterministic none
    decreases := none
    isFunctional := true
    body := .Transparent (mkE (.StaticCall "MkHeap" [
      mkE (.StaticCall "update"
        [mkE (.StaticCall "Heap..data" [mkE (.Identifier "heap")]),
         mkE (.Identifier "obj"),
         mkE (.StaticCall "update"
           [mkE (.StaticCall "select"
             [mkE (.StaticCall "Heap..data" [mkE (.Identifier "heap")]),
              mkE (.Identifier "obj")]),
            mkE (.Identifier "field"),
            mkE (.Identifier "val")])]),
      mkE (.StaticCall "Heap..nextReference" [mkE (.Identifier "heap")])
    ]))
    md := md }

-- increment(heap) = MkHeap(Heap..data(heap), Heap..nextReference(heap) + 1)
private def incrementFn : Procedure :=
  { name := "increment"
    inputs := [{ name := "heap", type := heapTy }]
    outputs := [{ name := "result", type := heapTy }]
    preconditions := []
    determinism := .deterministic none
    decreases := none
    isFunctional := true
    body := .Transparent (mkE (.StaticCall "MkHeap" [
      mkE (.StaticCall "Heap..data" [mkE (.Identifier "heap")]),
      mkE (.PrimitiveOp .Add [
        mkE (.StaticCall "Heap..nextReference" [mkE (.Identifier "heap")]),
        mkE (.LiteralInt 1)])
    ]))
    md := md }

/-- The Laurel Core prelude as a Laurel Program. -/
def laurelPrelude : Program :=
  { staticProcedures := [readFieldFn, updateFieldFn, incrementFn]
    staticFields := []
    types := [compositeDatatype, boxDatatype, heapDatatype]
    constants := [] }

end Strata.Laurel
