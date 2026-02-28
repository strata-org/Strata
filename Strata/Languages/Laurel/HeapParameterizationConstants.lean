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
private def compositeTy := mkTy (.UserDefined (mkId "Composite"))
private def fieldTy := mkTy (.UserDefined (mkId "Field"))
private def boxTy := mkTy (.UserDefined (mkId "Box"))
private def heapTy := mkTy (.UserDefined (mkId "Heap"))
private def typeTagTy := mkTy (.UserDefined (mkId "TypeTag"))
private def mapFieldBox := mkTy (.TMap fieldTy boxTy)
private def mapCompositeInner := mkTy (.TMap compositeTy mapFieldBox)

-- Composite: datatype with a reference (int) and a runtime type tag
def compositeDatatype : TypeDefinition :=
  .Datatype { name := mkId "Composite", typeArgs := [], constructors := [
    { name := mkId "MkComposite", args := [
      { name := mkId "ref", type := intTy },
      { name := mkId "typeTag", type := typeTagTy }
    ]}
  ]}

-- Box: tagged union for field values
private def boxDatatype : TypeDefinition :=
  .Datatype { name := mkId "Box", typeArgs := [], constructors := [
    { name := mkId "BoxInt", args := [{ name := mkId "intVal", type := intTy }] },
    { name := mkId "BoxBool", args := [{ name := mkId "boolVal", type := boolTy }] },
    { name := mkId "BoxFloat64", args := [{ name := mkId "float64Val", type := float64Ty }] },
    { name := mkId "BoxComposite", args := [{ name := mkId "compositeVal", type := compositeTy }] }
  ]}

-- Heap: contains the data map and a nextReference for allocation
private def heapDatatype : TypeDefinition :=
  .Datatype { name := mkId "Heap", typeArgs := [], constructors := [
    { name := mkId "MkHeap", args := [
      { name := mkId "data", type := mapCompositeInner },
      { name := mkId "nextReference", type := intTy }
    ]}
  ]}
-- readField(heap, obj, field) = Heap..data(heap)[obj][field]
private def readFieldFn : Procedure :=
  { name := mkId "readField"
    inputs := [
      { name := mkId "heap", type := heapTy },
      { name := mkId "obj", type := compositeTy },
      { name := mkId "field", type := fieldTy }
    ]
    outputs := [{ name := mkId "result", type := boxTy }]
    preconditions := []
    determinism := .deterministic none
    decreases := none
    isFunctional := true
    body := .Transparent (mkE (.StaticCall (mkId "select")
      [mkE (.StaticCall (mkId "select")
        [mkE (.StaticCall (mkId "Heap..data") [mkE (.Identifier (mkId "heap"))]),
         mkE (.Identifier (mkId "obj"))]),
       mkE (.Identifier (mkId "field"))]))
    md := md }

-- updateField(heap, obj, field, val) =
--   MkHeap(Heap..data(heap)[obj := Heap..data(heap)[obj][field := val]], Heap..nextReference(heap))
private def updateFieldFn : Procedure :=
  { name := mkId "updateField"
    inputs := [
      { name := mkId "heap", type := heapTy },
      { name := mkId "obj", type := compositeTy },
      { name := mkId "field", type := fieldTy },
      { name := mkId "val", type := boxTy }
    ]
    outputs := [{ name := mkId "result", type := heapTy }]
    preconditions := []
    determinism := .deterministic none
    decreases := none
    isFunctional := true
    body := .Transparent (mkE (.StaticCall (mkId "MkHeap") [
      mkE (.StaticCall (mkId "update")
        [mkE (.StaticCall (mkId "Heap..data") [mkE (.Identifier (mkId "heap"))]),
         mkE (.Identifier (mkId "obj")),
         mkE (.StaticCall (mkId "update")
           [mkE (.StaticCall (mkId "select")
             [mkE (.StaticCall (mkId "Heap..data") [mkE (.Identifier (mkId "heap"))]),
              mkE (.Identifier (mkId "obj"))]),
            mkE (.Identifier (mkId "field")),
            mkE (.Identifier (mkId "val"))])]),
      mkE (.StaticCall (mkId "Heap..nextReference") [mkE (.Identifier (mkId "heap"))])
    ]))
    md := md }

-- increment(heap) = MkHeap(Heap..data(heap), Heap..nextReference(heap) + 1)
private def incrementFn : Procedure :=
  { name := mkId "increment"
    inputs := [{ name := mkId "heap", type := heapTy }]
    outputs := [{ name := mkId "result", type := heapTy }]
    preconditions := []
    determinism := .deterministic none
    decreases := none
    isFunctional := true
    body := .Transparent (mkE (.StaticCall (mkId "MkHeap") [
      mkE (.StaticCall (mkId "Heap..data") [mkE (.Identifier (mkId "heap"))]),
      mkE (.PrimitiveOp .Add [
        mkE (.StaticCall (mkId "Heap..nextReference") [mkE (.Identifier (mkId "heap"))]),
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
