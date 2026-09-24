/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.AST
public import StrataLaurel.Implementation.LaurelAST
import StrataLaurel.Implementation.Grammar.ConcreteToAbstractTreeTranslator
import StrataLaurel.Implementation.Grammar.LaurelGrammar
import StrataDDM.Integration.Lean.HashCommands -- shake: keep

namespace Strata.Laurel

public section

/-- The name of the heap variable used by the heap parameterization pass. -/
def heapVarName : Identifier := "$heap"

/--
The Laurel Core prelude defines the heap model types and operations
used by the Laurel-to-Core translator. These declarations are expressed
in Laurel syntax via the `#strata program Laurel` macro and parsed into
a `Laurel.Program` at compile time.

The heap model uses:
- `Composite` - datatype with a reference (int); `TypeHierarchy` adds the runtime type tag
- `Field` - abstract type for field names (zero-constructor datatype)
- `TypeTag` - abstract type for type tags (zero-constructor datatype)
- `Heap` - datatype with a `data` map and a `nextReference` for allocation
- `readField` / `updateField` / `increment` - heap access functions

Note: `Field`, `TypeTag` and `$Box` are referenced here but declared by the passes --
`heapParameterization` and `typeHierarchyTransform` inject them, `$Box` with one variant per
field type the program actually uses.
-/

private def laurelPreludeDDM :=
#strata
program Laurel;

// Composite: datatype with a reference (int)
datatype Composite { MkComposite(ref: int) }

datatype NotSupportedYet {}

// Heap: contains the data map and a nextReference for allocation
datatype Heap {
  MkHeap(data: TotalMap Composite TotalMap Field $Box, nextReference: int)
}

// Read a field from the heap: readField(heap, obj, field) = Heap..data!(heap)[obj][field]
procedure readField(heap: Heap, obj: Composite, field: Field): $Box
  return select(select(Heap..data!(heap), obj), field);

// Update a field in the heap
procedure updateField(heap: Heap, obj: Composite, field: Field, val: $Box): Heap
  return MkHeap(
    update(Heap..data!(heap), obj,
      update(select(Heap..data!(heap), obj), field, val)),
    Heap..nextReference!(heap));

// Increment the heap allocation nextReference, returning a new heap
procedure increment(heap: Heap): Heap
  return MkHeap(Heap..data!(heap), Heap..nextReference!(heap) + 1);

#end

/-- The Laurel Core prelude as a Laurel Program. -/
def heapConstants : Program :=
  match Laurel.TransM.run
      (.file "StrataLaurel/Implementation/HeapParameterizationConstants.lean")
      (Laurel.parseProgram laurelPreludeDDM) (synthesized := true) with
  | .ok program => program
  | .error e => dbg_trace s!"BUG: Laurel heap prelude parse error: {e}"; default

/-! ### The names the prelude declares

`HeapParameterization`, `ModifiesClauses` and `TypeHierarchy` spell these names to build and to
recognise the heap model. The prelude above is what declares them, so a rename is one edit here. -/

/-- `readField(heap, obj, field)`, the field read. -/
def readFieldName : String := "readField"

/-- `updateField(heap, obj, field, val)`, the field write the heap model is built on. -/
def updateFieldName : String := "updateField"

/-- `increment(heap)`, allocation: raises `nextReference` and preserves `data`. -/
def incrementName : String := "increment"

/-- The heap-model datatype, threaded through every procedure that touches a field. -/
def heapTypeName : Identifier := "Heap"

def heapCtorName : String := "MkHeap"

/-- Core's unsafe destructor for `Heap`'s `data` field. -/
def heapDataAccessor : String := "Heap..data!"

def heapNextReferenceAccessor : String := "Heap..nextReference!"

/-- The datatype every composite (object) reference is flattened to by `TypeHierarchy`. -/
def compositeTypeName : Identifier := "Composite"

def compositeCtorName : String := "MkComposite"

def compositeRefAccessor : String := "Composite..ref!"

end -- public section

end Strata.Laurel
