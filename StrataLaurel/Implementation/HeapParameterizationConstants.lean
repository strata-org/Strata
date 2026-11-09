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
a `Laurel.LaurelProgram` at compile time.

The heap model uses:
- `Field` - abstract type for field names (zero-constructor datatype)
- `Heap` - datatype with a `data` map and a `nextReference` for allocation
- `readField` / `updateField` / `increment` - heap access functions

Note: `Field` and `$Box` are referenced here but declared by `heapParameterization`, `$Box`
with one variant per field type the program actually uses.
-/

private def laurelPreludeDDM :=
#strata
program Laurel;

datatype NotSupportedYet {}

// Heap: contains the data map and a nextReference for allocation
datatype Heap {
  MkHeap(data: TotalMap int TotalMap Field $Box, nextReference: int)
}

// Read a field from the heap: readField(heap, obj, field) = Heap..data!(heap)[obj][field]
procedure readField(heap: Heap, obj: int, field: Field): $Box
  return select(select(Heap..data!(heap), obj), field);

// Update a field in the heap
procedure updateField(heap: Heap, obj: int, field: Field, val: $Box): Heap
  return MkHeap(
    update(Heap..data!(heap), obj,
      update(select(Heap..data!(heap), obj), field, val)),
    Heap..nextReference!(heap));

// Increment the heap allocation nextReference, returning a new heap
procedure increment(heap: Heap): Heap
  return MkHeap(Heap..data!(heap), Heap..nextReference!(heap) + 1);

#end

/-- The Laurel Core prelude as a Laurel Program. -/
def heapConstants : LaurelProgram :=
  match Laurel.TransM.run
      (.file "StrataLaurel/Implementation/HeapParameterizationConstants.lean")
      (Laurel.parseProgram laurelPreludeDDM) (synthesized := true) with
  | .ok program => program
  | .error e => dbg_trace s!"BUG: Laurel heap prelude parse error: {e}"; default

/-! ### The names the prelude declares

`HeapParameterization`, `ModifiesClauses` and `LowerComposite` spell these names to build and to
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

def compositeCtorName : String := "MkComposite"

end -- public section

end Strata.Laurel
