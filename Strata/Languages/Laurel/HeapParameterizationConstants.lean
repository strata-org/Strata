/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator

namespace Strata.Laurel

/--
The Laurel Core prelude defines the heap model types and operations
used by the Laurel-to-Core translator. These declarations are expressed
in Laurel syntax via the `#strata program Laurel` macro and parsed into
a `Laurel.Program` at compile time.

The heap model uses:
- `Composite` - datatype with a reference (int) and a runtime type tag
- `Field` - abstract type for field names (zero-constructor datatype)
- `TypeTag` - abstract type for type tags (zero-constructor datatype)
- `Box` - tagged union for field values (int, bool, float64, Composite)
- `Heap` - datatype with a `data` map and a `nextReference` for allocation
- `readField` / `updateField` / `increment` - heap access functions
-/

private def laurelPreludeDDM :=
#strata
program Laurel;

// Composite: datatype with a reference (int)
datatype Composite { MkComposite(ref: int) }

// Box: tagged union for field values
datatype Box {
  BoxInt(intVal: int),
  BoxBool(boolVal: bool),
  BoxFloat64(float64Val: float64),
  BoxComposite(compositeVal: Composite)
}

// Heap: contains the data map and a nextReference for allocation
datatype Heap {
  MkHeap(data: Map Composite Map Field Box, nextReference: int)
}

// Read a field from the heap: readField(heap, obj, field) = Heap..data!(heap)[obj][field]
function readField(heap: Heap, obj: Composite, field: Field): Box {
  select(select(Heap..data!(heap), obj), field)
}

// Update a field in the heap
function updateField(heap: Heap, obj: Composite, field: Field, val: Box): Heap {
  MkHeap(
    update(Heap..data!(heap), obj,
      update(select(Heap..data!(heap), obj), field, val)),
    Heap..nextReference!(heap))
}

// Increment the heap allocation nextReference, returning a new heap
function increment(heap: Heap): Heap {
  MkHeap(Heap..data!(heap), Heap..nextReference!(heap) + 1)
}

// The #strata macro does not identify the end macro correctly,
// because Laurel's grammar also parses # signs
// Having this datatype here brings the parser in a state where it won't consume the #
// A fix would be to require ';' after the body of functions/procedures
datatype Workaround  {}
#end

/-- The Laurel Core prelude as a Laurel Program. -/
def heapConstants : Program :=
  let uri := Strata.Uri.file "Strata/Languages/Laurel/HeapParameterizationConstants.lean"
  match Laurel.TransM.run uri (Laurel.parseProgram laurelPreludeDDM) with
  | .ok program => program
  | .error e => panic! s!"Laurel heap prelude parse error: {e}"

end Strata.Laurel
