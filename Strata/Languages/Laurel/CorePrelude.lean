/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Core.DDMTransform.Grammar
import Strata.Languages.Core.Verifier

namespace Strata.Laurel

/--
The Laurel Core prelude defines the heap model types and operations
used by the Laurel-to-Core translator. These declarations are written
in Core grammar and parsed via DDM, replacing the previous hand-built
Lean AST definitions.

The heap model uses:
- `Composite` - type synonym for int (object references are integers)
- `Field` - abstract type for field names
- `Box` - tagged union for field values (int, bool, real, Composite)
- `Heap` - datatype with a `data` map and a `nextReference` for allocation
- `readField` / `updateField` - heap access functions using nested maps
-/
def corePreludeDDM :=
#strata
program Core;

// Abstract types for the heap model
type Field;
type Composite := int;

// Tagged union for field values
datatype Box () {
  BoxInt(intVal: int),
  BoxBool(boolVal: bool),
  BoxFloat64(float64Val: real),
  BoxComposite(compositeVal: Composite)
};

// Heap datatype: contains the data map and a nextReference for allocation
datatype Heap () {
  MkHeap(data: Map Composite (Map Field Box), nextReference: int)
};

// Read a field from the heap: readField(heap, obj, field) = Heap..data(heap)[obj][field]
function readField(heap: Heap, obj: Composite, field: Field) : Box {
  Heap..data(heap)[obj][field]
}

// Update a field in the heap
function updateField(heap: Heap, obj: Composite, field: Field, val: Box) : Heap {
  MkHeap(Heap..data(heap)[obj := Heap..data(heap)[obj][field := val]], Heap..nextReference(heap))
}

// Increment the heap allocation nextReference, returning a new heap
function increment(heap: Heap) : Heap {
  MkHeap(Heap..data(heap), Heap..nextReference(heap) + 1)
}

#end

def corePrelude : Core.Program :=
  Core.getProgram corePreludeDDM |>.fst

end Strata.Laurel
