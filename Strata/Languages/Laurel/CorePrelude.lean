/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Core.DDMTransform.Parse
import Strata.Languages.Core.Verifier

namespace Strata.Laurel

/--
The Laurel Core prelude defines the heap model types and operations
used by the Laurel-to-Core translator. These declarations are written
in Core grammar and parsed via DDM, replacing the previous hand-built
Lean AST definitions.

The heap model uses:
- `Composite` - abstract type for object references
- `Field` - abstract type for field names
- `Box` - tagged union for field values (int, bool, real, Composite)
- `readField` / `updateField` - heap access functions using nested maps
-/
def corePreludeDDM :=
#strata
program Core;

// Abstract types for the heap model
type Field;
type Composite;

// Tagged union for field values
datatype Box () {
  BoxInt(intVal: int),
  BoxBool(boolVal: bool),
  BoxFloat64(float64Val: real),
  BoxComposite(compositeVal: Composite)
};

// Read a field from the heap: readField(heap, obj, field) = heap[obj][field]
function readField(heap: Map Composite (Map Field Box), obj: Composite, field: Field) : Box {
  heap[obj][field]
}

// Update a field in the heap: updateField(heap, obj, field, val) = heap[obj := heap[obj][field := val]]
function updateField(heap: Map Composite (Map Field Box), obj: Composite, field: Field, val: Box) : Map Composite (Map Field Box) {
  heap[obj := heap[obj][field := val]]
}

#end

def corePrelude : Core.Program :=
  Core.getProgram corePreludeDDM |>.fst

end Strata.Laurel
