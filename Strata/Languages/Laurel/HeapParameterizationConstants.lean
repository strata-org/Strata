/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.AST
import Strata.DDM.Integration.Lean.HashCommands -- shake: keep

public import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.Grammar.LaurelGrammar

namespace Strata.Laurel

public section

/--
The Laurel Core prelude defines the heap model types and operations
used by the Laurel-to-Core translator. These declarations are expressed
in Laurel syntax via the `#strata program Laurel` macro and parsed into
a `Laurel.Program` at compile time.

The heap model uses:
- `Composite` - datatype with a reference (int) and a runtime type tag
- `Field` - abstract type for field names (zero-constructor datatype)
- `TypeTag` - abstract type for type tags (zero-constructor datatype)
- `Heap` - datatype with a `data` map and a `nextReference` for allocation
- `readField` / `updateField` / `increment` - heap access functions

Note: The `Box` datatype is generated dynamically by `heapParameterization`
based on which field types are actually used in the program.
-/

private def laurelPreludeDDM :=
#strata
program Laurel;

// Composite: datatype with a reference (int)
datatype Composite { MkComposite(ref: int) }

datatype NotSupportedYet {}

// Heap: contains the data map and a nextReference for allocation
datatype Heap {
  MkHeap(data: Map Composite Map Field Box, nextReference: int)
}

// Read a field from the heap: readField(heap, obj, field) = Heap..data!(heap)[obj][field]
function readField(heap: Heap, obj: Composite, field: Field): Box {
  select(select(Heap..data!(heap), obj), field)
};

// Update a field in the heap
function updateField(heap: Heap, obj: Composite, field: Field, val: Box): Heap {
  MkHeap(
    update(Heap..data!(heap), obj,
      update(select(Heap..data!(heap), obj), field, val)),
    Heap..nextReference!(heap))
};

// Increment the heap allocation nextReference, returning a new heap
function increment(heap: Heap): Heap {
  MkHeap(Heap..data!(heap), Heap..nextReference!(heap) + 1)
};

#end

/-- The Laurel Core prelude as a Laurel Program. -/
def heapConstants : Program :=
  match Laurel.TransM.run none (Laurel.parseProgram laurelPreludeDDM) with
  | .ok program => program
  | .error e => dbg_trace s!"BUG: Laurel heap prelude parse error: {e}"; default

end -- public section

end Strata.Laurel
