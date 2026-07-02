/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.AST
public import Strata.Languages.Laurel.LaurelAST
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.Grammar.LaurelGrammar
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

// Heap: contains the data map and a nextReference for allocation. The map is
// keyed by an object's reference (int), not the whole Composite: `new` hands out
// fresh references, so the reference alone identifies an object. Keying on the
// full Composite would let the same object be seen under two type tags (e.g. a
// base-typed vs subclass-typed view, or a dynamic-reference unbox), splitting
// its state across distinct keys.
datatype Heap {
  MkHeap(data: Map int Map Field Box, nextReference: int)
}

// Read a field from the heap: readField(heap, obj, field) = Heap..data!(heap)[ref!(obj)][field]
function readField(heap: Heap, obj: Composite, field: Field): Box {
  select(select(Heap..data!(heap), Composite..ref!(obj)), field)
};

// Update a field in the heap
function updateField(heap: Heap, obj: Composite, field: Field, val: Box): Heap {
  MkHeap(
    update(Heap..data!(heap), Composite..ref!(obj),
      update(select(Heap..data!(heap), Composite..ref!(obj)), field, val)),
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

-- Names of the dynamic-reference bridge functions, shared between the bridge
-- builder (`dynamicRefBridge`) and its callers in the heap parameterization pass.
def dynToCompositeName : Identifier := "dynToComposite"
def readFieldDynName : Identifier := "readFieldDyn"
def updateFieldDynName : Identifier := "updateFieldDyn"

/-- The `dynToComposite`/`readFieldDyn`/`updateFieldDyn` bridge for a program's
    dynamic-reference type. Built programmatically since the type name varies. -/
def dynamicRefBridge (dynTypeName : Identifier) (spec : DynamicRefSpec) : List Procedure :=
  let ty (name : String) : HighTypeMd := ⟨.UserDefined name, none⟩
  let dynTy : HighTypeMd := ⟨.UserDefined dynTypeName, none⟩
  let mkMd (e : StmtExpr) : StmtExprMd := ⟨e, none⟩
  let call (name : Identifier) (args : List StmtExprMd) : StmtExprMd := mkMd (.StaticCall name args)
  let localRef (name : Identifier) : StmtExprMd := mkMd (.Var (.Local name))
  let mkFn (name : Identifier) (inputs : List Parameter) (out : HighTypeMd) (body : StmtExprMd) : Procedure :=
    { name, inputs
      outputs := [{ name := "result", type := out }]
      body := .Transparent (mkMd (.Return body))
      isFunctional := true, decreases := none, preconditions := [] }
  let dynParam : Parameter := { name := "a", type := dynTy }
  let tagParam : Parameter := { name := "tag", type := ty "TypeTag" }
  let heapParam : Parameter := { name := "heap", type := ty "Heap" }
  let objParam : Parameter := { name := "obj", type := dynTy }
  let fieldParam : Parameter := { name := "field", type := ty "Field" }
  let valParam : Parameter := { name := "val", type := ty "Box" }
  let toComposite (obj : Identifier) (tag : Identifier) : StmtExprMd :=
    call dynToCompositeName [localRef obj, localRef tag]
  [ mkFn dynToCompositeName [dynParam, tagParam] (ty "Composite")
      (call "MkComposite" [call spec.refAccessor [localRef "a"], localRef "tag"])
  , mkFn readFieldDynName [heapParam, objParam, tagParam, fieldParam] (ty "Box")
      (call "readField" [localRef "heap", toComposite "obj" "tag", localRef "field"])
  , mkFn updateFieldDynName [heapParam, objParam, tagParam, fieldParam, valParam] (ty "Heap")
      (call "updateField" [localRef "heap", toComposite "obj" "tag", localRef "field", localRef "val"]) ]

end -- public section

end Strata.Laurel
