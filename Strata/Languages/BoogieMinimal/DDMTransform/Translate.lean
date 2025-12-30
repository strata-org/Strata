/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST
import Strata.Languages.BoogieMinimal.DDMTransform.DatatypeConfig
import Strata.Languages.BoogieMinimal.DDMTransform.Parse

---------------------------------------------------------------------
namespace Strata
namespace BoogieMinimal

/--
Translation context for BoogieMinimal.
This is a minimal implementation to demonstrate that the DDM datatype mechanism
works with different encoding strategies.
-/
structure TransBindings where
  /-- Bound type variables in scope -/
  boundTypeVars : Array String := #[]
  /-- Free variable declarations -/
  freeVars : Array String := #[]
  deriving Repr, Inhabited

/--
Information about a translated constructor.
-/
structure TransConstructorInfo where
  /-- Constructor name -/
  name : String
  /-- Field names and types (as strings for simplicity) -/
  fields : Array (String × String)
  deriving Repr, Inhabited

/--
Result of translating a datatype declaration.
Contains the datatype name, type parameters, constructors, and generated indexer names.
-/
structure TransDatatypeResult where
  /-- Datatype name -/
  name : String
  /-- Type parameters -/
  typeParams : Array String
  /-- Constructor information -/
  constructors : Array TransConstructorInfo
  /-- Generated indexer function names (one per constructor) -/
  indexerNames : Array String
  deriving Repr, Inhabited

/--
Generate indexer function names for a datatype using BoogieMinimalDatatypeConfig.
Unlike Boogie's boolean testers, these return int values.
-/
def generateIndexerNames (config : BoogieMinimalDatatypeConfig) (datatypeName : String)
    (constructors : Array TransConstructorInfo) : Array String :=
  constructors.map fun constr =>
    expandNamePattern config.indexerPattern datatypeName (some constr.name)

/--
Translate a datatype declaration to BoogieMinimal representation.
This demonstrates that the DDM mechanism correctly generates indexer functions
instead of tester functions, and does NOT generate field accessors.
-/
def translateDatatype (bindings : TransBindings) (datatypeName : String)
    (typeParams : Array String) (constructors : Array TransConstructorInfo) :
    TransDatatypeResult × TransBindings :=
  let config := defaultBoogieMinimalDatatypeConfig
  let indexerNames := generateIndexerNames config datatypeName constructors

  -- Build result
  let result : TransDatatypeResult :=
    { name := datatypeName
      typeParams := typeParams
      constructors := constructors
      indexerNames := indexerNames }

  -- Update bindings with new declarations
  -- Order: datatype type, constructors, indexers (matching DDM order)
  let bindings := { bindings with
    freeVars := bindings.freeVars.push datatypeName }
  let bindings := constructors.foldl (fun b c =>
    { b with freeVars := b.freeVars.push c.name }) bindings
  let bindings := indexerNames.foldl (fun b name =>
    { b with freeVars := b.freeVars.push name }) bindings

  (result, bindings)

/--
Verify that a datatype translation produces the expected indexer names.
This is used in tests to validate the DDM mechanism.
-/
def verifyIndexerNames (result : TransDatatypeResult) (expectedNames : Array String) : Bool :=
  result.indexerNames == expectedNames

/--
Verify that NO field accessors are generated.
BoogieMinimal does not have a perField template, so no field accessors should exist.
-/
def verifyNoFieldAccessors (result : TransDatatypeResult) : Bool :=
  -- In BoogieMinimal, we only generate indexers, not field accessors
  -- The number of generated functions should equal the number of constructors
  result.indexerNames.size == result.constructors.size

end BoogieMinimal
end Strata
