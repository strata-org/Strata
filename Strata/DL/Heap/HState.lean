/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Heap.HExpr
import Strata.DL.Heap.HTy
import Strata.DL.Lambda.LState
import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.IntBoolFactory
import Std.Data.HashMap

---------------------------------------------------------------------

namespace Heap

open Lambda (LState)

/-! ## Heap State

Simple object-centric heap implementation.
Each address points to an object with named fields.
Extended with heap variable environment for storing variables with heap-specific types.
-/

-- Object in the heap - maps field indices to heap expressions
abbrev HeapObject := Std.HashMap Nat HExpr

-- The heap - maps addresses to objects
abbrev HeapMemory := Std.HashMap Address HeapObject

-- Heap variable environment - maps variable names to (type, value) pairs
abbrev HeapVarEnv := Std.HashMap String (HMonoTy × HExpr)

-- String-keyed fields for objects
abbrev StringFieldMap := Std.HashMap String HExpr
abbrev StringFields := Std.HashMap Nat StringFieldMap

/--
Heap State extending Lambda state with heap memory and heap variable environment.
-/
structure HState where
  -- Lambda state for variables, scoping, and evaluation (using String as Identifier)
  lambdaState : LState String
  -- Heap memory
  heap : HeapMemory
  -- Next available address
  nextAddr : Address
  -- Heap variable environment (parallel to Lambda's variable environment)
  heapVars : HeapVarEnv
  -- String-keyed fields: address -> (key -> value)
  stringFields : StringFields

instance : Repr HState where
  reprPrec s _ := s!"HState(nextAddr: {s.nextAddr}, heap: <{s.heap.size} objects>, heapVars: <{s.heapVars.size} vars>, stringFields: <{s.stringFields.size} props>)"

namespace HState

-- Helper function to add a variable to Lambda state
private def addToLambdaState (lambdaState : LState String) (name : String) (ty : Option Lambda.LMonoTy) (expr : Lambda.LExpr Lambda.LMonoTy String) : LState String :=
  -- Add to the top scope (most recent scope)
  match lambdaState.state with
  | [] =>
    -- No scopes exist, create a new one
    { lambdaState with state := [[(name, (ty, expr))]] }
  | topScope :: restScopes =>
    -- Add to the top scope
    let newTopScope := topScope.insert name (ty, expr)
    { lambdaState with state := newTopScope :: restScopes }

-- Helper function to lookup a variable in Lambda state
private def lookupInLambdaState (lambdaState : LState String) (name : String) : Option (Lambda.LExpr Lambda.LMonoTy String) :=
  -- Search through the scope stack (most recent first)
  lambdaState.state.findSome? fun scope =>
    match scope.find? name with
    | some (_, expr) => some expr
    | none => none

-- Create empty heap state with basic Lambda factory
def empty : HState :=
  -- Set up Lambda state with IntBool factory for basic operations
  let lambdaState := (LState.init : LState String)
  -- Add IntBool factory for arithmetic and boolean operations
  let lambdaStateWithFactory := match lambdaState.addFactory Lambda.IntBoolFactory with
    | .ok state => state
    | .error _ => lambdaState  -- Fallback to basic state if factory addition fails
  { lambdaState := lambdaStateWithFactory,
    heap := Std.HashMap.emptyWithCapacity,
    nextAddr := 1,  -- Start addresses from 1 (0 can represent null)
    heapVars := Std.HashMap.emptyWithCapacity,
    stringFields := Std.HashMap.emptyWithCapacity }

-- Heap Variable Environment Operations

-- Set a heap variable with its type and value
def setHeapVar (state : HState) (name : String) (ty : HMonoTy) (value : HExpr) : HState :=
  match value with
  | .lambda lambdaExpr =>
    -- Pure Lambda expression - store ONLY in lambdaState (proper dialect separation)
    let lambdaTy := ty.toLambda?
    let newLambdaState := addToLambdaState state.lambdaState name lambdaTy lambdaExpr
    { state with lambdaState := newLambdaState }
  | _ =>
    -- Heap-specific expression (address, deferred op, etc.) - store ONLY in heapVars
    { state with heapVars := state.heapVars.insert name (ty, value) }

-- Get a heap variable (returns type and value)
def getHeapVar (state : HState) (name : String) : Option (HMonoTy × HExpr) :=
  state.heapVars.get? name

-- Get just the value of a heap variable
def getHeapVarValue (state : HState) (name : String) : Option HExpr :=
  match state.getHeapVar name with
  | some (_, value) => some value
  | none => none

-- Get just the type of a heap variable
def getHeapVarType (state : HState) (name : String) : Option HMonoTy :=
  match state.getHeapVar name with
  | some (ty, _) => some ty
  | none => none

-- Check if a heap variable exists
def hasHeapVar (state : HState) (name : String) : Bool :=
  state.heapVars.contains name

-- Unified variable lookup (checks both heap vars and lambda vars)
def getVar (state : HState) (name : String) : Option HExpr :=
  -- First check heapVars for heap-specific expressions (addresses, deferred ops, etc.)
  match state.getHeapVarValue name with
  | some value => some value
  | none =>
    -- Then check lambdaState for pure Lambda expressions
    match lookupInLambdaState state.lambdaState name with
    | some lambdaExpr => some (HExpr.lambda lambdaExpr)
    | none => none

-- Get all heap variable names
def getHeapVarNames (state : HState) : List String :=
  state.heapVars.toList.map (·.1)

-- Allocate a new object in the heap
def alloc (state : HState) (fields : List (Nat × HExpr)) : HState × Address :=
  let addr := state.nextAddr
  let obj := Std.HashMap.ofList fields
  let newHeap := state.heap.insert addr obj
  let newState := { state with heap := newHeap, nextAddr := addr + 1 }
  (newState, addr)

-- Get an object from the heap
def getObject (state : HState) (addr : Address) : Option HeapObject :=
  state.heap.get? addr

-- Get a field value from an object
def getField (state : HState) (addr : Address) (field : Nat) : Option HExpr :=
  match state.getObject addr with
  | some obj => obj.get? field
  | none => none

-- Update a field in an object
def setField (state : HState) (addr : Address) (field : Nat) (value : HExpr) : Option HState :=
  match state.getObject addr with
  | some obj =>
    let newObj := obj.insert field value
    let newHeap := state.heap.insert addr newObj
    some { state with heap := newHeap }
  | none => none

def deleteField (state : HState) (addr : Address) (field : Nat) : Option HState :=
  -- Remove the field from the object's fields
  -- As an example:
  --  before array deletion {'0': 1, '1': 5} (delete arr[1])
  --  after array deletion  {'0': 1} instead of {'0': 1, '1': None}
  match state.getObject addr with
  | some obj =>
    let newObj := obj.erase field
    let newHeap := state.heap.insert addr newObj
    some { state with heap := newHeap }
  | none => none

-- String field operations (for objects with string-keyed fields)
def getStringField (s : HState) (addr : Nat) (key : String) : Option HExpr :=
  match s.stringFields.get? addr with
  | some m => m.get? key
  | none => none

-- Set a string field in an object
def setStringField (s : HState) (addr : Nat) (key : String) (val : HExpr) : Option HState :=
  let existing : StringFieldMap := (s.stringFields.get? addr).getD (Std.HashMap.emptyWithCapacity)
  let updated := existing.insert key val
  some { s with stringFields := s.stringFields.insert addr updated }

-- Check if an address is valid (exists in heap)
def isValidAddr (state : HState) (addr : Address) : Bool :=
  state.heap.contains addr

-- Get all addresses in the heap
def getAllAddrs (state : HState) : List Address :=
  state.heap.toList.map (·.1)

-- Get the logical length of an array (highest index + 1, ignoring gaps)
def getArrayLength (state : HState) (addr : Address) : Nat :=
  match state.getObject addr with
  | some obj =>
    let indices := obj.toList.map (·.1)
    if indices.isEmpty then
      0
    else
      indices.foldl Nat.max 0 + 1
  | none => 0

-- Pretty printing helpers
def heapToString (state : HState) : String :=
  let entries := state.heap.toList
  let entryStrings := entries.map fun (addr, obj) =>
    let fieldCount := obj.size
    s!"  {addr}: {fieldCount} fields"
  s!"Heap:\n{String.intercalate "\n" entryStrings}"

def heapVarsToString (state : HState) : String :=
  let entries := state.heapVars.toList
  let entryStrings := entries.map fun (name, (ty, _)) =>
    s!"  {name}: {repr ty}"
  s!"Heap Variables:\n{String.intercalate "\n" entryStrings}"

def toString (state : HState) : String :=
  s!"{state.heapToString}\n{state.heapVarsToString}"

-- Return all string-keyed fields for an address as an association list
def getAllStringFields (s : HState) (addr : Nat) : List (String × HExpr) :=
  match s.stringFields.get? addr with
  | some m => m.toList
  | none => []

-- Return all fields (numeric and string) as string-keyed pairs
def getAllFieldsAsStringPairs (s : HState) (addr : Nat) : List (String × HExpr) :=
  let numeric : List (String × HExpr) :=
    match s.getObject addr with
    | some obj => obj.toList.map (fun (i, v) => (s!"{i}", v))
    | none => []
  let strk   : List (String × HExpr) := s.getAllStringFields addr
  -- string keys should override numeric if the same string exists
  let merged := Id.run do
    let mut map : Std.HashMap String HExpr := Std.HashMap.emptyWithCapacity
    for (k, v) in numeric do
      map := map.insert k v
    for (k, v) in strk do
      map := map.insert k v
    pure map
  merged.toList

end HState

end Heap
