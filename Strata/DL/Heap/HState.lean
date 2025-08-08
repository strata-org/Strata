import Strata.DL.Heap.HExpr
import Strata.DL.Heap.HTy
import Strata.DL.Lambda.LState
import Strata.DL.Lambda.IntBoolFactory
import Std.Data.HashMap
import Lean

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

instance : Repr HState where
  reprPrec s _ := s!"HState(nextAddr: {s.nextAddr}, heap: <{s.heap.size} objects>, heapVars: <{s.heapVars.size} vars>)"

namespace HState

-- Helper function to add a variable to Lambda state
private def addToLambdaState (lambdaState : LState String) (name : String) (ty : Option Lambda.LMonoTy) (expr : Lambda.LExpr String) : LState String :=
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
private def lookupInLambdaState (lambdaState : LState String) (name : String) : Option (Lambda.LExpr String) :=
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
    heap := Std.HashMap.empty,
    nextAddr := 1,  -- Start addresses from 1 (0 can represent null)
    heapVars := Std.HashMap.empty }

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
  let obj := Std.HashMap.ofList fields -- I think the fields need to be evaluated
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

-- Check if an address is valid (exists in heap)
def isValidAddr (state : HState) (addr : Address) : Bool :=
  state.heap.contains addr

-- Get all addresses in the heap
def getAllAddrs (state : HState) : List Address :=
  state.heap.toList.map (·.1)

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

end HState

end Heap
