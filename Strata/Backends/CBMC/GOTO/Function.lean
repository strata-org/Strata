/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.CProver.GOTO.Program

/-!
# GOTO Functions

This module defines GOTO functions and the overall GOTO model structure,
corresponding to CBMC's goto_functiont and goto_model.
-/

namespace CProverGOTO

/-- Parameter information for a function -/
structure Parameter where
  name : Identifier
  type : Ty
deriving Repr, BEq

/-- A GOTO function contains a body (GOTO program) and metadata -/
structure GotoFunction where
  /-- Function name -/
  name : Identifier
  /-- Function parameters -/
  parameters : List Parameter
  /-- Return type -/
  return_type : Ty
  /-- Function body as a GOTO program -/
  body : GotoProgram
  /-- Local variables -/
  locals : List Symbol
  /-- Whether this function has a body (not just a declaration) -/
  has_body : Bool
deriving Repr



/-- GOTO model containing all functions and global symbols -/
structure GotoModel where
  /-- All functions in the program -/
  functions : List (Identifier × GotoFunction)
  /-- Global symbol table -/
  symbol_table : SymbolTable
  /-- Entry point function name -/
  entry_point : Option Identifier
deriving Repr

-- Helper functions for GotoFunction

/-- Create an empty GOTO function -/
def GotoFunction.empty (name : Identifier) (ret_type : Ty := Ty.Integer) : GotoFunction :=
  { name := name,
    parameters := [],
    return_type := ret_type,
    body := GotoProgram.empty,
    locals := [],
    has_body := false }

/-- Add a parameter to a function -/
def GotoFunction.add_parameter (func : GotoFunction) (param : Parameter) : GotoFunction :=
  { func with parameters := func.parameters ++ [param] }

/-- Add a local variable to a function -/
def GotoFunction.add_local (func : GotoFunction) (symbol : Symbol) : GotoFunction :=
  { func with locals := func.locals ++ [symbol] }

/-- Set the function body -/
def GotoFunction.set_body (func : GotoFunction) (body : GotoProgram) : GotoFunction :=
  { func with body := body, has_body := true }

/-- Get all variables (parameters + locals) in a function -/
def GotoFunction.all_variables (func : GotoFunction) : List Symbol :=
  let param_symbols := func.parameters.map (fun p =>
    Symbol.mk_parameter p.name p.type)
  param_symbols ++ func.locals

-- Helper functions for GotoModel

/-- Create an empty GOTO model -/
def GotoModel.empty : GotoModel :=
  { functions := [],
    symbol_table := {},
    entry_point := none }

/-- Add a function to the model -/
def GotoModel.add_function (model : GotoModel) (func : GotoFunction) : GotoModel :=
  { model with functions := model.functions ++ [(func.name, func)] }

/-- Add a global symbol to the model -/
def GotoModel.add_symbol (model : GotoModel) (symbol : Symbol) : GotoModel :=
  { model with symbol_table := model.symbol_table.add symbol }

/-- Set the entry point -/
def GotoModel.set_entry_point (model : GotoModel) (entry : Identifier) : GotoModel :=
  { model with entry_point := some entry }

/-- Look up a function by name -/
def GotoModel.get_function (model : GotoModel) (name : Identifier) : Option GotoFunction :=
  model.functions.lookup name

/-- Look up a symbol by name -/
def GotoModel.get_symbol (model : GotoModel) (name : Identifier) : Option Symbol :=
  model.symbol_table.lookup name

/-- Get all function names -/
def GotoModel.function_names (model : GotoModel) : List Identifier :=
  model.functions.map (·.1)

/-- Check if model has an entry point -/
def GotoModel.has_entry_point (model : GotoModel) : Bool :=
  model.entry_point.isSome

-- Validation functions

/-- Check if a function is well-formed -/
def GotoFunction.is_valid (func : GotoFunction) : Bool :=
  -- Basic checks: if has_body is true, body should not be empty
  if func.has_body then !func.body.is_empty else true

/-- Check if a model is well-formed -/
def GotoModel.is_valid (model : GotoModel) : Bool :=
  -- All functions should be valid
  model.functions.all (fun (_, func) => func.is_valid) &&
  -- Entry point should exist if specified
  match model.entry_point with
  | none => true
  | some entry => model.get_function entry |>.isSome

-- Formatting instances

instance : ToString Parameter where
  toString param := s!"{param.name} : {Std.format param.type}"

instance : ToString GotoFunction where
  toString func :=
    let params_str := String.intercalate ", " (func.parameters.map toString)
    let body_str := if func.has_body then s!" ({func.body.size} instructions)" else " (declaration only)"
    s!"function {func.name}({params_str}) : {Std.format func.return_type}{body_str}"

instance : ToString GotoModel where
  toString model :=
    let funcs_str := String.intercalate "\n" (model.functions.map (fun (_, f) => toString f))
    let entry_str := match model.entry_point with
      | none => "No entry point"
      | some entry => s!"Entry point: {entry}"
    s!"GOTO Model:\n{entry_str}\nFunctions:\n{funcs_str}"
