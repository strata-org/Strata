/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Generic translation context that can work with any function type
-- This replaces the dialect-specific TranslationContext definitions

namespace Generic

-- Generic Strata function that can work with any statement and type system
structure StrataFunction (StatementType : Type) (TypeType : Type) where
  name : String
  params : List String                              -- Parameter names
  body : List StatementType                        -- Function body as Strata statements
  returnType : Option TypeType := none             -- Optional return type

-- ToString instance for generic StrataFunction
instance {S T : Type} : ToString (StrataFunction S T) where
  toString f := s!"def {f.name}({String.intercalate ", " f.params}): <{f.body.length} statements>"

-- Generic translation context parameterized by statement and type systems
structure TranslationContext (StatementType : Type) (TypeType : Type) where
  functions : List (StrataFunction StatementType TypeType) := []

-- Helper functions for working with generic translation contexts
def TranslationContext.getFunctionNames {S T : Type} (ctx : TranslationContext S T) : List String :=
  ctx.functions.map (fun f => f.name)

def TranslationContext.findFunction {S T : Type} (ctx : TranslationContext S T) (name : String) : Option (StrataFunction S T) :=
  ctx.functions.find? (fun f => f.name == name)

def TranslationContext.getFunctionParams {S T : Type} (ctx : TranslationContext S T) (name : String) : Option (List String) :=
  match ctx.findFunction name with
  | some f => some f.params
  | none => none

def TranslationContext.getFunctionBody {S T : Type} (ctx : TranslationContext S T) (name : String) : Option (List S) :=
  match ctx.findFunction name with
  | some f => some f.body
  | none => none

def TranslationContext.getFunctionReturnType {S T : Type} (ctx : TranslationContext S T) (name : String) : Option (Option T) :=
  match ctx.findFunction name with
  | some f => some f.returnType
  | none => none

-- Convenience functions for common queries
def TranslationContext.hasFunctions {S T : Type} (ctx : TranslationContext S T) : Bool :=
  !ctx.functions.isEmpty

def TranslationContext.functionCount {S T : Type} (ctx : TranslationContext S T) : Nat :=
  ctx.functions.length

-- Add function to context
def TranslationContext.addFunction {S T : Type} (ctx : TranslationContext S T) (func : StrataFunction S T) : TranslationContext S T :=
  { ctx with functions := func :: ctx.functions }

-- Empty context
def TranslationContext.empty {S T : Type} : TranslationContext S T := 
  { functions := [] }

end Generic
