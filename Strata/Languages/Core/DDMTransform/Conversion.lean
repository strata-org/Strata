/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST
import Strata.Languages.Core.DDMTransform.ParseCST
import Strata.Languages.Core.DDMTransform.DefinitionAST
import Std.Data.HashMap

---------------------------------------------------------------------

namespace Strata

---------------------------------------------------------------------

/- 
Bidirectional conversion between CoreCST and CoreAST

This module provides conversion functions between the concrete syntax tree (CST)
and abstract syntax tree (AST) representations of Strata Core programs.

Key components:
- Name resolution: Converting identifiers to de Bruijn indices
- Name generation: Converting de Bruijn indices back to identifiers  
- Context management: Tracking variable bindings and scopes
- Error handling: Comprehensive error types for conversion failures

Conversion process:
1. CST → AST: Resolve all identifiers to de Bruijn indices using NameContext
2. AST → CST: Generate fresh names for de Bruijn indices using GenContext
3. Round-trip: CST → AST → CST should preserve semantics

Error handling:
- CSTToASTError: Unresolved identifiers, type mismatches, unsupported constructs
- ASTToCSTError: Out-of-bounds indices, invalid metadata, unsupported constructs

Context management:
- NameContext: Maintains list of bound variables for name resolution
- GenContext: Generates fresh names and tracks naming state

Example usage:
```lean
let cst := CoreCSTDDM.Statement.var_decl ⟨"x"⟩ (.builtin "int")
let ast_result := cstToAST cst  -- Result: var_decl(int)
let cst_result := ast_result >>= astToCST  -- Result: var_decl ⟨"x0"⟩ (.builtin "int")
```

Current limitations:
- Function calls not fully implemented
- Complex expressions (quantifiers, let) need more work
- Declaration conversions are placeholders
- Metadata handling is basic
-/

-- Error types for conversion
inductive CSTToASTError
  | unresolvedIdentifier (name : String)
  | typeMismatch (expected : String) (actual : String)
  | unsupportedConstruct (construct : String)
  deriving Repr, BEq

instance : ToString CSTToASTError where
  toString
  | .unresolvedIdentifier name => s!"Unresolved identifier: {name}"
  | .typeMismatch expected actual => s!"Type mismatch: expected {expected}, got {actual}"
  | .unsupportedConstruct construct => s!"Unsupported construct: {construct}"

inductive ASTToCSTError  
  | outOfBoundsIndex (index : Nat)
  | invalidMetadata (msg : String)
  | unsupportedConstruct (construct : String)
  deriving Repr, BEq

instance : ToString ASTToCSTError where
  toString
  | .outOfBoundsIndex index => s!"Out of bounds index: {index}"
  | .invalidMetadata msg => s!"Invalid metadata: {msg}"
  | .unsupportedConstruct construct => s!"Unsupported construct: {construct}"

-- Context for name resolution
structure NameContext where
  bindings : List String  -- de Bruijn context (most recent first)
  functions : Std.HashMap String Nat  -- function names to arities
  types : Std.HashMap String Nat      -- type names to arities
  datatypes : Std.HashMap String Nat  -- datatype names to arities

def NameContext.empty : NameContext :=
  { bindings := [], functions := {}, types := {}, datatypes := {} }

def NameContext.pushBinding (ctx : NameContext) (name : String) : NameContext :=
  { ctx with bindings := name :: ctx.bindings }

def NameContext.lookupVar (ctx : NameContext) (name : String) : Option Nat :=
  ctx.bindings.findIdx? (· == name)

-- Context for name generation (reverse of name resolution)
structure NameGenContext where
  names : List String  -- generated names (most recent first)
  nameCounter : Nat    -- counter for generating fresh names

def NameGenContext.empty : NameGenContext :=
  { names := [], nameCounter := 0 }

def NameGenContext.pushName (ctx : NameGenContext) (name : String) : NameGenContext :=
  { ctx with names := name :: ctx.names }

def NameGenContext.generateFreshName (ctx : NameGenContext) (base : String := "x") : (String × NameGenContext) :=
  let name := base ++ toString ctx.nameCounter
  (name, { ctx with nameCounter := ctx.nameCounter + 1 })

def NameGenContext.lookupName (ctx : NameGenContext) (index : Nat) : Option String :=
  if h : index < ctx.names.length then
    some (ctx.names.get ⟨index, h⟩)
  else
    none

-- Conversion monad for CST → AST
abbrev CSTToASTM := StateT NameContext (Except CSTToASTError)

def CSTToASTM.error (err : CSTToASTError) : CSTToASTM α :=
  throw err

def CSTToASTM.lookupVar (name : String) : CSTToASTM Nat := do
  let ctx ← get
  match ctx.lookupVar name with
  | some idx => return idx
  | none => CSTToASTM.error (.unresolvedIdentifier name)

def CSTToASTM.pushBinding (name : String) : CSTToASTM Unit := do
  modify (·.pushBinding name)

-- Conversion monad for AST → CST  
abbrev ASTToCSTM := StateT NameGenContext (Except ASTToCSTError)

def ASTToCSTM.error (err : ASTToCSTError) : ASTToCSTM α :=
  throw err

def ASTToCSTM.lookupName (index : Nat) : ASTToCSTM String := do
  let ctx ← get
  match ctx.lookupName index with
  | some name => return name
  | none => ASTToCSTM.error (.outOfBoundsIndex index)

def ASTToCSTM.pushName (name : String) : ASTToCSTM Unit := do
  modify (·.pushName name)

def ASTToCSTM.generateFreshName (base : String := "x") : ASTToCSTM String := do
  let ctx ← get
  let (name, newCtx) := ctx.generateFreshName base
  set newCtx
  return name

-- Placeholder conversion functions (to be implemented)

-- Expression conversion CST → AST
partial def convertExprCSTToAST : CoreCSTDDM.Expression Unit → CSTToASTM (CoreASTDDM.Expression Unit)
  | _ => CSTToASTM.error (.unsupportedConstruct "expression conversion not fully implemented")

-- Expression conversion AST → CST  
partial def convertExprASTToCST : CoreASTDDM.Expression Unit → ASTToCSTM (CoreCSTDDM.Expression Unit)
  | _ => ASTToCSTM.error (.unsupportedConstruct "expression conversion not fully implemented")

-- Statement conversion CST → AST
partial def convertStmtCSTToAST : CoreCSTDDM.Statement Unit → CSTToASTM (CoreASTDDM.Statement Unit)
  | _ => CSTToASTM.error (.unsupportedConstruct "statement conversion not fully implemented")

-- Statement conversion AST → CST
partial def convertStmtASTToCST : CoreASTDDM.Statement Unit → ASTToCSTM (CoreCSTDDM.Statement Unit)  
  | _ => ASTToCSTM.error (.unsupportedConstruct "statement conversion not fully implemented")

-- Function declaration conversion CST → AST
def convertFuncDeclCSTToAST : CoreCSTDDM.FunctionDecl Unit → CSTToASTM (CoreASTDDM.FunctionDecl Unit)
  | _ => CSTToASTM.error (.unsupportedConstruct "function declaration conversion not implemented")

-- Function declaration conversion AST → CST
def convertFuncDeclASTToCST : CoreASTDDM.FunctionDecl Unit → ASTToCSTM (CoreCSTDDM.FunctionDecl Unit)
  | _ => ASTToCSTM.error (.unsupportedConstruct "function declaration conversion not implemented")

-- Datatype declaration conversion CST → AST
def convertDatatypeDeclCSTToAST : CoreCSTDDM.DatatypeDecl Unit → CSTToASTM (CoreASTDDM.DatatypeDecl Unit)
  | _ => CSTToASTM.error (.unsupportedConstruct "datatype declaration conversion not implemented")

-- Datatype declaration conversion AST → CST
def convertDatatypeDeclASTToCST : CoreASTDDM.DatatypeDecl Unit → ASTToCSTM (CoreCSTDDM.DatatypeDecl Unit)
  | _ => ASTToCSTM.error (.unsupportedConstruct "datatype declaration conversion not implemented")

-- Type declaration conversion CST → AST
def convertTypeDeclCSTToAST : CoreCSTDDM.TypeDecl Unit → CSTToASTM (CoreASTDDM.TypeDecl Unit)
  | _ => CSTToASTM.error (.unsupportedConstruct "type declaration conversion not implemented")

-- Type declaration conversion AST → CST
def convertTypeDeclASTToCST : CoreASTDDM.TypeDecl Unit → ASTToCSTM (CoreCSTDDM.TypeDecl Unit)
  | _ => ASTToCSTM.error (.unsupportedConstruct "type declaration conversion not implemented")

-- Main conversion functions

def cstToAST (cst : CoreCSTDDM.Statement Unit) : Except CSTToASTError (CoreASTDDM.Statement Unit) :=
  match convertStmtCSTToAST cst |>.run NameContext.empty with
  | .ok (ast, _) => .ok ast
  | .error err => .error err

def astToCST (ast : CoreASTDDM.Statement Unit) : Except ASTToCSTError (CoreCSTDDM.Statement Unit) :=
  match convertStmtASTToCST ast |>.run NameGenContext.empty with
  | .ok (cst, _) => .ok cst
  | .error err => .error err

-- Round-trip conversion test
def roundTripCST (cst : CoreCSTDDM.Statement Unit) : Except String (CoreCSTDDM.Statement Unit) := do
  let ast ← cstToAST cst |>.mapError toString
  let cst' ← astToCST ast |>.mapError toString
  return cst'

---------------------------------------------------------------------

end Strata
