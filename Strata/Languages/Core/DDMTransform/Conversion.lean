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

inductive ASTToCSTError  
  | outOfBoundsIndex (index : Nat)
  | invalidMetadata (msg : String)
  | unsupportedConstruct (construct : String)
  deriving Repr, BEq

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
structure GenContext where
  names : List String  -- generated names (most recent first)
  nameCounter : Nat    -- counter for generating fresh names

def GenContext.empty : GenContext :=
  { names := [], nameCounter := 0 }

def GenContext.pushName (ctx : GenContext) (name : String) : GenContext :=
  { ctx with names := name :: ctx.names }

def GenContext.generateFreshName (ctx : GenContext) (base : String := "x") : (String × GenContext) :=
  let name := base ++ toString ctx.nameCounter
  (name, { ctx with nameCounter := ctx.nameCounter + 1 })

def GenContext.lookupName (ctx : GenContext) (index : Nat) : Option String :=
  ctx.names.get? index

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
abbrev ASTToCSTM := StateT GenContext (Except ASTToCSTError)

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
partial def convertExprCSTToAST : CoreCSTDDM.Expression → CSTToASTM CoreASTDDM.Expression
  | .nat_lit n => return .nat_lit n
  | .bool_true => return .bool_true
  | .bool_false => return .bool_false
  | .string_lit s => return .string_lit s
  | .real_lit d => return .real_lit d
  | .var_ref name => do
    let idx ← CSTToASTM.lookupVar name.toString
    return .var_ref idx
  | .not_expr e => do
    let e' ← convertExprCSTToAST e
    return .not_expr e'
  | .and_expr a b => do
    let a' ← convertExprCSTToAST a
    let b' ← convertExprCSTToAST b
    return .and_expr a' b'
  | .or_expr a b => do
    let a' ← convertExprCSTToAST a
    let b' ← convertExprCSTToAST b
    return .or_expr a' b'
  | .implies_expr a b => do
    let a' ← convertExprCSTToAST a
    let b' ← convertExprCSTToAST b
    return .implies_expr a' b'
  | .iff_expr a b => do
    let a' ← convertExprCSTToAST a
    let b' ← convertExprCSTToAST b
    return .iff_expr a' b'
  | .eq_expr a b => do
    let a' ← convertExprCSTToAST a
    let b' ← convertExprCSTToAST b
    return .eq_expr a' b'
  | .ne_expr a b => do
    let a' ← convertExprCSTToAST a
    let b' ← convertExprCSTToAST b
    return .ne_expr a' b'
  | .lt_expr a b => do
    let a' ← convertExprCSTToAST a
    let b' ← convertExprCSTToAST b
    return .lt_expr a' b'
  | .le_expr a b => do
    let a' ← convertExprCSTToAST a
    let b' ← convertExprCSTToAST b
    return .le_expr a' b'
  | .gt_expr a b => do
    let a' ← convertExprCSTToAST a
    let b' ← convertExprCSTToAST b
    return .gt_expr a' b'
  | .ge_expr a b => do
    let a' ← convertExprCSTToAST a
    let b' ← convertExprCSTToAST b
    return .ge_expr a' b'
  | .neg_expr e => do
    let e' ← convertExprCSTToAST e
    return .neg_expr e'
  | .add_expr a b => do
    let a' ← convertExprCSTToAST a
    let b' ← convertExprCSTToAST b
    return .add_expr a' b'
  | .sub_expr a b => do
    let a' ← convertExprCSTToAST a
    let b' ← convertExprCSTToAST b
    return .sub_expr a' b'
  | .mul_expr a b => do
    let a' ← convertExprCSTToAST a
    let b' ← convertExprCSTToAST b
    return .mul_expr a' b'
  | .div_expr a b => do
    let a' ← convertExprCSTToAST a
    let b' ← convertExprCSTToAST b
    return .div_expr a' b'
  | .mod_expr a b => do
    let a' ← convertExprCSTToAST a
    let b' ← convertExprCSTToAST b
    return .mod_expr a' b'
  | .if_then_else c t f => do
    let c' ← convertExprCSTToAST c
    let t' ← convertExprCSTToAST t
    let f' ← convertExprCSTToAST f
    return .if_then_else c' t' f'
  | .call_expr f args => do
    -- Convert arguments (placeholder for now)
    CSTToASTM.error (.unsupportedConstruct "function calls not fully implemented")
  | _ => CSTToASTM.error (.unsupportedConstruct "unsupported expression")

-- Expression conversion AST → CST  
partial def convertExprASTToCST : CoreASTDDM.Expression → ASTToCSTM CoreCSTDDM.Expression
  | .nat_lit n => return .nat_lit n
  | .bool_true => return .bool_true
  | .bool_false => return .bool_false
  | .string_lit s => return .string_lit s
  | .real_lit d => return .real_lit d
  | .var_ref idx => do
    let name ← ASTToCSTM.lookupName idx.toNat
    return .var_ref ⟨name⟩
  | .not_expr e => do
    let e' ← convertExprASTToCST e
    return .not_expr e'
  | .and_expr a b => do
    let a' ← convertExprASTToCST a
    let b' ← convertExprASTToCST b
    return .and_expr a' b'
  | .or_expr a b => do
    let a' ← convertExprASTToCST a
    let b' ← convertExprASTToCST b
    return .or_expr a' b'
  | .implies_expr a b => do
    let a' ← convertExprASTToCST a
    let b' ← convertExprASTToCST b
    return .implies_expr a' b'
  | .iff_expr a b => do
    let a' ← convertExprASTToCST a
    let b' ← convertExprASTToCST b
    return .iff_expr a' b'
  | .eq_expr a b => do
    let a' ← convertExprASTToCST a
    let b' ← convertExprASTToCST b
    return .eq_expr a' b'
  | .ne_expr a b => do
    let a' ← convertExprASTToCST a
    let b' ← convertExprASTToCST b
    return .ne_expr a' b'
  | .lt_expr a b => do
    let a' ← convertExprASTToCST a
    let b' ← convertExprASTToCST b
    return .lt_expr a' b'
  | .le_expr a b => do
    let a' ← convertExprASTToCST a
    let b' ← convertExprASTToCST b
    return .le_expr a' b'
  | .gt_expr a b => do
    let a' ← convertExprASTToCST a
    let b' ← convertExprASTToCST b
    return .gt_expr a' b'
  | .ge_expr a b => do
    let a' ← convertExprASTToCST a
    let b' ← convertExprASTToCST b
    return .ge_expr a' b'
  | .neg_expr e => do
    let e' ← convertExprASTToCST e
    return .neg_expr e'
  | .add_expr a b => do
    let a' ← convertExprASTToCST a
    let b' ← convertExprASTToCST b
    return .add_expr a' b'
  | .sub_expr a b => do
    let a' ← convertExprASTToCST a
    let b' ← convertExprASTToCST b
    return .sub_expr a' b'
  | .mul_expr a b => do
    let a' ← convertExprASTToCST a
    let b' ← convertExprASTToCST b
    return .mul_expr a' b'
  | .div_expr a b => do
    let a' ← convertExprASTToCST a
    let b' ← convertExprASTToCST b
    return .div_expr a' b'
  | .mod_expr a b => do
    let a' ← convertExprASTToCST a
    let b' ← convertExprASTToCST b
    return .mod_expr a' b'
  | .if_then_else c t f => do
    let c' ← convertExprASTToCST c
    let t' ← convertExprASTToCST t
    let f' ← convertExprASTToCST f
    return .if_then_else c' t' f'
  | .call_expr f args => do
    -- Convert arguments (placeholder for now)
    ASTToCSTM.error (.unsupportedConstruct "function calls not fully implemented")
  | _ => ASTToCSTM.error (.unsupportedConstruct "unsupported expression")

-- Statement conversion CST → AST
partial def convertStmtCSTToAST : CoreCSTDDM.Statement → CSTToASTM CoreASTDDM.Statement
  | .var_decl v tp => do
    CSTToASTM.pushBinding v.toString
    return .var_decl tp
  | .var_decl_init v tp init => do
    let init' ← convertExprCSTToAST init
    CSTToASTM.pushBinding v.toString
    return .var_decl_init tp init'
  | .val_decl v tp val => do
    let val' ← convertExprCSTToAST val
    CSTToASTM.pushBinding v.toString
    return .val_decl tp val'
  | .assign_stmt v e => do
    let idx ← CSTToASTM.lookupVar v.toString
    let e' ← convertExprCSTToAST e
    return .assign_stmt idx e'
  | .havoc_stmt v => do
    let idx ← CSTToASTM.lookupVar v.toString
    return .havoc_stmt idx
  | .assert_stmt e => do
    let e' ← convertExprCSTToAST e
    return .assert_stmt e'
  | .assume_stmt e => do
    let e' ← convertExprCSTToAST e
    return .assume_stmt e'
  | .check_stmt e => do
    let e' ← convertExprCSTToAST e
    return .check_stmt e'
  | .reach_stmt e => do
    let e' ← convertExprCSTToAST e
    return .reach_stmt e'
  | .cover_stmt e => do
    let e' ← convertExprCSTToAST e
    return .cover_stmt e'
  | .exit_stmt => return .exit_stmt
  | .return_stmt (some e) => do
    let e' ← convertExprCSTToAST e
    return .return_stmt (some e')
  | .return_stmt none => return .return_stmt none
  | _ => CSTToASTM.error (.unsupportedConstruct "unsupported statement")

-- Statement conversion AST → CST
partial def convertStmtASTToCST : CoreASTDDM.Statement → ASTToCSTM CoreCSTDDM.Statement  
  | .var_decl tp => do
    let name ← ASTToCSTM.generateFreshName "x"
    ASTToCSTM.pushName name
    return .var_decl ⟨name⟩ tp
  | .var_decl_init tp init => do
    let init' ← convertExprASTToCST init
    let name ← ASTToCSTM.generateFreshName "x"
    ASTToCSTM.pushName name
    return .var_decl_init ⟨name⟩ tp init'
  | .val_decl tp val => do
    let val' ← convertExprASTToCST val
    let name ← ASTToCSTM.generateFreshName "x"
    ASTToCSTM.pushName name
    return .val_decl ⟨name⟩ tp val'
  | .assign_stmt idx e => do
    let name ← ASTToCSTM.lookupName idx.toNat
    let e' ← convertExprASTToCST e
    return .assign_stmt ⟨name⟩ e'
  | .havoc_stmt idx => do
    let name ← ASTToCSTM.lookupName idx.toNat
    return .havoc_stmt ⟨name⟩
  | .assert_stmt e => do
    let e' ← convertExprASTToCST e
    return .assert_stmt e'
  | .assume_stmt e => do
    let e' ← convertExprASTToCST e
    return .assume_stmt e'
  | .check_stmt e => do
    let e' ← convertExprASTToCST e
    return .check_stmt e'
  | .reach_stmt e => do
    let e' ← convertExprASTToCST e
    return .reach_stmt e'
  | .cover_stmt e => do
    let e' ← convertExprASTToCST e
    return .cover_stmt e'
  | .exit_stmt => return .exit_stmt
  | .return_stmt (some e) => do
    let e' ← convertExprASTToCST e
    return .return_stmt (some e')
  | .return_stmt none => return .return_stmt none
  | _ => ASTToCSTM.error (.unsupportedConstruct "unsupported statement")

-- Function declaration conversion CST → AST
def convertFuncDeclCSTToAST : CoreCSTDDM.FunctionDecl → CSTToASTM CoreASTDDM.FunctionDecl
  | _ => CSTToASTM.error (.unsupportedConstruct "function declaration conversion not implemented")

-- Function declaration conversion AST → CST
def convertFuncDeclASTToCST : CoreASTDDM.FunctionDecl → ASTToCSTM CoreCSTDDM.FunctionDecl
  | _ => ASTToCSTM.error (.unsupportedConstruct "function declaration conversion not implemented")

-- Datatype declaration conversion CST → AST
def convertDatatypeDeclCSTToAST : CoreCSTDDM.DatatypeDecl → CSTToASTM CoreASTDDM.DatatypeDecl
  | _ => CSTToASTM.error (.unsupportedConstruct "datatype declaration conversion not implemented")

-- Datatype declaration conversion AST → CST
def convertDatatypeDeclASTToCST : CoreASTDDM.DatatypeDecl → ASTToCSTM CoreCSTDDM.DatatypeDecl
  | _ => ASTToCSTM.error (.unsupportedConstruct "datatype declaration conversion not implemented")

-- Type declaration conversion CST → AST
def convertTypeDeclCSTToAST : CoreCSTDDM.TypeDecl → CSTToASTM CoreASTDDM.TypeDecl
  | _ => CSTToASTM.error (.unsupportedConstruct "type declaration conversion not implemented")

-- Type declaration conversion AST → CST
def convertTypeDeclASTToCST : CoreASTDDM.TypeDecl → ASTToCSTM CoreCSTDDM.TypeDecl
  | _ => ASTToCSTM.error (.unsupportedConstruct "type declaration conversion not implemented")

-- Main conversion functions

def cstToAST (cst : CoreCSTDDM.Statement) : Except CSTToASTError CoreASTDDM.Statement :=
  match convertStmtCSTToAST cst |>.run NameContext.empty with
  | .ok (ast, _) => .ok ast
  | .error err => .error err

def astToCST (ast : CoreASTDDM.Statement) : Except ASTToCSTError CoreCSTDDM.Statement :=
  match convertStmtASTToCST ast |>.run GenContext.empty with
  | .ok (cst, _) => .ok cst
  | .error err => .error err

-- Round-trip conversion test
def roundTripCST (cst : CoreCSTDDM.Statement) : Except String CoreCSTDDM.Statement := do
  let ast ← cstToAST cst |>.mapError toString
  let cst' ← astToCST ast |>.mapError toString
  return cst'

---------------------------------------------------------------------

end Strata
