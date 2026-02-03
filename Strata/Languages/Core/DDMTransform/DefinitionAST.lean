/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.DDM.Util.Format

---------------------------------------------------------------------

namespace Strata

---------------------------------------------------------------------
---------------------------------------------------------------------

/- 
DDM support for abstract syntax with de Bruijn indices for Strata Core

This module defines an abstract syntax tree (AST) dialect for Strata Core
that uses canonical forms and de Bruijn indices for variable binding.
The AST is designed to be the target of conversion from concrete syntax
and the source for conversion to Core.Statement.

Key features:
- De Bruijn indices for all variable references
- Canonical forms (no syntactic sugar)
- Explicit binding structure for quantifiers and let expressions
- Metadata transformation support

Design principles:
- Variables are represented as de Bruijn indices (#0, #1, etc.)
- All operators use prefix notation for consistency
- No syntactic sugar (e.g., no infix operators in AST)
- Explicit type information where needed
- Metadata can be transformed via mapMetadata functions

Example AST representation:
```
var_decl_init(int, nat_lit(42))     // var x : int := 42
assign(#0, add(var_ref(#0), nat_lit(1)))  // x := x + 1
assert(gt(var_ref(#0), nat_lit(0)))       // assert x > 0
```

The AST is designed to be easily convertible to/from concrete syntax
while maintaining precise binding information and canonical forms
suitable for analysis and transformation.
-/

#dialect
dialect CoreAST;

// Basic types
type bool;
type int;
type string;
type real;

// Expression category with canonical forms
category Expression;

// Literals
op nat_lit (n : Num) : Expression => n;
op bool_true : Expression => "true";
op bool_false : Expression => "false";
op string_lit (s : Str) : Expression => s;
op real_lit (d : Decimal) : Expression => d;

// Variables using de Bruijn indices
op var_ref (index : Num) : Expression => "#" index;

// Logical operators (canonical forms)
op not_expr (e : Expression) : Expression => "not" "(" e ")";
op and_expr (a : Expression, b : Expression) : Expression => "and" "(" a "," b ")";
op or_expr (a : Expression, b : Expression) : Expression => "or" "(" a "," b ")";
op implies_expr (a : Expression, b : Expression) : Expression => "implies" "(" a "," b ")";
op iff_expr (a : Expression, b : Expression) : Expression => "iff" "(" a "," b ")";

// Comparison operators
op eq_expr (a : Expression, b : Expression) : Expression => "eq" "(" a "," b ")";
op ne_expr (a : Expression, b : Expression) : Expression => "ne" "(" a "," b ")";
op lt_expr (a : Expression, b : Expression) : Expression => "lt" "(" a "," b ")";
op le_expr (a : Expression, b : Expression) : Expression => "le" "(" a "," b ")";
op gt_expr (a : Expression, b : Expression) : Expression => "gt" "(" a "," b ")";
op ge_expr (a : Expression, b : Expression) : Expression => "ge" "(" a "," b ")";

// Arithmetic operators
op neg_expr (e : Expression) : Expression => "neg" "(" e ")";
op add_expr (a : Expression, b : Expression) : Expression => "add" "(" a "," b ")";
op sub_expr (a : Expression, b : Expression) : Expression => "sub" "(" a "," b ")";
op mul_expr (a : Expression, b : Expression) : Expression => "mul" "(" a "," b ")";
op div_expr (a : Expression, b : Expression) : Expression => "div" "(" a "," b ")";
op mod_expr (a : Expression, b : Expression) : Expression => "mod" "(" a "," b ")";

// Conditionals
op if_then_else (c : Expression, t : Expression, f : Expression) : Expression => 
  "ite" "(" c "," t "," f ")";

// Let expressions with de Bruijn binding
op let_expr (tp : Type, bound : Expression, body : Expression) : Expression =>
  "let" "(" tp "," bound "," body ")";

// Function calls
op call_expr (f : Ident, args : CommaSepBy Expression) : Expression =>
  "call" "(" f "," args ")";

// Quantifiers with de Bruijn binding
category Pattern;
category PatternList;
op pattern_mk (exprs : CommaSepBy Expression) : Pattern => "{" exprs "}";
op pattern_atom (p : Pattern) : PatternList => p;
op pattern_push (pl : PatternList, p : Pattern) : PatternList => pl p;

op forall_expr (tp : Type, patterns : Option PatternList, body : Expression) : Expression =>
  "forall" "(" tp "," patterns "," body ")";

op exists_expr (tp : Type, patterns : Option PatternList, body : Expression) : Expression =>
  "exists" "(" tp "," patterns "," body ")";

// Labeled expressions
op labeled_expr (label : Ident, e : Expression) : Expression =>
  "labeled" "(" label "," e ")";

// Statement category
category Statement;

// Variable declarations
op var_decl (tp : Type) : Statement =>
  "var_decl" "(" tp ")";

op var_decl_init (tp : Type, init : Expression) : Statement =>
  "var_decl_init" "(" tp "," init ")";

// Value declarations
op val_decl (tp : Type, val : Expression) : Statement =>
  "val_decl" "(" tp "," val ")";

// Assignment using de Bruijn index
op assign_stmt (index : Num, e : Expression) : Statement =>
  "assign" "(" index "," e ")";

// Havoc/reinit
op havoc_stmt (index : Num) : Statement =>
  "havoc" "(" index ")";

// Assertions
op assert_stmt (e : Expression) : Statement =>
  "assert" "(" e ")";

op assume_stmt (e : Expression) : Statement =>
  "assume" "(" e ")";

op check_stmt (e : Expression) : Statement =>
  "check" "(" e ")";

op reach_stmt (e : Expression) : Statement =>
  "reach" "(" e ")";

op cover_stmt (e : Expression) : Statement =>
  "cover" "(" e ")";

// Control flow
category Block;
op block_stmt (stmts : Seq Statement) : Block =>
  "block" "(" stmts ")";

op if_stmt (c : Expression, then_block : Block, else_block : Option Block) : Statement =>
  "if_stmt" "(" c "," then_block "," else_block ")";

category LoopInvariant;
op loop_invariant (e : Expression) : LoopInvariant =>
  "invariant" "(" e ")";

op loop_stmt (c : Expression, invs : Option (Seq LoopInvariant), body : Block) : Statement =>
  "loop" "(" c "," invs "," body ")";

op exit_stmt : Statement => "exit";

op return_stmt (e : Option Expression) : Statement =>
  "return" "(" e ")";

// Blocks as statements
op block_as_stmt (b : Block) : Statement => b;

// Choice statements
op choice_stmt (stmts : Seq Statement) : Statement =>
  "choice" "(" stmts ")";

// Labeled statements
op labeled_stmt (label : Ident, s : Statement) : Statement =>
  "labeled_stmt" "(" label "," s ")";

// Forall statements with de Bruijn binding
op forall_stmt (tp : Type, body : Statement) : Statement =>
  "forall_stmt" "(" tp "," body ")";

// Function declarations
category FunctionDecl;
op func_decl (name : Ident, param_types : CommaSepBy Type, ret_type : Type, body : Expression) : FunctionDecl =>
  "function" "(" name "," param_types "," ret_type "," body ")";

// Datatype declarations
category Constructor;
category ConstructorList;

op constructor_decl (name : Ident, field_types : CommaSepBy Type) : Constructor =>
  "constructor" "(" name "," field_types ")";

op constructor_atom (c : Constructor) : ConstructorList => c;
op constructor_push (cl : ConstructorList, c : Constructor) : ConstructorList =>
  cl "," c;

category DatatypeDecl;
op datatype_decl (name : Ident, type_param_count : Num, constructors : ConstructorList) : DatatypeDecl =>
  "datatype" "(" name "," type_param_count "," constructors ")";

// Type declarations
category TypeDecl;
op type_decl (name : Ident, param_count : Num) : TypeDecl =>
  "type_decl" "(" name "," param_count ")";

// Metadata transformation functions
category Metadata;
op map_metadata (f : Ident, m : Metadata) : Metadata =>
  "map_metadata" "(" f "," m ")";

#end

namespace CoreASTDDM

#strata_gen CoreAST

end CoreASTDDM

---------------------------------------------------------------------

end Strata
