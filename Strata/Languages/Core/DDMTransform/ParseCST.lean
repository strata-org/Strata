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
DDM support for B3-like concrete syntax for Strata Core

This module defines a concrete syntax tree (CST) dialect for Strata Core
that closely follows B3 syntax conventions. The dialect includes:

- Expression syntax with B3-like operators and precedence
- Statement syntax without semicolons (like B3)
- Function declarations (without when/injective/taggers)
- Datatype declarations (matching Strata Core syntax)
- Type declarations

Key features:
- Almost a superset of B3 (except no axioms, only assumes)
- No semicolons required
- Support for quantifiers with patterns
- Labeled expressions and statements
- Choice and forall statements

Limitations:
- No axiom statements (only assume statements)
- No procedure declarations yet (will be added later)
- Function calls are basic (no complex argument patterns)

Example syntax:
```
var x : int := 42
assume x > 0
assert x != 0
if (x > 10) {
  var y : int := x * 2
  assert y > 20
}
```
-/

#dialect
dialect CoreCST;

// Basic types
type bool;
type int;
type string;
type real;

// Expression category with B3-like operators
category Expression;

// Literals
op nat_lit (n : Num) : Expression => n;
op bool_true : Expression => "true";
op bool_false : Expression => "false";
op string_lit (s : Str) : Expression => s;
op real_lit (d : Decimal) : Expression => d;

// Variables using identifiers (not de Bruijn indices)
op var_ref (name : Ident) : Expression => name;

// Logical operators
op not_expr (e : Expression) : Expression => "!" e;
op and_expr (a : Expression, b : Expression) : Expression => @[prec(10), leftassoc] a "&&" b;
op or_expr (a : Expression, b : Expression) : Expression => @[prec(8), leftassoc] a "||" b;
op implies_expr (a : Expression, b : Expression) : Expression => @[prec(5), rightassoc] a "==>" b;
op iff_expr (a : Expression, b : Expression) : Expression => @[prec(4)] a "<==>" b;

// Comparison operators
op eq_expr (a : Expression, b : Expression) : Expression => @[prec(15)] a "==" b;
op ne_expr (a : Expression, b : Expression) : Expression => @[prec(15)] a "!=" b;
op lt_expr (a : Expression, b : Expression) : Expression => @[prec(15)] a "<" b;
op le_expr (a : Expression, b : Expression) : Expression => @[prec(15)] a "<=" b;
op gt_expr (a : Expression, b : Expression) : Expression => @[prec(15)] a ">" b;
op ge_expr (a : Expression, b : Expression) : Expression => @[prec(15)] a ">=" b;

// Arithmetic operators
op neg_expr (e : Expression) : Expression => "-" e;
op add_expr (a : Expression, b : Expression) : Expression => @[prec(25), leftassoc] a "+" b;
op sub_expr (a : Expression, b : Expression) : Expression => @[prec(25), leftassoc] a "-" b;
op mul_expr (a : Expression, b : Expression) : Expression => @[prec(30), leftassoc] a "*" b;
op div_expr (a : Expression, b : Expression) : Expression => @[prec(30), leftassoc] a "div" b;
op mod_expr (a : Expression, b : Expression) : Expression => @[prec(30), leftassoc] a "mod" b;

// Conditionals
op if_then_else (c : Expression, t : Expression, f : Expression) : Expression => 
  "if" c "then" t "else" f;

// Let expressions
category LetBinding;
@[declare(v, tp)]
op let_bind (v : Ident, tp : Type, e : Expression) : LetBinding => v ":" tp ":=" e;

@[scope(b)]
op let_expr (b : LetBinding, @[scope(b)] body : Expression) : Expression =>
  "let" b "in" body;

// Function calls
op call_expr (f : Ident, args : CommaSepBy Expression) : Expression =>
  f "(" args ")";

// Quantifiers with patterns
category Pattern;
category PatternList;
op pattern_mk (exprs : CommaSepBy Expression) : Pattern => "{" exprs "}";
op pattern_atom (p : Pattern) : PatternList => p;
op pattern_push (pl : PatternList, p : Pattern) : PatternList => pl p;

category QuantBinding;
@[declare(v, tp)]
op quant_bind (v : Ident, tp : Type) : QuantBinding => v ":" tp;

category QuantBindings;
@[scope(b)]
op quant_bind_atom (b : QuantBinding) : QuantBindings => b;
@[scope(b)]
op quant_bind_push (qb : QuantBindings, @[scope(qb)] b : QuantBinding) : QuantBindings => qb "," b;

op forall_expr (binds : QuantBindings, @[scope(binds)] patterns : Option PatternList, @[scope(binds)] body : Expression) : Expression =>
  "forall" binds "::" patterns body;

op exists_expr (binds : QuantBindings, @[scope(binds)] patterns : Option PatternList, @[scope(binds)] body : Expression) : Expression =>
  "exists" binds "::" patterns body;

// Labeled expressions
op labeled_expr (label : Ident, e : Expression) : Expression =>
  "[" label "]:" e;

// Statement category
category Statement;

// Variable declarations
op var_decl (v : Ident, tp : Type) : Statement =>
  "var" v ":" tp;

op var_decl_init (v : Ident, tp : Type, init : Expression) : Statement =>
  "var" v ":" tp ":=" init;

// Value declarations
op val_decl (v : Ident, tp : Type, val : Expression) : Statement =>
  "val" v ":" tp ":=" val;

// Assignment using identifier (not de Bruijn index)
op assign_stmt (v : Ident, e : Expression) : Statement =>
  v ":=" e;

// Havoc/reinit using identifier
op havoc_stmt (v : Ident) : Statement =>
  "havoc" v;

// Assertions
op assert_stmt (e : Expression) : Statement =>
  "assert" e;

op assume_stmt (e : Expression) : Statement =>
  "assume" e;

op check_stmt (e : Expression) : Statement =>
  "check" e;

op reach_stmt (e : Expression) : Statement =>
  "reach" e;

op cover_stmt (e : Expression) : Statement =>
  "cover" e;

// Control flow
category Block;
op block_stmt (stmts : Seq Statement) : Block =>
  "{" stmts "}";

op if_stmt (c : Expression, then_block : Block, else_block : Option Block) : Statement =>
  "if" "(" c ")" then_block else_block;

category LoopInvariant;
op loop_invariant (e : Expression) : LoopInvariant =>
  "invariant" e;

op loop_stmt (c : Expression, invs : Option (Seq LoopInvariant), body : Block) : Statement =>
  "while" "(" c ")" invs body;

op exit_stmt : Statement => "exit";

op return_stmt (e : Option Expression) : Statement =>
  "return" e;

// Blocks as statements
op block_as_stmt (b : Block) : Statement => b;

// Choice statements
op choice_stmt (stmts : Seq Statement) : Statement =>
  "choice" "{" stmts "}";

// Labeled statements
op labeled_stmt (label : Ident, s : Statement) : Statement =>
  "[" label "]:" s;

// Forall statements
op forall_stmt (binds : QuantBindings, @[scope(binds)] body : Statement) : Statement =>
  "forall" binds "::" body;

// Function declarations
category FunctionParam;
@[declare(name, tp)]
op func_param (name : Ident, tp : Type) : FunctionParam =>
  name ":" tp;

category FunctionParams;
@[scope(p)]
op func_param_atom (p : FunctionParam) : FunctionParams => p;
@[scope(p)]
op func_param_push (ps : FunctionParams, @[scope(ps)] p : FunctionParam) : FunctionParams =>
  ps "," p;

category FunctionDecl;
op func_decl (name : Ident, params : Option FunctionParams, ret_type : Type, body : Expression) : FunctionDecl =>
  "function" name "(" params ")" ":" ret_type "{" body "}";

// Datatype declarations (matching Strata Core syntax)
category Constructor;
category ConstructorList;
category Field;
category FieldList;

@[declare(name, tp)]
op field_decl (name : Ident, tp : Type) : Field =>
  name ":" tp;

@[scope(f)]
op field_atom (f : Field) : FieldList => f;
@[scope(f)]
op field_push (fl : FieldList, @[scope(fl)] f : Field) : FieldList =>
  fl "," f;

@[constructor(name, fields)]
op constructor_decl (name : Ident, fields : Option FieldList) : Constructor =>
  name "(" fields ")";

op constructor_atom (c : Constructor) : ConstructorList => c;
op constructor_push (cl : ConstructorList, c : Constructor) : ConstructorList =>
  cl "," c;

category TypeParam;
@[declareTVar(name)]
op type_param (name : Ident) : TypeParam => name;

category TypeParams;
@[scope(tp)]
op type_param_atom (tp : TypeParam) : TypeParams => tp;
@[scope(tp)]
op type_param_push (tps : TypeParams, @[scope(tps)] tp : TypeParam) : TypeParams =>
  tps "," tp;

category DatatypeDecl;
op datatype_decl (name : Ident, type_params : Option TypeParams, constructors : ConstructorList) : DatatypeDecl =>
  "datatype" name "(" type_params ")" "{" constructors "}";

// Type declarations
category TypeDecl;
op type_decl (name : Ident, type_params : Option TypeParams) : TypeDecl =>
  "type" name "(" type_params ")";

#end

namespace CoreCSTDDM

#strata_gen CoreCST

end CoreCSTDDM

---------------------------------------------------------------------

end Strata
