/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.DDM.Util.Format

namespace Strata

#dialect
dialect Dyn;

// Primitive types
type int;
type bool;
type string;

// To support dynamic typing we type everything as `Any`
type Any;

// Generic types
category TypeArgs;
op type_args (args : CommaSepBy Type) : TypeArgs => "[" args "]";

// Function types
category FuncType;
op func_type (params : CommaSepBy Type, ret : Type) : FuncType => "(" params ")" "->" ret;

// Expressions
fn btrue : bool => "True";
fn bfalse : bool => "False";
fn to_int (n : Num) : int => n;
fn strLit (s : Str) : string => s;

// Typecasts
// Casts to Any
fn str_to_Any (s: string) : Any => "str_to_Any("s")";
fn int_to_Any (i: int) : Any => "int_to_Any("i")";
fn bool_to_Any (b: bool) : Any => "bool_to_Any("b")";
fn fun_to_Any (f: Any -> Any -> Any) : Any => "fun_to_Any("f")";

// Casts from Any
fn Any_to_string (a: Any) : string => "Any_to_str("a")";
fn Any_to_int (a: Any) : int => "Any_to_int("a")";
fn Any_to_bool (a: Any) : int => "Any_to_bool("a")";
fn Any_to_fun (a: Any) : Any -> Any -> Any => "Any_to_fun("a")";


// We'd like to be generic in our expression languages.
// For now, we just leave these hard-coded with the idea
// that you can coerce or return exceptions when the operator
// doesn't support an argument's type

// Arithmetic
fn add (x : Any, y : Any) : Any => x "+" y;
fn sub (x : Any, y : Any) : Any => x "-" y;
fn mul (x : Any, y : Any) : Any => x "*" y;
fn div (x : Any, y : Any) : Any => x "/" y;

// Comparisons
fn eq (x : Any, y : Any) : bool => x "==" y;
fn lt (x : Any, y : Any) : bool => x "<" y;
fn le (x : Any, y : Any) : bool => x "<=" y;
fn gt (x : Any, y : Any) : bool => x ">" y;
fn ge (x : Any, y : Any) : bool => x ">=" y;

// Boolean operations
fn not (x : Any) : Any => "not" x;
fn and (x : Any, y : Any) : Any => x "and" y;
fn or (x : Any, y : Any) : Any => x "or" y;

// List operations
fn list_get (lst : Any, idx : Any) : Any => lst "[" idx "]";
fn list_set (lst: Any, idx : Any, val : Any) : bool => lst "[" idx "] = " val;
fn list_len (lst : Any) : Any => "len(" lst ")";
fn list_create () : Any => "[]";
fn list_resize (lst : Any, new_size : Any) : bool => "list_resize(" lst ", " new_size")";

// Dict operations
fn dict_get (dict : Any, key : Any) : Any => dict "[" key "]";
fn dict_set (dict : Any, key : Any, val : Any) : Any => dict "[" key "]" "=" val;
fn dict_create () : Any => "{}";
fn dict_list_keys (dict : Any) : Any => "dict_list_keys(" dict ")";
fn dict_has_key (dict : Any, key: Any) : bool => "dict_has_key(" dict ", " key ")";

// Function calls with dynamic arguments
fn func_call (func : Any, args : CommaSepBy Expr) : Any =>  "call("func "," args ")";


// Type introspection
fn typeof (tp : Type, val : tp) : string => "typeof(" val ")";
fn isinstance (tp : Type, val : tp, target_type : string) : Any => "isinstance(" val "," target_type ")";

// Heap operations
fn heap_alloc () : Any => "alloc()";
fn heap_read (addr : Any) : Any => "read(" addr ")";
fn heap_write (addr : Any, val : Any) : Any => "write(" addr "," val ")";
fn heap_free (addr : Any) : Any => "free(" addr ")";

// Statements
category Statement;

// Variable declaration
@[declare(name, tp)]
op var_decl (name : Ident, tp : Type) : Statement => "var" name ":" tp ";\n";

// Assignment
op assign (tp : Type, name : Ident, val : tp) : Statement => name "=" val ";\n";

// Return statement
op return_stmt (tp : Type, val : tp) : Statement => "return" val ";\n";

// Block
category Block;
op block (stmts : Seq Statement) : Block => "{\n" stmts "}\n";

// If statement
category Else;
op if_stmt (cond : Any, then_block : Block, else_part : Else) : Statement =>
  "if" "(" cond ")" then_block else_part;
op else_block (block : Block) : Else => "else" block;
op no_else () : Else =>;

// While loop
op while_stmt (cond : Any, body : Block) : Statement =>
  "while" "(" cond ")" body;

// We use this to model language constructs that don't affect the analysis
// under consideration. By modeling a source language construct this way, any
// analysis downstream of this Dyn program will treat the construct as a no-op
op unmodeled : Statement => "UNMODELED";

category Param;
@[declare(name, tp)]
op mkParam (name : Ident, tp : TypeP) : Param => @[prec(40)] name ":" tp;

category Params;
@[scope(Params)]
op mkParams (Params : CommaSepBy Param) : Params => "(" Params ")";


// Function definition
@[declareFn(name, params, ret_type)]
op function_def (ret_type : Type,
                name : Ident,
                params : Params,
                @[scope(params)] body : Block) : Command =>
  "def" name params "->" ret_type body;

#end

-- Generate AST
namespace Dyn
#strata_gen Dyn
end Dyn
