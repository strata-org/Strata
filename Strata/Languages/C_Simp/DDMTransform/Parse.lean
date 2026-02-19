/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.DDM.Util.Format

#dialect
dialect C_Simp;

type int;
type bool;
type intArr;
type boolArr;

category TypeArgs;
op type_args (args : CommaSepBy Ident) : TypeArgs => "⟨" args "⟩";

category Bind;
@[declare(v, tp)]
op bind_mk (v : Ident, targs : Option TypeArgs, @[scope(targs)] tp : Type) : Bind =>
  v ":" targs tp;

category DeclList;
@[scope(b)]
op declAtom (b : Bind) : DeclList => b;
@[scope(b)]
op declPush (dl : DeclList, @[scope(dl)] b : Bind) : DeclList => dl "," b;

category MonoBind;
@[declare(v, tp)]
op mono_bind_mk (v : Ident, tp : Type) : MonoBind =>
  v ":" tp;

category MonoDeclList;
@[scope(b)]
op monoDeclAtom (b : MonoBind) : MonoDeclList => b;
@[scope(b)]
op monoDeclPush (dl : MonoDeclList, @[scope(dl)] b : MonoBind) : MonoDeclList =>
  dl "," b;


fn btrue : bool => "true";
fn bfalse : bool => "false";

fn eq (tp : Type, x : tp, y : tp) : bool => x "==" y;

fn lt (x : int, y : int) : bool => x "<" y;
fn le (x : int, y : int) : bool => x "<=" y;
fn gt (x : int, y : int) : bool => x ">" y;
fn ge (x : int, y : int) : bool => x ">=" y;

fn add (x : int, y : int) : int => x "+" y;
fn sub (x : int, y : int) : int => x "-" y;
fn mul (x : int, y : int) : int => x "*" y;
fn div (x : int, y : int) : int => x "/" y;
fn mod (x : int, y : int) : int => x "%" y;

fn not (x : bool) : bool => "!" x;
fn and (x : bool, y : bool) : bool => x "&&" y;
fn or  (x : bool, y : bool) : bool => x "||" y;


fn to_int (n : Num) : int => n;

fn len (a : intArr) : int => "len(" a ")";
fn get (a : intArr, i: int) : int => "get(" a "," i ")";

category Statement;

category Block;
op block (stmts : Seq Statement) : Block => "{\n" stmts "}\n";

@[declare(v, tp)]
op init_decl (v : Ident, tp : Type) : Statement => "var" v ":" tp ";\n";

category Else;
op if_command (c : bool, t : Block, f : Else) : Statement => "if" "(" c ")" t f;
op else1 (f : Block) : Else => "else" f;
op else0 () : Else =>;

category Binding;
@[declare(name, tp)]
op mkBinding (name : Ident, tp : TypeP) : Binding => @[prec(40)] name ":" tp;

category Bindings;
@[scope(bindings)]
op mkBindings (bindings : CommaSepBy Binding) : Bindings => "(" bindings ")";

category MeasureCat;
op measure (e : int) : MeasureCat => "//@decreases " e;

category InvariantCat;
op invariant (e : bool) : InvariantCat => "//@invariant " e;

op while_command (g : bool,
                  measure: Option MeasureCat,
                  invariant: Option InvariantCat,
                  b : Block) : Statement => "while"  "(" g ")\n" measure invariant b;

op assign (tp : Type, v : Ident, val : tp) : Statement => v "=" val ";\n";
op return (tp: Type, e : tp) : Statement => "return" e ";\n";

op procedure (retType: Type,
              typeArgs: Option TypeArgs,
              @[scope(typeArgs)] b : Bindings,
              name : Ident,
              @[scope(b)] pre: bool,
              @[scope(b)] post: bool,
              @[scope(b)] body : Block) : Command => retType " procedure " name typeArgs b
                                                     "//@pre " indent(2, pre) ";\n"
                                                     "//@post " indent(2, post) ";\n"
                                                     indent(2, body);

category Annotation;
op assert (lbl : Ident, c: bool) : Annotation => "//@assert [" lbl "]" c";\n";
op assume (lbl : Ident, c: bool) : Annotation => "//@assume [" lbl "]" c";\n";
op annotation (a : Annotation) : Statement => a;

#end


-- Test
private def testPrg :=
#strata
program C_Simp;

int procedure simpleTest (x: int, y: int)
  //@pre y > 0;
  //@post true;
{
  var z : int;
  z = x + y;
  //@assert [test_assert] z > x;
  if (z > 10) {
    z = z - 1;
  } else {
    z = z + 1;
  }
  //@assume [test_assume] z > 0;
  return 0;
}

#end
