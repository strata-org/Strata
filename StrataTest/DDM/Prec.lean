/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean

#dialect
dialect TestPrec;

type bool;
fn trueExpr : bool => "t";
fn falseExpr : bool => "f";
fn and (a : bool, b : bool) : bool => @[prec(10), leftassoc] a " && " b;
fn or (a : bool, b : bool) : bool => @[prec(8), leftassoc] a " || " b;
fn imp (a : bool, b : bool) : bool => @[prec(7), rightassoc] a " => " b;
fn xor (a : bool, b : bool) : bool => @[prec(12)] a " ^^ " b;

op assert (b : bool) : Command => "assert " b ";\n";
#end

def ppParen (pgm : Strata.Program) :=
  IO.println <| toString <| pgm |>.format {alwaysParen := true }

/--
info: program TestPrec;
assert ((t) && (t)) && (t);
-/
#guard_msgs in
#eval ppParen #strata
program TestPrec;
assert t && t && t;
#end

/--
info: program TestPrec;
assert (t) => ((t) => (t));
-/
#guard_msgs in
#eval ppParen #strata
program TestPrec;
assert t => t => t;
#end

/--
info: program TestPrec;
assert (f) ^^ (f);
-/
#guard_msgs in
#eval ppParen #strata
program TestPrec;
assert f ^^ f;
#end

-- Check without associativity annotations, we get error.
/--
error: unexpected token '^^'; expected ';'
-/
#guard_msgs in
#eval ppParen #strata
program TestPrec;
assert f ^^ f ^^ f;
#end

/--
info: program TestPrec;
assert ((t) && (t)) || (t);
-/
#guard_msgs in
#eval ppParen #strata
program TestPrec;
assert t && t || t;
#end

/--
info: program TestPrec;
assert (t) || ((t) && (t));
-/
#guard_msgs in
#eval ppParen #strata
program TestPrec;
assert t || t && t;
#end

/--
info: program TestPrec;
assert ((t) || (f)) => (t);
-/
#guard_msgs in
#eval ppParen #strata
program TestPrec;
assert t || f => t;
#end
