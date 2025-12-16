/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean

-- Test that Bool can be used as an inductive type with true/false operators
#dialect
dialect TestBool;

category BoolExpr;

op printBool (b : BoolExpr) : Command => "print " b ";";
op wrappedBool (b: Bool): BoolExpr => b;

op ifThenElse (cond : Bool, thenVal : BoolExpr, elseVal : BoolExpr) : BoolExpr =>
  "if " cond " then " thenVal " else " elseVal;

#end

-- Test parsing with true
def testTrue := #strata program TestBool; print true; #end

/--
info: "program TestBool;\nprint true;"
-/
#guard_msgs in
#eval toString testTrue.format

-- Test parsing with false
def testFalse := #strata program TestBool; print false; #end

/--
info: "program TestBool;\nprint false;"
-/
#guard_msgs in
#eval toString testFalse.format

-- Test parsing with if-then-else using booleans
def testIfThenElse := #strata
program TestBool;
print if true then false else true;
#end

/--
info: "program TestBool;\nprint if true then false else (true);"
-/
#guard_msgs in
#eval toString testIfThenElse.format

-- Test that we can use booleans in nested expressions
def testNested := #strata
program TestBool;
print if true then if false then true else false else true;
#end

/--
info: "program TestBool;\nprint if true then if false then true else (false) else (true);"
-/
#guard_msgs in
#eval toString testNested.format
