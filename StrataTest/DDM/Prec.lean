/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
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

def ppParen (env : Strata.Environment) := env |>.format {alwaysParen := true }

/--
info: assert ((t) && (t)) && (t);
-/
#guard_msgs in
#eval ppParen #strata
program TestPrec;
assert t && t && t;
#end

/--
info: assert (t) => ((t) => (t));
-/
#guard_msgs in
#eval ppParen #strata
program TestPrec;
assert t => t => t;
#end

/--
info: assert (f) ^^ (f);
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
info: assert ((t) && (t)) || (t);
-/
#guard_msgs in
#eval ppParen #strata
program TestPrec;
assert t && t || t;
#end

/--
info: assert (t) || ((t) && (t));
-/
#guard_msgs in
#eval ppParen #strata
program TestPrec;
assert t || t && t;
#end

/--
info: assert ((t) || (f)) => (t);
-/
#guard_msgs in
#eval ppParen #strata
program TestPrec;
assert t || f => t;
#end
