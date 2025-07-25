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

-- Minimal dialect to test dialects can be declared.
#guard_msgs in
#dialect
dialect Test;
op assert : Command => "assert" ";";
op decimal (v : Decimal) : Command => "decimal " v ";";
#end

def testProgram := #strata program Test; decimal 1e99; #end

#guard toString testProgram.format == "decimal 1e99;"

/--
error: P already declared.
---
error: Parameters for a type declaration must have category Type.
---
error: Undeclared type or category Undeclared.
---
error: Q already declared.
---
error: Parameters for a type declaration must have category Type.
-/
#guard_msgs in
#dialect
dialect FailTestType;
type P;
// Try declaring type that already exists
type P (b: Type);
// Declare parameterized type with invalid category
type Q (b: BindingType);
// Check type is declared
type Q (b: Undeclared);
// Should succeed without error.
type Q (b: Type);
// Should fail with two errors.
type Q (b: BindingType);
#end

/--
error: noArg already declared.
---
error: Unexpected argument to noArg.
-/
#guard_msgs in
#dialect
dialect FailTestAttr;
metadata noArg;
metadata noArg;
metadata foo (name : Ident);

type Nat;

@[noArg]
fn f (b: Nat) : Nat => "f" b;

@[noArg(abc)]
fn g (b: Decimal) : Nat => "f" b;
#end

#guard_msgs in
#dialect
dialect TestLambda;
type bool;
type int;
fn t : bool => "true";

category Decl;
@[declare(name, tp)]
op decl (name : Ident, tp : Type) : Decl => name ":" tp;

fn lambda (tp : Type, decl : Decl, @[scope(decl)] r : tp) : fnOf(decl, tp) =>
  "fun" "(" decl ")" "=>" r;

op eval (tp : Type, e : tp): Command => "eval" e ":" tp ";";
#end

/--
error: Expression has type bool -> bool when int expected.
-/
#guard_msgs in
example := #strata
program TestLambda;

// Should report error
eval ((fun (x : bool) => x)) : int;

// Should succeed.
eval ((fun (x : bool) => x)) : bool -> bool;
#end
