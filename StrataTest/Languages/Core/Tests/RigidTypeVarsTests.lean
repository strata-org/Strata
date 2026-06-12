/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.ProcedureType
import Strata.Languages.Core.Factory
import StrataDDM.Integration.Lean.HashCommands

meta section
open StrataDDM (Program)

/-!
# Rigid type-variable regression tests

These tests verify that a procedure's type parameter `a` behaves as a **rigid**
(skolemized) variable inside the procedure body. A body that refines `a` to a
concrete type (e.g., `a := int`) must be rejected.

## A — Soundness regressions (must be REJECTED)
## B — Must-still-accept (guard against over-rejection)
-/

namespace Strata.RigidTypeVarsTests

/-! ### A1: Body refines `a := int` via `x := 0`, caller instantiates `a := bool`.
    This is the headline soundness bug. -/
def refineThenCallBool : Program :=
#strata
program Core;
procedure Foo<a>(out x : a)
spec { ensures true; }
{
  x := 0;
};
procedure Test()
spec { ensures true; }
{
  var y : bool := true;
  call Foo(out y);
};
#end

/--
error: ❌ Type checking error.
Rigid type variable 'a' was refined to 'int' by the initializer
-/
#guard_msgs in
#eval Core.verify refineThenCallBool

/-! ### A2: Body `var tmp : a := 0` refines rigid `a` to `int`. -/
def refineThenCallInt : Program :=
#strata
program Core;
procedure Foo<a>(x : a)
spec { ensures true; }
{
  var tmp : a := 0;
};
procedure Test()
spec { ensures true; }
{
  call Foo(5);
};
#end

/--
error: ❌ Type checking error.
Rigid type variable 'a' was refined to 'int' by the initializer
-/
#guard_msgs in
#eval Core.verify refineThenCallInt

/-! ### A3: Call-site conflict — `Id<a>(x:a, out y:a){y:=x}` called with
    `a := bool` for input and `a := int` for output.
    Already correctly rejected; guard against regression. -/
def callSiteConflict : Program :=
#strata
program Core;
procedure Id<a>(x : a, out y : a)
spec { ensures true; }
{
  y := x;
};
procedure Test()
spec { ensures true; }
{
  var b : bool := true;
  var i : int := 0;
  call Id(b, out i);
};
#end

/--
error: ❌ Type checking error.
Impossible to unify bool with int.
-/
#guard_msgs in
#eval Core.verify callSiteConflict

/-! ### B4: Genuinely polymorphic body — must still be accepted.
    `Id<a>(x:a, out y:a){ y := x }` called at a consistent concrete type. -/
def polyBodyAccepted : Program :=
#strata
program Core;
procedure Id<a>(x : a, out y : a)
spec { ensures true; }
{
  y := x;
};
procedure Test()
spec { ensures true; }
{
  var b : bool := true;
  call Id(true, out b);
};
#end

/--
info: [Strata.Core] Type checking succeeded.
⏎
⏎
VCs:
Label: Id_ensures_0
Property: assert
Obligation:
true
⏎
Label: Test_ensures_0
Property: assert
Obligation:
true
⏎
---
info:
Obligation: Id_ensures_0
Property: assert
Result: ✅ pass
⏎
Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify polyBodyAccepted

/-! ### A5: Body equates two distinct rigid type params — `x := y` forces `a = b`. -/
def equateTwoTypeParams : Program :=
#strata
program Core;
procedure Foo<a, b>(x : a, out y : b)
spec { ensures true; }
{
  y := x;
};
#end

/--
error: ❌ Type checking error.
Rigid type variable 'b' was refined to 'a' by the initializer
-/
#guard_msgs in
#eval Core.verify equateTwoTypeParams

end Strata.RigidTypeVarsTests

---------------------------------------------------------------------

/-! ## Unit-level tests (abstract syntax, direct typechecker invocation) -/

section RigidTypeVarsUnitTests
open Core
open Std (ToFormat Format format)
open Procedure Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Strata (TransM translateProgram)

-- Q1: `var x : ∀a. a := true` (polymorphic declared type, single statement).
/--
info: ok: (procedure Q1 ()
 {
   var x : bool := true;
 };
 ,
 context:
 types:   ⏎
 aliases: [] state: tyGen: 1 tyPrefix: $__ty exprGen: 0 exprPrefix: $__var subst: [($__ty0, bool)])
-/
#guard_msgs in
#eval do let ans ← typeCheck (LContext.default (functions := Core.Factory)) TEnv.default
                    Program.init
                    { header := {name := "Q1", typeArgs := [], inputs := [], outputs := [] },
                      spec := { preconditions := [], postconditions := [] },
                      body := .structured [ Statement.init "x" t[∀a. %a] (.det eb[#true]) .empty] }
                    .empty
         return format ans

-- Q1 full: `var x : ∀a. a := true; x := x + 1` — the `set` fails because `x : bool`
-- cannot unify with `Int.Add`'s `(int, int) → int` signature.
/--
info: error: Impossible to unify (arrow int (arrow int int)) with (arrow bool $__ty1).
First mismatch: int with bool.
-/
#guard_msgs in
#eval do let ans ← typeCheck (LContext.default (functions := Core.Factory)) TEnv.default
                    Program.init
                    { header := {name := "Q1", typeArgs := [], inputs := [], outputs := [] },
                      spec := { preconditions := [], postconditions := [] },
                      body := .structured [ Statement.init "x" t[∀a. %a] (.det eb[#true]) .empty,
                                Statement.set "x" eb[((~Int.Add x) #1)] .empty ] }
                    .empty
         return format ans

-- Q2a: procedure ⟨a⟩(z : a) with body `var x : a := 3; x := true` (the full sequence).
-- Refining `a := int` via the initializer is rejected: `a` is a rigid type parameter.
def q2a_refineRigidVar : StrataDDM.Program :=
#strata
program Core;
procedure Q2a<a>(z : a)
spec { ensures true; }
{
  var x : a := 3;
  x := true;
};
#end

/-- info: error: (5543-5558) Rigid type variable 'a' was refined to 'int' by the initializer -/
#guard_msgs in
#eval Core.typeCheck .quiet (TransM.run Inhabited.default (translateProgram q2a_refineRigidVar)).fst

-- Q2b: procedure ⟨a⟩(z : a) with body `var x : a := z; x := z` (matches the rigid tyvar).
-- This is fine: the initializer `z` has type `a`, matching the declared type `a` exactly.
def q2b_matchRigidVar : StrataDDM.Program :=
#strata
program Core;
procedure Q2b<a>(z : a)
spec { ensures true; }
{
  var x : a := z;
  x := z;
};
#end

/--
info: ok: program Core;
⏎
procedure Q2b (z : a)
spec {
  ensures [Q2b_ensures_0]: true;
  } {
  var x : a := z;
  x := z;
};
-/
#guard_msgs in
#eval Core.typeCheck .quiet (TransM.run Inhabited.default (translateProgram q2b_matchRigidVar)).fst

-- Q2c: procedure ⟨a⟩(z : a) with body `var y : int := z` — the declared type is `int`
-- (no rigid vars in xty) but the initializer `z : a` forces `a = int` via unification.
-- Correctly rejected: the inferred-type side refined the rigid var.
def q2c_inferredSideRefine : StrataDDM.Program :=
#strata
program Core;
procedure Q2c<a>(z : a)
spec { ensures true; }
{
  var y : int := z;
};
#end

/-- info: error: (6756-6773) Rigid type variable 'a' was refined to 'int' by the initializer -/
#guard_msgs in
#eval Core.typeCheck .quiet (TransM.run Inhabited.default (translateProgram q2c_inferredSideRefine)).fst

-- Q2d: procedure ⟨a⟩(z : a) with body `assert z < 0` — the assert forces `a = int`
-- via expression-internal unification. Correctly rejected.
-- (Cannot be expressed in concrete syntax: the translator rejects `lt` on type vars.)
/--
info: error: Rigid type variable 'a' was refined to 'int' by the initializer
-/
#guard_msgs in
#eval do let ans ← typeCheck (LContext.default (functions := Core.Factory)) TEnv.default
                    Program.init
                    { header := {name := "Q2d", typeArgs := ["a"],
                                 inputs := [("z", mty[%a])], outputs := [] },
                      spec := { preconditions := [], postconditions := [] },
                      body := .structured [ Statement.assert "lbl" eb[((~Int.Lt z) #0)] .empty ] }
                    .empty
         return format ans

end RigidTypeVarsUnitTests

end
