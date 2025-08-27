/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Boogie

namespace Boogie

---------------------------------------------------------------------

section Tests
open Std (ToFormat Format format)
open Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Boogie.Syntax

def bad_prog : Program := { decls := [
      -- type Foo _ _;
      .type (.con { name := "Foo", numargs := 2}),
      -- type FooAlias a = Foo bool bool;
      .type (.syn { name := "FooAlias", typeArgs := ["a"], type := mty[Foo bool bool]}),
      -- const fooAliasVal : FooAlias bool;
      .func { name := "fooAliasVal", inputs := [], output := mty[FooAlias bool]},
      -- const fooVal : Foo int bool;
      .func { name := "fooVal", inputs := [], output := mty[Foo int bool]},
      .proc { header := {name := "P",
                         typeArgs := [],
                         inputs := [],
                         outputs := [] },
              spec := {
                  modifies := [],
                  preconditions := [],
                  postconditions := [] },
              body := [
                Statement.assert "test" eb[(~fooAliasVal == ~fooVal)]
              ]
      }
]}

/-- info: error: Cannot unify differently named type constructors bool and int! -/
#guard_msgs in
#eval do let ans ← typeCheckAndPartialEval Options.default bad_prog
         return (format ans)

def good_prog : Program := { decls := [
      -- type Foo _ _;
      .type (.con { name := "Foo", numargs := 2}),
      -- type FooAlias a = Foo int bool;
      .type (.syn { name := "FooAlias", typeArgs := ["a"], type := mty[Foo int bool]}),
      -- const fooAliasVal : ∀α. FooAlias α;
      .func { name := "fooAliasVal", typeArgs := ["α"], inputs := [], output := mty[FooAlias α]},
      -- const fooVal : Foo int bool;
      .func { name := "fooVal", inputs := [], output := mty[Foo int bool]},
      .proc { header := {name := "P",
                         typeArgs := [],
                         inputs := [],
                         outputs := [] },
              spec := {
                  modifies := [],
                  preconditions := [],
                  postconditions := [] },
              body := [
                Statement.assert "test" eb[(~fooAliasVal == ~fooVal)]
              ]
      }
]}

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: test
Assumptions:
Proof Obligation:
(~fooAliasVal == ~fooVal)

---
info: ok: [(type Boogie.Boundedness.Infinite Foo [_, _]
  type FooAlias a := (Foo int bool)
  func fooAliasVal : ∀[α]. () → (FooAlias α);
  func fooVal :  () → (Foo int bool);
  (procedure P :  () → ())
  modifies: []
  preconditions: ⏎
  postconditions: ⏎
  body: assert [test] (~fooAliasVal == ~fooVal)
  ,
  Error:
  none
  Subst Map:
  ⏎
  Expression Env:
  State:
  ⏎
  ⏎
  Evaluation Config:
  Eval Depth: 200
  Variable Prefix: $__
  Variable gen count: 0
  Factory Functions:
  func Int.Add :  ((x : int) (y : int)) → int;
  func Int.Sub :  ((x : int) (y : int)) → int;
  func Int.Mul :  ((x : int) (y : int)) → int;
  func Int.Div :  ((x : int) (y : int)) → int;
  func Int.Mod :  ((x : int) (y : int)) → int;
  func Int.Neg :  ((x : int)) → int;
  func Int.Lt :  ((x : int) (y : int)) → bool;
  func Int.Le :  ((x : int) (y : int)) → bool;
  func Int.Gt :  ((x : int) (y : int)) → bool;
  func Int.Ge :  ((x : int) (y : int)) → bool;
  func Real.Add :  ((x : real) (y : real)) → real;
  func Real.Sub :  ((x : real) (y : real)) → real;
  func Real.Mul :  ((x : real) (y : real)) → real;
  func Real.Div :  ((x : real) (y : real)) → real;
  func Real.Neg :  ((x : real)) → real;
  func Real.Lt :  ((x : real) (y : real)) → bool;
  func Real.Le :  ((x : real) (y : real)) → bool;
  func Real.Gt :  ((x : real) (y : real)) → bool;
  func Real.Ge :  ((x : real) (y : real)) → bool;
  func Bool.And :  ((x : bool) (y : bool)) → bool;
  func Bool.Or :  ((x : bool) (y : bool)) → bool;
  func Bool.Implies :  ((x : bool) (y : bool)) → bool;
  func Bool.Equiv :  ((x : bool) (y : bool)) → bool;
  func Bool.Not :  ((x : bool)) → bool;
  func Str.Length :  ((x : string)) → int;
  func Str.Concat :  ((x : string) (y : string)) → string;
  func old : ∀[a]. ((x : a)) → a;
  func select : ∀[k, v]. ((m : (Map k v)) (i : k)) → v;
  func update : ∀[k, v]. ((m : (Map k v)) (i : k) (x : v)) → (Map k v);
  func Bv8.Concat :  ((x : bv8) (y : bv8)) → bv16;
  func Bv16.Concat :  ((x : bv16) (y : bv16)) → bv32;
  func Bv32.Concat :  ((x : bv32) (y : bv32)) → bv64;
  func Bv1.Neg :  ((x : bv1)) → bv1;
  func Bv1.Add :  ((x : bv1) (y : bv1)) → bv1;
  func Bv1.Sub :  ((x : bv1) (y : bv1)) → bv1;
  func Bv1.Mul :  ((x : bv1) (y : bv1)) → bv1;
  func Bv1.Div :  ((x : bv1) (y : bv1)) → bv1;
  func Bv1.Mod :  ((x : bv1) (y : bv1)) → bv1;
  func Bv1.Not :  ((x : bv1)) → bv1;
  func Bv1.And :  ((x : bv1) (y : bv1)) → bv1;
  func Bv1.Or :  ((x : bv1) (y : bv1)) → bv1;
  func Bv1.Xor :  ((x : bv1) (y : bv1)) → bv1;
  func Bv1.Shl :  ((x : bv1) (y : bv1)) → bv1;
  func Bv1.UShr :  ((x : bv1) (y : bv1)) → bv1;
  func Bv1.Lt :  ((x : bv1) (y : bv1)) → bool;
  func Bv1.Le :  ((x : bv1) (y : bv1)) → bool;
  func Bv1.Gt :  ((x : bv1) (y : bv1)) → bool;
  func Bv1.Ge :  ((x : bv1) (y : bv1)) → bool;
  func Bv8.Neg :  ((x : bv8)) → bv8;
  func Bv8.Add :  ((x : bv8) (y : bv8)) → bv8;
  func Bv8.Sub :  ((x : bv8) (y : bv8)) → bv8;
  func Bv8.Mul :  ((x : bv8) (y : bv8)) → bv8;
  func Bv8.Div :  ((x : bv8) (y : bv8)) → bv8;
  func Bv8.Mod :  ((x : bv8) (y : bv8)) → bv8;
  func Bv8.Not :  ((x : bv8)) → bv8;
  func Bv8.And :  ((x : bv8) (y : bv8)) → bv8;
  func Bv8.Or :  ((x : bv8) (y : bv8)) → bv8;
  func Bv8.Xor :  ((x : bv8) (y : bv8)) → bv8;
  func Bv8.Shl :  ((x : bv8) (y : bv8)) → bv8;
  func Bv8.UShr :  ((x : bv8) (y : bv8)) → bv8;
  func Bv8.Lt :  ((x : bv8) (y : bv8)) → bool;
  func Bv8.Le :  ((x : bv8) (y : bv8)) → bool;
  func Bv8.Gt :  ((x : bv8) (y : bv8)) → bool;
  func Bv8.Ge :  ((x : bv8) (y : bv8)) → bool;
  func Bv16.Neg :  ((x : bv16)) → bv16;
  func Bv16.Add :  ((x : bv16) (y : bv16)) → bv16;
  func Bv16.Sub :  ((x : bv16) (y : bv16)) → bv16;
  func Bv16.Mul :  ((x : bv16) (y : bv16)) → bv16;
  func Bv16.Div :  ((x : bv16) (y : bv16)) → bv16;
  func Bv16.Mod :  ((x : bv16) (y : bv16)) → bv16;
  func Bv16.Not :  ((x : bv16)) → bv16;
  func Bv16.And :  ((x : bv16) (y : bv16)) → bv16;
  func Bv16.Or :  ((x : bv16) (y : bv16)) → bv16;
  func Bv16.Xor :  ((x : bv16) (y : bv16)) → bv16;
  func Bv16.Shl :  ((x : bv16) (y : bv16)) → bv16;
  func Bv16.UShr :  ((x : bv16) (y : bv16)) → bv16;
  func Bv16.Lt :  ((x : bv16) (y : bv16)) → bool;
  func Bv16.Le :  ((x : bv16) (y : bv16)) → bool;
  func Bv16.Gt :  ((x : bv16) (y : bv16)) → bool;
  func Bv16.Ge :  ((x : bv16) (y : bv16)) → bool;
  func Bv32.Neg :  ((x : bv32)) → bv32;
  func Bv32.Add :  ((x : bv32) (y : bv32)) → bv32;
  func Bv32.Sub :  ((x : bv32) (y : bv32)) → bv32;
  func Bv32.Mul :  ((x : bv32) (y : bv32)) → bv32;
  func Bv32.Div :  ((x : bv32) (y : bv32)) → bv32;
  func Bv32.Mod :  ((x : bv32) (y : bv32)) → bv32;
  func Bv32.Not :  ((x : bv32)) → bv32;
  func Bv32.And :  ((x : bv32) (y : bv32)) → bv32;
  func Bv32.Or :  ((x : bv32) (y : bv32)) → bv32;
  func Bv32.Xor :  ((x : bv32) (y : bv32)) → bv32;
  func Bv32.Shl :  ((x : bv32) (y : bv32)) → bv32;
  func Bv32.UShr :  ((x : bv32) (y : bv32)) → bv32;
  func Bv32.Lt :  ((x : bv32) (y : bv32)) → bool;
  func Bv32.Le :  ((x : bv32) (y : bv32)) → bool;
  func Bv32.Gt :  ((x : bv32) (y : bv32)) → bool;
  func Bv32.Ge :  ((x : bv32) (y : bv32)) → bool;
  func Bv64.Neg :  ((x : bv64)) → bv64;
  func Bv64.Add :  ((x : bv64) (y : bv64)) → bv64;
  func Bv64.Sub :  ((x : bv64) (y : bv64)) → bv64;
  func Bv64.Mul :  ((x : bv64) (y : bv64)) → bv64;
  func Bv64.Div :  ((x : bv64) (y : bv64)) → bv64;
  func Bv64.Mod :  ((x : bv64) (y : bv64)) → bv64;
  func Bv64.Not :  ((x : bv64)) → bv64;
  func Bv64.And :  ((x : bv64) (y : bv64)) → bv64;
  func Bv64.Or :  ((x : bv64) (y : bv64)) → bv64;
  func Bv64.Xor :  ((x : bv64) (y : bv64)) → bv64;
  func Bv64.Shl :  ((x : bv64) (y : bv64)) → bv64;
  func Bv64.UShr :  ((x : bv64) (y : bv64)) → bv64;
  func Bv64.Lt :  ((x : bv64) (y : bv64)) → bool;
  func Bv64.Le :  ((x : bv64) (y : bv64)) → bool;
  func Bv64.Gt :  ((x : bv64) (y : bv64)) → bool;
  func Bv64.Ge :  ((x : bv64) (y : bv64)) → bool;
  func fooAliasVal : ∀[α]. () → (FooAlias α);
  func fooVal :  () → (Foo int bool);
  ⏎
  ⏎
  Path Conditions:
  ⏎
  ⏎
  Warnings:
  []
  Deferred Proof Obligations:
  Label: test
  Assumptions:
  Proof Obligation:
  ((~fooAliasVal : (Foo int bool)) == (~fooVal : (Foo int bool)))
  ⏎
  )]
-/
#guard_msgs in
#eval do let ans ← typeCheckAndPartialEval Options.default good_prog
         return (format ans)

---------------------------------------------------------------------

def outOfScopeVarProg : Program := { decls := [
      .proc { header := {name := "P",
                         typeArgs := [],
                         inputs := [("x", mty[bool])],
                         outputs := [("y", mty[bool])] },
              spec := {
                  modifies := [],
                  preconditions := [],
                  postconditions := [] },
              body := [
                Statement.set "y" eb[((~Bool.Or x) x)],
                .ite eb[(x == #true)]
                  { ss := [Statement.init "q" t[int] eb[#0],
                           Statement.set "q" eb[#1],
                           Statement.set "y" eb[#true]] }
                  { ss := [Statement.init "q" t[int] eb[#0],
                           Statement.set "q" eb[#2],
                           Statement.set "y" eb[#true]] },
                Statement.assert "y_check" eb[y == #true],
                Statement.assert "q_check" eb[q == #1]
              ]
      }
]}

/--
info: error: [assert [q_check] (q == #1)] No free variables are allowed here!
Free Variables: [q]
-/
#guard_msgs in
#eval do let ans ← typeCheckAndPartialEval Options.default outOfScopeVarProg
         return (format ans)

---------------------------------------------------------------------

end Tests
end Boogie
