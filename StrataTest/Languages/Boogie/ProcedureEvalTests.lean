/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.ProcedureEval

namespace Boogie

---------------------------------------------------------------------

section Tests
open Std (ToFormat Format format)
open Procedure Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.Syntax Boogie.Syntax

/--
info: ok: Error:
none
Subst Map:
(x, ($__x0 : int)) (y, ($__y1 : int))
Expression Env:
State:


Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 2
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
func Bv1.Add :  ((x : bv1) (y : bv1)) → bv1;
func Bv1.Sub :  ((x : bv1) (y : bv1)) → bv1;
func Bv1.Mul :  ((x : bv1) (y : bv1)) → bv1;
func Bv1.Neg :  ((x : bv1)) → bv1;
func Bv1.Lt :  ((x : bv1) (y : bv1)) → bool;
func Bv1.Le :  ((x : bv1) (y : bv1)) → bool;
func Bv1.Gt :  ((x : bv1) (y : bv1)) → bool;
func Bv1.Ge :  ((x : bv1) (y : bv1)) → bool;
func Bv8.Add :  ((x : bv8) (y : bv8)) → bv8;
func Bv8.Sub :  ((x : bv8) (y : bv8)) → bv8;
func Bv8.Mul :  ((x : bv8) (y : bv8)) → bv8;
func Bv8.Neg :  ((x : bv8)) → bv8;
func Bv8.Lt :  ((x : bv8) (y : bv8)) → bool;
func Bv8.Le :  ((x : bv8) (y : bv8)) → bool;
func Bv8.Gt :  ((x : bv8) (y : bv8)) → bool;
func Bv8.Ge :  ((x : bv8) (y : bv8)) → bool;
func Bv16.Add :  ((x : bv16) (y : bv16)) → bv16;
func Bv16.Sub :  ((x : bv16) (y : bv16)) → bv16;
func Bv16.Mul :  ((x : bv16) (y : bv16)) → bv16;
func Bv16.Neg :  ((x : bv16)) → bv16;
func Bv16.Lt :  ((x : bv16) (y : bv16)) → bool;
func Bv16.Le :  ((x : bv16) (y : bv16)) → bool;
func Bv16.Gt :  ((x : bv16) (y : bv16)) → bool;
func Bv16.Ge :  ((x : bv16) (y : bv16)) → bool;
func Bv32.Add :  ((x : bv32) (y : bv32)) → bv32;
func Bv32.Sub :  ((x : bv32) (y : bv32)) → bv32;
func Bv32.Mul :  ((x : bv32) (y : bv32)) → bv32;
func Bv32.Neg :  ((x : bv32)) → bv32;
func Bv32.Lt :  ((x : bv32) (y : bv32)) → bool;
func Bv32.Le :  ((x : bv32) (y : bv32)) → bool;
func Bv32.Gt :  ((x : bv32) (y : bv32)) → bool;
func Bv32.Ge :  ((x : bv32) (y : bv32)) → bool;
func Bv64.Add :  ((x : bv64) (y : bv64)) → bv64;
func Bv64.Sub :  ((x : bv64) (y : bv64)) → bv64;
func Bv64.Mul :  ((x : bv64) (y : bv64)) → bv64;
func Bv64.Neg :  ((x : bv64)) → bv64;
func Bv64.Lt :  ((x : bv64) (y : bv64)) → bool;
func Bv64.Le :  ((x : bv64) (y : bv64)) → bool;
func Bv64.Gt :  ((x : bv64) (y : bv64)) → bool;
func Bv64.Ge :  ((x : bv64) (y : bv64)) → bool;


Path Conditions:


Deferred Proof Obligations:
Label: ret_y_lt_0
Assumptions:
(0_lt_x, ((~Int.Lt #0) $__x0))
Proof Obligation:
((~Int.Lt (~Int.Neg ($__x0 : int))) #0)
-/
#guard_msgs in
#eval do let E ← Env.init.addFactory Boogie.Factory
         let (_proc, E) := evalOne E
              { header := {name := "P",
                           typeArgs := [],
                           inputs := [("x", mty[int])],
                           outputs := [("y", mty[int])] },
                spec := {
                    modifies := [],
                    preconditions := [("0_lt_x", ⟨eb[((~Int.Lt #0) x)], .Default⟩)],
                    postconditions := [("ret_y_lt_0", ⟨eb[((~Int.Lt y) #0)], .Default⟩)] },
                body := [
                  Statement.set "y" eb[(~Int.Neg x)]
                ]
              }
          return format E


end Tests
---------------------------------------------------------------------

end Boogie
