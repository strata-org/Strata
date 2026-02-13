/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.ProcedureEval

namespace Core

---------------------------------------------------------------------

section Tests
open Std (ToFormat Format format)
open Procedure Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax

/--
info: Error:
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
func Str.Substr :  ((x : string) (i : int) (n : int)) → string;
func Str.ToRegEx :  ((x : string)) → regex;
func Str.InRegEx :  ((x : string) (y : regex)) → bool;
func Re.All :  () → regex;
func Re.AllChar :  () → regex;
func Re.Range :  ((x : string) (y : string)) → regex;
func Re.Concat :  ((x : regex) (y : regex)) → regex;
func Re.Star :  ((x : regex)) → regex;
func Re.Plus :  ((x : regex)) → regex;
func Re.Loop :  ((x : regex) (n1 : int) (n2 : int)) → regex;
func Re.Union :  ((x : regex) (y : regex)) → regex;
func Re.Inter :  ((x : regex) (y : regex)) → regex;
func Re.Comp :  ((x : regex)) → regex;
func Re.None :  () → regex;
func old : ∀[a]. ((x : a)) → a;
func select : ∀[k, v]. ((m : (Map k v)) (i : k)) → v;
func update : ∀[k, v]. ((m : (Map k v)) (i : k) (x : v)) → (Map k v);
func Triggers.empty :  () → Triggers;
func Triggers.addGroup :  ((g : TriggerGroup) (t : Triggers)) → Triggers;
func TriggerGroup.empty :  () → TriggerGroup;
func TriggerGroup.addTrigger : ∀[a]. ((x : a) (t : TriggerGroup)) → TriggerGroup;
func Bv8.Concat :  ((x : bv8) (y : bv8)) → bv16;
func Bv16.Concat :  ((x : bv16) (y : bv16)) → bv32;
func Bv32.Concat :  ((x : bv32) (y : bv32)) → bv64;
func Bv8.Extract_7_7 :  ((x : bv8)) → bv1;
func Bv16.Extract_15_15 :  ((x : bv16)) → bv1;
func Bv16.Extract_7_0 :  ((x : bv16)) → bv8;
func Bv32.Extract_31_31 :  ((x : bv32)) → bv1;
func Bv32.Extract_15_0 :  ((x : bv32)) → bv16;
func Bv32.Extract_7_0 :  ((x : bv32)) → bv8;
func Bv64.Extract_31_0 :  ((x : bv64)) → bv32;
func Bv64.Extract_15_0 :  ((x : bv64)) → bv16;
func Bv64.Extract_7_0 :  ((x : bv64)) → bv8;
func Bv1.Neg :  ((x : bv1)) → bv1;
func Bv1.Add :  ((x : bv1) (y : bv1)) → bv1;
func Bv1.Sub :  ((x : bv1) (y : bv1)) → bv1;
func Bv1.Mul :  ((x : bv1) (y : bv1)) → bv1;
func Bv1.UDiv :  ((x : bv1) (y : bv1)) → bv1;
func Bv1.UMod :  ((x : bv1) (y : bv1)) → bv1;
func Bv1.SDiv :  ((x : bv1) (y : bv1)) → bv1;
func Bv1.SMod :  ((x : bv1) (y : bv1)) → bv1;
func Bv1.Not :  ((x : bv1)) → bv1;
func Bv1.And :  ((x : bv1) (y : bv1)) → bv1;
func Bv1.Or :  ((x : bv1) (y : bv1)) → bv1;
func Bv1.Xor :  ((x : bv1) (y : bv1)) → bv1;
func Bv1.Shl :  ((x : bv1) (y : bv1)) → bv1;
func Bv1.UShr :  ((x : bv1) (y : bv1)) → bv1;
func Bv1.SShr :  ((x : bv1) (y : bv1)) → bv1;
func Bv1.ULt :  ((x : bv1) (y : bv1)) → bool;
func Bv1.ULe :  ((x : bv1) (y : bv1)) → bool;
func Bv1.UGt :  ((x : bv1) (y : bv1)) → bool;
func Bv1.UGe :  ((x : bv1) (y : bv1)) → bool;
func Bv1.SLt :  ((x : bv1) (y : bv1)) → bool;
func Bv1.SLe :  ((x : bv1) (y : bv1)) → bool;
func Bv1.SGt :  ((x : bv1) (y : bv1)) → bool;
func Bv1.SGe :  ((x : bv1) (y : bv1)) → bool;
func Bv8.Neg :  ((x : bv8)) → bv8;
func Bv8.Add :  ((x : bv8) (y : bv8)) → bv8;
func Bv8.Sub :  ((x : bv8) (y : bv8)) → bv8;
func Bv8.Mul :  ((x : bv8) (y : bv8)) → bv8;
func Bv8.UDiv :  ((x : bv8) (y : bv8)) → bv8;
func Bv8.UMod :  ((x : bv8) (y : bv8)) → bv8;
func Bv8.SDiv :  ((x : bv8) (y : bv8)) → bv8;
func Bv8.SMod :  ((x : bv8) (y : bv8)) → bv8;
func Bv8.Not :  ((x : bv8)) → bv8;
func Bv8.And :  ((x : bv8) (y : bv8)) → bv8;
func Bv8.Or :  ((x : bv8) (y : bv8)) → bv8;
func Bv8.Xor :  ((x : bv8) (y : bv8)) → bv8;
func Bv8.Shl :  ((x : bv8) (y : bv8)) → bv8;
func Bv8.UShr :  ((x : bv8) (y : bv8)) → bv8;
func Bv8.SShr :  ((x : bv8) (y : bv8)) → bv8;
func Bv8.ULt :  ((x : bv8) (y : bv8)) → bool;
func Bv8.ULe :  ((x : bv8) (y : bv8)) → bool;
func Bv8.UGt :  ((x : bv8) (y : bv8)) → bool;
func Bv8.UGe :  ((x : bv8) (y : bv8)) → bool;
func Bv8.SLt :  ((x : bv8) (y : bv8)) → bool;
func Bv8.SLe :  ((x : bv8) (y : bv8)) → bool;
func Bv8.SGt :  ((x : bv8) (y : bv8)) → bool;
func Bv8.SGe :  ((x : bv8) (y : bv8)) → bool;
func Bv16.Neg :  ((x : bv16)) → bv16;
func Bv16.Add :  ((x : bv16) (y : bv16)) → bv16;
func Bv16.Sub :  ((x : bv16) (y : bv16)) → bv16;
func Bv16.Mul :  ((x : bv16) (y : bv16)) → bv16;
func Bv16.UDiv :  ((x : bv16) (y : bv16)) → bv16;
func Bv16.UMod :  ((x : bv16) (y : bv16)) → bv16;
func Bv16.SDiv :  ((x : bv16) (y : bv16)) → bv16;
func Bv16.SMod :  ((x : bv16) (y : bv16)) → bv16;
func Bv16.Not :  ((x : bv16)) → bv16;
func Bv16.And :  ((x : bv16) (y : bv16)) → bv16;
func Bv16.Or :  ((x : bv16) (y : bv16)) → bv16;
func Bv16.Xor :  ((x : bv16) (y : bv16)) → bv16;
func Bv16.Shl :  ((x : bv16) (y : bv16)) → bv16;
func Bv16.UShr :  ((x : bv16) (y : bv16)) → bv16;
func Bv16.SShr :  ((x : bv16) (y : bv16)) → bv16;
func Bv16.ULt :  ((x : bv16) (y : bv16)) → bool;
func Bv16.ULe :  ((x : bv16) (y : bv16)) → bool;
func Bv16.UGt :  ((x : bv16) (y : bv16)) → bool;
func Bv16.UGe :  ((x : bv16) (y : bv16)) → bool;
func Bv16.SLt :  ((x : bv16) (y : bv16)) → bool;
func Bv16.SLe :  ((x : bv16) (y : bv16)) → bool;
func Bv16.SGt :  ((x : bv16) (y : bv16)) → bool;
func Bv16.SGe :  ((x : bv16) (y : bv16)) → bool;
func Bv32.Neg :  ((x : bv32)) → bv32;
func Bv32.Add :  ((x : bv32) (y : bv32)) → bv32;
func Bv32.Sub :  ((x : bv32) (y : bv32)) → bv32;
func Bv32.Mul :  ((x : bv32) (y : bv32)) → bv32;
func Bv32.UDiv :  ((x : bv32) (y : bv32)) → bv32;
func Bv32.UMod :  ((x : bv32) (y : bv32)) → bv32;
func Bv32.SDiv :  ((x : bv32) (y : bv32)) → bv32;
func Bv32.SMod :  ((x : bv32) (y : bv32)) → bv32;
func Bv32.Not :  ((x : bv32)) → bv32;
func Bv32.And :  ((x : bv32) (y : bv32)) → bv32;
func Bv32.Or :  ((x : bv32) (y : bv32)) → bv32;
func Bv32.Xor :  ((x : bv32) (y : bv32)) → bv32;
func Bv32.Shl :  ((x : bv32) (y : bv32)) → bv32;
func Bv32.UShr :  ((x : bv32) (y : bv32)) → bv32;
func Bv32.SShr :  ((x : bv32) (y : bv32)) → bv32;
func Bv32.ULt :  ((x : bv32) (y : bv32)) → bool;
func Bv32.ULe :  ((x : bv32) (y : bv32)) → bool;
func Bv32.UGt :  ((x : bv32) (y : bv32)) → bool;
func Bv32.UGe :  ((x : bv32) (y : bv32)) → bool;
func Bv32.SLt :  ((x : bv32) (y : bv32)) → bool;
func Bv32.SLe :  ((x : bv32) (y : bv32)) → bool;
func Bv32.SGt :  ((x : bv32) (y : bv32)) → bool;
func Bv32.SGe :  ((x : bv32) (y : bv32)) → bool;
func Bv64.Neg :  ((x : bv64)) → bv64;
func Bv64.Add :  ((x : bv64) (y : bv64)) → bv64;
func Bv64.Sub :  ((x : bv64) (y : bv64)) → bv64;
func Bv64.Mul :  ((x : bv64) (y : bv64)) → bv64;
func Bv64.UDiv :  ((x : bv64) (y : bv64)) → bv64;
func Bv64.UMod :  ((x : bv64) (y : bv64)) → bv64;
func Bv64.SDiv :  ((x : bv64) (y : bv64)) → bv64;
func Bv64.SMod :  ((x : bv64) (y : bv64)) → bv64;
func Bv64.Not :  ((x : bv64)) → bv64;
func Bv64.And :  ((x : bv64) (y : bv64)) → bv64;
func Bv64.Or :  ((x : bv64) (y : bv64)) → bv64;
func Bv64.Xor :  ((x : bv64) (y : bv64)) → bv64;
func Bv64.Shl :  ((x : bv64) (y : bv64)) → bv64;
func Bv64.UShr :  ((x : bv64) (y : bv64)) → bv64;
func Bv64.SShr :  ((x : bv64) (y : bv64)) → bv64;
func Bv64.ULt :  ((x : bv64) (y : bv64)) → bool;
func Bv64.ULe :  ((x : bv64) (y : bv64)) → bool;
func Bv64.UGt :  ((x : bv64) (y : bv64)) → bool;
func Bv64.UGe :  ((x : bv64) (y : bv64)) → bool;
func Bv64.SLt :  ((x : bv64) (y : bv64)) → bool;
func Bv64.SLe :  ((x : bv64) (y : bv64)) → bool;
func Bv64.SGt :  ((x : bv64) (y : bv64)) → bool;
func Bv64.SGe :  ((x : bv64) (y : bv64)) → bool;


Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: ret_y_lt_0
Property: assert
Assumptions:
(0_lt_x, (~Int.Lt #0 $__x0))
Proof Obligation:
(~Int.Lt (~Int.Neg ($__x0 : int)) #0)
-/
#guard_msgs in
#eval do let E := Env.init
         let (_proc, E) := evalOne E
              { header := {name := "P",
                           typeArgs := [],
                           inputs := [("x", mty[int])],
                           outputs := [("y", mty[int])] },
                spec := {
                    modifies := [],
                    preconditions := [("0_lt_x", ⟨eb[((~Int.Lt #0) x)], .Default, #[]⟩)],
                    postconditions := [("ret_y_lt_0", ⟨eb[((~Int.Lt y) #0)], .Default, #[]⟩)] },
                body := [
                  Statement.set "y" eb[(~Int.Neg x)]
                ]
              }
          return format E


end Tests
---------------------------------------------------------------------

end Core
