/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.Languages.Core.StatementEval

namespace Core

---------------------------------------------------------------------

section Tests
open Std (ToFormat Format format)
open Procedure Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax

/--
info: Error:
none
Subst Map:

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
func Int.SafeDiv :  ((x : int) (y : int)) → int
  requires !(y == 0);
func Int.Mod :  ((x : int) (y : int)) → int;
func Int.SafeMod :  ((x : int) (y : int)) → int
  requires !(y == 0);
func Int.DivT :  ((x : int) (y : int)) → int;
func Int.SafeDivT :  ((x : int) (y : int)) → int
  requires !(y == 0);
func Int.ModT :  ((x : int) (y : int)) → int;
func Int.SafeModT :  ((x : int) (y : int)) → int
  requires !(y == 0);
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
func const : ∀[k, v]. ((d : v)) → (Map k v);
func select : ∀[k, v]. ((m : (Map k v)) (i : k)) → v;
func update : ∀[k, v]. ((m : (Map k v)) (i : k) (x : v)) → (Map k v);
func Sequence.length : ∀[a]. ((s : (Sequence a))) → int;
func Sequence.empty : ∀[a]. () → (Sequence a);
func Sequence.append : ∀[a]. ((s1 : (Sequence a)) (s2 : (Sequence a))) → (Sequence a);
func Sequence.select : ∀[a]. ((s : (Sequence a)) (i : int)) → a;
func Sequence.build : ∀[a]. ((s : (Sequence a)) (v : a)) → (Sequence a);
func Sequence.update : ∀[a]. ((s : (Sequence a)) (i : int) (v : a)) → (Sequence a);
func Sequence.contains : ∀[a]. ((s : (Sequence a)) (v : a)) → bool;
func Sequence.take : ∀[a]. ((s : (Sequence a)) (n : int)) → (Sequence a);
func Sequence.drop : ∀[a]. ((s : (Sequence a)) (n : int)) → (Sequence a);
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
func Bv1.SNegOverflow :  ((x : bv1)) → bool;
func Bv1.SAddOverflow :  ((x : bv1) (y : bv1)) → bool;
func Bv1.SSubOverflow :  ((x : bv1) (y : bv1)) → bool;
func Bv1.SMulOverflow :  ((x : bv1) (y : bv1)) → bool;
func Bv1.SDivOverflow :  ((x : bv1) (y : bv1)) → bool;
func Bv1.UNegOverflow :  ((x : bv1)) → bool;
func Bv1.UAddOverflow :  ((x : bv1) (y : bv1)) → bool;
func Bv1.USubOverflow :  ((x : bv1) (y : bv1)) → bool;
func Bv1.UMulOverflow :  ((x : bv1) (y : bv1)) → bool;
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
func Bv8.SNegOverflow :  ((x : bv8)) → bool;
func Bv8.SAddOverflow :  ((x : bv8) (y : bv8)) → bool;
func Bv8.SSubOverflow :  ((x : bv8) (y : bv8)) → bool;
func Bv8.SMulOverflow :  ((x : bv8) (y : bv8)) → bool;
func Bv8.SDivOverflow :  ((x : bv8) (y : bv8)) → bool;
func Bv8.UNegOverflow :  ((x : bv8)) → bool;
func Bv8.UAddOverflow :  ((x : bv8) (y : bv8)) → bool;
func Bv8.USubOverflow :  ((x : bv8) (y : bv8)) → bool;
func Bv8.UMulOverflow :  ((x : bv8) (y : bv8)) → bool;
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
func Bv16.SNegOverflow :  ((x : bv16)) → bool;
func Bv16.SAddOverflow :  ((x : bv16) (y : bv16)) → bool;
func Bv16.SSubOverflow :  ((x : bv16) (y : bv16)) → bool;
func Bv16.SMulOverflow :  ((x : bv16) (y : bv16)) → bool;
func Bv16.SDivOverflow :  ((x : bv16) (y : bv16)) → bool;
func Bv16.UNegOverflow :  ((x : bv16)) → bool;
func Bv16.UAddOverflow :  ((x : bv16) (y : bv16)) → bool;
func Bv16.USubOverflow :  ((x : bv16) (y : bv16)) → bool;
func Bv16.UMulOverflow :  ((x : bv16) (y : bv16)) → bool;
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
func Bv32.SNegOverflow :  ((x : bv32)) → bool;
func Bv32.SAddOverflow :  ((x : bv32) (y : bv32)) → bool;
func Bv32.SSubOverflow :  ((x : bv32) (y : bv32)) → bool;
func Bv32.SMulOverflow :  ((x : bv32) (y : bv32)) → bool;
func Bv32.SDivOverflow :  ((x : bv32) (y : bv32)) → bool;
func Bv32.UNegOverflow :  ((x : bv32)) → bool;
func Bv32.UAddOverflow :  ((x : bv32) (y : bv32)) → bool;
func Bv32.USubOverflow :  ((x : bv32) (y : bv32)) → bool;
func Bv32.UMulOverflow :  ((x : bv32) (y : bv32)) → bool;
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
func Bv64.SNegOverflow :  ((x : bv64)) → bool;
func Bv64.SAddOverflow :  ((x : bv64) (y : bv64)) → bool;
func Bv64.SSubOverflow :  ((x : bv64) (y : bv64)) → bool;
func Bv64.SMulOverflow :  ((x : bv64) (y : bv64)) → bool;
func Bv64.SDivOverflow :  ((x : bv64) (y : bv64)) → bool;
func Bv64.UNegOverflow :  ((x : bv64)) → bool;
func Bv64.UAddOverflow :  ((x : bv64) (y : bv64)) → bool;
func Bv64.USubOverflow :  ((x : bv64) (y : bv64)) → bool;
func Bv64.UMulOverflow :  ((x : bv64) (y : bv64)) → bool;
func Bv1.SafeAdd :  ((x : bv1) (y : bv1)) → bv1
  requires !(x <= y);
func Bv1.SafeSub :  ((x : bv1) (y : bv1)) → bv1
  requires !(x <= y);
func Bv1.SafeMul :  ((x : bv1) (y : bv1)) → bv1
  requires !(x <= y);
func Bv1.SafeNeg :  ((x : bv1)) → bv1
  requires !(!x);
func Bv1.SafeUAdd :  ((x : bv1) (y : bv1)) → bv1
  requires !(x <= y);
func Bv1.SafeUSub :  ((x : bv1) (y : bv1)) → bv1
  requires !(x <= y);
func Bv1.SafeUMul :  ((x : bv1) (y : bv1)) → bv1
  requires !(x <= y);
func Bv1.SafeUNeg :  ((x : bv1)) → bv1
  requires !(!x);
func Bv8.SafeAdd :  ((x : bv8) (y : bv8)) → bv8
  requires !(x <= y);
func Bv8.SafeSub :  ((x : bv8) (y : bv8)) → bv8
  requires !(x <= y);
func Bv8.SafeMul :  ((x : bv8) (y : bv8)) → bv8
  requires !(x <= y);
func Bv8.SafeNeg :  ((x : bv8)) → bv8
  requires !(!x);
func Bv8.SafeUAdd :  ((x : bv8) (y : bv8)) → bv8
  requires !(x <= y);
func Bv8.SafeUSub :  ((x : bv8) (y : bv8)) → bv8
  requires !(x <= y);
func Bv8.SafeUMul :  ((x : bv8) (y : bv8)) → bv8
  requires !(x <= y);
func Bv8.SafeUNeg :  ((x : bv8)) → bv8
  requires !(!x);
func Bv16.SafeAdd :  ((x : bv16) (y : bv16)) → bv16
  requires !(x <= y);
func Bv16.SafeSub :  ((x : bv16) (y : bv16)) → bv16
  requires !(x <= y);
func Bv16.SafeMul :  ((x : bv16) (y : bv16)) → bv16
  requires !(x <= y);
func Bv16.SafeNeg :  ((x : bv16)) → bv16
  requires !(!x);
func Bv16.SafeUAdd :  ((x : bv16) (y : bv16)) → bv16
  requires !(x <= y);
func Bv16.SafeUSub :  ((x : bv16) (y : bv16)) → bv16
  requires !(x <= y);
func Bv16.SafeUMul :  ((x : bv16) (y : bv16)) → bv16
  requires !(x <= y);
func Bv16.SafeUNeg :  ((x : bv16)) → bv16
  requires !(!x);
func Bv32.SafeAdd :  ((x : bv32) (y : bv32)) → bv32
  requires !(x <= y);
func Bv32.SafeSub :  ((x : bv32) (y : bv32)) → bv32
  requires !(x <= y);
func Bv32.SafeMul :  ((x : bv32) (y : bv32)) → bv32
  requires !(x <= y);
func Bv32.SafeNeg :  ((x : bv32)) → bv32
  requires !(!x);
func Bv32.SafeUAdd :  ((x : bv32) (y : bv32)) → bv32
  requires !(x <= y);
func Bv32.SafeUSub :  ((x : bv32) (y : bv32)) → bv32
  requires !(x <= y);
func Bv32.SafeUMul :  ((x : bv32) (y : bv32)) → bv32
  requires !(x <= y);
func Bv32.SafeUNeg :  ((x : bv32)) → bv32
  requires !(!x);
func Bv64.SafeAdd :  ((x : bv64) (y : bv64)) → bv64
  requires !(x <= y);
func Bv64.SafeSub :  ((x : bv64) (y : bv64)) → bv64
  requires !(x <= y);
func Bv64.SafeMul :  ((x : bv64) (y : bv64)) → bv64
  requires !(x <= y);
func Bv64.SafeNeg :  ((x : bv64)) → bv64
  requires !(!x);
func Bv64.SafeUAdd :  ((x : bv64) (y : bv64)) → bv64
  requires !(x <= y);
func Bv64.SafeUSub :  ((x : bv64) (y : bv64)) → bv64
  requires !(x <= y);
func Bv64.SafeUMul :  ((x : bv64) (y : bv64)) → bv64
  requires !(x <= y);
func Bv64.SafeUNeg :  ((x : bv64)) → bv64
  requires !(!x);
func Bv1.SafeSDiv :  ((x : bv1) (y : bv1)) → bv1
  requires !(y == bv{1}(0))
  requires !(x <= y);
func Bv1.SafeSMod :  ((x : bv1) (y : bv1)) → bv1
  requires !(y == bv{1}(0))
  requires !(x <= y);
func Bv8.SafeSDiv :  ((x : bv8) (y : bv8)) → bv8
  requires !(y == bv{8}(0))
  requires !(x <= y);
func Bv8.SafeSMod :  ((x : bv8) (y : bv8)) → bv8
  requires !(y == bv{8}(0))
  requires !(x <= y);
func Bv16.SafeSDiv :  ((x : bv16) (y : bv16)) → bv16
  requires !(y == bv{16}(0))
  requires !(x <= y);
func Bv16.SafeSMod :  ((x : bv16) (y : bv16)) → bv16
  requires !(y == bv{16}(0))
  requires !(x <= y);
func Bv32.SafeSDiv :  ((x : bv32) (y : bv32)) → bv32
  requires !(y == bv{32}(0))
  requires !(x <= y);
func Bv32.SafeSMod :  ((x : bv32) (y : bv32)) → bv32
  requires !(y == bv{32}(0))
  requires !(x <= y);
func Bv64.SafeSDiv :  ((x : bv64) (y : bv64)) → bv64
  requires !(y == bv{64}(0))
  requires !(x <= y);
func Bv64.SafeSMod :  ((x : bv64) (y : bv64)) → bv64
  requires !(y == bv{64}(0))
  requires !(x <= y);


Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: ret_y_lt_0
Property: assert
Assumptions:
(0_lt_x, 0 < $__x0)
Proof Obligation:
-$__x0 < 0
-/
#guard_msgs in
#eval do let E := Env.init
         let (E, _stats) := eval E
              { header := {name := "P",
                           typeArgs := [],
                           inputs := [("x", mty[int])],
                           outputs := [("y", mty[int])] },
                spec := {
                    preconditions := [("0_lt_x", ⟨eb[((~Int.Lt #0) x)], .Default, #[]⟩)],
                    postconditions := [("ret_y_lt_0", ⟨eb[((~Int.Lt y) #0)], .Default, #[]⟩)] },
                body := [
                  Statement.set "y" eb[(~Int.Neg x)] .empty
                ]
              }
          return format E


end Tests

---------------------------------------------------------------------

section ConcreteInterpretation

/-! ## Concrete Interpretation Tests
-/

open Lambda Strata
open Std (ToFormat Format format)

private def parseAndTypeCheck (pgm : Strata.Program) : Except DiagnosticModel Core.Program := do
  let (cst, _errs) := TransM.run Inhabited.default (translateProgram pgm)
  Core.typeCheck { VerifyOptions.default with verbose := .quiet } cst

private def runProc (pgm : Strata.Program) (procName : String)
    (args : List Expression.Expr := [])
    (fuel : Nat := 10000) : IO Unit := do
  match parseAndTypeCheck pgm with
  | .error e => IO.println s!"type error: {e.message}"
  | .ok prog =>
    match prog.run with
    | .ok E =>
      let proc := Core.Program.Procedure.find? prog ⟨procName, ()⟩
      match proc with
      | none => IO.println "procedure not found"
      | some p =>
        let lhs := p.header.outputs.keys
        let E := Core.Statement.Command.runCall lhs procName args fuel E
        match E.error with
        | none =>
          let outputs := lhs.map fun name =>
            let val := (E.exprEnv.state.find? name).map (·.snd)
            s!"{name} = {val.map (fun v => toString (format v))}"
          IO.println (String.intercalate ", " outputs)
        | some e => IO.println f!"error: {e}"
    | .error diag => IO.println s!"error: {diag}"

-- Simple assignment
private def simplePgm : Strata.Program :=
#strata
program Core;
procedure Test(out y : int)
{
  y := 42;
};
#end

/-- info: y = (some 42) -/
#guard_msgs in
#eval runProc simplePgm "Test"

-- Arithmetic
private def arithPgm : Strata.Program :=
#strata
program Core;
procedure Test(x : int, out y : int)
{
  y := x + x;
};
#end

/-- info: y = (some 10) -/
#guard_msgs in
#eval runProc arithPgm "Test" [.intConst () 5]

-- If-then-else
private def itePgm : Strata.Program :=
#strata
program Core;
procedure Test(x : int, out y : int)
{
  if (x > 0) {
    y := x;
  } else {
    y := 0 - x;
  }
};
#end

/-- info: y = (some 7) -/
#guard_msgs in
#eval runProc itePgm "Test" [.intConst () 7]

/-- info: y = (some 3) -/
#guard_msgs in
#eval runProc itePgm "Test" [.intConst () (Int.negSucc 2)]

-- Procedure call
private def callPgm : Strata.Program :=
#strata
program Core;
procedure Double(n : int, out result : int)
{
  result := n + n;
};
procedure Test(x : int, out y : int)
{
  call Double(x, out y);
};
#end

/-- info: y = (some 20) -/
#guard_msgs in
#eval runProc callPgm "Test" [.intConst () 10]

-- Chained procedure calls (DoubleTwice)
private def chainedCallPgm : Strata.Program :=
#strata
program Core;
procedure Double(n : int, out result : int)
{
  result := n + n;
};
procedure Test(x : int, out output : int)
{
  call Double(x, out output);
  call Double(output, out output);
};
#end

/-- info: output = (some 20) -/
#guard_msgs in
#eval runProc chainedCallPgm "Test" [.intConst () 5]

-- Loop (sum of 0..n-1)
private def loopPgm : Strata.Program :=
#strata
program Core;
procedure Test(n : int, out sum : int)
{
  var i : int;
  sum := 0;
  i := 0;
  while (i < n)
  {
    sum := sum + i;
    i := i + 1;
  }
};
#end

/-- info: sum = (some 10) -/
#guard_msgs in
#eval runProc loopPgm "Test" [.intConst () 5]

-- Assertion success
private def assertSuccessPgm : Strata.Program :=
#strata
program Core;
procedure Test(out y : int)
{
  y := 42;
  assert [check]: (y == 42);
};
#end

/-- info: y = (some 42) -/
#guard_msgs in
#eval runProc assertSuccessPgm "Test"

-- Assertion failure
private def assertFailPgm : Strata.Program :=
#strata
program Core;
procedure Test(out y : int)
{
  y := 42;
  assert [check]: (y == 0);
};
#end

/-- info: error: [ASSERT ERROR] Assertion check failed!
false
-/
#guard_msgs in
#eval runProc assertFailPgm "Test"

-- Nested blocks with scoping
private def blockPgm : Strata.Program :=
#strata
program Core;
procedure Test(out y : int)
{
  y := 0;
  anon0: {
    var x : int;
    x := 10;
    y := x;
  }
};
#end

/-- info: y = (some 10) -/
#guard_msgs in
#eval runProc blockPgm "Test"

end ConcreteInterpretation

---------------------------------------------------------------------

end Core
