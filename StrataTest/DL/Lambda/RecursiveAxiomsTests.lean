/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.RecursiveAxioms
import Strata.DL.Lambda.Lambda
import Strata.DL.Lambda.IntBoolFactory

/-!
## Tests for genRecursiveAxioms
-/

namespace Lambda

open Std (ToFormat Format format)
open LExpr LTy.Syntax LExpr.SyntaxMono

private abbrev TP : LExprParams := ⟨Unit, Unit⟩

private instance : Coe String TP.Identifier where
  coe s := Identifier.mk s ()

private def intListTy : LDatatype Unit :=
  { name := "IntList", typeArgs := [],
    constrs := [
      { name := "Nil", args := [], testerName := "isNil" },
      { name := "Cons",
        args := [("hd", .int), ("tl", .tcons "IntList" [])],
        testerName := "isCons" }
    ], constrs_ne := rfl }

private def listLenBody : LExpr TP.mono :=
  let xs : LExpr TP.mono := LExpr.fvar () ("xs" : TP.Identifier) .none
  let isNil_xs := LExpr.app () (LExpr.op () ("isNil" : TP.Identifier) .none) xs
  let tl_xs := LExpr.app () (LExpr.op () ("IntList..tl" : TP.Identifier) .none) xs
  let listLen_tl := LExpr.app () (LExpr.op () ("listLen" : TP.Identifier) .none) tl_xs
  let one_plus := LExpr.app () (LExpr.app () (LExpr.op () ("Int.Add" : TP.Identifier) .none) (LExpr.intConst () 1)) listLen_tl
  LExpr.ite () isNil_xs (LExpr.intConst () 0) one_plus

private def listLenFunc : LFunc TP :=
  { name := "listLen",
    isRecursive := true,
    recParam := some 0,
    inputs := [("xs", .tcons "IntList" [])],
    output := mty[int],
    body := some listLenBody,
    attr := #[.inlineIfConstr 0] }

private def tf : @TypeFactory Unit := #[[intListTy]]

private def peFactory : @Factory TP := (@IntBoolFactory TP _ _) |>.push listLenFunc
private def peState : LState TP :=
  let C := LContext.default.addFactoryFunctions peFactory
  match C.addTypeFactory tf with
  | .error _ => panic "failed to add type factory"
  | .ok C =>
    match LState.addFactory LState.init C.functions with
    | .error _ => panic "failed to add factory"
    | .ok s => s
private def pe (e : LExpr TP.mono) : LExpr TP.mono := e.eval 100 peState

private def listLenAxioms := genRecursiveAxioms listLenFunc tf pe

-- Nil axiom: ground equation, no quantifier
/-- info: (((~listLen : (arrow IntList int)) ~Nil) == #0) -/
#guard_msgs in
#eval do
  match listLenAxioms with
  | .error e => return format e
  | .ok axs => return format axs[0]!

-- Cons axiom: ∀ hd:int, tl:IntList with trigger on listLen(Cons(hd, tl))
/-- info: (∀ (∀ (((~listLen : (arrow IntList int)) (~Cons %1 %0)) == (~Int.Add #1 (~listLen %0))))) -/
#guard_msgs in
#eval do
  match listLenAxioms with
  | .error e => return format e
  | .ok axs => return format axs[1]!

-- Cons axiom trigger: innermost quantifier has trigger = LHS (listLen(Cons(%1,%0)))
private def extractInnerTrigger : LExpr TP.mono → Option (LExpr TP.mono)
  | .quant _ _ _ _ (.quant _ _ _ tr _) => some tr
  | _ => none

/-- info: ((~listLen : (arrow IntList int)) (~Cons %1 %0)) -/
#guard_msgs in
#eval do
  match listLenAxioms with
  | .error e => return format e
  | .ok axs => return format (extractInnerTrigger axs[1]!).get!

/-! ### lookup: recursion on second parameter -/

-- lookup(key: int, xs: IntList) : bool
--   if isNil(xs) then false
--   else if hd(xs) == key then true
--   else lookup(key, tl(xs))
private def lookupBody : LExpr TP.mono :=
  let key : LExpr TP.mono := LExpr.fvar () ("key" : TP.Identifier) .none
  let xs : LExpr TP.mono := LExpr.fvar () ("xs" : TP.Identifier) .none
  let isNil_xs := LExpr.app () (LExpr.op () ("isNil" : TP.Identifier) .none) xs
  let hd_xs := LExpr.app () (LExpr.op () ("IntList..hd" : TP.Identifier) .none) xs
  let tl_xs := LExpr.app () (LExpr.op () ("IntList..tl" : TP.Identifier) .none) xs
  let hd_eq_key := LExpr.eq () hd_xs key
  let rec_call := LExpr.app () (LExpr.app () (LExpr.op () ("lookup" : TP.Identifier) .none) key) tl_xs
  LExpr.ite () isNil_xs (LExpr.boolConst () false)
    (LExpr.ite () hd_eq_key (LExpr.boolConst () true) rec_call)

private def lookupFunc : LFunc TP :=
  { name := "lookup",
    isRecursive := true,
    recParam := some 1,
    inputs := [("key", .int), ("xs", .tcons "IntList" [])],
    output := mty[bool],
    body := some lookupBody,
    attr := #[.inlineIfConstr 1] }

private def peFactory2 : @Factory TP := (@IntBoolFactory TP _ _) |>.push listLenFunc |>.push lookupFunc
private def peState2 : LState TP :=
  let C := LContext.default.addFactoryFunctions peFactory2
  match C.addTypeFactory tf with
  | .error _ => panic "failed to add type factory"
  | .ok C =>
    match LState.addFactory LState.init C.functions with
    | .error _ => panic "failed to add factory"
    | .ok s => s
private def pe2 (e : LExpr TP.mono) : LExpr TP.mono := e.eval 100 peState2

-- Check that IntList..tl(Cons(%1,%0)) reduces
private def testDestrReduce : LExpr TP.mono :=
  let cons := LExpr.app () (LExpr.app () (LExpr.op () ("Cons" : TP.Identifier) .none) (.bvar () 1)) (.bvar () 0)
  LExpr.app () (LExpr.op () ("IntList..tl" : TP.Identifier) .none) cons

/-- info: %0 -/
#guard_msgs in
#eval format (pe2 testDestrReduce)

private def lookupAxioms := genRecursiveAxioms lookupFunc tf pe2

-- Nil axiom: ∀ key:int. lookup(key, Nil) = false
/--
info: (∀ (((~lookup : (arrow int (arrow IntList bool))) %0 ~Nil) == #false))
-/
#guard_msgs in
#eval do
  match lookupAxioms with
  | .error e => return format e
  | .ok axs => return format axs[0]!

-- Cons axiom: ∀ key:int, hd:int, tl:IntList. lookup(key, Cons(hd,tl)) = ...
/--
info: (∀ (∀ (∀ (((~lookup : (arrow int (arrow IntList bool)))
     %2
     (~Cons %1 %0)) == (if (%1 == %2) then #true else (~lookup %2 %0))))))
-/
#guard_msgs in
#eval do
  match lookupAxioms with
  | .error e => return format e
  | .ok axs => return format axs[1]!

-- Cons axiom trigger: innermost quantifier trigger = lookup(key, Cons(hd, tl))
private def extractInnerTrigger3 : LExpr TP.mono → Option (LExpr TP.mono)
  | .quant _ _ _ _ (.quant _ _ _ _ (.quant _ _ _ tr _)) => some tr
  | _ => none

/--
info: ((~lookup : (arrow int (arrow IntList bool))) %2 (~Cons %1 %0))
-/
#guard_msgs in
#eval do
  match lookupAxioms with
  | .error e => return format e
  | .ok axs => return format (extractInnerTrigger3 axs[1]!).get!

/-! ### replace: args before and after the recursive parameter -/

-- replace(key: int, xs: IntList, val: int) : IntList
--   if isNil(xs) then Nil
--   else if hd(xs) == key then Cons(val, tl(xs))
--   else Cons(hd(xs), replace(key, tl(xs), val))
private def replaceBody : LExpr TP.mono :=
  let key : LExpr TP.mono := .fvar () ("key" : TP.Identifier) .none
  let xs  : LExpr TP.mono := .fvar () ("xs" : TP.Identifier) .none
  let val : LExpr TP.mono := .fvar () ("val" : TP.Identifier) .none
  let isNil_xs := LExpr.app () (.op () ("isNil" : TP.Identifier) .none) xs
  let hd_xs := LExpr.app () (.op () ("IntList..hd" : TP.Identifier) .none) xs
  let tl_xs := LExpr.app () (.op () ("IntList..tl" : TP.Identifier) .none) xs
  let cons (a b : LExpr TP.mono) := LExpr.app () (LExpr.app () (.op () ("Cons" : TP.Identifier) .none) a) b
  let rec_call := LExpr.app () (LExpr.app () (LExpr.app () (.op () ("replace" : TP.Identifier) .none) key) tl_xs) val
  .ite () isNil_xs (.op () ("Nil" : TP.Identifier) .none)
    (.ite () (.eq () hd_xs key) (cons val tl_xs) (cons hd_xs rec_call))

private def replaceFunc : LFunc TP :=
  { name := "replace",
    isRecursive := true,
    recParam := some 1,
    inputs := [("key", .int), ("xs", .tcons "IntList" []), ("val", .int)],
    output := .tcons "IntList" [],
    body := some replaceBody,
    attr := #[.inlineIfConstr 1] }

private def peFactory3 : @Factory TP := peFactory2 |>.push replaceFunc
private def peState3 : LState TP :=
  let C := LContext.default.addFactoryFunctions peFactory3
  match C.addTypeFactory tf with
  | .error _ => panic "failed to add type factory"
  | .ok C =>
    match LState.addFactory LState.init C.functions with
    | .error _ => panic "failed to add factory"
    | .ok s => s
private def pe3 (e : LExpr TP.mono) : LExpr TP.mono := e.eval 100 peState3

private def replaceAxioms := genRecursiveAxioms replaceFunc tf pe3

-- Nil axiom: ∀ key:int, val:int. replace(key, Nil, val) = Nil
/--
info: (∀ (∀ (((~replace : (arrow int (arrow IntList (arrow int IntList)))) %1 ~Nil %0) == ~Nil)))
-/
#guard_msgs in
#eval do
  match replaceAxioms with
  | .error e => return format e
  | .ok axs => return format axs[0]!

-- Cons axiom: ∀ key:int, hd:int, tl:IntList, val:int. replace(key, Cons(hd,tl), val) = ...
/--
info: (∀ (∀ (∀ (∀ (((~replace : (arrow int (arrow IntList (arrow int IntList))))
      %3
      (~Cons %1 %0)
      %2) == (if (%1 == %3) then (~Cons %2 %0) else (~Cons %1 (~replace %3 %0 %2))))))))
-/
#guard_msgs in
#eval do
  match replaceAxioms with
  | .error e => return format e
  | .ok axs => return format axs[1]!

end Lambda
