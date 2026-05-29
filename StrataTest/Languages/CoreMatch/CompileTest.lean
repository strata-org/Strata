/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.CoreMatch.CoreMatch
import Strata.Languages.CoreMatch.ToCore

/-!
Programmatic tests for `MProgram → Core.Program` lowering. Build
`MExpr` / `MStmt` values directly and assert on the resulting Core
shape: eliminator applications for expression-level matches, nested
ifs for statement-level matches, wildcard padding, arm reordering,
accessor calls in statement-arm prologues, and the unknown-datatype
and missing-arm fallbacks.
-/

open Strata.CoreMatch
open Lambda

namespace CoreMatchCompileTest


/-! Helper datatypes -/

private def color : LDatatype Unit :=
  { name := "Color", typeArgs := []
    constrs := [
      { name := ⟨"Red",   ()⟩, args := [] },
      { name := ⟨"Green", ()⟩, args := [] },
      { name := ⟨"Blue",  ()⟩, args := [] }],
    constrs_ne := by decide }

private def colorDecl : Core.Decl := .type (.data [color]) {}

private def list : LDatatype Unit :=
  { name := "List", typeArgs := []
    constrs := [
      { name := ⟨"Nil",  ()⟩, args := [] },
      { name := ⟨"Cons", ()⟩,
        args := [(⟨"hd", ()⟩, .int), (⟨"tl", ()⟩, .tcons "List" [])] }],
    constrs_ne := by decide }

private def listDecl : Core.Decl := .type (.data [list]) {}

private def cId : Core.Expression.Expr := .fvar () ⟨"c", ()⟩ (some (.tcons "Color" []))
private def xsId : Core.Expression.Expr := .fvar () ⟨"xs", ()⟩ (some (.tcons "List" []))


/-! AST inspection helpers -/

private partial def appHead : Core.Expression.Expr → Option String
  | .app _ f _ => appHead f
  | .op _ ⟨n, _⟩ _ => some n
  | _ => none

private partial def appArgCount : Core.Expression.Expr → Nat
  | .app _ f _ => appArgCount f + 1
  | _ => 0

private partial def appArgs : Core.Expression.Expr → List Core.Expression.Expr
  | .app _ f a => appArgs f ++ [a]
  | _ => []


/-! Expression match: head and arity -/

private def colorRank : MExpr :=
  .matchE (.core cId) "Color" [
    .ctor "Red" (.core (.intConst () 1)),
    .wild      (.core (.intConst () 0))]

private def lowered : Core.Expression.Expr :=
  Strata.CoreMatch.ToCore.compileMExpr [colorDecl] colorRank

#guard appHead lowered == some "Color$Elim"

-- `Color$Elim c <Red> <Green> <Blue>`: 4 args.
#guard appArgCount lowered == 4

-- The first arg after the eliminator is the scrutinee.
#guard match appArgs lowered with
       | scrut :: _ => scrut == cId
       | _ => false

-- The Red case is the explicit `1`; Green and Blue come from
-- wildcard expansion (also `0`, since the wildcard body is `0`).
#guard match appArgs lowered with
       | _ :: red :: green :: blue :: [] =>
         red == .intConst () 1
         && green == .intConst () 0
         && blue == .intConst () 0
       | _ => false


/-! Arm reordering

Cases must come out in the datatype's declaration order regardless of
the source order. -/

private def colorOutOfOrder : MExpr :=
  .matchE (.core cId) "Color" [
    .ctor "Blue"  (.core (.intConst () 3)),
    .ctor "Red"   (.core (.intConst () 1)),
    .ctor "Green" (.core (.intConst () 2))]

private def reordered : Core.Expression.Expr :=
  Strata.CoreMatch.ToCore.compileMExpr [colorDecl] colorOutOfOrder

-- After lowering, the case order must match `[Red, Green, Blue]`.
#guard match appArgs reordered with
       | _ :: red :: green :: blue :: [] =>
         red == .intConst () 1
         && green == .intConst () 2
         && blue == .intConst () 3
       | _ => false


/-! Wildcard padding

A wildcard arm for a constructor with arity > 0 must be wrapped in
λ-binders to match the ctor's arity. -/

private def listToInt : MExpr :=
  .matchE (.core xsId) "List" [
    .ctor "Nil" (.core (.intConst () 0)),
    .wild       (.core (.intConst () 1))]   -- covers Cons

private def loweredList : Core.Expression.Expr :=
  Strata.CoreMatch.ToCore.compileMExpr [listDecl] listToInt

#guard appHead loweredList == some "List$Elim"
#guard appArgCount loweredList == 3   -- scrut + Nil case + Cons case

-- Cons has arity 2; the wildcard expansion must wrap the body in
-- two `λ`s.
#guard match appArgs loweredList with
       | _ :: _nilCase :: consCase :: [] =>
         match consCase with
         | .abs _ _ _ (.abs _ _ _ (.intConst _ 1)) => true
         | _ => false
       | _ => false


/-! Statement match: nested-if compilation -/

private def colorStmt : MStmt :=
  .matchStmt cId "Color" [.ctor "Red" [], .ctor "Green" [], .wild []]

private def loweredStmt : List Core.Statement :=
  Strata.CoreMatch.ToCore.compileMStmt [colorDecl] colorStmt

-- Single statement — nested-if is a single ite at the top.
#guard loweredStmt.length == 1

#guard match loweredStmt with
       | [.ite _ _ _ _] => true
       | _ => false

-- The outer ite's condition is `Color..isRed(c)`.
#guard match loweredStmt with
       | [.ite (.det (.app _ (.op _ ⟨name, _⟩ _) _)) _ _ _] =>
         name == "Color..isRed"
       | _ => false


/-! Statement match: missing-arm fallback to assert false -/

-- Match without a wildcard and without an arm for `Blue`: lowering
-- emits `assert false` (`coreMatch_nonexhaustive`) for the gap.
private def colorIncomplete : MStmt :=
  .matchStmt cId "Color" [.ctor "Red" [], .ctor "Green" []]

private def loweredIncomplete : List Core.Statement :=
  Strata.CoreMatch.ToCore.compileMStmt [colorDecl] colorIncomplete

-- The Blue arm body is the assert-false fallback.  The exact shape
-- is one ite producing `Color$Elim` + `assert` for the missing case.
#guard loweredIncomplete.length == 1


/-! Unknown-datatype fallback

Lowering a match against a datatype not in the decl list emits a
distinctive sentinel rather than panicking — surfaces a clear error
downstream. -/

private def colorUnknown : MExpr :=
  .matchE (.core cId) "DoesNotExist" [.ctor "Foo" (.core (.intConst () 1))]

private def loweredUnknown : Core.Expression.Expr :=
  Strata.CoreMatch.ToCore.compileMExpr [] colorUnknown   -- empty decl list

-- The lowered expression is a fvar with a `__coreMatch_unknown_dt_*`
-- name — visible at typecheck time as an unbound symbol.
#guard match loweredUnknown with
       | .fvar _ ⟨n, _⟩ _ => n.startsWith "__coreMatch_unknown_dt_"
       | _ => false


/-! Missing-arm placeholder

`compileMExprWith` emits a `__coreMatch_missing_*` sentinel when a
constructor has no arm and no wildcard.  This should never reach
production (the arm-checker rejects it), but if it does, the verifier
fails loudly on an unbound symbol rather than silently producing
garbage. -/

-- Build a malformed MExpr that's missing the Cons arm and has no
-- wildcard.  Lowering should still complete and the placeholder
-- shows up where Cons would be.
private def badList : MExpr :=
  .matchE (.core xsId) "List" [.ctor "Nil" (.core (.intConst () 0))]

private def loweredBadList : Core.Expression.Expr :=
  Strata.CoreMatch.ToCore.compileMExpr [listDecl] badList

-- The Cons case slot should be the missing-arm placeholder.
#guard match appArgs loweredBadList with
       | _ :: _nilCase :: consCase :: [] =>
         match consCase with
         | .fvar _ ⟨n, _⟩ _ => n.startsWith "__coreMatch_missing_"
         | _ => false
       | _ => false


/-! `MStmts.ofCore` / `MStmt.ofCore` lifting helpers -/

#guard MStmt.ofCore (.assert "x" (LExpr.true ()) {}) matches .core _
#guard (MStmts.ofCore [.assert "a" (LExpr.true ()) {}, .assume "b" (LExpr.true ()) {}]).length == 2


end CoreMatchCompileTest
