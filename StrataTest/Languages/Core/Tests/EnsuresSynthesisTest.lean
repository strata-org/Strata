/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Transform.EnsuresSynthesis

/-!
# Unit tests for the ensures-synthesis pass

These tests verify that:
1. A simple linear procedure (structured body, `set out := arith(a, b)`) gets a
   synthesised `free ensures (out == arith(a, b))`.
2. A procedure with a branch body does NOT get any synthesised ensures.
3. A procedure that already has a postcondition is left unchanged.
4. A procedure with a user call in the body is NOT synthesised.
-/

namespace Core
namespace EnsuresSynthesis.Test

open Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono

-- Helpers for building expressions
private def intTy : Lambda.LTy := .base .int
private def boolTy : Lambda.LTy := .base .bool

private def mkIdent (name : String) : CoreIdent := ⟨name, ()⟩

private def fv (name : String) : Expression.Expr :=
  Lambda.LExpr.fvar () ⟨name, ()⟩ none

private def opApp (op : String) (a b : Expression.Expr) : Expression.Expr :=
  Lambda.LExpr.app () (Lambda.LExpr.app () (Lambda.LExpr.op () ⟨op, ()⟩ none) a) b

/-- Build a minimal structured-body procedure:
    `add(a : int, b : int, out r : int) { r := a + b; }` -/
private def addProc : Procedure :=
  { header :=
      { name := ⟨"add", ()⟩
        typeArgs := []
        inputs  := [(⟨"a", ()⟩, intTy), (⟨"b", ()⟩, intTy)]
        outputs := [(⟨"r", ()⟩, intTy)] }
    spec := { preconditions := [], postconditions := [] }
    body := .structured [
      -- r := a + b  (using a hypothetical "add_int" op)
      Statement.set ⟨"r", ()⟩ (opApp "add_int" (fv "a") (fv "b")) .empty
    ] }

/-- Build a procedure with a branch body: synthesis should be skipped. -/
private def branchProc : Procedure :=
  { header :=
      { name := ⟨"branch", ()⟩
        typeArgs := []
        inputs  := [(⟨"x", ()⟩, intTy)]
        outputs := [(⟨"r", ()⟩, intTy)] }
    spec := { preconditions := [], postconditions := [] }
    body := .structured [
      Statement.ite
        (.det (Lambda.LExpr.fvar () ⟨"x", ()⟩ none))
        [Statement.set ⟨"r", ()⟩ (fv "x") .empty]
        [Statement.set ⟨"r", ()⟩ (Lambda.LExpr.const () (.intConst 0)) .empty]
        .empty
    ] }

/-- Build a procedure that already has a postcondition: synthesis should not add more. -/
private def annotatedProc : Procedure :=
  { header :=
      { name := ⟨"annotated", ()⟩
        typeArgs := []
        inputs  := [(⟨"a", ()⟩, intTy)]
        outputs := [(⟨"r", ()⟩, intTy)] }
    spec :=
      { preconditions := []
        postconditions := [(⟨"existing", ()⟩,
          { expr := Lambda.LExpr.eq () (fv "r") (fv "a"), attr := .Default })] }
    body := .structured [
      Statement.set ⟨"r", ()⟩ (fv "a") .empty
    ] }

/-- Build a procedure with a user call in the body: synthesis should be skipped. -/
private def callProc : Procedure :=
  { header :=
      { name := ⟨"callProc", ()⟩
        typeArgs := []
        inputs  := [(⟨"a", ()⟩, intTy)]
        outputs := [(⟨"r", ()⟩, intTy)] }
    spec := { preconditions := [], postconditions := [] }
    body := .structured [
      Statement.call "user_helper" [.inArg (fv "a"), .outArg ⟨"r", ()⟩] .empty
    ] }

-- ---------------------------------------------------------------
-- Test 1: linear add procedure should get a synthesised ensures
-- ---------------------------------------------------------------

/--
info: some
-/
#guard_msgs in
#eval do
  let result := synthesizeForProcedure addProc
  IO.println (match result with | some _ => "some" | none => "none")

/--
info: 1
-/
#guard_msgs in
#eval do
  match synthesizeForProcedure addProc with
  | none => IO.println "none"
  | some p => IO.println (toString p.spec.postconditions.size)

-- ---------------------------------------------------------------
-- Test 2: branch body should produce none
-- ---------------------------------------------------------------

/--
info: none
-/
#guard_msgs in
#eval do
  let result := synthesizeForProcedure branchProc
  IO.println (match result with | some _ => "some" | none => "none")

-- ---------------------------------------------------------------
-- Test 3: already-annotated procedure should produce none
-- ---------------------------------------------------------------

/--
info: none
-/
#guard_msgs in
#eval do
  let result := synthesizeForProcedure annotatedProc
  IO.println (match result with | some _ => "some" | none => "none")

-- ---------------------------------------------------------------
-- Test 4: procedure with user call should produce none
-- ---------------------------------------------------------------

/--
info: none
-/
#guard_msgs in
#eval do
  let result := synthesizeForProcedure callProc
  IO.println (match result with | some _ => "some" | none => "none")

-- ---------------------------------------------------------------
-- Test 5: synthesised ensures label has expected prefix
-- ---------------------------------------------------------------

/--
info: synthesized_ensures_r
-/
#guard_msgs in
#eval do
  match synthesizeForProcedure addProc with
  | none => IO.println "none"
  | some p =>
    match p.spec.postconditions.keys with
    | [] => IO.println "empty"
    | lbl :: _ => IO.println lbl

end EnsuresSynthesis.Test
end Core
