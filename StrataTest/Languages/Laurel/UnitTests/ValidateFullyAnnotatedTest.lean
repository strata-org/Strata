/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-
Tests for `validateFullyAnnotated`, the post-resolution check that every
`Declare` carries a type annotation. A surviving `none` annotation cannot be
produced from surface syntax (resolution always fills in `some`), so these
tests construct violating programs programmatically and call the validator
directly; the last test checks that resolution itself establishes the
invariant on an unannotated declaring assignment.
-/

meta import Strata.Languages.Laurel.Resolution

meta section

open Strata.Laurel

/-- Helper: an AST node with a placeholder source. -/
private def mk (e : StmtExpr) : StmtExprMd := { val := e, source := default }

/-- Helper: a static procedure with no inputs/outputs and a transparent body. -/
private def mkProc (name : String) (body : StmtExprMd)
    (preconditions : List Condition := []) : Procedure :=
  { name := mkId name, inputs := [], outputs := [], preconditions,
    decreases := none, body := .Transparent body }

private def mkProgram (procs : List Procedure) : Program :=
  { staticProcedures := procs, staticFields := [], types := [] }

/-- The exact diagnostic `validateFullyAnnotated` must emit for `name`. -/
private def expectedBug (name : String) : String :=
  s!"declaration of '{name}' left resolution without a type annotation; resolution rewrites every declaration to carry an explicit type"

-- ============================================================
-- 1. An unannotated standalone declaration is flagged, including
--    nested inside a branch (the walk recurses).
--    Pre-resolution shape of:
--      procedure p() { if true then { var x } };
--    (resolution would rewrite the `none` to `some Unknown` and emit a
--    user error, so post-resolution this tree only exists via a bug)
-- ============================================================

private def unannotatedVar : Program := mkProgram [
  mkProc "p" (mk (.IfThenElse (mk (.LiteralBool true))
    (mk (.Block [mk (.Var (.Declare { name := mkId "x", type := none }))] none))
    none))
]

#guard (validateFullyAnnotated unannotatedVar).map (·.message) == [expectedBug "x"]
#guard (validateFullyAnnotated unannotatedVar).all (·.type == .StrataBug)

-- ============================================================
-- 2. An unannotated `Declare` among the targets of a (multi-)assignment
--    is flagged; non-`Declare` co-targets are not.
--    Pre-resolution shape of:
--      procedure p() { assign a, var y := 1 };
-- ============================================================

private def unannotatedAssignTarget : Program := mkProgram [
  mkProc "p" (mk (.Assign
    [⟨.Local (mkId "a"), default⟩,
     ⟨.Declare { name := mkId "y", type := none }, default⟩]
    (mk (.LiteralInt 1))))
]

#guard (validateFullyAnnotated unannotatedAssignTarget).map (·.message) == [expectedBug "y"]
#guard (validateFullyAnnotated unannotatedAssignTarget).all (·.type == .StrataBug)

-- ============================================================
-- 3. Spec positions are covered: a declaration inside a precondition.
--    Pre-resolution shape of:
--      procedure p() requires (var z) { };
-- ============================================================

private def unannotatedInSpec : Program := mkProgram [
  mkProc "p" (mk (.Block [] none))
    (preconditions := [{ condition := mk (.Var (.Declare { name := mkId "z", type := none })) }])
]

#guard (validateFullyAnnotated unannotatedInSpec).map (·.message) == [expectedBug "z"]

-- ============================================================
-- 4. An unannotated `Declare` as an increment/decrement target is
--    flagged. No surface syntax produces this tree — the translator
--    rejects a declaration as a `++`/`--` target — so it only exists
--    via a bug; the validator covers the arm regardless.
-- ============================================================

private def unannotatedIncrDecr : Program := mkProgram [
  mkProc "p" (mk (.IncrDecr .Pre .Incr
    ⟨.Declare { name := mkId "x", type := none }, default⟩))
]

#guard (validateFullyAnnotated unannotatedIncrDecr).map (·.message) == [expectedBug "x"]
#guard (validateFullyAnnotated unannotatedIncrDecr).all (·.type == .StrataBug)

-- ============================================================
-- 5. An unannotated `Declare` as a compound-assignment target is
--    flagged. As with `IncrDecr`, the translator rejects a declaration
--    as an `op=` target, so this tree also only exists via a bug.
-- ============================================================

private def unannotatedCompoundAssign : Program := mkProgram [
  mkProc "p" (mk (.CompoundAssign .Add
    ⟨.Declare { name := mkId "y", type := none }, default⟩
    (mk (.LiteralInt 1))))
]

#guard (validateFullyAnnotated unannotatedCompoundAssign).map (·.message) == [expectedBug "y"]
#guard (validateFullyAnnotated unannotatedCompoundAssign).all (·.type == .StrataBug)

-- ============================================================
-- 6. Annotated declarations pass clean, in both positions.
--    The post-resolution shape of:
--      procedure p() { var x: int; var y: bool := true };
-- ============================================================

private def annotated : Program := mkProgram [
  mkProc "p" (mk (.Block [
    mk (.Var (.Declare { name := mkId "x", type := some ⟨.TInt, default⟩ })),
    mk (.Assign [⟨.Declare { name := mkId "y", type := some ⟨.TBool, default⟩ }, default⟩]
      (mk (.LiteralBool true)))
  ] none))
]

#guard (validateFullyAnnotated annotated).isEmpty

-- ============================================================
-- 7. Resolution establishes the invariant: an unannotated declaring
--    assignment goes in, the resolved program passes the validator
--    with no diagnostics of any kind.
--    Pre-resolution shape of:
--      procedure p() { var x := 5 };
--    (resolution infers `int` and rewrites to `var x: int := 5`)
-- ============================================================

private def inferProgram : Program := mkProgram [
  mkProc "p" (mk (.Block [
    mk (.Assign [⟨.Declare { name := mkId "x", type := none }, default⟩]
      (mk (.LiteralInt 5)))
  ] none))
]

#guard (validateFullyAnnotated (resolve inferProgram).program).isEmpty
#guard (resolve inferProgram).errors.isEmpty

end
