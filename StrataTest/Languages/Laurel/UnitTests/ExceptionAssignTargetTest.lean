/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

/-
The exception checks in `resolve` see a throwing call in an assignment *target*,
not only in the assigned value.

`Variable.Field` carries an arbitrary object expression, so `mk()#x := 1` is a
representable assignment whose callee can throw. All three checks must therefore
descend into the target's object expression, not only into the assigned value: the
escape check (`validateExceptionEscapes`), the "not yet lowerable position" guard
(`validateExceptionLowerability`), and the least-common-ancestor collection for a
`catch` binding. A check that missed the target would accept a procedure declaring
no `throws`, and leave the call unlowered.

This is a unit test rather than an end-to-end one because the shape cannot be
written in Laurel source today: a field access whose object is a call does not
resolve at all (`mkPlain()#x := 1` reports *'x' is not defined* with no exception
anywhere in the program), so a source-level test would pin that unrelated
limitation instead. Front ends build Laurel ASTs directly, which is the path that
reaches this shape, so the program below is built the same way.

The unrelated field-resolution error is reported separately below rather than
filtered silently, so this test cannot start passing for the wrong reason.
-/

meta import Strata.Languages.Laurel.Resolution

meta section

open Strata
open Strata.Laurel

private def mkTy (ty : HighType) : HighTypeMd := { val := ty, source := .unknown }

private def nn (e : StmtExpr) : StmtExprMd := ⟨e, .unknown⟩

/-- `composite Obj { var x: int }` plus `composite MyError {}`. -/
private def objType : TypeDefinition :=
  .Composite { name := mkId "Obj"
               fields := [{ name := mkId "x", isMutable := true, type := mkTy .TInt }]
               extending := []
               instanceProcedures := [] }

private def errType : TypeDefinition :=
  .Composite { name := mkId "MyError", fields := [], extending := [], instanceProcedures := [] }

/-- `procedure mk() returns (o: Obj) throws (e: MyError) opaque;` (bodiless, so it has
    no escape of its own to report). -/
private def mkProc : Procedure :=
  { name := mkId "mk"
    inputs := []
    outputs := [{ name := mkId "o", type := mkTy (.UserDefined (mkId "Obj")) }]
    preconditions := []
    decreases := none
    throwsType := some (mkTy (.UserDefined (mkId "MyError")))
    body := .Opaque [] none [] }

/-- `procedure writesThroughTarget() { mk()#x := 1 }` — no `throws` clause, and the
    only call sits in the assignment target. -/
private def writerProc : Procedure :=
  { name := mkId "writesThroughTarget"
    inputs := []
    outputs := []
    preconditions := []
    decreases := none
    body := .Transparent (nn (.Assign
      [⟨.Field (nn (.StaticCall (mkId "mk") [])) (mkId "x"), .unknown⟩]
      (nn (.LiteralInt 1)))) }

private def program : Program :=
  { staticProcedures := [mkProc, writerProc], staticFields := [], types := [objType, errType] }

private def mentions (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- A diagnostic raised by one of the exception checks, as opposed to the unrelated
    field-resolution failure this shape also triggers. -/
private def isExceptionDiag (d : Strata.Message) : Bool :=
  mentions d.message "escape" || mentions d.message "`throws`"
    || mentions d.message "not yet supported in this expression position"

/--
info: exception diagnostics:
  procedure 'writesThroughTarget' may let an exception of type 'MyError' escape; catch it with a `try`/`catch` or declare a `throws` clause
  a call to a procedure that `throws` is not yet supported in this expression position; bind it to a variable first (e.g. `var t := f(); … t …`)
other diagnostics: 0
-/
-- NOTE: `other diagnostics` is 0: `resolveFieldRef` resolves a field access through
-- a CALL RESULT (`mk()#x`) against the call's return type (`Obj`), so field `x` resolves
-- cleanly with no spurious "not defined" field-resolution errors. Only the exception
-- diagnostics (the point of this test) are raised.
#guard_msgs in
#eval do
  let result := resolve program
  IO.println "exception diagnostics:"
  for d in result.errors do
    if isExceptionDiag d then IO.println s!"  {d.message}"
  let others := result.errors.filter (fun d => !isExceptionDiag d)
  IO.println s!"other diagnostics: {others.size}"

end
