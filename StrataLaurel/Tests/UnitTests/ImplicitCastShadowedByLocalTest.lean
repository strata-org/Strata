/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
A local variable named like an implicit procedure does not capture the cast.

Resolution inserts a call to the implicit procedure where a value of its input type fills a slot
of its output type, and binds the call's callee to the procedure. Variables and procedures live
in different namespaces, so a local `fromInt` in scope must not be what the cast call refers to.
Core refuses a local named like a function, so this cannot be checked end to end; it is checked
here, at resolution, by the kind of definition each inserted call is bound to.
-/

import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation.Resolution
import StrataLaurel.Implementation.MapStmtExpr

open Strata
open StrataTest.Util

namespace Strata.Laurel

private def calleesNamed (name : String) (proc : Procedure) : List Identifier :=
  match proc.body.implementation with
  | none => []
  | some impl =>
    foldStmtExpr (fun e acc =>
      match e.val with
      | .Call _ callee _ _ => if callee.text == name then acc ++ [callee] else acc
      | _ => acc) [] impl

private def report (src : String) : IO Unit := do
  let parsed ← (Strata.parseLaurelText "<implicit-cast-shadowed-test>" src : IO LaurelProgram)
  let resolved := resolve (withBuiltins parsed)
  for p in resolved.program.staticProcedures do
    for callee in calleesNamed "fromInt" p do
      let bound := callee.uniqueId.bind resolved.model.refToDef.get?
      let what := match bound with
        | some (.staticProcedure _) => "static procedure"
        | some node => s!"{repr node.kind}"
        | none => "unbound"
      IO.println s!"{p.name.text}: {callee.text} -> {what}"
  IO.println s!"errors: {resolved.errors.size}"
  for d in resolved.errors do
    IO.println s!"{d.kind}: {d.message}"

private def shadowed := r"
datatype Meters { MkMeters(m: int) }
procedure fromInt(x: int) : Meters implicit return MkMeters(x);
procedure use() opaque {
  var fromInt: int := 3;
  var d: Meters := 5;
  assert Meters..m!(d) == 5
};
"

/--
info: use: fromInt -> static procedure
errors: 0
-/
#guard_msgs in
#eval report shadowed

end Strata.Laurel
