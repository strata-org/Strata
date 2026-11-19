/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
No inference variable survives a resolution that reports nothing: each one is solved and written
back, or not recorded.
A pass that reads types before the next re-resolution would otherwise see a `?T.n`.
-/

import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation.Resolution
import StrataLaurel.Implementation.MapStmtExpr

open Strata
open StrataTest.Util

namespace Strata.Laurel

/-- Every type left mentioning an inference variable, by procedure. -/
private def report (src : String) : IO Unit := do
  let parsed ← (Strata.parseLaurelText "<inference-variable-leak-test>" src : IO LaurelProgram)
  let resolved := resolve (withBuiltins parsed)
  for p in resolved.program.staticProcedures do
    let (_, leaked) := (mapProcedureHighTypesM (m := StateM (List String)) (fun t => do
      if mentionsInferVar t.val then modify (· ++ [toString (formatHighTypeVal t.val)])
      pure t) p).run []
    unless leaked.isEmpty do IO.println s!"{p.name.text}: {", ".intercalate leaked}"

-- A constructor whose open `T` nothing reports: checked at the `Unknown` type of a target whose
-- declaration was already reported.
#guard_msgs in
#eval report r"
datatype Opt<T> { Som(v: T), Non() }
procedure atReportedType() opaque { var x: Undeclared; x := Non() };
"

-- Solved through a chain: `P := Opt<?T>`, then `?T := Opt<?T'>`, then `?T' := int`. Each solution
-- that mentions a variable solved later is rewritten, including one reached only through another.
#guard_msgs in
#eval report r"
datatype Opt<T> { Som(v: T), Non() }
datatype Pair<A, B> { MkPair(fst: A, snd: B) }
procedure same3<P>(a: Pair<P, int>, b: P, c: P) returns (r: P) opaque;
procedure p() opaque { var x := same3(MkPair(Non(), 1), Som(Non()), Som(Som(1))) };
"

-- The block is a nested root between `P := Opt<?V>` and `?V := int`: the outer root's solutions
-- and what mentions them survive it.
#guard_msgs in
#eval report r"
datatype Opt<T> { Som(v: T), Non() }
datatype Pair<A, B> { MkPair(fst: A, snd: B) }
procedure pairOpt<V>() returns (r: Pair<Opt<V>, int>) opaque;
procedure idp<T>(x: T) returns (r: T) opaque;
procedure same2<P>(a: Pair<P, int>, b: P) returns (r: P) opaque;
procedure p() opaque { var x := same2(pairOpt(), idp({ var t: int := 1; Som(t) })) };
"

/-- Every call that records a type argument mentioning `Unknown`, by procedure. -/
private def reportRecorded (src : String) : IO Unit := do
  let parsed ← (Strata.parseLaurelText "<inference-variable-leak-test>" src : IO LaurelProgram)
  let resolved := resolve (withBuiltins parsed)
  for p in resolved.program.staticProcedures do
    let (_, calls) := (foldProcedureExprsM (m := StateM (List String)) (fun e =>
      modify (· ++ foldStmtExpr (fun n acc => match n.val with
        | .Call _ callee _ tys => if tys.any (mentionsUnknown ·.val) then acc ++ [callee.text] else acc
        | _ => acc) [] e)) p).run []
    unless calls.isEmpty do IO.println s!"{p.name.text}: {", ".intercalate calls}"

-- Nor does a call record a type argument that is still `Unknown`, beside a hole.
#guard_msgs in
#eval reportRecorded r"
datatype Opt<T> { Som(v: T), Non() }
procedure g<T>(x: T) returns (r: T) opaque;
procedure p() opaque { var x := Som(<?>); var y: Opt<int> := Som(<?>); var z := g(<?>) };
"

end Strata.Laurel
