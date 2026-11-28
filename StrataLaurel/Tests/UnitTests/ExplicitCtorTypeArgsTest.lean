/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Implementation
import StrataLaurel.Implementation.LaurelCompilationPipeline
import StrataLaurel.Implementation.MapStmtExpr

open Strata

namespace Strata.Laurel

/-
Explicit type arguments on a constructor call win over the type the call is expected to have.

Surface syntax cannot spell type arguments on a call, so a frontend supplies them. Here the
`Null` in the `then` branch is given `Dog` after parsing. The conditional is the receiver of a
field read or a method call whose member the parent composite `Animal` declares, so the receiver
is expected to be a `NullableRef<Animal>`, and the call must still be a `NullableRef<Dog>`.
-/

private def dogTy : HighTypeMd := ⟨.UserDefined (mkId "Dog"), .unknown⟩

private def explicitDog (e : StmtExprMd) : StmtExprMd :=
  match e.val with
  | .IfThenElse c ⟨.Call none callee [] [], src⟩ els =>
    if callee.text == "Null" then
      { e with val := .IfThenElse c ⟨.Call none callee [] [dogTy], src⟩ els }
    else e
  | _ => e

private def report (src : String) : IO Unit := do
  let p ← (Strata.parseLaurelText "<explicit-ctor-type-args-test>" src : IO LaurelProgram)
  let (core, diags) ← translate {} (mapLaurelProgramStmtExpr explicitDog p)
  IO.println s!"core produced: {core.isSome}"
  for d in diags do
    IO.println s!"{d.kind}: {d.message}"

private def fieldRead := r"
composite Animal { var legs: int }
composite Dog extends Animal { }
procedure g(a: NullableRef<Animal>) returns (r: int) opaque {
  var n: int := (if a == Null() then Null() else NonNull(NullableRef..value!(a) as Dog))#legs;
  return n
};
"

private def methodCall := r"
composite Animal {
  var legs: int
  procedure getLegs(self: Animal) returns (r: int) opaque { return self#legs };
}
composite Dog extends Animal { }
procedure g(a: NullableRef<Animal>) returns (r: int) opaque {
  var n: int := (if a == Null() then Null() else NonNull(NullableRef..value!(a) as Dog))#getLegs();
  return n
};
"

/-- info: core produced: true -/
#guard_msgs in
#eval report fieldRead

/-- info: core produced: true -/
#guard_msgs in
#eval report methodCall

end Strata.Laurel
