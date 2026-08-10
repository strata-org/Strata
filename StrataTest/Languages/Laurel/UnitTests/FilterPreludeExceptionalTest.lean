/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

/-
`filterPrelude` keeps a prelude declaration reachable from *any* part of a `throwsOn`
behavior case — its guard, its postconditions, or its frame — not just from `throws`.

The pass restricts the prelude to what a user program transitively references, so
a name it fails to collect is silently deleted and only resurfaces downstream as
an undefined reference. `filterPrelude` has no caller inside this package (front
ends consume it), which is why the exceptional contract needs pinning here: nothing
else in the repo walks this code.

The programs are built directly as ASTs rather than parsed, because the point is
which fields the collector walks — each prelude procedure below is referenced from
exactly one part of the case, so dropping any one of them from the collector deletes
exactly one procedure from the filtered prelude.
-/

meta import Strata.Languages.Laurel.FilterPrelude

meta section

open Strata.Laurel

private def mkTy (ty : HighType) : HighTypeMd := { val := ty, source := .unknown }

private def call (name : String) : StmtExprMd :=
  ⟨.StaticCall (mkId name) [], .unknown⟩

/-- A prelude procedure returning `int`, with a body so it is not `External`. -/
private def preludeProc (name : String) : Procedure :=
  { name := mkId name, inputs := [], outputs := [{ name := mkId "r", type := mkTy .TInt }],
    preconditions := [], decreases := none,
    body := .Transparent ⟨.Block [] none, .unknown⟩ }

/-- Four candidates; the user program below reaches the first three, each from a
    different part of a `throwsOn` case, and never mentions `unreachedByAnyClause`. -/
private def prelude : Program :=
  { staticProcedures := [
      preludeProc "reachedFromGuard",
      preludeProc "reachedFromEnsures",
      preludeProc "reachedFromModifies",
      preludeProc "unreachedByAnyClause"
    ]
    staticFields := []
    types := [] }

/-- One throwing procedure whose *only* references to the prelude sit inside a
    `throwsOn` behavior case: its guard, its postcondition, and its frame. -/
private def user : Program :=
  { staticProcedures := [
      { name := mkId "throwsAndFrames"
        inputs := []
        outputs := []
        preconditions := []
        decreases := none
        throwsType := some (mkTy (.UserDefined (mkId "Err")))
        throwsBinding := some (mkId "e")
        throwsOn := [
          { guard := call "reachedFromGuard"
            postconditions := [{ condition := call "reachedFromEnsures" }]
            modifies := [call "reachedFromModifies"] }
        ]
        body := .Transparent ⟨.Block [] none, .unknown⟩ }
    ]
    staticFields := []
    types := [] }

/-- info: kept: reachedFromGuard, reachedFromEnsures, reachedFromModifies -/
#guard_msgs in
#eval do
  match filterPrelude prelude user with
  | .error e => IO.println s!"unexpected error: {e}"
  | .ok filtered =>
    let names := filtered.staticProcedures.map (fun (p : Procedure) => p.name.text)
    IO.println s!"kept: {", ".intercalate names}"

end
