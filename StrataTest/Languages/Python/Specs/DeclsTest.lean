/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Python.Specs.Decls

open Strata
open Strata.Python
open Strata.Python.Specs

namespace DeclsTest

-- unionArray deduplicates
#guard (SpecType.unionArray default
    #[SpecType.intLiteral ⟨0, 0⟩ 0, SpecType.intLiteral ⟨0, 0⟩ 0]).intLits.size == 1

/-! ## `SpecType.mapIdentNames`

The rewrite traverses every nested `SpecType` reachable via
`SpecIdent.args` and `SpecTypedDict.fieldTypes`, and re-sorts the
`idents`/`typedDicts` arrays so ordering invariants survive rewrites
that change the ordering key. -/

private def ll : SourceRange := SourceRange.none

private def bareInner : PythonIdent := { pythonModule := "", name := "Inner" }

/-- Rewrite bare `Inner` (empty module) to `Outer.Inner`. -/
private def qualifyInner (id : PythonIdent) : PythonIdent :=
  if id.pythonModule.isEmpty && id.name == "Inner" then
    { pythonModule := "Outer", name := "Inner" }
  else id

-- Top-level bare ident is rewritten.
/-- info: Outer.Inner -/
#guard_msgs in
#eval IO.println
  (SpecType.ident ll bareInner |>.mapIdentNames qualifyInner |>.toString)

-- Generic arg: `List[Inner]`. The rewrite must reach inside `SpecIdent.args`.
/-- info: typing.List[Outer.Inner] -/
#guard_msgs in
#eval IO.println <|
  (SpecType.ident ll { pythonModule := "typing", name := "List" }
      #[SpecType.ident ll bareInner]
   |>.mapIdentNames qualifyInner).toString

-- Dict args: `Dict[str, Inner]` — rewrite reaches each arg.
/-- info: typing.Dict[builtins.str, Outer.Inner] -/
#guard_msgs in
#eval IO.println <|
  (SpecType.ident ll { pythonModule := "typing", name := "Dict" }
      #[SpecType.ident ll { pythonModule := "builtins", name := "str" },
        SpecType.ident ll bareInner]
   |>.mapIdentNames qualifyInner).toString

-- Union atom: `Union[None, Inner]`. After rewriting, `Outer.Inner` sorts
-- ahead of `_types.NoneType` because `'O' (0x4f) < '_' (0x5f)`.
/-- info: Union[Outer.Inner, _types.NoneType] -/
#guard_msgs in
#eval IO.println <|
  (SpecType.unionArray ll
      #[SpecType.noneType ll, SpecType.ident ll bareInner]
   |>.mapIdentNames qualifyInner).toString

-- TypedDict field type: `TypedDict(f : Inner)`. The rewrite must reach
-- `SpecTypedDict.fieldTypes`.
/-- info: TypedDict(f : Outer.Inner) -/
#guard_msgs in
#eval IO.println <|
  (SpecType.typedDict ll #["f"] #[SpecType.ident ll bareInner] #[true]
   |>.mapIdentNames qualifyInner).toString

-- Nested generic: `List[TypedDict(f : Inner)]` — exercises both paths.
/-- info: typing.List[TypedDict(f : Outer.Inner)] -/
#guard_msgs in
#eval IO.println <|
  (SpecType.ident ll { pythonModule := "typing", name := "List" }
      #[SpecType.typedDict ll #["f"] #[SpecType.ident ll bareInner] #[true]]
   |>.mapIdentNames qualifyInner).toString

-- Sort restoration: rewriting an ident's `pythonModule` can change its
-- position under `PythonIdent` ordering. The result must stay sorted so
-- the "idents sorted by PythonIdent ordering" invariant (`Decls.lean`)
-- holds. Before: `[a.Alpha, b.Beta]`. Rewrite `b.Beta → a.Beta`; a naive
-- in-place map would leave them in original order — and since
-- `SpecType.toString` walks `idents` as stored, the printed order
-- exposes whether the sort was restored.
/-- info: Union[a.Alpha, a.Beta] -/
#guard_msgs in
#eval IO.println <|
  (SpecType.unionArray ll
      #[SpecType.ident ll { pythonModule := "a", name := "Alpha" },
        SpecType.ident ll { pythonModule := "b", name := "Beta" }]
   |>.mapIdentNames (fun id =>
      if id.pythonModule == "b" && id.name == "Beta" then
        { pythonModule := "a", name := "Beta" }
      else id)).toString

end DeclsTest
