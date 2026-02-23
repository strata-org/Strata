/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Statement

namespace Core

open Lambda Lambda.LTy.Syntax Core.Syntax
open Imperative (PureFunc)

section RenameLhsTests

/-! ## Tests for Statement.renameLhs on funcDecl -/

private def mkFunc (name : CoreIdent) : PureFunc Expression :=
  { name := name, inputs := [], output := t[int] }

-- renameLhs on funcDecl should match by name even when metadata differs.
-- The function has `glob` metadata, but `fr` has `locl` metadata — they share
-- the same name string "f", so the rename should succeed.
/-- info: true -/
#guard_msgs in
#eval
  let fr  : CoreIdent := ⟨"f", Visibility.locl⟩
  let to  : CoreIdent := ⟨"g", Visibility.locl⟩
  let decl := mkFunc ⟨"f", Visibility.glob⟩
  let s := Statement.renameLhs (.funcDecl decl) fr to
  match s with
  | .funcDecl decl' _ => decl'.name == to
  | _ => false

-- renameLhs on funcDecl should not rename when names differ.
/-- info: true -/
#guard_msgs in
#eval
  let fr  : CoreIdent := ⟨"h", Visibility.locl⟩
  let to  : CoreIdent := ⟨"g", Visibility.locl⟩
  let decl := mkFunc (CoreIdent.glob "f")
  let s := Statement.renameLhs (.funcDecl decl) fr to
  match s with
  | .funcDecl decl' _ => decl'.name == CoreIdent.glob "f"
  | _ => false

end RenameLhsTests

end Core
