/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Python.Specs.Decls

open Strata.Python.Specs

namespace DeclsTest

private abbrev mk1 (a : SpecAtomType) : SpecType := ⟨#[a], ⟨0, 0⟩⟩
private abbrev mk2 (a : SpecAtomType) : SpecType := ⟨#[a], ⟨⟨1⟩, ⟨2⟩⟩⟩

-- Atom ordering: ident < pyClass < intLiteral < stringLiteral < typedDict
#guard compare (SpecAtomType.ident .builtinsInt #[]) (.pyClass "Foo" #[]) == .lt
#guard compare (SpecAtomType.pyClass "Foo" #[]) (.intLiteral 0) == .lt
#guard compare (SpecAtomType.intLiteral 0) (.stringLiteral "a") == .lt

-- Same variant compares by fields
#guard compare (SpecAtomType.intLiteral 1) (.intLiteral 2) == .lt
#guard compare (SpecAtomType.intLiteral 1) (.intLiteral 1) == .eq
#guard compare (SpecAtomType.stringLiteral "a") (.stringLiteral "b") == .lt

-- ident compares by PythonIdent then args
#guard compare (SpecAtomType.ident .builtinsBool #[]) (.ident .builtinsInt #[]) == .lt

-- SpecType comparison ignores loc
#guard compare (mk1 (.intLiteral 1)) (mk2 (.intLiteral 1)) == .eq
-- BEq also ignores loc (consistent with Ord)
#guard mk1 (.intLiteral 1) == mk2 (.intLiteral 1)

-- SpecType compares by atoms content
#guard compare (mk1 (.intLiteral 1)) (mk1 (.intLiteral 2)) == .lt

-- ofArray deduplicates
#guard 1 == (SpecType.ofArray ⟨0, 0⟩ #[.intLiteral 0, .intLiteral 0] |>.atoms.size)

end DeclsTest
