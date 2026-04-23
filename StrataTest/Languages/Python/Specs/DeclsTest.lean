/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Python.Specs.Decls
import Strata.Languages.Python.Specs.DDM

open Strata.Python.Specs
open Strata (SourceRange)

namespace DeclsTest

private abbrev mk1 (a : SpecAtomType) : SpecType := ⟨#[a], ⟨0, 0⟩⟩
private abbrev mk2 (a : SpecAtomType) : SpecType := ⟨#[a], ⟨⟨1⟩, ⟨2⟩⟩⟩

-- Atom ordering: ident < intLiteral < stringLiteral < typedDict
#guard compare (SpecAtomType.ident .builtinsInt #[]) (.intLiteral 0) == .lt
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

/-! ## toDDM / fromDDM round-trip for arithmetic SpecExpr variants -/

private def loc : SourceRange := SourceRange.none

-- Round-trip: toString (expr.toDDM.fromDDM) == toString expr
-- This exercises both toDDM and fromDDM.
private def roundTrip (e : SpecExpr) : Bool :=
  toString e.toDDM.fromDDM == toString e

#guard roundTrip (.intAdd (.var "x" loc) (.intLit 1 loc) loc)
#guard roundTrip (.intSub (.var "balance" loc) (.var "amount" loc) loc)
#guard roundTrip (.intMul (.intLit 2 loc) (.var "n" loc) loc)
#guard roundTrip (.intEq (.var "x" loc) (.intLit 0 loc) loc)
-- Nested: (x + 1) * y
#guard roundTrip (.intMul (.intAdd (.var "x" loc) (.intLit 1 loc) loc) (.var "y" loc) loc)

end DeclsTest
