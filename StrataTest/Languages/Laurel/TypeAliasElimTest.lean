/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the type alias elimination pass correctly transforms
Laurel programs by comparing the output against expected results.

Since type aliases cannot be parsed from Laurel grammar text (they are
produced only by the Python frontend), these tests construct programs
programmatically and run resolve + typeAliasElim.
-/

import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.TypeAliasElim
import Strata.Languages.Laurel.Resolution

open Strata.Laurel

/-- Helper: construct a HighTypeMd with no source metadata. -/
private def mkTy (ty : HighType) : HighTypeMd := { val := ty, source := none }

/-- Helper: construct a minimal procedure. -/
private def mkProc (name : String) (inputs : List Parameter) (outputs : List Parameter)
    (body : Body := .Transparent ⟨.Block [] none, none⟩) : Procedure :=
  { name := mkId name, inputs, outputs, preconditions := [], decreases := none,
    isFunctional := false, body }

/-- Helper: run resolve + typeAliasElim on a program. -/
private def resolveAndElim (program : Program) : Program :=
  let result := resolve program
  typeAliasElim result.model result.program

private def printProcs (procs : List Procedure) : IO Unit :=
  procs.forM fun proc =>
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

-- ============================================================
-- 1. Chained aliases: A = int; B = A  →  both resolved to int
-- ============================================================

private def chainedProgram : Program :=
  { staticProcedures := [
      mkProc "test"
        [{ name := mkId "x", type := mkTy (.UserDefined (mkId "B")) }]
        [{ name := mkId "r", type := mkTy (.UserDefined (mkId "A")) }]
        (.Transparent ⟨.Return (some ⟨.Var (.Local (mkId "x")), none⟩), none⟩)
    ]
    staticFields := []
    types := [
      .Alias { name := mkId "A", target := mkTy .TInt },
      .Alias { name := mkId "B", target := mkTy (.UserDefined (mkId "A")) }
    ] }

/--
info: procedure test(x: int)
  returns (r: int)
return x;
-/
#guard_msgs in
#eval! do
  let result := resolveAndElim chainedProgram
  printProcs result.staticProcedures

-- Aliases are removed from types list
/--
info: 0
-/
#guard_msgs in
#eval! do
  let result := resolveAndElim chainedProgram
  IO.println (toString result.types.length)

-- ============================================================
-- 2. Cycle detection: A = B; B = A  →  terminates gracefully
-- ============================================================

private def cyclicProgram : Program :=
  { staticProcedures := [
      mkProc "test"
        [{ name := mkId "x", type := mkTy (.UserDefined (mkId "A")) }]
        []
    ]
    staticFields := []
    types := [
      .Alias { name := mkId "A", target := mkTy (.UserDefined (mkId "B")) },
      .Alias { name := mkId "B", target := mkTy (.UserDefined (mkId "A")) }
    ] }

-- The visited-set guard stops infinite resolution; we verify it terminates.
/--
info: 1
-/
#guard_msgs in
#eval! do
  let result := resolveAndElim cyclicProgram
  IO.println (toString result.staticProcedures.length)

-- ============================================================
-- 3. Aliases in procedure signatures (param + return types)
-- ============================================================

private def procSigProgram : Program :=
  { staticProcedures := [
      mkProc "compute"
        [{ name := mkId "a", type := mkTy (.UserDefined (mkId "MyInt")) },
         { name := mkId "b", type := mkTy (.UserDefined (mkId "MyBool")) }]
        [{ name := mkId "r", type := mkTy (.UserDefined (mkId "MyInt")) }]
        (.Transparent ⟨.Return (some ⟨.Var (.Local (mkId "a")), none⟩), none⟩)
    ]
    staticFields := []
    types := [
      .Alias { name := mkId "MyInt", target := mkTy .TInt },
      .Alias { name := mkId "MyBool", target := mkTy .TBool }
    ] }

/--
info: procedure compute(a: int, b: bool)
  returns (r: int)
return a;
-/
#guard_msgs in
#eval! do
  let result := resolveAndElim procSigProgram
  printProcs result.staticProcedures
