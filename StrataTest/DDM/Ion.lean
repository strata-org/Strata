/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Ion
import Strata.DDM.BuiltinDialects.StrataDDL
import Strata.DDM.Integration.Lean
import StrataTest.DDM.DeclareFn

namespace Strata

open _root_.Ion (SymbolTable Ion SymbolId)

def testRoundTrip {α} [FromIon α] [BEq α] [Inhabited α] (toF : α → ByteArray) (init : α) : Bool :=
  let bs := toF init
  match FromIon.deserialize (α := α) bs with
  | .error msg => @panic _ ⟨false⟩ msg
  | .ok res  => res == init

def testDialectRoundTrip (d : Dialect) : Bool :=
  testRoundTrip Dialect.toIon d

/-- Test that a `Program` can round-trip through Ion
serialization without losing commands. -/
private def testProgramRoundTrip (p : Program) : Bool :=
  let bs := p.toIon
  match Program.fromIon p.dialects p.dialect bs with
  | .error msg => @panic _ ⟨false⟩ msg
  | .ok res  => res.commands.size == p.commands.size

-- Load the actual Bool dialect from Examples
#load_dialect "../../Examples/dialects/Bool.dialect.st"

#guard testDialectRoundTrip Bool

-- Test we can serialize/deserialize dialect
#guard testDialectRoundTrip initDialect
#guard testDialectRoundTrip StrataDDL

-- Test we can serialize/deserialize programs with expressions
#guard testProgramRoundTrip testDeclareFnPgm
