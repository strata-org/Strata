/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Ion
import Strata.DDM.BuiltinDialects.StrataDDL

namespace Strata

open _root_.Ion (SymbolTable Ion SymbolId)

def runRoundTrip {α} [FromIon α] [BEq α] [Inhabited α] (toF : α → SymbolTable × Ion SymbolId) (init : α) : α  :=
  let (tbl, r) := toF init
  match @fromIon α _ r tbl with
  | .error s => panic! s!"Deserialize failed: {s}"
  | .ok d  => d

def testRoundTrip {α} [FromIon α] [BEq α] [Inhabited α] (toF : α → SymbolTable × Ion SymbolId) (v : α) : Bool :=
  runRoundTrip toF v == v

def testDialectRoundTrip (d : Dialect) : Bool :=
  runRoundTrip Dialect.toIon d == d

-- Test we can serialize/deserialize dialect
#guard testDialectRoundTrip initDialect
#guard testDialectRoundTrip StrataDDL
