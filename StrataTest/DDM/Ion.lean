/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Ion
import Strata.DDM.BuiltinDialects.StrataDD

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
#guard testDialectRoundTrip strataDialect


-- N.B. Run tests to print out the size of the Ion and JSON encoded messages.
/--
info: 2730
-/
#guard_msgs in #eval initDialect.toIonBinary |>.size

/--
info: 9212
-/
#guard_msgs in #eval initDialect.toIon |> fun (tbl, v) => v.unintern tbl |>.toJson |> toString |> String.length
