/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Ion
import Strata.DDM.Elab

namespace Strata

open _root_.Ion (SymbolTable Ion SymbolId)

def testRoundTrip {α} [FromIon α] [BEq α] [Inhabited α] (dialects : DialectMap) (toF : α → ByteArray) (init : α) : Bool :=
  let bs := toF init
  match FromIon.deserialize (α := α) dialects bs with
  | .error _ => false
  | .ok res  => res == init

def testDialectRoundTrip (d : Dialect) : Bool :=
  testRoundTrip Elab.LoadedDialects.builtin.dialects Dialect.toIon d

-- Test we can serialize/deserialize dialect
#guard testDialectRoundTrip initDialect
#guard testDialectRoundTrip StrataDDL
