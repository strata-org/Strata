/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Ion
import Strata.DDM.BuiltinDialects.StrataDDL
import Strata.DDM.Integration.Lean

namespace Strata

open _root_.Ion (SymbolTable Ion SymbolId)

def testRoundTrip {α} [FromIon α] [BEq α] [Inhabited α] (toF : α → ByteArray) (init : α) : Bool :=
  let bs := toF init
  match FromIon.deserialize (α := α) bs with
  | .error msg => @panic _ ⟨false⟩ msg
  | .ok res  => res == init

def testDialectRoundTrip (d : Dialect) : Bool :=
  testRoundTrip Dialect.toIon d

#dialect
dialect Bool;
// Introduce Boolean type
type Bool;

// Introduce literals as constants.
fn true_lit : Bool => "true";
fn false_lit : Bool => "false";

// Introduce basic Boolean operations.
fn not_expr (tp : Type) : tp => tp;
fn and (a : Bool, b : Bool) : Bool => @[prec(10), leftassoc] a " && " b;
fn or (a : Bool, b : Bool) : Bool => @[prec(8), leftassoc] a " || " b;
fn imp (a : Bool, b : Bool) : Bool => @[prec(8), leftassoc] a " ==> " b;

// Introduce equality operations that work for arbitrary types.
// The type is inferred.
fn equal (tp : Type, a : tp, b : tp) : Bool => @[prec(15)] a " == " b;
fn not_equal (tp : Type, a : tp, b : tp) : Bool => @[prec(15)] a " != " b;
#end

#guard testDialectRoundTrip Bool

-- Test we can serialize/deserialize dialect
#guard testDialectRoundTrip initDialect
#guard testDialectRoundTrip StrataDDL
