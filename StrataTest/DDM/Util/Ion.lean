/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DDM.Util.ByteArray
meta import Strata.DDM.Util.Ion
import Strata.DDM.Util.Ion

open Ion
open Strata

def example2 : Ion String := .struct #[
  ("foo", .null .null),
  ("bar", .bool true),
  ("baz", .list #[.int 1, .int 2, .int 3])
]

def example2_enc := Ion.internAndSerialize [example2]

#guard example2_enc.asHex = "e00100eaee958183de9186710387bc83666f6f836261728362617adc8a0f8b118cb6210121022103"

def runRoundtrip (v : List (Ion SymbolId)) : Array (Ion SymbolId) :=
 match Ion.deserialize (Ion.serialize v.toArray) with
 | .error (off, msg) => panic! s!"Error at {off}: {msg}"
 | .ok r => r.flatten

def testRoundtrip (v : List (Ion SymbolId)) : Bool :=
 match Ion.deserialize (Ion.serialize v.toArray) with
 | .error _ => false
 | .ok r => r.flatten == v.toArray

#guard testRoundtrip [.bool false, .bool true]
#guard testRoundtrip [.int 0, .int 1, .int (-1), .int 256, .int (-256)]
#guard testRoundtrip [.float 1e-3, .float 3]
#guard testRoundtrip [.decimal ⟨0, 0⟩]
#guard testRoundtrip [.decimal ⟨0, 1⟩]
#guard testRoundtrip [.decimal ⟨0, -1⟩]
#guard testRoundtrip [.decimal ⟨0,  65⟩]
#guard (serialize #[.decimal ⟨0, 256⟩]).asHex = "e00100ea520280"
#guard (serialize #[.decimal ⟨0, -256⟩]).asHex = "e00100ea524280"
#guard testRoundtrip [.decimal ⟨0,  256⟩]
#guard testRoundtrip [.decimal ⟨0, -256⟩]
#guard testRoundtrip [.decimal ⟨258, 0⟩]
#guard testRoundtrip [.decimal ⟨-258, 0⟩]
#guard testRoundtrip [.decimal ⟨1, 3⟩]

#guard testRoundtrip [.symbol (.mk 0), .symbol (.mk 1)]

#guard testRoundtrip [.string "", .string "⟨"]
#guard testRoundtrip [.string "this_is_a_long_name"]

#guard testRoundtrip [.blob <| Strata.ByteArray.zeros 20000]
#guard testRoundtrip [.list #[], .list #[.int 1]]
#guard testRoundtrip [.list (Array.ofFn (n := 8000) fun i => .int i.val)]
#guard testRoundtrip [.sexp #[], .sexp #[.int 1]]
#guard testRoundtrip [.struct #[], .struct #[(.mk 1, .int 1)]]
#guard testRoundtrip [.annotation #[.mk 1] (.int 1)]

#guard testRoundtrip <| intern [example2] |>.toList

-- Issue #1228: NOP pad in struct must not shift subsequent field-key indices
-- Input: struct with fields (key=1, int 1), NOP pad, (key=2, int 2)
private def nopPadInStruct : ByteArray :=
  ⟨#[0xE0, 0x01, 0x00, 0xEA, 0xD8, 0x81, 0x21, 0x01, 0x80, 0x00, 0x82, 0x21, 0x02]⟩

#guard
  match Ion.deserialize nopPadInStruct with
  | .ok #[#[.mk (.struct fields)]] =>
    fields == #[(.mk 1, .int 1), (.mk 2, .int 2)]
  | _ => false

-- Issue #1228: NOP pad at start of struct
-- Input: struct with NOP pad, then field (key=1, int 1)
private def nopPadAtStartOfStruct : ByteArray :=
  ⟨#[0xE0, 0x01, 0x00, 0xEA, 0xD5, 0x80, 0x00, 0x81, 0x21, 0x01]⟩

#guard
  match Ion.deserialize nopPadAtStartOfStruct with
  | .ok #[#[.mk (.struct fields)]] =>
    fields == #[(.mk 1, .int 1)]
  | _ => false
