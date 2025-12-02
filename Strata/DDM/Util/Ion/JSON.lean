/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Lean.Data.Json.Basic

import Strata.DDM.Util.Array
import Strata.DDM.Util.Ion.AST


namespace Strata.Decimal

def ofJsonNumber (n : Lean.JsonNumber) : Decimal where
  mantissa := n.mantissa
  exponent := n.exponent

def toJsonNumber (d : Decimal) : Lean.JsonNumber :=
  let m := d.mantissa
  let e := d.exponent
  if e > 0 then
    { mantissa := m * (10 ^ e.natAbs), exponent := 0 }
  else
    { mantissa := m, exponent := e.natAbs }

end Strata.Decimal

namespace Ion

namespace Ion

/--
Convert Value into a corresponding JSON object.

Note.  This function may loses some information as JSON
has fewer native types than Ion and so some information.

Specific changes include:
 - Type information in nulls is dropped (e.g., `.null .struct` becomes
   just `.null`.
 - Floating point numbers are converted to strings.  N.B.
 - Decimal numbers lose distinction between positive and negative zero.
 - Symbols become strings
 - Structs become objects and lose represented subfields (last is preserved).
 - Sexpressions become lists.
 - Annotations are discarded.
-/
def toJson : Ion String → Lean.Json
| .null _ => .null
| .bool b => .bool b
| .int i => .num <| .fromInt i
| .float f => .str (toString f)
| .decimal d => .num d.toJsonNumber
| .string s => .str s
| .symbol s => .str s
| .blob v => .arr <| v.data.map fun b => .num (.fromNat b.toNat)
| .struct a => .obj <| a.attach.foldl (init := {}) fun m ⟨(nm, v), _⟩ =>
  m.insert nm v.toJson
| .sexp l | .list l => .arr <| l.map (·.toJson)
| .annotation _ v => v.toJson
  termination_by t => t
  decreasing_by
    · rename_i p
      have q := Array.sizeOf_lt_of_mem p
      simp only [Prod.mk.sizeOf_spec] at q
      decreasing_tactic
    all_goals decreasing_tactic

/-- Constructs an ion value from a JSON object. -/
partial def ofJson : Lean.Json → Ion String
| .null => .null .null
| .bool b => .bool b
| .num n => .decimal <| .ofJsonNumber n
| .str s => .string s
| .obj m => .struct <| m.foldl (init := #[]) fun a nm v => a.push (nm, .ofJson v)
| .arr a => .list <| a.map fun v => .ofJson v

end Ion
