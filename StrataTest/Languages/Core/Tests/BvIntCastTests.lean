/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.SMTEncoder
import Strata.Languages.Core.Verifier

/-!
Tests for the three Bv↔Int cast operators, exercised all the way through
the SMT pipeline via the encoder API.

- `Bv{n}.ToUInt` ≙ SMT-LIB 2.7 `ubv_to_int`
- `Bv{n}.ToInt`  ≙ SMT-LIB 2.7 `sbv_to_int`
- `Int.ToBv{n}`  ≙ SMT-LIB 2.7 `(_ int_to_bv n)`
-/

namespace Core
open Lambda
open Strata.SMT

private abbrev m := ExprSourceLoc.synthesized "test"

private def coreEnv : Env := {Env.init with exprEnv := {
  Env.init.exprEnv with
    config := { Env.init.exprEnv.config with factory := Core.Factory }}}

/-! ## Bv8.ToUInt — unsigned bitvector → Int (ubv_to_int) -/

/--
info: "; x\n(declare-const x (_ BitVec 8))\n(assert (ubv_to_int x))\n"
-/
#guard_msgs in
#eval toSMTCommandsWithAssert
  (.app m (.op m ⟨"Bv8.ToUInt", ()⟩ (.some (.arrow (.bitvec 8) .int))) (.fvar m "x" (.some (.bitvec 8))))
  (E := coreEnv)

/-! ## Bv8.ToInt — signed bitvector → Int (sbv_to_int) -/

/--
info: "; x\n(declare-const x (_ BitVec 8))\n(assert (sbv_to_int x))\n"
-/
#guard_msgs in
#eval toSMTCommandsWithAssert
  (.app m (.op m ⟨"Bv8.ToInt", ()⟩ (.some (.arrow (.bitvec 8) .int))) (.fvar m "x" (.some (.bitvec 8))))
  (E := coreEnv)

/-! ## Int.ToBv8 — Int → bitvector (int_to_bv 8) -/

/--
info: "; x\n(declare-const x Int)\n(assert ((_ int_to_bv 8) x))\n"
-/
#guard_msgs in
#eval toSMTCommandsWithAssert
  (.app m (.op m ⟨"Int.ToBv8", ()⟩ (.some (.arrow .int (.bitvec 8)))) (.fvar m "x" (.some .int)))
  (E := coreEnv)

end Core
