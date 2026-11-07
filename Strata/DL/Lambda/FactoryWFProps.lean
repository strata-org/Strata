/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.FactoryWF

/-! ## Properties of well-formed factories

Key theorems: `LFuncWF.toSig` and `FactoryWF.toSig` (well-formed functions and
factories have well-formed type signatures). -/

namespace Lambda

public section

/-- A well-formed function has a well-formed type signature. -/
theorem LFuncWF.toSig {T : LExprParams} {f : LFunc T} (h : LFuncWF f) :
    LFuncSigWF f :=
  { typeArgs_nodup := h.typeArgs_nodup
    typeArgs_no_gen_prefix := h.typeArgs_no_gen_prefix
    inputs_typevars_in_typeArgs := h.inputs_typevars_in_typeArgs
    output_typevars_in_typeArgs := h.output_typevars_in_typeArgs }

/-- Every function of a well-formed factory has a well-formed type signature. -/
theorem FactoryWF.toSig {T} {fac : Factory T} (h : FactoryWF fac) :
    FactorySigWF fac :=
  { lfuncs_wf := fun lf hlf => (h.lfuncs_wf lf hlf).toSig }

end -- public section
end Lambda
