/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all Strata.Languages.Core.SMTEncoder
public import Strata.Languages.Core.SMTEncoder
public import Strata.Util.OrderedSetProps

/-!
# Coherence proofs for the SMT encoder `Context`

An `SMT.Context` looks up interpreted functions through `committedFn`, which uses
the O(1) key index of the `ifs` ordered set.

The proof `SMT.Context.committedFn_eq_any` relate that fast lookup to a direct
scan over the functions, provided the index is well-formed. -/

namespace Core
open Strata.SMT
open Strata.Util

/-- `committedFn`'s O(1) index lookup agrees with a linear scan over the
    interpreted functions, provided the `ifs` index is well-formed. -/
public theorem SMT.Context.committedFn_eq_any (ctx : SMT.Context) (uf : UF)
    (h : OrderedKeyedSetWF ctx.ifs) :
    ctx.committedFn uf
      = (ctx.ufs.contains uf || ctx.ifs.toArray.any (fun f => f.toUF == uf)) := by
  simp only [SMT.Context.committedFn, h.containsKey_eq_any]

end Core
