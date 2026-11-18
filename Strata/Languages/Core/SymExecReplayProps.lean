/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.SymExecReplay
import all Strata.Languages.Core.SymExecReplay

/-! # Properties of replay (`Core.SymExecReplay`)

Key theorem: `oracleFor_syms`.
-/

namespace Core.SymExec

public section

/-- A record with no merges is replayed as the plain list of its symbols' values. -/
theorem oracleFor_syms (pick : Expression.Expr → Option Bool)
    (val : Expression.Expr → Option Expression.Expr) :
    ∀ xs : List Expression.Expr, oracleFor pick val (xs.map .sym) = xs.mapM val
  | [] => by simp [oracleFor]
  | x :: xs => by simp [oracleFor, List.mapM_cons, oracleFor_syms pick val xs]

end

end Core.SymExec
