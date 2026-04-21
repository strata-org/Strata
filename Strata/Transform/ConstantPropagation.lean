/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.Expressions

namespace Strata

/-! ## Constant Propagation

A Core-to-Core transform that propagates literal and `from_str(literal)`
assignments through straight-line code. Conservative at control-flow
joins: kills propagated values at loops, propagates into branches.
-/

public section

/-- Check whether an expression is a small ground value suitable for propagation. -/
private def isSmallGroundValue : Lambda.LExpr Core.CoreLParams.mono → Bool
  | .const .. => true
  | .app _ (.op _ name _) (.const _ (.strConst _)) => name.1 == "from_str"
  | _ => false

/-- Propagate constant assignments through straight-line Core statements.
    For each `init x := e` or `set x := e` where `e` is a ground value,
    substitute `x → e` in subsequent statements. Kills propagated values
    on `havoc` and at control-flow joins (ite/loop bodies). -/
def propagateConstants (stmts : List Core.Statement) : List Core.Statement :=
  let substExpr (env : List (Core.CoreIdent × Lambda.LExpr Core.CoreLParams.mono))
      (e : Lambda.LExpr Core.CoreLParams.mono) : Lambda.LExpr Core.CoreLParams.mono :=
    if env.isEmpty then e
    else Lambda.LExpr.substFvars e env
  let eraseVar (env : List (Core.CoreIdent × Lambda.LExpr Core.CoreLParams.mono))
      (name : Core.CoreIdent) := env.filter (fun (n, _) => n != name)
  let rec go (env : List (Core.CoreIdent × Lambda.LExpr Core.CoreLParams.mono))
      (stmts : List Core.Statement) (acc : List Core.Statement) : List Core.Statement :=
    match stmts with
    | [] => acc.reverse
    | stmt :: rest =>
      match stmt with
      | .cmd (.cmd (.init name ty (.det e) md)) =>
        let e' := substExpr env e
        let env' := if isSmallGroundValue e' then (name, e') :: eraseVar env name
                    else eraseVar env name
        go env' rest ((.cmd (.cmd (.init name ty (.det e') md))) :: acc)
      | .cmd (.cmd (.set name (.det e) md)) =>
        let e' := substExpr env e
        let env' := if isSmallGroundValue e' then (name, e') :: eraseVar env name
                    else eraseVar env name
        go env' rest ((.cmd (.cmd (.set name (.det e') md))) :: acc)
      | .cmd (.cmd (.set name .nondet md)) =>
        go (eraseVar env name) rest ((.cmd (.cmd (.set name .nondet md))) :: acc)
      | .cmd (.cmd (.assert l e md)) =>
        go env rest ((.cmd (.cmd (.assert l (substExpr env e) md))) :: acc)
      | .cmd (.cmd (.assume l e md)) =>
        go env rest ((.cmd (.cmd (.assume l (substExpr env e) md))) :: acc)
      | .cmd (.cmd (.cover l e md)) =>
        go env rest ((.cmd (.cmd (.cover l (substExpr env e) md))) :: acc)
      | .cmd (.call lhs pn args md) =>
        let args' := args.map (substExpr env)
        let env' := lhs.foldl (fun e n => eraseVar e n) env
        go env' rest ((.cmd (.call lhs pn args' md)) :: acc)
      | .block l b md =>
        let b' := go env b []
        go env rest ((.block l b' md) :: acc)
      | .ite c tb eb md =>
        let c' := c.map (substExpr env)
        let tb' := go env tb []
        let eb' := go env eb []
        go env rest ((.ite c' tb' eb' md) :: acc)
      | .loop g m invs b md =>
        let g' := g.map (substExpr env)
        let m' := m.map (substExpr env)
        let invs' := invs.map (substExpr env)
        let b' := go env b []
        go {} rest ((.loop g' m' invs' b' md) :: acc)
      | other => go env rest (other :: acc)
  go {} stmts []

/-- Apply constant propagation to all procedure bodies in a Core program. -/
def propagateConstantsInProgram (pgm : Core.Program) : Core.Program :=
  { pgm with decls := pgm.decls.map fun d =>
    match d with
    | .proc p md => .proc { p with body := propagateConstants p.body } md
    | other => other }

/-- Constant propagation preserves the number of program declarations. -/
theorem propagateConstantsInProgram_decls_length (pgm : Core.Program) :
    (propagateConstantsInProgram pgm).decls.length = pgm.decls.length := by
  unfold propagateConstantsInProgram
  simp [List.length_map]

end -- public section

end Strata
