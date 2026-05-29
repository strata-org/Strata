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

private abbrev ConstEnv := List (Core.CoreIdent × Lambda.LExpr Core.CoreLParams.mono)

private def substExpr (env : ConstEnv) (e : Lambda.LExpr Core.CoreLParams.mono)
    : Lambda.LExpr Core.CoreLParams.mono :=
  if env.isEmpty then e else Lambda.LExpr.substFvars e env

private def eraseVar (env : ConstEnv) (name : Core.CoreIdent) : ConstEnv :=
  env.filter (fun (n, _) => n != name)

/-- Keep only bindings where both environments agree on the same value. -/
private def intersectEnv (a b : ConstEnv) : ConstEnv :=
  a.filter fun (n, v) => b.any fun (n', v') => n == n' && v == v'

/-- Propagate constant assignments through straight-line Core statements.
    For each `init x := e` or `set x := e` where `e` is a ground value,
    substitute `x → e` in subsequent statements. Kills propagated values
    on `havoc`, `init nondet`, and at control-flow joins. -/
def propagateConstants (stmts : List Core.Statement) : List Core.Statement :=
  let rec go (env : ConstEnv) (stmts : List Core.Statement) (acc : List Core.Statement)
      : List Core.Statement × ConstEnv :=
    match stmts with
    | [] => (acc.reverse, env)
    | stmt :: rest =>
      match stmt with
      | .cmd (.cmd (.init name ty (.det e) md)) =>
        let e' := substExpr env e
        let env' := if isSmallGroundValue e' then (name, e') :: eraseVar env name
                    else eraseVar env name
        go env' rest ((.cmd (.cmd (.init name ty (.det e') md))) :: acc)
      | .cmd (.cmd (.init name ty .nondet md)) =>
        go (eraseVar env name) rest ((.cmd (.cmd (.init name ty .nondet md))) :: acc)
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
        let (b', env') := go env b []
        go env' rest ((.block l b' md) :: acc)
      | .ite c tb eb md =>
        let c' := c.map (substExpr env)
        let (tb', envT) := go env tb []
        let (eb', envE) := go env eb []
        go (intersectEnv envT envE) rest ((.ite c' tb' eb' md) :: acc)
      | .loop g m invs b md =>
        -- Conservative: no substitution inside loop components (variables
        -- may change across iterations), and empty env after the loop.
        let (b', _) := go [] b []
        go [] rest ((.loop g m invs b' md) :: acc)
      | other => go env rest (other :: acc)
  (go [] stmts []).1

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
