/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.Expressions
public import Strata.Languages.Core.PipelinePhase
public import Strata.DL.Util.Map

namespace Strata

/-! ## Constant Propagation

A Core-to-Core transform that propagates literal and `from_str(literal)`
assignments through straight-line code. Conservative at control-flow
joins: kills propagated values at loops, propagates into branches.
-/

public section

/-- The "small ground value" predicate: check whether an expression is a
    small ground value suitable for propagation.

    This is the single concrete predicate ("knob") constant propagation uses to
    decide what counts as a propagatable ground value; `propagateConstants`
    calls it directly. -/
private def defaultSmallGroundValue : Lambda.LExpr Core.CoreLParams.mono → Bool
  | .const .. => true
  -- `from_str "..."` boxes a string literal (Python front-end encoding); it is a
  -- ground value just like a bare literal, so it is safe to propagate.
  | .app _ (.op _ name _) (.const _ (.strConst _)) => name.1 == "from_str"
  | _ => false

private abbrev ConstEnv := Map Core.CoreIdent (Lambda.LExpr Core.CoreLParams.mono)

private def eraseVar (env : ConstEnv) (name : Core.CoreIdent) : ConstEnv :=
  Map.erase env name

/-- Keep only bindings where both environments agree on the same value. -/
private def intersectEnv (a b : ConstEnv) : ConstEnv :=
  a.filter fun (n, v) => b.find? n == some v

/-- Detect whether any statement in the list is an `exit` (recursing into
    `block` bodies, both `ite` branches, and `loop` bodies).

    An `exit l` performs a non-local jump out of its enclosing labeled block,
    so straight-line statements textually following it do not execute and the
    block-join environment computed by `go` would be wrong. Constant
    propagation is therefore unsound in the presence of `exit`, and
    `propagateConstants` rejects any program containing one up front. -/
private def containsExit : List Core.Statement → Bool
  | [] => false
  | stmt :: rest =>
    let here := match stmt with
      | .exit _ _ => true
      | .block _ b _ => containsExit b
      | .ite _ tb eb _ => containsExit tb || containsExit eb
      | .loop _ _ _ b _ => containsExit b
      | _ => false
    here || containsExit rest

/-- Propagate constant assignments through straight-line Core statements.
    For each `init x := e` or `set x := e` where `e` is a small ground value
    (as decided by `defaultSmallGroundValue`), substitute `x → e` in subsequent
    statements. Kills propagated values on `havoc`, `init nondet`, and at
    control-flow joins.

    `defaultSmallGroundValue` is the single predicate that selects which
    expressions count as propagatable "small ground values"; it is called
    directly here.

    Rejects programs containing `exit` (see `containsExit`): an `exit`
    escapes its enclosing block, so `go`'s straight-line env threading and
    block-join reasoning would be unsound. The inner `go` worker stays pure
    (`List Core.Statement × ConstEnv`) — the correctness proofs in
    `ConstantPropagationCorrect.lean` depend on that shape — so the `exit`
    check is a separate pre-pass rather than being threaded through `go`. -/
def propagateConstants (stmts : List Core.Statement)
    : Except String (List Core.Statement) :=
  let rec go (env : ConstEnv) (stmts : List Core.Statement) (acc : List Core.Statement)
      : List Core.Statement × ConstEnv :=
    match stmts with
    | [] => (acc.reverse, env)
    | stmt :: rest =>
      match stmt with
      | .cmd (.cmd (.init name ty (.det e) md)) =>
        let e' := Lambda.LExpr.substFvars e env
        let env' := if defaultSmallGroundValue e' then Map.insert env name e'
                    else eraseVar env name
        -- Imperative forbids re-declaration: `Cmd.typeCheck`/`InitState`
        -- (Strata/DL/Imperative/CmdSemantics.lean) require an `init` LHS to be
        -- undeclared, so `name` is always FRESH here (not already bound in
        -- `env`). SOUNDNESS NOTE: we still call `eraseVar` in the else branch.
        -- For a fresh `name`, `eraseVar env name = env`, so it is a harmless
        -- no-op that keeps the UNCONDITIONAL proofs in
        -- ConstantPropagationCorrect.lean (which do not track this freshness
        -- invariant) valid. Dropping it would require threading the
        -- no-redeclaration invariant through the whole simulation; left as a
        -- follow-up.
        go env' rest ((.cmd (.cmd (.init name ty (.det e') md))) :: acc)
      | .cmd (.cmd (.init name ty .nondet md)) =>
        -- As above, `init` names are FRESH (Imperative forbids re-declaration),
        -- so `eraseVar env name = env` here — a harmless no-op retained to keep
        -- the unconditional correctness proofs valid (see the `.det` arm note).
        go (eraseVar env name) rest ((.cmd (.cmd (.init name ty .nondet md))) :: acc)
      | .cmd (.cmd (.set name (.det e) md)) =>
        let e' := Lambda.LExpr.substFvars e env
        let env' := if defaultSmallGroundValue e' then Map.insert env name e'
                    else eraseVar env name
        go env' rest ((.cmd (.cmd (.set name (.det e') md))) :: acc)
      | .cmd (.cmd (.set name .nondet md)) =>
        go (eraseVar env name) rest ((.cmd (.cmd (.set name .nondet md))) :: acc)
      | .cmd (.cmd (.assert l e md)) =>
        go env rest ((.cmd (.cmd (.assert l (Lambda.LExpr.substFvars e env) md))) :: acc)
      | .cmd (.cmd (.assume l e md)) =>
        go env rest ((.cmd (.cmd (.assume l (Lambda.LExpr.substFvars e env) md))) :: acc)
      | .cmd (.cmd (.cover l e md)) =>
        go env rest ((.cmd (.cmd (.cover l (Lambda.LExpr.substFvars e env) md))) :: acc)
      | .call pn args md =>
        -- The current Core `Statement.call` carries its outputs in `args`
        -- (output `CallArg`s) rather than an explicit lhs list, and a call may
        -- assign those outputs. Be conservative: drop the propagation
        -- environment across a call so no stale constant is substituted past it.
        go [] rest ((.call pn args md) :: acc)
      | .block l b md =>
        -- A block is a fresh scope. Propagate into it with the outer env, then
        -- keep only the outer bindings the body left unchanged. `intersectEnv`
        -- against the inner terminal env drops:
        --  (a) inner shadowing re-declarations (`var x := …` over an outer `x`):
        --      the inner env binds the name to a different value than the outer,
        --      so the outer binding is not retained; and
        --  (b) any outer-scoped variable the body `set` to a different or
        --      non-ground value — such writes persist in the parent store
        --      (`Stmt.block` projects away only block-local `init`s), so the
        --      pre-block constant would be stale.
        let (b', envInner) := go env b []
        go (intersectEnv env envInner) rest ((.block l b' md) :: acc)
      | .ite c tb eb md =>
        let c' := c.map (fun (e : Lambda.LExpr Core.CoreLParams.mono) => Lambda.LExpr.substFvars e env)
        let (tb', envT) := go env tb []
        let (eb', envE) := go env eb []
        -- Each branch is wrapped in its own block scope, so branch-local `init`s
        -- are projected away on join. Keep only the OUTER bindings that BOTH
        -- branches left unchanged: intersecting with the outer `env` first is
        -- what makes this sound — a plain `intersectEnv envT envE` would retain a
        -- branch-local shadow (e.g. both branches `var x := 99` over an outer
        -- `x := 42`) because the branches agree on it, even though the outer `x`
        -- is unchanged; filtering the joined env merely by `env.contains` would
        -- not help, since the shadowed name does exist in the outer env.
        go (intersectEnv (intersectEnv env envT) envE) rest ((.ite c' tb' eb' md) :: acc)
      | .loop g m invs b md =>
        -- Conservative: no substitution inside loop components (variables
        -- may change across iterations), and empty env after the loop.
        let (b', _) := go [] b []
        go [] rest ((.loop g m invs b' md) :: acc)
      | other => go env rest (other :: acc)
  if containsExit stmts then
    .error "unsupported program: constant propagation does not support `exit`"
  else
    .ok (go [] stmts []).1

/-- Apply constant propagation to all procedure bodies in a Core program.

    Uses the single `defaultSmallGroundValue` predicate (via `propagateConstants`)
    to decide which expressions count as propagatable small ground values.

    Runs in `CoreTransformM` so that a rejected program (one containing `exit`,
    see `propagateConstants`) surfaces as a transform error to callers rather
    than being silently mis-transformed. `.cfg` bodies and non-procedure
    declarations pass through unchanged. -/
def propagateConstantsInProgram
    (pgm : Core.Program)
    : Core.Transform.CoreTransformM Core.Program := do
  let decls' ← pgm.decls.mapM fun d =>
    match d with
    | .proc p md =>
      match p.body with
      | .structured stmts =>
        match propagateConstants stmts with
        | .ok stmts' => pure (.proc { p with body := .structured stmts' } md)
        | .error msg =>
          throw (Strata.DiagnosticModel.fromMessage s!"ConstantPropagation: {msg}")
      | .cfg _ => pure (.proc p md)
    | other => pure other
  return { pgm with decls := decls' }

/-- ConstantPropagation pipeline phase: propagates ground constants through
    straight-line procedure bodies, using the `defaultSmallGroundValue`
    predicate to decide what counts as a propagatable value. Model-preserving
    because it only replaces variable references with values the store already
    agrees on, so it cannot introduce spurious models. -/
def constantPropagationPipelinePhase : Core.PipelinePhase :=
  Core.modelPreservingPipelinePhase "ConstantPropagation" fun prog => do
    let prog' ← propagateConstantsInProgram prog
    return (true, prog')

end -- public section

end Strata
