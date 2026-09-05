/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.Expressions
public import Strata.Languages.Core.Factory
public import Strata.Languages.Core.PipelinePhase

namespace Strata

/-! ## Function Inlining

Core-to-Core transforms that replace function calls with their bodies.

Uses the same inlining logic as `LExprEval.eval`: `Factory.callOfLFunc`
to decompose applications, `LFunc.computeTypeSubst` + `LExpr.applySubst`
for polymorphic type instantiation, and `substFvarsLifting` for
capture-safe substitution under binders.

Unlike the attribute-gated inlining inside `LExprEval.eval` (which inlines
only `.inline`-attributed, non-recursive functions during evaluation), these
transforms are explicit, caller-driven passes: they inline **any**
fully-applied call whose function has a body, with the caller choosing the
re-inlining budget. In particular, bounded unrolling of recursive functions
is expressed by passing a small `fuel`.
-/

public section

/-- Try to inline a single function call. Returns `some result` if the
    function has a body and is fully applied; `none` otherwise.
    Handles polymorphic functions via type substitution, matching
    the inlining path in `LExprEval.eval`. -/
private def tryInlineCall
    (factory : Lambda.Factory Core.CoreLParams)
    (e : Lambda.LExpr Core.CoreLParams.mono)
    : Option (Lambda.LExpr Core.CoreLParams.mono) :=
  match factory.callOfLFunc e with
  | some (op_expr, args, lfunc) =>
    match lfunc.body with
    | none => none
    | some body =>
      match Lambda.LFunc.computeTypeSubst lfunc op_expr args with
      | some tySubst =>
        let body := body.applySubst tySubst
        let input_map := lfunc.inputs.keys.zip args
        some (Lambda.LExpr.substFvarsLifting body input_map)
      | none => none
  | none => none

/--
Inline function bodies in an expression. For each fully-applied call
`f(a₁, ..., aₙ)` where `f` has a known body in the factory, replace it with
`body[a₁/x₁, ..., aₙ/xₙ]` (with polymorphic type instantiation), then
re-process the result — bounded by `fuel` — so nested calls are inlined too.

`fuel` bounds how many times a freshly inlined body is *re*-inlined: an
inlined result at fuel `0` is kept without further inlining inside it, and
each re-inline strictly decreases `fuel` (each structural step strictly
decreases `sizeOf e` at the same `fuel`, so the function is total, not
`partial`). The two use cases are therefore two budgets of the same
transform:

- **Non-recursive inlining**: the default `fuel` is large enough to fully
  inline any acyclic call graph.
- **Bounded unrolling of recursive functions**: a small `fuel = k` unrolls a
  self-recursive call at most `k + 1` times, leaving the innermost residual
  call uninterpreted; see `inlineFuncDefsBounded`.

`postProcess` is a normalization hook applied to **every visited
subexpression** after its inlining attempt — both to a freshly inlined body
(before it is re-inlined) and to a node where no call was inlined. It is not
restricted to inlined bodies. It defaults to `id`. -/
def inlineFuncDefs
    (factory : Lambda.Factory Core.CoreLParams)
    (postProcess : Lambda.LExpr Core.CoreLParams.mono → Lambda.LExpr Core.CoreLParams.mono := id)
    (e : Lambda.LExpr Core.CoreLParams.mono)
    (fuel : Nat := 1000000) : Lambda.LExpr Core.CoreLParams.mono :=
  go fuel e
where
  go (fuel : Nat) (e : Lambda.LExpr Core.CoreLParams.mono) : Lambda.LExpr Core.CoreLParams.mono :=
    -- First recurse into subexpressions
    let e' := match e with
      | .app m f a => .app m (go fuel f) (go fuel a)
      | .ite m c t el => .ite m (go fuel c) (go fuel t) (go fuel el)
      | .abs m n ty b => .abs m n ty (go fuel b)
      | .quant m k n ty tr b => .quant m k n ty (go fuel tr) (go fuel b)
      | .eq m l r => .eq m (go fuel l) (go fuel r)
      | other => other
    -- Then try to inline the (possibly rebuilt) application, re-processing the
    -- result within the remaining budget.
    match tryInlineCall factory e' with
    | some inlined =>
      match fuel with
      | 0 => postProcess inlined
      | fuel + 1 => go fuel (postProcess inlined)
    | none => postProcess e'
  termination_by (fuel, sizeOf e)
  decreasing_by
    all_goals simp_wf
    all_goals omega

/-- Inline (possibly recursive) function calls with bounded unrolling: unroll
    each call chain at most `maxDepth` times; at depth `0` calls are left
    as-is (uninterpreted).

    This is `inlineFuncDefs` at a small explicit budget: `maxDepth = 0` is the
    identity, and `maxDepth = k + 1` runs the shared worker with fuel `k`
    (which inlines up to `k + 1` times along any chain). `postProcess` is the
    same normalization hook as in `inlineFuncDefs`. -/
def inlineFuncDefsBounded
    (factory : Lambda.Factory Core.CoreLParams)
    (maxDepth : Nat)
    (e : Lambda.LExpr Core.CoreLParams.mono)
    (postProcess : Lambda.LExpr Core.CoreLParams.mono → Lambda.LExpr Core.CoreLParams.mono := id)
    : Lambda.LExpr Core.CoreLParams.mono :=
  match maxDepth with
  | 0 => e
  | depth + 1 => inlineFuncDefs.go factory postProcess depth e

end -- public section

end Strata

public section

namespace Core
namespace FunctionInlining

open Strata (inlineFuncDefs inlineFuncDefsBounded)

/-- Apply a Core expression transform to every expression in a program:
    axiom bodies and procedures (pre/postcondition checks and structured
    bodies via `Procedure.mapExprs`; CFG bodies unchanged). All other
    declaration kinds pass through untouched — deliberately so for inlining:
    `.func`/`.recFuncBlock` are the inlining *source* (rewriting their bodies
    would fold definitions into each other), and `.distinct` declares
    pairwise-distinct names rather than evaluable expressions. -/
@[expose] def mapProgramExprs
    (f : Lambda.LExpr Core.CoreLParams.mono → Lambda.LExpr Core.CoreLParams.mono)
    (pgm : Core.Program) : Core.Program :=
  { pgm with decls := pgm.decls.map fun d =>
    match d with
    | .ax ax md => .ax { ax with e := f ax.e } md
    | .proc p md => .proc (p.mapExprs f) md
    | other => other }

/-- Add the program's own non-recursive `.func` definitions to `base`, which by
    default holds only built-ins, so their calls become inlinable. Recursive
    functions are skipped: inlining one only unfolds it until the budget runs out.
    A parsed program cannot reach that case, since `rec function` arrives as its own
    declaration kind; the guard is for a program built directly. -/
def withProgramFuncs (base : @Lambda.Factory Core.CoreLParams) (prog : Program) :
    @Lambda.Factory Core.CoreLParams :=
  prog.decls.foldl (fun F decl =>
    match decl with
    | .func f _ =>
      let lf := f.toLFunc
      -- The push cannot fail here: `precondElim` pushes the same functions and
      -- rejects a program whose function names collide with the factory's.
      if lf.isRecursive then F else (F.tryPush lf).toOption.getD F
    | _ => F) base

/-- Program-level function inlining, with the factory taken from the
    transform state: `maxDepth = none` inlines non-recursive definitions to a
    fixpoint (`inlineFuncDefs`), `maxDepth = some d` unrolls up to depth `d`
    (`inlineFuncDefsBounded`; depth 0 is the identity). Returns whether the
    program changed alongside the transformed program. -/
def run (prog : Program) (maxDepth : Option Nat := none) :
    Transform.CoreTransformM (Bool × Program) := do
  let factory ← Transform.getFactory
  let inline : Lambda.LExpr Core.CoreLParams.mono → Lambda.LExpr Core.CoreLParams.mono :=
    match maxDepth with
    | none => fun e => inlineFuncDefs factory id e
    | some d => fun e => inlineFuncDefsBounded factory d e
  let prog' := mapProgramExprs inline prog
  return (decide (prog' ≠ prog), prog')

end FunctionInlining

/-- Inline known function definitions throughout every expression of the program.
    `noBetaRedexes` is not preserved: substituting a body for a call introduces
    redexes that beta reduction removes. Requiring `noPrecondsFromFuncs` orders the
    phase after `precondElim`, since inlining a call removes the site where the
    function's precondition would be raised as an obligation. -/
def functionInliningPipelinePhase (maxDepth : Option Nat := none) : PipelinePhase :=
  modelPreservingPipelinePhase "functionInlining"
    (requires := factSet![.noPrecondsFromFuncs])
    (preserves := factSet![.noCFGBodies, .noCalls, .noLoops, .noLoopInvariants,
                         .noLoopMeasures, .staticSingleAssignment, .noPrecondsFromFuncs,
                         .noNondetGuards, .noInternalFuncDecl, .noPolymorphicProcedures,
                         .noPolymorphicFunctions])
    fun prog => do
      -- The program's functions are in the factory for this pass alone: the encoder
      -- environment registers every `.func` itself and rejects a redefinition.
      let base ← Transform.getFactory
      Transform.setFactory (FunctionInlining.withProgramFuncs base prog)
      try
        let res ← FunctionInlining.run prog maxDepth
        Transform.setFactory base
        return res
      catch e =>
        Transform.setFactory base
        throw e

end Core

end -- public section
