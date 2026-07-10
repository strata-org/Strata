/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import Strata.Transform.FunctionInlining

open Core
open Strata

/-! ## FunctionInlining Tests -/

section FunctionInliningTests

/-- A user-defined function `incr(x : int) : int { x }` — has a body, hence
    inlinable. Shared by several tests below. -/
private def incrLF : Lambda.LFunc Core.CoreLParams :=
  Lambda.LFunc.mk (name := ⟨"incr", ()⟩)
    (inputs := [(⟨"x", ()⟩, Lambda.LMonoTy.int)]) (output := Lambda.LMonoTy.int)
    (body := some (.fvar default ⟨"x", ()⟩ (some Lambda.LMonoTy.int)))

/-! ### Test: inlineFuncDefs on a literal is identity -/

#guard
  let m : Core.ExpressionMetadata := default
  let lit : Lambda.LExpr Core.CoreLParams.mono := .const m (.intConst 42)
  inlineFuncDefs Core.Factory id lit == lit

/-! ### Test: inlineFuncDefsBounded at depth 0 is identity -/

#guard
  let m : Core.ExpressionMetadata := default
  let lit : Lambda.LExpr Core.CoreLParams.mono := .const m (.intConst 42)
  inlineFuncDefsBounded Core.Factory 0 lit == lit

/-! ### Test: inlineFuncDefs leaves primitives (no body) unchanged -/

#guard
  let m : Core.ExpressionMetadata := default
  let negOp := Lambda.LExpr.op m ⟨"Int.Neg", ()⟩ none
  let call := Lambda.LExpr.app m negOp (.const m (.intConst 5))
  -- Int.Neg is a primitive (no body) — should NOT be inlined.
  inlineFuncDefs Core.Factory id call == call

/-! ### Test: a function *with a body* is actually inlined -/

-- A call `incr(42)` is replaced by its body with `x := 42` — i.e. the literal
-- `42`. The result is pinned to the full concrete value (metadata included:
-- substitution yields `.const m (.intConst 42)` with `m = default`).
#guard
  let m : Core.ExpressionMetadata := default
  match Lambda.Factory.tryAddAll Core.Factory #[incrLF] with
  | .ok factory =>
    let call : Lambda.LExpr Core.CoreLParams.mono :=
      .app m (.op m ⟨"incr", ()⟩ none) (.const m (.intConst 42))
    inlineFuncDefs factory id call == .const m (.intConst 42)
  | .error _ => false

/-! ### Test: nested inlining (calls nested in arguments and in bodies) -/

-- `incr(x){x}` and `g(y){incr(y)}`. `inlineFuncDefs` must fully resolve both a
-- call nested in an argument (`incr(incr(42))`) and a call nested in a body
-- (`g(42)`, whose body itself calls `incr`) — i.e. multi-level inlining.
#guard
  let m : Core.ExpressionMetadata := default
  let gLF : Lambda.LFunc Core.CoreLParams :=
    Lambda.LFunc.mk (name := ⟨"g", ()⟩)
      (inputs := [(⟨"y", ()⟩, Lambda.LMonoTy.int)]) (output := Lambda.LMonoTy.int)
      (body := some (.app m (.op m ⟨"incr", ()⟩ none)
                       (.fvar m ⟨"y", ()⟩ (some Lambda.LMonoTy.int))))
  match Lambda.Factory.tryAddAll Core.Factory #[incrLF, gLF] with
  | .ok factory =>
    let nestedArgs : Lambda.LExpr Core.CoreLParams.mono :=
      .app m (.op m ⟨"incr", ()⟩ none)
        (.app m (.op m ⟨"incr", ()⟩ none) (.const m (.intConst 42)))
    let nestedBody : Lambda.LExpr Core.CoreLParams.mono :=
      .app m (.op m ⟨"g", ()⟩ none) (.const m (.intConst 42))
    (inlineFuncDefs factory id nestedArgs == .const m (.intConst 42)) &&
    (inlineFuncDefs factory id nestedBody == .const m (.intConst 42))
  | .error _ => false

/-! ### Test: inlining descends under binders (abs / ite / eq)

The traversal has dedicated `.abs`, `.ite`, and `.eq` arms; this exercises a
call nested under each so the transform is shown to enter those sub-terms and
inline within them. -/

#guard
  let m : Core.ExpressionMetadata := default
  match Lambda.Factory.tryAddAll Core.Factory #[incrLF] with
  | .ok factory =>
    let incr42 : Lambda.LExpr Core.CoreLParams.mono :=
      .app m (.op m ⟨"incr", ()⟩ none) (.const m (.intConst 42))
    let c42 : Lambda.LExpr Core.CoreLParams.mono := .const m (.intConst 42)
    -- `fun x => incr(42)` → `fun x => 42`
    (inlineFuncDefs factory id (.abs m "x" (some Lambda.LMonoTy.int) incr42)
        == .abs m "x" (some Lambda.LMonoTy.int) c42) &&
    -- `if true then incr(42) else incr(42)` → both branches become `42`
    (inlineFuncDefs factory id (.ite m (.const m (.boolConst true)) incr42 incr42)
        == .ite m (.const m (.boolConst true)) c42 c42) &&
    -- `incr(42) == incr(42)` → `42 == 42`
    (inlineFuncDefs factory id (.eq m incr42 incr42) == .eq m c42 c42)
  | .error _ => false

/-! ### Test: type-substitution failure leaves the call unchanged

`tryInlineCall` bails out (`computeTypeSubst = none`) when a polymorphic
function is called with an unannotated `.op` and no argument carries a type to
infer from — there is no constraint to unify against the type argument `a`.
The transform must gracefully leave such a call untouched rather than inline
with an unresolved type variable. (A typed argument, by contrast, lets the
fallback unifier succeed — second check.) -/

#guard
  let m : Core.ExpressionMetadata := default
  let polyLF : Lambda.LFunc Core.CoreLParams :=
    Lambda.LFunc.mk (name := ⟨"poly", ()⟩)
      (typeArgs := ["a"])
      (inputs := [(⟨"x", ()⟩, Lambda.LMonoTy.ftvar "a")])
      (output := Lambda.LMonoTy.ftvar "a")
      (body := some (.fvar m ⟨"x", ()⟩ (some (Lambda.LMonoTy.ftvar "a"))))
  match Lambda.Factory.tryAddAll Core.Factory #[polyLF] with
  | .ok factory =>
    -- Unannotated op + untyped argument: no type constraint, `computeTypeSubst`
    -- fails, and the call is left exactly as-is.
    let callUntyped : Lambda.LExpr Core.CoreLParams.mono :=
      .app m (.op m ⟨"poly", ()⟩ none) (.fvar m ⟨"y", ()⟩ none)
    (inlineFuncDefs factory id callUntyped == callUntyped) &&
    -- Control: a typed argument gives the fallback unifier a constraint, so the
    -- same function DOES inline (to the substituted body, i.e. the argument).
    let callTyped : Lambda.LExpr Core.CoreLParams.mono :=
      .app m (.op m ⟨"poly", ()⟩ none) (.const m (.intConst 42))
    (inlineFuncDefs factory id callTyped == .const m (.intConst 42))
  | .error _ => false

/-! ### Test: inlining descends under quantifiers (`.quant`)

The traversal has a dedicated `.quant` arm that recurses into both the trigger
and the body; this places an inlinable call in each and pins the result. -/

#guard
  let m : Core.ExpressionMetadata := default
  match Lambda.Factory.tryAddAll Core.Factory #[incrLF] with
  | .ok factory =>
    let incr42 : Lambda.LExpr Core.CoreLParams.mono :=
      .app m (.op m ⟨"incr", ()⟩ none) (.const m (.intConst 42))
    let c42 : Lambda.LExpr Core.CoreLParams.mono := .const m (.intConst 42)
    -- `∀ x : int, [trigger incr(42)] incr(42)` → both trigger and body become `42`
    (inlineFuncDefs factory id
        (.quant m .all "x" (some Lambda.LMonoTy.int) incr42 incr42)
      == .quant m .all "x" (some Lambda.LMonoTy.int) c42 c42)
  | .error _ => false

/-! ### Test: `postProcess` fires on every visited subexpression

The docstring states `postProcess` runs on every visited node — both freshly
inlined bodies and nodes where nothing was inlined — not only inlined bodies.
A non-trivial `postProcess` (rewriting the literal `42` to `999`) makes that
observable: it fires on a bare non-inlinable leaf, and it participates in an
inlining traversal (changing the result vs. `id`). -/

#guard
  let m : Core.ExpressionMetadata := default
  let pp : Lambda.LExpr Core.CoreLParams.mono → Lambda.LExpr Core.CoreLParams.mono :=
    fun e => match e with
      | .const em (.intConst 42) => .const em (.intConst 999)
      | _ => e
  match Lambda.Factory.tryAddAll Core.Factory #[incrLF] with
  | .ok factory =>
    let call : Lambda.LExpr Core.CoreLParams.mono :=
      .app m (.op m ⟨"incr", ()⟩ none) (.const m (.intConst 42))
    -- (a) On a bare leaf with no call to inline, `postProcess` still fires
    --     (the `| none => postProcess e'` branch), proving it runs on
    --     non-inlined subexpressions.
    (inlineFuncDefs factory pp (.const m (.intConst 42)) == .const m (.intConst 999)) &&
    (inlineFuncDefs factory id (.const m (.intConst 42)) == .const m (.intConst 42)) &&
    -- (b) Within an actual inlining traversal, `postProcess` also participates:
    --     the result is `999` (vs `42` under `id`).
    (inlineFuncDefs factory pp call == .const m (.intConst 999)) &&
    (inlineFuncDefs factory id call == .const m (.intConst 42))
  | .error _ => false

/-! ### Test: bounded unrolling actually unrolls `maxDepth` times -/

-- `f(x){ Int.Neg(f(x)) }` is (self-)recursive; `Int.Neg` is a primitive with no
-- body, so each unroll wraps one more `Int.Neg` around the residual `f(42)`
-- call. Depth 0 leaves the call untouched; depth `k` produces `k` nested
-- `Int.Neg` — demonstrating bounded unrolling stops at the requested depth.
#guard
  let m : Core.ExpressionMetadata := default
  let fLF : Lambda.LFunc Core.CoreLParams :=
    Lambda.LFunc.mk (name := ⟨"f", ()⟩)
      (inputs := [(⟨"x", ()⟩, Lambda.LMonoTy.int)]) (output := Lambda.LMonoTy.int)
      (body := some (.app m (.op m ⟨"Int.Neg", ()⟩ none)
                       (.app m (.op m ⟨"f", ()⟩ none)
                         (.fvar m ⟨"x", ()⟩ (some Lambda.LMonoTy.int)))))
  match Lambda.Factory.tryAddAll Core.Factory #[fLF] with
  | .ok factory =>
    let call : Lambda.LExpr Core.CoreLParams.mono :=
      .app m (.op m ⟨"f", ()⟩ none) (.const m (.intConst 42))
    -- depth 0: identity (the call is left as-is)
    (inlineFuncDefsBounded factory 0 call == call) &&
    -- depth 1: exactly one `Int.Neg` wrapping the residual `f(42)`,
    -- pinned to the full concrete value (substitution is deterministic and
    -- every metadata in the fixture is `default`)
    (inlineFuncDefsBounded factory 1 call ==
      .app m (.op m ⟨"Int.Neg", ()⟩ none)
        (.app m (.op m ⟨"f", ()⟩ none) (.const m (.intConst 42)))) &&
    -- depth 2: two nested `Int.Neg`
    (inlineFuncDefsBounded factory 2 call ==
      .app m (.op m ⟨"Int.Neg", ()⟩ none)
        (.app m (.op m ⟨"Int.Neg", ()⟩ none)
          (.app m (.op m ⟨"f", ()⟩ none) (.const m (.intConst 42)))))
  | .error _ => false

end FunctionInliningTests
