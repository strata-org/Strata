/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.StmtProps
public import Strata.DL.Imperative.Cmd
public import Strata.DL.Util.LabelGen

public section

namespace Imperative

open LabelGen (StringGenM)

/-! # `hoistLoopPrefixInits` — structured-to-structured loop-init hoist

A pass that transforms a `List (Stmt P (Cmd P))` so that every `.loop` body
contains no `.init` commands at any nesting level. Concretely, the output
satisfies `Block.loopBodyNoInits = true`.

**Same-name lift (pure, no rename).**

Strategy (post-order traversal): at every `.loop _ _ _ body _`, recurse into
`body` first (so nested loops are already hoist-processed), then call
`liftInitsInLoopBody` to walk the body and collect every `.init` reachable
through `.block` and `.ite` substructures (but not into nested loops, which are
already processed). Each collected init `init y ty rhs md` is lifted to a
SAME-name prelude havoc `init y ty .nondet md` emitted as a SIBLING before the
rewritten loop, and the body init is rewritten in place to `set y rhs md`. No
fresh name is generated and no substitution is applied — soundness rests on the
`StoreAgreement` pipeline relation ignoring source-undefined slots, gated by
`Block.uniqueInits`.

This file keeps the pure same-name pass definitions. The `initVars` and
`noInitsAnywhere` correspondence lemmas live in `StmtProps`. The
measure-free-loop precondition is `Block.noMeasureLoops` from `Stmt.lean`.
-/

/-! ## Same-name lift and hoist (pure, no rename)

The pipeline relation is `StoreAgreement` (source-on-left), which constrains
only source-*defined* slots, so it ignores the post-iteration divergence where
the source pops a body-local `y` to `none` while the hoisted prelude keeps it
defined. Reuse of the source name `y` is therefore sound, gated by
`Block.uniqueInits` (global init-name `Nodup`, carried in `PipelinePre`), which
rules out two hoisted preludes colliding.

These same-name variants are pure (`Block → Block`, no `StringGenM`): the
`.init y ty rhs md` case lifts to a prelude havoc `init y ty .nondet md` (SAME
`y`), rewrites the body init to `set y rhs md`, and records no rename — so no
renaming/substitution step is needed. -/

mutual
/-- Same-name lift of a loop body: collect every `.init` at any depth and lift
it to a SAME-name prelude havoc. Does NOT recurse into nested `.loop`
substructures (already hoist-processed in post-order).

Returns a pair `(havocs, body')`:
* `havocs` is the list of prelude commands `init y ty .nondet md` (SAME lhs `y`,
  havoc rhs), and
* `body'` is `s` with each lifted init rewritten as `Cmd.set y rhs md` (SAME
  name `y`; no rename pair, no substitution). -/
def Stmt.liftInitsInLoopBody {P : PureExpr}
    (s : Stmt P (Cmd P)) :
    List (Cmd P) × List (Stmt P (Cmd P)) :=
  match s with
  | .cmd (.init y ty rhs md) =>
      ([.init y ty .nondet md], [.cmd (.set y rhs md)])
  | .cmd c => ([], [.cmd c])
  | .block lbl bss md =>
      let (hs, bss') := Block.liftInitsInLoopBody bss
      (hs, [.block lbl bss' md])
  | .ite g tss ess md =>
      let (ths, tss') := Block.liftInitsInLoopBody tss
      let (ehs, ess') := Block.liftInitsInLoopBody ess
      (ths ++ ehs, [.ite g tss' ess' md])
  | .loop g m inv body md => ([], [.loop g m inv body md])
  | .exit lbl md => ([], [.exit lbl md])
  | .typeDecl t md => ([], [.typeDecl t md])
  termination_by sizeOf s

/-- Apply `Stmt.liftInitsInLoopBody` to every statement in the block,
concatenating the harvested havocs and rewritten residuals. -/
def Block.liftInitsInLoopBody {P : PureExpr}
    (ss : List (Stmt P (Cmd P))) :
    List (Cmd P) × List (Stmt P (Cmd P)) :=
  match ss with
  | [] => ([], [])
  | s :: rest =>
      let (hs_s, ss_s) := Stmt.liftInitsInLoopBody s
      let (hs_r, ss_r) := Block.liftInitsInLoopBody rest
      (hs_s ++ hs_r, ss_s ++ ss_r)
  termination_by sizeOf ss
end

mutual
/-- Same-name top-level pass (pure): post-order traversal. For a `.loop`,
recurse into the body first (so nested loops are hoist-processed), then call
`Block.liftInitsInLoopBody` on the post-processed body to collect this loop's
body inits with their SAME names. The havocs are emitted as SIBLING commands
*before* the rewritten loop; the body is NOT renamed (same names). For `.block`
and `.ite`, recurse structurally. Other statements are identity. -/
def Stmt.hoistLoopPrefixInits {P : PureExpr}
    (s : Stmt P (Cmd P)) : List (Stmt P (Cmd P)) :=
  match s with
  | .cmd c => [.cmd c]
  | .block lbl bss md => [.block lbl (Block.hoistLoopPrefixInits bss) md]
  | .ite g tss ess md =>
      [.ite g (Block.hoistLoopPrefixInits tss) (Block.hoistLoopPrefixInits ess) md]
  | .loop g m inv body md =>
      let body₁ := Block.hoistLoopPrefixInits body
      let (havocs, body₂) := Block.liftInitsInLoopBody body₁
      havocs.map Stmt.cmd ++ [.loop g m inv body₂ md]
  | .exit lbl md => [.exit lbl md]
  | .typeDecl t md => [.typeDecl t md]
  termination_by sizeOf s

/-- Apply `Stmt.hoistLoopPrefixInits` to each statement of the block,
concatenating the resulting lists. -/
def Block.hoistLoopPrefixInits {P : PureExpr}
    (ss : List (Stmt P (Cmd P))) : List (Stmt P (Cmd P)) :=
  match ss with
  | [] => []
  | s :: rest => Stmt.hoistLoopPrefixInits s ++ Block.hoistLoopPrefixInits rest
  termination_by sizeOf ss
end

end Imperative
