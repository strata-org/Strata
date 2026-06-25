/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelAST
public import Strata.Languages.Laurel.LaurelPass
import Strata.Languages.Laurel.MapStmtExpr
import Strata.Util.Tactics

/-!
# Eliminate Do-While

Lowers post-test `While` loops (`postTest = true`, the `do … while` form) into
the pre-test `while` machinery. Runs early so that no later pass (or the Core
translator) observes `postTest = true`.

The desugaring of `do BODY while(COND) invariant I` is:
```
  { while(true) invariant I { BODY; if (!COND) exit L } } L
```
`BODY` runs once per iteration with `COND` re-checked after it; the real guard
reaches post-loop code via the structured `exit L`, so the encoding is sound,
complete, and linear (a single body in the IR — no peeling/duplication). The
invariant `I` is checked at the loop head (before each body), matching `while`.

The fresh exit label `L` is `$dowhile_exit_{n}` for a per-program monotonic
counter `n`. The leading `$` keeps it out of the user-name space (no source
identifier can contain `$`), so it can never capture, or be captured by, a user
`break`/`continue` label, and the counter keeps nested do-whiles distinct.

The traversal is the generic bottom-up `mapStmtExprM`, so inner do-whiles are
eliminated before their enclosing ones.
-/

namespace Strata.Laurel

/-- Monotonic counter feeding fresh exit labels (scheme described in the module header). -/
private structure ElimState where
  freshCounter : Nat := 0

private abbrev ElimM := StateM ElimState

private def freshExitLabel : ElimM String :=
  modifyGet fun s => (s!"$dowhile_exit_{s.freshCounter}", { s with freshCounter := s.freshCounter + 1 })

/-- Rewrites a post-test `While` to its pre-test desugaring; all other nodes pass through. -/
private def rewriteNode (node : StmtExprMd) : ElimM StmtExprMd := do
  match node.val with
  | .While cond invs dec body true =>
    let source := node.source
    let exitLabel ← freshExitLabel
    let notCond : StmtExprMd := ⟨.PrimitiveOp .Not [cond], source⟩
    let exitStmt : StmtExprMd := ⟨.Exit exitLabel, source⟩
    let guardCheck : StmtExprMd := ⟨.IfThenElse notCond exitStmt none, source⟩
    let loopBody : StmtExprMd := ⟨.Block [body, guardCheck] none, source⟩
    let trueCond : StmtExprMd := ⟨.LiteralBool true, source⟩
    -- Thread `dec` onto the `while(true)` rather than dropping it: each desugared
    -- iteration is one pass through that loop's head, so the measure decreases
    -- across exactly those iterations. The emitted loop is pre-test
    -- (`postTest := false`), so it is not rewritten again.
    let whileStmt : StmtExprMd := ⟨.While trueCond invs dec loopBody false, source⟩
    pure ⟨.Block [whileStmt] (some exitLabel), source⟩
  | _ => pure node

public section

/-- Eliminate every post-test `While` in a Laurel program; afterward every `While` has `postTest = false`. -/
def eliminateDoWhile (program : Program) : Program :=
  let rewrite : Procedure → ElimM Procedure := mapProcedureM (mapStmtExprM rewriteNode)
  (mapProgramProceduresM rewrite program |>.run {}).fst

/-- Pipeline pass: eliminate post-test (`do … while`) loops. -/
public def eliminateDoWhilePass : LoweringPass where
  name := "EliminateDoWhile"
  documentation := "Lowers post-test `While` loops (the `do … while` form) into the pre-test loop `{ while(true) invariant I { BODY; if (!COND) exit L } } L`, with a fresh `$`-prefixed exit label `L`. Runs early so no later pass observes a post-test loop; the invariant is checked at the loop head, matching `while`."
  run := fun _ p _m => (eliminateDoWhile p, [], {})

end -- public section
end Strata.Laurel
