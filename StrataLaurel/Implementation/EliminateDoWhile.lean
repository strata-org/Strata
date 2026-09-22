/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.LaurelAST
public import StrataLaurel.Implementation.LaurelPass
import StrataLaurel.Implementation.MapStmtExpr
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

namespace EliminateDoWhile

-- The state, the label generator and `rewriteNode` are public rather than
-- private because `EliminateDoWhileProps` states and proves the pass's
-- `NodeKind` specification against `rewriteNode` directly, and needs to unfold
-- it (hence `@[expose]`).

/-- Monotonic counter feeding fresh exit labels (scheme described in the module header). -/
public structure ElimState where
  freshCounter : Nat := 0

public abbrev ElimM := StateM ElimState

public def freshExitLabel : ElimM String :=
  modifyGet fun s => (s!"$dowhile_exit_{s.freshCounter}", { s with freshCounter := s.freshCounter + 1 })

/-- Rewrites a post-test `While` to its pre-test desugaring; all other nodes pass through. -/
@[expose] public def rewriteNode (node : StmtExprMd) : ElimM StmtExprMd := do
  match node.val with
  | .While cond invs dec body true =>
    let source := node.source
    let exitLabel ← freshExitLabel
    let notCond : StmtExprMd := ⟨.StaticCall (mkId Operation.Not.procName) [cond], source⟩
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

end EliminateDoWhile

public section

/-- Eliminate every post-test `While` in a Laurel program; afterward every `While`
    has `postTest = false`.

    The walk is `mapProgramStmtExprM`, which reaches *every* expression position
    in a program — not just procedure bodies and specifications, but also
    a constrained type's constraint and witness, field and constant
    initializers, and a coroutine's `relies`/`guarantees`.
    `EliminateDoWhileProps.eliminateDoWhile_spec` proves the `removes`
    declaration below against this walk, which needs the walk to be total. No
    source program puts a loop in one of the extra positions: each expects a
    value and a loop is `void`. -/
def eliminateDoWhile (program : Program) : Program :=
  (mapProgramStmtExprM EliminateDoWhile.rewriteNode program |>.run {}).fst

/-- Pipeline pass: eliminate post-test (`do … while`) loops. -/
public def eliminateDoWhilePass : LoweringPass where
  name := "EliminateDoWhile"
  creates := [
      NodeKind.StmtExpr.While,
      NodeKind.StmtExpr.Block,
      NodeKind.StmtExpr.Exit,
      NodeKind.StmtExpr.IfThenElse,
      NodeKind.StmtExpr.StaticCall,
      NodeKind.StmtExpr.LiteralBool
    ]
  removes := [NodeKind.StmtExpr.While.postTest.true]
  documentation := "Lowers post-test `While` loops (the `do … while` form) into the pre-test loop `{ while(true) invariant I { BODY; if (!COND) exit L } } L`, with a fresh `$`-prefixed exit label `L`. Runs early so no later pass observes a post-test loop; the invariant is checked at the loop head, matching `while`."
  run := fun _ p _m => (eliminateDoWhile p, [], {})

end -- public section
end Strata.Laurel
