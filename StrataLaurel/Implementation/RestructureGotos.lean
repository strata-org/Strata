/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.LaurelAST
public import StrataLaurel.Implementation.LaurelPass
import StrataLaurel.Implementation.MapStmtExpr

/-!
# Restructure Gotos

Lowers the two block features Core has no counterpart for: a `goto L` back to
the start of an enclosing block, and the invariants and termination measure a
block carries. Core's structured statements only offer `exit` (a forward jump
past the end of an enclosing block) and `while`, so a block that some `goto`
targets becomes a loop:

```
  { S } L invariant I decreases D
```
becomes
```
  { while(true) invariant I decreases D { { S'; exit L } $goto_start_n } } L
```
(`decreases D` stands for the block's measure in the AST. Laurel has no surface
syntax for a measure, on a block or on a `while`, so it is set only by a front
end and the pretty-printer omits it.) Here `S'` is `S` with every `goto L`
replaced by `exit $goto_start_n`. That
jump leaves the inner block and so reaches the loop's back edge; running off the
end of `S'` instead meets `exit L`, which leaves the loop, since falling off a
block's end never re-enters it. An `exit L` inside `S` leaves the loop directly.
The trailing `exit L` is omitted when `S'` already ends in a jump or `return`,
where it would be dead code. The invariants sit on the loop
head, which is exactly where a block's invariants are checked: on entry and on
every jump back to its start. Because every jump target is an *enclosing*
block, the control flow is reducible by construction and this local rewrite is
all the restructuring needed.

A labelled block that no `goto` targets is not a loop; its invariants become
`assert`s on entry and its measure, which has no iteration to decrease across,
is dropped.

The fresh label `$goto_start_{n}` uses a per-program counter; the leading `$`
keeps it out of the user-name space. A nested block reusing the label `L`
shadows it, so the replacement does not descend into one.

The pass runs late — after `EliminateReturnStatements` and before
`LoopInvariantWellFormedness`, which needs to see the loops it creates — so
every earlier pass works on the goto form, and everything downstream, Core
included, sees only structured control flow. The traversal is the generic
bottom-up `mapProgramStmtExprM`, so inner blocks are restructured first.
-/

namespace Strata.Laurel

namespace RestructureGotos

public structure RestructureState where
  freshCounter : Nat := 0

public abbrev RestructureM := StateM RestructureState

private def freshStartLabel : RestructureM String :=
  modifyGet fun s => (s!"$goto_start_{s.freshCounter}", { s with freshCounter := s.freshCounter + 1 })

/-- Replace every `goto label` that targets this block by `exit startLabel`,
    without descending into a nested block that shadows `label`. Returns whether
    any jump was replaced. -/
private def redirectGotos (label startLabel : String) (stmts : List StmtExprMd) :
    List StmtExprMd × Bool :=
  let pre (e : StmtExprMd) : StateM Bool (Option StmtExprMd) :=
    match e.val with
    | .Block _ (some l) _ _ => pure (if l == label then some e else none)
    | _ => pure none
  let post (e : StmtExprMd) : StateM Bool StmtExprMd :=
    match e.val with
    | .Goto l .blockStart =>
      if l == label then do
        set true
        pure ⟨.Goto startLabel .blockEnd, e.source⟩
      else pure e
    | _ => pure e
  (stmts.mapM (mapStmtExprPrePostM pre post) |>.run false)

/-- Lowers one labelled block carrying a backward `goto` or invariants; all other
    nodes pass through. -/
public def rewriteNode (node : StmtExprMd) : RestructureM StmtExprMd := do
  match node.val with
  | .Block stmts (some label) invs dec =>
    let source := node.source
    let startLabel ← freshStartLabel
    let (stmts', jumpsBack) := redirectGotos label startLabel stmts
    if jumpsBack then
      let endsInJump := match stmts'.getLast? with
        | some ⟨.Goto _ _, _⟩ | some ⟨.Return _, _⟩ => true
        | _ => false
      let leave : List StmtExprMd := if endsInJump then [] else [⟨.Goto label .blockEnd, source⟩]
      let body : StmtExprMd := ⟨.Block (stmts' ++ leave) (some startLabel) [] none, source⟩
      let loop : StmtExprMd := ⟨.While ⟨.LiteralBool true, source⟩ invs dec body false, source⟩
      pure ⟨.Block [loop] (some label) [] none, source⟩
    else if invs.isEmpty && dec.isNone then
      pure node
    else
      let asserts := invs.map fun inv => (⟨.Assert inv none, inv.source⟩ : StmtExprMd)
      pure ⟨.Block (asserts ++ [⟨.Block stmts (some label) [] none, source⟩]) none [] none, source⟩
  | _ => pure node

end RestructureGotos

public section

/-- Lower every backward `goto` and every block invariant in a Laurel program;
    afterwards every `Goto` is a forward `exit` and no block carries invariants
    or a measure. -/
def restructureGotos (program : Program) : Program :=
  (mapProgramStmtExprM RestructureGotos.rewriteNode program |>.run {}).fst

/-- Pipeline pass: turn blocks that are the targets of backward jumps into loops. -/
public def restructureGotosPass : LaurelPass where
  name := "RestructureGotos"
  creates := [
      NodeKind.StmtExpr.While,
      NodeKind.StmtExpr.Block,
      NodeKind.StmtExpr.Goto,
      NodeKind.StmtExpr.LiteralBool,
      NodeKind.StmtExpr.Assert
    ]
  removes := [
      NodeKind.StmtExpr.Goto.destination.blockStart,
      NodeKind.StmtExpr.Block.invariants.cons,
      NodeKind.StmtExpr.Block.decreases.some
    ]
  documentation := "Lowers a labelled block that some `goto` jumps back into to `{ while(true) invariant I decreases D { { S'; exit L } $goto_start_n } } L`, where `S'` redirects each `goto L` to `exit $goto_start_n`. A labelled block with invariants but no backward jump asserts them on entry instead. Afterwards Core sees only structured control flow: forward exits and `while` loops."
  run := fun _ p _m => (restructureGotos p, [], {})

end -- public section
end Strata.Laurel
