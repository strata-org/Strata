/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel
import Strata.Util.Tactics

/-!
# Eliminate Returns in Expression Position

Rewrites functional procedure bodies so that `return` statements are removed
and early-return guard patterns become if-then-else expressions. This makes
the body a pure expression tree suitable for translation to a Core function.

The algorithm walks a block backwards (from last statement to first),
accumulating a result expression:

- The last statement is converted via `lastStmtToExpr` which strips `return`,
  recurses into blocks, and handles if-then-else.
- Each preceding statement wraps around the accumulated result via `stmtsToExpr`:
  - `if (cond) { body }` (no else) becomes `if cond then lastStmtToExpr(body) else acc`
  - Other statements are kept in a two-element block with the accumulator.

-/

namespace Strata.Laurel

/-- Appending a singleton strictly increases `sizeOf`. -/
private theorem List.sizeOf_lt_append_singleton [SizeOf α] (xs : List α) (y : α) :
    sizeOf xs < sizeOf (xs ++ [y]) := by
  induction xs with
  | nil => simp_all; omega
  | cons hd tl ih => simp_all [List.cons_append]

/-- `dropLast` of a non-empty list has strictly smaller `sizeOf`. -/
private theorem List.sizeOf_dropLast_lt [SizeOf α] {l : List α} (h_ne : l ≠ []) :
    sizeOf l.dropLast < sizeOf l := by
  have h_concat := List.dropLast_concat_getLast h_ne
  have : sizeOf l = sizeOf (l.dropLast ++ [l.getLast h_ne]) := by rw [h_concat]
  rw [this]
  exact List.sizeOf_lt_append_singleton l.dropLast (l.getLast h_ne)

mutual

/--
Fold a list of preceding statements (right-to-left) around an accumulator
expression. Each `if-then` (no else) guard wraps as
`if cond then lastStmtToExpr(body) else acc`; other statements produce
`Block [stmt, acc]`.
-/
def stmtsToExpr (stmts : List StmtExprMd) (acc : StmtExprMd) (blockMd : MetaData)
    : StmtExprMd :=
  match stmts with
  | [] => acc
  | s :: rest =>
    let acc' := stmtsToExpr rest acc blockMd
    match s with
    | ⟨.IfThenElse cond thenBr none, smd⟩ =>
      ⟨.IfThenElse cond (lastStmtToExpr thenBr) (some acc'), smd⟩
    | _ =>
      ⟨.Block [s, acc'] none, blockMd⟩
  termination_by (sizeOf stmts, 1)

/--
Convert the last statement of a block into an expression.
- `return expr` → `expr`
- A non-empty block → process last element, fold preceding statements
- `if cond then A else B` → recurse into both branches
- Anything else → kept as-is
-/
def lastStmtToExpr (stmt : StmtExprMd) : StmtExprMd :=
  match stmt with
  | ⟨.Return (some val), _⟩ => val
  | ⟨.Block stmts _, md⟩ =>
    match h_last : stmts.getLast? with
    | some last =>
      have := List.mem_of_getLast? h_last
      let lastExpr := lastStmtToExpr last
      let dropped := stmts.dropLast
      -- have := List.dropLast_subset stmts
      have h : sizeOf stmts.dropLast < sizeOf stmts :=
        List.sizeOf_dropLast_lt (by intro h; simp [h] at h_last)
      stmtsToExpr dropped lastExpr md
    | none => stmt
  | ⟨.IfThenElse cond thenBr (some elseBr), md⟩ =>
    ⟨.IfThenElse cond (lastStmtToExpr thenBr) (some (lastStmtToExpr elseBr)), md⟩
  | _ => stmt
  termination_by (sizeOf stmt, 0)
  decreasing_by
    all_goals (simp_all; term_by_mem)

end

/--
Apply return elimination to a functional procedure's body.
The entire body is treated as an expression to be converted.
-/
def eliminateReturnsInExpression (proc : Procedure) : Procedure :=
  if !proc.isFunctional then proc
  else
    match proc.body with
    | .Transparent bodyExpr =>
      { proc with body := .Transparent (lastStmtToExpr bodyExpr) }
    | .Opaque postconds (some impl) modif =>
      { proc with body := .Opaque postconds (some (lastStmtToExpr impl)) modif }
    | _ => proc

/--
Transform a program by eliminating returns in all functional procedure bodies.
-/
def eliminateReturnsInExpressionTransform (program : Program) : Program :=
  { program with staticProcedures := program.staticProcedures.map eliminateReturnsInExpression }

end Laurel
