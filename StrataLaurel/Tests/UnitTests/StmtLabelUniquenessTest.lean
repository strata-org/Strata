/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Implementation.LaurelToCoreSchemaPass

/-! Core translation labels an assert `assert(<byte offset>)` and, when a second assert in the
same procedure starts at the same offset, falls back to `assert(<fresh id>)`. Both are bare
decimals in one namespace, so the fallback must also be checked against the labels already
taken: otherwise a fresh id can equal the offset of an unrelated assert, the procedure carries a
duplicate label, and Core reports the clash on stderr.

The statements are built directly, since source text cannot place two asserts at one offset.
Asserts at offsets 1, 2 and 3 take the positional labels the fresh-id counter (starting at 1)
would mint next; the second assert at offset 100 must skip all three. -/

open Strata
open Strata.Laurel

private def nodeAt (offset : Nat) (e : StmtExpr) : StmtExprMd :=
  ⟨e, { file := .file "Test.lr", range := { start := ⟨offset⟩, stop := ⟨offset + 1⟩ } }⟩

private def assertAt (offset : Nat) : StmtExprMd :=
  nodeAt offset (.Assert (nodeAt offset (.LiteralBool true)) none)

private partial def labels : Core.Statement → List String
  | Core.Statement.assert l _ _ | Core.Statement.assume l _ _ => [l]
  | Imperative.Stmt.block _ ss _ => ss.flatMap labels
  | _ => []

private def report (stmts : List StmtExprMd) : IO Unit := do
  let (r, _) := runTranslateM { model := { nextId := 0, compositeCount := 0, refToDef := {} } }
    (translateStmt (nodeAt 0 (.Block stmts none)))
  match r with
  | .error e => IO.println s!"error: {e}"
  | .ok ss =>
    let ls := ss.flatMap labels
    IO.println ls
    if ls.eraseDups.length != ls.length then IO.println "duplicate label"

/-- info: [assert(1), assert(2), assert(3), assert(100), assert(4)] -/
#guard_msgs in #eval report [assertAt 1, assertAt 2, assertAt 3, assertAt 100, assertAt 100]
