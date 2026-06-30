/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-
Tests that `subscriptElim` walks `program.constants` initializers,
rewriting subscripts there in addition to procedure bodies.

Constants with subscript-bearing initializers cannot currently be parsed
from Laurel grammar text, so this test constructs a program
programmatically — same pattern as `TypeAliasElimTest.lean`.

Latent today (no grammar path produces such constants), but defensive: the
walk was added to address a review comment, and this test pins that
contract so future grammar additions cannot regress it silently.
-/

meta import Strata.Languages.Laurel.SubscriptElim
meta import Strata.Languages.Laurel.Resolution

meta section

open Strata.Laurel

private def mkTy (ty : HighType) : HighTypeMd := { val := ty, source := none }
private def mkE (e : StmtExpr) : StmtExprMd := { val := e, source := none }

-- A constant `c : int := s[0]` where `s` is a sequence built inline.
-- After `subscriptElim`, the initializer should no longer contain a
-- `.Subscript` — it should be rewritten to `Sequence.select(..., 0)`.
private def constantWithSubscript : Program :=
  let buildEmpty := mkE (.StaticCall (mkId SeqOp.empty) [])
  let buildOne   := mkE (.StaticCall (mkId SeqOp.build) [buildEmpty, mkE (.LiteralInt 10)])
  let seqLit     := mkE (.StaticCall (mkId SeqOp.build) [buildOne, mkE (.LiteralInt 20)])
  -- Subscript: seqLit[0]
  let subscriptInit := mkE (.Subscript seqLit (mkE (.LiteralInt 0)) none)
  { staticProcedures := []
    staticFields := []
    types := []
    constants := [{
      name := mkId "c"
      type := mkTy .TInt
      initializer := some subscriptInit }] }

/-- Returns `true` if any `.Subscript` survives in the initializer. -/
private partial def hasSubscript (e : StmtExprMd) : Bool :=
  match e.val with
  | .Subscript _ _ _ => true
  | .StaticCall _ args => args.any hasSubscript
  | .Block stmts _ => stmts.any hasSubscript
  | .Var (.Field t _) => hasSubscript t
  | .IfThenElse c t e =>
    hasSubscript c || hasSubscript t || (e.map hasSubscript).getD false
  | _ => false

-- The initializer should still be a `.StaticCall` to `Sequence.select`,
-- and `hasSubscript` should report `false`.
/--
info: subscript eliminated
-/
#guard_msgs in
#eval! do
  let model := (resolve constantWithSubscript).model
  let (program', _) := subscriptElim model constantWithSubscript
  match program'.constants with
  | [{ initializer := some init, .. }] =>
    if hasSubscript init then
      IO.println "BUG: subscript still present"
    else
      IO.println "subscript eliminated"
  | _ => IO.println "BUG: unexpected constants shape"

end
