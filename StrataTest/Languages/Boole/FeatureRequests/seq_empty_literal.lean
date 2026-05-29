/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

/-!
Regression test for the empty `Sequence.of_<ty>[]` literal lowering.

`Sequence.empty_<ty>` literals carry their element type into Core (see the
`.seq_empty_*` arms in `Boole/Verify.lean`'s `toCoreExpr`). Sequence-literal
syntax `Sequence.of_<ty>[v0, …, vn]` lowers to a left-fold of `seq_build` over
`seq_empty`. For non-empty `vs` the surrounding `seq_build` calls constrain
the element type, but for `vs = []` the seed `seq_empty` is the only place
the type information lives — so the seed must carry it explicitly.

Without that, the bounds-precondition pass produces polymorphic obligations
like `0 < Sequence.length (Sequence.empty)` that lose track of the element
type and break verification downstream.
-/

namespace Strata

open Lambda

/-- Walk a Core expression and yield the `ty` annotation of every
    `Sequence.empty` op encountered. -/
private def collectSeqEmptyTys
    (e : Core.Expression.Expr) : List (Option LMonoTy) :=
  match e with
  | .op _ ⟨"Sequence.empty", _⟩ ty => [ty]
  | .app _ f a => collectSeqEmptyTys f ++ collectSeqEmptyTys a
  | .abs _ _ _ body => collectSeqEmptyTys body
  | .quant _ _ _ _ trig body =>
      collectSeqEmptyTys trig ++ collectSeqEmptyTys body
  | .ite _ c t f =>
      collectSeqEmptyTys c ++ collectSeqEmptyTys t ++ collectSeqEmptyTys f
  | .eq _ a b => collectSeqEmptyTys a ++ collectSeqEmptyTys b
  | _ => []

/-- Render a `Sequence.empty` type annotation: a concrete element type
    (the post-fix expectation), an unresolved type variable like
    `Sequence(?a)` (the pre-fix bug — the seed is polymorphic and the
    bounds-precondition pass produces polymorphic obligations from it),
    or `untyped` if no annotation is present at all. -/
private def fmtSeqEmptyTy : Option LMonoTy → String
  | none => "untyped"
  | some (.tcons "Sequence" [.bitvec n]) => s!"Sequence bv{n}"
  | some (.tcons "Sequence" [.tcons name []]) => s!"Sequence {name}"
  | some (.tcons "Sequence" [.ftvar v]) => s!"Sequence(?{v})"
  | some ty => s!"other: {repr ty}"

/-- Walk a Core statement (recursing into nested blocks/loops/ites) and
    return every `Sequence.empty` element-type annotation found on the
    right-hand side of `set` commands. -/
private def collectFromStmt (s : Core.Statement) : List (Option LMonoTy) :=
  match s with
  | .init _ _ (.det e) _ => collectSeqEmptyTys e
  | .set _ rhs _ => collectSeqEmptyTys rhs
  | .block _ ss _ => ss.flatMap collectFromStmt
  | .ite _ thenb elseb _ =>
      thenb.flatMap collectFromStmt ++ elseb.flatMap collectFromStmt
  | .loop _ _ _ body _ => body.flatMap collectFromStmt
  | _ => []

/-- Lower a Boole program to Core and return one string per `Sequence.empty`
    op found in the body of every procedure. -/
private def seqEmptyTysIn (p : Strata.Program) : Except String (List String) := do
  let prog ← (Boole.getProgram p).mapError toString
  let cp ← (Boole.toCoreProgram prog p.globalContext).mapError
    fun e => toString (e.format none)
  let mut out : List String := []
  for d in cp.decls do
    match d with
    | .proc proc _ =>
      for stmt in proc.body do
        out := out ++ (collectFromStmt stmt).map fmtSeqEmptyTy
    | _ => pure ()
  return out

/-! ## Empty literal: `Sequence.of_bv32[]` must lower to a typed `Sequence.empty`. -/

private def emptyBv32LiteralPgm : Strata.Program :=
#strata
program Boole;

procedure p() returns (s: (Sequence bv32))
spec { }
{
  s := Sequence.of_bv32[];
};
#end

/-- info: Except.ok ["Sequence bv32"] -/
#guard_msgs in #eval seqEmptyTysIn emptyBv32LiteralPgm

/-! ## Empty literal: `Sequence.of_int[]` must lower to a typed `Sequence.empty`. -/

private def emptyIntLiteralPgm : Strata.Program :=
#strata
program Boole;

procedure p() returns (s: (Sequence int))
spec { }
{
  s := Sequence.of_int[];
};
#end

/-- info: Except.ok ["Sequence int"] -/
#guard_msgs in #eval seqEmptyTysIn emptyIntLiteralPgm

/-! ## Non-empty literal: typing must still come through (sanity check). -/

private def nonEmptyBv32LiteralPgm : Strata.Program :=
#strata
program Boole;

procedure p() returns (s: (Sequence bv32))
spec { }
{
  s := Sequence.of_bv32[bv{32}(0), bv{32}(1)];
};
#end

/-- info: Except.ok ["Sequence bv32"] -/
#guard_msgs in #eval seqEmptyTysIn nonEmptyBv32LiteralPgm

/-! ## Empty literals for bv8, bv16, bv64 must also lower to typed `Sequence.empty`. -/

private def emptyBv8LiteralPgm : Strata.Program :=
#strata
program Boole;

procedure p() returns (s: (Sequence bv8))
spec { }
{
  s := Sequence.of_bv8[];
};
#end

/-- info: Except.ok ["Sequence bv8"] -/
#guard_msgs in #eval seqEmptyTysIn emptyBv8LiteralPgm

private def emptyBv16LiteralPgm : Strata.Program :=
#strata
program Boole;

procedure p() returns (s: (Sequence bv16))
spec { }
{
  s := Sequence.of_bv16[];
};
#end

/-- info: Except.ok ["Sequence bv16"] -/
#guard_msgs in #eval seqEmptyTysIn emptyBv16LiteralPgm

private def emptyBv64LiteralPgm : Strata.Program :=
#strata
program Boole;

procedure p() returns (s: (Sequence bv64))
spec { }
{
  s := Sequence.of_bv64[];
};
#end

/-- info: Except.ok ["Sequence bv64"] -/
#guard_msgs in #eval seqEmptyTysIn emptyBv64LiteralPgm

end Strata
