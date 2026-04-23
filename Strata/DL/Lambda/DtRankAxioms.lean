/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.Factory
public import Strata.DL.Lambda.TypeFactory

/-!
## dtRank Axiom Generation for Termination Checking

For each ADT used as a decreasing measure, we generate:
1. An uninterpreted function `D..dtRank : D → Int`
2. Per-constructor axioms: for each constructor field of datatype type,
   `dtRank(field) < dtRank(C(fields...))`, with trigger `dtRank(C(fields...))`.

This follows the Dafny encoding, adapted for typed SMT (`declare-datatype`).
See `docs/TerminationChecking.md` §3 for details.
-/

namespace Lambda

public section

open Strata.DL.Util (FuncAttr TyIdentifier)

def dtRankSuffix : String := "..dtRank"

def dtRankFuncName (dtName : String) : String := s!"{dtName}{dtRankSuffix}"

/-- Create the `D..dtRank : D → Int` uninterpreted function declaration. -/
def mkDtRankFunc {T : LExprParams} [Inhabited T.IDMeta] (dt : LDatatype T.IDMeta) : LFunc T :=
  { name := dtRankFuncName dt.name
    typeArgs := dt.typeArgs
    inputs := [(⟨"x", default⟩, dataDefault dt)]
    output := LMonoTy.int }

/-- Generate per-constructor dtRank axioms for a single datatype.
    For each constructor `C` and each field of datatype type within the
    mutual block `block`, generates:
      `∀ fields. D'..dtRank(field_i) < D..dtRank(C(fields...))`
    with trigger `D..dtRank(C(fields...))`.

    The `block` parameter determines which field types are considered
    "recursive" (i.e., belong to the mutual datatype block). -/
def mkDtRankPerConstrAxioms {T : LExprParams} [Inhabited T.Metadata] [Inhabited T.IDMeta] [DecidableEq T.IDMeta]
    (dt : LDatatype T.IDMeta) (block : MutualDatatype T.IDMeta)
    (m : T.Metadata) : List (LExpr T.mono) :=
  let dtTy := dataDefault dt
  dt.constrs.flatMap fun c =>
    let numFields := c.args.length
    let constrTy := c.args.foldr (fun (_, argTy) acc => LMonoTy.arrow argTy acc) dtTy
    let constrApp := c.args.foldlIdx (fun acc i _ =>
      .app m acc (.bvar m (numFields - 1 - i))
    ) (.op m c.name (.some constrTy) : LExpr T.mono)
    let dtRankTy : LMonoTy := LMonoTy.arrow dtTy LMonoTy.int
    let dtRankConstr : LExpr T.mono :=
      .app m (.op m (dtRankFuncName dt.name) (.some dtRankTy)) constrApp
    c.args.foldlIdx (init := []) fun acc i (_, fieldTy) =>
      match block.find? (fun d => fieldTy == dataDefault d) with
      | none => acc
      | some fieldDt =>
        let fieldBvar : LExpr T.mono := .bvar m (numFields - 1 - i)
        let fieldDtTy := dataDefault fieldDt
        let fieldRankTy : LMonoTy := LMonoTy.arrow fieldDtTy LMonoTy.int
        let dtRankField : LExpr T.mono :=
          .app m (.op m (dtRankFuncName fieldDt.name) (.some fieldRankTy)) fieldBvar
        let ltTy : LMonoTy := LMonoTy.arrow LMonoTy.int (LMonoTy.arrow LMonoTy.int LMonoTy.bool)
        let ltExpr : LExpr T.mono :=
          .app m (.app m (.op m "Int.Lt" (.some ltTy)) dtRankField) dtRankConstr
        let fieldTys := (c.args.map (·.snd)).reverse
        let axiom_ := match fieldTys with
          | [] => ltExpr
          | ty :: rest =>
            let inner := LExpr.quant m .all "" (.some ty) dtRankConstr ltExpr
            rest.foldl (fun body ty =>
              .quant m .all "" (.some ty) (LExpr.noTrigger m) body
            ) inner
        acc ++ [axiom_]

/-- Generate the non-negativity axiom `∀ x. dtRank(x) >= 0` for a datatype.
    Trigger: `dtRank(x)` — fires only when dtRank terms already exist. -/
def mkDtRankNonNegAxiom {T : LExprParams} [Inhabited T.Metadata] [Inhabited T.IDMeta]
    (dt : LDatatype T.IDMeta) (m : T.Metadata) : LExpr T.mono :=
  let dtTy := dataDefault dt
  let rankTy : LMonoTy := LMonoTy.arrow dtTy LMonoTy.int
  let rankX : LExpr T.mono :=
    .app m (.op m (dtRankFuncName dt.name) (.some rankTy)) (.bvar m 0)
  let geTy : LMonoTy := LMonoTy.arrow .int (LMonoTy.arrow .int .bool)
  let geExpr : LExpr T.mono :=
    .app m (.app m (.op m "Int.Ge" (.some geTy)) rankX) (.intConst m 0)
  .quant m .all "" (.some dtTy) rankX geExpr

/-- Generate all dtRank axioms for a single datatype within a mutual block. -/
def mkDtRankAxioms {T : LExprParams} [Inhabited T.Metadata] [Inhabited T.IDMeta] [DecidableEq T.IDMeta]
    (dt : LDatatype T.IDMeta) (block : MutualDatatype T.IDMeta)
    (m : T.Metadata) : List (LExpr T.mono) :=
  mkDtRankNonNegAxiom dt m :: mkDtRankPerConstrAxioms dt block m

/-- Generate dtRank functions and axioms for all datatypes in a mutual block. -/
def mkDtRankDeclsForBlock {T : LExprParams} [Inhabited T.Metadata] [Inhabited T.IDMeta]
    [DecidableEq T.IDMeta]
    (block : MutualDatatype T.IDMeta) (m : T.Metadata)
    : List (LFunc T) × List (LExpr T.mono) :=
  let funcs := block.map fun dt => mkDtRankFunc dt
  let axioms := block.flatMap fun dt => mkDtRankAxioms dt block m
  (funcs, axioms)

end

end Lambda
