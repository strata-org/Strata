/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.Factory
public import Strata.DL.Lambda.TypeFactory

/-!
## adtRank Axiom Generation for Termination Checking

For each ADT used as a decreasing measure, we generate:
1. An uninterpreted function `D..adtRank : D → Int`
2. Per-constructor axioms: for each constructor field of datatype type,
   `adtRank(field) < adtRank(C(fields...))`, with trigger `adtRank(C(fields...))`.
-/

namespace Lambda

public section

open Strata.DL.Util (FuncAttr TyIdentifier)

def adtRankSuffix : String := "..adtRank"

def adtRankFuncName (dtName : String) : String := s!"{dtName}{adtRankSuffix}"

/-- Create the `D..adtRank : D → Int` uninterpreted function declaration. -/
def mkAdtRankFunc {T : LExprParams} [Inhabited T.IDMeta] (dt : LDatatype T.IDMeta) : LFunc T :=
  { name := adtRankFuncName dt.name
    typeArgs := dt.typeArgs
    inputs := [(⟨"x", default⟩, dataDefault dt)]
    output := LMonoTy.int }

/-- Generate per-constructor adtRank axioms for a single datatype.
    For each constructor `C` and each field of datatype type within the
    mutual block `block`, generates:
      `∀ fields. D'..adtRank(field_i) < D..adtRank(C(fields...))`
    with trigger `D..adtRank(C(fields...))`.

    The `block` parameter determines which field types are considered
    "recursive" (i.e., belong to the mutual datatype block). -/
def mkAdtRankPerConstrAxioms {T : LExprParams} [Inhabited T.Metadata] [Inhabited T.IDMeta] [DecidableEq T.IDMeta]
    (dt : LDatatype T.IDMeta) (block : MutualDatatype T.IDMeta)
    (m : T.Metadata) : List (LExpr T.mono) :=
  let dtTy := dataDefault dt
  dt.constrs.flatMap fun c =>
    let numFields := c.args.length
    let constrTy := LMonoTy.mkArrow' dtTy (c.args.map (·.2))
    let constrApp := c.args.foldlIdx (fun acc i _ =>
      .app m acc (.bvar m (numFields - 1 - i))
    ) (.op m c.name (.some constrTy))
    let adtRankTy := .arrow dtTy .int
    let adtRankConstr : LExpr T.mono :=
      .app m (.op m (adtRankFuncName dt.name) (.some adtRankTy)) constrApp
    let fieldTys := (c.args.map (·.snd)).reverse
    (c.args.foldlIdx (init := []) fun acc i (_, fieldTy) =>
      match block.find? (fun d => fieldTy == dataDefault d) with
      | none => acc
      | some fieldDt =>
        let fieldBvar := .bvar m (numFields - 1 - i)
        let fieldRankTy := .arrow (dataDefault fieldDt) .int
        let adtRankField := .app m (.op m (adtRankFuncName fieldDt.name)
          (.some fieldRankTy)) fieldBvar
        let ltTy := .arrow .int (.arrow .int .bool)
        let ltExpr := LExpr.mkApp m (.op m "Int.Lt" (.some ltTy))
          [adtRankField, adtRankConstr]
        let axiom_ := match fieldTys with
          | [] => ltExpr
          | ty :: rest =>
            let inner := .quant m .all "" (.some ty) adtRankConstr ltExpr
            rest.foldl (fun body ty =>
              .quant m .all "" (.some ty) (LExpr.noTrigger m) body
            ) inner
        axiom_ :: acc
    ).reverse

/-- Generate the non-negativity axiom `∀ x. adtRank(x) >= 0` for a datatype.
    Trigger: `adtRank(x)` — fires only when adtRank terms already exist. -/
def mkAdtRankNonNegAxiom {T : LExprParams} [Inhabited T.Metadata] [Inhabited T.IDMeta]
    (dt : LDatatype T.IDMeta) (m : T.Metadata) : LExpr T.mono :=
  let dtTy := dataDefault dt
  let rankTy := .arrow dtTy .int
  let rankX := .app m (.op m (adtRankFuncName dt.name) (.some rankTy))
    (.bvar m 0)
  let geTy := .arrow .int (.arrow .int .bool)
  let geExpr := .mkApp m (.op m "Int.Ge" (.some geTy)) [rankX, .intConst m 0]
  .quant m .all "" (.some dtTy) rankX geExpr

/-- Generate all adtRank axioms for a single datatype within a mutual block. -/
def mkAdtRankAxioms {T : LExprParams} [Inhabited T.Metadata] [Inhabited T.IDMeta] [DecidableEq T.IDMeta]
    (dt : LDatatype T.IDMeta) (block : MutualDatatype T.IDMeta)
    (m : T.Metadata) : List (LExpr T.mono) :=
  mkAdtRankNonNegAxiom dt m :: mkAdtRankPerConstrAxioms dt block m

/-- Generate adtRank functions and axioms for all datatypes in a mutual block. -/
def mkAdtRankDeclsForBlock {T : LExprParams} [Inhabited T.Metadata] [Inhabited T.IDMeta]
    [DecidableEq T.IDMeta]
    (block : MutualDatatype T.IDMeta) (m : T.Metadata)
    : List (LFunc T) × List (LExpr T.mono) :=
  let funcs := block.map fun dt => mkAdtRankFunc dt
  let axioms := block.flatMap fun dt => mkAdtRankAxioms dt block m
  (funcs, axioms)

end

end Lambda
