/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.IntBoolFactory
public import Strata.DL.Lambda.TypeFactory

/-!
## adtRank Axiom Generation for Termination Checking

For each ADT used as a decreasing measure, we generate:
1. An uninterpreted function `D..adtRank : D → Int`
2. Per-constructor axioms: for each constructor field of datatype type,
   `adtRank(field) < adtRank(C(fields...))`, with trigger `adtRank(C(fields...))`.
3. `adtRank(x) >= 0`, and `adtRank(x) >= 1` when `x` is not built by a
   constructor without a field of datatype type.

A value's height, counting only fields of the block's datatypes, satisfies
these axioms, and is `0` for a constructor without such fields: termination
checking uses `0` for the rank of such a value.
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
    let constrApp := c.args.foldlIdxVal (fun acc i _ =>
      .app m acc (.bvar m (numFields - 1 - i))
    ) (.op m c.name (.some constrTy))
    let adtRankTy := .arrow dtTy .int
    let adtRankConstr : LExpr T.mono :=
      .app m (.op m (adtRankFuncName dt.name) (.some adtRankTy)) constrApp
    let fields := (c.args.map (fun (id, ty) => (id.name, ty))).reverse
    (c.args.foldlIdxVal (init := []) fun acc i (_, fieldTy) =>
      match findDirectRecTy block fieldTy with
      | none => acc
      | some fieldDt =>
        let fieldBvar := .bvar m (numFields - 1 - i)
        let fieldRankTy := .arrow (dataDefault fieldDt) .int
        let adtRankField := .app m (.op m (adtRankFuncName fieldDt.name)
          (.some fieldRankTy)) fieldBvar
        let ltExpr := LExpr.mkApp m (@intLtFunc T).opExpr
          [adtRankField, adtRankConstr]
        let axiom_ := match fields with
          | (name, ty) :: rest =>
            let inner := .quant m .all name (.some ty) adtRankConstr ltExpr
            rest.foldl (fun body (name, ty) =>
              .quant m .all name (.some ty) (LExpr.noTrigger m) body
            ) inner
          | [] => ltExpr
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
  let geExpr := .mkApp m (@intGeFunc T).opExpr [rankX, .intConst m 0]
  .quant m .all "x" (.some dtTy) rankX geExpr

/-- Whether the constructor `c` has a field whose type is a datatype of `block`
    (`findDirectRecTy`), which is a field that gets a per-constructor axiom.
    The rank-`1` axiom and termination checking's rank `0` (see the module
    documentation) must both use this test, or the rank `0` is unsound.

    TODO: prove that these axioms are sound, by the model where a value's rank
    is its height, counting only fields of `block`'s datatypes: height satisfies
    every adtRank axiom, and is `0` exactly on the values built by constructors
    for which this test is false. -/
def LConstr.hasBlockField (block : MutualDatatype IDMeta) (c : LConstr IDMeta) : Bool :=
  c.args.any fun (_, ty) => (findDirectRecTy block ty).isSome

/-- Generate `∀ x. !(isC₁(x) || … || isCₙ(x)) ==> adtRank(x) >= 1`, where the
    `Cᵢ` are the constructors of `dt` without a field of a datatype of `block`,
    or nothing when every constructor is one of them. Trigger: `adtRank(x)`. -/
def mkAdtRankPosAxiom {T : LExprParams} [Inhabited T.Metadata] [Inhabited T.IDMeta]
    [DecidableEq T.IDMeta]
    (dt : LDatatype T.IDMeta) (block : MutualDatatype T.IDMeta) (m : T.Metadata) :
    List (LExpr T.mono) :=
  let dtTy := dataDefault dt
  if dt.constrs.all (!·.hasBlockField block) then [] else
  let testers : List (LExpr T.mono) := (dt.constrs.filter (!·.hasBlockField block)).map fun c =>
    .app m (.op m c.testerName (.some (.arrow dtTy .bool))) (.bvar m 0)
  let rankX := .app m (.op m (adtRankFuncName dt.name) (.some (.arrow dtTy .int))) (.bvar m 0)
  let geOne := .mkApp m (@intGeFunc T).opExpr [rankX, .intConst m 1]
  let body := match testers with
    | [] => geOne
    | t :: ts =>
      let isBase := ts.foldl (fun acc t => .mkApp m (@boolOrFunc T).opExpr [acc, t]) t
      .mkApp m (@boolImpliesFunc T).opExpr [.app m (@boolNotFunc T).opExpr isBase, geOne]
  [.quant m .all "x" (.some dtTy) rankX body]

/-- Generate all adtRank axioms for a single datatype within a mutual block. -/
def mkAdtRankAxioms {T : LExprParams} [Inhabited T.Metadata] [Inhabited T.IDMeta] [DecidableEq T.IDMeta]
    (dt : LDatatype T.IDMeta) (block : MutualDatatype T.IDMeta)
    (m : T.Metadata) : List (LExpr T.mono) :=
  mkAdtRankNonNegAxiom dt m :: mkAdtRankPerConstrAxioms dt block m ++ mkAdtRankPosAxiom dt block m

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
