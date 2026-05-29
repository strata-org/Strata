/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.CoreMatch.DDMTransform.Translate.Basic
public import Strata.Languages.CoreMatch.DDMTransform.Translate.Datatypes
public import Strata.Languages.CoreMatch.DDMTransform.Translate.Types
public import Strata.Languages.CoreMatch.DDMTransform.Translate.NaturalCata
public import Strata.Languages.CoreMatch.CoreMatch
public import Strata.Languages.CoreMatch.ToCore
public import Strata.Languages.CoreMatch.ArmCheck

/-!
Translate `CoreMatchDDM.Expr` AST nodes into `Core.Expression.Expr`.
Mutually recursive with the match-arm translators because
`match_expr` walks back into its arm bodies.
-/

namespace Strata.CoreMatch.Translate

open Lambda
open Strata.CoreMatchDDM

public section

mutual

partial def toCoreExpr (e : CoreMatchDDM.Expr SourceRange)
    : TransM Core.Expression.Expr := do
  let bin (op : Core.Expression.Expr) (a b : CoreMatchDDM.Expr SourceRange) :
      TransM Core.Expression.Expr :=
    return .app () (.app () op (← toCoreExpr a)) (← toCoreExpr b)
  match e with
  | .fvar m i =>
    let n ← getFVarName m i
    if (← StateT.get).recFns.contains n then
      throwAt m s!"non-structural use of recursive function '{n}': \
                   must apply directly to a recursive constructor field"
    return if (← getFVarIsOp i) then .op   () (mkIdent n) none
                                else .fvar () (mkIdent n) none
  | .bvar m i => getBVarExpr m i
  | .app m f a =>
    -- Try the natural-recursion rewrite first; otherwise reject any
    -- non-structural self-application before recursing into the args.
    if let some rewritten ← tryRecRewrite f a then return rewritten
    if let .fvar _ i := f then
      let s ← StateT.get
      if let some name := s.gctx.nameOf? i then
        if s.recFns.contains name then
          throwAt m s!"non-structural recursive call to '{name}': \
                       argument must be a recursive constructor field \
                       of the enclosing match"
    return .app () (← toCoreExpr f) (← toCoreExpr a)
  | .btrue _           => return LExpr.true ()
  | .bfalse _          => return LExpr.false ()
  | .natToInt _ ⟨_, n⟩ => return .intConst () (Int.ofNat n)
  | .not _ a           => return .app () Core.boolNotOp (← toCoreExpr a)
  | .and _ a b         => bin Core.boolAndOp     a b
  | .or _ a b          => bin Core.boolOrOp      a b
  | .implies _ a b     => bin Core.boolImpliesOp a b
  | .equiv _ a b       => bin Core.boolEquivOp   a b
  | .equal _ _ a b     => return .eq () (← toCoreExpr a) (← toCoreExpr b)
  | .not_equal _ _ a b => return .app () Core.boolNotOp
                                   (.eq () (← toCoreExpr a) (← toCoreExpr b))
  | .le _ _ a b        => bin Core.intLeOp a b
  | .lt _ _ a b        => bin Core.intLtOp a b
  | .ge _ _ a b        => bin Core.intGeOp a b
  | .gt _ _ a b        => bin Core.intGtOp a b
  | .neg_expr _ _ a    => return .app () Core.intNegOp (← toCoreExpr a)
  | .add_expr _ _ a b  => bin Core.intAddOp a b
  | .sub_expr _ _ a b  => bin Core.intSubOp a b
  | .mul_expr _ _ a b  => bin Core.intMulOp a b
  | .if _ _ c t f      => return .ite () (← toCoreExpr c) (← toCoreExpr t) (← toCoreExpr f)
  | .match_expr m scrutTy resTy scrut headPat headBody tailArms => do
    let scrutMTy  ← toCoreMonoType scrutTy
    let dtName    ← expectDatatype m scrutMTy
    let resultMTy ← toCoreMonoType resTy
    let dt        ← lookupLDatatype dtName
    let scrutE    ← toCoreExpr scrut
    let headArm   ← translateExprArm dtName resultMTy headPat headBody
    let tailArms  ← collectTailArms dtName resultMTy tailArms
    let arms      := headArm :: tailArms
    let issues    := ArmCheck.check dt (arms.map ArmCheck.MArm.key)
    unless issues.isEmpty do
      throw <| .fromMessage
        s!"match on '{dtName}': {String.intercalate "; " (issues.map ArmCheck.ArmIssue.format)}"
    return Strata.CoreMatch.ToCore.compileMExprWith
      (fun n => if n == dtName then some dt else none)
      (.matchE (.core scrutE) dtName arms)
  | _ => throw <| .fromMessage s!"unsupported CoreMatch expression: {repr e}"

/-- Translate one arm `pat => body` into the eliminator's case
lambda for this constructor. -/
partial def translateExprArm
    (dtName : String) (resultMTy : LMonoTy)
    (pat : MatchPat SourceRange) (body : CoreMatchDDM.Expr SourceRange)
    : TransM Strata.CoreMatch.MArm := do
  match pat with
  | .matchPat_wild _ =>
    return .wild (.core (← toCoreExpr body))
  | .matchPat_ctor _ ⟨_, ctor⟩ vs =>
    let binders ← (matchPatVarsToList vs).mapM fun
      | .matchPatVar_typed _ ⟨_, n⟩ ty => return (n, ← toCoreMonoType ty)
    let shape ← classifyArm dtName ctor (binders.map (·.2))
    let st ← StateT.get
    -- Stage rec-rewrites for natural arms; cata/unknown arms run with
    -- an empty map and translate verbatim.
    let recRewrites := match shape with
      | .natural recIdxs =>
          naturalRecRewrites st.recFns recIdxs st.bvars.size
      | _ => []
    let bodyE ← withBoundBVars (binders.map (·.1)) <|
      withRecRewrites recRewrites (toCoreExpr body)
    let (caseBinders, caseBody) := match shape with
      | .natural recIdxs =>
          desugarNaturalToCata resultMTy recIdxs.length binders bodyE
      | _ => (binders, bodyE)
    let caseFn := LExpr.absMulti () (caseBinders.map (·.2)) caseBody
    return .ctor ctor (.core caseFn)

partial def collectTailArms
    (dtName : String) (resultMTy : LMonoTy)
    : MatchExprTailArmList SourceRange → TransM (List Strata.CoreMatch.MArm)
  | .matchExprTailArmList_nil _ => return []
  | .matchExprTailArmList_cons _ (.matchExprTailArm_mk _ pat body) rest => do
    let arm  ← translateExprArm dtName resultMTy pat body
    let rest ← collectTailArms dtName resultMTy rest
    return arm :: rest

end

end

end Strata.CoreMatch.Translate
