/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.CoreMatch.DDMTransform.Translate.Basic
public import Strata.Languages.CoreMatch.DDMTransform.Translate.Datatypes
public import Strata.Languages.CoreMatch.DDMTransform.Translate.Types
public import Strata.Languages.CoreMatch.DDMTransform.Translate.Expressions
public import Strata.Languages.CoreMatch.CoreMatch
public import Strata.Languages.CoreMatch.ArmCheck
public import Strata.Languages.Core.Statement

/-!
Translate statement-level forms. Statement-position `match` lowers
to a nested-if chain over the auto-generated testers, with pattern
binders prepended as `var b : T := D..fᵢ(scrut);` init statements.
-/

namespace Strata.CoreMatch.Translate

open Lambda Imperative
open Strata.CoreMatchDDM

public section

def freshLabel (m : SourceRange) (prefix_ : String)
    (l? : Option (Label SourceRange)) : TransM String := do
  match l? with
  | some (.label _ ⟨_, l⟩) => return l
  | none =>
    let i := (← StateT.get).labelCounter
    modify fun s => { s with labelCounter := i + 1 }
    return s!"{prefix_}_{i}_{m.start}"

private def toCoreCondBool (c : ExprOrNondet SourceRange)
    : TransM (Imperative.ExprOrNondet Core.Expression) := do
  match c with
  | .condDet _ e  => return .det (← toCoreExpr e)
  | .condNondet _ => return .nondet

/-- Build the binder-init statements for a constructor arm:
`var b₁ : T₁ := D..f₁(scrut); …`. Falls back to positional `f0, f1,
…` names when the cached field list disagrees with the binder count;
downstream type-checking surfaces the real problem. -/
private def buildArmInits
    (dtName ctor : String) (binders : List (String × LMonoTy))
    (scrut : Core.Expression.Expr) : TransM (List Core.Statement) := do
  let cachedFields := (← lookupCtor dtName ctor).getD []
  let names :=
    if cachedFields.length == binders.length then cachedFields
    else (List.range binders.length).map (s!"f{·}")
  return (binders.zip names).map fun ((b, ty), fname) =>
    let acc : Core.Expression.Expr :=
      .app () (.op () ⟨dtName ++ ".." ++ fname, ()⟩ none) scrut
    Core.Statement.init (mkIdent b) (.forAll [] ty) (.det acc) {}

mutual

partial def toMBlock : Block SourceRange → TransM (List Strata.CoreMatch.MStmt)
  | .block _ ⟨_, ss⟩ => return (← ss.toList.mapM toMStmt).flatten

/-- Translate a block to plain Core statements. Inner `matchStmt`
wrappers are dropped here; they are lowered by the procedure-level
pass that has access to the full declaration scope. -/
partial def toCoreBlock (b : Block SourceRange) : TransM (List Core.Statement) := do
  return (← toMBlock b).flatMap fun
    | .core c          => [c]
    | .matchStmt _ _ _ => []

partial def matchArmToMStmtArm
    (dtName : String) (scrut : Core.Expression.Expr)
    : MatchStmtArm SourceRange → TransM Strata.CoreMatch.MStmtArm
  | .matchStmtArm_mk _ (.matchPat_wild _) body =>
    return .wild (← toCoreBlock body)
  | .matchStmtArm_mk _ (.matchPat_ctor _ ⟨_, ctor⟩ vs) body => do
    let binders ← (matchPatVarsToList vs).mapM fun
      | .matchPatVar_typed _ ⟨_, n⟩ ty => return (n, ← toCoreMonoType ty)
    let inits ← buildArmInits dtName ctor binders scrut
    let body  ← withBVars (binders.map (·.1)) (toCoreBlock body)
    return .ctor ctor (inits ++ body)

partial def toMStmt : Statement SourceRange → TransM (List Strata.CoreMatch.MStmt)
  | .initStatement _ ty ⟨_, n⟩ e => do
    let mty ← toCoreMonoType ty
    let rhs ← toCoreExpr e
    -- Bring the new binder into scope for the rest of the enclosing block.
    modify fun s => { s with bvars := s.bvars.push (.fvar () (mkIdent n) none) }
    return [.core <| Core.Statement.init (mkIdent n) (.forAll [] mty) (.det rhs) {}]
  | .assign _ _ lhs rhs => do
    let n ← match lhs with
      | .lhsIdent _ ⟨_, n⟩ => pure n
      | .lhsArray _ _ _ _  =>
        throw <| .fromMessage "array assignment not yet supported in CoreMatch"
    return [.core <| Core.Statement.set (mkIdent n) (← toCoreExpr rhs) {}]
  | .assume m ⟨_, l?⟩ e => do
    let lbl ← freshLabel m "assume" l?
    return [.core <| Core.Statement.assume lbl (← toCoreExpr e) {}]
  | .assert m _ ⟨_, l?⟩ e => do
    let lbl ← freshLabel m "assert" l?
    return [.core <| Core.Statement.assert lbl (← toCoreExpr e) {}]
  | .if_statement _ c t f => do
    let cond     ← toCoreCondBool c
    let thenBlk  ← toCoreBlock t
    let elseBlk  ← match f with
      | .else0 _   => pure []
      | .else1 _ b => toCoreBlock b
    return [.core <| Imperative.Stmt.ite cond thenBlk elseBlk {}]
  | .match_statement m scrutTy scrut arms => do
    let scrutMTy ← toCoreMonoType scrutTy
    let dtName   ← expectDatatype m scrutMTy
    let dt       ← lookupLDatatype dtName
    let scrutE   ← toCoreExpr scrut
    let mArms    ← (matchStmtArmsToList arms).mapM (matchArmToMStmtArm dtName scrutE)
    let issues   := ArmCheck.check dt (mArms.map ArmCheck.MStmtArm.key)
    unless issues.isEmpty do
      throw <| .fromMessage
        s!"match on '{dtName}': {String.intercalate "; " (issues.map ArmCheck.ArmIssue.format)}"
    return [.matchStmt scrutE dtName mArms]
  | .block_statement _ ⟨_, label⟩ b => do
    let inner ← withBVars [] (toCoreBlock b)
    return [.core <| Imperative.Stmt.block label inner {}]
  | .varStatement _ _ => return []
  | s => throw <| .fromMessage s!"unsupported CoreMatch statement: {repr s}"

end

end

end Strata.CoreMatch.Translate
