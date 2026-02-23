/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.CoreGen
import Strata.Languages.Core.Procedure
import Strata.Util.Tactics

namespace Core

namespace OldExpressions

open Lambda.LExpr.SyntaxMono Lambda.LTy.Syntax Core.Syntax

/-! ## Old Expressions in Strata Core

The `old e` expression in Strata Core follows the syntax of the old expression
in Boogie. Specifically, in Section 4.3 in "This is Boogie 2":

"Postconditions and procedure implementations are two-state contexts. This means
that it is possible to refer to two different values of each variable. In a
postcondition, the two states are the pre- and post-states of the procedure's
invocations, and in a procedure implementation, the two states are the pre-state
of the procedure and the current state. In both cases, the pre-state value of an
expression is denoted by enclosing it as the argument to `old`. For example, in
the postcondition of a procedure, if `x` and `y` are global variables, then
`old(x + y)` refers to the value of `x + y` on entry to the procedure, whereas
`x + y` not enclosed inside any old expression denotes the value of `x + y` on
exit from the procedure.

Only global variables are affected by `old` expressions. For example, if `a` is
a global variable, `b` is a local variable, and `c` is an out-parameter, then
the use of `old(a + b + c)` in a procedure implementation is equivalent to
`old(a) + b + c`. Stated differently, `old` distributes to the leaves of
expressions and is the identity for every leaf expression that is not a global
variable. Nested occurrences of `old` do not further change the meaning of the
expression; `old(old(E))` is equivalent to just `old(E)`. In other words, `old`
is idempotent."

In our implementation, function `normalizeOldExpr` removes redundant
applications of `old` and distributes `old` to the leaf variables of an
expression. Let us suppose we have normalized the body and postconditions of a
procedure `P`. No `old` expressions are allowed in `P`'s preconditions. Now we
are only left with `old(var)` expressions:

1. Any `old(var)` in `P`'s body and postconditions can be replaced by the
   initial value of `var` (i.e., at the beginning of `P`).

2. Any `old(var)` in the postcondition of a procedure `Q` that is called in `P`
   can be replaced by the value of `var` immediately before `Q`'s call.
-/
@[match_pattern]
def oldExpr
  (mApp: ExpressionMetadata)
  (mOp: ExpressionMetadata)
  {tyold : Option Lambda.LMonoTy}
  (e : Expression.Expr)
  : Expression.Expr
  :=
  .app mApp (.op mOp (CoreIdent.unres "old") tyold) e

@[match_pattern]
def oldVar
  (mApp: ExpressionMetadata)
  (mOp: ExpressionMetadata)
  (mVar: ExpressionMetadata)
  {tyold : Option Lambda.LMonoTy}
  (v : Expression.Ident)
  {tyv : Option Lambda.LMonoTy}
  : Expression.Expr
  := @oldExpr mApp mOp tyold (.fvar mVar v tyv)

inductive IsOldPred : Expression.Expr → Prop where
  | oldPred : IsOldPred (.op m (CoreIdent.unres "old") ty)

def IsOldPred.decidablePred (e : Expression.Expr): Decidable (IsOldPred e) :=
  match He : e with
  | .op m id ty =>
    if Hid : (id = "old") then
      by simp [Hid]; exact isTrue oldPred
    else
      by apply isFalse; intros Hold; cases Hold; contradiction
  | .const _ _ | .bvar _ _ | .fvar _ _ _ | .abs _ _ _
  | .quant _ _ _ _ _ | .app _ _ _ | .ite _ _ _ _  | .eq _ _ _ =>
    by apply isFalse; intros Hold; cases Hold

inductive IsFvar : Expression.Expr → Prop where
  | fvar : IsFvar (.fvar () v ty)

def IsFvar.decidablePred (e : Expression.Expr): Decidable (IsFvar e) :=
  match He : e with
  | .fvar _ v ty => isTrue fvar
  | .op _ _ _ | .const _ _ | .bvar _ _ | .abs _ _ _
  | .quant _ _ _ _ _ | .app _ _ _ | .ite _ _ _ _  | .eq _ _ _ =>
    by apply isFalse; intros H; cases H
/--
Normalize an expression containing applications of the `old` function by
distributing it to the leaf variables of an expression and by removing nested
occurrences.

E.g., `old(a + b + c) == old(a) + old(b) + old(c)` and `old(old(g)) == old(g)`.
-/
def normalizeOldExpr (e : Expression.Expr) (inOld : Bool := false)
  : Expression.Expr :=
  match _He : e with
  | .fvar _ v ty =>
    if inOld then
      @oldVar e.metadata e.metadata e.metadata none v ty -- ignoring the operation type
    else e
  | .const _ _ | .bvar _ _ | .op _ _ _ => e
  | .abs m ty e' => .abs m ty (normalizeOldExpr e' inOld)
  | .quant m qk ty tr' e' => .quant m qk ty (normalizeOldExpr tr' inOld) (normalizeOldExpr e' inOld)
  | .app m e1 e2 =>
    match _He1 : e1 with
    | .op m o ty =>
      if _Hop : o = "old" then
        -- is an old var or old expr
        match _He2 : e2 with
        | .fvar _ _ _ => e
        | e' => normalizeOldExpr e' true
      else
        .app m (normalizeOldExpr e1 inOld) (normalizeOldExpr e2 inOld)
    | _ => .app m (normalizeOldExpr e1 inOld) (normalizeOldExpr e2 inOld)
  | .ite m c t f => .ite m (normalizeOldExpr c inOld)
                      (normalizeOldExpr t inOld) (normalizeOldExpr f inOld)
  | .eq m e1 e2 => .eq m (normalizeOldExpr e1 inOld) (normalizeOldExpr e2 inOld)
    termination_by sizeOf e
  decreasing_by all_goals (simp[sizeOf, Lambda.LExpr.sizeOf]; try term_by_mem)

def normalizeOldExprs (sm : List Expression.Expr) :=
  sm.map normalizeOldExpr

def normalizeOldCheck (c : Procedure.Check) : Procedure.Check :=
  { c with expr := normalizeOldExpr c.expr }

def normalizeOldChecks (c : ListMap String Procedure.Check) : ListMap String Procedure.Check :=
  c.map (λ p ↦ (p.fst, normalizeOldCheck p.snd))

/--
Checks if `e` contains an application of the `old` function.

This function is agnostic of old expression normalization (see
`normalizeOldExpr`). Also see `extractOldExprVars` that extracts `var` from
`old(var)` after normalization.
-/
def containsOldExpr (e : Expression.Expr) : Bool :=
  match e with
  | .op _ (CoreIdent.unres "old") _ => true
  | .op _ _ _ => false
  | .const _ _ | .bvar _ _ | .fvar _ _ _ => false
  | .abs _ _ e' => containsOldExpr e'
  | .quant _ _ _ tr' e' => containsOldExpr tr' || containsOldExpr e'
  | .app _ e1 e2 => containsOldExpr e1 || containsOldExpr e2
  | .ite _ c t f => containsOldExpr c || containsOldExpr t || containsOldExpr f
  | .eq _ e1 e2 => containsOldExpr e1 || containsOldExpr e2

/--
Get a list of original global variable names that are referred to in an
`old(...)` expression. Note that `expr` below should be normalized by
`normalizeOldExpr`.
-/
def extractOldExprVars (expr : Expression.Expr)
  : List Expression.Ident := match expr with
  | .const _ _ | .bvar _ _ | .fvar _ _ _ | .op _ _ _ => []
  | .abs _ _ e => extractOldExprVars e
  | .quant _ _ _ tr e => extractOldExprVars tr ++ extractOldExprVars e
  | .app _ e1 e2 => match e1, e2 with
    | .op _ (CoreIdent.unres "old") _, .fvar _ v _ => [v]
    | .op _ (CoreIdent.unres "old") _, _ => panic! s!"Old expression {expr} not normalized"
    | e1', e2' => extractOldExprVars e1' ++ extractOldExprVars e2'
  | .ite _ c t e => extractOldExprVars c ++ extractOldExprVars t ++ extractOldExprVars e
  | .eq _ e1 e2 => extractOldExprVars e1 ++ extractOldExprVars e2

/--
Substitute `old(var)` in expression `e` with `s`.
-/
def substOld (var : Expression.Ident) (s e : Expression.Expr) :
  Expression.Expr :=
  match e with
  | .const _ _ | .fvar _ _ _ | .bvar _ _ | .op _ _ _ => e
  | .abs m ty e' => .abs m ty (substOld var s e')
  | .quant m qk ty tr' e' => .quant m qk ty (substOld var s tr') (substOld var s e')
  | .app m e1 e2 =>
    match e1, e2 with
    | .op _ (CoreIdent.unres "old") _, .fvar _ x _ =>
      -- NOTE: We rely on the typeChecker to normalize `e` ensure that `old` is
      -- only used with an `fvar`.
      if x == var
        -- substitute, if should be substituted
        then s
        else e
    | _, _ => .app m (substOld var s e1) (substOld var s e2)
  | .ite m c t f => .ite m (substOld var s c)
                      (substOld var s t) (substOld var s f)
  | .eq m e1 e2 => .eq m (substOld var s e1) (substOld var s e2)

/--
For each `(var, val)` in `sm`, substitute `old(var)` in expression `e` with
`val`.
-/
def substsOldExpr (sm : Map Expression.Ident Expression.Expr) (e : Expression.Expr)
  : Expression.Expr :=
  if sm.isEmpty then e else
  match e with
  | .const _ _ | .fvar _ _ _ | .bvar _ _ | .op _ _ _ => e
  | .abs m ty e' => .abs m ty (substsOldExpr sm e')
  | .quant m qk ty tr' e' => .quant m qk ty (substsOldExpr sm tr') (substsOldExpr sm e')
  | .app m e1 e2 =>
    match e1, e2 with
    | .op _ (CoreIdent.unres "old") _, .fvar _ x _ =>
      match sm.find? x with
      | some s => s
      | none => e
    | _, _ => .app m (substsOldExpr sm e1) (substsOldExpr sm e2)
  | .ite m c t f => .ite m (substsOldExpr sm c)
                      (substsOldExpr sm t) (substsOldExpr sm f)
  | .eq m e1 e2 => .eq m (substsOldExpr sm e1) (substsOldExpr sm e2)

/--
For each `(var, val)` in `sm`, substitute `old(var)` in each expression `es`
with `val`.
-/
def substsOldExprs (sm : Map Expression.Ident Expression.Expr) (es : List Expression.Expr) :=
  es.map $ substsOldExpr sm

theorem substsOldExpr_singleton: substsOldExpr [(var,s)] e = substOld var s e := by
  induction e <;> simp [substsOldExpr, substOld, Map.isEmpty, *]
  split <;> simp_all;
  simp [Map.find?]
  split <;> simp_all
  intro h; rw [Eq.comm] at h
  contradiction

theorem substOldExpr_nil: OldExpressions.substsOldExpr [] e = e := by
  unfold OldExpressions.substsOldExpr
  simp [Map.isEmpty]

/--
For each `(var, expr)` pair in `sm`, substitute `old(var)` with `expr` in
`conds`.
-/
protected def substsOldInProcChecks {Ty}
  (sm : List ((Expression.Ident × Option Ty) × Expression.Expr))
  (conds : Map String Procedure.Check) :
  Map String Procedure.Check :=
  let sm_map := sm.map (fun ((e1, _), e2) => (e1, e2))
  conds.map (fun (label, c) =>
                 (label, { c with expr := substsOldExpr sm_map c.expr }))


protected def substsOldChecks (sm : Map Expression.Ident Expression.Expr)
  (conds : ListMap String Procedure.Check) :
  ListMap Expression.Ident Procedure.Check :=
  conds.map (fun (label, c) =>
                 (label, { c with expr := substsOldExpr sm c.expr }))

/-- Old predicate can only apply to var
    unapplied old predicates are ignored
e.g. old(true) should not satisfy the constraint
e.g. What about old(·) that is not applied to anything?
     It is normalized, but when it is applied to an expression, it is not
e.g. What if lhs is an abstraction that can reduce to old(·)?
     ((λ _ ↦ old(·)) true)(a + b)
     when normalizing the above expression, this doesn't change, and thus it should be considered normalized
 -/
inductive NormalizedOldExpr : Expression.Expr → Prop where
  -- | oldVar : NormalizedOldExpr (@oldVar tyOld v ty)
  | const :  NormalizedOldExpr (.const _ _)
  | op :     NormalizedOldExpr (.op _ _ _)
  | bvar :   NormalizedOldExpr (.bvar _ _)
  | fvar :   NormalizedOldExpr (.fvar _ _ _)
  | abs :    NormalizedOldExpr e →
             NormalizedOldExpr (.abs m ty e)
  | quant :  NormalizedOldExpr tr →
             NormalizedOldExpr e →
             NormalizedOldExpr (.quant m k ty tr e)
  | app :    NormalizedOldExpr fn →
             NormalizedOldExpr e →
             (IsOldPred fn → IsFvar e) →
             NormalizedOldExpr (.app m fn e)
  | ite :    NormalizedOldExpr c →
             NormalizedOldExpr t →
             NormalizedOldExpr e →
             NormalizedOldExpr (.ite m c t e)
  | eq  :    NormalizedOldExpr e1 →
             NormalizedOldExpr e2 →
             NormalizedOldExpr (.eq m e1 e2)

inductive ValidExpression : Expression.Expr → Prop where
  | const :  ValidExpression (.const _ _)
  | op :     ValidExpression (.op _ _ _)
  | bvar :   ValidExpression (.bvar _ _)
  | fvar :   ValidExpression (.fvar _ _ _)
  | abs :    ValidExpression e →
             ValidExpression (.abs m ty e)
  | quant :  ValidExpression tr → ValidExpression e →
             ValidExpression (.quant m k ty tr e)
  | app :    ValidExpression fn →
             ValidExpression e →
             ¬ IsOldPred e →
             ValidExpression (.app m fn e)
  | ite :    ValidExpression c →
             ValidExpression t →
             ValidExpression e →
             ValidExpression (.ite m c t e)
  | eq  :    ValidExpression e1 →
             ValidExpression e2 →
             ValidExpression (.eq m e1 e2)

-- This is not a ValidExpression
-- #eval normalizeOldExpr eb[((~old ~old) (~old (a b)))]

-- -- This is a ValidExpression
-- #eval normalizeOldExpr eb[(~old (~old (a b)))]

theorem IsOldPredNormalizeTrueIff :
  IsOldPred (normalizeOldExpr e true) ↔
  IsOldPred (normalizeOldExpr e) := by
apply Iff.intro
. intros Hold
  cases e <;> try simp [normalizeOldExpr] at * <;> try cases Hold
  . constructor
  . next fn e =>
    cases fn <;> try simp [normalizeOldExpr] at * <;> try cases Hold
    unfold  normalizeOldExpr at Hold
    split at Hold <;> simp_all
    split at Hold <;> simp_all
    split at Hold <;> simp_all
    . cases Hold
    . unfold normalizeOldExpr
      split <;> simp_all
    . simp [normalizeOldExpr] at Hold
      cases Hold
. intros Hold
  cases e <;> try simp [normalizeOldExpr] at * <;> try cases Hold
  . constructor
  . next fn e =>
    cases fn <;> try simp [normalizeOldExpr] at * <;> try cases Hold
    unfold normalizeOldExpr at Hold
    split at Hold <;> simp_all
    split at Hold <;> simp_all
    split at Hold <;> simp_all
    . cases Hold
    . unfold normalizeOldExpr
      split <;> simp_all
    . simp [normalizeOldExpr] at Hold
      cases Hold

theorem IsOldPredNormalize :
  ValidExpression e →
  IsOldPred (normalizeOldExpr e) →
  IsOldPred e := by
  intros Hval Hold
  induction e <;> try simp [normalizeOldExpr] at Hold <;> cases Hold
  . constructor
  . next fn e fn_ih e_ih =>
    by_cases IsOldPred fn
    case pos Hpos =>
      cases Hpos
      by_cases IsFvar e
      case pos Hpos' =>
        cases Hpos'
        simp [normalizeOldExpr] at Hold
        cases Hold
      case neg Hneg' =>
        unfold CoreIdent.unres at *
        unfold normalizeOldExpr at Hold
        unfold CoreIdent.unres at *
        split at Hold <;> simp_all
        split at Hold <;> simp_all
        unfold normalizeOldExpr at Hold
        split at Hold <;> simp_all <;> try cases Hold
        cases Hval
        next _ _ H =>
          exfalso
          apply H
          constructor
        split at Hold <;> simp_all <;> try cases Hold
        split at Hold <;> try cases Hold
        split at Hold <;> try cases Hold
        cases Hval
        next Hval1 Hval2 Hnold =>
        exfalso
        apply Hnold
        apply e_ih <;> try assumption
        simp [normalizeOldExpr]
        simp_all
    case neg Hneg =>
      by_cases IsOldPred fn <;> simp_all
      unfold normalizeOldExpr at Hold
      split at Hold <;> try cases Hold
      split at Hold <;> try cases Hold
      split at Hold <;> try cases Hold
      cases Hval
      next Hval1 Hval2 Hnold =>
      exfalso
      apply Hnold
      apply e_ih <;> try assumption
      exact IsOldPredNormalizeTrueIff.mp Hold

/--
the inverse is not true, because e could be a single .fvar
-/
theorem IsFvarNormalizeTrue :
  IsFvar (normalizeOldExpr e true) →
  IsFvar (normalizeOldExpr e) := by
  intros Hfvar
  cases e <;> try simp [normalizeOldExpr] at * <;> try cases Hfvar
  . next fn e =>
    cases fn <;> try simp [normalizeOldExpr] at * <;> try cases Hfvar
    unfold normalizeOldExpr at Hfvar
    split at Hfvar <;> simp_all
    split at Hfvar <;> simp_all
    split at Hfvar <;> simp_all
    . cases Hfvar
    . unfold normalizeOldExpr
      split <;> simp_all
    . simp [normalizeOldExpr] at Hfvar
      cases Hfvar

/--
Problem: e = old (e1 (fvar var))
the premise with false flag would be normalized
When e is an application inside an old predicate,
-/
theorem normalizedOldExprTrueSound :
  ValidExpression e →
  NormalizedOldExpr (normalizeOldExpr e) →
  NormalizedOldExpr (normalizeOldExpr e true) := by
intros Hval Hnorm
induction e <;> try simp [normalizeOldExpr] at * <;> try constructor <;> try assumption
case fvar name ty =>
  constructor
case fvar name ty =>
  intros Hold
  constructor
case abs ty e e_ih =>
  apply e_ih
  . cases Hval <;> assumption
  . cases Hnorm <;> assumption
case quant k ty tr e tr_ih e_ih =>
  . apply tr_ih
    . cases Hval <;> assumption
    . cases Hnorm <;> assumption
case quant k ty tr e tr_ih e_ih =>
  . apply e_ih
    . cases Hval <;> assumption
    . cases Hnorm <;> assumption

case app fn e fn_ih e_ih =>
  unfold normalizeOldExpr
  split <;> simp_all
  split <;> try simp_all
  split <;> simp_all
  . constructor
    . constructor
    . constructor
    . intros Hold
      constructor
  . unfold normalizeOldExpr at Hnorm
    split at Hnorm <;> simp_all
  . constructor
    . simp [normalizeOldExpr]; constructor
    . apply e_ih
      cases Hval <;> assumption
      unfold normalizeOldExpr at Hnorm
      split at Hnorm <;> simp_all
      simp [normalizeOldExpr] at Hnorm
      next o ty o' ty' _he h heq =>
      generalize Hop : (Lambda.LExpr.op () o' ty') = op at Hnorm
      generalize Hne : (normalizeOldExpr e) = ne at *
      cases Hnorm <;> simp_all
    . intros Hold
      simp [normalizeOldExpr] at Hold
      cases Hold
      contradiction
  . constructor
    . apply fn_ih
      cases Hval <;> assumption
      unfold normalizeOldExpr at Hnorm
      split at Hnorm <;> simp_all
      cases Hnorm <;> simp_all
    . apply e_ih
      cases Hval <;> assumption
      unfold normalizeOldExpr at Hnorm
      split at Hnorm <;> simp_all
      cases Hnorm <;> simp_all
    . intros Hold
      unfold normalizeOldExpr at Hnorm
      split at Hnorm <;> simp_all
      . cases Hnorm <;> simp_all
        next Hnorm1 Hnorm2 Hold' =>
          specialize Hold' ?_
          exact IsOldPredNormalizeTrueIff.mp Hold
          have Hold' := IsOldPredNormalizeTrueIff.mp Hold
          cases Hval with
          | app Hval1 Hval2 Hnold =>
            have Hold'' := IsOldPredNormalize Hval1 Hold'
            cases Hold'' <;> simp [CoreIdent.unres] at *
case ite c t e c_ih t_ih e_ih =>
  apply c_ih
  cases Hval <;> assumption
  cases Hnorm <;> assumption
case ite c t e c_ih t_ih e_ih =>
  apply t_ih
  cases Hval <;> assumption
  cases Hnorm <;> assumption
case ite c t e c_ih t_ih e_ih =>
  apply e_ih
  cases Hval <;> assumption
  cases Hnorm <;> assumption
case eq e1 e2 e1_ih e2_ih =>
  apply e1_ih
  cases Hval <;> assumption
  cases Hnorm <;> assumption
case eq e1 e2 e1_ih e2_ih =>
  apply e2_ih
  cases Hval <;> assumption
  cases Hnorm <;> assumption

theorem normalizeOldExprSound :
  ValidExpression e →
  NormalizedOldExpr (normalizeOldExpr e) := by
  intros Hvalid
  induction e <;> try simp [normalizeOldExpr] <;> try constructor <;> simp_all
  case app fn e fn_ih e_ih =>
    unfold normalizeOldExpr
    split <;> simp_all
    . -- old var
      next o ty =>
      split <;> try simp_all
      split <;> simp_all
      . constructor
        . constructor
        . constructor
        . intros Hold
          constructor
      . -- general old expressions
        next e2 _ _ =>
        -- e2 not fvar, e2 not op
        apply normalizedOldExprTrueSound
        . cases Hvalid <;> assumption
        . apply e_ih
          cases Hvalid <;> assumption
      . constructor
        . simp [normalizeOldExpr]
          constructor
        . apply e_ih
          cases Hvalid <;> assumption
        . intros Hold
          simp [normalizeOldExpr] at Hold
          cases Hold
          contradiction
    . -- not old var
      constructor
      . apply fn_ih
        cases Hvalid <;> assumption
      . apply e_ih
        cases Hvalid <;> assumption
      . intros Hold
        refine IsFvarNormalizeTrue ?_
        cases Hvalid <;> simp_all
        next Hval1 Hval2 Hnold =>
        have HH := IsOldPredNormalize Hval1 Hold
        cases HH <;> simp_all
  case abs ty e e_ih =>
    constructor
    apply e_ih
    cases Hvalid <;> assumption
  case quant k ty tr e tr_ih e_ih =>
    constructor
    apply tr_ih <;> cases Hvalid <;> assumption
    apply e_ih <;> cases Hvalid <;> assumption
  case ite c t e c_ih t_ih e_ih =>
    cases Hvalid
    constructor
    apply c_ih <;> assumption
    apply t_ih <;> assumption
    apply e_ih <;> assumption
  case eq e1 e2 e1_ih e2_ih =>
    cases Hvalid
    constructor
    apply e1_ih <;> assumption
    apply e2_ih <;> assumption

theorem substOldIsOldPred :
  IsOldPred fn → IsOldPred (substOld v s fn) := by
  . induction fn <;> simp [substOld] <;> intro Hold <;> try cases Hold

theorem substOldIsOldPred' :
  ¬ IsOldPred s →
  IsOldPred (substOld v s fn) → IsOldPred fn := by
  intros Hnold
  induction fn <;> simp [substOld] <;> intro Hold <;> try cases Hold
  case app fn e fn_ih e_ih =>
  split at Hold
  . next e1 e2 ty' x ty =>
    split at Hold <;> simp_all
  . cases Hold

theorem substOldNormalizedMono :
  ¬ IsOldPred s →
  NormalizedOldExpr e →
  NormalizedOldExpr s →
  NormalizedOldExpr (substOld v s e) := by
intros Hnold Hnorm Hnorm'
induction e <;> simp [substOld] <;> try assumption
case abs ty e e_ih =>
  constructor
  apply e_ih
  cases Hnorm
  assumption
case quant k ty tr e tr_ih e_ih =>
  constructor
  apply tr_ih <;> cases Hnorm <;> assumption
  apply e_ih <;> cases Hnorm <;> assumption

case app =>
  split
  split <;> simp_all
  next fn_ih e_ih e1 e2 h =>
  constructor
  . apply fn_ih
    cases Hnorm
    assumption
  . apply e_ih
    cases Hnorm
    assumption
  . intros Hold
    cases Hnorm
    next fn e Hnorm1 Hnorm2 Holdp =>
    have Hnoldfn : ¬ IsOldPred fn := by
      intros Hold
      specialize Holdp Hold
      cases Hold
      cases Holdp
      apply h
      rfl
      rfl
    exfalso
    have HH := substOldIsOldPred' Hnold Hold <;> simp_all
case ite c t e c_ih t_ih e_ih =>
  constructor
  . apply c_ih
    cases Hnorm
    assumption
  . apply t_ih
    cases Hnorm
    assumption
  . apply e_ih
    cases Hnorm
    assumption
case eq e1 e2 e1_ih e2_ih =>
  constructor
  . apply e1_ih
    cases Hnorm
    assumption
  . apply e2_ih
    cases Hnorm
    assumption

inductive ContainsOldVar : Expression.Expr → Prop where
  | old : ContainsOldVar (@oldVar mApp mOp mVar tyOld v ty)
  | abs : ContainsOldVar e → ContainsOldVar (.abs m ty e)
  | quant : ContainsOldVar e → ContainsOldVar (.quant m k ty tr e)
  | app_l : ContainsOldVar fn → ContainsOldVar (.app m fn e)
  | app_r : ContainsOldVar e → ContainsOldVar (.app m fn e)
  | ite_1 : ContainsOldVar c → ContainsOldVar (.ite m c t e)
  | ite_2 : ContainsOldVar t → ContainsOldVar (.ite m c t e)
  | ite_3 : ContainsOldVar e → ContainsOldVar (.ite m c t e)
  | eq_1  : ContainsOldVar e1 → ContainsOldVar (.eq m e1 e2)
  | eq_2  : ContainsOldVar e2 → ContainsOldVar (.eq m e1 e2)

end OldExpressions
end Core
