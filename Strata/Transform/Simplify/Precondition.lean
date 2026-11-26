/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Simplify.Entry
public import Strata.Languages.Core.InstExprTyping
public import Strata.DL.Lambda.Denote.Assumptions
import all Strata.Util.ListMap
import all Strata.Transform.Simplify.Expr

/-! # The precondition of the Simplify theorem

What the Simplify theorems (`sweptBody_overapproximatesTraces`,
`checkedBody_overapproximatesTraces`) ask of the body (`BodyWF`) and of the context it is
simplified from (`Ctx.Fresh`). They live apart from the theorems so that a caller can
establish them without depending on their proofs. What the theorems ask of the factory is the
condition of evaluator soundness, `Lambda.Factory.EvalSoundWF`.
-/

namespace Core.Simplify

open Imperative

public section

/-! ## Typing, scope by scope -/

/-- `e` has type `ty` under `Γ`, its operators are consistent with the factory `F`, and each
    of its free variables already carries the monotype `Γ` gives it, as the type checker's
    output does. Core's evaluator annotates free variables with the sorts of their stored
    values before denoting; with the last conjunct, and a store whose values have their
    `Γ` types, that annotation leaves `e` unchanged. -/
@[expose] def ExprOK (F : Lambda.Factory CoreLParams) (Γ : VarTyping Expression)
    (e : Expression.Expr) (ty : Expression.Ty) : Prop :=
  Expression.HasType Γ e ty ∧ Lambda.OpsConsistent F e ∧
    e.annotateFvars (fun x => (Γ x).bind Lambda.LTy.toMonoType?) = e

mutual
/-- Every expression of the statement list is `ExprOK` under the typing in scope at it.
    Each statement extends the typing with what it declares (`Stmt.typedDefinedVars`, so an
    `init` declares its variable) for the rest of its list, as `Block.fvarTypesWellAnnotated`
    does; nested lists start from the enclosing typing, so a declaration leaves scope with
    its list, and sibling scopes may declare the same name at different types. -/
@[expose] def Block.exprsOKIn (F : Lambda.Factory CoreLParams) (Γ : VarTyping Expression) :
    List Statement → Prop
  | [] => True
  | s :: rest => Stmt.exprsOKIn F Γ s ∧
      Block.exprsOKIn F (Γ.extend (Stmt.typedDefinedVars (P := Expression) s)) rest

/-- `Block.exprsOKIn` for the statement's own expressions, under the typing before it. -/
@[expose] def Stmt.exprsOKIn (F : Lambda.Factory CoreLParams) (Γ : VarTyping Expression) :
    Statement → Prop
  | .cmd (.cmd (.init _ ty (.det e) _)) => ExprOK F Γ e ty
  | .cmd (.cmd (.init _ _ .nondet _)) => True
  | .cmd (.cmd (.set x (.det e) _)) => ∃ ty, Γ x = some ty ∧ ExprOK F Γ e ty
  | .cmd (.cmd (.set x .nondet _)) => (Γ x).isSome
  | .cmd (.cmd (.assert _ e _)) | .cmd (.cmd (.assume _ e _))
  | .cmd (.cmd (.cover _ e _)) => ExprOK F Γ e (HasBool.boolTy (P := Expression))
  | .block _ ss _ => Block.exprsOKIn F Γ ss
  | .ite (.det g) ts es _ =>
    ExprOK F Γ g (HasBool.boolTy (P := Expression)) ∧ Block.exprsOKIn F Γ ts ∧
      Block.exprsOKIn F Γ es
  | .ite .nondet ts es _ => Block.exprsOKIn F Γ ts ∧ Block.exprsOKIn F Γ es
  | .loop _ _ _ body _ => Block.exprsOKIn F Γ body
  | _ => True
end

/-! ## The precondition -/

/-- The context a body is simplified from records nothing, and folds with its factory with
    `inline` weakened, as `Ctx.ofFactory` builds it. -/
@[expose] def Ctx.Fresh (base : Ctx) : Prop :=
  base.foldFactory = withoutInline base.carriers base.factory ∧ base.values.toList = []

/-- The context `Ctx.ofFactory` builds is fresh. -/
theorem Ctx.ofFactory_fresh (F : Lambda.Factory CoreLParams) (c : List String) :
    (Ctx.ofFactory F c).Fresh := ⟨rfl, rfl⟩

/-- The fragment the simulation covers: no call and no loop, which `callElim` and `loopElim`
    remove before Simplify runs. `havoc` and an `init` without a value are included.

    At the pipeline level this is an assumption: `callElim` and `loopElim` declare that
    they establish `ProgramFact.noCalls` and `ProgramFact.noLoops`, but their
    `establishes_ok` obligations are not proved yet: both list every fact in `unproved`. -/
@[expose] def BodyFragment (ss : List Statement) : Prop :=
  Statements.noCalls ss = true ∧ Block.noLoops ss = true

/-- **The statement precondition.** The body is in the fragment, and every expression in it
    is typed under the entry typing `Γ`, extended scope by scope. -/
@[expose] def BodyWF (F : Lambda.Factory CoreLParams) (Γ : VarTyping Expression)
    (ss : List Statement) : Prop :=
  BodyFragment ss ∧ Block.exprsOKIn F Γ ss

end

end Core.Simplify
