/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Simplify.Entry
public import Strata.Languages.Core.InstExprTyping
public import Strata.DL.Lambda.Denote.Assumptions
import all Strata.DL.Lambda.FactoryProps
import all Strata.Util.ListMap
import all Strata.Transform.Simplify.Expr

/-! # The precondition of the Simplify theorem

The transform `simplifyBody` and what `simplifyBody_overapproximatesTraces` asks of the body
(`BodyWF`) and of the factory Simplify folds with (`Laws`). They live apart from the theorem
so that a caller can establish them without depending on its proof.
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

/-! ## The transform and its precondition -/

/-- What `simplifyProcedure` does to a structured body: rewrite the statements, then drop
    the definitions nothing reads, knowing that the input parameters are defined
    throughout it.

    `live` is what the theorem promises about: final stores agree on its names and on
    nothing else (`EnvAgreeOnLive`). At the call site it must hold every name read after
    the body. `simplifyProcedure` seeds it with the output parameters and the free
    variables of the contract. That is enough: Core's type checker rejects a body that
    writes anything but its output parameters and its own locals, so no global or input
    written by the body can be read after it. -/
@[expose] def simplifyBody (base : Ctx) (inputs : @Lambda.LMonoTySignature Unit)
    (live : Std.HashSet String) (ss : List Statement) : Option (List Statement) :=
  some (dropDeadDefs base.factory (Defined.ofParams inputs (simpStmts base ss).1) live
    (simpStmts base ss).1)

/-- What `simplifyProcedure` installs for a structured body: `simplifyBody`'s output when it
    passes the def-use check `gateOK`, the body itself otherwise. -/
@[expose] def simplifyBodyChecked (base : Ctx) (inputs : @Lambda.LMonoTySignature Unit)
    (live : Std.HashSet String) (ss : List Statement) : Option (List Statement) :=
  let out := dropDeadDefs base.factory (Defined.ofParams inputs (simpStmts base ss).1) live
    (simpStmts base ss).1
  some (if gateOK base.factory ss out then out else ss)

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
    `establishes_ok` obligations are not proved yet (`proveAllPhaseContracts`). -/
@[expose] def BodyFragment (ss : List Statement) : Prop :=
  Statements.noCalls ss = true ∧ Block.noLoops ss = true

/-- **The statement precondition.** The body is in the fragment, and every expression in it
    is typed under the entry typing `Γ`, extended scope by scope. -/
@[expose] def BodyWF (F : Lambda.Factory CoreLParams) (Γ : VarTyping Expression)
    (ss : List Statement) : Prop :=
  BodyFragment ss ∧ Block.exprsOKIn F Γ ss

/-- `tyMap` types a formal parameter of a function of `F` with a body only if the function
    declares it at a ground type, and then at that type. A formal whose declared type has type
    variables is left untyped: its annotation in the body changes with each instantiation, so
    no one type agrees with all of them. Functions without a body are not constrained: only
    bodies are substituted into the expression being simplified. -/
@[expose] def AgreesOnFormals (F : Lambda.Factory CoreLParams)
    (tyMap : Map CoreIdent Lambda.LMonoTy) : Prop :=
  ∀ (f : String) (hf : f ∈ F), (F[f]).body.isSome →
    ∀ x ty, (x, ty) ∈ (F[f]).inputs.toList →
    ∀ τ, Map.find? tyMap x = some τ → τ = ty ∧ ty.freeVars = []

/-- The names whose types the entry typing `Γ` and the body's declarations give: the
    variables the clash check compares with the formals, and those the run invariant types. -/
@[expose] def typeList (Γ : VarTyping Expression) (ss : List Statement) :
    List (CoreIdent × Expression.Ty) :=
  (Block.entryVars ss).filterMap (fun y => (Γ y).map (y, ·)) ++ Block.declaredTypes ss

/-- Whether a variable of the body `ss`, an entry variable typed by `Γ` or a local at its
    declared type, is named like a formal parameter of a function of `F` with a body at a
    different type, or like one whose declared type has type variables. When it is `false`,
    the typings Simplify folds `ss` under agree with `F`'s formals (`AgreesOnFormals`). It
    names the clash `Laws` cannot rule out, and makes it a checked condition.

    Locals are collected from every branch and loop body, so a name declared at two types in
    sibling scopes is checked at both: a local that matches a formal's type in one branch and
    not in the other counts as a clash. That can only reject more bodies. -/
def Block.clashesWithFormals (F : Lambda.Factory CoreLParams) (Γ : VarTyping Expression)
    (ss : List Statement) : Bool :=
  let formals := F.toArray.toList.filter (·.body.isSome) |>.flatMap (·.inputs.toList)
  (typeList Γ ss).any fun (x, ty) => formals.any fun (y, fty) =>
    y == x && (ty.toMonoType? != some fty || !fty.freeVars.isEmpty)

/-- **No clash, so the fold typings agree with the formals.** Every typing that types only
    variables of the body, each at the type `Γ`, extended scope by scope, gives it, agrees
    with the formals of `F`'s functions with a body when the body has no clash. The
    simulation applies `Laws` at the typing of the values Simplify has recorded, which is
    such a typing.

    Simplify introduces no name into a body: the values it records are keyed by the variables
    `init` and `set` write (`Ctx.record`), and inline expansion substitutes the arguments for
    a function's formals. The fresh `$__lemma` names of `simplifyLemma` occur only in lemmas,
    never in a procedure body. So the typings of recorded values type only body variables. -/
theorem agreesOnFormals_of_noClash {F : Lambda.Factory CoreLParams} {Γ : VarTyping Expression}
    {ss : List Statement} (hclash : Block.clashesWithFormals F Γ ss = false)
    {tyMap : Map CoreIdent Lambda.LMonoTy}
    (htyped : ∀ x τ, Map.find? tyMap x = some τ →
      (x, Lambda.LTy.forAll [] τ) ∈ typeList Γ ss) :
    AgreesOnFormals F tyMap := by
  intro f hf hbody x ty hx τ hτ
  obtain ⟨g, hg, hgn⟩ := Array.mem_map.mp ((Lambda.Factory.mem_iff_mem_names F f).mp hf)
  obtain ⟨_, hget⟩ := Lambda.Factory.mem_name_eq_getElem hg hgn
  have hget : F[f]'hf = g := hget
  rw [hget] at hbody hx
  have hno := hclash
  simp only [Block.clashesWithFormals, List.any_eq_false] at hno
  have hformal : (x, ty) ∈ (F.toArray.toList.filter (·.body.isSome)).flatMap (·.inputs.toList) :=
    List.mem_flatMap.mpr ⟨g, List.mem_filter.mpr ⟨Array.mem_toList_iff.mpr hg, hbody⟩, hx⟩
  have h := hno _ (htyped x τ hτ)
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, bne_iff_ne,
    ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff, not_exists,
    not_and, not_or] at h
  obtain ⟨h1, h2⟩ := h _ hformal rfl
  refine ⟨?_, by simpa using h2⟩
  simpa only [Lambda.LTy.toMonoType?, Option.some.injEq, Classical.not_not] using h1

/-- **The factory's well-formedness**, in the two forms the expression lemmas ask for.

    `StepWF` is asked only at typings that agree with the formals of the factory's functions
    with a body (`AgreesOnFormals`), not at every typing: its `BodyAnnotated` field requires
    each variable a function body mentions to carry the type the typing gives that name, so a
    typing that gives a formal's name another type falsifies it for any factory with a
    function body. The typings Simplify folds under are those of the values it has recorded
    (`Env.smallValues`), so they agree with the factory's formals when no variable of the body
    is named like a formal of a function with a body at a different type.

    Monomorphization can create such a clash: every specialization of a polymorphic function
    keeps the formal's name at a different type. -/
@[expose] def Laws (F : Lambda.Factory CoreLParams) : Prop :=
  (∃ tf : @Lambda.TypeFactory CoreLParams.IDMeta, Lambda.Factory.WF F tf) ∧
    ∀ tyMap, AgreesOnFormals F tyMap → Lambda.Factory.StepWF F tyMap

end

end Core.Simplify
