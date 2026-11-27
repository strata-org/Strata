/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.StatementType
public import Strata.Languages.Core.Typing.Props.TypeSkolemProps
public import Strata.Languages.Core.Typing.Props.SourceExprResolveProps
import all Strata.Languages.Core.Typing.Props.TypeSkolemProps
import all Strata.Languages.Core.Typing.Props.SourceExprResolveProps
public import Strata.Languages.Core.CmdType
import all Strata.Languages.Core.CmdType
import all Strata.DL.Imperative.CmdType
import all Strata.DL.Lambda.LExprTypeSpec
import all Strata.DL.Lambda.LTyUnify
import all Strata.DL.Lambda.LTyProps
import all Strata.DL.Lambda.LExprT
import all Strata.DL.Lambda.LExprTypeEnvProps
import Strata.Languages.Core.CallWFProps
import all Strata.Languages.Core.StatementType
import all Strata.Languages.Core.TypeSkolem
import all Strata.Languages.Core.Statement
import all Strata.DL.Imperative.Cmd
import all Strata.DL.Lambda.LExprTypeEnv
import all Strata.Languages.Core.Procedure

/-! # Inversion of the command checker and its effect on the context

Every successful `Statement.typeCheckCmd` run is an accepting run (`CmdRun`) recording the result
of each step (`Statement.typeCheckCmd_ok_inv`). Any relation on type environments that every
step preserves relates the input and output environments of the command (`CmdRun.rel`); the one
used is that a checked command keeps the scopes below the newest, up to lookup equivalence, and
the alias list (`Statement.typeCheckCmd_preserves_context`). Also here: inversion of a
successful procedure-header instantiation, and the fact that instantiating declared types and
signatures only draws fresh type variables (they are `GenOnly`). -/

public section

namespace Core

open Lambda Imperative
open TypeSpec
open Except
open Strata.Util (HMap HMaps)

/-- Successful declaration preprocessing accepts only a monotype and checks it as a source type
    without reserved type variables. -/
theorem preprocess_ok_inv
    (C : LContext CoreLParams) (Env Env1 : TEnv Unit)
    (xty ty1 : LTy) (h : CmdType.preprocess C Env xty = .ok (ty1, Env1)) :
    ∃ m0 mtyP, xty = .forAll [] m0 ∧ ty1 = .forAll [] mtyP ∧
      m0.typeCheckSource C Env TyVarAdmissibility.notGeneratedOrRigid = .ok (mtyP, Env1) := by
  rcases xty with ⟨xs, m0⟩
  cases xs with
  | cons x xrest =>
    simp [CmdType.preprocess, LTy.isMonoType, LTy.boundVars] at h
  | nil =>
    simp only [CmdType.preprocess, LTy.isMonoType, LTy.boundVars, List.isEmpty_nil,
      ↓reduceDIte, LTy.toMonoType, bind, Except.bind, pure, Except.pure] at h
    cases hsrc : m0.typeCheckSource C Env TyVarAdmissibility.notGeneratedOrRigid with
    | error e => rw [hsrc] at h; simp [Except.mapError] at h
    | ok v =>
      obtain ⟨mtyP, E1⟩ := v
      rw [hsrc] at h
      simp only [Except.mapError, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨m0, mtyP, rfl, rfl, hsrc⟩

/-- Instantiating a monotype with a check keeps the environment and returns a registered type that
    is the monotype's alias resolution, alias-equivalent to it. -/
theorem instantiateWithCheck_forAll_nil_env_eq (C : LContext CoreLParams) (Env Env1 : TEnv Unit)
    (m0 r : LMonoTy) (h : LTy.instantiateWithCheck (.forAll [] m0) C Env = .ok (r, Env1)) :
    Env1 = Env ∧ LMonoTy.resolveAliases m0 Env = .ok (r, Env) ∧
      AliasEquiv Env.context.aliases m0 r ∧ isInstanceOfKnownType r C = true := by
  obtain ⟨hresolve, hknown⟩ := LTy.instantiateWithCheck_forAll_nil_inv C m0 r Env Env1 h
  have hE := LMonoTy.resolveAliases_env_eq m0 Env r Env1 hresolve
  subst Env1
  exact ⟨rfl, hresolve, LExpr.resolveAliases_aliasEquiv (T := CoreLParams) (Γ := Env.context)
    m0 Env r Env hresolve rfl, hknown⟩

/-- Successful declaration preprocessing keeps the environment and resolves the written monotype
    to an alias-equivalent type, as a valid source type without reserved type variables. -/
theorem CmdType.preprocess_inv
    (C : LContext CoreLParams) (Env Env1 : TEnv Unit)
    (xty ty1 : LTy) (h : CmdType.preprocess C Env xty = .ok (ty1, Env1)) :
    ∃ m0 mtyP,
      xty = .forAll [] m0 ∧ ty1 = .forAll [] mtyP ∧ Env1 = Env ∧
      AliasEquiv Env.context.aliases m0 mtyP ∧
      SourceTyWF C TyVarAdmissibility.notGeneratedOrRigid Env.context.aliases m0 mtyP := by
  obtain ⟨m0, mtyP, rfl, rfl, hsrc⟩ := preprocess_ok_inv C Env Env1 xty ty1 h
  obtain ⟨hE1, -, hae, -⟩ := instantiateWithCheck_forAll_nil_env_eq C Env Env1 m0 mtyP
    (typeCheckSource_notGeneratedOrRigid_instantiateWithCheck m0 mtyP C Env Env1 hsrc)
  exact ⟨m0, mtyP, rfl, rfl, hE1, hae,
    LMonoTy.typeCheckSource_sound m0 mtyP C Env Env1 _ hsrc⟩

/-- Successful inference returns the resolver's result. -/
theorem CmdType.inferType_inv
    (C : LContext CoreLParams) (Env E2 : TEnv Unit)
    (c : Cmd Expression) (e e1 : Expression.Expr) (ety : LTy)
    (h : CmdType.inferType C Env c e = .ok (e1, ety, E2)) :
    ∃ ea,
      SourceExpr.resolve C Env e = .ok (ea, E2) ∧
      e1 = ea.unresolved ∧ ety = .forAll [] ea.toLMonoTy := by
  unfold CmdType.inferType at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  elim_err h with v hres
  obtain ⟨ea, E⟩ := v
  have hres' : SourceExpr.resolve C Env e = .ok (ea, E) :=
    SourceExpr.orFreeVarError_eq_ok.mp (Except.mapError_ok_h' hres)
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨ea, hres', rfl, rfl⟩

/-- Canonicalizing one constraint exposes its two monotype bodies. -/
private theorem CmdType.canonicalizeConstraints_inv
    (t1 t2 : LTy) (cs : Constraints)
    (h : CmdType.canonicalizeConstraints [(t1, t2)] = .ok cs) :
    ∃ a b, t1 = .forAll [] a ∧ t2 = .forAll [] b ∧ cs = [(a, b)] := by
  simp only [CmdType.canonicalizeConstraints, bind, Except.bind] at h
  elim_err h with hmono
  simp only [Bool.and_eq_true] at hmono
  obtain ⟨m1, rfl⟩ := LTy.eq_forAll_nil_of_isMonoType hmono.1
  obtain ⟨m2, rfl⟩ := LTy.eq_forAll_nil_of_isMonoType hmono.2
  simp only [Except.ok.injEq] at h
  exact ⟨m1, m2, rfl, rfl, h.symm⟩

/-- Unifying one constraint records the unifier's solution in the environment. -/
theorem CmdType.unifyTypes_inv
    (Env Env3 : TEnv Unit) (t1 t2 : LTy)
    (h : CmdType.unifyTypes Env [(t1, t2)] = .ok Env3) :
    ∃ a b Sx,
      t1 = .forAll [] a ∧ t2 = .forAll [] b ∧
      Constraints.unify [(a, b)] Env.stateSubstInfo = .ok Sx ∧
      Env3 = Env.updateSubst Sx := by
  unfold CmdType.unifyTypes at h
  simp only [bind, Except.bind, pure, Except.pure, Except.mapError] at h
  elim_err h with cs hcs
  obtain ⟨a, b, rfl, rfl, rfl⟩ :=
    CmdType.canonicalizeConstraints_inv t1 t2 cs hcs
  elim_err h with Sx hu
  have hu' : Constraints.unify [(a, b)] Env.stateSubstInfo = .ok Sx :=
    Except.mapError_ok_h' hu
  simp only [Except.ok.injEq] at h
  subst h
  exact ⟨a, b, Sx, rfl, rfl, hu', rfl⟩

/-- The accepting runs of the imperative command checker on Core, recording each step's result. -/
inductive ImperativeCmdRun (C : LContext CoreLParams) (Env : TEnv Unit) :
    Cmd Expression → Cmd Expression → TEnv Unit → Prop where
  | initDet {x : CoreIdent} {xty xtyP ety xtyQ : LTy} {expr e' : Expression.Expr}
      {md : MetaData Expression} {Env1 Env2 Env3 Env4 : TEnv Unit}
      (hlookup : Env.context.types.find? x = none)
      (hself : x ∉ CmdType.freeVars expr)
      (hpre : CmdType.preprocess C Env xty = .ok (xtyP, Env1))
      (hinfer : CmdType.inferType C Env1 (.init x xty (.det expr) md) expr = .ok (e', ety, Env2))
      (hunify : CmdType.unifyTypes Env2 [(xtyP, ety)] = .ok Env3)
      (hpost : CmdType.postprocess C Env3 xtyP = .ok (xtyQ, Env4)) :
      ImperativeCmdRun C Env (.init x xty (.det expr) md)
        (.init x xtyQ (.det (CmdType.substExpr C Env4 e')) md) (CmdType.update Env4 x xtyQ)
  | initNondet {x : CoreIdent} {xty xtyP xtyQ : LTy} {md : MetaData Expression}
      {Env1 Env2 : TEnv Unit}
      (hlookup : Env.context.types.find? x = none)
      (hpre : CmdType.preprocess C Env xty = .ok (xtyP, Env1))
      (hpost : CmdType.postprocess C Env1 xtyP = .ok (xtyQ, Env2)) :
      ImperativeCmdRun C Env (.init x xty .nondet md) (.init x xtyQ .nondet md)
        (CmdType.update Env2 x xtyQ)
  | setDet {x : CoreIdent} {xty ety : LTy} {expr e' : Expression.Expr}
      {md : MetaData Expression} {Env1 Env2 : TEnv Unit}
      (hlookup : Env.context.types.find? x = some xty)
      (hinfer : CmdType.inferType C Env (.set x (.det expr) md) expr = .ok (e', ety, Env1))
      (hunify : CmdType.unifyTypes Env1 [(Env.context.resolveScheme xty, ety)] = .ok Env2) :
      ImperativeCmdRun C Env (.set x (.det expr) md) (.set x (.det e') md) Env2
  | setNondet {x : CoreIdent} {xty : LTy} {md : MetaData Expression}
      (hlookup : Env.context.types.find? x = some xty)
      (hmono : xty.isMonoType = true) :
      ImperativeCmdRun C Env (.set x .nondet md) (.set x .nondet md) Env
  | assert {l : String} {e e' : Expression.Expr} {ety : LTy} {md : MetaData Expression}
      {Env1 : TEnv Unit}
      (hinfer : CmdType.inferType C Env (.assert l e md) e = .ok (e', ety, Env1))
      (hbool : CmdType.isBoolType ety = true) :
      ImperativeCmdRun C Env (.assert l e md) (.assert l e' md) Env1
  | assume {l : String} {e e' : Expression.Expr} {ety : LTy} {md : MetaData Expression}
      {Env1 : TEnv Unit}
      (hinfer : CmdType.inferType C Env (.assume l e md) e = .ok (e', ety, Env1))
      (hbool : CmdType.isBoolType ety = true) :
      ImperativeCmdRun C Env (.assume l e md) (.assume l e' md) Env1
  | cover {l : String} {e e' : Expression.Expr} {ety : LTy} {md : MetaData Expression}
      {Env1 : TEnv Unit}
      (hinfer : CmdType.inferType C Env (.cover l e md) e = .ok (e', ety, Env1))
      (hbool : CmdType.isBoolType ety = true) :
      ImperativeCmdRun C Env (.cover l e md) (.cover l e' md) Env1

/-! ### Instantiating a procedure header -/

/-- A successful header instantiation instantiates the joint input-output signature once and
    returns its input and output parts; substituting either part takes or drops the corresponding
    prefix of the substituted joint signature. The returned type arguments are the instantiation
    of the type parameters themselves. -/
private theorem Procedure.Header.instantiate_ok_inv {C : LContext CoreLParams}
    {Env Env' : TEnv Unit} {h : Procedure.Header}
    {inp out : @LMonoTySignature Unit} {instTys : LMonoTys}
    (hinst : h.instantiate C Env = .ok (inp, out, instTys, Env')) :
    ∃ io_sig EnvA, LMonoTySignature.instantiate C Env h.typeArgs
        (h.inputs ++ h.outputs) = .ok (io_sig, Env') ∧
      LMonoTys.instantiateEnv h.typeArgs (h.typeArgs.map LMonoTy.ftvar) Env
        = .ok (instTys, EnvA) ∧
      ∀ S : Subst, LMonoTys.subst S inp.values
          = (LMonoTys.subst S io_sig.values).take h.inputs.length ∧
        LMonoTys.subst S out.values
          = (LMonoTys.subst S io_sig.values).drop h.inputs.length := by
  unfold Procedure.Header.instantiate at hinst
  simp only [bind, Except.bind] at hinst
  elim_err hinst with sigPair hsig
  obtain ⟨io_sig, E⟩ := sigPair
  elim_err hinst with argsPair hargs
  obtain ⟨tys, EnvA⟩ := argsPair
  simp only [pure, Except.pure, Except.ok.injEq] at hinst
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hinst
  refine ⟨io_sig, EnvA, hsig, hargs, fun S => ⟨?_, ?_⟩⟩
  all_goals
    erw [List.splitAt_eq, ListMap.values_eq_map_snd]
    simp only [LMonoTys.subst_eq_map, ListMap.values_eq_map_snd]
    grind [List.map_take, List.map_drop]

/-- Every successful imperative command check is an accepting run. -/
private theorem imperativeCmd_ok_inv {C : LContext CoreLParams} {Env Env' : TEnv Unit}
    {cmd cmd' : Cmd Expression}
    (h : Imperative.Cmd.typeCheck (P := Expression) (T := TEnv Unit) C Env cmd
      = .ok (cmd', Env')) :
    ImperativeCmdRun C Env cmd cmd' Env' := by
  simp only [Imperative.Cmd.typeCheck] at h
  replace h := ok_of_tryCatch h (fun _ => ⟨_, rfl⟩)
  cases cmd
  case init x xty e md =>
    simp only [bind, Except.bind] at h
    elim_err h with hlookupR
    have hlookup : Env.context.types.find? x = none := Option.map_eq_none_iff.mp hlookupR
    cases e with
    | det expr =>
      dsimp only at h
      elim_err h with hself
      elim_err h with vp hpre
      obtain ⟨xtyP, Env1⟩ := vp
      elim_err h with vi hinfer
      obtain ⟨e', ety, Env2⟩ := vi
      elim_err h with Env3 hunify
      elim_err h with vq hpost
      obtain ⟨xtyQ, Env4⟩ := vq
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .initDet hlookup hself hpre hinfer hunify hpost
    | nondet =>
      dsimp only at h
      elim_err h with vp hpre
      obtain ⟨xtyP, Env1⟩ := vp
      elim_err h with vq hpost
      obtain ⟨xtyQ, Env2⟩ := vq
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .initNondet hlookup hpre hpost
  case set x e md =>
    simp only [bind, Except.bind] at h
    elim_err h with xtyR hlookupR
    obtain ⟨xty, hlookup, rfl⟩ := Option.map_eq_some_iff.mp hlookupR
    cases e with
    | det expr =>
      dsimp only at h
      elim_err h with vi hinfer
      obtain ⟨e', ety, Env1⟩ := vi
      elim_err h with Env2 hunify
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .setDet hlookup hinfer hunify
    | nondet =>
      dsimp only at h
      elim_err h with hmonoR
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hmono : xty.isMonoType = true := by
        cases xty
        exact hmonoR
      exact .setNondet hlookup hmono
  all_goals
    simp only [bind, Except.bind] at h
    elim_err h with vi hinfer
    obtain ⟨e', ety, Env1⟩ := vi
    elim_err h with hbool
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
  · exact .assert hinfer hbool
  · exact .assume hinfer hbool
  · exact .cover hinfer hbool

/-- The accepting runs of the Core command checker, recording each step's result. -/
inductive CmdRun (C : LContext CoreLParams) (Env : TEnv Unit) (P : Program) :
    Command → Command → TEnv Unit → Prop where
  | cmd {cc cc' : Cmd Expression} {Env' : TEnv Unit}
      (run : ImperativeCmdRun C Env cc cc' Env') :
      CmdRun C Env P (.cmd cc) (.cmd cc') Env'
  | call {nm : String} {tyArgs : Option (List Expression.Ty)}
      {callArgs : List (CallArg Expression)} {md : MetaData Expression}
      {proc : Procedure} {lhs_tys : LMonoTys} {io_sig : @LMonoTySignature Unit}
      {argsa : List (LExprT CoreLParams.mono)} {Env1 Env2 Env3 : TEnv Unit} {Suni : SubstInfo}
      {instTys : LMonoTys} {EnvA : TEnv Unit}
      (hproc : Program.Procedure.find? P nm = some proc)
      (hlhsSome : ∀ l ∈ CallArg.getLhs callArgs, (Env.context.types.find? l).isSome = true)
      (hwf : WF.WFcallProp P nm callArgs)
      (hlhs : Lambda.Identifier.instantiateAndSubsts (CallArg.getLhs callArgs) C Env
        = .ok (some (lhs_tys, Env1)))
      (hsig : LMonoTySignature.instantiate C Env1 proc.header.typeArgs
        (proc.header.inputs ++ proc.header.outputs) = .ok (io_sig, Env2))
      (hres : SourceExpr.resolves C Env2 (CallArg.getInputExprs callArgs) = .ok (argsa, Env3))
      (hunify : Constraints.unify
        ((argsa.map LExpr.toLMonoTy).zip
            ((LMonoTys.subst Env2.stateSubstInfo.subst io_sig.values).take
              proc.header.inputs.length) ++
          lhs_tys.zip
            ((LMonoTys.subst Env2.stateSubstInfo.subst io_sig.values).drop
              proc.header.inputs.length))
        Env3.stateSubstInfo = .ok Suni)
      (hargs : LMonoTys.instantiateEnv proc.header.typeArgs
        (proc.header.typeArgs.map LMonoTy.ftvar) Env1 = .ok (instTys, EnvA)) :
      CmdRun C Env P (.call nm tyArgs callArgs md)
        (.call nm (some (instTys.map (Lambda.LTy.forAll [] ·)))
          (CallArg.replaceInArgs callArgs (argsa.map LExpr.unresolved)) md)
        (Env3.updateSubst Suni)

/-- Every successful Core command check is an accepting run. -/
theorem Statement.typeCheckCmd_ok_inv {C : LContext CoreLParams} {Env Env' : TEnv Unit}
    {P : Program} {c c' : Command}
    (h : Statement.typeCheckCmd C Env P c = .ok (c', Env')) :
    CmdRun C Env P c c' Env' := by
  cases c with
  | cmd cc =>
    unfold Statement.typeCheckCmd at h
    simp only [bind, Except.bind] at h
    elim_err h with result hic
    obtain ⟨c2, E2⟩ := result
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .cmd (imperativeCmd_ok_inv hic)
  | call nm tyArgs callArgs md =>
    unfold Statement.typeCheckCmd at h
    simp only [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch] at h
    elim_err h with v heq
    simp only [Except.ok.injEq] at h
    subst h
    simp only [bind, Except.bind] at heq
    elim_err heq with proc hproc
    split at heq
    · exact absurd heq (by simp)
    rename_i hargsNone
    simp only [Except.ite_error_then_eq_ok] at heq
    obtain ⟨hlhsSome, heq⟩ := heq
    elim_err heq with lhsOpt hlhs
    replace hlhs := Except.mapError_ok_h' hlhs
    match lhsOpt with
    | none => exact absurd heq (by simp)
    | some (lhs_tys, Env1) =>
      dsimp only at heq
      elim_err heq with sigPair hhdr
      obtain ⟨inp_sig, ret_sig, instTys, Env2⟩ := sigPair
      obtain ⟨io_sig, EnvA, hsig, hargs, hsplit⟩ :=
        Procedure.Header.instantiate_ok_inv
          (SourceExpr.orFreeVarError_eq_ok.mp (Except.mapError_ok_h' hhdr))
      elim_err heq with resPair hres
      obtain ⟨argsa, Env3⟩ := resPair
      elim_err heq with Suni huni
      rw [(hsplit Env2.stateSubstInfo.subst).1, (hsplit Env2.stateSubstInfo.subst).2] at huni
      simp only [Except.ok.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have hlhsSome' :
          ∀ l ∈ CallArg.getLhs callArgs,
            (Env.context.types.find? l).isSome = true := by
        intro l hl
        cases hf : Env.context.types.find? l with
        | none =>
          exact absurd
            (List.any_eq_true.mpr ⟨l, hl, by simp [hf]⟩) hlhsSome
        | some ty => simp
      obtain ⟨hmatch, hnodup⟩ := (callArgsError?_eq_none_iff nm proc callArgs).mp
        (Option.eq_none_iff_forall_ne_some.mpr hargsNone)
      have hwf : WF.WFcallProp P nm callArgs := WF.WFcallProp.of_argsMatch hproc hmatch hnodup
      exact .call hproc hlhsSome' hwf hlhs hsig
        (SourceExpr.orFreeVarError_eq_ok.mp (Except.mapError_ok_h' hres))
        (Except.mapError_ok_h' huni) hargs

/-! ### Reading and instantiating declared types never records a solution -/

/-- Reading off the type of one identifier only draws fresh type variables. -/
theorem Identifier.instantiateAndSubst_genOnly (x : CoreIdent) (C : LContext CoreLParams)
    (Env Env' : TEnv Unit) (mty : LMonoTy)
    (h : Lambda.Identifier.instantiateAndSubst x C Env = .ok (some (mty, Env'))) :
    SourceExpr.GenOnly Env Env' := by
  obtain ⟨ty, mtyR, -, hv, -⟩ := Lambda.Identifier.instantiateAndSubst_inv x C Env mty Env' h
  exact SourceExpr.instantiateWithCheck_genOnly ty C Env Env' mtyR hv

/-- Reading off the types of a list of identifiers only draws fresh type variables. -/
theorem Identifier.instantiateAndSubsts_genOnly (xs : List CoreIdent)
    (C : LContext CoreLParams) (Env : TEnv Unit) (mtys : List LMonoTy) (Env' : TEnv Unit)
    (h : Lambda.Identifier.instantiateAndSubsts xs C Env = .ok (some (mtys, Env'))) :
    SourceExpr.GenOnly Env Env' := by
  induction xs generalizing Env mtys with
  | nil =>
    simp only [Lambda.Identifier.instantiateAndSubsts, pure, Except.pure, Except.ok.injEq,
      Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact SourceExpr.GenOnly.refl Env
  | cons x xrest ih =>
    obtain ⟨xty, EnvA, xtys, hhd, htl, -⟩ := Lambda.Identifier.instantiateAndSubsts_cons_inv h
    exact SourceExpr.GenOnly.trans
      (Identifier.instantiateAndSubst_genOnly x C Env EnvA xty hhd)
      (ih EnvA xtys htl)

/-- The per-entry loop of signature instantiation only draws fresh type variables. -/
private theorem LMonoTySignature.instantiate_go_genOnly (C : LContext CoreLParams)
    (tys : LTys) :
    ∀ (Env EnvR : TEnv Unit) (rtys : LMonoTys),
      LMonoTySignature.instantiate.go (T := CoreLParams) C Env tys = Except.ok (rtys, EnvR) →
      SourceExpr.GenOnly Env EnvR := by
  induction tys with
  | nil =>
    intro Env EnvR rtys h
    simp only [LMonoTySignature.instantiate.go, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact SourceExpr.GenOnly.refl Env
  | cons t trest ih =>
    intro Env EnvR rtys h
    obtain ⟨mt, EnvA, mtrest, hhd, htl, -⟩ := LMonoTySignature.instantiate_go_cons_inv h
    exact SourceExpr.GenOnly.trans
      (SourceExpr.instantiateWithCheck_genOnly t C Env EnvA mt hhd)
      (ih EnvA EnvR mtrest htl)

/-- Renaming type parameters of monotypes to fresh variables only draws fresh type variables. -/
private theorem LMonoTys.instantiateEnv_genOnly (ids : List TyIdentifier) (mtys : LMonoTys)
    (Env Env' : TEnv Unit) (mtys' : LMonoTys)
    (h : LMonoTys.instantiateEnv ids mtys Env = .ok (mtys', Env')) :
    SourceExpr.GenOnly Env Env' := by
  refine ⟨LExpr.LMonoTys.instantiateEnv_context ids mtys Env mtys' Env' h, ?_,
    LMonoTys.instantiateEnv_tyGen_mono ids mtys Env mtys' Env' h⟩
  unfold LMonoTys.instantiateEnv at h
  cases hinst : LMonoTys.instantiate ids mtys Env.genEnv with
  | error e => rw [hinst] at h; exact absurd h (by simp)
  | ok v =>
    obtain ⟨mtysG, genEnv1⟩ := v
    rw [hinst] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]

/-- Instantiating a procedure signature only draws fresh type variables. -/
theorem LMonoTySignature.instantiate_genOnly (C : LContext CoreLParams)
    (Env EnvR : TEnv Unit) (tyArgs : List TyIdentifier)
    (sig sig' : @LMonoTySignature Unit)
    (h : LMonoTySignature.instantiate C Env tyArgs sig = .ok (sig', EnvR)) :
    SourceExpr.GenOnly Env EnvR := by
  simp only [LMonoTySignature.instantiate, bind, Except.bind] at h
  elim_err h with vI hI
  obtain ⟨mtysI, EnvI⟩ := vI
  elim_err h with vG hG
  obtain ⟨newtys, EnvG⟩ := vG
  rw [← (Prod.mk.inj (Except.ok.inj h)).2]
  exact SourceExpr.GenOnly.trans
    (LMonoTys.instantiateEnv_genOnly tyArgs sig.values Env EnvI mtysI hI)
    (LMonoTySignature.instantiate_go_genOnly C _ EnvI EnvG newtys hG)

/-! ### Preprocessing and postprocessing a declared type keep the environment -/

/-- Preprocessing a declared local type keeps the environment. -/
theorem CmdType.preprocess_env_eq (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (ty ty' : LTy)
    (h : CmdType.preprocess C Env ty = .ok (ty', Env')) : Env' = Env := by
  obtain ⟨m0, mtyP, -, -, hEnv, -⟩ := CmdType.preprocess_inv C Env Env' ty ty' h
  exact hEnv

/-- Postprocessing a monotype applies the solved substitution and keeps the environment. -/
theorem CmdType.postprocess_inv
    (C : LContext CoreLParams) (Env Env2 : TEnv Unit)
    (m : LMonoTy) (ty2 : LTy)
    (h : CmdType.postprocess C Env (.forAll [] m) = .ok (ty2, Env2)) :
    ty2 = .forAll [] (LMonoTy.subst Env.stateSubstInfo.subst m) ∧ Env2 = Env := by
  unfold CmdType.postprocess at h
  elim_err h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

/-! ### Relations preserved by every checker step -/

/-- A transitive relation on type environments that holds across each kind of checker step
    relates the input and output environments of every accepted command. The relation need only
    hold across adding a binding when the command is a declaration. -/
theorem CmdRun.rel {C : LContext CoreLParams} {Env Env' : TEnv Unit} {P : Program}
    {c c' : Command} (R : TEnv Unit → TEnv Unit → Prop)
    (run : CmdRun C Env P c c' Env')
    (htrans : ∀ {E1 E2 E3 : TEnv Unit}, R E1 E2 → R E2 E3 → R E1 E3)
    (hgen : ∀ {E E' : TEnv Unit}, SourceExpr.GenOnly E E' → R E E')
    (hresolve : ∀ {E' : TEnv Unit} {e : Expression.Expr} {et : LExprT CoreLParams.mono},
      SourceExpr.resolve C Env e = .ok (et, E') → R Env E')
    (hresolves : ∀ {E E' : TEnv Unit} {es : List Expression.Expr}
      {ets : List (LExprT CoreLParams.mono)}, SourceExpr.GenOnly Env E →
      SourceExpr.resolves C E es = .ok (ets, E') → R E E')
    (hunify : ∀ {E : TEnv Unit} {cs : Constraints} {Sx : SubstInfo},
      Constraints.unify cs E.stateSubstInfo = .ok Sx → R E (E.updateSubst Sx))
    (hupdate : ∀ {E : TEnv Unit} {x : CoreIdent} {ty : LTy},
      (∃ x' xty e md, c = .cmd (.init x' xty e md)) → R E (CmdType.update E x ty)) :
    R Env Env' := by
  have hinfer : ∀ {cmd : Cmd Expression} {e e' : Expression.Expr} {ety : LTy} {E' : TEnv Unit},
      CmdType.inferType C Env cmd e = .ok (e', ety, E') → R Env E' := by
    intro cmd e e' ety E' h
    obtain ⟨ea, hres, -, -⟩ := CmdType.inferType_inv C Env E' cmd e e' ety h
    exact hresolve hres
  have hunifyTypes : ∀ {E E' : TEnv Unit} {t1 t2 : LTy},
      CmdType.unifyTypes E [(t1, t2)] = .ok E' → R E E' := by
    intro E E' t1 t2 h
    obtain ⟨a, b, Sx, -, -, hu, rfl⟩ := CmdType.unifyTypes_inv E E' t1 t2 h
    exact hunify hu
  cases run with
  | cmd run =>
    cases run with
    | initDet hlookup hself hpre hinf hunif hpost =>
      obtain ⟨m0, mtyP, -, rfl, hEnv1, -⟩ := CmdType.preprocess_inv C Env _ _ _ hpre
      rw [hEnv1] at hinf
      rw [(CmdType.postprocess_inv _ _ _ _ _ hpost).2]
      exact htrans (hinfer hinf) (htrans (hunifyTypes hunif) (hupdate ⟨_, _, _, _, rfl⟩))
    | initNondet hlookup hpre hpost =>
      obtain ⟨m0, mtyP, -, rfl, hEnv1, -⟩ := CmdType.preprocess_inv C Env _ _ _ hpre
      rw [(CmdType.postprocess_inv _ _ _ _ _ hpost).2, hEnv1]
      exact hupdate ⟨_, _, _, _, rfl⟩
    | setDet hlookup hinf hunif => exact htrans (hinfer hinf) (hunifyTypes hunif)
    | setNondet => exact hgen (SourceExpr.GenOnly.refl Env)
    | assert hinf | assume hinf | cover hinf => exact hinfer hinf
  | call hproc hlhsSome hwf hlhs hsig hres hunif =>
    have hg1 := Identifier.instantiateAndSubsts_genOnly _ C Env _ _ hlhs
    have hg2 := LMonoTySignature.instantiate_genOnly C _ _ _ _ _ hsig
    exact htrans (hgen hg1)
      (htrans (hgen hg2) (htrans (hresolves (hg1.trans hg2) hres) (hunify hunif)))

/-! ### Command checking preserves the lower scopes and the aliases -/

/-- `Env'` has the same scopes below the newest one as `Env`, up to lookup equivalence, and the
    same alias list. -/
private structure ContextTailPreserved (Env Env' : TEnv Unit) : Prop where
  types : HMaps.Equiv Env'.context.types.pop Env.context.types.pop
  aliases : Env'.context.aliases = Env.context.aliases

/-- Context-tail preservation composes across consecutive environment steps. -/
private theorem ContextTailPreserved.trans
    {Env₁ Env₂ Env₃ : TEnv Unit}
    (h₁₂ : ContextTailPreserved Env₁ Env₂)
    (h₂₃ : ContextTailPreserved Env₂ Env₃) :
    ContextTailPreserved Env₁ Env₃ :=
  ⟨h₂₃.types.trans h₁₂.types, h₂₃.aliases.trans h₁₂.aliases⟩

/-- Environments with equal contexts preserve their context tail. -/
private theorem ContextTailPreserved.of_context_eq
    {Env Env' : TEnv Unit} (h : Env'.context = Env.context) :
    ContextTailPreserved Env Env' := by
  constructor
  · rw [h]
  · exact congrArg TContext.aliases h

/-- Adding a local binding changes only the newest type scope. -/
private theorem ContextTailPreserved.update
    (Env : TEnv Unit) (x : CoreIdent) (ty : LTy) :
    ContextTailPreserved Env (CmdType.update Env x ty) := by
  constructor
  · simp only [CmdType.update, TEnv.addInNewestContext, TEnv.updateContext, TEnv.context]
    cases Env.genEnv.context.types with
    | nil => exact True.intro
    | cons scope rest => exact HMaps.Equiv.refl rest
  · rfl

/-- Resolving one Core source expression preserves the context tail. -/
private theorem resolveSource_context_tail
    (e : Expression.Expr) (et : LExprT CoreLParams.mono)
    (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (h : SourceExpr.resolve C Env e = .ok (et, Env')) :
    ContextTailPreserved Env Env' := by
  have hpop := SourceExpr.resolve_context_pop_equiv C Env Env' e et h
  exact ⟨hpop.1, hpop.2⟩

/-- Resolving a list of Core source expressions preserves the context tail. -/
private theorem resolveSources_context_tail
    (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (es : List Expression.Expr) (ets : List (LExprT CoreLParams.mono))
    (h : SourceExpr.resolves C Env es = .ok (ets, Env')) :
    ContextTailPreserved Env Env' := by
  change SourceExpr.resolves C Env es = .ok (ets, Env') at h
  have hpop := SourceExpr.resolves_context_pop_equiv C Env Env' es ets h
  exact ⟨hpop.1, hpop.2⟩

/-- `typeCheckCmd` preserves every scope below the newest, up to lookup equivalence, and the
    alias list. -/
theorem Statement.typeCheckCmd_preserves_context
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program) (cmd cmd' : Command)
    (h : Statement.typeCheckCmd C Env P cmd = .ok (cmd', Env')) :
    Strata.Util.HMaps.Equiv (Env'.context.types.pop) (Env.context.types.pop) ∧
      Env'.context.aliases = Env.context.aliases := by
  have hctx : ContextTailPreserved Env Env' := by
    refine CmdRun.rel ContextTailPreserved (Statement.typeCheckCmd_ok_inv h) ?_ ?_ ?_ ?_ ?_ ?_
    · intro E1 E2 E3 h12 h23
      exact h12.trans h23
    · intro E E' hg
      exact ContextTailPreserved.of_context_eq hg.context
    · intro E' e et hres
      exact resolveSource_context_tail e et C Env E' hres
    · intro E E' es ets _ hres
      exact resolveSources_context_tail C E E' es ets hres
    · intro E cs Sx _
      exact ContextTailPreserved.of_context_eq rfl
    · intro E x ty _
      exact ContextTailPreserved.update E x ty
  exact ⟨hctx.types, hctx.aliases⟩

end Core

end -- public section
