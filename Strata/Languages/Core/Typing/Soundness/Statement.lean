/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.StatementType
public import Strata.Languages.Core.Typing.Props.StatementTypeProps
public import Strata.Languages.Core.FunctionType
public import Strata.Languages.Core.Typing.Spec.StatementTypeSpec
public import Strata.Languages.Core.Typing.Soundness.TypingAssumptions
public import Strata.Languages.Core.Typing.Soundness.Command
public import Strata.Languages.Core.Typing.Soundness.Function
public import Strata.Languages.Core.Typing.Soundness.WrittenTyVarScope
public import Strata.DL.Lambda.LExprTypeSpec
public import Strata.DL.Lambda.LExprTypeSpecProps
public import Strata.DL.Lambda.Denote.LExprAnnotatedProps
public import Strata.DL.Lambda.LExprT
public import Strata.DL.Lambda.FactoryWF
public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Lambda.Denote.LExprResolveAnnotated
public import Strata.Util.HMapsProps
public import Strata.Util.ListMapProps
public import Strata.Util.ListUtilsProps
import Strata.Languages.Core.StatementProps
import Strata.Languages.Core.Typing.Props.StatementEraseProps
import Strata.Languages.Core.Typing.Props.ExprEraseProps
import all Strata.Languages.Core.WrittenTyVarScope
import Strata.Languages.Core.Typing.Soundness.TypeDecl
import all Strata.Languages.Core.Typing.Props.StatementTypeProps
import Strata.Languages.Core.Typing.Spec.CmdTypeSpec
import Strata.Languages.Core.Typing.Spec.CommandTypeSpec
import Strata.Languages.Core.Typing.Spec.FunctionTypeSpec
import Strata.DL.Lambda.LExprAnnotRel
import Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.Denote.LExprDenoteTySubst
import Strata.DL.Imperative.Cmd
import Strata.DL.Imperative.CmdType
import Strata.Languages.Core.CmdType
import Strata.Languages.Core.TypeSkolem
import Strata.Languages.Core.Typing.Spec.TypeSpecShared
import all Strata.Languages.Core.Typing.Soundness.Command
import Strata.DL.Imperative.StmtProps
import Strata.Languages.Core.StatementProps
import Strata.DL.Lambda.LTyUnify
import Strata.DL.Lambda.LExprProps
import Strata.DL.Lambda.LExprEvalFuelProps
import all Strata.Languages.Core.TypeDecl
import Strata.DL.Lambda.FactoryProps
import Strata.DL.Lambda.LTyProps
import Strata.Languages.Core.Typing.Spec.NamesWF

/-! # Soundness of the executable statement typechecker
Key result: `Statement.typeCheckAux_sound_visible_withSource` (input soundness). -/

namespace Core

open Lambda Imperative
open TypeSpec
open WrittenTyVarScope (ScopeMap ScopeState renameCmd renameExpr renameExprOrNondet
  unboundAnnotVar?)

/-! ## Statement-walk inversion -/

/-- An `ite` condition or loop guard the checker accepts: a deterministic one resolves to a
    `bool` expression; a nondeterministic one is kept. -/
def CondChecked (C : LContext CoreLParams) (Env : TEnv Unit) :
    ExprOrNondet Expression → ExprOrNondet Expression → TEnv Unit → Prop
  | .det c, condElab, Ec => ∃ conda,
      SourceExpr.resolve C Env c = .ok (conda, Ec) ∧
      conda.toLMonoTy = .tcons "bool" [] ∧ condElab = .det conda.unresolved
  | .nondet, condElab, Ec => condElab = .nondet ∧ Ec = Env

/-- A loop measure the checker accepts: a present one resolves to an `int` expression; an absent
    one stays absent. -/
def MeasureChecked (C : LContext CoreLParams) (Env : TEnv Unit) :
    Option Expression.Expr → Option Expression.Expr → TEnv Unit → Prop
  | some m, measureElab, Em => ∃ ma,
      SourceExpr.resolve C Env m = .ok (ma, Em) ∧
      ma.toLMonoTy = .tcons "int" [] ∧ measureElab = some ma.unresolved
  | none, measureElab, Em => measureElab = none ∧ Em = Env

/-- Loop invariants the checker accepts: a left-to-right fold that resolves each invariant to a
    `bool` expression. -/
def InvariantsChecked (C : LContext CoreLParams) (Env : TEnv Unit)
    (invariant invElab : List (String × Expression.Expr)) (Efold : TEnv Unit) : Prop :=
  ∃ (step : (List (String × LExprT CoreLParams.mono) × TEnv Unit) →
        (String × Expression.Expr) →
        Except Strata.Message (List (String × LExprT CoreLParams.mono) × TEnv Unit))
    (it : List (String × LExprT CoreLParams.mono)),
    (∀ acc E lbl i r, step (acc, E) (lbl, i) = .ok r →
      ∃ ia E',
        r = (acc ++ [(lbl, ia)], E') ∧
        SourceExpr.resolve C E i = .ok (ia, E') ∧
        ia.toLMonoTy = LMonoTy.bool) ∧
    invariant.foldlM step ([], Env) = .ok (it, Efold) ∧
    invElab = it.map (fun x => (x.1, x.2.unresolved))

/-- A successful block check returns the input `C`. When the body declares a variable at its top
    level or the context has no scope, it walks the body under a pushed scope and pops it;
    otherwise it walks the body in the input context. -/
private theorem goBlock_ok_inv {P : Program} {op : Option Procedure} {C C' : LContext CoreLParams}
    {Env Env' : TEnv Unit} {bss acc ss' : List Statement} {labels : List String}
    {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.goBlock P op C Env bss acc labels m st
      = .ok (ss', Env', C', st')) :
    ((Statement.hasTopLevelInit bss || Env.context.types.isEmpty) = true ∧
      ∃ Ego Cgo, @Core.Statement.typeCheckAux.go P op C Env.pushEmptyContext bss acc
        labels m st = .ok (ss', Ego, Cgo, st') ∧ Env' = Ego.popContext ∧ C' = C) ∨
    ((Statement.hasTopLevelInit bss || Env.context.types.isEmpty) = false ∧
      Statement.hasTopLevelInit bss = false ∧ Env.context.types ≠ [] ∧
      ∃ Cgo, @Core.Statement.typeCheckAux.go P op C Env bss acc labels m st
        = .ok (ss', Env', Cgo, st') ∧ C' = C) := by
  rw [Core.Statement.typeCheckAux.goBlock] at h
  obtain ⟨⟨bss', Ego, Cgo, stg⟩, hg, h⟩ := (Except.bind_is_ok _ _ _).mp h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, hEnv, rfl, rfl⟩ := h
  cases hpush : (Statement.hasTopLevelInit bss || Env.context.types.isEmpty) with
  | true =>
    simp only [hpush, ↓reduceIte] at hg hEnv
    exact Or.inl ⟨rfl, Ego, Cgo, hg, hEnv.symm, rfl⟩
  | false =>
    obtain ⟨hinit, hempty⟩ := Bool.or_eq_false_iff.mp hpush
    simp only [hpush, Bool.false_eq_true, ↓reduceIte] at hg hEnv
    subst hEnv
    have hne : Env.context.types ≠ [] := fun hnil =>
      Bool.false_ne_true (hempty.symm.trans (Strata.Util.HMaps.isEmpty_iff_eq_nil.mpr hnil))
    exact Or.inr ⟨rfl, hinit, hne, Cgo, hg, rfl⟩

/-- A successful block check returns the input `C`. -/
private theorem goBlock_ok_lctx {P : Program} {op : Option Procedure} {C C' : LContext CoreLParams}
    {Env Env' : TEnv Unit} {bss acc ss' : List Statement} {labels : List String}
    {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.goBlock P op C Env bss acc labels m st
      = .ok (ss', Env', C', st')) : C' = C := by
  rcases goBlock_ok_inv h with ⟨-, -, -, -, -, hC⟩ | ⟨-, -, -, -, -, hC⟩
  · exact hC
  · exact hC

/-- If `s :: ss` has no top-level declaration, `s` is not a declaration and `ss` has none. -/
private theorem hasTopLevelInit_cons_eq_false {s : Statement} {ss : List Statement}
    (h : Statement.hasTopLevelInit (s :: ss) = false) :
    (∀ x xty e md, s ≠ .cmd (.cmd (.init x xty e md))) ∧
      Statement.hasTopLevelInit ss = false := by
  simp only [Statement.hasTopLevelInit, List.any_cons, Bool.or_eq_false_iff] at h ⊢
  refine ⟨?_, h.2⟩
  intro x xty e md hs
  subst hs
  simp at h

/-- Renaming the type variables of a command that is not a declaration gives no declaration. -/
private theorem renameCmd_noInit (rigid : List TyIdentifier) (m : ScopeMap) (st : ScopeState)
    {cmd : Command} (hni : ∀ x xty e md, cmd ≠ .cmd (.init x xty e md)) :
    ∀ x xty e md, (renameCmd rigid m st cmd).1 ≠ .cmd (.init x xty e md) := by
  intro x xty e md hc
  rcases cmd with ⟨⟨x', xty', e', md'⟩ | _ | _ | _ | _⟩ | _
  · exact hni x' xty' e' md' rfl
  all_goals simp [renameCmd] at hc

/-- After a successful scope check, no expression of the list has an unbound annotation
    variable. -/
private theorem checkAnnotsInScope_ok {writable : Bool} {rigid : List TyIdentifier} {m : ScopeMap}
    {es : List Expression.Expr} {u : Unit}
    (h : Statement.checkAnnotsInScope writable rigid m es = .ok u) :
    ∀ e ∈ es, unboundAnnotVar? writable rigid m e = none := by
  unfold Statement.checkAnnotsInScope at h
  split at h
  · cases h
  · rename_i hnone
    rw [unboundAnnotMsg?_eq, Option.map_eq_none_iff] at hnone
    exact List.findSome?_eq_none_iff.mp hnone

/-- A successful walk step on a command checks the renamed command, whose annotation type
    variables are all rigid or in scope, and continues with the checked command. -/
private theorem go_cmd_inv {P : Program} {op : Option Procedure} {C C' : LContext CoreLParams}
    {Env Env' : TEnv Unit} {cmd : Command} {srest acc ss' : List Statement}
    {labels : List String} {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.go P op C Env (Stmt.cmd cmd :: srest) acc
      labels m st = .ok (ss', Env', C', st')) :
    ∃ c' Env1,
      Statement.typeCheckCmd C Env P (renameCmd C.rigidTypeVars m st cmd).1 = .ok (c', Env1) ∧
      (∀ e ∈ Statement.cmdExprs cmd,
        unboundAnnotVar? false C.rigidTypeVars (renameCmd C.rigidTypeVars m st cmd).2.1 e
          = none) ∧
      @Core.Statement.typeCheckAux.go P op C Env1 srest (Stmt.cmd c' :: acc) labels
        (renameCmd C.rigidTypeVars m st cmd).2.1 (renameCmd C.rigidTypeVars m st cmd).2.2
        = .ok (ss', Env', C', st') := by
  rw [Core.Statement.typeCheckAux.go.eq_def] at h
  dsimp only at h
  obtain ⟨u, hscope, h⟩ := (Except.bind_is_ok _ _ _).mp h
  obtain ⟨⟨c', Env1⟩, htc, h⟩ := (Except.bind_is_ok _ _ _).mp h
  exact ⟨c', Env1, htc, checkAnnotsInScope_ok (Except.mapError_ok_h' hscope), h⟩

/-- A successful walk step on a labeled block has a label no enclosing block uses, checks the
    body as a block under the extended label list, and continues with the checked block. -/
private theorem go_block_inv {P : Program} {op : Option Procedure} {C C' : LContext CoreLParams}
    {Env Env' : TEnv Unit} {label : String} {bss : List Statement} {md : MetaData Expression}
    {srest acc ss' : List Statement} {labels : List String} {m : ScopeMap}
    {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.go P op C Env
      (Stmt.block label bss md :: srest) acc labels m st = .ok (ss', Env', C', st')) :
    ¬ labels.contains label = true ∧
      ∃ bss' Eb stb, @Core.Statement.typeCheckAux.goBlock P op C Env bss []
          (label :: labels) m st = .ok (bss', Eb, C, stb) ∧
        @Core.Statement.typeCheckAux.go P op C Eb srest
          (Stmt.block label bss' md :: acc) labels m stb = .ok (ss', Env', C', st') := by
  rw [Core.Statement.typeCheckAux.go.eq_def] at h
  dsimp only at h
  split at h
  · simp only [bind, Except.bind, reduceCtorEq] at h
  rename_i hcon
  cases hgb : @Core.Statement.typeCheckAux.goBlock P op C Env bss []
      (label :: labels) m st with
  | error e =>
    rw [hgb] at h
    simp only [bind, Except.bind, reduceCtorEq] at h
  | ok r =>
    obtain ⟨bss', Eb, Cb, stb⟩ := r
    rw [hgb] at h
    obtain rfl := goBlock_ok_lctx hgb
    exact ⟨hcon, bss', Eb, stb, rfl, h⟩

/-- A successful walk step on an `exit` happens inside a procedure, targets an enclosing block
    label, and continues with the `exit` recorded unchanged. -/
private theorem go_exit_inv {P : Program} {op : Option Procedure} {C C' : LContext CoreLParams}
    {Env Env' : TEnv Unit} {l : String} {md : MetaData Expression}
    {srest acc ss' : List Statement} {labels : List String} {m : ScopeMap}
    {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.go P op C Env (Stmt.exit l md :: srest) acc
      labels m st = .ok (ss', Env', C', st')) :
    op.isSome = true ∧ labels.contains l = true ∧
      @Core.Statement.typeCheckAux.go P op C Env srest (Stmt.exit l md :: acc)
        labels m st = .ok (ss', Env', C', st') := by
  rw [Core.Statement.typeCheckAux.go.eq_def] at h
  dsimp only at h
  split at h
  · split at h
    · rename_i hc
      exact ⟨rfl, hc, h⟩
    · simp only [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch,
        bind, Except.bind, reduceCtorEq] at h
  · simp only [tryCatch, tryCatchThe, MonadExceptOf.tryCatch,
      Except.tryCatch, bind, Except.bind, reduceCtorEq] at h

/-- A successful walk step on a local type declaration registers it with
    `TypeConstructor.typeCheck` and continues in the returned context. -/
private theorem go_typeDecl_ok_inv {P : Program} {op : Option Procedure}
    {C C' : LContext CoreLParams}
    {Env Env' : TEnv Unit} {tc : TypeConstructor} {md : MetaData Expression}
    {srest acc ss' : List Statement} {labels : List String} {m : ScopeMap}
    {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.go P op C Env (Stmt.typeDecl tc md :: srest)
      acc labels m st = .ok (ss', Env', C', st')) :
    ∃ Cnew, TypeConstructor.typeCheck tc (.bodyLocal P.getNames) C Env = .ok Cnew ∧
      @Core.Statement.typeCheckAux.go P op Cnew Env srest
        (Stmt.typeDecl tc md :: acc) labels m st = .ok (ss', Env', C', st') := by
  rw [Core.Statement.typeCheckAux.go.eq_def] at h
  dsimp only at h
  cases htc : TypeConstructor.typeCheck tc (.bodyLocal P.getNames) C Env with
  | error e =>
    rw [htc] at h
    simp only [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch,
      bind, Except.bind, reduceCtorEq] at h
  | ok Cnew =>
    rw [htc] at h
    exact ⟨Cnew, rfl, h⟩

/-- After an `ite` condition, a successful step checks the then-branch and then the else-branch
    as blocks, threading the environment and walk state. -/
private theorem ite_branches_inv {P : Program} {op : Option Procedure} {C : LContext CoreLParams}
    {Ec : TEnv Unit} {tss ess : List Statement} {labels : List String}
    {condElab : ExprOrNondet Expression} {md : MetaData Expression} {m : ScopeMap}
    {stc : ScopeState}
    {a : Statement × TEnv Unit × LContext CoreLParams × ScopeMap × ScopeState}
    (h : (@Core.Statement.typeCheckAux.goBlock P op C Ec tss [] labels m stc).bind
      (fun v => (@Core.Statement.typeCheckAux.goBlock P op v.2.2.1 v.2.1 ess []
        labels m v.2.2.2).bind
          (fun v1 => .ok (Stmt.ite condElab v.1 v1.1 md, v1.2.1, v1.2.2.1, m, v1.2.2.2)))
      = .ok a) :
    ∃ tss' Et stt ess' Ee ste,
      @Core.Statement.typeCheckAux.goBlock P op C Ec tss [] labels m stc
        = .ok (tss', Et, C, stt) ∧
      @Core.Statement.typeCheckAux.goBlock P op C Et ess [] labels m stt
        = .ok (ess', Ee, C, ste) ∧
      a = (Stmt.ite condElab tss' ess' md, Ee, C, m, ste) := by
  obtain ⟨⟨tss', Et, Ct, stt⟩, hgt, h⟩ := (Except.bind_is_ok _ _ _).mp h
  have hCt := goBlock_ok_lctx hgt
  subst Ct
  obtain ⟨⟨ess', Ee, Ce, ste⟩, hge, h⟩ := (Except.bind_is_ok _ _ _).mp h
  have hCe := goBlock_ok_lctx hge
  subst Ce
  simp only [Except.ok.injEq] at h
  exact ⟨tss', Et, stt, ess', Ee, ste, hgt, hge, h.symm⟩

/-- A successful walk step on an `ite` checks the renamed condition, whose annotation type
    variables are all rigid or in scope, then both branches as blocks in turn, and continues with
    the checked `ite`. -/
private theorem go_ite_inv {P : Program} {op : Option Procedure} {C C' : LContext CoreLParams}
    {Env Env' : TEnv Unit} {cond : ExprOrNondet Expression} {tss ess : List Statement}
    {md : MetaData Expression} {srest acc ss' : List Statement} {labels : List String}
    {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.go P op C Env
      (Stmt.ite cond tss ess md :: srest) acc labels m st = .ok (ss', Env', C', st')) :
    ∃ condElab Ec tss' Et stt ess' Ee ste,
      CondChecked C Env (renameExprOrNondet m cond) condElab Ec ∧
      (∀ e ∈ cond.toList, unboundAnnotVar? false C.rigidTypeVars m e = none) ∧
      @Core.Statement.typeCheckAux.goBlock P op C Ec tss [] labels m st
        = .ok (tss', Et, C, stt) ∧
      @Core.Statement.typeCheckAux.goBlock P op C Et ess [] labels m stt
        = .ok (ess', Ee, C, ste) ∧
      @Core.Statement.typeCheckAux.go P op C Ee srest
        (Stmt.ite condElab tss' ess' md :: acc) labels m ste = .ok (ss', Env', C', st') := by
  rw [Core.Statement.typeCheckAux.go.eq_def] at h
  dsimp only at h
  simp only [bind, Except.bind, Except.mapError, tryCatch, tryCatchThe,
    MonadExceptOf.tryCatch, Except.tryCatch] at h
  elim_err h with vO heqO
  elim_err heqO with a heqT
  simp only [Except.ok.injEq] at heqO
  subst heqO
  elim_err heqT with u hscope
  cases cond with
  | det c =>
    simp only [renameExprOrNondet, ExprOrNondet.map] at heqT ⊢
    elim_err heqT with rc hrcs
    obtain ⟨conda, Ec⟩ := rc
    elim_err heqT with hbool
    have hc : CondChecked C Env (.det (renameExpr m c)) (.det conda.unresolved) Ec := by
      refine ⟨conda, ?_, hbool, rfl⟩
      split at hrcs
      · simp at hrcs
      · rename_i hrcr
        simp only [Except.ok.injEq] at hrcs
        rw [SourceExpr.orFreeVarError_eq_ok.mp hrcr, hrcs]
    obtain ⟨tss', Et, stt, ess', Ee, ste, hgt, hge, rfl⟩ := ite_branches_inv heqT
    exact ⟨_, _, tss', Et, stt, ess', Ee, ste, hc, checkAnnotsInScope_ok hscope, hgt, hge, h⟩
  | nondet =>
    simp only [renameExprOrNondet, ExprOrNondet.map] at heqT ⊢
    obtain ⟨tss', Et, stt, ess', Ee, ste, hgt, hge, rfl⟩ := ite_branches_inv heqT
    exact ⟨_, _, tss', Et, stt, ess', Ee, ste, ⟨rfl, rfl⟩,
      fun e he => by simp only [ExprOrNondet.toList, List.not_mem_nil] at he, hgt, hge, h⟩

/-- A successful step of the checker's loop-invariant fold appends the invariant, which resolves
    to a `bool` expression. -/
private theorem loop_invariant_check_step_ok
    (Cx : LContext CoreLParams) (guard : ExprOrNondet Core.Expression)
    (measure : Option Core.Expression.Expr) (invariant : List (String × Core.Expression.Expr))
    (bss : List Statement) (md : MetaData Core.Expression) :
    ∀ acc E lbl i r,
      (fun ((acc, E) : List (String × LExprT CoreLParams.mono) × TEnv Unit)
          ((lbl, i) : String × Core.Expression.Expr) => do
        let (ia, E') ←
          SourceExpr.orFreeVarError
            (fun _ => E.freeVarCheck i (fun _ => f!"[{Stmt.loop guard measure invariant bss md}]"))
            (SourceExpr.resolve Cx E i) |>.mapError Strata.Message.fromFormat
        if ia.toLMonoTy == LMonoTy.bool then
          .ok (acc ++ [(lbl, ia)], E')
        else
          .error <| md.toDiagnosticF
            f!"[{Stmt.loop guard measure invariant bss md}]: Loop's invariant {i} is not of type \
              `bool`!"
      ) (acc, E) (lbl, i) = .ok r →
      ∃ ia E',
        r = (acc ++ [(lbl, ia)], E') ∧
        SourceExpr.resolve Cx E i = .ok (ia, E') ∧
        ia.toLMonoTy = LMonoTy.bool := by
  intro acc E lbl i r hstep
  dsimp only at hstep
  simp only [bind, Except.bind] at hstep
  elim_err hstep with result hresolve
  elim_err hstep with hbool
  obtain ⟨ia, E'⟩ := result
  refine ⟨ia, E', ?_,
    SourceExpr.orFreeVarError_eq_ok.mp (Except.mapError_ok_h' hresolve), eq_of_beq hbool⟩
  simp only [Except.ok.injEq] at hstep
  exact hstep.symm

/-- A successful walk step on a loop checks the renamed guard, measure and invariants in turn,
    whose annotation type variables are all rigid or in scope, then the body as a block, and
    continues with the checked loop. -/
private theorem go_loop_inv {P : Program} {op : Option Procedure} {C C' : LContext CoreLParams}
    {Env Env' : TEnv Unit} {guard : ExprOrNondet Expression} {measure : Option Expression.Expr}
    {invariant : List (String × Expression.Expr)} {bss : List Statement}
    {md : MetaData Expression} {srest acc ss' : List Statement} {labels : List String}
    {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.go P op C Env
      (Stmt.loop guard measure invariant bss md :: srest) acc labels m st
        = .ok (ss', Env', C', st')) :
    ∃ guardElab Eg measureElab Em invElab Efold bss' Eb stb,
      CondChecked C Env (renameExprOrNondet m guard) guardElab Eg ∧
      MeasureChecked C Eg (measure.map (renameExpr m)) measureElab Em ∧
      InvariantsChecked C Em (invariant.map (fun (l, i) => (l, renameExpr m i))) invElab Efold ∧
      (∀ e ∈ Statement.loopExprs guard measure invariant,
        unboundAnnotVar? false C.rigidTypeVars m e = none) ∧
      @Core.Statement.typeCheckAux.goBlock P op C Efold bss [] labels m st
        = .ok (bss', Eb, C, stb) ∧
      @Core.Statement.typeCheckAux.go P op C Eb srest
        (Stmt.loop guardElab measureElab invElab bss' md :: acc) labels m stb
        = .ok (ss', Env', C', st') := by
  rw [Core.Statement.typeCheckAux.go.eq_def] at h
  dsimp (config := {zeta := false}) only at h
  obtain ⟨a, hbody, h⟩ := (Except.bind_is_ok _ _ _).mp h
  have hbody := Except.ok_of_tryCatch hbody (fun e => ⟨_, rfl⟩)
  obtain ⟨u, hscope, hbody⟩ := (Except.bind_is_ok _ _ _).mp hbody
  extract_lets jp at hbody
  have hjp : ∀ gres, jp gres = .ok a →
      ∃ measureElab Em invElab Efold bss' Eb stb,
        MeasureChecked C gres.2 (measure.map (renameExpr m)) measureElab Em ∧
        InvariantsChecked C Em (invariant.map (fun (l, i) => (l, renameExpr m i))) invElab
          Efold ∧
        @Core.Statement.typeCheckAux.goBlock P op C Efold bss [] labels m st
          = .ok (bss', Eb, C, stb) ∧
        a = (Stmt.loop (match gres.1 with
                | some e => ExprOrNondet.det e.unresolved
                | none => ExprOrNondet.nondet)
              measureElab invElab bss' md, Eb, C, m, stb) := by
    intro gres hj
    simp only [jp] at hj
    obtain ⟨mres, hm, hj⟩ := (Except.bind_is_ok _ _ _).mp hj
    obtain ⟨ires, hi, hj⟩ := (Except.bind_is_ok _ _ _).mp hj
    have hint : ∀ ma, mres.1 = some ma → ma.toLMonoTy = .tcons "int" [] := by
      intro ma hma
      rw [hma] at hj
      dsimp only [Option.map] at hj
      split at hj
      · rename_i heq
        simp at heq
      · rename_i heq
        simp only [Option.some.injEq] at heq
        exact heq
      · simp at hj
    have hmeas : MeasureChecked C gres.2 (measure.map (renameExpr m))
        (mres.1.map (fun e => e.unresolved)) mres.2 := by
      revert hm
      cases measure.map (renameExpr m) with
      | some me =>
        intro hm
        obtain ⟨d, hrs, hm⟩ := (Except.bind_is_ok _ _ _).mp hm
        simp only [Except.ok.injEq] at hm
        subst hm
        exact ⟨d.1, SourceExpr.orFreeVarError_eq_ok.mp (Except.mapError_ok_h' hrs),
          hint d.1 rfl, rfl⟩
      | none =>
        intro hm
        simp only [Except.ok.injEq] at hm
        subst hm
        exact ⟨rfl, rfl⟩
    obtain ⟨bres, hgb, hres⟩ : ∃ bres,
        @Core.Statement.typeCheckAux.goBlock P op C ires.2 bss [] labels m st
          = .ok bres ∧
        a = (Stmt.loop (match gres.1 with
                | some e => ExprOrNondet.det e.unresolved
                | none => ExprOrNondet.nondet)
              (mres.1.map (fun e => e.unresolved))
              (ires.1.map (fun x => (x.1, x.2.unresolved))) bres.1 md, bres.2.1, bres.2.2.1, m,
              bres.2.2.2) := by
      split at hj
      all_goals first
        | simp at hj
        | (obtain ⟨bres, hgb, hres⟩ := (Except.bind_is_ok _ _ _).mp hj
           simp only [Except.ok.injEq] at hres
           refine ⟨bres, hgb, hres.symm.trans ?_⟩
           obtain ⟨_ | g, _⟩ := gres <;> rfl)
    obtain ⟨bss', Eb, Cb, stb⟩ := bres
    have hCb := goBlock_ok_lctx hgb
    subst Cb
    exact ⟨_, mres.2, _, ires.2, bss', Eb, stb, hmeas,
      ⟨_, ires.1, loop_invariant_check_step_ok C guard measure invariant bss md, hi, rfl⟩,
      hgb, hres⟩
  obtain ⟨gres, guardElab, hcond, hgres, hguardElab⟩ : ∃ gres guardElab,
      CondChecked C Env (renameExprOrNondet m guard) guardElab gres.2 ∧ jp gres = .ok a ∧
      (match gres.1 with
        | some e => ExprOrNondet.det e.unresolved
        | none => ExprOrNondet.nondet) = guardElab := by
    revert hbody
    cases renameExprOrNondet m guard with
    | det g =>
      intro hbody
      obtain ⟨d, hrs, hbody⟩ := (Except.bind_is_ok _ _ _).mp hbody
      extract_lets condty jp2 at hbody
      split at hbody
      · simp [throw, throwThe, MonadExceptOf.throw, Except.bind, bind] at hbody
      · rename_i hbool
        refine ⟨(some d.1, d.2), _,
          ⟨d.1, SourceExpr.orFreeVarError_eq_ok.mp (Except.mapError_ok_h' hrs), ?_, rfl⟩,
          hbody, rfl⟩
        simpa [condty] using hbool
    | nondet =>
      intro hbody
      exact ⟨(none, Env), .nondet, ⟨rfl, rfl⟩, hbody, rfl⟩
  obtain ⟨measureElab, Em, invElab, Efold, bss', Eb, stb, hmeas, hinv, hgb, rfl⟩ :=
    hjp gres hgres
  exact ⟨guardElab, gres.2, measureElab, Em, invElab, Efold, bss', Eb, stb, hcond, hmeas, hinv,
    checkAnnotsInScope_ok hscope, hgb, hguardElab ▸ h⟩

/-- Induction over successful runs of the statement walk `go`, with `motiveB` for nested block
    checks: each statement case gets the checker's acceptance conditions and the sub-runs with
    their induction hypotheses. -/
theorem go_ok_induct {P : Program} {op : Option Procedure}
    (motive motiveB : LContext CoreLParams → TEnv Unit → List Statement → List Statement →
      List String → ScopeMap → ScopeState → List Statement → TEnv Unit → LContext CoreLParams →
      ScopeState → Prop)
    (nil : ∀ C Env acc labels m st, motive C Env [] acc labels m st acc.reverse Env C st)
    (cmd : ∀ C Env acc labels m st srest cmd c' Env1 ss' Env' C' st',
      Statement.typeCheckCmd C Env P (renameCmd C.rigidTypeVars m st cmd).1 = .ok (c', Env1) →
      (∀ e ∈ Statement.cmdExprs cmd,
        unboundAnnotVar? false C.rigidTypeVars (renameCmd C.rigidTypeVars m st cmd).2.1 e
          = none) →
      @Core.Statement.typeCheckAux.go P op C Env1 srest (Stmt.cmd c' :: acc) labels
        (renameCmd C.rigidTypeVars m st cmd).2.1 (renameCmd C.rigidTypeVars m st cmd).2.2
        = .ok (ss', Env', C', st') →
      motive C Env1 srest (Stmt.cmd c' :: acc) labels (renameCmd C.rigidTypeVars m st cmd).2.1
        (renameCmd C.rigidTypeVars m st cmd).2.2 ss' Env' C' st' →
      motive C Env (Stmt.cmd cmd :: srest) acc labels m st ss' Env' C' st')
    (block : ∀ C Env acc labels m st srest label bss md bss' Eb stb ss' Env' C' st',
      ¬ labels.contains label = true →
      @Core.Statement.typeCheckAux.goBlock P op C Env bss [] (label :: labels) m st
        = .ok (bss', Eb, C, stb) →
      motiveB C Env bss [] (label :: labels) m st bss' Eb C stb →
      @Core.Statement.typeCheckAux.go P op C Eb srest
        (Stmt.block label bss' md :: acc) labels m stb = .ok (ss', Env', C', st') →
      motive C Eb srest (Stmt.block label bss' md :: acc) labels m stb ss' Env' C' st' →
      motive C Env (Stmt.block label bss md :: srest) acc labels m st ss' Env' C' st')
    (ite : ∀ C Env acc labels m st srest cond tss ess md condElab Ec tss' Et stt ess' Ee ste ss'
        Env' C' st',
      CondChecked C Env (renameExprOrNondet m cond) condElab Ec →
      (∀ e ∈ cond.toList, unboundAnnotVar? false C.rigidTypeVars m e = none) →
      @Core.Statement.typeCheckAux.goBlock P op C Ec tss [] labels m st
        = .ok (tss', Et, C, stt) →
      motiveB C Ec tss [] labels m st tss' Et C stt →
      @Core.Statement.typeCheckAux.goBlock P op C Et ess [] labels m stt
        = .ok (ess', Ee, C, ste) →
      motiveB C Et ess [] labels m stt ess' Ee C ste →
      @Core.Statement.typeCheckAux.go P op C Ee srest
        (Stmt.ite condElab tss' ess' md :: acc) labels m ste = .ok (ss', Env', C', st') →
      motive C Ee srest (Stmt.ite condElab tss' ess' md :: acc) labels m ste ss' Env' C' st' →
      motive C Env (Stmt.ite cond tss ess md :: srest) acc labels m st ss' Env' C' st')
    (loop : ∀ C Env acc labels m st srest guard measure invariant bss md guardElab Eg measureElab
        Em invElab Efold bss' Eb stb ss' Env' C' st',
      CondChecked C Env (renameExprOrNondet m guard) guardElab Eg →
      MeasureChecked C Eg (measure.map (renameExpr m)) measureElab Em →
      InvariantsChecked C Em (invariant.map (fun (l, i) => (l, renameExpr m i))) invElab Efold →
      (∀ e ∈ Statement.loopExprs guard measure invariant,
        unboundAnnotVar? false C.rigidTypeVars m e = none) →
      @Core.Statement.typeCheckAux.goBlock P op C Efold bss [] labels m st
        = .ok (bss', Eb, C, stb) →
      motiveB C Efold bss [] labels m st bss' Eb C stb →
      @Core.Statement.typeCheckAux.go P op C Eb srest
        (Stmt.loop guardElab measureElab invElab bss' md :: acc) labels m stb
        = .ok (ss', Env', C', st') →
      motive C Eb srest (Stmt.loop guardElab measureElab invElab bss' md :: acc) labels m stb
        ss' Env' C' st' →
      motive C Env (Stmt.loop guard measure invariant bss md :: srest) acc labels m st ss' Env'
        C' st')
    (exit : ∀ C Env acc labels m st srest l md ss' Env' C' st',
      op.isSome = true → labels.contains l = true →
      @Core.Statement.typeCheckAux.go P op C Env srest (Stmt.exit l md :: acc)
        labels m st = .ok (ss', Env', C', st') →
      motive C Env srest (Stmt.exit l md :: acc) labels m st ss' Env' C' st' →
      motive C Env (Stmt.exit l md :: srest) acc labels m st ss' Env' C' st')
    (typeDecl : ∀ C Env acc labels m st srest tc md Cnew ss' Env' C' st',
      TypeConstructor.typeCheck tc (.bodyLocal P.getNames) C Env = .ok Cnew →
      @Core.Statement.typeCheckAux.go P op Cnew Env srest
        (Stmt.typeDecl tc md :: acc) labels m st = .ok (ss', Env', C', st') →
      motive Cnew Env srest (Stmt.typeDecl tc md :: acc) labels m st ss' Env' C' st' →
      motive C Env (Stmt.typeDecl tc md :: srest) acc labels m st ss' Env' C' st')
    (blockScope : ∀ C Env bss acc labels m st ss' Ego Cgo st',
      @Core.Statement.typeCheckAux.go P op C Env.pushEmptyContext bss acc labels m st
        = .ok (ss', Ego, Cgo, st') →
      motive C Env.pushEmptyContext bss acc labels m st ss' Ego Cgo st' →
      motiveB C Env bss acc labels m st ss' Ego.popContext C st')
    (blockFlat : ∀ C Env bss acc labels m st ss' Ego Cgo st',
      Statement.hasTopLevelInit bss = false → Env.context.types ≠ [] →
      @Core.Statement.typeCheckAux.go P op C Env bss acc labels m st
        = .ok (ss', Ego, Cgo, st') →
      motive C Env bss acc labels m st ss' Ego Cgo st' →
      motiveB C Env bss acc labels m st ss' Ego C st') :
    ∀ C Env ss acc labels ss' Env' C' {m st st'},
      @Core.Statement.typeCheckAux.go P op C Env ss acc labels m st
        = .ok (ss', Env', C', st') →
      motive C Env ss acc labels m st ss' Env' C' st' := by
  intro C Env ss acc labels ss' Env' C' m st st' h
  revert ss' Env' C' st' h
  induction C, Env, ss, acc, labels, m, st using
      Core.Statement.typeCheckAux.go.induct P op
    (motive2 := fun C Env bss acc labels m st => ∀ ss' Env' C' st',
      @Core.Statement.typeCheckAux.goBlock P op C Env bss acc labels m st
        = .ok (ss', Env', C', st') →
      motiveB C Env bss acc labels m st ss' Env' C' st') with
  | case1 C Env acc labels m st =>
    intro ss' Env' C' st' h
    simp only [Core.Statement.typeCheckAux.go, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact nil C Env acc labels m st
  | case2 C Env acc labels m st srest c ih =>
    intro ss' Env' C' st' h
    obtain ⟨c', Env1, htc, hscope, hgo⟩ := go_cmd_inv h
    exact cmd C Env acc labels m st srest c c' Env1 ss' Env' C' st' htc hscope hgo
      (ih _ _ _ _ _ _ _ _ hgo)
  | case3 C Env acc labels m st srest label bss md hcon =>
    intro ss' Env' C' st' h
    exact absurd hcon (go_block_inv h).1
  | case4 C Env acc labels m st srest label bss md hcon ih2 ih1 =>
    intro ss' Env' C' st' h
    obtain ⟨-, bss', Eb, stb, hgb, hgo⟩ := go_block_inv h
    exact block C Env acc labels m st srest label bss md bss' Eb stb ss' Env' C' st' hcon
      hgb (ih1 _ _ _ _ hgb) hgo (ih2 _ _ _ _ _ _ _ _ hgo)
  | case5 C Env acc labels m st srest cond tss ess md ihr ihtDet ihe ihtNondet =>
    intro ss' Env' C' st' h
    obtain ⟨condElab, Ec, tss', Et, stt, ess', Ee, ste, hcond, hscope, hgt, hge, hgo⟩ :=
      go_ite_inv h
    have ihThen : motiveB C Ec tss [] labels m st tss' Et C stt := by
      cases hrc : renameExprOrNondet m cond with
      | det c => exact ihtDet Ec _ _ _ _ hgt
      | nondet =>
        rw [hrc] at hcond
        obtain ⟨-, rfl⟩ := hcond
        exact ihtNondet _ _ _ _ hgt
    exact ite C Env acc labels m st srest cond tss ess md condElab Ec tss' Et stt ess' Ee ste ss'
      Env' C' st' hcond hscope hgt ihThen hge (ihe Et C stt _ _ _ _ hge) hgo
      (ihr _ _ _ _ _ _ _ _ hgo)
  | case6 C Env acc labels m st srest guard measure invariant bss md ihr ihb =>
    intro ss' Env' C' st' h
    obtain ⟨guardElab, Eg, measureElab, Em, invElab, Efold, bss', Eb, stb, hg, hm, hi, hscope,
      hgb, hgo⟩ := go_loop_inv h
    exact loop C Env acc labels m st srest guard measure invariant bss md guardElab Eg measureElab
      Em invElab Efold bss' Eb stb ss' Env' C' st' hg hm hi hscope hgb (ihb Efold _ _ _ _ hgb) hgo
      (ihr _ _ _ _ _ _ _ _ hgo)
  | case7 C Env acc labels m st srest l md ih =>
    intro ss' Env' C' st' h
    obtain ⟨hop, hl, hgo⟩ := go_exit_inv h
    exact exit C Env acc labels m st srest l md ss' Env' C' st' hop hl hgo
      (ih _ _ _ _ _ _ _ _ hgo)
  | case8 C Env acc labels m st srest tc md ih =>
    intro ss' Env' C' st' h
    obtain ⟨Cnew, htc, hgo⟩ := go_typeDecl_ok_inv h
    exact typeDecl C Env acc labels m st srest tc md Cnew ss' Env' C' st' htc hgo
      (ih _ _ _ _ _ _ _ _ hgo)
  | case9 C Env bss acc labels m st push ih ss' Env' C' st' h =>
    rcases goBlock_ok_inv h with
      ⟨hpush, Ego, Cgo, hgo, rfl, hC⟩ | ⟨hpush, hinit, hne, Cgo, hgo, hC⟩
    · subst C'
      have hp : push = true := hpush
      simp only [hp, ↓reduceDIte] at ih
      exact blockScope C Env bss acc labels m st ss' Ego Cgo st' hgo (ih _ _ _ hgo)
    · subst C'
      have hp : push = false := hpush
      simp only [hp, Bool.false_eq_true, ↓reduceDIte] at ih
      exact blockFlat C Env bss acc labels m st ss' Env' Cgo st' hinit hne hgo (ih _ _ _ hgo)

/-- A successful run of the statement-list checker is a successful walk from the empty scope
    map and the initial walk state. -/
theorem typeCheckAux_ok_inv {P : Program} {op : Option Procedure}
    {C C' : LContext CoreLParams} {Env Env' : TEnv Unit} {ss ss' : List Statement}
    (h : Statement.typeCheckAux C Env P op ss = .ok (ss', Env', C')) :
    ∃ st', @Core.Statement.typeCheckAux.go P op C Env ss [] [] []
      (WrittenTyVarScope.initState C.rigidTypeVars (Statement.usedTyVars Env) ss)
      = .ok (ss', Env', C', st') := by
  unfold Statement.typeCheckAux at h
  cases hg : @Core.Statement.typeCheckAux.go P op C Env ss [] [] []
      (WrittenTyVarScope.initState C.rigidTypeVars (Statement.usedTyVars Env) ss)
    with
  | error e =>
    rw [hg] at h
    simp only [bind, Except.bind, reduceCtorEq] at h
  | ok r =>
    obtain ⟨ssr, Envr, Cr, str⟩ := r
    rw [hg] at h
    simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨str, rfl⟩

/-! ### Environments reached by source-expression resolution -/

/-- `E'` is reached from `E` by finitely many successful source-expression resolutions under
    `C`. -/
def ResolveChain (C : LContext CoreLParams) (E E' : TEnv Unit) : Prop :=
  ∀ R : TEnv Unit → TEnv Unit → Prop, (∀ E, R E E) →
    (∀ E1 E2 E3, R E1 E2 → R E2 E3 → R E1 E3) →
    (∀ E E' e ea, SourceExpr.resolve C E e = .ok (ea, E') → R E E') → R E E'

/-- Every environment reaches itself. -/
private theorem ResolveChain.refl (C : LContext CoreLParams) (E : TEnv Unit) : ResolveChain C E E :=
  fun _ hrefl _ _ => hrefl E

/-- Reachability by resolution is transitive. -/
private theorem ResolveChain.trans {C : LContext CoreLParams} {E1 E2 E3 : TEnv Unit}
    (h12 : ResolveChain C E1 E2) (h23 : ResolveChain C E2 E3) : ResolveChain C E1 E3 :=
  fun R hrefl htrans hstep => htrans _ _ _ (h12 R hrefl htrans hstep) (h23 R hrefl htrans hstep)

/-- A single successful resolution reaches its result environment. -/
private theorem ResolveChain.of_resolveSource {C : LContext CoreLParams} {E E' : TEnv Unit}
    {e : Expression.Expr} {ea : LExprT CoreLParams.mono}
    (h : SourceExpr.resolve C E e = .ok (ea, E')) : ResolveChain C E E' :=
  fun _ _ _ hstep => hstep _ _ _ _ h

/-- Checking an `ite` condition or a loop guard reaches the environment after the check. -/
private theorem CondChecked.chain {C : LContext CoreLParams} {Env Ec : TEnv Unit}
    {cond condElab : ExprOrNondet Expression} (h : CondChecked C Env cond condElab Ec) :
    ResolveChain C Env Ec := by
  cases cond with
  | det c =>
    obtain ⟨conda, hrs, -, -⟩ := h
    exact ResolveChain.of_resolveSource hrs
  | nondet =>
    obtain ⟨-, rfl⟩ := h
    exact ResolveChain.refl _ _

/-- Checking a loop measure reaches the environment after the check. -/
private theorem MeasureChecked.chain {C : LContext CoreLParams} {Env Em : TEnv Unit}
    {measure measureElab : Option Expression.Expr}
    (h : MeasureChecked C Env measure measureElab Em) : ResolveChain C Env Em := by
  cases measure with
  | some m =>
    obtain ⟨ma, hrs, -, -⟩ := h
    exact ResolveChain.of_resolveSource hrs
  | none =>
    obtain ⟨-, rfl⟩ := h
    exact ResolveChain.refl _ _

/-- Between `Env` and `Efold`, the source invariant `i` resolves to `ia` of type `bool`. -/
def InvariantResolvedAt (C : LContext CoreLParams) (Env Efold : TEnv Unit) (i : Expression.Expr)
    (ia : LExprT CoreLParams.mono) : Prop :=
  ∃ E E', ResolveChain C Env E ∧
    SourceExpr.resolve C E i = .ok (ia, E') ∧ ia.toLMonoTy = LMonoTy.bool ∧
    ResolveChain C E' Efold

/-- Checking loop invariants reaches the environment after the fold; each source invariant is
    resolved within the fold and elaborated under its label, and each elaborated invariant is
    such a resolved one. -/
private theorem InvariantsChecked.chain_mem {C : LContext CoreLParams} {Env Efold : TEnv Unit}
    {invariant invElab : List (String × Expression.Expr)}
    (h : InvariantsChecked C Env invariant invElab Efold) :
    ResolveChain C Env Efold ∧
      (∀ p ∈ invariant, ∃ ia, InvariantResolvedAt C Env Efold p.2 ia ∧
        (p.1, ia.unresolved) ∈ invElab) ∧
      ∀ q ∈ invElab, ∃ i ia, q.2 = ia.unresolved ∧ InvariantResolvedAt C Env Efold i ia := by
  obtain ⟨step, it, hst, hfold, rfl⟩ := h
  suffices key : ∀ (inv : List (String × Expression.Expr)) acc E itout Eout,
      inv.foldlM step (acc, E) = .ok (itout, Eout) →
      ResolveChain C E Eout ∧
        (∀ p ∈ inv, ∃ ia, InvariantResolvedAt C E Eout p.2 ia ∧ (p.1, ia) ∈ itout) ∧
        ∃ new, itout = acc ++ new ∧
          ∀ q ∈ new, ∃ i, InvariantResolvedAt C E Eout i q.2 by
    obtain ⟨hchain, hinv, new, hnew, hq⟩ := key invariant [] Env it Efold hfold
    simp only [List.nil_append] at hnew
    subst hnew
    refine ⟨hchain, ?_, ?_⟩
    · intro p hp
      obtain ⟨ia, hia, hmem⟩ := hinv p hp
      exact ⟨ia, hia, List.mem_map_of_mem (f := fun x => (x.1, x.2.unresolved)) hmem⟩
    · intro q hqm
      simp only [List.mem_map] at hqm
      obtain ⟨r, hr, rfl⟩ := hqm
      obtain ⟨i, hi⟩ := hq r hr
      exact ⟨i, r.2, rfl, hi⟩
  intro inv
  induction inv with
  | nil =>
    intro acc E itout Eout hf
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    exact ⟨ResolveChain.refl C E, fun p hp => absurd hp List.not_mem_nil, [], by simp,
      fun q hq => absurd hq List.not_mem_nil⟩
  | cons hd tl ih =>
    intro acc E itout Eout hf
    obtain ⟨lbl, i⟩ := hd
    rw [List.foldlM_cons] at hf
    obtain ⟨r, hr, hf⟩ := (Except.bind_is_ok _ _ _).mp hf
    obtain ⟨ia, E', rfl, hres, hbool⟩ := hst acc E lbl i r hr
    obtain ⟨hchain, hinv, new, hnew, hq⟩ := ih _ _ _ _ hf
    have hstep := ResolveChain.of_resolveSource hres
    have hhead : InvariantResolvedAt C E Eout i ia :=
      ⟨E, E', ResolveChain.refl C E, hres, hbool, hchain⟩
    have hlift : ∀ j ja, InvariantResolvedAt C E' Eout j ja → InvariantResolvedAt C E Eout j ja :=
      fun j ja ⟨F, F', hF, hresF, hboolF, hF'⟩ =>
        ⟨F, F', hstep.trans hF, hresF, hboolF, hF'⟩
    refine ⟨hstep.trans hchain, ?_, (lbl, ia) :: new, ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · refine ⟨ia, hhead, ?_⟩
        rw [hnew]
        exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
      · obtain ⟨ja, hja, hmem⟩ := hinv p hp
        exact ⟨ja, hlift _ _ hja, hmem⟩
    · rw [hnew]
      simp
    · intro q hqm
      rcases List.mem_cons.mp hqm with rfl | hqm
      · exact ⟨i, hhead⟩
      · obtain ⟨j, hj⟩ := hq q hqm
        exact ⟨j, hlift _ _ hj⟩

/-- Checking a loop's guard, measure and invariants reaches the environment after the invariants. -/
private theorem loopHead_chain {C : LContext CoreLParams} {Env Eg Em Efold : TEnv Unit}
    {guard guardElab : ExprOrNondet Expression} {measure measureElab : Option Expression.Expr}
    {invariant invElab : List (String × Expression.Expr)}
    (hg : CondChecked C Env guard guardElab Eg) (hm : MeasureChecked C Eg measure measureElab Em)
    (hi : InvariantsChecked C Em invariant invElab Efold) : ResolveChain C Env Efold :=
  hg.chain.trans (hm.chain.trans hi.chain_mem.1)

/-- If `E` is well formed with a nonempty scope stack, then `E'` is well formed and has an
    equivalent context. -/
def EnvScopeStep (E E' : TEnv Unit) : Prop :=
  LExpr.TEnvWF (T := CoreLParams) E → E.context.types ≠ [] →
    TContext.Equiv (T := CoreLParams) E'.context E.context ∧ LExpr.TEnvWF (T := CoreLParams) E'

/-- Every environment is related to itself by `EnvScopeStep`. -/
private theorem EnvScopeStep.refl (E : TEnv Unit) : EnvScopeStep E E :=
  fun he _ => ⟨TContext.Equiv.refl _, he⟩

/-- `EnvScopeStep` is transitive. -/
private theorem EnvScopeStep.trans {E1 E2 E3 : TEnv Unit} (h12 : EnvScopeStep E1 E2)
    (h23 : EnvScopeStep E2 E3) : EnvScopeStep E1 E3 := by
  intro he hne
  obtain ⟨heq12, hwf2⟩ := h12 he hne
  obtain ⟨heq23, hwf3⟩ := h23 hwf2 (heq12.symm.types_ne_nil hne)
  exact ⟨heq23.trans heq12, hwf3⟩

/-- An `EnvScopeStep` from a well-formed environment with a nonempty scope stack yields an
    equivalent context, a well-formed environment, and a nonempty scope stack. -/
private theorem EnvScopeStep.facts {E E' : TEnv Unit} (h : EnvScopeStep E E')
    (he : LExpr.TEnvWF (T := CoreLParams) E) (hne : E.context.types ≠ []) :
    TContext.Equiv (T := CoreLParams) E'.context E.context ∧ LExpr.TEnvWF (T := CoreLParams) E' ∧
      E'.context.types ≠ [] :=
  ⟨(h he hne).1, (h he hne).2, (h he hne).1.symm.types_ne_nil hne⟩

/-- An environment reached by resolution is related to the starting one by `EnvScopeStep`. -/
private theorem ResolveChain.scope {C : LContext CoreLParams} {E E' : TEnv Unit}
    (h : ResolveChain C E E') (hf : FactorySigWF C.functions) : EnvScopeStep E E' :=
  h _ EnvScopeStep.refl (fun _ _ _ => EnvScopeStep.trans)
    (fun E E' e ea hrs he hne =>
      ⟨SourceExpr.resolve_context_equiv_of_ne C E E' e ea hrs hne,
        SourceExpr.resolve_TEnvWF C E E' e ea hrs he hf⟩)

/-- If `E` is well formed, then `E'` is well formed and its substitution absorbs that of `E`. -/
def EnvAbsorbStep (E E' : TEnv Unit) : Prop :=
  LExpr.TEnvWF (T := CoreLParams) E →
    LExpr.TEnvWF (T := CoreLParams) E' ∧
      Subst.absorbs E'.stateSubstInfo.subst E.stateSubstInfo.subst

/-- Every environment is related to itself by `EnvAbsorbStep`. -/
private theorem EnvAbsorbStep.refl (E : TEnv Unit) : EnvAbsorbStep E E :=
  fun he => ⟨he, Subst.absorbs_refl _ E.stateSubstInfo.isWF⟩

/-- `EnvAbsorbStep` is transitive. -/
private theorem EnvAbsorbStep.trans {E1 E2 E3 : TEnv Unit} (h12 : EnvAbsorbStep E1 E2)
    (h23 : EnvAbsorbStep E2 E3) : EnvAbsorbStep E1 E3 := by
  intro he
  obtain ⟨hwf2, habs12⟩ := h12 he
  obtain ⟨hwf3, habs23⟩ := h23 hwf2
  exact ⟨hwf3, Subst.absorbs_trans _ _ _ habs12 habs23⟩

/-- An environment reached by resolution is related to the starting one by `EnvAbsorbStep`. -/
private theorem ResolveChain.absorb {C : LContext CoreLParams} {E E' : TEnv Unit}
    (h : ResolveChain C E E') (hf : FactorySigWF C.functions) : EnvAbsorbStep E E' :=
  h _ EnvAbsorbStep.refl (fun _ _ _ => EnvAbsorbStep.trans)
    (fun E E' e ea hrs he =>
      ⟨SourceExpr.resolve_TEnvWF C E E' e ea hrs he hf,
        resolveSource_absorbs e ea C E E' hrs he hf⟩)

/-! ## `go`/`goBlock` scope and well-formedness preservation -/

/-- A successful statement walk never decreases the type-variable generator counter. -/
private theorem go_genState_tyGen_mono
    (C C' : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program)
    (op : Option Procedure) (ss acc ss' : List Statement) (labels : List String)
    {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.go P op C Env ss acc labels m st
      = .ok (ss', Env', C', st')) :
    Env.genEnv.genState.tyGen ≤ Env'.genEnv.genState.tyGen := by
  have hres : ∀ C E E' e ea, SourceExpr.resolve C E e = .ok (ea, E') →
      E.genEnv.genState.tyGen ≤ E'.genEnv.genState.tyGen :=
    fun C E E' e ea hrs => SourceExpr.resolve_genState_tyGen_mono C E E' e ea hrs
  refine go_ok_induct
    (motive := fun _ Env _ _ _ _ _ _ Env' _ _ =>
      Env.genEnv.genState.tyGen ≤ Env'.genEnv.genState.tyGen)
    (motiveB := fun _ Env _ _ _ _ _ _ Env' _ _ =>
      Env.genEnv.genState.tyGen ≤ Env'.genEnv.genState.tyGen)
    ?nil ?cmd ?block ?ite ?loop ?exit ?typeDecl ?blockScope ?blockFlat C Env ss acc labels ss'
    Env' C' h
  case nil => exact fun _ _ _ _ _ _ => Nat.le_refl _
  case cmd =>
    intro C Env _ _ _ _ _ cmd c' Env1 _ _ _ _ htc _ _ ih
    exact Nat.le_trans (Statement.typeCheckCmd_genState_tyGen_mono C Env Env1 P _ c' htc) ih
  case block =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihb _ ih
    exact Nat.le_trans ihb ih
  case ite =>
    intro C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcond _ _ iht _ ihe _ ih
    have hcondMono := hcond.chain
      (fun E E' : TEnv Unit => E.genEnv.genState.tyGen ≤ E'.genEnv.genState.tyGen)
      (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.le_trans) (hres C)
    exact Nat.le_trans hcondMono (Nat.le_trans iht (Nat.le_trans ihe ih))
  case loop =>
    intro C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hg hm hi _ _ ihb _ ih
    have hhead := loopHead_chain hg hm hi
      (fun E E' : TEnv Unit => E.genEnv.genState.tyGen ≤ E'.genEnv.genState.tyGen)
      (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.le_trans) (hres C)
    exact Nat.le_trans hhead (Nat.le_trans ihb ih)
  case exit => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => ih
  case typeDecl => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => ih
  case blockFlat => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => ih
  case blockScope => exact fun _ _ _ _ _ _ _ _ _ _ _ _ ih => ih

/-- Statement-list checking preserves the scopes below the newest and the aliases, keeps the
    environment well formed, and keeps the whole context lookup-equivalent for a list without a
    top-level declaration. -/
private theorem go_scope_facts
    (C C' : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program)
    (op : Option Procedure) (ss acc ss' : List Statement) (labels : List String)
    {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.go P op C Env ss acc labels m st
      = .ok (ss', Env', C', st'))
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions)
    (h_ne : Env.context.types ≠ []) :
    ((Strata.Util.HMaps.Equiv (Env'.context.types.pop) (Env.context.types.pop) ∧
        Env'.context.aliases = Env.context.aliases) ∧
      LExpr.TEnvWF (T := CoreLParams) Env') ∧
    (Statement.hasTopLevelInit ss = false →
      TContext.Equiv (T := CoreLParams) Env'.context Env.context) := by
  have hcomb : ∀ (Env Eb Env' : TEnv Unit) (s : Statement) (srest : List Statement),
      EnvScopeStep Env Eb → LExpr.TEnvWF (T := CoreLParams) Env → Env.context.types ≠ [] →
      (LExpr.TEnvWF (T := CoreLParams) Eb → Eb.context.types ≠ [] →
        ((Strata.Util.HMaps.Equiv (Env'.context.types.pop) (Eb.context.types.pop) ∧
          Env'.context.aliases = Eb.context.aliases) ∧ LExpr.TEnvWF (T := CoreLParams) Env') ∧
        (Statement.hasTopLevelInit srest = false →
          TContext.Equiv (T := CoreLParams) Env'.context Eb.context)) →
      ((Strata.Util.HMaps.Equiv (Env'.context.types.pop) (Env.context.types.pop) ∧
          Env'.context.aliases = Env.context.aliases) ∧ LExpr.TEnvWF (T := CoreLParams) Env') ∧
        (Statement.hasTopLevelInit (s :: srest) = false →
          TContext.Equiv (T := CoreLParams) Env'.context Env.context) := by
    intro Env Eb Env' s srest hR he hne ih
    obtain ⟨heq, hwf⟩ := hR he hne
    obtain ⟨⟨⟨htailPop, htailAl⟩, hEnv'WF⟩, hnoInit⟩ := ih hwf (heq.symm.types_ne_nil hne)
    exact ⟨⟨⟨htailPop.trans (Strata.Util.HMaps.Equiv.pop heq.1), htailAl.trans heq.2⟩, hEnv'WF⟩,
      fun hni => (hnoInit (hasTopLevelInit_cons_eq_false hni).2).trans heq⟩
  refine go_ok_induct
    (motive := fun C Env ss _ _ _ _ _ Env' _ _ =>
      LExpr.TEnvWF (T := CoreLParams) Env → FactorySigWF C.functions → Env.context.types ≠ [] →
      ((Strata.Util.HMaps.Equiv (Env'.context.types.pop) (Env.context.types.pop) ∧
          Env'.context.aliases = Env.context.aliases) ∧ LExpr.TEnvWF (T := CoreLParams) Env') ∧
      (Statement.hasTopLevelInit ss = false →
        TContext.Equiv (T := CoreLParams) Env'.context Env.context))
    (motiveB := fun C Env _ _ _ _ _ _ Env' _ _ => FactorySigWF C.functions → EnvScopeStep Env Env')
    ?nil ?cmd ?block ?ite ?loop ?exit ?typeDecl ?blockScope ?blockFlat C Env ss acc labels ss'
    Env' C' h he hf h_ne
  case nil =>
    exact fun _ _ _ _ _ _ he _ _ =>
      ⟨⟨⟨Strata.Util.HMaps.Equiv.refl _, rfl⟩, he⟩, fun _ => TContext.Equiv.refl _⟩
  case cmd =>
    intro C Env _ _ m st _ cmd c' Env1 _ _ _ _ htc _ _ ih he hf h_ne
    have hwf1 := Statement.typeCheckCmd_preserves_TEnvWF C Env Env1 P _ c' htc he hf
    obtain ⟨⟨⟨htailPop, htailAl⟩, hEnv'WF⟩, hnoInit⟩ :=
      ih hwf1 hf (Statement.typeCheckCmd_preserves_context_types_ne C Env Env1 P _ c' htc h_ne)
    obtain ⟨hstepPop, hstepAl⟩ := Statement.typeCheckCmd_preserves_context C Env Env1 P _ c' htc
    refine ⟨⟨⟨htailPop.trans hstepPop, htailAl.trans hstepAl⟩, hEnv'WF⟩, fun hni => ?_⟩
    obtain ⟨hcmd, hrest⟩ := hasTopLevelInit_cons_eq_false hni
    have hcmdNi : ∀ x xty e md, cmd ≠ .cmd (.init x xty e md) :=
      fun x xty e md hc => hcmd x xty e md (congrArg Stmt.cmd hc)
    exact (hnoInit hrest).trans (Statement.typeCheckCmd_noInit_context_equiv C Env Env1 P _ c' htc
      (renameCmd_noInit C.rigidTypeVars m st hcmdNi) h_ne)
  case block =>
    intro _ Env _ _ _ _ _ _ _ _ _ Eb _ _ _ _ _ _ _ ihb _ ih he hf h_ne
    exact hcomb Env Eb _ _ _ (ihb hf) he h_ne (fun hwf hne => ih hwf hf hne)
  case ite =>
    intro C Env _ _ _ _ _ _ _ _ _ _ Ec _ Et _ _ Ee _ _ _ _ _ hcond _ _ iht _ ihe _ ih he hf h_ne
    have hR : EnvScopeStep Env Ee :=
      (hcond.chain.scope hf).trans ((iht hf).trans (ihe hf))
    exact hcomb Env Ee _ _ _ hR he h_ne (fun hwf hne => ih hwf hf hne)
  case loop =>
    intro C Env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Efold _ Eb _ _ _ _ _ hg hm hi _ _ ihb _ ih he hf h_ne
    have hR : EnvScopeStep Env Eb :=
      ((loopHead_chain hg hm hi).scope hf).trans (ihb hf)
    exact hcomb Env Eb _ _ _ hR he h_ne (fun hwf hne => ih hwf hf hne)
  case exit =>
    intro C Env _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih he hf h_ne
    exact hcomb Env Env _ _ _ (EnvScopeStep.refl Env) he h_ne (fun hwf hne => ih hwf hf hne)
  case typeDecl =>
    intro C Env _ _ _ _ _ tc _ Cnew _ _ _ _ htc _ ih he hf h_ne
    exact hcomb Env Env _ _ _ (EnvScopeStep.refl Env) he h_ne
      (fun hwf hne => ih hwf (TypeConstructor.typeCheck_functions_eq htc ▸ hf) hne)
  case blockScope =>
    intro C Env bss acc labels _ _ _ Ego Cgo _ hgo ih hf he _
    have he1 : LExpr.TEnvWF (T := CoreLParams) Env.pushEmptyContext :=
      pushEmptyContext_preserves_TEnvWF (T := CoreLParams) Env he
    obtain ⟨⟨⟨hgoPop, hgoAl⟩, hEgoWF⟩, -⟩ :=
      ih he1 hf (TEnv.pushEmptyContext_types_ne_nil (T := CoreLParams) Env)
    have hEq0 : TContext.Equiv (T := CoreLParams) Ego.popContext.context Env.context := by
      refine ⟨?_, ?_⟩
      · simp only [TEnv.popContext, TEnv.updateContext, TEnv.context,
          Strata.Util.HMaps.pop] at hgoPop ⊢
        exact hgoPop
      · simp only [TEnv.popContext, TEnv.updateContext, TEnv.context] at hgoAl ⊢
        exact hgoAl
    have hmono : Env.genEnv.genState.tyGen ≤ Ego.genEnv.genState.tyGen :=
      go_genState_tyGen_mono C Cgo Env.pushEmptyContext Ego P op bss acc _ labels hgo
    exact ⟨hEq0, popContext_preserves_TEnvWF (T := CoreLParams) Env Ego he hEgoWF hmono hEq0⟩
  case blockFlat =>
    intro C Env _ _ _ _ _ _ _ _ _ hinit hne _ ih hf he _
    obtain ⟨⟨-, hEgoWF⟩, hnoInit⟩ := ih he hf hne
    exact ⟨hnoInit hinit, hEgoWF⟩

/-- Statement-list checking keeps every alias fully resolved. -/
private theorem go_preserves_aliasesResolved
    (C C' : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program)
    (op : Option Procedure) (ss acc ss' : List Statement) (labels : List String)
    {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.go P op C Env ss acc labels m st
      = .ok (ss', Env', C', st'))
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions)
    (hr : TContext.AliasesResolved Env.context) (h_ne : Env.context.types ≠ []) :
    TContext.AliasesResolved Env'.context := by
  have halias : Env'.context.aliases = Env.context.aliases :=
    (go_scope_facts C C' Env Env' P op ss acc ss' labels h he hf h_ne).1.1.2
  unfold TContext.AliasesResolved at hr ⊢
  rw [halias]
  exact hr

/-! ## Typing a resolved source expression -/

/-- A source expression that resolves at a ground type has that type in the input scope under any
    well-formed substitution absorbing the resolver's. -/
private theorem resolve_ground_HasType_source
    (Cx : LContext CoreLParams) (Env Env' : TEnv Unit)
    (e : Core.Expression.Expr) (et : LExprT CoreLParams.mono) (expected : LMonoTy)
    (hres : SourceExpr.resolve Cx Env e = .ok (et, Env'))
    (hty : et.toLMonoTy = expected)
    (hground : LMonoTy.freeVars expected = [])
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF Cx.functions)
    (hmono : MonoScope Env.context)
    (S : Subst) (habs : Subst.absorbs S Env'.stateSubstInfo.subst) (hSwf : SubstWF S) :
    LExpr.HasType Cx (TContext.subst Env.context S) e (.forAll [] expected) := by
  have hsource := hres
  obtain ⟨EnvR, hdirect, hlinkAbs⟩ :=
    SourceExpr.resolve_link_absorbs Cx Env Env' e et hsource
  have hcore :=
    LExpr.resolve_HasType_core (T := CoreLParams) e et Cx Env EnvR hdirect he hf
      (SourceExpr.resolve_WellScoped Cx Env Env' e et hsource)
  have habsR : Subst.absorbs S EnvR.stateSubstInfo.subst :=
    Subst.absorbs_trans _ _ _ hlinkAbs habs
  have htyped := hcore.1 S habsR hSwf
    (polyKeysFresh_of_MonoScope (T := CoreLParams) S Env.context hmono) e
    (LExpr.AnnotFits.refl _ _ _ e _)
  rw [hty, LMonoTy.subst_ground S expected hground] at htyped
  exact htyped

/-! ## Lexical blocks and checked loop heads -/

/-- Checking a lexical block returns the input `C` and a type scope equivalent to the input one. -/
private theorem goBlock_scoping
    (C C' : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program)
    (op : Option Procedure) (bss : Imperative.Block Core.Expression Core.Command)
    (acc ss' : List Statement) (labels : List String)
    {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.goBlock P op C Env bss acc labels m st
      = .ok (ss', Env', C', st'))
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions) :
    C' = C ∧ TContext.Equiv (T := CoreLParams) Env'.context Env.context := by
  rcases goBlock_ok_inv h with ⟨-, Ego, Cgo, hg, rfl, hC⟩ | ⟨-, hinit, hne, Cgo, hg, hC⟩
  · subst C'
    refine ⟨rfl, ?_⟩
    obtain ⟨htail, halias⟩ :=
      (go_scope_facts C Cgo (Env.pushEmptyContext) Ego P op bss acc ss' labels hg
          (pushEmptyContext_preserves_TEnvWF (T := CoreLParams) Env he) hf
          (TEnv.pushEmptyContext_types_ne_nil (T := CoreLParams) Env)).1.1
    refine ⟨?_, ?_⟩
    · simp only [TEnv.popContext, TEnv.updateContext, TEnv.context, TEnv.pushEmptyContext,
        Strata.Util.HMaps.push, Strata.Util.HMaps.pop] at htail ⊢
      exact htail
    · simp only [TEnv.popContext, TEnv.updateContext, TEnv.context,
        TEnv.pushEmptyContext] at halias ⊢
      exact halias
  · subst C'
    exact ⟨rfl, (go_scope_facts C Cgo Env Env' P op bss acc ss' labels hg he hf hne).2 hinit⟩

/-- Checking a lexical block preserves well-formedness of the type environment. -/
private theorem goBlock_preserves_TEnvWF
    (C C' : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program)
    (op : Option Procedure) (bss : Imperative.Block Core.Expression Core.Command)
    (acc ss' : List Statement) (labels : List String)
    {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.goBlock P op C Env bss acc labels m st
      = .ok (ss', Env', C', st'))
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions) :
    LExpr.TEnvWF (T := CoreLParams) Env' := by
  have hEq0 : TContext.Equiv (T := CoreLParams) Env'.context Env.context :=
    (goBlock_scoping C C' Env Env' P op bss acc ss' labels h he hf).2
  rcases goBlock_ok_inv h with ⟨-, Ego, Cgo, hg, rfl, -⟩ | ⟨-, -, hne, Cgo, hg, -⟩
  · have he1 : LExpr.TEnvWF (T := CoreLParams) (Env.pushEmptyContext) :=
      pushEmptyContext_preserves_TEnvWF (T := CoreLParams) Env he
    have hEgoWF : LExpr.TEnvWF (T := CoreLParams) Ego :=
      (go_scope_facts C Cgo (Env.pushEmptyContext) Ego P op bss acc ss' labels hg he1 hf
          (TEnv.pushEmptyContext_types_ne_nil (T := CoreLParams) Env)).1.2
    have hmono : Env.genEnv.genState.tyGen ≤ Ego.genEnv.genState.tyGen :=
      go_genState_tyGen_mono C Cgo (Env.pushEmptyContext) Ego P op bss acc ss' labels hg
    exact popContext_preserves_TEnvWF (T := CoreLParams) Env Ego he hEgoWF hmono hEq0
  · exact (go_scope_facts C Cgo Env Env' P op bss acc ss' labels hg he hf hne).1.2

/-- A block check relates the environments before and after by `EnvScopeStep`. -/
private theorem EnvScopeStep.of_goBlock {P : Program} {op : Option Procedure}
    {C C' : LContext CoreLParams}
    {Env Env' : TEnv Unit} {bss acc ss' : List Statement} {labels : List String}
    {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.goBlock P op C Env bss acc labels m st
      = .ok (ss', Env', C', st'))
    (hf : FactorySigWF C.functions) : EnvScopeStep Env Env' :=
  fun he _ => ⟨(goBlock_scoping C C' Env Env' P op bss acc ss' labels h he hf).2,
    goBlock_preserves_TEnvWF C C' Env Env' P op bss acc ss' labels h he hf⟩

/-- Checking a lexical block keeps every alias fully resolved. -/
private theorem goBlock_preserves_aliasesResolved
    (C C' : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program)
    (op : Option Procedure) (bss : Imperative.Block Core.Expression Core.Command)
    (acc ss' : List Statement) (labels : List String)
    {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.goBlock P op C Env bss acc labels m st
      = .ok (ss', Env', C', st'))
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions)
    (hr : TContext.AliasesResolved Env.context) :
    TContext.AliasesResolved Env'.context := by
  rcases goBlock_ok_inv h with ⟨-, Ego, Cgo, hg, rfl, -⟩ | ⟨-, -, hne, Cgo, hg, -⟩
  · have hAREgo : Ego.context.AliasesResolved :=
      go_preserves_aliasesResolved C Cgo (Env.pushEmptyContext) Ego P op bss acc ss' labels hg
        (pushEmptyContext_preserves_TEnvWF (T := CoreLParams) Env he) hf
        (TEnv.pushEmptyContext_preserves_aliasesResolved Env hr)
        (TEnv.pushEmptyContext_types_ne_nil (T := CoreLParams) Env)
    exact TEnv.popContext_preserves_aliasesResolved Ego hAREgo
  · exact go_preserves_aliasesResolved C Cgo Env Env' P op bss acc ss' labels hg he hf hr hne

/-! ### Resolved source expressions and checked loop heads -/

/-- A source expression resolved at type `ty`, in an environment reached from a well-formed
    `Env`, has an unresolved form of annotated type `ty`. -/
private theorem resolved_HasTypeA {C : LContext CoreLParams} {Env E E' : TEnv Unit}
    {e : Expression.Expr} {ea : LExprT CoreLParams.mono} {ty : LMonoTy}
    (hchain : ResolveChain C Env E) (hrs : SourceExpr.resolve C E e = .ok (ea, E'))
    (hty : ea.toLMonoTy = ty)
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions)
    (hr : Env.context.AliasesResolved) (h_ne : Env.context.types ≠ []) :
    LExpr.HasTypeA [] ea.unresolved ty := by
  obtain ⟨heq, hwf, -⟩ := (hchain.scope hf).facts he h_ne
  exact hty ▸ resolveSource_HasTypeA e ea C E E' hrs hwf hf (heq.symm.aliasesResolved hr)

/-- A source expression resolved in an environment reached from `Env`, with `S` applied to its
    annotations for an `S` absorbing a later environment's, agrees with the substituted
    alias-free scope of `Env`, when the table's signatures are fixed for the aliases of `Env`. -/
private theorem resolved_annotAgree {C : LContext CoreLParams} {Env E E' Efin : TEnv Unit}
    {e : Expression.Expr} {ea : LExprT CoreLParams.mono}
    (hchain : ResolveChain C Env E) (hrs : SourceExpr.resolve C E e = .ok (ea, E'))
    (hfin : ResolveChain C E' Efin)
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions)
    (hmono : MonoScope Env.context) (h_ne : Env.context.types ≠ [])
    (hsig : FactorySigsFixed Env.context.aliases C.functions)
    (S : Subst) (habs : Subst.absorbs S Efin.stateSubstInfo.subst) :
    TypeSpec.ScopesAnnotAgree C (TContext.subst Env.context.dealias S).types
      (LExpr.applyTypeSubst ea.unresolved S) := by
  obtain ⟨heq, hwf, -⟩ := (hchain.scope hf).facts he h_ne
  have habsE' : Subst.absorbs S E'.stateSubstInfo.subst :=
    Subst.absorbs_trans _ _ _
      ((hfin.absorb hf) (SourceExpr.resolve_TEnvWF C E E' e ea hrs hwf hf)).2 habs
  refine resolveSource_annotAgree_dealias e ea C E E' hrs hwf hf
    (MonoScope_of_findEq heq.toFindEq hmono) ?_ heq.symm.toFindEq S habsE'
  rw [heq.2]
  exact hsig

/-- After the checker accepts a loop head, the elaborated guard and invariants have annotated
    type `bool` and the measure `int`; the final environment is well formed, with resolved
    aliases and an equivalent context. -/
private theorem loopHead_annotated {C : LContext CoreLParams} {Env Eg Em Efold : TEnv Unit}
    {guard guardElab : ExprOrNondet Expression} {measure measureElab : Option Expression.Expr}
    {invariant invElab : List (String × Expression.Expr)}
    (hg : CondChecked C Env guard guardElab Eg) (hm : MeasureChecked C Eg measure measureElab Em)
    (hi : InvariantsChecked C Em invariant invElab Efold)
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions)
    (hr : Env.context.AliasesResolved) (h_ne : Env.context.types ≠ []) :
    (∀ g, guardElab = ExprOrNondet.det g → LExpr.HasTypeA [] g (.tcons "bool" [])) ∧
      (∀ m, measureElab = some m → LExpr.HasTypeA [] m (.tcons "int" [])) ∧
      (∀ p ∈ invElab, LExpr.HasTypeA [] p.2 (.tcons "bool" [])) ∧
      TContext.Equiv (T := CoreLParams) Efold.context Env.context ∧
      LExpr.TEnvWF (T := CoreLParams) Efold ∧ Efold.context.AliasesResolved := by
  obtain ⟨heq, hwf, -⟩ := ((loopHead_chain hg hm hi).scope hf).facts he h_ne
  refine ⟨?_, ?_, ?_, heq, hwf, heq.symm.aliasesResolved hr⟩
  · intro g hgd
    cases guard with
    | det c =>
      obtain ⟨conda, hrs, hbool, rfl⟩ := hg
      cases hgd
      exact resolved_HasTypeA (ResolveChain.refl C Env) hrs hbool he hf hr h_ne
    | nondet =>
      obtain ⟨rfl, -⟩ := hg
      cases hgd
  · intro m hmd
    cases measure with
    | some m0 =>
      obtain ⟨ma, hrs, hint, rfl⟩ := hm
      cases hmd
      exact resolved_HasTypeA hg.chain hrs hint he hf hr h_ne
    | none =>
      obtain ⟨rfl, -⟩ := hm
      cases hmd
  · intro p hp
    obtain ⟨i, ia, hpia, E, E', hE, hrs, hbool, -⟩ := hi.chain_mem.2.2 p hp
    rw [hpia]
    exact resolved_HasTypeA (hg.chain.trans (hm.chain.trans hE)) hrs hbool he hf hr h_ne

/-- After the checker accepts a loop head, under any `S` absorbing the final substitution, the
    elaborated guard, measure and invariants with `S` applied agree with the substituted
    alias-free starting scope, when the table's signatures are fixed for its aliases. -/
private theorem loopHead_annotAgree {C : LContext CoreLParams} {Env Eg Em Efold : TEnv Unit}
    {guard guardElab : ExprOrNondet Expression} {measure measureElab : Option Expression.Expr}
    {invariant invElab : List (String × Expression.Expr)}
    (hg : CondChecked C Env guard guardElab Eg) (hm : MeasureChecked C Eg measure measureElab Em)
    (hi : InvariantsChecked C Em invariant invElab Efold)
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions)
    (hmono : MonoScope Env.context) (h_ne : Env.context.types ≠ [])
    (hsig : FactorySigsFixed Env.context.aliases C.functions)
    (S : Subst) (habs : Subst.absorbs S Efold.stateSubstInfo.subst) :
    (∀ g, guardElab = ExprOrNondet.det g → TypeSpec.ScopesAnnotAgree C
        (TContext.subst Env.context.dealias S).types (LExpr.applyTypeSubst g S)) ∧
      (∀ m, measureElab = some m → TypeSpec.ScopesAnnotAgree C
        (TContext.subst Env.context.dealias S).types (LExpr.applyTypeSubst m S)) ∧
      (∀ p ∈ invElab, TypeSpec.ScopesAnnotAgree C
        (TContext.subst Env.context.dealias S).types (LExpr.applyTypeSubst p.2 S)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hgd
    cases guard with
    | det c =>
      obtain ⟨conda, hrs, -, rfl⟩ := hg
      cases hgd
      exact resolved_annotAgree (ResolveChain.refl C Env) hrs
        (hm.chain.trans hi.chain_mem.1) he hf hmono h_ne hsig S habs
    | nondet =>
      obtain ⟨rfl, -⟩ := hg
      cases hgd
  · intro m hmd
    cases measure with
    | some m0 =>
      obtain ⟨ma, hrs, -, rfl⟩ := hm
      cases hmd
      exact resolved_annotAgree hg.chain hrs hi.chain_mem.1 he hf hmono h_ne hsig S habs
    | none =>
      obtain ⟨rfl, -⟩ := hm
      cases hmd
  · intro p hp
    obtain ⟨i, ia, hpia, E, E', hE, hrs, -, hfin⟩ := hi.chain_mem.2.2 p hp
    rw [hpia]
    exact resolved_annotAgree (hg.chain.trans (hm.chain.trans hE)) hrs hfin he hf hmono h_ne
      hsig S habs

/-- A source expression that resolved to ground type `ty` is typable as `ty`, with valid written
    annotations, at the input scope under any well-formed substitution absorbing a later
    environment's. -/
private theorem resolved_input_facts {C : LContext CoreLParams} {Env E E' Efin : TEnv Unit}
    {e : Expression.Expr} {ea : LExprT CoreLParams.mono} {ty : LMonoTy}
    (hchain : ResolveChain C Env E)
    (hrs : SourceExpr.resolve C E e = .ok (ea, E')) (hty : ea.toLMonoTy = ty)
    (hground : LMonoTy.freeVars ty = []) (hfin : ResolveChain C E' Efin)
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions)
    (hmono : MonoScope Env.context) (h_ne : Env.context.types ≠ []) :
    (∀ S : Subst, Subst.absorbs S Efin.stateSubstInfo.subst → SubstWF S →
      LExpr.HasType C (TContext.subst Env.context S) e (.forAll [] ty)) ∧
    ∀ S : Subst, WrittenAnnotsOk C (TContext.subst Env.context S) e := by
  obtain ⟨heq, hwf, -⟩ := (hchain.scope hf).facts he h_ne
  refine ⟨?_, ?_⟩
  · intro S habs hSwf
    have habsE' : Subst.absorbs S E'.stateSubstInfo.subst :=
      Subst.absorbs_trans _ _ _
        ((hfin.absorb hf) (SourceExpr.resolve_TEnvWF C E E' e ea hrs hwf hf)).2 habs
    exact HasType_FindEq C (TContext.subst E.context S) (TContext.subst Env.context S) e _
      (heq.subst S).symm.toFindEq
      (resolve_ground_HasType_source C E E' e ea ty hrs hty hground hwf hf
        (MonoScope_of_findEq heq.toFindEq hmono) S habsE' hSwf)
  · intro S
    exact writtenAnnotsOk_of_aliases_eq (heq.subst S).symm.toFindEq.aliases
      (resolveSource_writtenAnnotsOk C E E' e ea hrs S)

/-- A resolved source expression of ground type, with its annotations read through `S`, is
    typable as that type at the scope substituted by `S`, for a well-formed `S` absorbing a later
    environment's under which the resolved binder annotations are registered types. -/
private theorem resolved_input_read {C : LContext CoreLParams} {Env E E' Efin : TEnv Unit}
    {e : Expression.Expr} {ea : LExprT CoreLParams.mono} {ty : LMonoTy}
    (hchain : ResolveChain C Env E)
    (hrs : SourceExpr.resolve C E e = .ok (ea, E')) (hty : ea.toLMonoTy = ty)
    (hground : LMonoTy.freeVars ty = []) (hfin : ResolveChain C E' Efin)
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions)
    (hmono : MonoScope Env.context) (h_ne : Env.context.types ≠ [])
    (hAN : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (S : Subst) (habs : Subst.absorbs S Efin.stateSubstInfo.subst) (hSwf : SubstWF S)
    (hknown : BinderAnnotsKnown C (LExpr.applyTypeSubst ea.unresolved S)) :
    LExpr.HasType C (TContext.subst Env.context S) (instAnnots (substEnv S) e) (.forAll [] ty) := by
  obtain ⟨heq, hwf, -⟩ := (hchain.scope hf).facts he h_ne
  have habsE' : Subst.absorbs S E'.stateSubstInfo.subst :=
    Subst.absorbs_trans _ _ _
      ((hfin.absorb hf) (SourceExpr.resolve_TEnvWF C E E' e ea hrs hwf hf)).2 habs
  have hANE : ∀ al ∈ E.context.aliases, C.knownTypes.containsName al.name = false := by
    intro al hal
    rw [heq.2] at hal
    exact hAN al hal
  have ht := SourceExpr.resolve_HasType_instAnnots C E E' e ea hrs
    (SourceExpr.resolve_WellScoped C E E' e ea hrs) hwf hf
    (MonoScope_of_findEq heq.toFindEq hmono) hANE S habsE' hSwf hknown
  rw [hty, LMonoTy.subst_ground S ty hground] at ht
  exact HasType_FindEq C (TContext.subst E.context S) (TContext.subst Env.context S) _ _
    (heq.subst S).symm.toFindEq ht

/-- After the checker accepts a loop head, the source guard and invariants are typable as `bool`
    and the measure as `int` at the substituted starting scope, with valid written annotations. -/
private theorem loopHead_input {C : LContext CoreLParams} {Env Eg Em Efold : TEnv Unit}
    {guard guardElab : ExprOrNondet Expression} {measure measureElab : Option Expression.Expr}
    {invariant invElab : List (String × Expression.Expr)}
    (hg : CondChecked C Env guard guardElab Eg) (hm : MeasureChecked C Eg measure measureElab Em)
    (hi : InvariantsChecked C Em invariant invElab Efold)
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions)
    (hmono : MonoScope Env.context) (h_ne : Env.context.types ≠ []) :
    (∀ (S : Subst), Subst.absorbs S Efold.stateSubstInfo.subst → SubstWF S →
      ∀ (g : Expression.Expr), guard = ExprOrNondet.det g →
        LExpr.HasType C (TContext.subst Env.context S) g (.forAll [] LMonoTy.bool)) ∧
    (∀ (S : Subst), Subst.absorbs S Efold.stateSubstInfo.subst → SubstWF S →
      ∀ (m : Expression.Expr), measure = some m →
        LExpr.HasType C (TContext.subst Env.context S) m (.forAll [] LMonoTy.int)) ∧
    (∀ (S : Subst), Subst.absorbs S Efold.stateSubstInfo.subst → SubstWF S →
      ∀ p ∈ invariant,
        LExpr.HasType C (TContext.subst Env.context S) p.2 (.forAll [] LMonoTy.bool)) ∧
    (∀ (S : Subst) (g : Expression.Expr), guard = ExprOrNondet.det g →
      WrittenAnnotsOk C (TContext.subst Env.context S) g) ∧
    (∀ (S : Subst) (m : Expression.Expr), measure = some m →
      WrittenAnnotsOk C (TContext.subst Env.context S) m) ∧
    (∀ (S : Subst), ∀ p ∈ invariant,
      WrittenAnnotsOk C (TContext.subst Env.context S) p.2) ∧
    TContext.Equiv (T := CoreLParams) Efold.context Env.context ∧
    LExpr.TEnvWF (T := CoreLParams) Efold ∧ MonoScope Efold.context ∧
    Subst.absorbs Efold.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  have hEgEfold : ResolveChain C Eg Efold := hm.chain.trans hi.chain_mem.1
  have hguard : ∀ g, guard = ExprOrNondet.det g →
      (∀ S : Subst, Subst.absorbs S Efold.stateSubstInfo.subst → SubstWF S →
        LExpr.HasType C (TContext.subst Env.context S) g (.forAll [] LMonoTy.bool)) ∧
      ∀ S : Subst,
        WrittenAnnotsOk C (TContext.subst Env.context S) g := by
    intro g hgd
    subst hgd
    obtain ⟨conda, hrs, hbool, -⟩ := hg
    exact resolved_input_facts (ResolveChain.refl C Env) hrs hbool rfl hEgEfold he hf hmono
      h_ne
  have hmeasure : ∀ m, measure = some m →
      (∀ S : Subst, Subst.absorbs S Efold.stateSubstInfo.subst → SubstWF S →
        LExpr.HasType C (TContext.subst Env.context S) m (.forAll [] LMonoTy.int)) ∧
      ∀ S : Subst,
        WrittenAnnotsOk C (TContext.subst Env.context S) m := by
    intro m hmd
    subst hmd
    obtain ⟨ma, hrs, hint, -⟩ := hm
    exact resolved_input_facts hg.chain hrs hint rfl hi.chain_mem.1 he hf hmono h_ne
  have hinv : ∀ p ∈ invariant,
      (∀ S : Subst, Subst.absorbs S Efold.stateSubstInfo.subst → SubstWF S →
        LExpr.HasType C (TContext.subst Env.context S) p.2 (.forAll [] LMonoTy.bool)) ∧
      ∀ S : Subst,
        WrittenAnnotsOk C (TContext.subst Env.context S) p.2 := by
    intro p hp
    obtain ⟨ia, ⟨E, E', hE, hrs, hbool, hE'⟩, -⟩ := hi.chain_mem.2.1 p hp
    exact resolved_input_facts (hg.chain.trans (hm.chain.trans hE)) hrs hbool rfl hE' he hf
      hmono h_ne
  obtain ⟨heq, hwf, -⟩ := ((loopHead_chain hg hm hi).scope hf).facts he h_ne
  exact ⟨fun S habs hSwf g hgd => (hguard g hgd).1 S habs hSwf,
    fun S habs hSwf m hmd => (hmeasure m hmd).1 S habs hSwf,
    fun S habs hSwf p hp => (hinv p hp).1 S habs hSwf,
    fun S g hgd => (hguard g hgd).2 S, fun S m hmd => (hmeasure m hmd).2 S,
    fun S p hp => (hinv p hp).2 S, heq, hwf, MonoScope_of_findEq heq.toFindEq hmono,
    ((loopHead_chain hg hm hi).absorb hf he).2⟩

/-! ## Per-command evidence -/

mutual

/-- Evidence beside a statement typing, one node per typing rule, with `ReadAvoids` for the
    written environment wherever an expression is read. -/
public inductive StatementSideConditionsΔ (ambientRigids : RigidNames)
    {P : Program} :
    ∀ {C Cfin : LContext CoreLParams} {Γ Γfin : TContext Unit} {Δ Δfin : WrittenEnv}
      {L : List String} {s : Statement},
      StatementHasType P C Γ Δ L s Cfin Γfin Δfin → Prop where
  | cmd {C Γ Γc Δ Δ' L c Γ'}
      (hce : CmdExtHasType C P Δ Γ c Γc Δ')
      (hEqv : TContext.Equiv (T := CoreLParams) Γ' Γc) :
      ReadAvoids ambientRigids Δ' →
      StatementSideConditionsΔ ambientRigids
        (StatementHasType.cmd C Γ Γc Δ Δ' L c Γ' hce hEqv)
  | block {C Γ Δ Cb Γb Δb L label body md Γ'}
      (hnot : label ∉ L)
      (hb : StatementsHasType P C Γ Δ (label :: L) body Cb Γb Δb)
      (hEqv : TContext.Equiv (T := CoreLParams) Γ' Γ)
      (hs : StatementsSideConditionsΔ ambientRigids hb) :
      StatementSideConditionsΔ ambientRigids
        (StatementHasType.block C Γ Δ Cb Γb Δb L label body md Γ' hnot hb hEqv)
  | ite_det {C Γ Δ Ct Γt Δt Ce Γe Δe L cond thenb elseb md Γ'}
      (hcond : LExpr.HasType C Γ (instAnnots Δ cond) (.forAll [] .bool))
      (hcondAnn : WrittenAnnotsOk C Γ cond)
      (hcondScope : AnnotsInScope C.rigidTypeVars Δ cond)
      (hread : ReadAvoids ambientRigids Δ)
      (ht : StatementsHasType P C Γ Δ L thenb Ct Γt Δt)
      (he : StatementsHasType P C Γ Δ L elseb Ce Γe Δe)
      (hEqv : TContext.Equiv (T := CoreLParams) Γ' Γ)
      (hst : StatementsSideConditionsΔ ambientRigids ht)
      (hse : StatementsSideConditionsΔ ambientRigids he) :
      StatementSideConditionsΔ ambientRigids
        (StatementHasType.ite_det C Γ Δ Ct Γt Δt Ce Γe Δe L cond thenb elseb md Γ'
          hcond hcondAnn hcondScope ht he hEqv)
  | ite_nondet {C Γ Δ Ct Γt Δt Ce Γe Δe L thenb elseb md Γ'}
      (ht : StatementsHasType P C Γ Δ L thenb Ct Γt Δt)
      (he : StatementsHasType P C Γ Δ L elseb Ce Γe Δe)
      (hEqv : TContext.Equiv (T := CoreLParams) Γ' Γ)
      (hst : StatementsSideConditionsΔ ambientRigids ht)
      (hse : StatementsSideConditionsΔ ambientRigids he) :
      StatementSideConditionsΔ ambientRigids
        (StatementHasType.ite_nondet C Γ Δ Ct Γt Δt Ce Γe Δe L thenb elseb md Γ'
          ht he hEqv)
  | loop {C Γ Δ Cb Γb Δb L guard measure invariants body md Γ'}
      (hg : ∀ g, guard = .det g → LExpr.HasType C Γ (instAnnots Δ g) (.forAll [] .bool))
      (hgAnn : ∀ g, guard = .det g → WrittenAnnotsOk C Γ g)
      (hm : ∀ m, measure = some m → LExpr.HasType C Γ (instAnnots Δ m) (.forAll [] .int))
      (hmAnn : ∀ m, measure = some m → WrittenAnnotsOk C Γ m)
      (hi : ∀ p, p ∈ invariants → LExpr.HasType C Γ (instAnnots Δ p.2) (.forAll [] .bool))
      (hiAnn : ∀ p, p ∈ invariants → WrittenAnnotsOk C Γ p.2)
      (hgS : ∀ g, guard = .det g → AnnotsInScope C.rigidTypeVars Δ g)
      (hmS : ∀ m, measure = some m → AnnotsInScope C.rigidTypeVars Δ m)
      (hiS : ∀ p, p ∈ invariants → AnnotsInScope C.rigidTypeVars Δ p.2)
      (hb : StatementsHasType P C Γ Δ L body Cb Γb Δb)
      (hEqv : TContext.Equiv (T := CoreLParams) Γ' Γ)
      (hread : ReadAvoids ambientRigids Δ)
      (hs : StatementsSideConditionsΔ ambientRigids hb) :
      StatementSideConditionsΔ ambientRigids
        (StatementHasType.loop C Γ Δ Cb Γb Δb L guard measure invariants body md Γ'
          hg hgAnn hm hmAnn hi hiAnn hgS hmS hiS hb hEqv)
  | exit {C Γ Δ L label md Γ'}
      (hmem : label ∈ L)
      (hEqv : TContext.Equiv (T := CoreLParams) Γ' Γ) :
      StatementSideConditionsΔ ambientRigids
        (StatementHasType.exit C Γ Δ L label md Γ' hmem hEqv)
  | typeDecl {C C' Γ Δ L tc md Γ'}
      (hprog : ∀ n ∈ P.getNames, n.name ≠ tc.name)
      (hnotAlias : ∀ al ∈ Γ.aliases, al.name ≠ tc.name)
      (hadd : C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } default = .ok C')
      (hEqv : TContext.Equiv (T := CoreLParams) Γ' Γ) :
      StatementSideConditionsΔ ambientRigids
        (StatementHasType.typeDecl C C' Γ Δ L tc md Γ' hprog hnotAlias hadd hEqv)

/-- List form of `StatementSideConditionsΔ`: the same evidence for every statement of a list. -/
public inductive StatementsSideConditionsΔ (ambientRigids : RigidNames)
    {P : Program} :
    ∀ {C Cfin : LContext CoreLParams} {Γ Γfin : TContext Unit} {Δ Δfin : WrittenEnv}
      {L : List String} {ss : List Statement},
      StatementsHasType P C Γ Δ L ss Cfin Γfin Δfin → Prop where
  | nil {C Γ Δ L Γ'} (hEqv : TContext.Equiv (T := CoreLParams) Γ' Γ) :
      StatementsSideConditionsΔ ambientRigids (StatementsHasType.nil C Γ Δ L Γ' hEqv)
  | cons {C C' C'' Γ Γ' Γ'' Δ Δ' Δ'' L s ss}
      (hs : StatementHasType P C Γ Δ L s C' Γ' Δ')
      (ht : StatementsHasType P C' Γ' Δ' L ss C'' Γ'' Δ'')
      (hss : StatementSideConditionsΔ ambientRigids hs)
      (hst : StatementsSideConditionsΔ ambientRigids ht) :
      StatementsSideConditionsΔ ambientRigids
        (StatementsHasType.cons C C' C'' Γ Γ' Γ'' Δ Δ' Δ'' L s ss hs ht)

end

/-! ### Moving a typing and its evidence to an input scope with the same lookups -/

/-- A typing of a statement list by the typechecker spec, with its side-condition evidence, holds
    again from any input scope with the same variable lookups, ending in a scope with the same
    lookups as the original output scope. -/
public theorem StatementsSideConditionsΔ.input_ctx_FindEq
    {ambientRigids : RigidNames}
    {P : Program}
    {C Cfin : LContext CoreLParams} {Γ Γin Γfin : TContext Unit} {Δ Δfin : WrittenEnv}
    {L : List String} {ss : List Statement}
    {h : StatementsHasType P C Γ Δ L ss Cfin Γfin Δfin}
    (hstrict : StatementsSideConditionsΔ ambientRigids h)
    (hEq : TContext.FindEq (T := CoreLParams) Γin Γ) :
    ∃ Γfin', ∃ h' : StatementsHasType P C Γin Δ L ss Cfin Γfin' Δfin,
      StatementsSideConditionsΔ ambientRigids h' ∧
        TContext.FindEq (T := CoreLParams) Γfin' Γfin := by
  refine StatementsSideConditionsΔ.rec
    (motive_1 := fun {C Cfin Γ Γfin Δ Δfin L s} _ _ =>
      ∀ Γin, TContext.FindEq (T := CoreLParams) Γin Γ →
        ∃ Γfin', ∃ h' : StatementHasType P C Γin Δ L s Cfin Γfin' Δfin,
          StatementSideConditionsΔ ambientRigids h' ∧
            TContext.FindEq (T := CoreLParams) Γfin' Γfin)
    (motive_2 := fun {C Cfin Γ Γfin Δ Δfin L ss} _ _ =>
      ∀ Γin, TContext.FindEq (T := CoreLParams) Γin Γ →
        ∃ Γfin', ∃ h' : StatementsHasType P C Γin Δ L ss Cfin Γfin' Δfin,
          StatementsSideConditionsΔ ambientRigids h' ∧
            TContext.FindEq (T := CoreLParams) Γfin' Γfin)
    ?cmd ?block ?ite_det ?ite_nondet ?loop ?exit ?typeDecl ?nil ?cons
    hstrict Γin hEq
  case cmd =>
    intro C Γ Γc Δ Δ' L c Γ' hce hEqv hread Γin hEq
    obtain ⟨Γce', hce', hfe⟩ := CmdExtHasType_transport hEq hce
    let h' := @StatementHasType.cmd P
      C Γin Γce' Δ Δ' L c Γce' hce' (TContext.Equiv.refl _)
    exact ⟨Γce', h', .cmd hce' (TContext.Equiv.refl _) hread,
      hfe.trans hEqv.toFindEq.symm⟩
  case block =>
    intro C Γ Δ Cb Γb Δb L label body md Γ' hnot hb hEqv hs ih Γin hEq
    obtain ⟨Γb', hb', hs', -⟩ := ih Γin hEq
    let h' := StatementHasType.block C Γin Δ Cb Γb' Δb L label body md Γin
      hnot hb' (TContext.Equiv.refl _)
    exact ⟨Γin, h', .block hnot hb' (TContext.Equiv.refl _) hs',
      hEq.trans hEqv.toFindEq.symm⟩
  case ite_det =>
    intro C Γ Δ Ct Γt Δt Ce Γe Δe L cond thenb elseb md Γ' hcond hcondAnn hcondScope hread ht he
      hEqv hst hse iht ihe Γin hEq
    obtain ⟨Γt', ht', hst', -⟩ := iht Γin hEq
    obtain ⟨Γe', he', hse', -⟩ := ihe Γin hEq
    have hcond' := HasType_FindEq C _ _ _ _ hEq hcond
    have hcondAnn' := writtenAnnotsOk_of_aliases_eq hEq.aliases hcondAnn
    let h' := StatementHasType.ite_det C Γin Δ Ct Γt' Δt Ce Γe' Δe L cond thenb elseb md
      Γin hcond' hcondAnn' hcondScope ht' he' (TContext.Equiv.refl _)
    exact ⟨Γin, h', .ite_det hcond' hcondAnn' hcondScope hread ht' he' (TContext.Equiv.refl _) hst'
      hse',
      hEq.trans hEqv.toFindEq.symm⟩
  case ite_nondet =>
    intro C Γ Δ Ct Γt Δt Ce Γe Δe L thenb elseb md Γ' ht he hEqv hst hse iht ihe Γin hEq
    obtain ⟨Γt', ht', hst', -⟩ := iht Γin hEq
    obtain ⟨Γe', he', hse', -⟩ := ihe Γin hEq
    let h' := StatementHasType.ite_nondet C Γin Δ Ct Γt' Δt Ce Γe' Δe L thenb elseb md
      Γin ht' he' (TContext.Equiv.refl _)
    exact ⟨Γin, h', .ite_nondet ht' he' (TContext.Equiv.refl _) hst' hse',
      hEq.trans hEqv.toFindEq.symm⟩
  case loop =>
    intro C Γ Δ Cb Γb Δb L guard measure invariants body md Γ' hg hgAnn hm hmAnn hi hiAnn
      hgS hmS hiS hb hEqv hread hs ih Γin hEq
    obtain ⟨Γb', hb', hs', -⟩ := ih Γin hEq
    have hg' := fun g hgd =>
      HasType_FindEq C _ _ _ _ hEq (hg g hgd)
    have hgAnn' := fun g hgd =>
      writtenAnnotsOk_of_aliases_eq hEq.aliases (hgAnn g hgd)
    have hm' := fun m hms =>
      HasType_FindEq C _ _ _ _ hEq (hm m hms)
    have hmAnn' := fun m hms =>
      writtenAnnotsOk_of_aliases_eq hEq.aliases (hmAnn m hms)
    have hi' := fun p hp =>
      HasType_FindEq C _ _ _ _ hEq (hi p hp)
    have hiAnn' := fun p hp =>
      writtenAnnotsOk_of_aliases_eq hEq.aliases (hiAnn p hp)
    let h' := StatementHasType.loop C Γin Δ Cb Γb' Δb L guard measure invariants
      body md Γin hg' hgAnn' hm' hmAnn' hi' hiAnn' hgS hmS hiS hb' (TContext.Equiv.refl _)
    exact ⟨Γin, h', .loop hg' hgAnn' hm' hmAnn' hi' hiAnn' hgS hmS hiS hb'
      (TContext.Equiv.refl _) hread hs', hEq.trans hEqv.toFindEq.symm⟩
  case exit =>
    intro C Γ Δ L label md Γ' hmem hEqv Γin hEq
    let h' := @StatementHasType.exit P
      C Γin Δ L label md Γin hmem (TContext.Equiv.refl _)
    exact ⟨Γin, h', .exit hmem (TContext.Equiv.refl _), hEq.trans hEqv.toFindEq.symm⟩
  case typeDecl =>
    intro C C' Γ Δ L tc md Γ' hprog hnotAlias hadd hEqv Γin hEq
    have hnotAlias' := nameNotAlias_of_aliases_eq hEq.aliases hnotAlias
    let h' := @StatementHasType.typeDecl P
      C C' Γin Δ L tc md Γin hprog hnotAlias' hadd (TContext.Equiv.refl _)
    exact ⟨Γin, h', .typeDecl hprog hnotAlias' hadd (TContext.Equiv.refl _),
      hEq.trans hEqv.toFindEq.symm⟩
  case nil =>
    intro C Γ Δ L Γ' hEqv Γin hEq
    let h' := @StatementsHasType.nil P
      C Γin Δ L Γin (TContext.Equiv.refl _)
    exact ⟨Γin, h', .nil (TContext.Equiv.refl _), hEq.trans hEqv.toFindEq.symm⟩
  case cons =>
    intro C C' C'' Γ Γ' Γ'' Δ Δ' Δ'' L s ss hs ht hss hst ihs iht Γin hEq
    obtain ⟨Γm', hs', hss', hEqm⟩ := ihs Γin hEq
    obtain ⟨Γfin', ht', hst', hEqfin⟩ := iht Γm' hEqm
    let h' := StatementsHasType.cons C C' C'' Γin Γm' Γfin' Δ Δ' Δ'' L s ss hs' ht'
    exact ⟨Γfin', h', .cons hs' ht' hss' hst', hEqfin⟩

/-! ## The positional annotation sweep
The check `tysDeclaredStmts` as an inductive judgment, one statement at a time. -/

/-- The statements `ss`, after applying `S`, pass the annotation check `Statement.tysDeclaredStmts`
    from the registered types `ks`, one statement at a time. -/
public inductive SweepFrom (S : Subst) : Lambda.KnownTypes → List Statement → Prop where
  | nil (ks : Lambda.KnownTypes) : SweepFrom S ks []
  | cons {ks ks' : Lambda.KnownTypes} {s : Statement} {ss : List Statement}
      (head : Statement.tysDeclaredStmt ks (Statement.Statement.subst S s) = some ks')
      (tail : SweepFrom S ks' ss) :
      SweepFrom S ks (s :: ss)

/-- The statements `ss`, after applying `S`, pass the annotation check `Statement.tysDeclaredStmts`
    starting from the registered types of the context `C`. -/
public def SweepAt (C : LContext CoreLParams) (S : Subst) (ss : List Statement) : Prop :=
  SweepFrom S C.knownTypes ss

/-- The inductive sweep is exactly the success condition computed by `tysDeclaredStmts`. -/
private theorem sweepFrom_iff_tysDeclaredStmts (S : Subst) (ks : Lambda.KnownTypes)
    (ss : List Statement) :
    SweepFrom S ks ss ↔
      (Statement.tysDeclaredStmts ks
        (ss.map (Statement.Statement.subst S))).isSome = true := by
  induction ss generalizing ks with
  | nil =>
    constructor
    · intro _
      rw [List.map_nil, Statement.tysDeclaredStmts_nil]
      rfl
    · intro _
      exact .nil ks
  | cons s rest ih =>
    constructor
    · intro h
      cases h with
      | cons hhead htail =>
        simp only [List.map_cons, Statement.tysDeclaredStmts_cons, bind, Option.bind, hhead]
        exact (ih _).mp htail
    · intro h
      simp only [List.map_cons, Statement.tysDeclaredStmts_cons, bind, Option.bind] at h
      elim_err h with ks' hhead
      exact .cons hhead ((ih ks').mpr h)

/-- The positional sweep at a context holds exactly when `tysDeclaredStmts`, run from that
    context's registered-type table over the substituted statements, succeeds. -/
private theorem sweepAt_iff_tysDeclaredStmts (C : LContext CoreLParams) (S : Subst)
    (ss : List Statement) :
    SweepAt C S ss ↔
      (Statement.tysDeclaredStmts C.knownTypes
        (ss.map (Statement.Statement.subst S))).isSome = true :=
  sweepFrom_iff_tysDeclaredStmts S C.knownTypes ss

/-- A positional sweep exposes the substituted annotation validity of its head statement. -/
private theorem SweepAt.head_ownTysDeclared (C : LContext CoreLParams) (S : Subst)
    (s : Statement) (rest : List Statement) (h : SweepAt C S (s :: rest)) :
    Statement.ownTysDeclared C.knownTypes (Statement.Statement.subst S s) = true := by
  cases h with
  | cons hhead htail =>
    rw [Statement.tysDeclaredStmt_eq] at hhead
    cases hown : Statement.ownTysDeclared C.knownTypes
        (Statement.Statement.subst S s) with
    | true => rfl
    | false =>
      rw [hown] at hhead
      exact absurd hhead (by simp)

/-! ## Invariants of the walk for additive statement measures -/

/-- A list-valued measure on statements that adds up over a list: its value on a list is the
    concatenation of its values on the elements. -/
private structure StmtMeasure (β : Type) where
  stmt : Statement → List β
  stmts : List Statement → List β
  stmts_nil : stmts [] = []
  stmts_cons : ∀ s ss, stmts (s :: ss) = stmt s ++ stmts ss

/-- An additive measure distributes over list append. -/
private theorem StmtMeasure.stmts_append {β : Type} (M : StmtMeasure β) (a b : List Statement) :
    M.stmts (a ++ b) = M.stmts a ++ M.stmts b := by
  induction a with
  | nil => rw [List.nil_append, M.stmts_nil, List.nil_append]
  | cons s rest ih => rw [List.cons_append, M.stmts_cons, ih, M.stmts_cons, List.append_assoc]

/-- The walk invariant for a measure: the output has the measure of the reversed accumulator
    followed by that of the input. -/
private def GoPreserves {β : Type} (M : StmtMeasure β) (out acc inp : List Statement) : Prop :=
  M.stmts out = M.stmts acc.reverse ++ M.stmts inp

/-- The invariant holds when the walk has consumed its whole input. -/
private theorem GoPreserves.nil {β : Type} (M : StmtMeasure β) (acc : List Statement) :
    GoPreserves M acc.reverse acc [] := by
  simp only [GoPreserves, M.stmts_nil, List.append_nil]

/-- With an empty accumulator, the invariant gives equal measures of output and input. -/
private theorem GoPreserves.of_nil_acc {β : Type} {M : StmtMeasure β} {out inp : List Statement}
    (h : GoPreserves M out [] inp) : M.stmts out = M.stmts inp := by
  simpa only [GoPreserves, List.reverse_nil, M.stmts_nil, List.nil_append] using h

/-- Emitting a statement with the same measure as its source extends the invariant. -/
private theorem GoPreserves.cons {β : Type} {M : StmtMeasure β} {acc srest out : List Statement}
    {s s' : Statement} (hn : M.stmt s' = M.stmt s) (hih : GoPreserves M out (s' :: acc) srest) :
    GoPreserves M out acc (s :: srest) := by
  unfold GoPreserves at hih ⊢
  rw [hih, List.reverse_cons, M.stmts_append, M.stmts_cons s' [], M.stmts_cons s srest,
    M.stmts_nil, hn]
  simp only [List.append_nil, List.append_assoc]

/-- The variables a statement list modifies. -/
private def modifiedVarsMeasure : StmtMeasure Expression.Ident :=
  ⟨fun s => Stmt.modifiedVars s, fun ss => Block.modifiedVars ss, rfl, fun _ _ => rfl⟩

/-- The variables a statement list defines, with scoped definitions excluded when `b` holds. -/
private def definedVarsMeasure (b : Bool) : StmtMeasure Expression.Ident :=
  ⟨fun s => Stmt.definedVars s b, fun ss => Block.definedVars ss b, rfl, fun _ _ => rfl⟩

/-- The procedure names a statement list calls. -/
private def calledNamesMeasure : StmtMeasure String :=
  ⟨Statement.calledProcedureNames, Statements.calledProcedureNames,
    Statements.calledProcedureNames_nil, Statements.calledProcedureNames_cons⟩

/-- The type constructor names in the literals of a statement list. -/
private def litNamesMeasure : StmtMeasure String :=
  ⟨stmtLitTyNames, stmtsLitTyNames, stmtsLitTyNames_nil, stmtsLitTyNames_cons⟩

/-! ## Variable-set preservation through statement elaboration -/

/-- The walk invariant for the modified and defined variables, with the fact that the output
    extends the reversed accumulator. -/
private def GoVars (out acc inp : List Statement) : Prop :=
  GoPreserves modifiedVarsMeasure out acc inp ∧
  (∀ b, GoPreserves (definedVarsMeasure b) out acc inp) ∧
  ∃ emitted, out = acc.reverse ++ emitted

/-- With an empty accumulator, `GoVars` gives exact modified- and defined-variable equality. -/
private theorem GoVars.of_nil_acc {out inp : List Statement} (h : GoVars out [] inp) :
    Block.modifiedVars out = Block.modifiedVars inp ∧
    ∀ b, Block.definedVars out b = Block.definedVars inp b :=
  ⟨GoPreserves.of_nil_acc h.1, fun b => GoPreserves.of_nil_acc (h.2.1 b)⟩

/-- Equal variable sets for one emitted statement extend the `GoVars` walk invariant. -/
private theorem GoVars.cons {acc srest out : List Statement} {s s' : Statement}
    (hm : Stmt.modifiedVars s' = Stmt.modifiedVars s)
    (hd : ∀ b, Stmt.definedVars s' b = Stmt.definedVars s b)
    (hih : GoVars out (s' :: acc) srest) :
    GoVars out acc (s :: srest) := by
  obtain ⟨h1, h2, emitted, h3⟩ := hih
  refine ⟨GoPreserves.cons hm h1, fun b => GoPreserves.cons (hd b) (h2 b), s' :: emitted, ?_⟩
  rw [h3, List.reverse_cons, List.append_assoc]
  rfl

/-- A successful walk keeps the modified and defined variables of its input, after the reversed
    accumulator. -/
private theorem go_vars_eq
    (C C' : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program)
    (op : Option Procedure) (ss acc ss' : List Statement) (labels : List String)
    {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.go P op C Env ss acc labels m st
      = .ok (ss', Env', C', st')) :
    GoVars ss' acc ss := by
  refine go_ok_induct (motive := fun _ _ ss acc _ _ _ ss' _ _ _ => GoVars ss' acc ss)
    (motiveB := fun _ _ ss acc _ _ _ ss' _ _ _ => GoVars ss' acc ss)
    ?nil ?cmd ?block ?ite ?loop ?exit ?typeDecl ?blockScope ?blockFlat C Env ss acc labels ss'
    Env' C' h
  case nil =>
    intro _ _ _ _ _ _
    exact ⟨GoPreserves.nil _ _, fun _ => GoPreserves.nil _ _, [], (List.append_nil _).symm⟩
  case cmd =>
    intro C Env _ _ _ _ _ cmd c' Env1 _ _ _ _ htc _ _ ih
    obtain ⟨hm, hd⟩ := Statement.typeCheckCmd_vars_eq C Env Env1 P _ c' htc
    have hmod : Stmt.modifiedVars (Stmt.cmd c' : Statement) = Stmt.modifiedVars (Stmt.cmd cmd) := by
      simp only [Stmt.modifiedVars]
      exact hm.trans (Command.modifiedVars_renameCmd _ _ _ cmd)
    have hdef : ∀ b, Stmt.definedVars (Stmt.cmd c' : Statement) b =
        Stmt.definedVars (Stmt.cmd cmd) b := by
      intro b
      simp only [Stmt.definedVars]
      exact hd.trans (Command.definedVars_renameCmd _ _ _ cmd)
    exact GoVars.cons hmod hdef ih
  case block =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihb _ ih
    obtain ⟨hm, hd⟩ := GoVars.of_nil_acc ihb
    refine GoVars.cons ?_ ?_ ih
    · simp only [Stmt.modifiedVars]; exact hm
    · intro b; simp only [Stmt.definedVars]; split
      · rfl
      · exact hd b
  case ite =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ iht _ ihe _ ih
    obtain ⟨mt, dt⟩ := GoVars.of_nil_acc iht
    obtain ⟨me, de⟩ := GoVars.of_nil_acc ihe
    refine GoVars.cons ?_ ?_ ih
    · simp only [Stmt.modifiedVars, mt, me]
    · intro b; simp only [Stmt.definedVars]; split
      · rfl
      · rw [dt b, de b]
  case loop =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihb _ ih
    obtain ⟨mb, db⟩ := GoVars.of_nil_acc ihb
    refine GoVars.cons ?_ ?_ ih
    · simp only [Stmt.modifiedVars]; exact mb
    · intro b; simp only [Stmt.definedVars]; split
      · rfl
      · exact db b
  case exit => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => GoVars.cons rfl (fun _ => rfl) ih
  case typeDecl => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => GoVars.cons rfl (fun _ => rfl) ih
  case blockFlat => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => ih
  case blockScope => exact fun _ _ _ _ _ _ _ _ _ _ _ _ ih => ih

/-! ## The called procedure names survive statement elaboration -/

/-- A successful walk keeps the called procedure names of its input, after the reversed
    accumulator. -/
private theorem go_calledProcedureNames_eq
    (C C' : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program)
    (op : Option Procedure) (ss acc ss' : List Statement) (labels : List String)
    {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.go P op C Env ss acc labels m st
      = .ok (ss', Env', C', st')) :
    GoPreserves calledNamesMeasure ss' acc ss := by
  refine go_ok_induct (motive := fun _ _ ss acc _ _ _ ss' _ _ _ => GoPreserves calledNamesMeasure
      ss' acc ss)
    (motiveB := fun _ _ ss acc _ _ _ ss' _ _ _ => GoPreserves calledNamesMeasure ss' acc ss)
    ?nil ?cmd ?block ?ite ?loop ?exit ?typeDecl ?blockScope ?blockFlat C Env ss acc labels ss'
    Env' C' h
  case nil =>
    intro _ _ _ _ _ _
    exact GoPreserves.nil _ _
  case cmd =>
    intro C Env _ _ _ _ _ cmd c' Env1 _ _ _ _ htc _ _ ih
    have hn := (Statement.typeCheckCmd_calledProcedureNames_eq C Env Env1 P _ c' htc).trans
      (calledProcedureNames_renameCmd _ _ _ cmd)
    refine GoPreserves.cons ?_ ih
    show Statement.calledProcedureNames _ = Statement.calledProcedureNames _
    simp only [Statement.calledProcedureNames_cmd]
    exact hn
  case block =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihb _ ih
    refine GoPreserves.cons ?_ ih
    show Statement.calledProcedureNames _ = Statement.calledProcedureNames _
    simp only [Statement.calledProcedureNames_block]
    exact GoPreserves.of_nil_acc ihb
  case ite =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ iht _ ihe _ ih
    refine GoPreserves.cons ?_ ih
    have ht : Statements.calledProcedureNames _ = Statements.calledProcedureNames _ :=
      GoPreserves.of_nil_acc iht
    have he : Statements.calledProcedureNames _ = Statements.calledProcedureNames _ :=
      GoPreserves.of_nil_acc ihe
    show Statement.calledProcedureNames _ = Statement.calledProcedureNames _
    simp only [Statement.calledProcedureNames_ite, ht, he]
  case loop =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihb _ ih
    refine GoPreserves.cons ?_ ih
    show Statement.calledProcedureNames _ = Statement.calledProcedureNames _
    simp only [Statement.calledProcedureNames_loop]
    exact GoPreserves.of_nil_acc ihb
  case exit => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => GoPreserves.cons rfl ih
  case typeDecl => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => GoPreserves.cons rfl ih
  case blockFlat => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => ih
  case blockScope => exact fun _ _ _ _ _ _ _ _ _ _ _ _ ih => ih

/-! ## Literal type names survive statement elaboration -/

/-- A checked guard keeps the literal type names of its source. -/
private theorem condChecked_litTyNames {C : LContext CoreLParams} {Env Ec : TEnv Unit}
    {m : ScopeMap} {cond condElab : ExprOrNondet Expression}
    (h : CondChecked C Env (renameExprOrNondet m cond) condElab Ec) :
    condElab.toList.flatMap exprLitTyNames = cond.toList.flatMap exprLitTyNames := by
  cases cond with
  | nondet =>
    simp only [renameExprOrNondet, ExprOrNondet.map, CondChecked] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  | det c =>
    simp only [renameExprOrNondet, ExprOrNondet.map, CondChecked] at h
    obtain ⟨conda, hres, -, rfl⟩ := h
    have hc := SourceExpr.resolve_getConsts_eq _ _ _ _ _ hres
    simp only [ExprOrNondet.toList, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      exprLitTyNames]
    rw [Lambda.LExpr.Proofs.getConsts_unresolved, hc, getConsts_renameExpr]

/-- A checked measure keeps the literal type names of its source. -/
private theorem measureChecked_litTyNames {C : LContext CoreLParams} {Env Em : TEnv Unit}
    {m : ScopeMap} {measure measureElab : Option Expression.Expr}
    (h : MeasureChecked C Env (measure.map (renameExpr m)) measureElab Em) :
    measureElab.toList.flatMap exprLitTyNames = measure.toList.flatMap exprLitTyNames := by
  cases measure with
  | none =>
    simp only [Option.map, MeasureChecked] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  | some mm =>
    simp only [Option.map, MeasureChecked] at h
    obtain ⟨ma, hres, -, rfl⟩ := h
    have hc := SourceExpr.resolve_getConsts_eq _ _ _ _ _ hres
    simp only [Option.toList, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      exprLitTyNames]
    rw [Lambda.LExpr.Proofs.getConsts_unresolved, hc, getConsts_renameExpr]

/-- Checked invariants keep the literal type names of their sources. -/
private theorem invariantsChecked_litTyNames {C : LContext CoreLParams} {Env Efold : TEnv Unit}
    {m : ScopeMap} {invariant invElab : List (String × Expression.Expr)}
    (h : InvariantsChecked C Env (invariant.map (fun (l, i) => (l, renameExpr m i))) invElab
      Efold) :
    (invElab.map (·.2)).flatMap exprLitTyNames = (invariant.map (·.2)).flatMap exprLitTyNames := by
  obtain ⟨step, it, hstep, hfold, rfl⟩ := h
  have hgen : ∀ (inv : List (String × Expression.Expr))
      (acc : List (String × LExprT CoreLParams.mono)) (E : TEnv Unit)
      (it' : List (String × LExprT CoreLParams.mono)) (Ef : TEnv Unit),
      inv.foldlM step (acc, E) = .ok (it', Ef) →
      ((it'.map (fun x => (x.1, x.2.unresolved))).map (·.2)).flatMap exprLitTyNames =
        ((acc.map (fun x => (x.1, x.2.unresolved))).map (·.2)).flatMap exprLitTyNames ++
          (inv.map (·.2)).flatMap exprLitTyNames := by
    intro inv
    induction inv with
    | nil =>
      intro acc E it' Ef h'
      simp only [List.foldlM, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h'
      obtain ⟨rfl, -⟩ := h'
      simp only [List.map_nil, List.flatMap_nil, List.append_nil]
    | cons q rest ih =>
      intro acc E it' Ef h'
      simp only [List.foldlM, bind, Except.bind] at h'
      elim_err h' with r hr
      obtain ⟨ia, E', hrdef, hres, -⟩ := hstep acc E q.1 q.2 r hr
      have h2 := ih _ _ _ _ h'
      subst hrdef
      have hc := SourceExpr.resolve_getConsts_eq _ _ _ _ _ hres
      simp only [List.map_append, List.map_cons, List.map_nil, List.flatMap_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc] at h2 ⊢
      rw [h2]
      congr 1
      unfold exprLitTyNames
      rw [Lambda.LExpr.Proofs.getConsts_unresolved, hc]
  have h := hgen _ _ _ _ _ hfold
  simp only [List.map_nil, List.flatMap_nil, List.nil_append] at h
  rw [h]
  have hren : ∀ inv : List (String × Expression.Expr),
      ((inv.map (fun (l, i) => (l, renameExpr m i))).map (·.2)).flatMap exprLitTyNames =
        (inv.map (·.2)).flatMap exprLitTyNames := by
    intro inv
    induction inv with
    | nil => rfl
    | cons q rest ih =>
      simp only [List.map_cons, List.flatMap_cons, exprLitTyNames_renameExpr]
      rw [← ih]
  exact hren invariant

/-- A successful walk keeps the literal type names of its input, after the reversed
    accumulator. -/
private theorem go_litTyNames_eq
    (C C' : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program)
    (op : Option Procedure) (ss acc ss' : List Statement) (labels : List String)
    {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.go P op C Env ss acc labels m st
      = .ok (ss', Env', C', st')) :
    GoPreserves litNamesMeasure ss' acc ss := by
  refine go_ok_induct (motive := fun _ _ ss acc _ _ _ ss' _ _ _ => GoPreserves litNamesMeasure ss'
      acc ss)
    (motiveB := fun _ _ ss acc _ _ _ ss' _ _ _ => GoPreserves litNamesMeasure ss' acc ss)
    ?nil ?cmd ?block ?ite ?loop ?exit ?typeDecl ?blockScope ?blockFlat C Env ss acc labels ss'
    Env' C' h
  case nil =>
    intro _ _ _ _ _ _
    exact GoPreserves.nil _ _
  case cmd =>
    intro C Env acc labels m st srest cmd c' Env1 ss' Env' C' st' htc _ _ ih
    refine GoPreserves.cons ?_ ih
    show stmtLitTyNames _ = stmtLitTyNames _
    rw [stmtLitTyNames_cmd, stmtLitTyNames_cmd]
    exact (Statement.typeCheckCmd_litTyNames_eq C Env Env1 P _ c' htc).trans
      (litTyNames_renameCmd _ _ _ cmd)
  case block =>
    intro _ _ _ _ _ _ _ label bss md bss' Egb stb ss' Env' C' st' _ _ ihb _ ih
    refine GoPreserves.cons ?_ ih
    show stmtLitTyNames _ = stmtLitTyNames _
    rw [stmtLitTyNames_block, stmtLitTyNames_block]
    exact GoPreserves.of_nil_acc ihb
  case ite =>
    intro _ _ _ _ _ _ _ cond tss ess md condElab Ec tss' Et stt ess' Ee ste ss' Env' C' st'
      hcond _ _ iht _ ihe _ ih
    refine GoPreserves.cons ?_ ih
    have ht : stmtsLitTyNames _ = stmtsLitTyNames _ := GoPreserves.of_nil_acc iht
    have he : stmtsLitTyNames _ = stmtsLitTyNames _ := GoPreserves.of_nil_acc ihe
    show stmtLitTyNames _ = stmtLitTyNames _
    rw [stmtLitTyNames_ite, stmtLitTyNames_ite, condChecked_litTyNames hcond, ht, he]
  case loop =>
    intro _ _ _ _ _ _ _ guard measure invariant bss md guardElab Eg measureElab Em invElab Efold
      bss' Eb stb ss' Env' C' st' hgc hmc hic _ _ ihb _ ih
    refine GoPreserves.cons ?_ ih
    have hb : stmtsLitTyNames _ = stmtsLitTyNames _ := GoPreserves.of_nil_acc ihb
    show stmtLitTyNames _ = stmtLitTyNames _
    rw [stmtLitTyNames_loop, stmtLitTyNames_loop, hb]
    simp only [Statement.loopExprs, List.flatMap_append, condChecked_litTyNames hgc,
      measureChecked_litTyNames hmc, invariantsChecked_litTyNames hic]
  case exit => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => GoPreserves.cons rfl ih
  case typeDecl => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => GoPreserves.cons rfl ih
  case blockFlat => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => ih
  case blockScope => exact fun _ _ _ _ _ _ _ _ _ _ _ _ ih => ih

/-! ## Erasure survives statement elaboration -/

/-- Applying `F` to the output of a walk gives `F` of the statements emitted so far, in order,
    followed by `F` of the statements still to check. -/
private def GoAdd {α : Type} (F : List Statement → List α) (out acc inp : List Statement) :
    Prop :=
  F out = F acc.reverse ++ F inp

/-- With an empty accumulator, `GoAdd` gives `F` of the output equal to `F` of the input. -/
private theorem GoAdd.of_nil_acc {α : Type} {F : List Statement → List α} (hnil : F [] = [])
    {out inp : List Statement} (h : GoAdd F out [] inp) : F out = F inp := by
  simpa only [GoAdd, List.reverse_nil, hnil, List.nil_append] using h

/-- Equal `F` for one emitted statement extends the `GoAdd` walk invariant, when `F` distributes
    over concatenation. -/
private theorem GoAdd.cons {α : Type} {F : List Statement → List α}
    (hF : ∀ a b, F (a ++ b) = F a ++ F b) {acc srest out : List Statement} {s s' : Statement}
    (hn : F [s'] = F [s]) (hih : GoAdd F out (s' :: acc) srest) : GoAdd F out acc (s :: srest) := by
  unfold GoAdd at hih ⊢
  have hcons : F (s :: srest) = F [s] ++ F srest := hF [s] srest
  rw [hih, List.reverse_cons, hF acc.reverse [s'], hn, hcons, List.append_assoc]

/-- A checked guard keeps the erasure of its source. -/
private theorem condChecked_eraseTypes {C : LContext CoreLParams} {Env Ec : TEnv Unit}
    {m : ScopeMap} {cond condElab : ExprOrNondet Expression}
    (h : CondChecked C Env (renameExprOrNondet m cond) condElab Ec) :
    (condElab.map LExpr.eraseTypes : ExprOrNondet Expression) =
      cond.map LExpr.eraseTypes := by
  cases cond with
  | nondet =>
    simp only [renameExprOrNondet, ExprOrNondet.map, CondChecked] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  | det c =>
    simp only [renameExprOrNondet, ExprOrNondet.map, CondChecked] at h
    obtain ⟨conda, hres, -, rfl⟩ := h
    simp only [ExprOrNondet.map]
    rw [SourceExpr.resolve_unresolved_eraseTypes _ _ _ _ _ hres,
      WrittenTyVarScope.eraseTypes_renameExpr]

/-- A checked measure keeps the erasure of its source. -/
private theorem measureChecked_eraseTypes {C : LContext CoreLParams} {Env Em : TEnv Unit}
    {m : ScopeMap} {measure measureElab : Option Expression.Expr}
    (h : MeasureChecked C Env (measure.map (renameExpr m)) measureElab Em) :
    measureElab.map LExpr.eraseTypes = measure.map LExpr.eraseTypes := by
  cases measure with
  | none =>
    simp only [Option.map, MeasureChecked] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  | some mm =>
    simp only [Option.map, MeasureChecked] at h
    obtain ⟨ma, hres, -, rfl⟩ := h
    simp only [Option.map]
    rw [SourceExpr.resolve_unresolved_eraseTypes _ _ _ _ _ hres,
      WrittenTyVarScope.eraseTypes_renameExpr]

/-- Checked invariants keep the erasure of their sources. -/
private theorem invariantsChecked_eraseTypes {C : LContext CoreLParams} {Env Efold : TEnv Unit}
    {m : ScopeMap} {invariant invElab : List (String × Expression.Expr)}
    (h : InvariantsChecked C Env (invariant.map (fun (l, i) => (l, renameExpr m i))) invElab
      Efold) :
    invElab.map (fun p => (p.1, p.2.eraseTypes)) =
      invariant.map (fun p => (p.1, p.2.eraseTypes)) := by
  obtain ⟨step, it, hstep, hfold, rfl⟩ := h
  have hgen : ∀ (inv : List (String × Expression.Expr))
      (acc : List (String × LExprT CoreLParams.mono)) (E : TEnv Unit)
      (it' : List (String × LExprT CoreLParams.mono)) (Ef : TEnv Unit),
      inv.foldlM step (acc, E) = .ok (it', Ef) →
      (it'.map (fun x => (x.1, x.2.unresolved))).map (fun p => (p.1, p.2.eraseTypes)) =
        (acc.map (fun x => (x.1, x.2.unresolved))).map (fun p => (p.1, p.2.eraseTypes)) ++
          inv.map (fun p => (p.1, p.2.eraseTypes)) := by
    intro inv
    induction inv with
    | nil =>
      intro acc E it' Ef h'
      simp only [List.foldlM, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h'
      obtain ⟨rfl, -⟩ := h'
      simp only [List.map_nil, List.append_nil]
    | cons q rest ih =>
      intro acc E it' Ef h'
      simp only [List.foldlM, bind, Except.bind] at h'
      elim_err h' with r hr
      obtain ⟨ia, E', hrdef, hres, -⟩ := hstep acc E q.1 q.2 r hr
      have h2 := ih _ _ _ _ h'
      subst hrdef
      simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.cons_append, List.nil_append] at h2 ⊢
      rw [h2, SourceExpr.resolve_unresolved_eraseTypes _ _ _ _ _ hres]
  have h := hgen _ _ _ _ _ hfold
  simp only [List.map_nil, List.nil_append] at h
  rw [h]
  simp only [List.map_map]
  refine List.map_congr_left fun q _ => ?_
  simp only [Function.comp, WrittenTyVarScope.eraseTypes_renameExpr]

/-- A successful walk keeps the erasure of its input, after the reversed accumulator. -/
private theorem go_eraseAnnots_eq
    (C C' : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program)
    (op : Option Procedure) (ss acc ss' : List Statement) (labels : List String)
    {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.go P op C Env ss acc labels m st
      = .ok (ss', Env', C', st')) :
    GoAdd Statements.eraseAnnots ss' acc ss := by
  have hF : ∀ a b, Statements.eraseAnnots (a ++ b) =
      Statements.eraseAnnots a ++ Statements.eraseAnnots b := Statements.eraseAnnots_append
  have hnil : Statements.eraseAnnots [] = [] := Statements.eraseAnnots_nil
  have hone : ∀ s, Statements.eraseAnnots [s] = [Statement.eraseAnnots s] := fun s => by
    rw [Statements.eraseAnnots_cons, hnil]
  refine go_ok_induct
    (motive := fun _ _ ss acc _ _ _ ss' _ _ _ => GoAdd Statements.eraseAnnots ss' acc ss)
    (motiveB := fun _ _ ss acc _ _ _ ss' _ _ _ => GoAdd Statements.eraseAnnots ss' acc ss)
    ?nil ?cmd ?block ?ite ?loop ?exit ?typeDecl ?blockScope ?blockFlat C Env ss acc labels ss'
    Env' C' h
  case nil =>
    intro _ _ _ _ _ _
    simp only [GoAdd, hnil, List.append_nil]
  case cmd =>
    intro C Env acc labels m st srest cmd c' Env1 ss' Env' C' st' htc _ _ ih
    refine GoAdd.cons hF ?_ ih
    rw [hone, hone, Statement.eraseAnnots_cmd, Statement.eraseAnnots_cmd,
      (Statement.typeCheckCmd_eraseAnnots_eq C Env Env1 P _ c' htc).trans
        (Command.eraseAnnots_renameCmd _ _ _ cmd)]
  case block =>
    intro _ _ _ _ _ _ _ label bss md bss' Egb stb ss' Env' C' st' _ _ ihb _ ih
    refine GoAdd.cons hF ?_ ih
    rw [hone, hone, Statement.eraseAnnots_block, Statement.eraseAnnots_block,
      GoAdd.of_nil_acc hnil ihb]
  case ite =>
    intro _ _ _ _ _ _ _ cond tss ess md condElab Ec tss' Et stt ess' Ee ste ss' Env' C' st'
      hcond _ _ iht _ ihe _ ih
    refine GoAdd.cons hF ?_ ih
    rw [hone, hone, Statement.eraseAnnots_ite, Statement.eraseAnnots_ite,
      condChecked_eraseTypes hcond, GoAdd.of_nil_acc hnil iht, GoAdd.of_nil_acc hnil ihe]
  case loop =>
    intro _ _ _ _ _ _ _ guard measure invariant bss md guardElab Eg measureElab Em invElab Efold
      bss' Eb stb ss' Env' C' st' hgc hmc hic _ _ ihb _ ih
    refine GoAdd.cons hF ?_ ih
    rw [hone, hone, Statement.eraseAnnots_loop, Statement.eraseAnnots_loop,
      condChecked_eraseTypes hgc, measureChecked_eraseTypes hmc,
      invariantsChecked_eraseTypes hic, GoAdd.of_nil_acc hnil ihb]
  case exit =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih
    exact GoAdd.cons hF rfl ih
  case typeDecl =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih
    exact GoAdd.cons hF rfl ih
  case blockFlat => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => ih
  case blockScope => exact fun _ _ _ _ _ _ _ _ _ _ _ _ ih => ih

/-! ## The public statement checker -/

/-- The final substitution of a statement check absorbs the substitution its walk solved. -/
theorem Statement.finalSubstInfo_absorbs (before : TState) (Env : Expression.TyEnv) :
    Subst.absorbs (Statement.finalSubstInfo before Env).subst Env.stateSubstInfo.subst :=
  ambientSubst_absorbs _ _ _ (Subst.absorbs_refl _ Env.stateSubstInfo.isWF)

/-- Statement checking runs the walk and applies its final substitution to the emitted statements
    and output context; the emitted statements' types are registered in the input context. -/
private theorem Statement.typeCheck_ok_inv
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (P : Program)
    (op : Option Procedure) (ss ss' : List Statement)
    (h : Statement.typeCheck C Env P op ss = .ok (ss', Env')) :
    ∃ ssA EnvA CA,
      Statement.typeCheckAux C Env P op ss = .ok (ssA, EnvA, CA) ∧
      ss' = Statement.Statement.subst.go
        (Statement.finalSubstInfo Env.genEnv.genState EnvA).subst ssA [] ∧
      Env' = (EnvA.updateSubst
          (Statement.finalSubstInfo Env.genEnv.genState EnvA)).updateContext
        (TContext.subst EnvA.context
          (Statement.finalSubstInfo Env.genEnv.genState EnvA).subst) ∧
      (Statement.tysDeclaredStmts C.knownTypes ss').isSome = true := by
  unfold Statement.typeCheck at h
  simp only [bind, Except.bind] at h
  split at h
  · simp only [reduceCtorEq] at h
  · rename_i r hr
    obtain ⟨ssA, EnvA, CA⟩ := r
    split at h
    · simp only [reduceCtorEq] at h
    · rename_i hsweep
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨ssA, EnvA, CA, hr, rfl, rfl, ?_⟩
      unfold Statement.tysDeclaredWhereStored at hsweep
      split at hsweep
      · rename_i k hk
        unfold Statement.tysDeclaredStmts
        rw [hk]
        rfl
      · simp only [reduceCtorEq] at hsweep

public section

/-! ### The walk keeps the substitution free of parameter-named type variables
A body checked with its type parameters replaced by constants writes no parameter name, and the
walk introduces none. -/

mutual
/-- No type variable in `ps` occurs free in a declared type or in a free-variable or binder
    annotation the statement writes. -/
def Statement.SrcAvoid (ps : List TyIdentifier) : Statement → Prop
  | .cmd c => Command.VarsAvoid ps c
  | .block _ bss _ => Statements.SrcAvoid ps bss
  | .ite c tss ess _ =>
    (∀ x, c = .det x → LExpr.AnnotsAvoid x ps) ∧ Statements.SrcAvoid ps tss ∧
      Statements.SrcAvoid ps ess
  | .loop g me inv bss _ =>
    (∀ x, g = .det x → LExpr.AnnotsAvoid x ps) ∧ (∀ x, me = some x → LExpr.AnnotsAvoid x ps) ∧
      (∀ p ∈ inv, LExpr.AnnotsAvoid p.2 ps) ∧ Statements.SrcAvoid ps bss
  | .exit _ _ | .typeDecl _ _ => True

/-- The list form of `Statement.SrcAvoid`. -/
def Statements.SrcAvoid (ps : List TyIdentifier) : List Statement → Prop
  | [] => True
  | s :: ss => Statement.SrcAvoid ps s ∧ Statements.SrcAvoid ps ss
end

/-- Skolemizing an expression removes the renamed parameters from its free-variable and binder
    annotations. -/
private theorem annotsAvoid_skolemizeBody_self (nm : Option String) (σ : RigidNames)
    (e : Expression.Expr) : LExpr.AnnotsAvoid (skolemizeBody nm σ e) (σ.map Prod.fst) :=
  annotsAvoid_skolemizeBody nm σ e (fun _ _ _ _ => (Decidable.em _).symm)

/-- Skolemizing a command removes the renamed parameters from its declared type and from the
    annotations of the expressions it reads. -/
private theorem commandVarsAvoid_skolemizeCmd (σ : RigidNames) (c : Command) :
    Command.VarsAvoid (σ.map Prod.fst) (skolemizeCmd none σ c) := by
  cases c with
  | cmd cc =>
    cases cc with
    | init x ty e md =>
      obtain ⟨vs, t⟩ := ty
      refine ⟨?_, ?_⟩
      · intro v hv
        simp only [mapLTyTys, LTy.freeVars, List.removeAll, List.mem_filter] at hv
        exact (LMonoTy.mem_freeVars_skolemizeTy σ t v hv.1).2
      · intro x' hx'
        cases e with
        | det e0 =>
          simp only [ExprOrNondet.map, ExprOrNondet.det.injEq] at hx'
          subst hx'
          exact annotsAvoid_skolemizeBody_self none σ e0
        | nondet => cases hx'
    | set x e md =>
      intro x' hx'
      cases e with
      | det e0 =>
        simp only [ExprOrNondet.map, ExprOrNondet.det.injEq] at hx'
        subst hx'
        exact annotsAvoid_skolemizeBody_self none σ e0
      | nondet => cases hx'
    | assert l b md => exact annotsAvoid_skolemizeBody_self none σ b
    | assume l b md => exact annotsAvoid_skolemizeBody_self none σ b
    | cover l b md => exact annotsAvoid_skolemizeBody_self none σ b
  | call pname tyArgs args md =>
    have hargs : ∀ as : List (CallArg Expression),
        ∀ e ∈ CallArg.getInputExprs (as.map (CallArg.mapInput (skolemizeBody none σ))),
          LExpr.AnnotsAvoid e (σ.map Prod.fst) := by
      intro as e he
      simp only [CallArg.getInputExprs, Calls.getInputExprs, List.mem_filterMap, List.mem_map] at he
      obtain ⟨a, ⟨a0, -, rfl⟩, ha⟩ := he
      cases a0 with
      | inArg e0 =>
        simp only [CallArg.mapInput, Option.some.injEq] at ha
        subst ha
        exact annotsAvoid_skolemizeBody_self none σ e0
      | inoutArg id =>
        simp only [CallArg.mapInput, Option.some.injEq] at ha
        subst ha
        intro t ht
        have hfvar : (HasFvar.mkFvar id : Expression.Expr) = LExpr.fvar Core.coreLoc id none := rfl
        rw [hfvar] at ht
        simp [LExpr.fvarAnnotations, LExpr.binderAnnotations] at ht
      | outArg id => simp [CallArg.mapInput] at ha
    exact hargs args

mutual
/-- A statement skolemized by `σ` writes no free type variable that `σ` renames. -/
theorem Statement.srcAvoid_skolemizeStmt (σ : RigidNames) :
    ∀ s : Statement, Statement.SrcAvoid (σ.map Prod.fst) (skolemizeStmt none σ s)
  | .cmd c => by
    rw [skolemizeStmt_cmd]
    exact commandVarsAvoid_skolemizeCmd σ c
  | .block _ bss _ => by
    rw [skolemizeStmt_block]
    exact Statements.srcAvoid_skolemizeStmts σ bss
  | .ite c tss ess _ => by
    rw [skolemizeStmt_ite]
    refine ⟨?_, Statements.srcAvoid_skolemizeStmts σ tss, Statements.srcAvoid_skolemizeStmts σ ess⟩
    intro x hx
    cases c with
    | det c0 =>
      simp only [ExprOrNondet.map, ExprOrNondet.det.injEq] at hx
      subst hx
      exact annotsAvoid_skolemizeBody_self none σ c0
    | nondet => cases hx
  | .loop g me inv bss _ => by
    rw [skolemizeStmt_loop]
    refine ⟨?_, ?_, ?_, Statements.srcAvoid_skolemizeStmts σ bss⟩
    · intro x hx
      cases g with
      | det g0 =>
        simp only [ExprOrNondet.map, ExprOrNondet.det.injEq] at hx
        subst hx
        exact annotsAvoid_skolemizeBody_self none σ g0
      | nondet => cases hx
    · intro x hx
      cases me with
      | some m0 =>
        simp only [Option.map_some, Option.some.injEq] at hx
        subst hx
        exact annotsAvoid_skolemizeBody_self none σ m0
      | none => cases hx
    · intro p hp
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp hp
      exact annotsAvoid_skolemizeBody_self none σ q.2
  | .exit _ _ => by
    rw [skolemizeStmt_exit]
    trivial
  | .typeDecl _ _ => by
    rw [skolemizeStmt_typeDecl]
    trivial

/-- The list form of `Statement.srcAvoid_skolemizeStmt`. -/
theorem Statements.srcAvoid_skolemizeStmts (σ : RigidNames) :
    ∀ ss : List Statement, Statements.SrcAvoid (σ.map Prod.fst) (skolemizeStmts none σ ss)
  | [] => by
    rw [skolemizeStmts_empty]
    trivial
  | s :: ss => by
    rw [skolemizeStmts_cons]
    exact ⟨Statement.srcAvoid_skolemizeStmt σ s, Statements.srcAvoid_skolemizeStmts σ ss⟩
end

/-- Checking a condition keeps a well-formed environment avoiding `ps` when the written condition's
    annotations avoid `ps` and so do the scope map's checker names. -/
private theorem condChecked_varsAvoid {ps : List TyIdentifier} {C : LContext CoreLParams}
    {Env Ec : TEnv Unit} {m : ScopeMap} {cond condElab : ExprOrNondet Expression}
    (hcond : CondChecked C Env (renameExprOrNondet m cond) condElab Ec)
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hne : Env.context.types ≠ [])
    (hf : FactorySigWF C.functions) (hgen : NoGenName ps) (hm : ∀ p ∈ m, p.2 ∉ ps)
    (hsrc : ∀ x, cond = .det x → LExpr.AnnotsAvoid x ps) (hE : TEnv.VarsAvoid Env ps) :
    TEnv.VarsAvoid Ec ps := by
  cases cond with
  | det c0 =>
    obtain ⟨conda, hrs, -, -⟩ := hcond
    exact (SourceExpr.resolve_varsAvoid C Env Ec _ conda hrs he hne hf hgen
      (annotsAvoid_renameExpr hm (hsrc c0 rfl)) hE).1
  | nondet =>
    obtain ⟨-, rfl⟩ := hcond
    exact hE

/-- Checking a loop's invariants keeps a well-formed environment avoiding `ps` when every
    invariant's annotations avoid `ps`. -/
private theorem invariantsChecked_varsAvoid {ps : List TyIdentifier} {C : LContext CoreLParams}
    {Env Efold : TEnv Unit} {inv invElab : List (String × Expression.Expr)}
    (hi : InvariantsChecked C Env inv invElab Efold)
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hne : Env.context.types ≠ [])
    (hf : FactorySigWF C.functions) (hgen : NoGenName ps)
    (hsrc : ∀ p ∈ inv, LExpr.AnnotsAvoid p.2 ps) (hE : TEnv.VarsAvoid Env ps) :
    TEnv.VarsAvoid Efold ps := by
  obtain ⟨step, it, hst, hfold, -⟩ := hi
  suffices key : ∀ (l : List (String × Expression.Expr)) acc E itout Eout,
      l.foldlM step (acc, E) = .ok (itout, Eout) → LExpr.TEnvWF (T := CoreLParams) E →
      E.context.types ≠ [] → (∀ p ∈ l, LExpr.AnnotsAvoid p.2 ps) → TEnv.VarsAvoid E ps →
      TEnv.VarsAvoid Eout ps from key inv [] Env it Efold hfold he hne hsrc hE
  intro l
  induction l with
  | nil =>
    intro acc E itout Eout h _ _ _ hE
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact hE
  | cons hd tl ih =>
    intro acc E itout Eout h hwf hne' hs hE
    obtain ⟨lbl, i⟩ := hd
    rw [List.foldlM_cons] at h
    obtain ⟨r, hr, h⟩ := (Except.bind_is_ok _ _ _).mp h
    obtain ⟨ia, E', rfl, hres, -⟩ := hst acc E lbl i r hr
    have hwf' := SourceExpr.resolve_TEnvWF C E E' i ia hres hwf hf
    have hne'' :=
      (SourceExpr.resolve_context_equiv_of_ne C E E' i ia hres hne').symm.types_ne_nil hne'
    have hE' := (SourceExpr.resolve_varsAvoid C E E' i ia hres hwf hne' hf hgen
      (hs (lbl, i) List.mem_cons_self) hE).1
    exact ih _ _ _ _ h hwf' hne'' (fun p hp => hs p (List.mem_cons_of_mem _ hp)) hE'

/-- The statement walk only adds names a fresh checker name must avoid. -/
private theorem go_avoid_mono {P : Program} {op : Option Procedure}
    (C C' : LContext CoreLParams) (Env Env' : TEnv Unit) (ss acc ss' : List Statement)
    (labels : List String) {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.go P op C Env ss acc labels m st
      = .ok (ss', Env', C', st')) :
    ∀ x ∈ st.avoid, x ∈ st'.avoid := by
  refine go_ok_induct
    (motive := fun _ _ _ _ _ _ st _ _ _ st' => ∀ x ∈ st.avoid, x ∈ st'.avoid)
    (motiveB := fun _ _ _ _ _ _ st _ _ _ st' => ∀ x ∈ st.avoid, x ∈ st'.avoid)
    ?nil ?cmd ?block ?ite ?loop ?exit ?typeDecl ?blockScope ?blockFlat C Env ss acc labels ss'
    Env' C' h
  case nil => exact fun _ _ _ _ _ _ _ hx => hx
  case cmd =>
    intro C _ _ _ m st _ cmd _ _ _ _ _ _ _ _ _ ih x hx
    exact ih x (renameCmd_avoid_mono _ m st cmd x hx)
  case block =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihb _ ih x hx
    exact ih x (ihb x hx)
  case ite =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ iht _ ihe _ ih x hx
    exact ih x (ihe x (iht x hx))
  case loop =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihb _ ih x hx
    exact ih x (ihb x hx)
  case exit =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih x hx
    exact ih x hx
  case typeDecl =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih x hx
    exact ih x hx
  case blockFlat => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => ih
  case blockScope =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ ih x hx
    exact ih x hx

/-- Checking a block only adds names a fresh checker name must avoid. -/
private theorem goBlock_avoid_mono {P : Program} {op : Option Procedure}
    {C C' : LContext CoreLParams} {Env Env' : TEnv Unit} {bss acc ss' : List Statement}
    {labels : List String} {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.goBlock P op C Env bss acc labels m st
      = .ok (ss', Env', C', st')) :
    ∀ x ∈ st.avoid, x ∈ st'.avoid := by
  rcases goBlock_ok_inv h with ⟨-, Ego, Cgo, hg, -, -⟩ | ⟨-, -, -, Cgo, hg, -⟩
  · exact go_avoid_mono C Cgo _ Ego bss acc ss' labels hg
  · exact go_avoid_mono C Cgo _ Env' bss acc ss' labels hg

/-- The statement walk keeps the environment avoiding `ps` and `ps` among the names fresh checker
    names avoid, when `ps` holds no generated name and the statements and scope avoid `ps`. -/
private theorem go_varsAvoid {P : Program} {op : Option Procedure} {ps : List TyIdentifier}
    (hgen : NoGenName ps) (hsigs : ProcSigsDeclared P)
    (C C' : LContext CoreLParams) (Env Env' : TEnv Unit) (ss acc ss' : List Statement)
    (labels : List String) {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.go P op C Env ss acc labels m st
      = .ok (ss', Env', C', st'))
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hne : Env.context.types ≠ [])
    (hf : FactorySigWF C.functions) (hsrc : Statements.SrcAvoid ps ss)
    (hsc : ScopeAvoids ps m st) (hE : TEnv.VarsAvoid Env ps) :
    TEnv.VarsAvoid Env' ps ∧ ∀ x ∈ ps, x ∈ st'.avoid := by
  refine go_ok_induct
    (motive := fun C Env ss _ _ m st _ Env' _ st' =>
      LExpr.TEnvWF (T := CoreLParams) Env → Env.context.types ≠ [] → FactorySigWF C.functions →
      Statements.SrcAvoid ps ss → ScopeAvoids ps m st →
      TEnv.VarsAvoid Env ps → TEnv.VarsAvoid Env' ps ∧ ∀ x ∈ ps, x ∈ st'.avoid)
    (motiveB := fun C Env ss _ _ m st _ Env' _ st' =>
      LExpr.TEnvWF (T := CoreLParams) Env → Env.context.types ≠ [] → FactorySigWF C.functions →
      Statements.SrcAvoid ps ss → ScopeAvoids ps m st →
      TEnv.VarsAvoid Env ps → TEnv.VarsAvoid Env' ps ∧ ∀ x ∈ ps, x ∈ st'.avoid)
    ?nil ?cmd ?block ?ite ?loop ?exit ?typeDecl ?blockScope ?blockFlat C Env ss acc labels ss'
    Env' C' h he hne hf hsrc hsc hE
  case nil => exact fun _ _ _ _ _ _ _ _ _ _ hsc hE => ⟨hE, hsc.avoid⟩
  case cmd =>
    intro C Env _ _ m st _ cmd c' Env1 _ _ _ _ htc _ _ ih he hne hf hsrc hsc hE
    obtain ⟨hcRen, hscRen⟩ :=
      renameCmd_varsAvoid C.rigidTypeVars m st cmd hsrc.1 hsc
    exact ih (Statement.typeCheckCmd_preserves_TEnvWF C Env Env1 P _ c' htc he hf)
      (Statement.typeCheckCmd_preserves_context_types_ne C Env Env1 P _ c' htc hne) hf hsrc.2 hscRen
      (Statement.typeCheckCmd_varsAvoid C Env Env1 P _ c' htc he hne hf hgen hsigs hcRen hE)
  case block =>
    intro _ Env _ _ _ _ _ _ _ _ _ Eb _ _ _ _ _ _ hgb ihb _ ih he hne hf hsrc hsc hE
    obtain ⟨hEb, havb⟩ := ihb he hne hf hsrc.1 hsc hE
    obtain ⟨-, hwfb, hneb⟩ := (EnvScopeStep.of_goBlock hgb hf).facts he hne
    exact ih hwfb hneb hf hsrc.2 ⟨hsc.names, havb⟩ hEb
  case ite =>
    intro C Env _ _ _ _ _ _ _ _ _ _ Ec _ Et _ _ Ee _ _ _ _ _ hcond _ hgt iht hge ihe _ ih
      he hne hf hsrc hsc hE
    obtain ⟨⟨hcSrc, htSrc, heSrc⟩, hrestSrc⟩ := hsrc
    have hEc := condChecked_varsAvoid hcond he hne hf hgen hsc.names hcSrc hE
    obtain ⟨-, hwfc, hnec⟩ := (hcond.chain.scope hf).facts he hne
    obtain ⟨hEt, havt⟩ := iht hwfc hnec hf htSrc hsc hEc
    obtain ⟨-, hwft, hnet⟩ := (EnvScopeStep.of_goBlock hgt hf).facts hwfc hnec
    obtain ⟨hEe, havE⟩ := ihe hwft hnet hf heSrc ⟨hsc.names, havt⟩ hEt
    obtain ⟨-, hwfe, hnee⟩ := (EnvScopeStep.of_goBlock hge hf).facts hwft hnet
    exact ih hwfe hnee hf hrestSrc ⟨hsc.names, havE⟩ hEe
  case loop =>
    intro C Env _ _ m _ _ guard measure invariant _ _ _ Eg _ Em _ Efold _ Eb _ _ _ _ _ hg hm hi _
      hgb ihb _ ih he hne hf hsrc hsc hE
    obtain ⟨⟨hgSrc, hmSrc, hiSrc, hbSrc⟩, hrestSrc⟩ := hsrc
    have hEg := condChecked_varsAvoid hg he hne hf hgen hsc.names hgSrc hE
    obtain ⟨-, hwfg, hneg⟩ := (hg.chain.scope hf).facts he hne
    have hEm : TEnv.VarsAvoid Em ps := by
      cases measure with
      | some m0 =>
        obtain ⟨ma, hrs, -, -⟩ := hm
        exact (SourceExpr.resolve_varsAvoid C Eg Em _ ma hrs hwfg hneg hf hgen
          (annotsAvoid_renameExpr hsc.names (hmSrc m0 rfl)) hEg).1
      | none =>
        obtain ⟨-, rfl⟩ := hm
        exact hEg
    obtain ⟨-, hwfm, hnem⟩ := (hm.chain.scope hf).facts hwfg hneg
    have hiRen : ∀ p ∈ invariant.map (fun (l, i) => (l, renameExpr m i)),
        LExpr.AnnotsAvoid p.2 ps := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact annotsAvoid_renameExpr hsc.names (hiSrc q hq)
    have hEf := invariantsChecked_varsAvoid hi hwfm hnem hf hgen hiRen hEm
    obtain ⟨-, hwff, hnef⟩ := (hi.chain_mem.1.scope hf).facts hwfm hnem
    obtain ⟨hEb, havb⟩ := ihb hwff hnef hf hbSrc hsc hEf
    obtain ⟨-, hwfb, hneb⟩ := (EnvScopeStep.of_goBlock hgb hf).facts hwff hnef
    exact ih hwfb hneb hf hrestSrc ⟨hsc.names, havb⟩ hEb
  case exit =>
    exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih he hne hf hsrc hsc hE =>
      ih he hne hf hsrc.2 hsc hE
  case typeDecl =>
    intro C Env _ _ _ _ _ tc _ Cnew _ _ _ _ htc _ ih he hne hf hsrc hsc hE
    exact ih he hne (TypeConstructor.typeCheck_functions_eq htc ▸ hf) hsrc.2 hsc hE
  case blockFlat => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => ih
  case blockScope =>
    intro C Env _ _ _ _ _ _ Ego _ _ _ ih he _ hf hsrc hsc hE
    obtain ⟨hEgo, hav⟩ := ih (pushEmptyContext_preserves_TEnvWF (T := CoreLParams) Env he)
      (TEnv.pushEmptyContext_types_ne_nil (T := CoreLParams) Env) hf hsrc hsc
      (TEnv.VarsAvoid.pushEmptyContext (T := CoreLParams) hE)
    exact ⟨TEnv.VarsAvoid.popContext (T := CoreLParams) hEgo, hav⟩

/-- A name generated during a check has the generator's form. -/
private theorem Statement.generatedDuring_genName {before after : TState} {key : TyIdentifier}
    (h : Statement.generatedDuring before after key = true) :
    ∃ n : Nat, key = TState.tyPrefix ++ toString n := by
  obtain ⟨n, -, hn⟩ := (Statement.generatedDuring_iff _ _ _).mp h
  exact ⟨n, hn⟩

/-- Checking statements that write no type variable in the rigid, non-generated names `ps`, from
    an environment avoiding `ps`, ends with a substitution avoiding `ps`. -/
theorem Statement.typeCheck_varsAvoid {ps : List TyIdentifier}
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (P : Program)
    (op : Option Procedure) (ss ss' : List Statement)
    (h : Statement.typeCheck C Env P op ss = .ok (ss', Env'))
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hne : Env.context.types ≠ [])
    (hf : FactorySigWF C.functions) (hgen : NoGenName ps) (hsigs : ProcSigsDeclared P)
    (hrig : ∀ x ∈ ps, x ∈ C.rigidTypeVars) (hsrc : Statements.SrcAvoid ps ss)
    (hE : TEnv.VarsAvoid Env ps) :
    Subst.VarsAvoid Env'.stateSubstInfo.subst ps := by
  obtain ⟨ssA, EnvA, CA, haux, -, rfl, -⟩ :=
    Statement.typeCheck_ok_inv C Env Env' P op ss ss' h
  unfold Statement.typeCheckAux at haux
  simp only [bind, Except.bind] at haux
  elim_err haux with r hgo
  obtain ⟨ss1, E1, C1, st1⟩ := r
  simp only [Except.ok.injEq, Prod.mk.injEq] at haux
  obtain ⟨hss, hE1, -⟩ := haux
  rw [hss, hE1] at hgo
  have hsc0 : ScopeAvoids ps []
      (WrittenTyVarScope.initState C.rigidTypeVars (Statement.usedTyVars Env) ss) :=
    ⟨fun _ hp => absurd hp List.not_mem_nil, fun x hx =>
      List.mem_append_left _ (List.mem_append_right _ (hrig x hx))⟩
  obtain ⟨hEA, -⟩ := go_varsAvoid hgen hsigs C _ Env _ ss [] _ []
    hgo he hne hf hsrc hsc0 hE
  show Subst.VarsAvoid (Statement.finalSubstInfo Env.genEnv.genState EnvA).subst ps
  refine ambientSubst_varsAvoid _ _ ?_ hEA.1
  intro g hg
  obtain ⟨n, rfl⟩ := Statement.generatedDuring_genName hg
  exact hgen n

/-! ### Callees and variables of a checked statement list -/

/-- `Statement.typeCheck` preserves the called procedure names of the statement list. -/
theorem Statement.typeCheck_calledProcedureNames_eq
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (P : Program)
    (op : Option Procedure) (ss ss' : List Statement)
    (h : Statement.typeCheck C Env P op ss = .ok (ss', Env')) :
    Statements.calledProcedureNames ss' = Statements.calledProcedureNames ss := by
  obtain ⟨ssA, E1, C1, hr, rfl, -, -⟩ :=
    Statement.typeCheck_ok_inv C Env Env' P op ss ss' h
  obtain ⟨_, hr⟩ := typeCheckAux_ok_inv hr
  have hn : Statements.calledProcedureNames ssA = Statements.calledProcedureNames ss :=
    GoPreserves.of_nil_acc (go_calledProcedureNames_eq C C1 Env E1 P op ss [] ssA [] hr)
  rw [Statement_subst_go_calledProcedureNames, hn]

/-- `Statement.typeCheck` preserves the modified and scoped defined variables of the
    statement list. -/
theorem Statement.typeCheck_vars_eq
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (P : Program)
    (op : Option Procedure) (ss ss' : List Statement)
    (h : Statement.typeCheck C Env P op ss = .ok (ss', Env')) :
    Block.modifiedVars ss' = Block.modifiedVars ss ∧
    ∀ b, Block.definedVars ss' b = Block.definedVars ss b := by
  obtain ⟨ssA, E1, C1, hr, rfl, -, -⟩ :=
    Statement.typeCheck_ok_inv C Env Env' P op ss ss' h
  obtain ⟨_, hr⟩ := typeCheckAux_ok_inv hr
  obtain ⟨hm, hd⟩ := GoVars.of_nil_acc (go_vars_eq C C1 Env E1 P op ss [] ssA [] hr)
  refine ⟨?_, ?_⟩
  · rw [Statement_subst_go_modifiedVars, hm]
  · intro b
    rw [Statement_subst_go_definedVars, hd b]

/-- `Statement.typeCheck` keeps the erasure of the statement list: it adds type annotations to
    expressions, replaces the declared types of variable declarations, and applies the final
    type substitution, and changes nothing else. -/
theorem Statement.typeCheck_eraseAnnots_eq
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (P : Program)
    (op : Option Procedure) (ss ss' : List Statement)
    (h : Statement.typeCheck C Env P op ss = .ok (ss', Env')) :
    Statements.eraseAnnots ss' = Statements.eraseAnnots ss := by
  obtain ⟨ssA, E1, C1, hr, rfl, -, -⟩ :=
    Statement.typeCheck_ok_inv C Env Env' P op ss ss' h
  obtain ⟨_, hr⟩ := typeCheckAux_ok_inv hr
  have hn := GoAdd.of_nil_acc Statements.eraseAnnots_nil
    (go_eraseAnnots_eq C C1 Env E1 P op ss [] ssA [] hr)
  rw [Statement_subst_go_eq, List.reverse_nil, List.nil_append,
    Statements.eraseAnnots_map_subst, hn]

/-! ## Statement derivations carry `DeskolAmbientScope` -/

/-- `DeskolAmbientScope` carries over to an equivalent scope and to any ambient context whose
    factory satisfies `Q` and whose signatures avoid capture by the rigid parameter names. -/
private theorem DeskolAmbientScope.of_scopeEquiv {Q : Lambda.Factory CoreLParams → Prop}
    {σ : RigidNames} {C C' : LContext CoreLParams}
    {Γ Δ : TContext Unit} (hi : DeskolAmbientScope Q σ C Γ)
    (hEqv : TContext.Equiv (T := CoreLParams) Δ Γ)
    (hfac : Q C'.functions)
    (hsafe : FactorySigDeskolSafe σ C'.functions) :
    DeskolAmbientScope Q σ C' Δ :=
  { factoryWF := hfac
    signaturesSafe := hsafe
    monoScope := MonoScope_of_findEq hEqv.toFindEq hi.monoScope
    aliasesWF := TContext.AliasesWF.of_aliases_eq hEqv.2 hi.aliasesWF
    aliasesNoSkolem :=
      hEqv.2 ▸ hi.aliasesNoSkolem }

/-- A statement derivation with well-formed factories carries `DeskolAmbientScope` from its input
    context and scope to its output ones. -/
theorem StatementHasType_DeskolAmbientScope
    {P : Program}
    {Q : Lambda.Factory CoreLParams → Prop} {σ : RigidNames}
    {C Cfin : LContext CoreLParams} {Γ Γfin : TContext Unit} {Δ Δfin : WrittenEnv}
    {L : List String} {s : Statement}
    (h : StatementHasType P C Γ Δ L s Cfin Γfin Δfin)
    (hi : DeskolAmbientScope Q σ C Γ) :
    DeskolAmbientScope Q σ Cfin Γfin := by
  cases h with
  | cmd _ _ _ _ _ _ _ _ hce hEqv =>
    have haliases := hEqv.2.trans (TypeSpec.CmdExtHasType.aliases_eq hce)
    exact { factoryWF := hi.factoryWF
            signaturesSafe := hi.signaturesSafe
            monoScope :=
              MonoScope_of_findEq hEqv.toFindEq
                (CmdExtHasType_MonoScope hce hi.monoScope)
            aliasesWF := TContext.AliasesWF.of_aliases_eq haliases hi.aliasesWF
            aliasesNoSkolem := haliases ▸ hi.aliasesNoSkolem }
  | block _ _ _ _ _ _ _ _ _ _ _ _ _ hEqv =>
    exact hi.of_scopeEquiv hEqv hi.factoryWF hi.signaturesSafe
  | ite_det _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hEqv =>
    exact hi.of_scopeEquiv hEqv hi.factoryWF hi.signaturesSafe
  | ite_nondet _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hEqv =>
    exact hi.of_scopeEquiv hEqv hi.factoryWF hi.signaturesSafe
  | loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hEqv =>
    exact hi.of_scopeEquiv hEqv hi.factoryWF hi.signaturesSafe
  | exit _ _ _ _ _ _ _ _ hEqv =>
    exact hi.of_scopeEquiv hEqv hi.factoryWF hi.signaturesSafe
  | typeDecl _ _ _ _ _ _ _ _ _ _ hadd hEqv =>
    have hfun := Lambda.addKnownTypeWithError_functions_eq _ _ _ _ hadd
    have hfac : Q Cfin.functions := by
      rw [hfun]; exact hi.factoryWF
    have hsafe : FactorySigDeskolSafe σ Cfin.functions := by
      rw [hfun]; exact hi.signaturesSafe
    exact hi.of_scopeEquiv hEqv hfac hsafe

/-! ## Rigid type variables of statement typing; deskolemizing loop clauses -/

/-- Expressions satisfying `E` keep their type across deskolemization: an expression that has
    type `mty` when read through `r` in the skolem scope `Γ` has the deskolemized type when its
    deskolemization is read through `r'` in the rigid scope `Γ'`. -/
private abbrev ExprDeskolTransport (σ : RigidNames) (Csk Crig : LContext CoreLParams)
    (Γ Γ' : TContext Unit) (E : Core.Expression.Expr → Prop)
    (r r' : Core.Expression.Expr → Core.Expression.Expr) : Prop :=
  ∀ (e : Core.Expression.Expr) (mty : LMonoTy), E e →
    LExpr.HasType Csk Γ (r e) (.forAll [] mty) →
    LExpr.HasType Crig Γ' (r' (mapExprTys (deskolemizeTy σ) e))
      (.forAll [] (deskolemizeTy σ mty))

/-- Under an expression transport, an expression satisfying `E` whose type deskolemization fixes
    keeps that type once deskolemized. -/
private theorem expr_deskolemize_fixed
    {σ : RigidNames} {Csk Crig : LContext CoreLParams} {Γ Γ' : TContext Unit}
    {E : Core.Expression.Expr → Prop} {r r' : Core.Expression.Expr → Core.Expression.Expr}
    (h_tr : ExprDeskolTransport σ Csk Crig Γ Γ' E r r') {mty : LMonoTy}
    (hfix : deskolemizeTy σ mty = mty) {e : Core.Expression.Expr} (hE : E e)
    (h : LExpr.HasType Csk Γ (r e) (.forAll [] mty)) :
    LExpr.HasType Crig Γ' (r' (mapExprTys (deskolemizeTy σ) e)) (.forAll [] mty) := by
  have htr := h_tr e mty hE h
  rwa [hfix] at htr

/-- A deterministic loop guard satisfying `E` that is boolean read through `r` stays boolean
    deskolemized, read through `r'`. -/
private theorem loop_guard_deskolemize
    {σ : RigidNames} (hpfx : RigidNamesPrefixed σ) {Csk Crig : LContext CoreLParams}
    {Γ Γ' : TContext Unit} {E : Core.Expression.Expr → Prop}
    {r r' : Core.Expression.Expr → Core.Expression.Expr}
    (guard : ExprOrNondet Core.Expression)
    (h_tr : ExprDeskolTransport σ Csk Crig Γ Γ' E r r')
    (h_ann : ∀ g, guard = .det g → E g)
    (hg : ∀ g, guard = .det g → LExpr.HasType Csk Γ (r g) (.forAll [] .bool)) :
    ∀ g, guard.map (mapExprTys (deskolemizeTy σ)) = .det g →
      LExpr.HasType Crig Γ' (r' g) (.forAll [] .bool) := by
  intro g hgd
  cases guard with
  | nondet => simp only [ExprOrNondet.map, reduceCtorEq] at hgd
  | det g0 =>
    simp only [ExprOrNondet.map, ExprOrNondet.det.injEq] at hgd
    subst hgd
    exact expr_deskolemize_fixed h_tr (deskolemizeTy_bool hpfx) (h_ann g0 rfl) (hg g0 rfl)

/-- A present loop measure satisfying `E` that is integer-typed read through `r` stays
    integer-typed deskolemized, read through `r'`. -/
private theorem loop_measure_deskolemize
    {σ : RigidNames} (hpfx : RigidNamesPrefixed σ) {Csk Crig : LContext CoreLParams}
    {Γ Γ' : TContext Unit} {E : Core.Expression.Expr → Prop}
    {r r' : Core.Expression.Expr → Core.Expression.Expr}
    (measure : Option Core.Expression.Expr)
    (h_tr : ExprDeskolTransport σ Csk Crig Γ Γ' E r r')
    (h_ann : ∀ m, measure = some m → E m)
    (hm : ∀ m, measure = some m → LExpr.HasType Csk Γ (r m) (.forAll [] .int)) :
    ∀ m, measure.map (mapExprTys (deskolemizeTy σ)) = some m →
      LExpr.HasType Crig Γ' (r' m) (.forAll [] .int) := by
  intro m hmm
  cases measure with
  | none => simp only [Option.map_none, reduceCtorEq] at hmm
  | some m0 =>
    simp only [Option.map_some, Option.some.injEq] at hmm
    subst hmm
    exact expr_deskolemize_fixed h_tr (deskolemizeTy_int hpfx) (h_ann m0 rfl) (hm m0 rfl)

/-- Loop invariants satisfying `E` that are boolean read through `r` stay boolean deskolemized,
    read through `r'`. -/
private theorem loop_invariants_deskolemize
    {σ : RigidNames} (hpfx : RigidNamesPrefixed σ) {Csk Crig : LContext CoreLParams}
    {Γ Γ' : TContext Unit} {E : Core.Expression.Expr → Prop}
    {r r' : Core.Expression.Expr → Core.Expression.Expr}
    (invariants : List (String × Core.Expression.Expr))
    (h_tr : ExprDeskolTransport σ Csk Crig Γ Γ' E r r')
    (h_ann : ∀ q, q ∈ invariants → E q.2)
    (hinv : ∀ p, p ∈ invariants → LExpr.HasType Csk Γ (r p.2) (.forAll [] .bool)) :
    ∀ p, p ∈ invariants.map (fun (l, e) => (l, mapExprTys (deskolemizeTy σ) e)) →
      LExpr.HasType Crig Γ' (r' p.2) (.forAll [] .bool) := by
  intro p hp
  simp only [List.mem_map] at hp
  obtain ⟨q, hq, hqe⟩ := hp
  subst hqe
  exact expr_deskolemize_fixed h_tr (deskolemizeTy_bool hpfx) (h_ann q hq) (hinv q hq)

/-! ## Statement-level deskolemization with written type variables in scope -/

/-- The facts deskolemizing statement typing against `P` and the rigid names `σ` needs: each typing
    judgment transports across deskolemization, and the invariant `Inv` is preserved by statement
    typing. `A` is the predicate the statements' type annotations must satisfy. -/
structure DeskolHyps
    (P : Program) (σ : RigidNames) (Inv : LContext CoreLParams → TContext Unit → Prop)
    (A : LMonoTy → Bool) : Prop where
  /-- Every rigid constant of `σ` carries the reserved prefix. -/
  pfx : RigidNamesPrefixed σ
  /-- Expression typing transports across deskolemization, reading the expression through `Δ`
      on the skolem side and through its deskolemization `Δ'` on the rigid side; the annotations
      must avoid the renamed parameters. -/
  tr : ∀ (Csk Crig : LContext CoreLParams) (Γ Γ' : TContext Unit) (Δ Δ' : WrittenEnv)
      (e : Core.Expression.Expr) (mty : LMonoTy),
      Inv Csk Γ → AmbientDeskol σ Csk Crig → DeskolemizesScope σ Γ Γ' →
      EnvDeskol σ Δ Δ' → NoParamBinding σ Δ → ReadAvoids σ Δ →
      LExpr.AnnotsAvoid e (σ.map Prod.fst) →
      allExprTys A e = true → ConstTysFixed σ e →
      LExpr.HasType Csk Γ (instAnnots Δ e) (.forAll [] mty) →
      LExpr.HasType Crig Γ' (instAnnots Δ' (mapExprTys (deskolemizeTy σ) e))
        (.forAll [] (deskolemizeTy σ mty))
  /-- Every alias body and alias application is unchanged by deskolemization. -/
  aliasNoSkolem : ∀ (Csk : LContext CoreLParams) (Γ : TContext Unit),
      Inv Csk Γ → AliasesNoSkolem σ Γ.aliases
  /-- Every rigid constant of `σ` stands for a type variable a user may write. -/
  rigAdm : ∀ p ∈ σ, TyVarAdmissibility.notGeneratedOrRigid p.1 = true
  /-- The declaration conditions with written type variables transport across deskolemization,
      through `deskolInst`, when every renamed parameter is rigid and `Δ` binds none of them. -/
  declΔ : ∀ (Csk Crig : LContext CoreLParams) (Γ Γ' : TContext Unit) (Δ Δ' : WrittenEnv)
      (ρ : SubstOne) (ann mty : LMonoTy),
      Inv Csk Γ → AmbientDeskol σ Csk Crig → DeskolemizesScope σ Γ Γ' →
      EnvDeskol σ Δ Δ' → NoParamBinding σ Δ → (∀ q ∈ σ, q.1 ∈ Csk.rigidTypeVars) →
      A ann = true → (ScopedAnnotInst Γ.aliases Csk.rigidTypeVars Δ ρ ann mty ∧
        ValidDeclaredTy Csk Γ.aliases ann) →
      (ScopedAnnotInst Γ'.aliases Crig.rigidTypeVars Δ' (deskolInst σ ann ρ)
          (deskolemizeTy σ ann) (deskolemizeTy σ mty) ∧
        ValidDeclaredTy Crig Γ'.aliases (deskolemizeTy σ ann))
  /-- `Inv` is carried along a statement derivation. -/
  inv : ∀ (Cin Cfin : LContext CoreLParams) (Γin Γfin : TContext Unit) (Δin Δfin : WrittenEnv)
      (L : List String) (s : Statement),
      StatementHasType P Cin Γin Δin L s Cfin Γfin Δfin → Inv Cin Γin → Inv Cfin Γfin
  /-- Deskolemizing fixes the signature of every procedure a command calls. -/
  calls : ∀ c, CalledProcedureSignaturesFixed σ P c
  /-- Deskolemizing an annotation `A` accepts keeps its free type variables. -/
  keep : ∀ ann, A ann = true →
      ∀ v ∈ LMonoTy.freeVars ann, v ∈ LMonoTy.freeVars (deskolemizeTy σ ann)

/-- Call arguments transport across deskolemization: an unannotated variable is looked up in the
    deskolemized scope, and any other argument is typed as read through the environment. -/
private theorem callExpr_deskol
    {P : Program} {σ : RigidNames} {Inv : LContext CoreLParams → TContext Unit → Prop}
    {A : LMonoTy → Bool} (H : DeskolHyps P σ Inv A)
    {Csk Crig : LContext CoreLParams} {Γ Γ' : TContext Unit} {Δ Δ' : WrittenEnv}
    (hinv : Inv Csk Γ) (hamb : AmbientDeskol σ Csk Crig) (hsc : DeskolemizesScope σ Γ Γ')
    (henv : EnvDeskol σ Δ Δ') (hnp : NoParamBinding σ Δ) (hrd : ReadAvoids σ Δ) :
    ∀ (e : Expression.Expr) (mty : LMonoTy),
      LExpr.AnnotsAvoid e (σ.map Prod.fst) →
      allExprTys A e = true → ConstTysFixed σ e →
      (match e with
       | .fvar _ x none => Γ.types.find? x = some (.forAll [] mty)
       | e => LExpr.HasType Csk Γ (instAnnots Δ e) (.forAll [] mty)) →
      (match mapExprTys (deskolemizeTy σ) e with
       | .fvar _ x none => Γ'.types.find? x = some (.forAll [] (deskolemizeTy σ mty))
       | e => LExpr.HasType Crig Γ' (instAnnots Δ' e) (.forAll [] (deskolemizeTy σ mty))) := by
  intro e mty hav hae hlit he
  cases e with
  | fvar m x ann =>
    cases ann with
    | none =>
      simp only [mapExprTys, LExpr.replaceUserProvidedType, Option.map_none]
      rw [hsc.2 x, he]
      rfl
    | some ty => exact H.tr Csk Crig Γ Γ' Δ Δ' _ mty hinv hamb hsc henv hnp hrd hav hae hlit he
  | op | const | bvar | abs | quant | app | ite | eq =>
    exact H.tr Csk Crig Γ Γ' Δ Δ' _ mty hinv hamb hsc henv hnp hrd hav hae hlit he

/-- The annotation scope condition carries across deskolemization, from a context whose rigid
    type variables include every renamed parameter to its deskolemized context. -/
private theorem annotsInScope_deskol_of_ambient
    {σ : RigidNames} {Csk Crig : LContext CoreLParams} (hamb : AmbientDeskol σ Csk Crig)
    (hσ : ∀ q ∈ σ, q.1 ∈ Csk.rigidTypeVars) {Δ Δ' : WrittenEnv} (henv : EnvDeskol σ Δ Δ')
    {e : Core.Expression.Expr} (h : AnnotsInScope Csk.rigidTypeVars Δ e) :
    AnnotsInScope Crig.rigidTypeVars Δ' (mapExprTys (deskolemizeTy σ) e) := by
  rw [← hamb.rigidTypeVars_eq]
  exact annotsInScope_deskolemize σ hσ henv h

mutual

/-- A statement typed by the typechecker spec with written type variables in a context holding
    the skolems of `σ` stays typed, deskolemized, in a context making them rigid, from any
    deskolemized scope and environment; the outputs are again deskolemization-related. -/
private theorem StatementHasTypeΔ_deskol
    {P : Program} {σ : RigidNames}
    {Inv : LContext CoreLParams → TContext Unit → Prop} {A : LMonoTy → Bool}
    (H : DeskolHyps P σ Inv A) :
    (s : Statement) → ∀ {Csk Cfin : LContext CoreLParams} {Γ Γfin : TContext Unit}
      {Δ Δfin : WrittenEnv} {L : List String}
      (h : StatementHasType P Csk Γ Δ L s Cfin Γfin Δfin),
    StatementSideConditionsΔ σ h → Inv Csk Γ → allStmtTys A s = true →
    Statement.SrcAvoid (σ.map Prod.fst) s → (∀ p ∈ σ, p.2 ∉ stmtLitTyNames s) →
    (∀ q ∈ σ, q.1 ∈ Csk.rigidTypeVars) →
    NoParamBinding σ Δ →
    ∀ (Crig : LContext CoreLParams) (Γ' : TContext Unit) (Δ' : WrittenEnv),
    AmbientDeskol σ Csk Crig → DeskolemizesScope σ Γ Γ' → EnvDeskol σ Δ Δ' →
    ∃ Co Γo Δo,
      StatementHasType P Crig Γ' Δ' L (mapStmtTys (deskolemizeTy σ) s) Co Γo Δo ∧
      AmbientDeskol σ Cfin Co ∧ DeskolemizesScope σ Γfin Γo ∧ EnvDeskol σ Δfin Δo ∧
      NoParamBinding σ Δfin
  | .cmd c, _, _, _, _, _, _, _, _, hwf, hinv, hann, hsrc, hlit, hσ, hnp, Crig, Γ', Δ', hamb,
      hsc, henv => by
    cases hwf with
    | cmd hce heq hread =>
      obtain ⟨Γc', Δc', hce', hscc, henvc, hnpc⟩ :=
        TypeSpec.CmdExtHasType.deskolemize σ H.pfx P _ Crig
        _ Γ' _ _ Δ' _ c A hamb hsc
        (fun Δ₁ Δ₁' e mty henv₁ hnp₁ hrd₁ hav hae hl he =>
          H.tr _ Crig _ Γ' Δ₁ Δ₁' e mty hinv hamb hsc henv₁ hnp₁ hrd₁ hav hae hl he)
        (callExpr_deskol H hinv hamb hsc henv hnp)
        (fun ρ ann mty hA hd => H.declΔ _ Crig _ Γ' _ Δ' ρ ann mty hinv hamb hsc henv hnp hσ hA hd)
        (WellKindedTy_deskolemizeTy hamb)
        (H.aliasNoSkolem _ _ hinv) H.rigAdm (H.calls c) hann
        hsrc (ConstTysFixed_of_stmtLitTyNames_cmd hlit) hread hσ
        henv hnp H.keep hce
      rw [mapStmtTys_cmd]
      exact ⟨Crig, Γc', Δc', .cmd _ _ _ _ _ _ _ _ hce' (TContext.Equiv.refl _), hamb,
        DeskolemizesScope.of_equiv_left σ _ _ _ heq hscc, henvc, hnpc⟩
  | .block l b md, _, _, _, _, _, _, _, _, hwf, hinv, hann, hsrc, hlit, hσ, hnp,
      Crig, Γ', Δ', hamb, hsc, henv => by
    cases hwf with
    | block hnot hb heq hbwf =>
      have hannb : allStmtsTys A b = true := by simpa only [allStmtTys] using hann
      obtain ⟨_, _, _, hb', -, -, -, -⟩ :=
        StatementsHasTypeΔ_deskol H b hb hbwf hinv hannb hsrc (stmtLitTyNames_block_body hlit)
          hσ hnp Crig Γ' Δ' hamb hsc henv
      rw [mapStmtTys_block]
      exact ⟨Crig, Γ', Δ', .block _ _ _ _ _ _ _ _ _ _ _ hnot hb' (TContext.Equiv.refl _),
        hamb, DeskolemizesScope.of_equiv_left σ _ _ _ heq hsc, henv, hnp⟩
  | .ite (.det cond) t els md, _, _, _, _, Δ, _, _, _, hwf, hinv, hann, hsrc, hlit, hσ, hnp,
      Crig, Γ', Δ', hamb, hsc, henv => by
    cases hwf with
    | ite_det hcond hcondAnn hcondScope hread ht he heq hst hse =>
      simp only [allStmtTys, allExprOrNondetTys, Bool.and_eq_true] at hann
      obtain ⟨hlitc, hlitt, hlite⟩ := stmtLitTyNames_ite_parts hlit
      obtain ⟨_, _, _, ht', -, -, -, -⟩ :=
        StatementsHasTypeΔ_deskol H t ht hst hinv hann.1.2 (hsrc.2.1) hlitt hσ hnp
          Crig Γ' Δ' hamb hsc henv
      obtain ⟨_, _, _, he', -, -, -, -⟩ :=
        StatementsHasTypeΔ_deskol H els he hse hinv hann.2 (hsrc.2.2) hlite hσ hnp
          Crig Γ' Δ' hamb hsc henv
      have hcond' := H.tr _ Crig _ Γ' Δ Δ' cond .bool hinv hamb hsc henv hnp hread
        (hsrc.1 cond rfl) hann.1.1 (hlitc cond (List.mem_singleton_self _)) hcond
      rw [deskolemizeTy_bool H.pfx] at hcond'
      have hcondAnn' := writtenAnnotsOk_deskolemize σ _ Crig _ Γ' hamb hsc
        (H.aliasNoSkolem _ _ hinv) H.rigAdm cond hcondAnn
      rw [mapStmtTys_ite]
      exact ⟨Crig, Γ', Δ', .ite_det _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcond' hcondAnn'
        (annotsInScope_deskol_of_ambient hamb hσ henv hcondScope) ht' he'
        (TContext.Equiv.refl _), hamb, DeskolemizesScope.of_equiv_left σ _ _ _ heq hsc, henv, hnp⟩
  | .ite .nondet t els md, _, _, _, _, _, _, _, _, hwf, hinv, hann, hsrc, hlit, hσ, hnp,
      Crig, Γ', Δ', hamb, hsc, henv => by
    cases hwf with
    | ite_nondet ht he heq hst hse =>
      simp only [allStmtTys, allExprOrNondetTys, Bool.and_eq_true] at hann
      obtain ⟨-, hlitt, hlite⟩ := stmtLitTyNames_ite_parts hlit
      obtain ⟨_, _, _, ht', -, -, -, -⟩ :=
        StatementsHasTypeΔ_deskol H t ht hst hinv hann.1.2 (hsrc.2.1) hlitt hσ hnp
          Crig Γ' Δ' hamb hsc henv
      obtain ⟨_, _, _, he', -, -, -, -⟩ :=
        StatementsHasTypeΔ_deskol H els he hse hinv hann.2 (hsrc.2.2) hlite hσ hnp
          Crig Γ' Δ' hamb hsc henv
      rw [mapStmtTys_ite]
      exact ⟨Crig, Γ', Δ', .ite_nondet _ _ _ _ _ _ _ _ _ _ _ _ _ _ ht' he'
        (TContext.Equiv.refl _), hamb, DeskolemizesScope.of_equiv_left σ _ _ _ heq hsc, henv, hnp⟩
  | .loop guard measure invariants b md, _, _, _, _, Δ, _, _, _, hwf, hinv, hann, hsrc, hlit,
      hσ, hnp, Crig, Γ', Δ', hamb, hsc, henv => by
    cases hwf with
    | loop hg hgAnn hm hmAnn hi hiAnn hgS hmS hiS hb heq hread hbwf =>
      simp only [allStmtTys, Bool.and_eq_true] at hann
      obtain ⟨⟨⟨hanng, hannm⟩, hanni⟩, hannb⟩ := hann
      obtain ⟨hlitl, hlitb⟩ := stmtLitTyNames_loop_parts hlit
      have htrΓ : ∀ (e : Core.Expression.Expr) (mty : LMonoTy),
          ((allExprTys A e = true ∧ LExpr.AnnotsAvoid e (σ.map Prod.fst)) ∧
            ConstTysFixed σ e) →
          LExpr.HasType _ _ (instAnnots Δ e) (.forAll [] mty) →
          LExpr.HasType Crig Γ' (instAnnots Δ' (mapExprTys (deskolemizeTy σ) e))
            (.forAll [] (deskolemizeTy σ mty)) :=
        fun e mty hae he =>
          H.tr _ Crig _ Γ' Δ Δ' e mty hinv hamb hsc henv hnp hread hae.1.2 hae.1.1 hae.2 he
      have hwrΓ : ∀ e : Core.Expression.Expr, WrittenAnnotsOk _ _ e →
          WrittenAnnotsOk Crig Γ' (mapExprTys (deskolemizeTy σ) e) :=
        fun e he => writtenAnnotsOk_deskolemize σ _ Crig _ Γ' hamb hsc
          (H.aliasNoSkolem _ _ hinv) H.rigAdm e he
      obtain ⟨_, _, _, hb', -, -, -, -⟩ :=
        StatementsHasTypeΔ_deskol H b hb hbwf hinv hannb (hsrc.2.2.2) hlitb hσ hnp
          Crig Γ' Δ' hamb hsc henv
      rw [mapStmtTys_loop]
      refine ⟨Crig, Γ', Δ', .loop _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hb'
        (TContext.Equiv.refl _), hamb, DeskolemizesScope.of_equiv_left σ _ _ _ heq hsc, henv, hnp⟩
      · refine loop_guard_deskolemize H.pfx guard htrΓ ?_ hg
        intro g hgd
        subst hgd
        refine ⟨⟨by simpa only [allExprOrNondetTys] using hanng, hsrc.1 g rfl⟩, ?_⟩
        refine hlitl g ?_
        simp only [Statement.loopExprs, ExprOrNondet.toList, List.mem_append,
          List.mem_singleton, true_or]
      · intro g hgd
        cases guard with
        | nondet => simp only [ExprOrNondet.map, reduceCtorEq] at hgd
        | det g0 =>
          simp only [ExprOrNondet.map, ExprOrNondet.det.injEq] at hgd
          subst hgd
          exact hwrΓ g0 (hgAnn g0 rfl)
      · refine loop_measure_deskolemize H.pfx measure htrΓ ?_ hm
        intro m hmd
        subst hmd
        refine ⟨⟨by simpa using hannm, hsrc.2.1 m rfl⟩, ?_⟩
        refine hlitl m ?_
        simp only [Statement.loopExprs, List.mem_append, Option.mem_toList, or_true, true_or]
      · intro m hmm
        obtain ⟨m0, hm0, rfl⟩ := Option.map_eq_some_iff.mp hmm
        exact hwrΓ m0 (hmAnn m0 hm0)
      · refine loop_invariants_deskolemize H.pfx invariants htrΓ ?_ hi
        intro q hq
        refine ⟨⟨(List.all_eq_true.mp hanni) q hq, hsrc.2.2.1 q hq⟩, ?_⟩
        have hmem : q.2 ∈ Statement.loopExprs guard measure invariants := by
          simp only [Statement.loopExprs, List.mem_append, List.mem_map]
          exact Or.inr ⟨q, hq, rfl⟩
        exact hlitl q.2 hmem
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact hwrΓ q.2 (hiAnn q hq)
      · intro g hgd
        cases guard with
        | nondet => simp only [ExprOrNondet.map, reduceCtorEq] at hgd
        | det g0 =>
          simp only [ExprOrNondet.map, ExprOrNondet.det.injEq] at hgd
          subst hgd
          exact annotsInScope_deskol_of_ambient hamb hσ henv (hgS g0 rfl)
      · intro m hmm
        obtain ⟨m0, hm0, rfl⟩ := Option.map_eq_some_iff.mp hmm
        exact annotsInScope_deskol_of_ambient hamb hσ henv (hmS m0 hm0)
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact annotsInScope_deskol_of_ambient hamb hσ henv (hiS q hq)
  | .exit l md, _, _, _, _, _, _, _, _, hwf, _, _, _, _, _, hnp, Crig, Γ', Δ', hamb, hsc,
      henv => by
    cases hwf with
    | exit hmem heq =>
      rw [mapStmtTys_exit]
      exact ⟨Crig, Γ', Δ', .exit _ _ _ _ _ _ _ hmem (TContext.Equiv.refl _), hamb,
        DeskolemizesScope.of_equiv_left σ _ _ _ heq hsc, henv, hnp⟩
  | .typeDecl tc md, _, _, _, _, _, _, _, _, hwf, _, _, _, _, _, hnp, Crig, Γ', Δ', hamb, hsc,
      henv => by
    cases hwf with
    | typeDecl hprog hnotAlias hadd heq =>
      obtain ⟨Cnew', hadd', hamb'⟩ := addKnownTypeWithError_deskolemize σ _ Crig _ tc hamb hadd
      have hnotAlias' := nameNotAlias_of_aliases_eq hsc.1 hnotAlias
      rw [mapStmtTys_typeDecl]
      exact ⟨Cnew', Γ', Δ',
        .typeDecl _ _ _ _ _ _ _ _ hprog hnotAlias' hadd' (TContext.Equiv.refl _),
        hamb',
        DeskolemizesScope.of_equiv_left σ _ _ _ heq hsc, henv, hnp⟩

/-- A statement list typed by the typechecker spec with written type variables in a context
    holding the skolems of `σ` stays typed, deskolemized, in a context making them rigid, from
    any deskolemized scope and environment; the outputs are again deskolemization-related. -/
private theorem StatementsHasTypeΔ_deskol
    {P : Program} {σ : RigidNames}
    {Inv : LContext CoreLParams → TContext Unit → Prop} {A : LMonoTy → Bool}
    (H : DeskolHyps P σ Inv A) :
    (ss : List Statement) → ∀ {Csk Cfin : LContext CoreLParams} {Γ Γfin : TContext Unit}
      {Δ Δfin : WrittenEnv} {L : List String}
      (h : StatementsHasType P Csk Γ Δ L ss Cfin Γfin Δfin),
    StatementsSideConditionsΔ σ h → Inv Csk Γ → allStmtsTys A ss = true →
    Statements.SrcAvoid (σ.map Prod.fst) ss → (∀ p ∈ σ, p.2 ∉ stmtsLitTyNames ss) →
    (∀ q ∈ σ, q.1 ∈ Csk.rigidTypeVars) →
    NoParamBinding σ Δ →
    ∀ (Crig : LContext CoreLParams) (Γ' : TContext Unit) (Δ' : WrittenEnv),
    AmbientDeskol σ Csk Crig → DeskolemizesScope σ Γ Γ' → EnvDeskol σ Δ Δ' →
    ∃ Co Γo Δo,
      StatementsHasType P Crig Γ' Δ' L (mapStmtsTys (deskolemizeTy σ) ss) Co Γo Δo ∧
      AmbientDeskol σ Cfin Co ∧ DeskolemizesScope σ Γfin Γo ∧ EnvDeskol σ Δfin Δo ∧
      NoParamBinding σ Δfin
  | [], _, _, _, _, _, _, _, _, hwf, _, _, _, _, _, hnp, Crig, Γ', Δ', hamb, hsc, henv => by
    cases hwf with
    | nil heq =>
      rw [mapStmtsTys_nil]
      exact ⟨Crig, Γ', Δ', .nil _ _ _ _ _ (TContext.Equiv.refl _), hamb,
        DeskolemizesScope.of_equiv_left σ _ _ _ heq hsc, henv, hnp⟩
  | s :: ss, _, _, _, _, _, _, _, _, hwf, hinv, hann, hsrc, hlit, hσ, hnp,
      Crig, Γ', Δ', hamb, hsc, henv => by
    cases hwf with
    | cons hs ht hswf htwf =>
      simp only [allStmtsTys, Bool.and_eq_true] at hann
      obtain ⟨hanns, hannt⟩ := hann
      obtain ⟨hlits, hlitr⟩ := stmtsLitTyNames_cons_parts hlit
      obtain ⟨Cm', Γm', Δm', hs', hambm, hscm, henvm, hnpm⟩ :=
        StatementHasTypeΔ_deskol H s hs hswf hinv hanns (hsrc.1) hlits hσ hnp Crig
          Γ' Δ' hamb hsc henv
      have hσm : ∀ q ∈ σ, q.1 ∈ _ := fun q hq => hs.rigid_eq ▸ hσ q hq
      obtain ⟨Co', Γo', Δo', ht', hambo, hsco, henvo, hnpo⟩ :=
        StatementsHasTypeΔ_deskol H ss ht htwf (H.inv _ _ _ _ _ _ _ _ hs hinv)
          hannt (hsrc.2) hlitr hσm hnpm Cm' Γm' Δm' hambm hscm henvm
      rw [mapStmtsTys_cons]
      exact ⟨Co', Γo', Δo', .cons _ _ _ _ _ _ _ _ _ _ _ _ hs' ht', hambo, hsco, henvo, hnpo⟩

end

/-- A statement list typed by the typechecker spec with written type variables under
    `addSkolemTypes C₀ σ` stays typed, deskolemized, under `C₀` with `σ`'s names made rigid,
    from any deskolemized scope and environment; the output scopes and environments are again
    deskolemization-related. -/
theorem StatementsHasTypeΔ_of_deskolemized_outputAgree
    {P : Program}
    (σ : RigidNames) (C₀ : LContext CoreLParams)
    (Inv : LContext CoreLParams → TContext Unit → Prop) (A : LMonoTy → Bool)
    (H : DeskolHyps P σ Inv A)
    (h_base : FactorySigDeskolemizes σ C₀.functions C₀.functions)
    {Γ : TContext Unit} {Δ : WrittenEnv} {L : List String} {ss : List Statement}
    {Cout : LContext CoreLParams} {Γout : TContext Unit} {Δout : WrittenEnv}
    (h : StatementsHasType P (addSkolemTypes C₀ σ) Γ Δ L ss Cout Γout Δout)
    (hstrict : StatementsSideConditionsΔ σ h)
    (h_inv0 : Inv (addSkolemTypes C₀ σ) Γ)
    (h_ann : allStmtsTys A ss = true)
    (h_src : Statements.SrcAvoid (σ.map Prod.fst) ss)
    (h_lit : ∀ p ∈ σ, p.2 ∉ stmtsLitTyNames ss)
    (h_np : NoParamBinding σ Δ) :
    ∀ Γ' Δ', DeskolemizesScope σ Γ Γ' → EnvDeskol σ Δ Δ' →
      ∃ Cout' Γout' Δout',
        StatementsHasType P
          { C₀ with rigidTypeVars := C₀.rigidTypeVars ++ σ.map Prod.fst } Γ' Δ' L
          (mapStmtsTys (deskolemizeTy σ) ss) Cout' Γout' Δout' ∧
        DeskolemizesScope σ Γout Γout' ∧ EnvDeskol σ Δout Δout' := by
  intro Γ' Δ' hsc henv
  have hambRig : AmbientDeskol σ (addSkolemTypes C₀ σ)
      { C₀ with rigidTypeVars := C₀.rigidTypeVars ++ σ.map Prod.fst } :=
    ⟨fun x => addSkolemTypes_getElem?_congr C₀ _ σ (fun _ => rfl) x,
     rigidTypeVars_addSkolemTypes C₀ σ,
     by simpa only [addSkolemTypes] using h_base⟩
  obtain ⟨Cout', Γout', Δout', hd, -, hsco, henvo, -⟩ :=
    StatementsHasTypeΔ_deskol H ss h hstrict h_inv0 h_ann h_src h_lit
      (rigid_mem_addSkolemTypes C₀ σ) h_np
      { C₀ with rigidTypeVars := C₀.rigidTypeVars ++ σ.map Prod.fst } Γ' Δ' hambRig hsc henv
  exact ⟨Cout', Γout', Δout', hd, hsco, henvo⟩

/-! ## Statement typing across contexts with alias-equivalent scopes -/

section AliasScopeTransport

open Lambda.LExpr

/-- Two type contexts share one alias table and have lookup-wise alias-equivalent scopes. -/
private structure AliasScopeCtxRel (aliases : List TypeAlias)
    (ΓD ΓR : TContext Unit) : Prop where
  d_aliases : ΓD.aliases = aliases
  r_aliases : ΓR.aliases = aliases
  scopes : ScopeRel (T := CoreLParams) aliases ΓD.types ΓR.types

/-- Expression typing transfers from the resolved context to its alias-equivalent declared
    context when the shared aliases are well-formed. -/
private theorem AliasScopeCtxRel.expr {aliases : List TypeAlias}
    {ΓD ΓR : TContext Unit} (hrel : AliasScopeCtxRel aliases ΓD ΓR)
    (hwf : ∀ a ∈ aliases, TypeAlias.WF a)
    {C : LContext CoreLParams} {e : Expression.Expr} {t : LTy}
    (h : HasType C ΓR e t) :
    HasType C ΓD e t := by
  have hwfR : ∀ a ∈ ΓR.aliases, TypeAlias.WF a := by
    rw [hrel.r_aliases]
    exact hwf
  have hscopesR : ScopeRel (T := CoreLParams) ΓR.aliases ΓD.types ΓR.types := by
    rw [hrel.r_aliases]
    exact hrel.scopes
  have h' := HasType_ScopeRel C ΓR e t h ΓD.types hwfR hscopesR
  have hctx : { ΓR with types := ΓD.types } = ΓD := by
    cases ΓD
    cases ΓR
    congr
    exact hrel.r_aliases.trans hrel.d_aliases.symm
  rwa [hctx] at h'

/-- The relation holds for any context equivalent to the resolved one. -/
private theorem AliasScopeCtxRel.rightEquiv {aliases : List TypeAlias}
    {ΓD ΓR ΔR : TContext Unit} (hrel : AliasScopeCtxRel aliases ΓD ΓR)
    (heq : TContext.Equiv (T := CoreLParams) ΔR ΓR) :
    AliasScopeCtxRel aliases ΓD ΔR := by
  refine ⟨hrel.d_aliases, heq.2.trans hrel.r_aliases, ?_⟩
  intro x
  have hx := hrel.scopes x
  rw [heq.find? x]
  exact hx

/-- Inserting the same binding in both contexts preserves their alias-scope relation. -/
private theorem AliasScopeCtxRel.insert {aliases : List TypeAlias}
    {ΓD ΓR : TContext Unit} (hrel : AliasScopeCtxRel aliases ΓD ΓR)
    (x : CoreIdent) (t : LTy) :
    AliasScopeCtxRel aliases
      { ΓD with types := ΓD.types.insert x t }
      { ΓR with types := ΓR.types.insert x t } :=
  ⟨hrel.d_aliases, hrel.r_aliases, hrel.scopes.insert x t⟩

/-- A missing resolved binding is also missing from the related declared context. -/
private theorem AliasScopeCtxRel.find_none {aliases : List TypeAlias}
    {ΓD ΓR : TContext Unit} (hrel : AliasScopeCtxRel aliases ΓD ΓR)
    {x : CoreIdent} (h : ΓR.types.find? x = none) :
    ΓD.types.find? x = none := by
  rcases hrel.scopes x with heq | ⟨d, r, hd, hr, hae⟩
  · rw [heq, h]
  · rw [h] at hr
    contradiction

/-- A present resolved binding has a corresponding binding in the related declared context. -/
private theorem AliasScopeCtxRel.find_isSome {aliases : List TypeAlias}
    {ΓD ΓR : TContext Unit} (hrel : AliasScopeCtxRel aliases ΓD ΓR)
    {x : CoreIdent} (h : (ΓR.types.find? x).isSome) :
    (ΓD.types.find? x).isSome := by
  rcases hrel.scopes x with heq | ⟨d, r, hd, hr, hae⟩
  · rw [heq]
    exact h
  · rw [hd]
    simp

/-- A monomorphic resolved binding corresponds to an alias-equivalent monomorphic declared
    binding. -/
private theorem AliasScopeCtxRel.find_mono {aliases : List TypeAlias}
    {ΓD ΓR : TContext Unit} (hrel : AliasScopeCtxRel aliases ΓD ΓR)
    {x : CoreIdent} {r : LMonoTy}
    (h : ΓR.types.find? x = some (.forAll [] r)) :
    ∃ d, ΓD.types.find? x = some (.forAll [] d) ∧ AliasEquiv aliases d r := by
  rcases hrel.scopes x with heq | ⟨d, r', hd, hr, hae⟩
  · exact ⟨r, heq.trans h, AliasEquiv.refl⟩
  · have h_r_eq : r' = r := by
      have hs := hr.symm.trans h
      injection hs with hty
      injection hty
    subst h_r_eq
    exact ⟨d, hd, hae⟩

/-- Extended-command typing with written type variables transfers from a resolved context to its
    related declared context, keeping the relation on the outputs. -/
private theorem AliasScopeCtxRel.cmdExtΔ {aliases : List TypeAlias}
    {ΓD ΓR ΓR' : TContext Unit} (hrel : AliasScopeCtxRel aliases ΓD ΓR)
    (hwf : ∀ a ∈ aliases, TypeAlias.WF a)
    {C : LContext CoreLParams} {P : Program} {Δ Δ' : WrittenEnv} {c : Command}
    (h : CmdExtHasType C P Δ ΓR c ΓR' Δ') :
    ∃ ΓD', CmdExtHasType C P Δ ΓD c ΓD' Δ' ∧ AliasScopeCtxRel aliases ΓD' ΓR' := by
  have haliases : ΓD.aliases = ΓR.aliases := hrel.d_aliases.trans hrel.r_aliases.symm
  cases h with
  | call pname tyArgs args proc md σ _ hproc hcall hlhs hin hann hsc hout hΔ =>
    refine ⟨ΓD, .call _ ΓD pname tyArgs args proc md σ ΓD hproc hcall ?_ ?_
      (fun e he => writtenAnnotsOk_of_aliases_eq haliases (hann e he)) hsc ?_
      (TContext.Equiv.refl _), hrel.rightEquiv hΔ⟩
    · intro v hv
      exact hrel.find_isSome (hlhs v hv)
    · intro i hi hj
      obtain ⟨r, hae, hm⟩ := hin i hi hj
      have haeA : AliasEquiv aliases r
          (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) proc.header.inputs.values[i]) := by
        change AliasEquiv _ _ _ at hae
        simpa only [hrel.r_aliases] using hae
      revert hm
      split
      · intro hm
        obtain ⟨d, hfindD, hdr⟩ := hrel.find_mono hm
        refine ⟨d, ?_, hfindD⟩
        change AliasEquiv _ _ _
        simpa only [hrel.d_aliases] using AliasEquiv.trans hdr haeA
      · intro hm
        refine ⟨r, ?_, hrel.expr hwf hm⟩
        change AliasEquiv _ _ _
        simpa only [hrel.d_aliases] using haeA
    · intro i hi hj
      obtain ⟨r, hae, hfind⟩ := hout i hi hj
      obtain ⟨d, hfindD, hdr⟩ := hrel.find_mono hfind
      have haeA : AliasEquiv aliases r
          (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) proc.header.outputs.values[i]) := by
        change AliasEquiv _ _ _ at hae
        simpa only [hrel.r_aliases] using hae
      refine ⟨d, ?_, hfindD⟩
      change AliasEquiv _ _ _
      simpa only [hrel.d_aliases] using AliasEquiv.trans hdr haeA
  | cmd =>
    rename_i cc hcc
    cases hcc with
    | init_det x _ e mty _ _ _ _ hfresh hfvar hxty hdecl hwk he hann hsc hΓ =>
      obtain ⟨hinst', hvalid'⟩ := hdecl
      rw [← haliases] at hinst' hvalid'
      exact ⟨{ ΓD with types := ΓD.types.insert x (.forAll [] mty) },
        .cmd _ _ _ _ _ (.init_det _ _ _ _ _ _ _ _ _ _ (hrel.find_none hfresh) hfvar hxty
          ⟨hinst', hvalid'⟩ hwk (hrel.expr hwf he) (writtenAnnotsOk_of_aliases_eq haliases hann) hsc
          (TContext.Equiv.refl _)),
        (hrel.insert x (.forAll [] mty)).rightEquiv hΓ⟩
    | init_nondet x _ mty _ _ _ _ hfresh hxty hdecl hwk hΓ =>
      obtain ⟨hinst', hvalid'⟩ := hdecl
      rw [← haliases] at hinst' hvalid'
      exact ⟨{ ΓD with types := ΓD.types.insert x (.forAll [] mty) },
        .cmd _ _ _ _ _ (.init_nondet _ _ _ _ _ _ _ _ _ (hrel.find_none hfresh) hxty
          ⟨hinst', hvalid'⟩ hwk (TContext.Equiv.refl _)),
        (hrel.insert x (.forAll [] mty)).rightEquiv hΓ⟩
    | set_det x r e md _ hfind he hann hsc hΓ =>
      obtain ⟨d, hfindD, hae⟩ := hrel.find_mono hfind
      have haeD : AliasEquiv ΓD.aliases d r := by
        simpa only [hrel.d_aliases] using hae
      have heD := HasType.talias (C := C) ΓD _ r d (AliasEquiv.symm haeD) (hrel.expr hwf he)
      exact ⟨ΓD, .cmd _ _ _ _ _ (.set_det _ ΓD x d e md ΓD hfindD heD
        (writtenAnnotsOk_of_aliases_eq haliases hann) hsc (TContext.Equiv.refl _)),
        hrel.rightEquiv hΓ⟩
    | set_nondet x r md _ hfind hΓ =>
      obtain ⟨d, hfindD, hae⟩ := hrel.find_mono hfind
      exact ⟨ΓD, .cmd _ _ _ _ _ (.set_nondet _ ΓD x d md ΓD hfindD (TContext.Equiv.refl _)),
        hrel.rightEquiv hΓ⟩
    | assert l e md _ he hann hsc hΓ =>
      exact ⟨ΓD, .cmd _ _ _ _ _ (.assert _ ΓD l e md ΓD (hrel.expr hwf he)
        (writtenAnnotsOk_of_aliases_eq haliases hann) hsc (TContext.Equiv.refl _)),
        hrel.rightEquiv hΓ⟩
    | assume l e md _ he hann hsc hΓ =>
      exact ⟨ΓD, .cmd _ _ _ _ _ (.assume _ ΓD l e md ΓD (hrel.expr hwf he)
        (writtenAnnotsOk_of_aliases_eq haliases hann) hsc (TContext.Equiv.refl _)),
        hrel.rightEquiv hΓ⟩
    | cover l e md _ he hann hsc hΓ =>
      exact ⟨ΓD, .cmd _ _ _ _ _ (.cover _ ΓD l e md ΓD (hrel.expr hwf he)
        (writtenAnnotsOk_of_aliases_eq haliases hann) hsc (TContext.Equiv.refl _)),
        hrel.rightEquiv hΓ⟩

mutual

/-- Statement typing with written type variables transfers from a resolved context to its
    related declared context, keeping the relation on the outputs. -/
private theorem AliasScopeCtxRel.statementΔ {aliases : List TypeAlias}
    {ΓD ΓR ΓR' : TContext Unit} (hrel : AliasScopeCtxRel aliases ΓD ΓR)
    (hwf : ∀ a ∈ aliases, TypeAlias.WF a)
    {C C' : LContext CoreLParams} {Δ Δ' : WrittenEnv}
    {P : Program} {L : List String} {s : Statement}
    (h : StatementHasType P C ΓR Δ L s C' ΓR' Δ') :
    ∃ ΓD', StatementHasType P C ΓD Δ L s C' ΓD' Δ' ∧
      AliasScopeCtxRel aliases ΓD' ΓR' := by
  have haliases : ΓD.aliases = ΓR.aliases := hrel.d_aliases.trans hrel.r_aliases.symm
  cases h with
  | cmd _ _ _ _ _ _ c _ hc hΓ =>
      obtain ⟨ΓD', hcD, hrel'⟩ := hrel.cmdExtΔ hwf hc
      exact ⟨ΓD', .cmd _ _ _ _ _ _ _ _ hcD (TContext.Equiv.refl _), hrel'.rightEquiv hΓ⟩
  | block _ _ _ _ _ _ _ _ _ _ _ hlabel hbody hΓ =>
      obtain ⟨ΓDb, hbodyD, -⟩ := hrel.statementsΔ hwf hbody
      exact ⟨ΓD, .block _ _ _ _ _ _ _ _ _ _ ΓD hlabel hbodyD (TContext.Equiv.refl _),
        hrel.rightEquiv hΓ⟩
  | ite_det _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcond hcondAnn hcondScope ht he hΓ =>
      obtain ⟨ΓDt, htD, -⟩ := hrel.statementsΔ hwf ht
      obtain ⟨ΓDe, heD, -⟩ := hrel.statementsΔ hwf he
      exact ⟨ΓD, .ite_det _ _ _ _ _ _ _ _ _ _ _ _ _ _ ΓD (hrel.expr hwf hcond)
        (writtenAnnotsOk_of_aliases_eq haliases hcondAnn) hcondScope htD heD
        (TContext.Equiv.refl _),
        hrel.rightEquiv hΓ⟩
  | ite_nondet _ _ _ _ _ _ _ _ _ _ _ _ _ _ ht he hΓ =>
      obtain ⟨ΓDt, htD, -⟩ := hrel.statementsΔ hwf ht
      obtain ⟨ΓDe, heD, -⟩ := hrel.statementsΔ hwf he
      exact ⟨ΓD, .ite_nondet _ _ _ _ _ _ _ _ _ _ _ _ _ ΓD htD heD (TContext.Equiv.refl _),
        hrel.rightEquiv hΓ⟩
  | loop _ _ _ _ _ _ _ _ _ _ _ _ _ hg hgAnn hm hmAnn hi hiAnn hgS hmS hiS hb hΓ =>
      obtain ⟨ΓDb, hbD, -⟩ := hrel.statementsΔ hwf hb
      refine ⟨ΓD, .loop _ _ _ _ _ _ _ _ _ _ _ _ ΓD ?_ ?_ ?_ ?_ ?_ ?_ hgS hmS hiS hbD
        (TContext.Equiv.refl _), hrel.rightEquiv hΓ⟩
      · intro g hguard
        exact hrel.expr hwf (hg g hguard)
      · intro g hguard
        exact writtenAnnotsOk_of_aliases_eq haliases (hgAnn g hguard)
      · intro m hmeasure
        exact hrel.expr hwf (hm m hmeasure)
      · intro m hmeasure
        exact writtenAnnotsOk_of_aliases_eq haliases (hmAnn m hmeasure)
      · intro p hp
        exact hrel.expr hwf (hi p hp)
      · intro p hp
        exact writtenAnnotsOk_of_aliases_eq haliases (hiAnn p hp)
  | exit _ _ _ _ _ _ _ hlabel hΓ =>
      exact ⟨ΓD, .exit _ _ _ _ _ _ ΓD hlabel (TContext.Equiv.refl _), hrel.rightEquiv hΓ⟩
  | typeDecl _ _ _ _ _ _ _ _ hprog hnotAlias hadd hΓ =>
      exact ⟨ΓD, .typeDecl _ _ _ _ _ _ _ ΓD hprog
        (nameNotAlias_of_aliases_eq haliases hnotAlias) hadd (TContext.Equiv.refl _),
        hrel.rightEquiv hΓ⟩

/-- Statement-list typing with written type variables transfers from a resolved context to its
    related declared context, keeping the relation on the outputs. -/
private theorem AliasScopeCtxRel.statementsΔ {aliases : List TypeAlias}
    {ΓD ΓR ΓR' : TContext Unit} (hrel : AliasScopeCtxRel aliases ΓD ΓR)
    (hwf : ∀ a ∈ aliases, TypeAlias.WF a)
    {C C' : LContext CoreLParams} {Δ Δ' : WrittenEnv}
    {P : Program} {L : List String} {ss : List Statement}
    (h : StatementsHasType P C ΓR Δ L ss C' ΓR' Δ') :
    ∃ ΓD', StatementsHasType P C ΓD Δ L ss C' ΓD' Δ' ∧
      AliasScopeCtxRel aliases ΓD' ΓR' := by
  cases h with
  | nil _ _ _ _ _ hΓ =>
      exact ⟨ΓD, .nil _ _ _ _ ΓD (TContext.Equiv.refl _), hrel.rightEquiv hΓ⟩
  | cons _ _ _ _ _ _ _ _ _ _ _ _ hs hss =>
      obtain ⟨ΓDm, hsD, hrelm⟩ := hrel.statementΔ hwf hs
      obtain ⟨ΓD', hssD, hrel'⟩ := hrelm.statementsΔ hwf hss
      exact ⟨ΓD', .cons _ _ _ _ _ _ _ _ _ _ _ _ hsD hssD, hrel'⟩

end

/-- With well-formed aliases, statement-list typing with written type variables survives
    replacing the newest scope by one with the same names and alias-equivalent monotypes. -/
theorem StatementsHasTypeΔ_pushScope_aliasEquiv {P : Program}
    (Cc : LContext CoreLParams) (Γ : TContext Unit) (Δ : WrittenEnv)
    (sigD sigR : @LMonoTySignature Unit) (L : List String) (ss : List Statement)
    (Cout : LContext CoreLParams) (Γout : TContext Unit) (Δout : WrittenEnv)
    (h_aliasesWF : TContext.AliasesWF Γ)
    (h_keys : sigD.keys = sigR.keys)
    (h_vals : AliasEquivList Γ.aliases sigD.values sigR.values)
    (h : StatementsHasType P Cc
      { Γ with types := Γ.types.push (Strata.Util.HMap.ofList
          (sigR.map (fun q => (q.1, LTy.forAll [] q.2)))) } Δ L ss Cout Γout Δout) :
    ∃ Γout', StatementsHasType P Cc
      { Γ with types := Γ.types.push (Strata.Util.HMap.ofList
          (sigD.map (fun q => (q.1, LTy.forAll [] q.2)))) } Δ L ss Cout Γout' Δout := by
  let ΓD := { Γ with types := Γ.types.push (Strata.Util.HMap.ofList
    (sigD.map (fun (q : CoreIdent × LMonoTy) => (q.1, LTy.forAll [] q.2)))) }
  let ΓR := { Γ with types := Γ.types.push (Strata.Util.HMap.ofList
    (sigR.map (fun (q : CoreIdent × LMonoTy) => (q.1, LTy.forAll [] q.2)))) }
  have hrel : AliasScopeCtxRel Γ.aliases ΓD ΓR :=
    ⟨rfl, rfl, scopeRel_push (T := CoreLParams) Γ sigD sigR h_keys h_vals⟩
  obtain ⟨ΓoutD, hD, -⟩ := hrel.statementsΔ h_aliasesWF h
  exact ⟨ΓoutD, hD⟩

end AliasScopeTransport

/-! ## Statements use only types registered where they occur -/

section TysDeclaredWhereStored

/-- A statement's own annotations are read the same way against two registered-type tables that
    record the same arity for every name. -/
private theorem ownTysDeclared_congr (s : Statement) {ks1 ks2 : Lambda.KnownTypes}
    (h : TableAgree ks1 ks2) :
    Statement.ownTysDeclared ks1 s = Statement.ownTysDeclared ks2 s := by
  have hp : (fun mty => LMonoTy.knownInstance mty ks1)
      = (fun mty => LMonoTy.knownInstance mty ks2) :=
    funext (fun mty => knownInstance_congr mty h)
  unfold Statement.ownTysDeclared
  rw [hp]

/-- Two successful readings that return tables recording the same arity for every name agree in
    success and in what they return. -/
private theorem some_tableAgree_congr {ks1 ks2 : Lambda.KnownTypes} (h : TableAgree ks1 ks2) :
    (some ks1).isSome = (some ks2).isSome ∧
      ∀ o1 o2, some ks1 = some o1 → some ks2 = some o2 → TableAgree o1 o2 := by
  refine ⟨rfl, ?_⟩
  intro o1 o2 h1 h2
  cases h1
  cases h2
  exact h

/-- Discarding a first reading that succeeds on both sides or neither keeps the agreement of the
    second reading after it. -/
private theorem bind_discard_tableAgree_congr {a1 a2 r1 r2 : Option Lambda.KnownTypes}
    (ha : a1.isSome = a2.isSome)
    (hr : r1.isSome = r2.isSome ∧ ∀ o1 o2, r1 = some o1 → r2 = some o2 → TableAgree o1 o2) :
    (a1.bind fun _ => r1).isSome = (a2.bind fun _ => r2).isSome ∧
      ∀ o1 o2, (a1.bind fun _ => r1) = some o1 → (a2.bind fun _ => r2) = some o2 →
        TableAgree o1 o2 := by
  cases a1 with
  | none =>
    cases a2 with
    | none => exact ⟨rfl, fun _ _ h1 => absurd h1 (by simp)⟩
    | some _ => simp at ha
  | some _ =>
    cases a2 with
    | none => simp at ha
    | some _ => exact hr

mutual
/-- Reading a statement against two tables that agree on every arity succeeds on both or neither,
    and the tables it reports agree again. -/
private theorem tysDeclaredStmt_congr (s : Statement) {ks1 ks2 : Lambda.KnownTypes}
    (h : TableAgree ks1 ks2) :
    (Statement.tysDeclaredStmt ks1 s).isSome = (Statement.tysDeclaredStmt ks2 s).isSome ∧
      ∀ o1 o2, Statement.tysDeclaredStmt ks1 s = some o1 →
        Statement.tysDeclaredStmt ks2 s = some o2 → TableAgree o1 o2 := by
  rw [Statement.tysDeclaredStmt_eq, Statement.tysDeclaredStmt_eq,
    ownTysDeclared_congr s h]
  cases hown : Statement.ownTysDeclared ks2 s with
  | false => simp
  | true =>
    simp only [Bool.false_eq_true, reduceIte, Bool.not_true]
    match s with
    | .typeDecl tc md => exact some_tableAgree_congr (h.insert tc.name tc.numargs)
    | .block label bss md | .loop _ _ _ bss md =>
      exact bind_discard_tableAgree_congr (tysDeclaredStmts_congr bss h).1
        (some_tableAgree_congr h)
    | .ite cond tss ess md =>
      exact bind_discard_tableAgree_congr (tysDeclaredStmts_congr tss h).1
        (bind_discard_tableAgree_congr (tysDeclaredStmts_congr ess h).1
          (some_tableAgree_congr h))
    | .cmd _ | .exit _ _ => exact some_tableAgree_congr h

/-- Reading a statement list against two tables that agree on every arity succeeds on both or
    neither, and the tables it reports agree again. -/
private theorem tysDeclaredStmts_congr (ss : List Statement) {ks1 ks2 : Lambda.KnownTypes}
    (h : TableAgree ks1 ks2) :
    (Statement.tysDeclaredStmts ks1 ss).isSome = (Statement.tysDeclaredStmts ks2 ss).isSome ∧
      ∀ o1 o2, Statement.tysDeclaredStmts ks1 ss = some o1 →
        Statement.tysDeclaredStmts ks2 ss = some o2 → TableAgree o1 o2 := by
  match ss with
  | [] =>
    refine ⟨rfl, fun o1 o2 h1 h2 => ?_⟩
    simp only [Statement.tysDeclaredStmts_nil, Option.some.injEq] at h1 h2
    subst h1; subst h2; exact h
  | s :: rest =>
    obtain ⟨hs, hsa⟩ := tysDeclaredStmt_congr s h
    have hsn := Option.isSome_eq_isSome.mp hs
    simp only [Statement.tysDeclaredStmts_cons, bind, Option.bind]
    cases h1 : Statement.tysDeclaredStmt ks1 s with
    | none =>
      rw [hsn.mp h1]
      exact ⟨rfl, fun o1 o2 hc => absurd hc (by simp)⟩
    | some k1 =>
      have hne : Statement.tysDeclaredStmt ks2 s ≠ none := by
        intro hc; rw [hsn.mpr hc] at h1; exact absurd h1 (by simp)
      cases h2 : Statement.tysDeclaredStmt ks2 s with
      | none => exact absurd h2 hne
      | some k2 => exact tysDeclaredStmts_congr rest (hsa k1 k2 h1 h2)
end

/-! ### Reading the condition one statement at a time -/

/-- Reading a list starting with `s` succeeds only if `s`'s own annotations are accepted where `s`
    sits and the rest of the list is accepted against the registrations `s` reports. -/
private theorem tysDeclaredStmts_cons_inv (ks : Lambda.KnownTypes) (s : Statement)
    (rest : List Statement)
    (h : (Statement.tysDeclaredStmts ks (s :: rest)).isSome = true) :
    Statement.ownTysDeclared ks s = true ∧
      ∃ ks', Statement.tysDeclaredStmt ks s = some ks'
        ∧ (Statement.tysDeclaredStmts ks' rest).isSome = true := by
  simp only [Statement.tysDeclaredStmts_cons, bind, Option.bind] at h
  elim_err h with ks' hs
  refine ⟨?_, ks', hs, h⟩
  rw [Statement.tysDeclaredStmt_eq] at hs
  cases hown : Statement.ownTysDeclared ks s with
  | true => rfl
  | false => rw [hown] at hs; exact absurd hs (by simp)

/-- An `exit` registers nothing. -/
private theorem tysDeclaredStmt_exit (ks : Lambda.KnownTypes) (l : String)
    (md : MetaData Expression) :
    Statement.tysDeclaredStmt ks (Stmt.exit l md) = some ks := by
  rw [Statement.tysDeclaredStmt_eq]
  rfl

/-- A reading that runs a first reading, discards its result, and continues with a second succeeds
    only when the first succeeds, and then returns what the second returns. -/
private theorem bind_discard_eq_some {a r : Option Lambda.KnownTypes} {o : Lambda.KnownTypes}
    (h : (a.bind fun _ => r) = some o) : a.isSome = true ∧ r = some o := by
  cases a with
  | none => exact absurd h (by simp)
  | some _ => exact ⟨rfl, h⟩

/-- A block reports the table it sits at, and its body is read against a copy of it. -/
private theorem tysDeclaredStmt_block (ks ks' : Lambda.KnownTypes) (label : String)
    (bss : List Statement)
    (md : MetaData Expression)
    (h : Statement.tysDeclaredStmt ks (Stmt.block label bss md) = some ks') :
    ks' = ks ∧ (Statement.tysDeclaredStmts ks bss).isSome = true := by
  rw [Statement.tysDeclaredStmt_eq] at h
  elim_err h
  obtain ⟨hb, h⟩ := bind_discard_eq_some h
  exact ⟨(Option.some.inj h).symm, hb⟩

/-- A conditional reports the table it sits at, and each branch is read against a copy of it. -/
private theorem tysDeclaredStmt_ite (ks ks' : Lambda.KnownTypes) (cond : ExprOrNondet Expression)
    (tss ess : List Statement) (md : MetaData Expression)
    (h : Statement.tysDeclaredStmt ks (Stmt.ite cond tss ess md) = some ks') :
    ks' = ks ∧ (Statement.tysDeclaredStmts ks tss).isSome = true
      ∧ (Statement.tysDeclaredStmts ks ess).isSome = true := by
  rw [Statement.tysDeclaredStmt_eq] at h
  elim_err h
  obtain ⟨ht, h⟩ := bind_discard_eq_some h
  obtain ⟨he, h⟩ := bind_discard_eq_some h
  exact ⟨(Option.some.inj h).symm, ht, he⟩

/-- A loop reports the table it sits at, and its body is read against a copy of it. -/
private theorem tysDeclaredStmt_loop (ks ks' : Lambda.KnownTypes) (g : ExprOrNondet Expression)
    (m : Option Expression.Expr) (i : List (String × Expression.Expr)) (bss : List Statement)
    (md : MetaData Expression)
    (h : Statement.tysDeclaredStmt ks (Stmt.loop g m i bss md) = some ks') :
    ks' = ks ∧ (Statement.tysDeclaredStmts ks bss).isSome = true := by
  rw [Statement.tysDeclaredStmt_eq] at h
  elim_err h
  obtain ⟨hb, h⟩ := bind_discard_eq_some h
  exact ⟨(Option.some.inj h).symm, hb⟩

/-! ### A `type` declaration registers its name for the statements after it -/

/-- If a list starting with a `type` declaration passes the registered-type check and registering
    that type succeeds, the rest of the list passes against the resulting table. -/
private theorem tysDeclaredStmts_tail_of_addKnownType
    (C Cnew : Expression.TyContext) (tc : TypeConstructor) (md : MetaData Expression)
    (rest : List Statement) (msg : Strata.Message)
    (hchk : C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } msg = .ok Cnew)
    (h : (Statement.tysDeclaredStmts C.knownTypes
      (Stmt.typeDecl tc md :: rest)).isSome = true) :
    (Statement.tysDeclaredStmts Cnew.knownTypes rest).isSome = true := by
  obtain ⟨hown, ks', hs, htail⟩ := tysDeclaredStmts_cons_inv C.knownTypes _ rest h
  rw [Statement.tysDeclaredStmt_eq, hown] at hs
  simp only [Bool.not_true, Bool.false_eq_true, reduceIte, Option.some.injEq] at hs
  subst hs
  rw [(tysDeclaredStmts_congr rest
    (addKnownTypeWithError_tableAgree C Cnew
      { name := tc.name, metadata := tc.numargs } msg hchk)).1]
  exact htail

/-! ### Checked statements pass the registered-type check -/

/-- Statement checking emits a list passing the registered-type check against the input's
    registered types: the auxiliary walk's output with the final substitution applied. -/
private theorem typeCheck_sweep
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (P : Program)
    (op : Option Procedure) (ss ss' : List Statement)
    (h : Statement.typeCheck C Env P op ss = .ok (ss', Env')) :
    (Statement.tysDeclaredStmts C.knownTypes ss').isSome = true
      ∧ ∃ ssA EnvA CA,
        Statement.typeCheckAux C Env P op ss = .ok (ssA, EnvA, CA)
        ∧ ss' = ssA.map (Statement.Statement.subst
          (Statement.finalSubstInfo Env.genEnv.genState EnvA).subst) := by
  obtain ⟨ssA, EnvA, CA, hr, rfl, -, hsweep⟩ :=
    Statement.typeCheck_ok_inv C Env Env' P op ss ss' h
  refine ⟨hsweep, ssA, EnvA, CA, hr, ?_⟩
  rw [Statement_subst_go_eq]
  simp only [List.reverse_nil, List.nil_append]

/-- When `Statement.typeCheck` succeeds, the statements its auxiliary walk returns pass the
    annotation check `Statement.tysDeclaredStmts` (each statement's annotations use registered
    types) after applying the check's final substitution. -/
theorem typeCheck_sweepAt
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (P : Program)
    (op : Option Procedure) (ss ss' : List Statement)
    (h : Statement.typeCheck C Env P op ss = .ok (ss', Env')) :
    ∀ ssA EnvA CA,
      Statement.typeCheckAux C Env P op ss = .ok (ssA, EnvA, CA) →
      SweepAt C (Statement.finalSubstInfo Env.genEnv.genState EnvA).subst ssA := by
  intro ssA EnvA CA haux
  obtain ⟨hsweep, ssA', EnvA', CA', hr, hmap⟩ :=
    typeCheck_sweep C Env Env' P op ss ss' h
  rw [haux] at hr
  simp only [Except.ok.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl, rfl⟩ := hr
  apply (sweepAt_iff_tysDeclaredStmts C
    (Statement.finalSubstInfo Env.genEnv.genState EnvA).subst ssA).mpr
  rw [← hmap]
  exact hsweep

/-! ## The walk's output and the positional condition at a cons -/

/-- Reading the condition at a cons: the head's own annotations are accepted where the head sits,
    and what follows is accepted against the registrations the head reports. -/
private theorem sweepAt_cons_inv (C : LContext CoreLParams) (S : Subst) (s : Statement)
    (rest : List Statement) (h : SweepAt C S (s :: rest)) :
    Statement.ownTysDeclared C.knownTypes (Statement.Statement.subst S s) = true ∧
      ∃ ks', Statement.tysDeclaredStmt C.knownTypes (Statement.Statement.subst S s) = some ks'
        ∧ SweepFrom S ks' rest := by
  refine ⟨h.head_ownTysDeclared C S s rest, ?_⟩
  cases h with
  | cons hhead htail => exact ⟨_, hhead, htail⟩

/-- A head statement that registers nothing leaves what follows accepted at the same context. -/
private theorem sweepAt_tail_of_keeps (C : LContext CoreLParams) (S : Subst) (s : Statement)
    (rest : List Statement)
    (hkeep : Statement.tysDeclaredStmt C.knownTypes (Statement.Statement.subst S s)
      = some C.knownTypes)
    (h : SweepAt C S (s :: rest)) : SweepAt C S rest := by
  cases h with
  | cons hhead htail =>
    rw [hkeep, Option.some.injEq] at hhead
    subst hhead
    exact htail

/-- A property of `out` transfers to any `ss_proc` with `out = [].reverse ++ ss_proc`. -/
private theorem nil_acc_splits {Pr : List Statement → Prop} {out : List Statement} (h : Pr out) :
    ∀ ss_proc, out = ([] : List Statement).reverse ++ ss_proc → Pr ss_proc := by
  intro ss_proc hp
  simp only [List.reverse_nil, List.nil_append] at hp
  rw [← hp]
  exact h

/-- The positional condition on a list headed by a command gives the command's stored types as
    registered and the condition for the statements after it. -/
private theorem SweepAt.cmd_peel (C : LContext CoreLParams) (S : Subst) (c : Command)
    (rest : List Statement) (h : SweepAt C S (Stmt.cmd c :: rest)) :
    allCmdTys (fun mty => LMonoTy.knownInstance mty C.knownTypes)
        (Statement.Command.subst S c) = true ∧ SweepAt C S rest := by
  have hown := (sweepAt_cons_inv C S (Stmt.cmd c) rest h).1
  have hkeeps : Statement.tysDeclaredStmt C.knownTypes (Statement.Statement.subst S (Stmt.cmd c))
      = some C.knownTypes := by
    rw [Statement.tysDeclaredStmt_eq, hown]
    rfl
  have hcmd : allCmdTys (fun mty => LMonoTy.knownInstance mty C.knownTypes)
      (Statement.Command.subst S c) = true := by
    rw [Statement.allCmdTys_eq_all_cmdAnnotTys]
    simpa only [Statement.Statement.subst, Statement.ownTysDeclared,
      Statement.stmtOwnAnnotTys, stmtOwnCollect, cmdAnnotTys] using hown
  exact ⟨hcmd, sweepAt_tail_of_keeps C S (Stmt.cmd c) rest hkeeps h⟩

/-- The positional condition on a list headed by a statement that keeps the registered types and
    reads a nested body against them holds for that body and for the statements after it. -/
private theorem SweepAt.body_peel (C : LContext CoreLParams) (S : Subst) (s : Statement)
    (bss rest : List Statement)
    (hbody : ∀ ks', Statement.tysDeclaredStmt C.knownTypes (Statement.Statement.subst S s)
        = some ks' →
      ks' = C.knownTypes ∧
        (Statement.tysDeclaredStmts C.knownTypes
          (bss.map (Statement.Statement.subst S))).isSome = true)
    (h : SweepAt C S (s :: rest)) : SweepAt C S bss ∧ SweepAt C S rest := by
  obtain ⟨-, ks', hstep, -⟩ := sweepAt_cons_inv C S s rest h
  obtain ⟨hks, hnested⟩ := hbody ks' hstep
  subst hks
  exact ⟨(sweepAt_iff_tysDeclaredStmts C S bss).mpr hnested,
    sweepAt_tail_of_keeps C S s rest hstep h⟩

/-- The positional condition on a list headed by a block holds for the block's body and for the
    statements after it. -/
private theorem SweepAt.block_peel (C : LContext CoreLParams) (S : Subst) (label : String)
    (bss : List Statement) (md : MetaData Expression) (rest : List Statement)
    (h : SweepAt C S (Stmt.block label bss md :: rest)) :
    SweepAt C S bss ∧ SweepAt C S rest := by
  refine SweepAt.body_peel C S _ bss rest ?_ h
  intro ks' hstep
  simp only [Statement.Statement.subst, Statement_subst_go_eq, List.reverse_nil,
    List.nil_append] at hstep
  exact tysDeclaredStmt_block C.knownTypes ks' label _ md hstep

/-- The positional condition on a list headed by a conditional holds for both branches and for
    the statements after it. -/
private theorem SweepAt.ite_peel (C : LContext CoreLParams) (S : Subst)
    (cond : ExprOrNondet Expression) (tss ess : List Statement) (md : MetaData Expression)
    (rest : List Statement) (h : SweepAt C S (Stmt.ite cond tss ess md :: rest)) :
    SweepAt C S tss ∧ SweepAt C S ess ∧ SweepAt C S rest := by
  obtain ⟨-, ks', hstep, -⟩ := sweepAt_cons_inv C S _ rest h
  have hstep2 := hstep
  simp only [Statement.Statement.subst, Statement_subst_go_eq,
    List.reverse_nil, List.nil_append] at hstep2
  obtain ⟨hks, hntss, hness⟩ := tysDeclaredStmt_ite C.knownTypes ks' _ _ _ md hstep2
  subst hks
  exact ⟨(sweepAt_iff_tysDeclaredStmts C S tss).mpr hntss,
    (sweepAt_iff_tysDeclaredStmts C S ess).mpr hness, sweepAt_tail_of_keeps C S _ rest hstep h⟩

/-- The positional condition on a list headed by a loop holds for the loop body and for the
    statements after it. -/
private theorem SweepAt.loop_peel (C : LContext CoreLParams) (S : Subst)
    (guard : ExprOrNondet Expression) (measure : Option Expression.Expr)
    (invariant : List (String × Expression.Expr)) (bss : List Statement)
    (md : MetaData Expression) (rest : List Statement)
    (h : SweepAt C S (Stmt.loop guard measure invariant bss md :: rest)) :
    SweepAt C S bss ∧ SweepAt C S rest := by
  refine SweepAt.body_peel C S _ bss rest ?_ h
  intro ks' hstep
  simp only [Statement.Statement.subst, Statement_subst_go_eq, List.reverse_nil,
    List.nil_append] at hstep
  exact tysDeclaredStmt_loop C.knownTypes ks' _ _ _ _ md hstep

/-- When every type annotating the expressions `es` is a registered instance, so is every
    annotation in each member of `es`. -/
private theorem allExprTys_known_of_flatMap {ks : Lambda.KnownTypes} {es : List Expression.Expr}
    (h : (es.flatMap exprAnnotTys).all (LMonoTy.knownInstance · ks) = true) :
    ∀ e ∈ es, allExprTys (fun m => LMonoTy.knownInstance m ks) e = true := by
  intro e he
  rw [allExprTys_eq_all_exprAnnotTys]
  rw [List.all_flatMap, List.all_eq_true] at h
  exact h e he

/-- A conditional whose positional sweep holds emits a condition whose binder annotations,
    under the substitution, are registered types. -/
private theorem SweepAt.ite_condKnown (C : LContext CoreLParams) (S : Subst)
    (c : Expression.Expr) (tss ess : List Statement) (md : MetaData Expression)
    (rest : List Statement) (h : SweepAt C S (Stmt.ite (.det c) tss ess md :: rest)) :
    BinderAnnotsKnown C (LExpr.applyTypeSubst c S) := by
  have hown := SweepAt.head_ownTysDeclared C S _ rest h
  simp only [Statement.Statement.subst, ExprOrNondet.map, Statement.ownTysDeclared,
    Statement.stmtOwnAnnotTys, stmtOwnCollect] at hown
  exact binderAnnotsKnown_of_allExprTys C _
    (allExprTys_known_of_flatMap hown _ (List.mem_singleton_self _))

/-- A loop whose positional sweep holds emits a substituted guard, measure and invariants whose
    binder annotations are registered types. -/
private theorem SweepAt.loop_known (C : LContext CoreLParams) (S : Subst)
    (guard : ExprOrNondet Expression) (measure : Option Expression.Expr)
    (invariant : List (String × Expression.Expr)) (bss : List Statement)
    (md : MetaData Expression) (rest : List Statement)
    (h : SweepAt C S (Stmt.loop guard measure invariant bss md :: rest)) :
    (∀ g, (guard.map (fun e : Expression.Expr => LExpr.applyTypeSubst e S) :
        ExprOrNondet Expression) = .det g → BinderAnnotsKnown C g) ∧
      (∀ m, measure.map (·.applyTypeSubst S) = some m → BinderAnnotsKnown C m) ∧
      ∀ q ∈ invariant.map (fun p => (p.1, p.2.applyTypeSubst S)), BinderAnnotsKnown C q.2 := by
  have hown := SweepAt.head_ownTysDeclared C S _ rest h
  simp only [Statement.Statement.subst, Statement.ownTysDeclared,
    Statement.stmtOwnAnnotTys, stmtOwnCollect] at hown
  have hknown := allExprTys_known_of_flatMap hown
  refine ⟨fun g hgd => ?_, fun m hmd => ?_, fun q hq => ?_⟩
  · have hmem : g ∈ ExprOrNondet.toList
        (guard.map (fun e : Expression.Expr => LExpr.applyTypeSubst e S)) :=
      hgd ▸ List.mem_singleton_self g
    exact binderAnnotsKnown_of_allExprTys C _
      (hknown g (List.mem_append_left _ (List.mem_append_left _ hmem)))
  · have hmem : m ∈ (measure.map (·.applyTypeSubst S)).toList := hmd ▸ List.mem_singleton_self m
    exact binderAnnotsKnown_of_allExprTys C _
      (hknown m (List.mem_append_left _ (List.mem_append_right _ hmem)))
  · exact binderAnnotsKnown_of_allExprTys C _
      (hknown q.2 (List.mem_append_right _ (List.mem_map_of_mem hq)))

/-- The positional condition on a list headed by a local type declaration holds for the
    statements after it, read against the context in which the type is registered. -/
private theorem SweepAt.typeDecl_peel (C Cnew : LContext CoreLParams) (S : Subst)
    (tc : TypeConstructor) (md : MetaData Expression) (rest : List Statement)
    (msg : Strata.Message)
    (hkt : C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } msg = .ok Cnew)
    (h : SweepAt C S (Stmt.typeDecl tc md :: rest)) : SweepAt Cnew S rest :=
  (sweepAt_iff_tysDeclaredStmts Cnew S rest).mpr
    (tysDeclaredStmts_tail_of_addKnownType C Cnew tc md (rest.map (Statement.Statement.subst S))
      msg hkt ((sweepAt_iff_tysDeclaredStmts C S _).mp h))

end TysDeclaredWhereStored

/-! ## Substitution facts for output typing -/

section SubstStability

open Strata.Util (HMaps)

/-! ### Expression-level substitution facts -/

/-- Applying a substitution to an expression with an annotated type in the empty de Bruijn
    context gives an expression whose annotated type is the substituted type. -/
private theorem hasTypeA_applyTypeSubst (S : Subst) {e : Expression.Expr} {mty : LMonoTy}
    (h : Lambda.LExpr.HasTypeA (T := CoreLParams) [] e mty) :
    Lambda.LExpr.HasTypeA (T := CoreLParams) []
      (LExpr.applyTypeSubst e S) (LMonoTy.subst S mty) := by
  simpa using Lambda.applyTypeSubst_typeCheck (T := CoreLParams) S h

/-! ### `call` arguments under substitution -/

/-- Substituting call arguments preserves their output-variable list. -/
private theorem getLhs_map_subst (S : Subst) (args : List (CallArg Expression)) :
    CallArg.getLhs (args.map (Statement.CallArg.subst S)) = CallArg.getLhs args := by
  simp only [CallArg.getLhs, List.filterMap_map]
  congr 1
  funext a
  cases a <;> rfl

/-- Substituting call arguments maps substitution over their input expressions. -/
private theorem getInputExprs_map_subst (S : Subst) (args : List (CallArg Expression)) :
    CallArg.getInputExprs (args.map (Statement.CallArg.subst S))
      = (CallArg.getInputExprs args).map (fun e => LExpr.applyTypeSubst e S) := by
  simp only [CallArg.getInputExprs, Calls.getInputExprs, List.filterMap_map, List.map_filterMap]
  congr 1
  funext a
  cases a with
  | inArg e => rfl
  | inoutArg id =>
    show (some (LExpr.fvar Core.coreLoc id none) : Option Expression.Expr)
      = Option.map (fun e => LExpr.applyTypeSubst e S) (some (LExpr.fvar Core.coreLoc id none))
    rw [Option.map_some, LExpr.applyTypeSubst_fvar_none]
  | outArg id => rfl

/-- The `call` rule's per-input premise survives substitution when the substituted binder
    annotations are registered and agree with the substituted scope: a bare unannotated variable
    stays one, and any other expression becomes well typed. -/
private theorem inputMatch_subst (C : LContext CoreLParams) (Γ : TContext Unit) (S : Subst)
    (e : Expression.Expr) (mty : LMonoTy)
    (h : match e with
         | .fvar _ x none => Γ.types.find? x = some (.forAll [] mty)
         | e => Lambda.LExpr.HasTypeA (T := CoreLParams) [] e mty)
    (hB : BinderAnnotsKnown C (LExpr.applyTypeSubst e S))
    (hag : TypeSpec.ScopesAnnotAgree C (TContext.subst Γ S).types (LExpr.applyTypeSubst e S)) :
    match LExpr.applyTypeSubst e S with
    | .fvar _ x none =>
        (TContext.subst Γ S).types.find? x = some (.forAll [] (LMonoTy.subst S mty))
    | e' => ExprWellTyped C (TContext.subst Γ S).types e' (LMonoTy.subst S mty) := by
  have hgen : ∀ e0 : Expression.Expr,
      Lambda.LExpr.HasTypeA (T := CoreLParams) [] e0 mty →
      Lambda.LExpr.HasTypeA (T := CoreLParams) []
        (LExpr.applyTypeSubst e0 S) (LMonoTy.subst S mty) :=
      fun _ h0 => hasTypeA_applyTypeSubst S h0
  rw [LExpr.applyTypeSubst_eq_replaceUserProvidedType]
  rw [LExpr.applyTypeSubst_eq_replaceUserProvidedType] at hB hag
  match e with
  | .fvar m x none =>
    show (TContext.subst Γ S).types.find? x = some (.forAll [] (LMonoTy.subst S mty))
    rw [TContext_subst_find?, h, Option.map_some]
    rfl
  | .fvar _ _ (some _) | .const .. | .op .. | .bvar .. | .abs .. | .quant .. | .app .. | .ite ..
  | .eq .. =>
    have h0 := hgen _ h
    rw [LExpr.applyTypeSubst_eq_replaceUserProvidedType] at h0
    exact ⟨h0, hB, hag⟩

/-! ## Absorption over the walk -/

section Absorption

/-- The substitution a statement-list walk ends with absorbs the one it started from. -/
private theorem go_absorbs
    (P : Program) (op : Option Procedure)
    (C : LContext CoreLParams) (Env : TEnv Unit)
    (ss acc : List Statement) (labels : List String)
    (ss' : List Statement) (Env' : TEnv Unit) (C' : LContext CoreLParams)
    {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.go P op C Env ss acc labels m st
      = .ok (ss', Env', C', st'))
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  have hRblock : ∀ C (Env : TEnv Unit) bss labels bss' Eb {m : ScopeMap} {st stb : ScopeState},
      FactorySigWF C.functions →
      @Core.Statement.typeCheckAux.goBlock P op C Env bss [] labels m st
        = .ok (bss', Eb, C, stb) →
      (FactorySigWF C.functions → LExpr.TEnvWF (T := CoreLParams) Env →
        Subst.absorbs Eb.stateSubstInfo.subst Env.stateSubstInfo.subst) → EnvAbsorbStep Env Eb :=
    fun C Env bss labels bss' Eb _ _ _ hf hgb ihb he =>
      ⟨goBlock_preserves_TEnvWF C C Env Eb P op bss [] bss' labels hgb he hf, ihb hf he⟩
  refine go_ok_induct
    (motive := fun C Env _ _ _ _ _ _ Env' _ _ => LExpr.TEnvWF (T := CoreLParams) Env →
      FactorySigWF C.functions → Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst)
    (motiveB := fun C Env _ _ _ _ _ _ Env' _ _ => FactorySigWF C.functions →
      LExpr.TEnvWF (T := CoreLParams) Env →
      Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst)
    ?nil ?cmd ?block ?ite ?loop ?exit ?typeDecl ?blockScope ?blockFlat C Env ss acc labels ss'
    Env' C' h he hf
  case nil => exact fun _ Env _ _ _ _ _ _ => Subst.absorbs_refl _ Env.stateSubstInfo.isWF
  case cmd =>
    intro C Env _ _ _ _ _ cmd c' Env1 _ _ _ _ htc _ _ ih he hf
    exact Subst.absorbs_trans _ _ _ (Statement.typeCheckCmd_absorbs C Env Env1 P _ c' htc he hf)
      (ih (Statement.typeCheckCmd_preserves_TEnvWF C Env Env1 P _ c' htc he hf) hf)
  case block =>
    intro C Env _ _ _ _ _ _ bss _ bss' Eb _ _ _ _ _ _ hgb ihb _ ih he hf
    obtain ⟨hwf, habs⟩ := hRblock C Env bss _ bss' Eb hf hgb ihb he
    exact Subst.absorbs_trans _ _ _ habs (ih hwf hf)
  case ite =>
    intro C Env _ _ _ _ _ _ tss ess _ _ Ec tss' Et _ ess' Ee _ _ _ _ _ hcond _ hgt iht hge ihe _ ih
      he hf
    obtain ⟨hwf, habs⟩ :=
      ((hcond.chain.absorb hf).trans (hRblock C Ec tss _ tss' Et hf hgt iht)).trans
        (hRblock C Et ess _ ess' Ee hf hge ihe) he
    exact Subst.absorbs_trans _ _ _ habs (ih hwf hf)
  case loop =>
    intro C Env _ _ _ _ _ _ _ _ bss _ _ _ _ _ _ Efold bss' Eb _ _ _ _ _ hg hm hi _ hgb ihb _ ih he
      hf
    obtain ⟨hwf, habs⟩ := ((loopHead_chain hg hm hi).absorb hf).trans
      (hRblock C Efold bss _ bss' Eb hf hgb ihb) he
    exact Subst.absorbs_trans _ _ _ habs (ih hwf hf)
  case exit => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => ih
  case typeDecl =>
    intro C Env _ _ _ _ _ tc _ Cnew _ _ _ _ htc _ ih he hf
    exact ih he (TypeConstructor.typeCheck_functions_eq htc ▸ hf)
  case blockFlat => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih hf he => ih he hf
  case blockScope =>
    exact fun _ Env _ _ _ _ _ _ _ _ _ _ ih hf he =>
      ih (Lambda.pushEmptyContext_preserves_TEnvWF (T := CoreLParams) Env he) hf

end Absorption

/-! ## Input soundness of statement checking -/

/-- If no alias of a scope is named after a registered type, neither is one of an equivalent
    scope. -/
private theorem aliasNamesUnregistered_of_equiv {ks : Lambda.KnownTypes} {Γ Γ' : TContext Unit}
    (h : TContext.Equiv (T := CoreLParams) Γ Γ')
    (hp : ∀ al ∈ Γ'.aliases, ks.containsName al.name = false) :
    ∀ al ∈ Γ.aliases, ks.containsName al.name = false := by
  rw [h.2]
  exact hp

/-- `R` under the premises of the input-soundness induction at one walk position: well-formedness
    and scope facts about the start state, the annotation sweep under `S`, and fixity of the rigid
    type variables. -/
private abbrev GoInputPre (ambientRigids : RigidNames) (S : Subst) (C : LContext CoreLParams)
    (Env Env' : TEnv Unit) (acc ss' : List Statement) (R : Prop) : Prop :=
  Subst.absorbs S Env'.stateSubstInfo.subst →
    LExpr.TEnvWF (T := CoreLParams) Env → FactorySigWF C.functions →
    MonoScope Env.context →
    Env.context.types ≠ [] →
    (∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false) →
    (∀ ss_proc, ss' = acc.reverse ++ ss_proc → SweepAt C S ss_proc) →
    (∀ v ∈ C.rigidTypeVars, LMonoTy.subst S (.ftvar v) = .ftvar v) →
    (∀ x ∈ ambientRigids.map Prod.fst, x ∈ C.rigidTypeVars) →
    R

/-- The conclusion of input soundness at one walk position: the final substitution absorbs the
    starting one, the recorded type variables stay writable, and the statements are well typed
    with side-condition evidence. -/
private abbrev GoInputMotive (P : Program) (ambientRigids : RigidNames) (S : Subst)
    (C : LContext CoreLParams) (Env : TEnv Unit) (ss : List Statement) (acc : List Statement)
    (labels : List String) (m : ScopeMap) (st : ScopeState) (ss' : List Statement)
    (Env' : TEnv Unit) (C' : LContext CoreLParams) (st' : ScopeState) : Prop :=
  GoInputPre ambientRigids S C Env Env' acc ss'
    (Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst ∧
      (ScopeAdmissible C.rigidTypeVars m st →
        ∀ v ∈ st'.seen, TyVarAdmissibility.notGeneratedOrRigid v = true) ∧
      (ScopeAvoids (ambientRigids.map Prod.fst) m st →
        ScopeAdmissible C.rigidTypeVars m st →
        ∀ Δ, WrittenEnv.Tracks S C.rigidTypeVars m Δ →
          ∃ Γ' Δ', ∃ hty : StatementsHasType P C
              (TContext.subst Env.context S) Δ labels ss C' Γ' Δ',
            StatementsSideConditionsΔ ambientRigids hty ∧
              TContext.FindEq (T := CoreLParams) Γ' (TContext.subst Env'.context S)))

/-- The conclusion of input soundness for a block check, in the same form as for a statement
    list: absorption, writable type variables, and well-typed statements with side-condition
    evidence. -/
private abbrev GoInputMotiveB (P : Program) (ambientRigids : RigidNames) (S : Subst)
    (C : LContext CoreLParams) (Env : TEnv Unit) (ss : List Statement) (acc : List Statement)
    (labels : List String) (m : ScopeMap) (st : ScopeState) (ss' : List Statement)
    (Env' : TEnv Unit) (_ : LContext CoreLParams) (st' : ScopeState) : Prop :=
  GoInputPre ambientRigids S C Env Env' acc ss'
    (Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst ∧
      (ScopeAdmissible C.rigidTypeVars m st →
        ∀ v ∈ st'.seen, TyVarAdmissibility.notGeneratedOrRigid v = true) ∧
      (ScopeAvoids (ambientRigids.map Prod.fst) m st →
        ScopeAdmissible C.rigidTypeVars m st →
        ∀ Δ, WrittenEnv.Tracks S C.rigidTypeVars m Δ →
          ∃ C_body Γ_body Δ_body, ∃ hty :
            StatementsHasType P C (TContext.subst Env.context S) Δ
              labels ss C_body Γ_body Δ_body,
            StatementsSideConditionsΔ ambientRigids hty))

/-- A scope with the same lookups as one that is a monotype stack with no alias named after a
    registered type is again such a scope. -/
private theorem goInputScope_of_equiv {C : LContext CoreLParams} {Env E : TEnv Unit} :
      TContext.Equiv (T := CoreLParams) E.context Env.context →
      MonoScope Env.context → Env.context.types ≠ [] →
      (∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false) →
      MonoScope E.context ∧ E.context.types ≠ [] ∧
        ∀ al ∈ E.context.aliases, C.knownTypes.containsName al.name = false :=
  fun heq hmono hne hAN =>
      ⟨MonoScope_of_findEq heq.toFindEq hmono, heq.symm.types_ne_nil hne,
        aliasNamesUnregistered_of_equiv heq hAN⟩

/-- Input soundness of the walk at a statement `cmd`, given the induction hypotheses for its
    sub-runs. -/
private theorem go_input_cmd {P : Program} {op : Option Procedure} {ambientRigids : RigidNames}
    {S : Subst}
    (h_Swf : SubstWF S) (h_np : NoParamRange ambientRigids S) :
    ∀ C Env acc labels m st srest cmd c' Env1 ss' Env' C' st',
      Statement.typeCheckCmd C Env P (renameCmd C.rigidTypeVars m st cmd).1 = .ok (c', Env1) →
      (∀ e ∈ Statement.cmdExprs cmd,
        unboundAnnotVar? false C.rigidTypeVars (renameCmd C.rigidTypeVars m st cmd).2.1 e
          = none) →
      @Core.Statement.typeCheckAux.go P op C Env1 srest (Stmt.cmd c' :: acc) labels
        (renameCmd C.rigidTypeVars m st cmd).2.1 (renameCmd C.rigidTypeVars m st cmd).2.2
        = .ok (ss', Env', C', st') →
      GoInputMotive P ambientRigids S C Env1 srest (Stmt.cmd c' :: acc) labels
        (renameCmd C.rigidTypeVars m st cmd).2.1
        (renameCmd C.rigidTypeVars m st cmd).2.2 ss' Env' C' st' →
      GoInputMotive P ambientRigids S C Env (Stmt.cmd cmd :: srest) acc labels m st ss' Env' C'
          st' := by
  intro C Env acc labels m st srest cmd c' Envm ss' Env' C' st' htc hscope hgo2 ih1 habs he hf hcl
    h_ne hAN hS hfix hpsRig
  have hwf' : LExpr.TEnvWF (T := CoreLParams) Envm :=
    Statement.typeCheckCmd_preserves_TEnvWF C Env Envm P _ c' htc he hf
  have h_ne' : Envm.context.types ≠ [] :=
    Statement.typeCheckCmd_preserves_context_types_ne C Env Envm P _ c' htc h_ne
  have hpeel : ∀ tp, ss' = (Stmt.cmd c' :: acc).reverse ++ tp →
      allCmdTys (fun mty => LMonoTy.knownInstance mty C.knownTypes)
          (Statement.Command.subst S c') = true ∧ SweepAt C S tp :=
    fun tp htp => SweepAt.cmd_peel C S _ _ (hS _ (acc_cons_shift htp))
  obtain ⟨tp0, htp0⟩ :=
    (go_vars_eq C C' Envm Env' P op srest (Stmt.cmd c' :: acc) ss' labels hgo2).2.2
  have htailAbs0 : Subst.absorbs Env'.stateSubstInfo.subst
      Envm.stateSubstInfo.subst :=
    go_absorbs P op C Envm srest (Stmt.cmd c' :: acc) labels ss' Env' C'
      hgo2 hwf' hf
  have habsEnvm : Subst.absorbs S Envm.stateSubstInfo.subst :=
    Subst.absorbs_trans _ _ _ htailAbs0 habs
  have hcmdAbs : Subst.absorbs Envm.stateSubstInfo.subst Env.stateSubstInfo.subst :=
    Statement.typeCheckCmd_absorbs C Env Envm P _ c' htc he hf
  obtain ⟨Δcmd, hcmd, hcmdEq⟩ :=
    Statement.typeCheckCmd_sound_absorbing C Env Envm P _ c' S htc he hf
      hcl hAN (hpeel tp0 htp0).1 habsEnvm h_Swf hfix
  have hwfA : ∀ a ∈ (TContext.subst Env.context S).aliases, TypeAlias.WF a := by
    rw [TContext.subst_aliases]
    exact he.aliasesWF
  have hcl' : MonoScope Envm.context :=
    (MonoScope_subst_iff Envm.context S).mp
      (MonoScope_of_findEq hcmdEq.symm
        (CmdExtHasType_MonoScope hcmd
          ((MonoScope_subst_iff Env.context S).mpr hcl)))
  have hANm : ∀ al ∈ Envm.context.aliases, C.knownTypes.containsName al.name = false := by
    rw [(Statement.typeCheckCmd_preserves_context C Env Envm P _ c' htc).2]
    exact hAN
  obtain ⟨htailAbs, htailSeen, htailAll⟩ :=
    ih1 habs hwf' hf hcl' h_ne' hANm
    (fun tp htp => (hpeel tp htp).2) hfix hpsRig
  refine ⟨Subst.absorbs_trans _ _ _ hcmdAbs htailAbs,
    fun hinv => htailSeen
      (hcmd.rename_scopeAdmissible C.rigidTypeVars m st cmd hwfA hinv).1,
    fun hsc hinv Δ htr => ?_⟩
  obtain ⟨-, hrenamed⟩ :=
    CmdExtHasType.of_rename S hfix m st cmd hwfA hinv hcmd hscope
  obtain ⟨Δc, htrc, hcmdW⟩ := hrenamed Δ htr
  have hsc' := renameCmd_scopeAvoids C.rigidTypeVars hpsRig m st cmd hsc
  obtain ⟨Γtail, Δtail, htail, htailStrict, htailEq⟩ := htailAll hsc'
    (hcmd.rename_scopeAdmissible C.rigidTypeVars m st cmd hwfA hinv).1 Δc htrc
  obtain ⟨Γtail', htail', htailStrict', htailEq'⟩ :=
    StatementsSideConditionsΔ.input_ctx_FindEq htailStrict hcmdEq
  let hstmt : StatementHasType P C
      (TContext.subst Env.context S) Δ labels (Stmt.cmd cmd) C Δcmd Δc :=
    StatementHasType.cmd _ _ _ _ _ _ _ _ hcmdW (TContext.Equiv.refl (T := CoreLParams) _)
  exact ⟨Γtail', Δtail, StatementsHasType.cons _ _ _ _ _ _ _ _ _ _ _ _ hstmt htail',
    .cons hstmt htail' (.cmd hcmdW (TContext.Equiv.refl _)
      (htrc.noParam hsc'.names h_np)) htailStrict',
    htailEq'.trans htailEq⟩

/-- Input soundness of the walk at a statement `block`, given the induction hypotheses for its
    sub-runs. -/
private theorem go_input_block {P : Program} {op : Option Procedure} {ambientRigids : RigidNames}
    {S : Subst} :
    ∀ C Env acc labels m st srest label bss md bss' Eb stb ss' Env' C' st',
      ¬ labels.contains label = true →
      @Core.Statement.typeCheckAux.goBlock P op C Env bss [] (label :: labels) m st
        = .ok (bss', Eb, C, stb) →
      GoInputMotiveB P ambientRigids S C Env bss [] (label :: labels) m st bss' Eb C stb →
      @Core.Statement.typeCheckAux.go P op C Eb srest
        (Stmt.block label bss' md :: acc) labels m stb = .ok (ss', Env', C', st') →
      GoInputMotive P ambientRigids S C Eb srest (Stmt.block label bss' md :: acc) labels m stb
          ss' Env' C' st' →
      GoInputMotive P ambientRigids S C Env (Stmt.block label bss md :: srest) acc labels m st ss'
          Env' C' st' := by
  intro Cgb Env acc labels m st srest label bss md bss' Egb stb ss' Env' C' _ hcon hgb
    ih1 hgo2 ih2 habs he hf hcl h_ne hAN hS hfix hpsRig
  obtain ⟨-, hEqctx⟩ :=
    goBlock_scoping Cgb Cgb Env Egb P op bss [] bss' (label :: labels) hgb he hf
  have hEgbWF : LExpr.TEnvWF (T := CoreLParams) Egb :=
    goBlock_preserves_TEnvWF Cgb Cgb Env Egb P op bss [] bss' (label :: labels) hgb he hf
  have hEgbMono : MonoScope Egb.context :=
    MonoScope_of_findEq hEqctx.toFindEq hcl
  have hpeel : ∀ tp, ss' = (Stmt.block label bss' md :: acc).reverse ++ tp →
      SweepAt Cgb S bss' ∧ SweepAt Cgb S tp :=
    fun tp htp => SweepAt.block_peel Cgb S _ _ _ _ (hS _ (acc_cons_shift htp))
  obtain ⟨tp0, htp0⟩ :=
    (go_vars_eq Cgb C' Egb Env' P op srest (Stmt.block label bss' md :: acc) ss' labels hgo2).2.2
  obtain ⟨htailAbs, htailSeen, httyAll⟩ :=
    ih2 habs
      hEgbWF hf hEgbMono (hEqctx.symm.types_ne_nil h_ne)
      (aliasNamesUnregistered_of_equiv hEqctx hAN)
      (fun tp htp => (hpeel tp htp).2) hfix hpsRig
  have habsEgb : Subst.absorbs S Egb.stateSubstInfo.subst :=
    Subst.absorbs_trans _ _ _ htailAbs habs
  obtain ⟨hbodyAbs, hbodySeen, hbtyAll⟩ :=
    ih1 habsEgb he hf hcl h_ne hAN
      (nil_acc_splits (hpeel tp0 htp0).1) hfix hpsRig
  have hnotmem : label ∉ labels := fun hmem => hcon (List.elem_eq_true_of_mem hmem)
  refine ⟨Subst.absorbs_trans _ _ _ hbodyAbs htailAbs,
    fun hinv => htailSeen (hinv.of_seen (hbodySeen hinv)),
    fun hsc hinv Δ htr => ?_⟩
  obtain ⟨C_body, Γ_body, Δ_body, hbty, hbtyStrict⟩ := hbtyAll hsc hinv Δ htr
  obtain ⟨Γtail, Δtail, htty, httyStrict, httyEq⟩ :=
    httyAll ⟨hsc.names, fun x hx => goBlock_avoid_mono hgb x (hsc.avoid x hx)⟩
      (hinv.of_seen (hbodySeen hinv)) Δ htr
  let hstmt : StatementHasType P Cgb
      (TContext.subst Env.context S) Δ labels (Stmt.block label bss md)
      Cgb (TContext.subst Egb.context S) Δ :=
    StatementHasType.block _ _ _ _ _ _ _ _ _ _ _ hnotmem hbty (hEqctx.subst S)
  exact ⟨Γtail, Δtail, StatementsHasType.cons _ _ _ _ _ _ _ _ _ _ _ _ hstmt htty,
    .cons hstmt htty (.block hnotmem hbty (hEqctx.subst S) hbtyStrict)
      httyStrict,
    httyEq⟩

/-- Input soundness of the walk at a statement `ite`, given the induction hypotheses for its
    sub-runs. -/
private theorem go_input_ite {P : Program} {op : Option Procedure} {ambientRigids : RigidNames}
    {S : Subst}
    (h_Swf : SubstWF S) (h_np : NoParamRange ambientRigids S) :
    ∀ C Env acc labels m st srest cond tss ess md condElab Ec tss' Et stt ess' Ee ste ss'
        Env' C' st',
      CondChecked C Env (renameExprOrNondet m cond) condElab Ec →
      (∀ e ∈ cond.toList, unboundAnnotVar? false C.rigidTypeVars m e = none) →
      @Core.Statement.typeCheckAux.goBlock P op C Ec tss [] labels m st
        = .ok (tss', Et, C, stt) →
      GoInputMotiveB P ambientRigids S C Ec tss [] labels m st tss' Et C stt →
      @Core.Statement.typeCheckAux.goBlock P op C Et ess [] labels m stt
        = .ok (ess', Ee, C, ste) →
      GoInputMotiveB P ambientRigids S C Et ess [] labels m stt ess' Ee C ste →
      @Core.Statement.typeCheckAux.go P op C Ee srest
        (Stmt.ite condElab tss' ess' md :: acc) labels m ste = .ok (ss', Env', C', st') →
      GoInputMotive P ambientRigids S C Ee srest (Stmt.ite condElab tss' ess' md :: acc) labels m
          ste ss' Env' C' st' →
      GoInputMotive P ambientRigids S C Env (Stmt.ite cond tss ess md :: srest) acc labels m st
          ss' Env' C' st' := by
  intro Cx Env acc labels m st srest cond tss ess md condElab Ec tss' Et stt ess' Ee ste ss' Env'
    C' _ hcond hscope hgt ih_t hge ih_e hgo ih2 habs he hf hcl h_ne hAN hS hfix hpsRig
  obtain ⟨hEc_env, hEcWF, -⟩ := (hcond.chain.scope hf).facts he h_ne
  obtain ⟨hEcMono, hEcNe, hEcAN⟩ := goInputScope_of_equiv hEc_env hcl h_ne hAN
  obtain ⟨-, hEt_eq⟩ := goBlock_scoping Cx Cx Ec Et P op tss [] tss' labels hgt hEcWF hf
  have hEt_env : TContext.Equiv (T := CoreLParams) Et.context Env.context :=
    hEt_eq.trans hEc_env
  have hEtWF : LExpr.TEnvWF (T := CoreLParams) Et :=
    goBlock_preserves_TEnvWF Cx Cx Ec Et P op tss [] tss' labels hgt hEcWF hf
  obtain ⟨hEtMono, hEtNe, hEtAN⟩ := goInputScope_of_equiv hEt_env hcl h_ne hAN
  obtain ⟨-, hEe_eq⟩ := goBlock_scoping Cx Cx Et Ee P op ess [] ess' labels hge hEtWF hf
  have hEe_env : TContext.Equiv (T := CoreLParams) Ee.context Env.context :=
    hEe_eq.trans hEt_env
  have hEeWF : LExpr.TEnvWF (T := CoreLParams) Ee :=
    goBlock_preserves_TEnvWF Cx Cx Et Ee P op ess [] ess' labels hge hEtWF hf
  obtain ⟨hEeMono, hEeNe, hEeAN⟩ := goInputScope_of_equiv hEe_env hcl h_ne hAN
  have hpeel : ∀ tp, ss' = (Stmt.ite condElab tss' ess' md :: acc).reverse ++ tp →
      SweepAt Cx S tss' ∧ SweepAt Cx S ess' ∧ SweepAt Cx S tp :=
    fun tp htp => SweepAt.ite_peel Cx S _ _ _ _ _ (hS _ (acc_cons_shift htp))
  obtain ⟨tp0, htp0⟩ :=
    (go_vars_eq Cx C' Ee Env' P op srest (Stmt.ite condElab tss' ess' md :: acc) ss' labels hgo).2.2
  obtain ⟨htailAbs, htailSeen, htailAll⟩ :=
    ih2 habs hEeWF hf hEeMono hEeNe hEeAN
      (fun tp htp => (hpeel tp htp).2.2) hfix hpsRig
  have habsEe : Subst.absorbs S Ee.stateSubstInfo.subst :=
    Subst.absorbs_trans _ _ _ htailAbs habs
  obtain ⟨hElseAbs, hElseSeen, hteAll⟩ :=
    ih_e habsEe hEtWF hf hEtMono hEtNe hEtAN
      (nil_acc_splits (hpeel tp0 htp0).2.1) hfix hpsRig
  have habsEt : Subst.absorbs S Et.stateSubstInfo.subst :=
    Subst.absorbs_trans _ _ _ hElseAbs habsEe
  obtain ⟨hThenAbs, hThenSeen, httAll⟩ :=
    ih_t habsEt hEcWF hf hEcMono hEcNe hEcAN
      (nil_acc_splits (hpeel tp0 htp0).1) hfix hpsRig
  have habsEc : Subst.absorbs S Ec.stateSubstInfo.subst :=
    Subst.absorbs_trans _ _ _ hThenAbs habsEt
  refine ⟨Subst.absorbs_trans _ _ _
      (Subst.absorbs_trans _ _ _
        (Subst.absorbs_trans _ _ _ ((hcond.chain.absorb hf) he).2 hThenAbs)
        hElseAbs)
      htailAbs,
    fun hinv => htailSeen (hinv.of_seen (hElseSeen (hinv.of_seen (hThenSeen hinv)))),
    fun hsc hinv Δ htr => ?_⟩
  have hinvT : ScopeAdmissible Cx.rigidTypeVars m stt := hinv.of_seen (hThenSeen hinv)
  have hinvE : ScopeAdmissible Cx.rigidTypeVars m ste := hinv.of_seen (hElseSeen hinvT)
  have hscT : ScopeAvoids (ambientRigids.map Prod.fst) m stt :=
    ⟨hsc.names, fun x hx => goBlock_avoid_mono hgt x (hsc.avoid x hx)⟩
  have hscE : ScopeAvoids (ambientRigids.map Prod.fst) m ste :=
    ⟨hsc.names, fun x hx => goBlock_avoid_mono hge x (hscT.avoid x hx)⟩
  obtain ⟨Cbt, Γbt, Δbt, htt_ty, httStrict⟩ := httAll hsc hinv Δ htr
  obtain ⟨Cbe, Γbe, Δbe, hte_ty, hteStrict⟩ := hteAll hscT hinvT Δ htr
  obtain ⟨Γtail, Δtail, htail, htailStrict, htailEq⟩ := htailAll hscE hinvE Δ htr
  obtain ⟨Γbe', hte_ty', hteStrict', -⟩ :=
    StatementsSideConditionsΔ.input_ctx_FindEq hteStrict
      (TContext.FindEq.subst_subst S hEt_env.symm.toFindEq)
  obtain ⟨Γbt', htt_ty', httStrict', -⟩ :=
    StatementsSideConditionsΔ.input_ctx_FindEq httStrict
      (TContext.FindEq.subst_subst S hEc_env.symm.toFindEq)
  -- Only the typing rule for the statement itself depends on the condition's form.
  obtain ⟨hstmt, hstmtStrict⟩ : ∃ hstmt : StatementHasType P Cx
      (TContext.subst Env.context S) Δ labels (Stmt.ite cond tss ess md)
      Cx (TContext.subst Ee.context S) Δ, StatementSideConditionsΔ ambientRigids hstmt := by
    cases cond with
    | det c =>
      obtain ⟨conda, hrs, hbool, hcondElab⟩ := hcond
      obtain ⟨-, hguardAnnAll⟩ :=
        resolved_input_facts (ResolveChain.refl Cx Env) hrs hbool rfl
          (ResolveChain.refl Cx Ec) he hf hcl h_ne
      have hguardAnn := writtenAnnotsOk_of_renameExpr m c (hguardAnnAll S)
      have hcmem : c ∈ (ExprOrNondet.det c).toList := by
        simp only [ExprOrNondet.toList, List.mem_singleton]
      have hguardScope : AnnotsInScope Cx.rigidTypeVars Δ c :=
        annotsInScope_of_unboundAnnotVar? htr.3 (hscope c hcmem)
      have hknown : BinderAnnotsKnown Cx (LExpr.applyTypeSubst conda.unresolved S) := by
        subst hcondElab
        exact SweepAt.ite_condKnown Cx S _ _ _ md tp0 (hS _ (acc_cons_shift htp0))
      have hguard : LExpr.HasType Cx (TContext.subst Env.context S) (instAnnots Δ c)
          (.forAll [] .bool) := by
        rw [← instAnnots_substEnv_renameExpr htr hfix c hguardScope]
        exact resolved_input_read (ResolveChain.refl Cx Env) hrs hbool rfl
          (ResolveChain.refl Cx Ec) he hf hcl h_ne hAN S habsEc h_Swf hknown
      have hread : ReadAvoids ambientRigids Δ := htr.noParam hsc.names h_np
      exact ⟨StatementHasType.ite_det _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          hguard hguardAnn hguardScope htt_ty' hte_ty' (hEe_env.subst S),
        .ite_det hguard hguardAnn hguardScope hread htt_ty' hte_ty' (hEe_env.subst S) httStrict'
          hteStrict'⟩
    | nondet =>
      exact ⟨StatementHasType.ite_nondet _ _ _ _ _ _ _ _ _ _ _ _ _ _
          htt_ty' hte_ty' (hEe_env.subst S),
        .ite_nondet htt_ty' hte_ty' (hEe_env.subst S) httStrict' hteStrict'⟩
  exact ⟨Γtail, Δtail, StatementsHasType.cons _ _ _ _ _ _ _ _ _ _ _ _ hstmt htail,
    .cons hstmt htail hstmtStrict htailStrict, htailEq⟩

/-- Input soundness of the walk at a statement `loop`, given the induction hypotheses for its
    sub-runs. -/
private theorem go_input_loop {P : Program} {op : Option Procedure} {ambientRigids : RigidNames}
    {S : Subst}
    (h_Swf : SubstWF S) (h_np : NoParamRange ambientRigids S) :
    ∀ C Env acc labels m st srest guard measure invariant bss md guardElab Eg measureElab
        Em invElab Efold bss' Eb stb ss' Env' C' st',
      CondChecked C Env (renameExprOrNondet m guard) guardElab Eg →
      MeasureChecked C Eg (measure.map (renameExpr m)) measureElab Em →
      InvariantsChecked C Em (invariant.map (fun (l, i) => (l, renameExpr m i))) invElab Efold →
      (∀ e ∈ Statement.loopExprs guard measure invariant,
        unboundAnnotVar? false C.rigidTypeVars m e = none) →
      @Core.Statement.typeCheckAux.goBlock P op C Efold bss [] labels m st
        = .ok (bss', Eb, C, stb) →
      GoInputMotiveB P ambientRigids S C Efold bss [] labels m st bss' Eb C stb →
      @Core.Statement.typeCheckAux.go P op C Eb srest
        (Stmt.loop guardElab measureElab invElab bss' md :: acc) labels m stb
        = .ok (ss', Env', C', st') →
      GoInputMotive P ambientRigids S C Eb srest (Stmt.loop guardElab measureElab invElab bss' md
          :: acc) labels m stb
        ss' Env' C' st' →
      GoInputMotive P ambientRigids S C Env (Stmt.loop guard measure invariant bss md :: srest)
          acc labels m st ss' Env'
        C' st' := by
  intro Cx Env acc labels m st srest guard measure invariant bss md guardElab Eg measureElab Em
    invElab Efold bss' Ebody stb ss' Env' C' _ hgc hmc hic hscope hbody ih1 htail ih2 habs he hf
    hcl h_ne hAN hS hfix hpsRig
  obtain ⟨-, -, -, hguardAnn, hmeasureAnn, hinvariantAnn,
    hEfoldCtx, hEfoldWF, hEfoldMono, hEfoldAbs⟩ := loopHead_input hgc hmc hic he hf hcl h_ne
  obtain ⟨_, hEbody_eq⟩ :=
    goBlock_scoping Cx Cx Efold Ebody P op bss [] bss' labels hbody hEfoldWF hf
  have hEbody_env : TContext.Equiv (T := CoreLParams) Ebody.context Env.context :=
    hEbody_eq.trans hEfoldCtx
  have hEbodyWF : LExpr.TEnvWF (T := CoreLParams) Ebody :=
    goBlock_preserves_TEnvWF Cx Cx Efold Ebody P op bss [] bss' labels hbody hEfoldWF hf
  have hEbodyMono : MonoScope Ebody.context :=
    MonoScope_of_findEq hEbody_eq.toFindEq hEfoldMono
  have hpeel : ∀ tp,
      ss' = ((Stmt.loop guardElab measureElab invElab bss' md) :: acc).reverse ++ tp →
      SweepAt Cx S bss' ∧ SweepAt Cx S tp :=
    fun tp htp => SweepAt.loop_peel Cx S _ _ _ _ _ _ (hS _ (acc_cons_shift htp))
  obtain ⟨tp0, htp0⟩ :=
    (go_vars_eq Cx C' Ebody Env' P op srest ((Stmt.loop guardElab measureElab invElab bss' md) ::
        acc) ss' labels htail).2.2
  obtain ⟨htailAbs, htailSeen, htailAll⟩ :=
    ih2 habs hEbodyWF hf hEbodyMono
      (hEbody_env.symm.types_ne_nil h_ne)
      (aliasNamesUnregistered_of_equiv hEbody_env hAN)
      (fun tp htp => (hpeel tp htp).2) hfix hpsRig
  have habsEbody : Subst.absorbs S Ebody.stateSubstInfo.subst :=
    Subst.absorbs_trans _ _ _ htailAbs habs
  obtain ⟨hbodyAbs, hbodySeen, hbtyAll⟩ :=
    ih1 habsEbody hEfoldWF hf hEfoldMono
      (hEfoldCtx.symm.types_ne_nil h_ne)
      (aliasNamesUnregistered_of_equiv hEfoldCtx hAN)
      (nil_acc_splits (hpeel tp0 htp0).1) hfix hpsRig
  have habsEfold : Subst.absorbs S Efold.stateSubstInfo.subst :=
    Subst.absorbs_trans _ _ _ hbodyAbs habsEbody
  have hgAnn := hguardAnn S
  have hmAnn := hmeasureAnn S
  have hiAnn := hinvariantAnn S
  have hknownAll := SweepAt.loop_known Cx S guardElab measureElab invElab bss' md tp0
    (hS _ (acc_cons_shift htp0))
  have hgAnn' : ∀ g, guard = .det g →
      WrittenAnnotsOk Cx (TContext.subst Env.context S) g := by
    intro g hgEq
    subst hgEq
    exact writtenAnnotsOk_of_renameExpr m g (hgAnn _ rfl)
  have hmAnn' : ∀ me, measure = some me →
      WrittenAnnotsOk Cx (TContext.subst Env.context S) me := by
    intro me hmEq
    subst hmEq
    exact writtenAnnotsOk_of_renameExpr m me (hmAnn _ rfl)
  have hiAnn' : ∀ p, p ∈ invariant →
      WrittenAnnotsOk Cx (TContext.subst Env.context S) p.2 := by
    intro p hp
    obtain ⟨l, i⟩ := p
    exact writtenAnnotsOk_of_renameExpr m i (hiAnn _ (List.mem_map_of_mem hp))
  refine ⟨Subst.absorbs_trans _ _ _ hEfoldAbs (Subst.absorbs_trans _ _ _ hbodyAbs htailAbs),
    fun hinv => htailSeen (hinv.of_seen (hbodySeen hinv)),
    fun hsc hinv Δ htr => ?_⟩
  obtain ⟨C_body, Γ_body, Δ_body, hbty, hbtyStrict⟩ := hbtyAll hsc hinv Δ htr
  obtain ⟨Γ_body', hbty', hbtyStrict', -⟩ :=
    StatementsSideConditionsΔ.input_ctx_FindEq hbtyStrict
      (TContext.FindEq.subst_subst S hEfoldCtx.symm.toFindEq)
  obtain ⟨Γtail, Δtail, htty, httyStrict, htailEq⟩ :=
    htailAll ⟨hsc.names, fun x hx => goBlock_avoid_mono hbody x (hsc.avoid x hx)⟩
      (hinv.of_seen (hbodySeen hinv)) Δ htr
  have hscope' : ∀ e ∈ Statement.loopExprs guard measure invariant,
      AnnotsInScope Cx.rigidTypeVars Δ e :=
    fun e he => annotsInScope_of_unboundAnnotVar? htr.3 (hscope e he)
  have hgS : ∀ g, guard = .det g → AnnotsInScope Cx.rigidTypeVars Δ g := by
    intro g hgEq
    subst hgEq
    have hgmem : g ∈ Statement.loopExprs (.det g) measure invariant := by
      simp [Statement.loopExprs, ExprOrNondet.toList]
    exact hscope' g hgmem
  have hmS : ∀ me, measure = some me → AnnotsInScope Cx.rigidTypeVars Δ me := by
    intro me hmEq
    subst hmEq
    have hmmem : me ∈ Statement.loopExprs guard (some me) invariant := by
      simp [Statement.loopExprs]
    exact hscope' me hmmem
  have hiS : ∀ p, p ∈ invariant → AnnotsInScope Cx.rigidTypeVars Δ p.2 := by
    intro p hp
    have hmem : p.2 ∈ Statement.loopExprs guard measure invariant :=
      List.mem_append_right _ (List.mem_map_of_mem hp)
    exact hscope' p.2 hmem
  have hEgEfold : ResolveChain Cx Eg Efold := hmc.chain.trans hic.chain_mem.1
  have hg' : ∀ g, guard = .det g → LExpr.HasType Cx (TContext.subst Env.context S)
      (instAnnots Δ g) (.forAll [] .bool) := by
    intro g hgEq
    subst hgEq
    obtain ⟨conda, hrs, hbool, hel⟩ := hgc
    rw [← instAnnots_substEnv_renameExpr htr hfix g (hgS g rfl)]
    exact resolved_input_read (ResolveChain.refl Cx Env) hrs hbool rfl hEgEfold he hf hcl
      h_ne hAN S habsEfold h_Swf (hknownAll.1 _ (congrArg (ExprOrNondet.map _) hel))
  have hm' : ∀ me, measure = some me → LExpr.HasType Cx (TContext.subst Env.context S)
      (instAnnots Δ me) (.forAll [] .int) := by
    intro me hmEq
    subst hmEq
    obtain ⟨ma, hrs, hint, hel⟩ := hmc
    rw [← instAnnots_substEnv_renameExpr htr hfix me (hmS me rfl)]
    exact resolved_input_read hgc.chain hrs hint rfl hic.chain_mem.1 he hf hcl h_ne hAN S
      habsEfold h_Swf (hknownAll.2.1 _ (congrArg (Option.map _) hel))
  have hi' : ∀ p, p ∈ invariant → LExpr.HasType Cx (TContext.subst Env.context S)
      (instAnnots Δ p.2) (.forAll [] .bool) := by
    intro p hp
    obtain ⟨ia, ⟨E, E', hE, hrs, hbool, hE'⟩, hmem⟩ :=
      hic.chain_mem.2.1 _ (List.mem_map_of_mem (f := fun (l, i) => (l, renameExpr m i)) hp)
    rw [← instAnnots_substEnv_renameExpr htr hfix p.2 (hiS p hp)]
    exact resolved_input_read (hgc.chain.trans (hmc.chain.trans hE)) hrs hbool rfl hE' he
      hf hcl h_ne hAN S habsEfold h_Swf (hknownAll.2.2 _ (List.mem_map_of_mem hmem))
  have hread : ReadAvoids ambientRigids Δ := htr.noParam hsc.names h_np
  let hstmt : StatementHasType P Cx
      (TContext.subst Env.context S) Δ labels (Stmt.loop guard measure invariant bss md)
      Cx (TContext.subst Ebody.context S) Δ :=
    StatementHasType.loop _ _ _ _ _ _ _ _ _ _ _ _ _
      hg' hgAnn' hm' hmAnn' hi' hiAnn' hgS hmS hiS hbty' (hEbody_env.subst S)
  exact ⟨Γtail, Δtail, StatementsHasType.cons _ _ _ _ _ _ _ _ _ _ _ _ hstmt htty,
    .cons hstmt htty
      (.loop hg' hgAnn' hm' hmAnn' hi' hiAnn' hgS hmS hiS hbty' (hEbody_env.subst S)
        hread hbtyStrict')
      httyStrict,
    htailEq⟩

/-- Input soundness of a successful statement walk, for a well-formed `S` that absorbs the walk's
    final substitution. If the scope state is admissible and its map avoids the ambient rigid
    names, then from any written-variable environment tracking the map, the source statements
    satisfy the typechecker spec in the `S`-applied scope, with side-condition evidence, and the
    spec's output scope agrees by lookup with the checker's under `S`. -/
private theorem go_input_sound_withSource
    (P : Program) (op : Option Procedure) (S : Subst)
    (C : LContext CoreLParams) (Env : TEnv Unit) (ss acc : List Statement)
    (labels : List String) (ss' : List Statement) (Env' : TEnv Unit) (C' : LContext CoreLParams)
    {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.go P op C Env ss acc labels m st
      = .ok (ss', Env', C', st'))
    (h_absorbs : Subst.absorbs S Env'.stateSubstInfo.subst)
    (h_Swf : SubstWF S) (h_np : NoParamRange ambientRigids S)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_mono : MonoScope Env.context)
    (h_types_ne : Env.context.types ≠ [])
    (h_aliasNames : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (hS : ∀ ss_proc, ss' = acc.reverse ++ ss_proc → SweepAt C S ss_proc)
    (h_rigidFixed : ∀ v ∈ C.rigidTypeVars, LMonoTy.subst S (.ftvar v) = .ftvar v)
    (h_rig : ∀ x ∈ ambientRigids.map Prod.fst, x ∈ C.rigidTypeVars) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst ∧
      (ScopeAdmissible C.rigidTypeVars m st →
        ∀ v ∈ st'.seen, TyVarAdmissibility.notGeneratedOrRigid v = true) ∧
      (ScopeAvoids (ambientRigids.map Prod.fst) m st →
      ScopeAdmissible C.rigidTypeVars m st →
      ∀ Δ, WrittenEnv.Tracks S C.rigidTypeVars m Δ →
        ∃ Γ' Δ', ∃ hty : StatementsHasType P C
            (TContext.subst Env.context S) Δ labels ss C' Γ' Δ',
          StatementsSideConditionsΔ ambientRigids hty ∧
            TContext.FindEq (T := CoreLParams) Γ' (TContext.subst Env'.context S)) := by
  refine go_ok_induct
    (motive := GoInputMotive P ambientRigids S)
    (motiveB := GoInputMotiveB P ambientRigids S)
    ?nil (go_input_cmd h_Swf h_np) go_input_block (go_input_ite h_Swf h_np) (go_input_loop h_Swf
        h_np) ?exit ?typeDecl ?blockScope ?blockFlat C Env ss acc labels ss'
    Env' C' h h_absorbs h_env h_fac h_mono h_types_ne h_aliasNames
    hS h_rigidFixed h_rig
  case nil =>
    intro Cx Env acc labels _ _ _ _ _ _ _ _ _ _ _
    refine ⟨Subst.absorbs_refl _ Env.stateSubstInfo.isWF, fun hinv => hinv.seen,
      fun _ _ Δ _ => ?_⟩
    exact ⟨TContext.subst Env.context S, Δ,
      StatementsHasType.nil _ _ _ _ _ (TContext.Equiv.refl (T := CoreLParams) _),
      .nil (TContext.Equiv.refl _), TContext.FindEq.refl _⟩
  case exit =>
    intro Cx Env acc labels _ _ srest l md ss' Env' C' _ _ hc _ ih1
      habs he hf hcl h_ne hAN hS hfix hpsRig
    obtain ⟨htailAbs, htailSeen, htailAll⟩ :=
      ih1 habs he hf hcl h_ne hAN
        (fun tp htp =>
          sweepAt_tail_of_keeps Cx S (Stmt.exit l md) tp
            (tysDeclaredStmt_exit Cx.knownTypes l md)
            (hS _ (acc_cons_shift htp))) hfix hpsRig
    refine ⟨htailAbs, htailSeen, fun hsc hinv Δ htr => ?_⟩
    obtain ⟨Γtail, Δtail, htail, htailStrict, htailEq⟩ := htailAll hsc hinv Δ htr
    let hstmt : StatementHasType P Cx
        (TContext.subst Env.context S) Δ labels (Stmt.exit l md)
        Cx (TContext.subst Env.context S) Δ :=
      @StatementHasType.exit P
        Cx (TContext.subst Env.context S) Δ labels l md
        (TContext.subst Env.context S)
        (List.mem_of_elem_eq_true hc) (TContext.Equiv.refl (T := CoreLParams) _)
    exact ⟨Γtail, Δtail, StatementsHasType.cons _ _ _ _ _ _ _ _ _ _ _ _ hstmt htail,
      .cons hstmt htail
        (.exit (List.mem_of_elem_eq_true hc) (TContext.Equiv.refl _))
        htailStrict,
      htailEq⟩
  case typeDecl =>
    intro Cx Env acc labels m _ srest tc md Cnew ss' Env' C' _ htc _ ih1
      habs he hf hcl h_ne hAN hS hfix hpsRig
    have hdecomp := TypeConstructor.typeCheck_decompose tc (.bodyLocal P.getNames) Cx Cnew Env htc
    have hprog : ∀ n ∈ P.getNames, n.name ≠ tc.name := hdecomp.1
    have hnotAlias := hdecomp.2.1 rfl
    have hkt := hdecomp.2.2 (default : Strata.Message)
    have hfCnew : FactorySigWF Cnew.functions := TypeConstructor.typeCheck_functions_eq htc ▸ hf
    have haddk : Cx.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } default
        = .ok Cnew := addKnownTypeWithError_message_irrel Cx Cnew _ _ default hkt
    have hrig : Cnew.rigidTypeVars = Cx.rigidTypeVars := addKnownTypeWithError_rigidTypeVars haddk
    have hfix' : ∀ v ∈ Cnew.rigidTypeVars, LMonoTy.subst S (.ftvar v) = .ftvar v := by
      rw [hrig]
      exact hfix
    have hpsRigNew : ∀ x ∈ ambientRigids.map Prod.fst, x ∈ Cnew.rigidTypeVars := by
      rw [hrig]
      exact hpsRig
    obtain ⟨htailAbs, htailSeen, htailAll⟩ :=
      ih1 habs he hfCnew hcl h_ne
        (fun al hal => knownTypes_addKnownTypeWithError_notContains_of_ne Cx Cnew _ default
          al.name hkt (fun h => hnotAlias al hal h.symm) (hAN al hal))
        (fun tp htp => SweepAt.typeDecl_peel Cx Cnew S tc md tp _ hkt (hS _ (acc_cons_shift htp)))
        hfix' hpsRigNew
    have hinv' : ∀ {st : ScopeState}, ScopeAdmissible Cx.rigidTypeVars m st →
        ScopeAdmissible Cnew.rigidTypeVars m st := by
      intro st hinv
      rw [hrig]
      exact hinv
    refine ⟨htailAbs, fun hinv => htailSeen (hinv' hinv), fun hsc hinv Δ htr => ?_⟩
    have htr' : WrittenEnv.Tracks S Cnew.rigidTypeVars m Δ := by
      rw [hrig]
      exact htr
    obtain ⟨Γtail, Δtail, htail, htailStrict, htailEq⟩ := htailAll hsc (hinv' hinv) Δ htr'
    have hnotAliasS : ∀ al ∈ (TContext.subst Env.context S).aliases, al.name ≠ tc.name :=
      nameNotAlias_of_aliases_eq (TContext.subst_aliases Env.context S) hnotAlias
    let hstmt : StatementHasType P Cx
        (TContext.subst Env.context S) Δ labels (Stmt.typeDecl tc md)
        Cnew (TContext.subst Env.context S) Δ :=
      @StatementHasType.typeDecl P
        Cx Cnew (TContext.subst Env.context S) Δ labels tc md
        (TContext.subst Env.context S) hprog hnotAliasS haddk
        (TContext.Equiv.refl (T := CoreLParams) _)
    exact ⟨Γtail, Δtail, StatementsHasType.cons _ _ _ _ _ _ _ _ _ _ _ _ hstmt htail,
      .cons hstmt htail
        (.typeDecl hprog hnotAliasS haddk (TContext.Equiv.refl _)) htailStrict,
      htailEq⟩
  case blockFlat =>
    intro _ _ _ _ _ _ _ _ _ Cgo _ _ _ _ ih1 habs he hf hcl h_ne hAN hS hfix hpsRig
    obtain ⟨hbodyAbs, hbodySeen, htyAll⟩ := ih1 habs he hf hcl h_ne hAN hS hfix hpsRig
    refine ⟨hbodyAbs, hbodySeen, fun hsc hinv Δ htr => ?_⟩
    obtain ⟨Γbody, Δbody, hty, htyStrict, -⟩ := htyAll hsc hinv Δ htr
    exact ⟨Cgo, Γbody, Δbody, hty, htyStrict⟩
  case blockScope =>
    intro Cx Envpre bss acc labels _ _ bss' Ego Cgo _ hg ih1 habs he hf hcl h_ne hAN hS hfix hpsRig
    obtain ⟨hbodyAbs, hbodySeen, htyAll⟩ :=
      ih1 habs
      (pushEmptyContext_preserves_TEnvWF (T := CoreLParams) Envpre he) hf
      (MonoScope_of_findEq
        (pushEmptyContext_context_FindEq (T := CoreLParams) Envpre) hcl)
      (TEnv.pushEmptyContext_types_ne_nil (T := CoreLParams) Envpre)
      hAN hS hfix hpsRig
    refine ⟨hbodyAbs, hbodySeen, fun hsc hinv Δ htr => ?_⟩
    obtain ⟨Γbody, Δbody, hty, htyStrict, -⟩ := htyAll hsc hinv Δ htr
    obtain ⟨Γout', hty', htyStrict', -⟩ :=
      StatementsSideConditionsΔ.input_ctx_FindEq htyStrict
        (TContext.FindEq.subst_subst S
          (pushEmptyContext_context_FindEq (T := CoreLParams) Envpre).symm)
    exact ⟨Cgo, Γout', Δbody, hty', htyStrict'⟩

/-- Input soundness under the ambient rigid names `ambientRigids`: statements the checker accepts,
    as written, satisfy the typechecker spec in the `S`-applied input scope, with side-condition
    evidence, and the spec's output scope agrees by lookup with the checker's under `S`.
    The hypotheses mean: `S` is well formed, absorbs the checker's final substitution, and fixes
    every rigid type variable of `C`; it moves no parameter that the ambient rigid names rename
    (`h_np`); the input environment and function table are well formed; the input scope holds
    only monotypes (`h_mono`) and is a nonempty stack (`h_types_ne`); no alias is named after a
    registered type (`h_aliasNames`); the accepted output passes the annotation check under `S`
    (`h_sweep`); and every ambient rigid name is a rigid type variable of `C` (`h_rig`). -/
theorem Statement.typeCheckAux_sound_visible_withSource
    (ambientRigids : RigidNames)
    (C C' : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program)
    (op : Option Procedure) (ss ss' : List Statement) (S : Subst)
    (h : Statement.typeCheckAux C Env P op ss = .ok (ss', Env', C'))
    (h_absorbs : Subst.absorbs S Env'.stateSubstInfo.subst) (h_Swf : SubstWF S)
    (h_np : NoParamRange ambientRigids S)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_mono : MonoScope Env.context)
    (h_types_ne : Env.context.types ≠ [])
    (h_aliasNames : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_sweep : SweepAt C S ss')
    (h_rigidFixed : ∀ v ∈ C.rigidTypeVars, LMonoTy.subst S (.ftvar v) = .ftvar v)
    (h_rig : ∀ x ∈ ambientRigids.map Prod.fst, x ∈ C.rigidTypeVars) :
    ∃ Γ' Δ', ∃ hty :
      StatementsHasType P C (TContext.subst Env.context S)
        (fun _ => none) [] ss C' Γ' Δ',
      StatementsSideConditionsΔ ambientRigids hty ∧
        TContext.FindEq (T := CoreLParams) Γ' (TContext.subst Env'.context S) := by
  obtain ⟨_, hgo⟩ := typeCheckAux_ok_inv h
  have hS : ∀ ss_proc, ss' = ([] : List Statement).reverse ++ ss_proc → SweepAt C S ss_proc := by
    intro ss_proc hshape
    simp only [List.reverse_nil, List.nil_append] at hshape
    subst ss_proc
    exact h_sweep
  obtain ⟨-, -, hall⟩ := go_input_sound_withSource P op S C Env ss [] [] ss' Env' C' hgo
    h_absorbs h_Swf h_np h_env h_fac h_mono h_types_ne h_aliasNames hS h_rigidFixed h_rig
  have hsc0 : ScopeAvoids (ambientRigids.map Prod.fst) []
      (WrittenTyVarScope.initState C.rigidTypeVars (Statement.usedTyVars Env) ss) :=
    ⟨fun _ hp => absurd hp List.not_mem_nil, fun x hx =>
      List.mem_append_left _ (List.mem_append_right _ (h_rig x hx))⟩
  have hinv0 : ScopeAdmissible C.rigidTypeVars []
      (WrittenTyVarScope.initState C.rigidTypeVars (Statement.usedTyVars Env) ss) :=
    ⟨fun _ _ => rfl, fun _ hp => absurd hp List.not_mem_nil,
      fun _ hp => absurd hp List.not_mem_nil⟩
  obtain ⟨Γ', Δ', hty, hstrict, hEq⟩ :=
    hall hsc0 hinv0 (fun _ => none) (WrittenEnv.Tracks.empty S _)
  exact ⟨Γ', Δ', hty, hstrict, hEq⟩

/-- Input soundness under the ambient rigid names `ambientRigids`: accepted statements, as
    written, satisfy the typechecker spec in the input scope substituted by the checker's final
    substitution, with side-condition evidence, and the spec's output scope agrees by lookup with
    the substituted checker's. The hypotheses `h_sweep`, `h_rigidFixed` and `h_np` are stated for
    that substitution. -/
private theorem Statement.typeCheckAux_sound_visible_withFactories
    (ambientRigids : RigidNames)
    (C C' : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program)
    (op : Option Procedure) (ss ss' : List Statement)
    (h : Statement.typeCheckAux C Env P op ss = .ok (ss', Env', C'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_mono : MonoScope Env.context)
    (h_types_ne : Env.context.types ≠ [])
    (h_aliasNames : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_sweep : SweepAt C Env'.stateSubstInfo.subst ss')
    (h_rigidFixed : ∀ v ∈ C.rigidTypeVars,
      LMonoTy.subst Env'.stateSubstInfo.subst (.ftvar v) = .ftvar v)
    (h_np : NoParamRange ambientRigids Env'.stateSubstInfo.subst)
    (h_rig : ∀ x ∈ ambientRigids.map Prod.fst, x ∈ C.rigidTypeVars) :
    ∃ Γ' Δ', ∃ hty :
      StatementsHasType P C
        (TContext.subst Env.context Env'.stateSubstInfo.subst) (fun _ => none) [] ss C' Γ' Δ',
      StatementsSideConditionsΔ ambientRigids hty ∧
        TContext.FindEq (T := CoreLParams) Γ'
          (TContext.subst Env'.context Env'.stateSubstInfo.subst) := by
  obtain ⟨Γ', Δ', hty, hstrict, hEq⟩ :=
    Statement.typeCheckAux_sound_visible_withSource ambientRigids C C' Env Env' P op ss ss'
      Env'.stateSubstInfo.subst h (Subst.absorbs_refl _ Env'.stateSubstInfo.isWF)
      Env'.stateSubstInfo.isWF h_np h_env h_fac h_mono h_types_ne h_aliasNames h_sweep h_rigidFixed
      h_rig
  exact ⟨Γ', Δ', hty, hstrict, hEq⟩

/-- Input soundness under the ambient rigid names `ambientRigids`, without side-condition
    evidence: accepted statements, as written, satisfy the typechecker spec in the substituted
    input scope, and the spec's output scope agrees by lookup with the substituted checker's.
    It has the same hypotheses. -/
private theorem Statement.typeCheckAux_sound_visible
    (ambientRigids : RigidNames)
    (C C' : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program)
    (op : Option Procedure) (ss ss' : List Statement)
    (h : Statement.typeCheckAux C Env P op ss = .ok (ss', Env', C'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_mono : MonoScope Env.context)
    (h_types_ne : Env.context.types ≠ [])
    (h_aliasNames : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_sweep : SweepAt C Env'.stateSubstInfo.subst ss')
    (h_rigidFixed : ∀ v ∈ C.rigidTypeVars,
      LMonoTy.subst Env'.stateSubstInfo.subst (.ftvar v) = .ftvar v)
    (h_np : NoParamRange ambientRigids Env'.stateSubstInfo.subst)
    (h_rig : ∀ x ∈ ambientRigids.map Prod.fst, x ∈ C.rigidTypeVars) :
    ∃ Γ' Δ',
      StatementsHasType P C
        (TContext.subst Env.context Env'.stateSubstInfo.subst) (fun _ => none) [] ss C' Γ' Δ' ∧
      TContext.FindEq (T := CoreLParams) Γ'
        (TContext.subst Env'.context Env'.stateSubstInfo.subst) := by
  obtain ⟨Γ', Δ', hty, -, hEq⟩ :=
    Statement.typeCheckAux_sound_visible_withFactories ambientRigids
      C C' Env Env' P op ss ss' h h_env h_fac h_mono h_types_ne h_aliasNames h_sweep h_rigidFixed
      h_np h_rig
  exact ⟨Γ', Δ', hty, hEq⟩

/-- Input soundness: an accepted statement list, as written, satisfies the typechecker spec in
    the input scope substituted by the checker's final substitution, and the spec's output scope
    agrees by lookup with the substituted checker's. The hypotheses mean: the input environment
    and function table are well formed; the input scope holds only monotypes (`h_mono`) and is a
    nonempty stack (`h_types_ne`); no alias is named after a registered type (`h_aliasNames`);
    the accepted output passes the annotation check under the final substitution (`h_sweep`);
    and that substitution fixes every rigid type variable (`h_rigidFixed`). -/
theorem Statement.typeCheckAux_sound
    (C C' : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program)
    (op : Option Procedure) (ss ss' : List Statement)
    (h : Statement.typeCheckAux C Env P op ss = .ok (ss', Env', C'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_mono : MonoScope Env.context)
    (h_types_ne : Env.context.types ≠ [])
    (h_aliasNames : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_sweep : SweepAt C Env'.stateSubstInfo.subst ss')
    (h_rigidFixed : ∀ v ∈ C.rigidTypeVars,
      LMonoTy.subst Env'.stateSubstInfo.subst (.ftvar v) = .ftvar v) :
    ∃ Γ' Δ',
      StatementsHasType P C
        (TContext.subst Env.context Env'.stateSubstInfo.subst) (fun _ => none) [] ss C' Γ' Δ' ∧
      TContext.FindEq (T := CoreLParams) Γ'
        (TContext.subst Env'.context Env'.stateSubstInfo.subst) :=
  Statement.typeCheckAux_sound_visible [] C C' Env Env' P op ss ss' h h_env h_fac h_mono
    h_types_ne h_aliasNames h_sweep h_rigidFixed (fun _ _ hv => absurd hv List.not_mem_nil)
    (fun _ hx => absurd hx List.not_mem_nil)

/-! ## Well-typed statements: scope transport, deskolemization, programs and tables -/

section WellTypedTransport

/-- A well-typed extended command stores only monotypes when its input scopes do. -/
private theorem TypeSpec.CmdExtWellTyped.monoScope {C : LContext CoreLParams} {P : Program}
    {ts ts' : TypeScopes} {c : Command} (h : CmdExtWellTyped C P ts c ts')
    (hmono : ∀ z tz, ts.find? z = some tz → LTy.boundVars tz = []) :
    ∀ z tz, ts'.find? z = some tz → LTy.boundVars tz = [] := by
  cases h with
  | cmd _ _ hc =>
    cases hc with
    | init_det x _ _ mty _ _ _ _ _ _ _ hEqv | init_nondet x _ mty _ _ _ _ _ hEqv =>
      intro z tz hz
      rw [hEqv.find? z] at hz
      by_cases hzx : z = x
      · subst hzx
        rw [HMaps.find?_insert_self] at hz
        cases hz
        rfl
      · rw [HMaps.find?_insert_ne _ _ _ _ hzx] at hz
        exact hmono z tz hz
    | set_det _ _ _ _ _ _ _ hEqv | set_nondet _ _ _ _ _ hEqv | assert _ _ _ _ _ hEqv
    | assume _ _ _ _ _ hEqv | cover _ _ _ _ _ hEqv =>
      intro z tz hz
      rw [hEqv.find? z] at hz
      exact hmono z tz hz
  | call _ _ _ _ _ _ _ _ _ _ _ _ _ _ hEqv =>
    intro z tz hz
    rw [hEqv.find? z] at hz
    exact hmono z tz hz


/-! ### Deskolemization -/

/-- Scope deskolemization respects equivalent variable scopes on the source side. -/
private theorem DeskolemizesScope.of_equiv_types {σ : RigidNames} {ts tsc ts' : TypeScopes}
    (hEqv : HMaps.Equiv tsc ts) (h : DeskolemizesScope σ { types := ts } { types := ts' }) :
    DeskolemizesScope σ { types := tsc } { types := ts' } :=
  DeskolemizesScope.of_equiv_left σ _ { types := ts } _ ⟨hEqv, rfl⟩ h

/-- A `call` argument condition (a looked-up bare variable or a well-typed expression)
    survives deskolemizing the argument, its type, the scopes and the context. -/
private theorem callInputMatch_deskolemize (σ : RigidNames) (hpfx : RigidNamesPrefixed σ)
    {Csk Crig : LContext CoreLParams} {ts ts' : TypeScopes} (hamb : AmbientDeskol σ Csk Crig)
    (hwf : FactorySigWF (T := CoreLParams) Csk.functions)
    (hsafe : FactorySigDeskolSafe σ Csk.functions)
    (hsc : DeskolemizesScope σ { types := ts } { types := ts' })
    (e : Expression.Expr) (mty : LMonoTy)
    (h : match e with
      | .fvar _ x none => ts.find? x = some (.forAll [] mty)
      | e => ExprWellTyped Csk ts e mty)
    (hc : ConstTysFixed σ e) :
    match mapExprTys (deskolemizeTy σ) e with
    | .fvar _ x none => ts'.find? x = some (.forAll [] (deskolemizeTy σ mty))
    | e => ExprWellTyped Crig ts' e (deskolemizeTy σ mty) := by
  have hfind : ∀ x, ts'.find? x = (ts.find? x).map (mapLTyTys (deskolemizeTy σ)) := hsc.2
  cases e with
  | fvar m x ann =>
    cases ann with
    | none =>
      simp only [mapExprTys, LExpr.replaceUserProvidedType, Option.map_none]
      have hx : ts.find? x = some (.forAll [] mty) := h
      rw [hfind x, hx]
      rfl
    | some ty => exact TypeSpec.ExprWellTyped.deskolemize σ hpfx hamb hsc hwf hsafe hc h
  | op | const | bvar | abs | quant | app | ite | eq =>
    exact TypeSpec.ExprWellTyped.deskolemize σ hpfx hamb hsc hwf hsafe hc h

/-- A well-typed extended `call` command, deskolemized, is well typed in a context making `σ`'s
    names rigid, from any deskolemization of its input scopes, when deskolemizing fixes the
    signatures of the procedures it calls. -/
private theorem TypeSpec.CmdExtWellTyped.deskolemize_call (σ : RigidNames)
    (hpfx : RigidNamesPrefixed σ) {P : Program} {Csk Crig : LContext CoreLParams}
    {ts ts' tsOut : TypeScopes} {pname : String} {tyArgs : Option (List Expression.Ty)}
    {callArgs : List (CallArg Expression)} {md : MetaData Expression}
    (hamb : AmbientDeskol σ Csk Crig) (hwf : FactorySigWF (T := CoreLParams) Csk.functions)
    (hsafe : FactorySigDeskolSafe σ Csk.functions)
    (hsc : DeskolemizesScope σ { types := ts } { types := ts' })
    (hcalls : CalledProcedureSignaturesFixed σ P (.call pname tyArgs callArgs md))
    (hlit : ∀ e ∈ Statement.cmdExprs (.call pname tyArgs callArgs md), ConstTysFixed σ e)
    (h : CmdExtWellTyped Csk P ts (.call pname tyArgs callArgs md) tsOut) :
    ∃ tsOut', CmdExtWellTyped Crig P ts' (mapCmdTys (deskolemizeTy σ)
        (.call pname tyArgs callArgs md)) tsOut' ∧
      DeskolemizesScope σ { types := tsOut } { types := tsOut' } := by
  have hfind : ∀ x, ts'.find? x = (ts.find? x).map (mapLTyTys (deskolemizeTy σ)) := hsc.2
  have hsame : ∀ {tsc : TypeScopes}, HMaps.Equiv tsc ts →
      DeskolemizesScope σ { types := tsc } { types := ts' } :=
    fun hEqv => DeskolemizesScope.of_equiv_types hEqv hsc
  cases h with
    | call pname tyArgs callArgs proc md callσ _ hproc hcall hlhs hin hout hinst hkind hEqv =>
  let callσ' := callσ.map (fun q => (q.1, deskolemizeTy σ q.2))
  have hinput := CallArg.getInputExprs_map_types (deskolemizeTy σ) callArgs
  have hlhsMap := CallArg.getLhs_map_congr (mapExprTys (deskolemizeTy σ)) callArgs
  have hsubst (formal : LMonoTy) (hfixed : deskolemizeTy σ formal = formal) :
      LMonoTy.subst (HMaps.ofScopes [callσ']) formal =
        deskolemizeTy σ (LMonoTy.subst (HMaps.ofScopes [callσ]) formal) := by
    symm
    apply deskolemizeTy_subst_eq_subst σ (HMaps.ofScopes [callσ]) (HMaps.ofScopes [callσ'])
      formal hfixed
    intro x hx
    cases hfind0 : Strata.Util.HMap.find? (Strata.Util.HMap.ofList callσ) x with
    | none =>
      have hfind1 : Strata.Util.HMap.find? (Strata.Util.HMap.ofList callσ') x = none := by
        simp only [callσ', Strata.Util.HMap.find?_ofList_map_snd, hfind0, Option.map_none]
      have hfindS : HMaps.find? (HMaps.ofScopes [callσ]) x = none := by
        simp only [HMaps.ofScopes, List.map_cons, List.map_nil, HMaps.find?_single_scope,
          hfind0]
      have hfindS' : HMaps.find? (HMaps.ofScopes [callσ']) x = none := by
        simp only [HMaps.ofScopes, List.map_cons, List.map_nil, HMaps.find?_single_scope,
          hfind1]
      rw [LMonoTy.subst_ftvar_of_none hfindS, LMonoTy.subst_ftvar_of_none hfindS']
      exact deskolemizeTy_ftvar σ x
    | some ty =>
      have hfind1 : Strata.Util.HMap.find? (Strata.Util.HMap.ofList callσ') x =
          some (deskolemizeTy σ ty) := by
        simp only [callσ', Strata.Util.HMap.find?_ofList_map_snd, hfind0, Option.map_some]
      have hfindS : HMaps.find? (HMaps.ofScopes [callσ]) x = some ty := by
        simp only [HMaps.ofScopes, List.map_cons, List.map_nil, HMaps.find?_single_scope,
          hfind0]
      have hfindS' : HMaps.find? (HMaps.ofScopes [callσ']) x = some (deskolemizeTy σ ty) := by
        simp only [HMaps.ofScopes, List.map_cons, List.map_nil, HMaps.find?_single_scope,
          hfind1]
      rw [LMonoTy.subst_ftvar_of_some hfindS, LMonoTy.subst_ftvar_of_some hfindS']
  have hpmem : pname ∈ CmdExt.calledProcedureNames (.call pname tyArgs callArgs md) := by
    simp only [CmdExt.calledProcedureNames_call, List.mem_singleton]
  have hsig := hcalls pname hpmem proc hproc
  have hinFixed : ∀ e ∈ CallArg.getInputExprs callArgs, ConstTysFixed σ e := hlit
  refine ⟨ts', ?_, hsame hEqv⟩
  change CmdExtWellTyped Crig P ts'
    (.call pname (tyArgs.map (·.map (mapLTyTys (deskolemizeTy σ))))
      (callArgs.map (CallArg.mapInput (mapExprTys (deskolemizeTy σ)))) md) ts'
  refine .call ts' pname _ (callArgs.map (CallArg.mapInput (mapExprTys (deskolemizeTy σ))))
    proc md callσ' ts' hproc ?_ ?_ ?_ ?_ ?_ ?_ (HMaps.Equiv.refl _)
  · exact hcall.transfer (.boolConst Core.valueLoc true) hproc hproc rfl rfl
      (CallArg.map_mapInput_const _ _ callArgs)
  · intro v hv
    rw [hlhsMap] at hv
    cases hv0 : ts.find? v with
    | none =>
      have hsome := hlhs v hv
      rw [hv0] at hsome
      simp only [Option.isSome_none, Bool.false_eq_true] at hsome
    | some ty =>
      rw [hfind v, hv0]
      rfl
  · intro i hi hj
    have hi0 : i < (CallArg.getInputExprs callArgs).length := by
      simpa only [hinput, List.length_map] using hi
    have heq :
        (CallArg.getInputExprs
          (callArgs.map (CallArg.mapInput (mapExprTys (deskolemizeTy σ)))))[i] =
          mapExprTys (deskolemizeTy σ) (CallArg.getInputExprs callArgs)[i] :=
      (getElem_congr_coll hinput).trans (List.getElem_map (mapExprTys (deskolemizeTy σ)))
    have hmem : proc.header.inputs.values[i] ∈
        proc.header.inputs.values ++ proc.header.outputs.values :=
      List.mem_append_left _ (List.getElem_mem hj)
    rw [hsubst proc.header.inputs.values[i] (hsig _ hmem), heq]
    exact callInputMatch_deskolemize σ hpfx hamb hwf hsafe hsc _ _
      (hin i hi0 hj) (hinFixed _ (List.getElem_mem hi0))
  · intro i hi hj
    have hi0 : i < (CallArg.getLhs callArgs).length := by
      simpa only [hlhsMap] using hi
    have heq :
        (CallArg.getLhs
          (callArgs.map (CallArg.mapInput (mapExprTys (deskolemizeTy σ)))))[i] =
          (CallArg.getLhs callArgs)[i] := by
      simp only [hlhsMap]
    have hmem : proc.header.outputs.values[i] ∈
        proc.header.inputs.values ++ proc.header.outputs.values :=
      List.mem_append_right _ (List.getElem_mem hj)
    rw [hsubst proc.header.outputs.values[i] (hsig _ hmem), heq, hfind, hout i hi0 hj]
    rfl
  · rw [hinst, Option.map_some, List.map_map]
    refine congrArg some (List.map_congr_left fun a _ => ?_)
    simp only [Function.comp_apply, mapLTyTys]
    rw [hsubst (.ftvar a) (deskolemizeTy_ftvar σ a)]
  · intro tys' htys' ty' hty'
    obtain ⟨tys, htys, rfl⟩ := Option.map_eq_some_iff.mp htys'
    obtain ⟨ty0, hty0, rfl⟩ := List.mem_map.mp hty'
    cases ty0 with
    | forAll vs mty =>
      exact WellKindedTy_deskolemizeTy hamb mty (hkind tys htys (.forAll vs mty) hty0)

/-- A well-typed extended command, deskolemized, is well typed in a context making `σ`'s names
    rigid, from any deskolemization of its input scopes, ending in a deskolemization of its
    output scopes, when deskolemizing fixes the signatures of the procedures it calls. -/
private theorem TypeSpec.CmdExtWellTyped.deskolemize (σ : RigidNames) (hpfx : RigidNamesPrefixed σ)
    {P : Program} {Csk Crig : LContext CoreLParams} {ts ts' tsOut : TypeScopes} {c : Command}
    (hamb : AmbientDeskol σ Csk Crig) (hwf : FactorySigWF (T := CoreLParams) Csk.functions)
    (hsafe : FactorySigDeskolSafe σ Csk.functions)
    (hsc : DeskolemizesScope σ { types := ts } { types := ts' })
    (hcalls : CalledProcedureSignaturesFixed σ P c)
    (hlit : ∀ e ∈ Statement.cmdExprs c, ConstTysFixed σ e) (h : CmdExtWellTyped Csk P ts c tsOut) :
    ∃ tsOut', CmdExtWellTyped Crig P ts' (mapCmdTys (deskolemizeTy σ) c) tsOut' ∧
      DeskolemizesScope σ { types := tsOut } { types := tsOut' } := by
  have hfind : ∀ x, ts'.find? x = (ts.find? x).map (mapLTyTys (deskolemizeTy σ)) := hsc.2
  have hsame : ∀ {tsc : TypeScopes}, HMaps.Equiv tsc ts →
      DeskolemizesScope σ { types := tsc } { types := ts' } :=
    fun hEqv => DeskolemizesScope.of_equiv_types hEqv hsc
  have hexpr : ∀ {e : Expression.Expr} {mty : LMonoTy}, ConstTysFixed σ e →
      ExprWellTyped Csk ts e mty →
      ExprWellTyped Crig ts' (mapExprTys (deskolemizeTy σ) e) (deskolemizeTy σ mty) :=
    fun hc he => TypeSpec.ExprWellTyped.deskolemize σ hpfx hamb hsc hwf hsafe hc he
  have hbool : ∀ {e : Expression.Expr}, ConstTysFixed σ e → ExprWellTyped Csk ts e .bool →
      ExprWellTyped Crig ts' (mapExprTys (deskolemizeTy σ) e) .bool := by
    intro e hc he
    have hd := hexpr hc he
    rwa [deskolemizeTy_bool hpfx] at hd
  cases c with
  | cmd cc =>
    cases h with
    | cmd _ _ hc =>
      cases hc with
      | init_det x xty e mty md _ hnone hfv hxty hwk he hEqv =>
        subst hxty
        have hnone' : ts'.find? x = none := by
          rw [hfind x, hnone]
          rfl
        have hfv' : x ∉ HasFvars.getFvars (P := Expression) (mapExprTys (deskolemizeTy σ) e) := by
          rw [getFvars_mapExprTys]
          exact hfv
        refine ⟨ts'.insert x (.forAll [] (deskolemizeTy σ mty)), ?_,
          DeskolemizesScope.of_equiv_types hEqv (DeskolemizesScope.insert σ _ _ hsc x mty)⟩
        have hexp := hexpr (hlit e Statement.mem_cmdExprs_init_det) he
        exact .cmd _ _ _ (.init_det _ _ _ _ _ _ _ hnone' hfv' rfl
          (WellKindedTy_deskolemizeTy hamb mty hwk) hexp (HMaps.Equiv.refl _))
      | init_nondet x xty mty md _ hnone hxty hwk hEqv =>
        subst hxty
        have hnone' : ts'.find? x = none := by
          rw [hfind x, hnone]
          rfl
        refine ⟨ts'.insert x (.forAll [] (deskolemizeTy σ mty)), ?_,
          DeskolemizesScope.of_equiv_types hEqv (DeskolemizesScope.insert σ _ _ hsc x mty)⟩
        exact .cmd _ _ _ (.init_nondet _ _ _ _ _ _ hnone' rfl
          (WellKindedTy_deskolemizeTy hamb mty hwk) (HMaps.Equiv.refl _))
      | set_det x mty e md _ hx he hEqv =>
        have hx' : ts'.find? x = some (.forAll [] (deskolemizeTy σ mty)) := by
          rw [hfind x, hx]
          rfl
        have hexp := hexpr (hlit e Statement.mem_cmdExprs_set_det) he
        exact ⟨ts', .cmd _ _ _ (.set_det _ _ _ _ _ _ hx' hexp (HMaps.Equiv.refl _)),
          hsame hEqv⟩
      | set_nondet x mty md _ hx hEqv =>
        have hx' : ts'.find? x = some (.forAll [] (deskolemizeTy σ mty)) := by
          rw [hfind x, hx]
          rfl
        exact ⟨ts', .cmd _ _ _ (.set_nondet _ _ _ _ _ hx' (HMaps.Equiv.refl _)), hsame hEqv⟩
      | assert l e md _ he hEqv =>
        have hb := hbool (hlit e Statement.mem_cmdExprs_assert) he
        exact ⟨ts', .cmd _ _ _ (.assert _ _ _ _ _ hb (HMaps.Equiv.refl _)),
          hsame hEqv⟩
      | assume l e md _ he hEqv =>
        have hb := hbool (hlit e Statement.mem_cmdExprs_assume) he
        exact ⟨ts', .cmd _ _ _ (.assume _ _ _ _ _ hb (HMaps.Equiv.refl _)),
          hsame hEqv⟩
      | cover l e md _ he hEqv =>
        have hb := hbool (hlit e Statement.mem_cmdExprs_cover) he
        exact ⟨ts', .cmd _ _ _ (.cover _ _ _ _ _ hb (HMaps.Equiv.refl _)),
          hsame hEqv⟩
  | call pname tyArgs callArgs md =>
    exact TypeSpec.CmdExtWellTyped.deskolemize_call σ hpfx hamb hwf hsafe hsc hcalls hlit h

mutual

/-- A well-typed statement, deskolemized, is well typed in a context making `σ`'s names rigid,
    from any deskolemization of its input scopes, when deskolemizing fixes every procedure
    signature of the program; the output context and scopes are again related. -/
private theorem TypeSpec.StatementWellTyped.deskolemize_aux (σ : RigidNames)
    (hpfx : RigidNamesPrefixed σ) {P : Program}
    (hcalls : ∀ c, CalledProcedureSignaturesFixed σ P c) {Csk Cfin : LContext CoreLParams}
    {ts tsFin : TypeScopes} {L : List String} {s : Statement}
    (h : StatementWellTyped P Csk ts L s Cfin tsFin) {Crig : LContext CoreLParams}
    {ts' : TypeScopes} (hamb : AmbientDeskol σ Csk Crig)
    (hwf : FactorySigWF (T := CoreLParams) Csk.functions)
    (hsafe : FactorySigDeskolSafe σ Csk.functions)
    (hsc : DeskolemizesScope σ { types := ts } { types := ts' }) :
    (∀ p ∈ σ, p.2 ∉ stmtLitTyNames s) →
    ∃ Co tso, StatementWellTyped P Crig ts' L (mapStmtTys (deskolemizeTy σ) s) Co tso ∧
      AmbientDeskol σ Cfin Co ∧ FactorySigWF (T := CoreLParams) Cfin.functions ∧
      FactorySigDeskolSafe σ Cfin.functions ∧
      DeskolemizesScope σ { types := tsFin } { types := tso } :=
  match h with
  | .cmd _ _ _ c _ hc => fun hlit => by
    obtain ⟨tso, hc', hsco⟩ :=
      TypeSpec.CmdExtWellTyped.deskolemize σ hpfx hamb hwf hsafe hsc (hcalls c)
        (ConstTysFixed_of_stmtLitTyNames_cmd hlit) hc
    rw [mapStmtTys_cmd]
    exact ⟨Crig, tso, .cmd _ _ _ _ _ hc', hamb, hwf, hsafe, hsco⟩
  | .block _ _ _ _ _ _ _ _ _ hl hb hEqv => fun hlit => by
    obtain ⟨_, _, hb', -⟩ :=
      TypeSpec.StatementsWellTyped.deskolemize_aux σ hpfx hcalls hb hamb hwf hsafe hsc
        (stmtLitTyNames_block_body hlit)
    rw [mapStmtTys_block]
    exact ⟨Crig, ts', .block _ _ _ _ _ _ _ _ _ hl hb' (HMaps.Equiv.refl _), hamb, hwf, hsafe,
      DeskolemizesScope.of_equiv_types hEqv hsc⟩
  | .ite_det _ _ _ _ _ _ _ cond _ _ _ _ hc ht he hEqv => fun hlit => by
    obtain ⟨hlitc, hlitt, hlite⟩ := stmtLitTyNames_ite_parts hlit
    obtain ⟨_, _, ht', -⟩ :=
      TypeSpec.StatementsWellTyped.deskolemize_aux σ hpfx hcalls ht hamb hwf hsafe hsc hlitt
    obtain ⟨_, _, he', -⟩ :=
      TypeSpec.StatementsWellTyped.deskolemize_aux σ hpfx hcalls he hamb hwf hsafe hsc hlite
    have hcond : ConstTysFixed σ cond := hlitc cond (List.mem_singleton_self _)
    have hc' := TypeSpec.ExprWellTyped.deskolemize σ hpfx hamb hsc hwf hsafe hcond hc
    rw [deskolemizeTy_bool hpfx] at hc'
    rw [mapStmtTys_ite]
    exact ⟨Crig, ts', .ite_det _ _ _ _ _ _ _ _ _ _ _ _ hc' ht' he' (HMaps.Equiv.refl _), hamb,
      hwf, hsafe, DeskolemizesScope.of_equiv_types hEqv hsc⟩
  | .ite_nondet _ _ _ _ _ _ _ _ _ _ _ ht he hEqv => fun hlit => by
    obtain ⟨-, hlitt, hlite⟩ := stmtLitTyNames_ite_parts hlit
    obtain ⟨_, _, ht', -⟩ :=
      TypeSpec.StatementsWellTyped.deskolemize_aux σ hpfx hcalls ht hamb hwf hsafe hsc hlitt
    obtain ⟨_, _, he', -⟩ :=
      TypeSpec.StatementsWellTyped.deskolemize_aux σ hpfx hcalls he hamb hwf hsafe hsc hlite
    rw [mapStmtTys_ite]
    exact ⟨Crig, ts', .ite_nondet _ _ _ _ _ _ _ _ _ _ _ ht' he' (HMaps.Equiv.refl _), hamb, hwf,
      hsafe, DeskolemizesScope.of_equiv_types hEqv hsc⟩
  | .loop _ _ _ _ _ guard measure invariants _ _ _ hg hm hi hb hEqv => fun hlit => by
    obtain ⟨hlitl, hlitb⟩ := stmtLitTyNames_loop_parts hlit
    obtain ⟨_, _, hb', -⟩ :=
      TypeSpec.StatementsWellTyped.deskolemize_aux σ hpfx hcalls hb hamb hwf hsafe hsc hlitb
    have hexpr : ∀ {e : Expression.Expr} {mty : LMonoTy}, ConstTysFixed σ e →
        ExprWellTyped Csk ts e mty →
        ExprWellTyped Crig ts' (mapExprTys (deskolemizeTy σ) e) (deskolemizeTy σ mty) :=
      fun hc he => TypeSpec.ExprWellTyped.deskolemize σ hpfx hamb hsc hwf hsafe hc he
    have hg' : ∀ g, guard.map (mapExprTys (deskolemizeTy σ) ·) = .det g →
        ExprWellTyped Crig ts' g .bool := by
      intro g hgd
      cases guard with
      | nondet => simp only [ExprOrNondet.map, reduceCtorEq] at hgd
      | det g0 =>
        simp only [ExprOrNondet.map, ExprOrNondet.det.injEq] at hgd
        subst hgd
        have hmem : g0 ∈ Statement.loopExprs (.det g0) measure invariants := by
          simp only [Statement.loopExprs, ExprOrNondet.toList, List.mem_append,
            List.mem_singleton, true_or]
        have hd := hexpr (hlitl g0 hmem) (hg g0 rfl)
        rwa [deskolemizeTy_bool hpfx] at hd
    have hm' : ∀ m, measure.map (mapExprTys (deskolemizeTy σ) ·) = some m →
        ExprWellTyped Crig ts' m .int := by
      intro m hmm
      obtain ⟨m0, hm0, rfl⟩ := Option.map_eq_some_iff.mp hmm
      have hmem : m0 ∈ Statement.loopExprs guard measure invariants := by
        simp only [Statement.loopExprs, List.mem_append, Option.mem_toList, hm0, true_or, or_true]
      have hd := hexpr (hlitl m0 hmem) (hm m0 hm0)
      rwa [deskolemizeTy_int hpfx] at hd
    have hi' : ∀ p, p ∈ invariants.map (fun (l, e) => (l, mapExprTys (deskolemizeTy σ) e)) →
        ExprWellTyped Crig ts' p.2 .bool := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have hmem : q.2 ∈ Statement.loopExprs guard measure invariants := by
        simp only [Statement.loopExprs, List.mem_append, List.mem_map]
        exact Or.inr ⟨q, hq, rfl⟩
      have hd := hexpr (hlitl q.2 hmem) (hi q hq)
      rwa [deskolemizeTy_bool hpfx] at hd
    rw [mapStmtTys_loop]
    exact ⟨Crig, ts', .loop _ _ _ _ _ _ _ _ _ _ _ hg' hm' hi' hb' (HMaps.Equiv.refl _), hamb,
      hwf, hsafe, DeskolemizesScope.of_equiv_types hEqv hsc⟩
  | .exit _ _ _ _ _ _ hl hEqv => fun _ => by
    rw [mapStmtTys_exit]
    exact ⟨Crig, ts', .exit _ _ _ _ _ _ hl (HMaps.Equiv.refl _), hamb, hwf, hsafe,
      DeskolemizesScope.of_equiv_types hEqv hsc⟩
  | .typeDecl _ _ _ _ tc _ _ hn hadd hEqv => fun _ => by
    obtain ⟨Cnew', hadd', hamb'⟩ := addKnownTypeWithError_deskolemize σ _ Crig _ tc hamb hadd
    have hfun := Lambda.addKnownTypeWithError_functions_eq _ _ _ _ hadd
    rw [mapStmtTys_typeDecl]
    refine ⟨Cnew', ts', .typeDecl _ _ _ _ _ _ _ hn hadd' (HMaps.Equiv.refl _), hamb', ?_, ?_,
      DeskolemizesScope.of_equiv_types hEqv hsc⟩
    · rw [hfun]
      exact hwf
    · rw [hfun]
      exact hsafe

/-- A well-typed statement list, deskolemized, is well typed in a context making `σ`'s names
    rigid, from any deskolemization of its input scopes, when deskolemizing fixes every procedure
    signature of the program; the output context and scopes are again related. -/
private theorem TypeSpec.StatementsWellTyped.deskolemize_aux (σ : RigidNames)
    (hpfx : RigidNamesPrefixed σ) {P : Program}
    (hcalls : ∀ c, CalledProcedureSignaturesFixed σ P c) {Csk Cfin : LContext CoreLParams}
    {ts tsFin : TypeScopes} {L : List String} {ss : List Statement}
    (h : StatementsWellTyped P Csk ts L ss Cfin tsFin) {Crig : LContext CoreLParams}
    {ts' : TypeScopes} (hamb : AmbientDeskol σ Csk Crig)
    (hwf : FactorySigWF (T := CoreLParams) Csk.functions)
    (hsafe : FactorySigDeskolSafe σ Csk.functions)
    (hsc : DeskolemizesScope σ { types := ts } { types := ts' }) :
    (∀ p ∈ σ, p.2 ∉ stmtsLitTyNames ss) →
    ∃ Co tso, StatementsWellTyped P Crig ts' L (mapStmtsTys (deskolemizeTy σ) ss) Co tso ∧
      AmbientDeskol σ Cfin Co ∧ FactorySigWF (T := CoreLParams) Cfin.functions ∧
      FactorySigDeskolSafe σ Cfin.functions ∧
      DeskolemizesScope σ { types := tsFin } { types := tso } :=
  match h with
  | .nil _ _ _ _ hEqv => fun _ => by
    rw [mapStmtsTys_nil]
    exact ⟨Crig, ts', .nil _ _ _ _ (HMaps.Equiv.refl _), hamb, hwf, hsafe,
      DeskolemizesScope.of_equiv_types hEqv hsc⟩
  | .cons _ _ _ _ _ _ _ _ _ hs ht => fun hlit => by
    obtain ⟨hlits, hlitr⟩ := stmtsLitTyNames_cons_parts hlit
    obtain ⟨Cm, tsm, hs', hambm, hwfm, hsafem, hscm⟩ :=
      TypeSpec.StatementWellTyped.deskolemize_aux σ hpfx hcalls hs hamb hwf hsafe hsc hlits
    obtain ⟨Co, tso, ht', hambo, hwfo, hsafeo, hsco⟩ :=
      TypeSpec.StatementsWellTyped.deskolemize_aux σ hpfx hcalls ht hambm hwfm hsafem hscm hlitr
    rw [mapStmtsTys_cons]
    exact ⟨Co, tso, .cons _ _ _ _ _ _ _ _ _ hs' ht', hambo, hwfo, hsafeo, hsco⟩

end

/-- A statement list well typed under `C₀` with `σ`'s skolem constants registered stays well
    typed, deskolemized, under `C₀` with `σ`'s names made rigid, from any deskolemization of its
    input scopes. -/
theorem TypeSpec.StatementsWellTyped.deskolemize (σ : RigidNames) (hpfx : RigidNamesPrefixed σ)
    {P : Program} (hcalls : ∀ c, CalledProcedureSignaturesFixed σ P c)
    (C₀ : LContext CoreLParams) (hwf : FactorySigWF (T := CoreLParams) C₀.functions)
    (hsafe : FactorySigDeskolSafe σ C₀.functions)
    (hbase : FactorySigDeskolemizes σ C₀.functions C₀.functions)
    {ts tsOut : TypeScopes} {L : List String} {ss : List Statement} {Cout : LContext CoreLParams}
    (h : StatementsWellTyped P (addSkolemTypes C₀ σ) ts L ss Cout tsOut) {ts' : TypeScopes}
    (hsc : DeskolemizesScope σ { types := ts } { types := ts' })
    (hlit : ∀ p ∈ σ, p.2 ∉ stmtsLitTyNames ss) :
    ∃ Cout' tsOut', StatementsWellTyped P
      { C₀ with rigidTypeVars := C₀.rigidTypeVars ++ σ.map Prod.fst } ts' L
      (mapStmtsTys (deskolemizeTy σ) ss) Cout' tsOut' := by
  have hambRig : AmbientDeskol σ (addSkolemTypes C₀ σ)
      { C₀ with rigidTypeVars := C₀.rigidTypeVars ++ σ.map Prod.fst } :=
    ⟨fun x => addSkolemTypes_getElem?_congr C₀ _ σ (fun _ => rfl) x,
     rigidTypeVars_addSkolemTypes C₀ σ,
     by simpa only [addSkolemTypes] using hbase⟩
  have hwfSk : FactorySigWF (T := CoreLParams) (addSkolemTypes C₀ σ).functions := by
    simpa only [addSkolemTypes_functions] using hwf
  have hsafeSk : FactorySigDeskolSafe σ (addSkolemTypes C₀ σ).functions := by
    simpa only [addSkolemTypes_functions] using hsafe
  obtain ⟨Cout', tsOut', hd, -⟩ :=
    TypeSpec.StatementsWellTyped.deskolemize_aux σ hpfx hcalls h hambRig hwfSk hsafeSk hsc hlit
  exact ⟨Cout', tsOut', hd⟩

end WellTypedTransport

end SubstStability

end -- public section

end Core
