/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Preservation.SmallStep
import Strata.Languages.Core.ProgramProps
import Strata.Languages.Core.ProcedureProps
import Strata.Languages.Core.CallWF
import Strata.Languages.Core.CallWFProps
import Strata.Languages.Core.StatementProps
import Strata.Languages.Core.StatementSemanticsProps
import Strata.DL.Imperative.StmtCFGCallSemanticsProps
import Strata.DL.Imperative.InterpreterCallProps
import Strata.Util.ListMapProps
import Strata.DL.Lambda.LTyProps
import Strata.Languages.Core.ExpressionsProps
import all Strata.DL.Lambda.LTy
import all Strata.DL.Imperative.Cmd
import all Strata.Languages.Core.Procedure
import all Strata.DL.Lambda.LExprTypeEnv

/-! ## Progress for Core's small-step semantics

A configuration reachable from the start of a well-typed structured procedure body is finished,
steps, or runs a call whose callee never finishes. The semantics runs a call as one step whose
premise is a complete run of the callee body, so a callee that diverges, or whose body gets
stuck, leaves the caller with no step: that outcome is part of the conclusion, not a hypothesis.

Core's semantics also checks the type of each value a call returns to the caller's variables. A
step that fails the check does not exist, so the check must never fail on a well-typed program:
`callExit_check_holds`. The check needs no typing of the callee: a call frame starts each
output formal at the value of the caller variable it returns to, and a run keeps every slot at
its type.

Key results:
* `CalleesStructured`: every procedure of the program has a structured body or no body. A call to
  an opaque procedure (`Body.isOpaque`) runs its contract and steps.
* `ProgramWellTyped.calleesTyVarsScoped`: no undeclared type variables. Every type variable in a
  structured body's local declarations and call type arguments is a type parameter of its
  procedure; the typing relation of a procedure requires this.
* `CallDoesNotFinish`: a call is next to run, its entry succeeds, and its callee body has no
  complete run.
* `callExit_check_holds`: the values a well-typed call returns pass the call's check against the
  caller's variables.
* `coreStep_progress`: a well-typed configuration is finished, exiting, steps, or runs a call
  that does not finish.
* `CallRunsForever`: a call is next to run and every configuration reachable in its callee
  steps or again runs such a call.
* `coreStep_progress_forever`, `reachable_configs_progress_forever`: the same progress results
  with `CallRunsForever` in place of `CallDoesNotFinish`, for programs typed in empty ambient
  scopes. The procedures may have type parameters: a call runs an instance of its callee at
  ground type arguments, and `reachable_configs_progress_forever` starts a procedure at any
  ground instance.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

/-- A well-typed imperative command, with the type substitution `S` applied to its annotations,
    runs: in a store that conforms to its scopes with `S` applied and binds no variable they do
    not declare, a command whose `init` declares a ground type steps to some store. -/
private theorem CmdWellTyped.progress {C : LContext CoreLParams} {ts ts' : TypeScopes}
    {S : Subst} {c0 c : Cmd Expression} {F : Expression.Factory} {σ : CoreStore}
    (hc : CmdWellTyped C ts c0 ts')
    (hmap : (.cmd c : Command) = mapCmdTys (LMonoTy.subst S) (.cmd c0))
    (hground : ∀ x xty e md, c = .init x xty e md → LTy.GroundMono xty)
    (hs : StoreHasTyping F σ (ts.instVarTyping S)) (hfresh : StoreFresh σ ts.find?) :
    ∃ σ' evs, EvalCmdE Expression F σ c σ' evs := by
  have hvar := coreEvaluator_WellFormedSemanticEvalVar F
  cases hc with
  | init_det x xty e mty md ts' hfind hnot hxty hwk he hequiv =>
    subst hxty
    simp only [mapCmdTys_init, ExprOrNondet.map] at hmap
    cases hmap
    obtain ⟨τ, hτ, hg⟩ := hground x _ (.det _) md rfl
    cases hτ
    obtain ⟨v, -, -, hev⟩ := EvalCmdE.init_progress (md := md) (he.hasType_inst S hg) hs
      (hfresh x hfind) hvar
    exact ⟨_, _, hev⟩
  | init_nondet x xty mty md ts' hfind hxty hwk hequiv =>
    subst hxty
    simp only [mapCmdTys_init, ExprOrNondet.map] at hmap
    cases hmap
    obtain ⟨τ, hτ, hg⟩ := hground x _ .nondet md rfl
    cases hτ
    obtain ⟨v, hv⟩ := exists_valueOfTy_of_ground F hg
    exact ⟨_, _, .eval_init_unconstrained (InitState.of_update (hfresh x hfind)) hv hvar⟩
  | set_det x mty e md ts' hfind he hequiv =>
    simp only [mapCmdTys_set, ExprOrNondet.map] at hmap
    cases hmap
    have hx := TypeScopes.instVarTyping_of_find? (S := S) hfind
    obtain ⟨prev, -, hprev⟩ := hs x _ hx
    have hg : (LMonoTy.subst S mty).IsGround := isGround_of_valueOfTy hprev
    obtain ⟨v, -, -, hev⟩ := EvalCmdE.set_progress (md := md) hx (he.hasType_inst S hg) hs hvar
    exact ⟨_, _, hev⟩
  | set_nondet x mty md ts' hfind hequiv =>
    simp only [mapCmdTys_set, ExprOrNondet.map] at hmap
    cases hmap
    obtain ⟨prev, hprevx, hprev⟩ := hs x _ (TypeScopes.instVarTyping_of_find? (S := S) hfind)
    exact ⟨_, _, .eval_set_nondet (UpdateState.of_update hprevx)
      ⟨prev, _, hprevx, hprev, hprev⟩ hvar⟩
  | assert =>
    simp only [mapCmdTys_assert] at hmap
    cases hmap
    exact ⟨_, _, .eval_assert⟩
  | assume =>
    simp only [mapCmdTys_assume] at hmap
    cases hmap
    exact ⟨_, _, .eval_assume⟩
  | cover =>
    simp only [mapCmdTys_cover] at hmap
    cases hmap
    exact ⟨_, _, .eval_cover⟩

/-- An argument of a call, typed as the call's typing requires and with the type substitution
    `S` applied to its annotations, has its free variables bound and evaluates, in a store that
    conforms to the call's scopes with `S` applied, to a value of its type with `S` applied,
    when that type is ground. -/
private theorem inputArg_evaluable_typed {C : LContext CoreLParams} {ts : TypeScopes}
    {e : Expression.Expr}
    {mty : LMonoTy} {f : Expression.Factory} {σ : CoreStore} (S : Subst)
    (he : match e with
      | .fvar _ x none => ts.find? x = some (.forAll [] mty)
      | e => ExprWellTyped C ts e mty)
    (hground : (LMonoTy.subst S mty).IsGround) (hs : StoreHasTyping f σ (ts.instVarTyping S)) :
    SemanticStore.varsDefined
        (· ∈ HasFvars.getFvars (P := Expression) (mapExprTys (LMonoTy.subst S) e)) σ ∧
      ∃ v, Expression.eval f σ (mapExprTys (LMonoTy.subst S) e) = some v ∧
        HasVal.valueOfTy f v (.forAll [] (LMonoTy.subst S mty)) := by
  split at he
  · exact fvar_evaluable S he hs
  · obtain ⟨v, hv, hvty⟩ := exprWellTyped_eval_progress_inst S he hground hs
    exact ⟨exprWellTyped_varsDefined_inst S he hs, v, hv, hvty⟩

/-- The type arguments of a call whose type arguments are the images of the procedure's type
    parameters under a substitution `σ`, once the substitution `S` is applied to each, are the
    images of the type parameters under `σ` followed by `S`. -/
private theorem mapped_tyArgs {S : Subst} {σ : List (TyIdentifier × LMonoTy)}
    {typeArgs : List TyIdentifier} {tyArgs tyArgs' : Option (List Expression.Ty)}
    (h : tyArgs = some (typeArgs.map
      (fun a => LTy.forAll [] (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (.ftvar a)))))
    (hmap : tyArgs' = tyArgs.map (·.map (mapLTyTys (LMonoTy.subst S)))) :
    tyArgs' = some (typeArgs.map (fun a => LTy.forAll []
      (LMonoTy.subst S (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (.ftvar a))))) := by
  subst h
  subst hmap
  simp only [Option.map_some, List.map_map, Function.comp_def, mapLTyTys]

/-- A well-typed call, with the type substitution `S` applied to its type arguments and to the
    annotations of its input expressions, is of a declared procedure whose arguments match its
    signature and whose result variables are distinct and declared. Each input expression is the
    image under `S` of an expression typed as the procedure's formal instantiated by a
    substitution `σ` of its type parameters; each result variable has the formal's instantiated
    type; and the type arguments are the images of the type parameters under `σ` followed by
    `S`. -/
private theorem CmdExtWellTyped.call_inv_inst {C : LContext CoreLParams} {P : Program}
    {S : Subst} {ts ts' : TypeScopes} {n : String} {tyArgs tyArgs' : Option (List Expression.Ty)}
    {callArgs callArgs' : List (CallArg Expression)} {md : MetaData Expression}
    (h : CmdExtWellTyped C P ts (.call n tyArgs callArgs md) ts')
    (htyArgs : tyArgs' = tyArgs.map (·.map (mapLTyTys (LMonoTy.subst S))))
    (hargs : callArgs' = callArgs.map (CallArg.mapInput (mapExprTys (LMonoTy.subst S)))) :
    ∃ proc σ, Program.Procedure.find? P n = some proc ∧
      WF.ArgsMatchSignature proc callArgs' ∧ (CallArg.getLhs callArgs').Nodup ∧
      (∀ v, v ∈ CallArg.getLhs callArgs' → (ts.find? v).isSome) ∧
      (∀ i (hi : i < (CallArg.getInputExprs callArgs').length)
           (hj : i < proc.header.inputs.values.length),
        ∃ e0, (CallArg.getInputExprs callArgs')[i] = mapExprTys (LMonoTy.subst S) e0 ∧
          match e0 with
          | .fvar _ x none => ts.find? x =
              some (.forAll [] (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ])
                (proc.header.inputs.values[i])))
          | e => ExprWellTyped C ts e
              (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (proc.header.inputs.values[i]))) ∧
      (∀ i (hi : i < (CallArg.getLhs callArgs').length)
           (hj : i < proc.header.outputs.values.length),
        ts.find? ((CallArg.getLhs callArgs')[i]) =
          some (.forAll [] (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ])
            (proc.header.outputs.values[i])))) ∧
      tyArgs' = some (proc.header.typeArgs.map (fun a => LTy.forAll []
        (LMonoTy.subst S (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (.ftvar a))))) := by
  obtain ⟨proc, σ, hfind, hwf, hlhs, hin, hout, hty⟩ := h.call_inv
  subst hargs
  have hlhsEq := CallArg.getLhs_map_congr (mapExprTys (LMonoTy.subst S)) callArgs
  have hinEq := CallArg.getInputExprs_map_types (LMonoTy.subst S) callArgs
  refine ⟨proc, σ, hfind, ?_, ?_, ?_, ?_, ?_, mapped_tyArgs hty htyArgs⟩
  · exact (WF.ArgsMatchSignature.map_mapInput_iff _ proc callArgs).2 (hwf.argsMatch hfind)
  · rw [hlhsEq]
    exact hwf.lhsWF
  · rw [hlhsEq]
    exact hlhs
  · intro i hi hj
    have hi0 : i < (CallArg.getInputExprs callArgs).length := by
      rw [← CallArg.getInputExprs_length_map_mapInput (mapExprTys (LMonoTy.subst S))]
      exact hi
    refine ⟨(CallArg.getInputExprs callArgs)[i], ?_, hin i hi0 hj⟩
    exact (List.getElem_of_eq_map hinEq hi).2
  · intro i hi hj
    have hi0 : i < (CallArg.getLhs callArgs).length := by
      rw [← hlhsEq]
      exact hi
    rw [List.getElem_of_eq hlhsEq hi]
    exact hout i hi0 hj

/-- The procedure a call names, found in a procedure table that contains the procedures of a
    well-typed program, is well typed in the program. The table maps the name to this
    procedure. -/
private theorem call_proc_wellTyped {C0 : LContext CoreLParams} {ts0 : TypeScopes} {P : Program}
    {π : String → Option Procedure} {n : String} {proc : Procedure}
    (hP : ProgramWellTyped C0 ts0 P) (hfind : Program.Procedure.find? P n = some proc)
    (hπ : ∀ q, Program.Procedure.find? P n = some q → π n = some q) :
    π n = some proc ∧ ∃ C1, ProcWellTyped P C1 ts0 proc := by
  exact ⟨hπ proc hfind, hP.procWellTyped_of_find? hfind⟩

/-- The callee of a call, found in a procedure table that contains the procedures of a well-typed
    program, is an instance of the named procedure that keeps the names of its formals. -/
private theorem call_callee_instance {C0 : LContext CoreLParams} {ts0 : TypeScopes} {P : Program}
    {π : String → Option Procedure} {n : String} {tyArgs : Option (List Expression.Ty)}
    {proc p : Procedure}
    (hP : ProgramWellTyped C0 ts0 P) (hfind : Program.Procedure.find? P n = some proc)
    (hπ : ∀ q, Program.Procedure.find? P n = some q → π n = some q)
    (hcallee : Calls.typeInstantiatedCallee π n tyArgs = some p) :
    π n = some proc ∧ (∃ C1, ProcWellTyped P C1 ts0 proc) ∧
      proc.instantiateTypes (tyArgs.getD []) = some p ∧
      p.header.inputs.keys = proc.header.inputs.keys ∧
      p.header.outputs.keys = proc.header.outputs.keys := by
  obtain ⟨hπ0, hproc⟩ := call_proc_wellTyped hP hfind hπ
  have hinst := (Procedure.typeInstantiatedCallee_eq_some_iff hπ0).1 hcallee
  exact ⟨hπ0, hproc, hinst, Procedure.instantiateTypes_keys hinst⟩

/-- The callee of a well-typed call, instantiated at the call's type arguments with a
    substitution `S` applied, exists, and has a structured body that is not opaque or is opaque
    (`Body.isOpaque`). -/
private theorem call_instance {C0 : LContext CoreLParams} {ts0 : TypeScopes} {P : Program}
    {C : LContext CoreLParams} {S : Subst} {ts ts' : TypeScopes}
    {π : String → Option Procedure} {n : String} {tyArgs tyArgs' : Option (List Expression.Ty)}
    {callArgs : List (CallArg Expression)} {md : MetaData Expression}
    (hP : ProgramWellTyped C0 ts0 P) (hc : CmdExtWellTyped C P ts (.call n tyArgs callArgs md) ts')
    (htyArgs : tyArgs' = tyArgs.map (·.map (mapLTyTys (LMonoTy.subst S))))
    (hπ : ∀ q, Program.Procedure.find? P n = some q → π n = some q)
    (hstruct : CalleesStructured P) :
    ∃ p, Calls.typeInstantiatedCallee π n tyArgs' = some p ∧
      ((∃ ss, p.body = .structured ss false) ∨ p.body.isOpaque = true) := by
  obtain ⟨proc, σ, hfind, -, -, -, -, htyArgs0⟩ := hc.call_inv
  obtain ⟨hπ0, C1, hproc⟩ := call_proc_wellTyped hP hfind hπ
  have htyArgs' := mapped_tyArgs htyArgs0 htyArgs
  subst htyArgs'
  have hlen : (proc.header.typeArgs.map (fun a => LTy.forAll []
      (LMonoTy.subst S (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (.ftvar a))))).length =
      proc.header.typeArgs.length := List.length_map _
  have htysMono : ∀ ty ∈ proc.header.typeArgs.map (fun a => LTy.forAll []
      (LMonoTy.subst S (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (.ftvar a)))),
      ∃ m, ty = .forAll [] m := by
    intro ty hty
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hty
    exact ⟨_, rfl⟩
  obtain ⟨inst, hinst, hbody⟩ : ∃ inst, proc.instantiateTypes _ = some inst ∧
      ((∃ ss, inst.body = .structured ss false) ∨ inst.body.isOpaque = true) := by
    rcases hstruct n proc hfind with ⟨ss, opq, hss⟩ | habs
    · obtain ⟨inst, ss', hinst, hbody⟩ :=
        Procedure.instantiateTypes_structured hlen htysMono (hproc.initTypesMono hss) hss
      refine ⟨inst, hinst, ?_⟩
      cases opq
      · exact .inl ⟨ss', hbody⟩
      · exact .inr (by rw [hbody]; rfl)
    · obtain ⟨inst, hinst, hbody⟩ := Procedure.instantiateTypes_abstract hlen htysMono habs
      exact ⟨inst, hinst, .inr (by rw [hbody]; rfl)⟩
  refine ⟨inst, (Procedure.typeInstantiatedCallee_eq_some_iff hπ0).2 ?_, hbody⟩
  rw [Option.getD_some]
  exact hinst

/-- When a call's type arguments are the images of the procedure's type parameters under `σ` and
    then `S`, and are ground, each type parameter is sent by `σ` and then `S` to a ground
    type. -/
private theorem call_typeParams_ground {proc : Procedure} {σ : List (TyIdentifier × LMonoTy)}
    {S : Subst} {tyArgs : Option (List Expression.Ty)}
    (hground : ∀ tys, tyArgs = some tys → ∀ ty ∈ tys, LTy.GroundMono ty)
    (hty : tyArgs = some (proc.header.typeArgs.map (fun a => LTy.forAll []
      (LMonoTy.subst S (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (.ftvar a)))))) :
    ∀ a ∈ proc.header.typeArgs,
      (LMonoTy.subst S (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (.ftvar a))).IsGround := by
  intro a ha
  obtain ⟨τ, hτ, hgτ⟩ := hground _ hty _ (List.mem_map_of_mem ha)
  cases hτ
  exact hgτ

/-- A complete run of a structured callee body from a call frame keeps a slot at the type of
    the value it held: the slot is bound in the final store, to a value of that type. -/
private theorem structured_run_slot {π : String → Option Procedure} {p : Procedure}
    {ss : List Statement} {f : Expression.Factory} {σAO σEnd : CoreStore}
    {evs : Trace Expression} {z : Expression.Ident} {pc : Expression.Val}
    {opq : Bool} (hbody : p.body = .structured ss opq)
    (hrun : CoreBodyExecE π p.body ⟨σAO, f⟩ σEnd evs)
    (hσAO : σAO z = some pc) (hpcv : HasVal.value f pc) :
    ∃ v ty, σEnd z = some v ∧ HasVal.valueOfTy f pc ty ∧ HasVal.valueOfTy f v ty := by
  obtain ⟨ρ', hstar, hρ', hfac⟩ := CoreBodyExecE.structured_terminal hbody hrun
  obtain ⟨ty, hpcty⟩ := LawfulHasVal.value_typed f pc hpcv
  obtain ⟨v, hv, hvty⟩ :=
    core_stmt_preserves_typedAtE π hstar (y := z) (ty := ty) ⟨pc, hσAO, hpcty⟩
  rw [← hρ'] at hv
  rw [hfac] at hvty
  exact ⟨v, ty, hv, hpcty, hvty⟩

/-- A well-typed program has no undeclared type variables: in every procedure with a structured
    body, each type variable in a local declaration's type, or in a type argument of a call, is a
    type parameter of the procedure. The typing relation of a procedure requires this of the
    declarations and call type arguments of its body. -/
theorem ProgramWellTyped.calleesTyVarsScoped {C0 : LContext CoreLParams} {ts0 : TypeScopes}
    {P : Program} (h : ProgramWellTyped C0 ts0 P) : CalleesTyVarsScoped P := by
  intro n p ss opq hfind hbody
  obtain ⟨C, hproc⟩ := h.procWellTyped_of_find? hfind
  exact hproc.declTysScoped hbody

/-- The body of a callee, with a substitution that sends each type parameter of its procedure to
    a ground type applied, is ground: its declarations are at monotypes whose type variables are
    type parameters. -/
private theorem body_ground {C0 : LContext CoreLParams} {ts0 : TypeScopes} {P : Program}
    {C C' : LContext CoreLParams} {ts ts' : TypeScopes} {n : String} {proc : Procedure}
    {ss : List Statement} {S1 : Subst} (hP : ProgramWellTyped C0 ts0 P)
    (hfind : Program.Procedure.find? P n = some proc) {opq : Bool}
    (hbody : proc.body = .structured ss opq)
    (hss : StatementsWellTyped P C ts [] ss C' ts')
    (hS1 : ∀ a ∈ proc.header.typeArgs, (LMonoTy.subst S1 (.ftvar a)).IsGround) :
    Statements.Ground (mapStmtsTys (LMonoTy.subst S1) ss) := by
  have hscopedTys : Statements.AllDeclTys (fun ty => ∃ τ, ty = .forAll [] τ ∧
      ∀ a ∈ LMonoTy.freeVars τ, a ∈ proc.header.typeArgs) ss := by
    refine Statements.AllDeclTys.and_imp (fun ty hscope hm => ?_) ss
      (hP.calleesTyVarsScoped n proc ss opq hfind hbody) (StatementsWellTyped.allDeclTys_mono hss)
    obtain ⟨τ, rfl⟩ := hm
    exact ⟨τ, rfl, hscope τ rfl⟩
  exact Statements.ground_mapStmtsTys hS1 ss hscopedTys

/-- A store that conforms to the body scopes of an instance of a procedure at type arguments
    `tys`, and binds nothing outside them, conforms to the body scopes of the procedure with the
    substitution of the type arguments applied, and binds nothing outside the procedure's body
    scopes. The ambient scopes `ts0` declare nothing. -/
private theorem instStore_conforms {ts0 : TypeScopes} {proc inst : Procedure}
    {tys : List Expression.Ty} {ms : List LMonoTy} {f : Expression.Factory} {σ : CoreStore}
    (ht0 : ∀ x, ts0.find? x = none) (hinst : proc.instantiateTypes tys = some inst)
    (hms : tys.mapM LTy.toMonoType? = some ms)
    (hstore : StoreHasTyping f σ (procBodyScopes ts0 inst).find?)
    (hfresh : StoreFresh σ (procBodyScopes ts0 inst).find?) :
    StoreHasTyping f σ ((procBodyScopes ts0 proc).instVarTyping
        (Strata.Util.HMaps.ofScopes [proc.header.typeArgs.zip ms])) ∧
      StoreFresh σ (procBodyScopes ts0 proc).find? := by
  obtain ⟨ms2, hms2, hvt⟩ := procBodyScopes_inst ht0 hinst
  obtain rfl : ms = ms2 := (Option.some.inj (hms2.symm.trans hms)).symm
  rw [hvt] at hstore hfresh
  exact ⟨hstore, TypeScopes.storeFresh_instVarTyping.1 hfresh⟩

/-- The formal types of a procedure, instantiated by a substitution `σ` and then by `S`, are
    ground when each type parameter is sent by `σ` and then `S` to a ground type, since each
    type variable of the formals is a type parameter. -/
private theorem call_argTypes_ground {P : Program} {C : LContext CoreLParams} {ts : TypeScopes}
    {proc : Procedure} {σ : List (TyIdentifier × LMonoTy)} {S : Subst}
    (hproc : ProcWellTyped P C ts proc)
    (hparams : ∀ a ∈ proc.header.typeArgs,
      (LMonoTy.subst S (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (.ftvar a))).IsGround) :
    ∀ ty ∈ proc.header.inputs.values ++ proc.header.outputs.values,
      (LMonoTy.subst S (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) ty)).IsGround := by
  intro ty hty
  apply LMonoTy.subst_subst_isGround
  intro a ha
  exact hparams a (hproc.typeArg_of_mem_freeVars_formal hty ha)

/-- When a call frame is built, the output-only formal at position `j` among the output-only
    formals starts at the value held by the caller variable at position `j` among the call's
    `out` arguments, and that value is a value of the factory. -/
private theorem callEntry_outOnly_slot {f : Expression.Factory} {σ σAO : CoreStore}
    {p : Procedure} {callArgs : List (CallArg Expression)}
    (hentry : CallEntry f σ p callArgs σAO) (hold : p.header.oldNamesFresh)
    {j : Nat} {z w : CoreIdent}
    (hj1 : (Calls.outputOnlyParams (P := Expression) p.header)[j]? = some z)
    (hj2 : (CallArg.getOutArgs callArgs)[j]? = some w) :
    ∃ pc, σ w = some pc ∧ HasVal.value f pc ∧ σAO z = some pc := by
  obtain ⟨_, _, -, hreadOut, _, σIO, -, hinitIO, hAO⟩ := hentry
  obtain ⟨pc, hpcj, hσw, hpcval⟩ := ReadValues.getElem?_store hreadOut hj2
  obtain ⟨v1, hv1, hσIOz⟩ := InitStates.getElem?_store hinitIO hj1
  obtain rfl : v1 = pc := Option.some.inj (hv1.symm.trans hpcj)
  have hj1' : (p.header.outputs.keys.filter
      (fun x => !p.header.inputs.keys.contains x))[j]? = some z := hj1
  have hzp : z ∈ p.header.outputs.keys :=
    (List.mem_filter.1 (List.mem_iff_getElem?.2 ⟨j, hj1'⟩)).1
  have hAOz : σAO z = σIO z := by
    rw [hAO]
    exact Procedure.withOldSnapshots_inoutParams_eq hold (List.mem_append_right _ hzp)
  exact ⟨v1, hσw, hpcval, hAOz.trans hσIOz⟩

/-- The frame a call builds for its callee conforms to the scopes the callee body is typed in,
    and binds no other variable. The call has as many arguments as the callee has formals, and
    the callee's input types are ground. Each input argument is typed at a type that becomes the
    callee's input type once the type substitution `S` is applied, and each caller variable that
    receives an output is typed at a type that becomes the callee's output type. The caller's
    store conforms to the call's scopes with `S` applied. The ambient scopes `ts0` declare nothing,
    since the frame starts from the empty store and so binds no variable of them. -/
private theorem callEntry_conforms {C : LContext CoreLParams} {ts0 ts : TypeScopes}
    {callArgs : List (CallArg Expression)} {p : Procedure} {f : Expression.Factory}
    {σ σAO : CoreStore} (S : Subst)
    (ht0 : ∀ x, ts0.find? x = none)
    (hmatch : WF.ArgsMatchSignature p callArgs)
    (hinNodup : p.header.inputs.keys.Nodup) (houtNodup : p.header.outputs.keys.Nodup)
    (hold : p.header.oldNamesFresh)
    (hground : ∀ ty ∈ p.header.inputs.values, ty.IsGround)
    (hin : ∀ i (hi : i < (CallArg.getInputExprs callArgs).length)
        (hj : i < p.header.inputs.values.length),
      ∃ e0 τ, (CallArg.getInputExprs callArgs)[i] = mapExprTys (LMonoTy.subst S) e0 ∧
        LMonoTy.subst S τ = p.header.inputs.values[i] ∧
        match e0 with
        | .fvar _ x none => ts.find? x = some (.forAll [] τ)
        | e => ExprWellTyped C ts e τ)
    (hout : ∀ i (hi : i < (CallArg.getLhs callArgs).length)
        (hj : i < p.header.outputs.values.length),
      ∃ τ, LMonoTy.subst S τ = p.header.outputs.values[i] ∧
        ts.find? ((CallArg.getLhs callArgs)[i]) = some (.forAll [] τ))
    (hs : StoreHasTyping f σ (ts.instVarTyping S)) (hentry : CallEntry f σ p callArgs σAO) :
    StoreHasTyping f σAO (procBodyScopes ts0 p).find? ∧
      StoreFresh σAO (procBodyScopes ts0 p).find? := by
  have hentry0 := hentry
  obtain ⟨inputVals, outOnlyVals, hevalIn, -, σA, σIO, hinitA, hinitIO, hAO⟩ := hentry
  have hinitA' : InitStates emptyStore p.header.inputs.keys inputVals σA := hinitA
  have hinitIO' : InitStates σA (p.header.outputs.keys.filter
      (fun x => !p.header.inputs.keys.contains x)) outOnlyVals σIO := hinitIO
  have hG : Calls.inoutParams (P := Expression) p.header = p.header.getInoutParams.keys :=
    (Procedure.Header.keys_getInoutParams p.header).symm
  have hAOeq : ∀ z, (z ∈ p.header.inputs.keys ∨ z ∈ p.header.outputs.keys) → σAO z = σIO z := by
    intro z hz
    rw [hAO]
    exact Procedure.withOldSnapshots_inoutParams_eq hold
      (hz.elim (List.mem_append_left _ ·) (List.mem_append_right _ ·))
  -- Each input formal is bound to the value of its argument.
  have hclaimIn : ∀ (i : Nat) (x : CoreIdent) (ty : LMonoTy),
      p.header.inputs.toList[i]? = some (x, ty) →
        ∃ v, σIO x = some v ∧ HasVal.valueOfTy f v (.forAll [] ty) := by
    intro i x ty hi
    have hilt : i < p.header.inputs.length := (List.getElem?_eq_some_iff.1 hi).1
    have hj : i < p.header.inputs.values.length := by rw [ListMap.values_length]; exact hilt
    have hi' : i < (CallArg.getInputExprs callArgs).length := by
      rw [hmatch.inputCount]; exact hilt
    have hexpr : (Calls.getInputExprs callArgs)[i]? =
        some ((CallArg.getInputExprs callArgs)[i]) := List.getElem?_eq_getElem hi'
    obtain ⟨v, hv, hev⟩ := EvalExpressions.getElem?_eval hevalIn hexpr
    obtain ⟨e0, τ, he0eq, hτ, he0⟩ := hin i hi' hj
    have hSg : (LMonoTy.subst S τ).IsGround := by
      rw [hτ]
      exact hground _ (List.getElem_mem hj)
    obtain ⟨-, v', hev', hty0⟩ := inputArg_evaluable_typed S he0 hSg hs
    rw [← he0eq] at hev'
    have hty' : HasVal.valueOfTy f v' (.forAll [] p.header.inputs.values[i]) := by
      rw [hτ] at hty0
      exact hty0
    obtain rfl : v' = v := Option.some.inj (hev'.symm.trans hev)
    obtain ⟨hkey, hvi⟩ := ListMap.keys_values_getElem?_of_toList hi
    have hty : p.header.inputs.values[i] = ty := (List.getElem?_eq_some_iff.1 hvi).2
    obtain ⟨v1, hv1, hσA⟩ := InitStates.getElem?_store hinitA' hkey
    obtain rfl : v1 = v' := Option.some.inj (hv1.symm.trans hv)
    exact ⟨v1, InitStatesSomeMonotone hσA hinitIO', hty ▸ hty'⟩
  -- Each output-only formal is bound to the value of the caller variable that receives it.
  have houtM := hmatch.outputsMatch
  have hclaimOut : ∀ (k : Nat) (x : CoreIdent) (ty : LMonoTy),
      p.header.outputs.toList[k]? = some (x, ty) → x ∉ p.header.inputs.keys →
      ∃ v, σIO x = some v ∧ HasVal.valueOfTy f v (.forAll [] ty) := by
    intro k x ty hk hxI
    have hklt : k < p.header.outputs.length := (List.getElem?_eq_some_iff.1 hk).1
    have hj : k < p.header.outputs.values.length := by rw [ListMap.values_length]; exact hklt
    obtain ⟨hkey, hvi⟩ := ListMap.keys_values_getElem?_of_toList hk
    have hty : p.header.outputs.values[k] = ty := (List.getElem?_eq_some_iff.1 hvi).2
    have hrlen : k < (CallArg.resultArgs callArgs).length := by
      rw [CallArg.resultArgs_length_eq, hmatch.resultCount]; exact hklt
    obtain ⟨r, hr⟩ : ∃ r, (CallArg.resultArgs callArgs)[k]? = some r :=
      ⟨_, List.getElem?_eq_getElem hrlen⟩
    have hmz := WF.outputArgMatches_of_zip houtM
    have hmatchz := hmz k x r hkey hr
    cases r with
    | inArg ex => simp only [WF.outputArgMatches, Bool.false_eq_true] at hmatchz
    | inoutArg w' =>
      exfalso
      have hcont : p.header.inputs.keys.contains x = true := by
        simpa only [WF.outputArgMatches] using hmatchz
      exact hxI (List.contains_iff_mem.1 hcont)
    | outArg w' =>
      have hw : (CallArg.getLhs callArgs)[k]? = some w' :=
        CallArg.getLhs_getElem?_of_resultArgs callArgs (Or.inr hr)
      obtain ⟨j, hj1, hj2⟩ := WF.outArg_aligned p.header.inputs.keys p.header.outputs.keys _
        hmz k x w' hkey hr
      rw [CallArg.getOutArgs_resultArgs] at hj2
      obtain ⟨pc, hσw, -, hσAOx⟩ := callEntry_outOnly_slot hentry0 hold hj1 hj2
      have hxo : x ∈ p.header.outputs.keys := List.mem_iff_getElem?.2 ⟨k, hkey⟩
      have hσIOx : σIO x = some pc := (hAOeq x (Or.inr hxo)).symm.trans hσAOx
      have hlhs : k < (CallArg.getLhs callArgs).length := (List.getElem?_eq_some_iff.1 hw).1
      have hwk : (CallArg.getLhs callArgs)[k] = w' :=
        Option.some.inj ((List.getElem?_eq_getElem hlhs).symm.trans hw)
      obtain ⟨τ, hτ, hfindτ⟩ := hout k hlhs hj
      obtain ⟨v2, hv2, hv2ty0⟩ :=
        hs w' _ (TypeScopes.instVarTyping_of_find? (S := S) (hwk ▸ hfindτ))
      have hv2ty : HasVal.valueOfTy f v2 (.forAll [] p.header.outputs.values[k]) := by
        have hv2ty' : HasVal.valueOfTy f v2 (.forAll [] (LMonoTy.subst S τ)) := hv2ty0
        rw [hτ] at hv2ty'
        exact hv2ty'
      obtain rfl : v2 = pc := Option.some.inj (hv2.symm.trans hσw)
      exact ⟨_, hσIOx, hty ▸ hv2ty⟩
  -- The saved copy of an in-out parameter holds the value the parameter was given.
  have hclaimOld : ∀ (g : CoreIdent) (ty : LMonoTy),
      (g, ty) ∈ p.header.getInoutParams.toList →
      ∃ v, σAO (CoreIdent.mkOld g.name) = some v ∧ HasVal.valueOfTy f v (.forAll [] ty) := by
    intro g ty hmem
    have hmem2 : (g, ty) ∈ p.header.inputs.toList.filter
        (fun q => p.header.outputs.keys.contains q.1) := hmem
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 (List.mem_filter.1 hmem2).1
    obtain ⟨v, hv, hvty⟩ := hclaimIn i g ty hi
    refine ⟨v, ?_, hvty⟩
    rw [hAO, hG, withOldSnapshots_mkOld (ListMap.mem_keys_of_mem_toList hmem)]
    exact hv
  refine ⟨?_, ?_⟩
  · intro x ty hx
    have hx' : (procBodyScopes ts0 p).find? x = some ty := hx
    rcases procBodyScopes_find?_some (ht0 x) hinNodup houtNodup hx' with
      ⟨t, hq, rfl⟩ | ⟨hxI, t, hq, rfl⟩ | ⟨-, -, g, t, hgt, rfl, rfl⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hq
      obtain ⟨v, hv, hvty⟩ := hclaimIn i x t hi
      exact ⟨v, (hAOeq x (.inl (ListMap.mem_keys_of_mem_toList hq))).trans hv, hvty⟩
    · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hq
      obtain ⟨v, hv, hvty⟩ := hclaimOut k x t hk hxI
      exact ⟨v, (hAOeq x (.inr (ListMap.mem_keys_of_mem_toList hq))).trans hv, hvty⟩
    · exact hclaimOld g t hgt
  · intro x hx
    have hx' : (procBodyScopes ts0 p).find? x = none := hx
    obtain ⟨hxI, hxO, hxold⟩ := procBodyScopes_find?_none hx'
    rw [hAO]
    unfold Calls.withOldSnapshots
    cases hf : (Calls.inoutParams (P := Expression) p.header).find?
        (fun g => HasOldIdent.mkOld g == x) with
    | some g =>
      exfalso
      have hp0 := List.find?_some hf
      exact hxold g (hG ▸ List.mem_of_find?_eq_some hf) (beq_iff_eq.1 hp0).symm
    | none =>
      have hIO : σIO x = σA x :=
        InitStates.eq_of_not_mem hinitIO' (fun hm => hxO (List.mem_filter.1 hm).1)
      show σIO x = none
      rw [hIO, InitStates.eq_of_not_mem hinitA' hxI]
      rfl

/-- Entering the callee of a well-typed call succeeds. In a store that conforms to the call's
    scopes, the input arguments evaluate, the `out` variables are read, and the callee's frame
    is built. Every output formal of the callee is bound to a value in the frame. -/
private theorem callEntry_exists {C0 : LContext CoreLParams} {ts0 : TypeScopes} {P : Program}
    {C : LContext CoreLParams} {S : Subst} {ts ts' : TypeScopes} {π : String → Option Procedure}
    {n : String} {tyArgs0 tyArgs : Option (List Expression.Ty)}
    {callArgs0 callArgs : List (CallArg Expression)} {md : MetaData Expression}
    {p : Procedure} {f : Expression.Factory} {σ : CoreStore}
    (hP : ProgramWellTyped C0 ts0 P)
    (hc : CmdExtWellTyped C P ts (.call n tyArgs0 callArgs0 md) ts')
    (htyArgs : tyArgs = tyArgs0.map (·.map (mapLTyTys (LMonoTy.subst S))))
    (hargs : callArgs = callArgs0.map (CallArg.mapInput (mapExprTys (LMonoTy.subst S))))
    (hπ : ∀ q, Program.Procedure.find? P n = some q → π n = some q)
    (hcallee : Calls.typeInstantiatedCallee π n tyArgs = some p)
    (hground : ∀ tys, tyArgs = some tys → ∀ ty ∈ tys, LTy.GroundMono ty)
    (hs : StoreHasTyping f σ (ts.instVarTyping S)) :
    ∃ σAO, CallEntry f σ p callArgs σAO ∧
      ∀ z ∈ p.header.outputs.keys, ∃ v, σAO z = some v ∧ HasVal.value f v := by
  obtain ⟨proc, σ0, hfind, hmatch, -, -, hin, hout, htyArgs'⟩ := hc.call_inv_inst htyArgs hargs
  obtain ⟨-, ⟨C1, hproc⟩, hinst, hinK, houtK⟩ := call_callee_instance hP hfind hπ hcallee
  have hparams := call_typeParams_ground hground htyArgs'
  have hgr := call_argTypes_ground hproc hparams
  have hlenIn : (CallArg.getInputExprs callArgs).length = proc.header.inputs.values.length := by
    rw [hmatch.inputCount, ListMap.values_length]
  have hresLen : (CallArg.getLhs callArgs).length = proc.header.outputs.values.length := by
    rw [hmatch.resultCount, ListMap.values_length]
  obtain ⟨inputVals, hevalIn, hinVals⟩ :
      ∃ vs, EvalExpressions f σ (Calls.getInputExprs callArgs) vs ∧
        ∀ v ∈ vs, HasVal.value f v := by
    apply EvalExpressions.exists_of_evaluable
    intro e he
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 he
    have hj : i < proc.header.inputs.values.length := hlenIn ▸ hi
    obtain ⟨e0, he0eq, he0⟩ := hin i hi hj
    rw [he0eq]
    obtain ⟨hdef, v, hv, hvty⟩ := inputArg_evaluable_typed S he0
      (hgr _ (List.mem_append_left _ (List.getElem_mem hj))) hs
    exact ⟨hdef, v, hv, LawfulHasVal.valueOfTy_isVal f v _ hvty⟩
  obtain ⟨outOnlyVals, hreadOut⟩ : ∃ vs, ReadValues f σ (CallArg.getOutArgs callArgs) vs := by
    apply ReadValues.exists_of_bound
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 (CallArg.mem_getLhs_of_mem_getOutArgs hw)
    obtain ⟨v, hv, hvty⟩ :=
      hs _ _ (TypeScopes.instVarTyping_of_find? (S := S) (hout i hi (hresLen ▸ hi)))
    exact ⟨v, hv, LawfulHasVal.valueOfTy_isVal f v _ hvty⟩
  have hnodupIn : p.header.inputs.keys.Nodup := hinK ▸ hproc.inputsNodup
  have hlenVals : p.header.inputs.keys.length = inputVals.length := by
    rw [← EvalExpressionsLength hevalIn, hinK, hmatch.inputCount, ListMap.keys.length]
  have hnodupOO : (p.header.outputs.keys.filter
      (fun x => !p.header.inputs.keys.contains x)).Nodup :=
    List.Pairwise.filter _ (houtK ▸ hproc.outputsNodup)
  have hdisj : ∀ a ∈ p.header.inputs.keys, ∀ b ∈ p.header.outputs.keys.filter
      (fun x => !p.header.inputs.keys.contains x), a ≠ b := by
    intro a ha b hb hab
    have hb2 := (List.mem_filter.1 hb).2
    rw [← hab, List.contains_iff_mem.2 ha] at hb2
    exact absurd hb2 (by decide)
  have hlenOO : (p.header.outputs.keys.filter
      (fun x => !p.header.inputs.keys.contains x)).length = outOnlyVals.length := by
    rw [← ReadValuesLength hreadOut, ← CallArg.getOutArgs_resultArgs, hinK, houtK]
    have hresLen' : proc.header.outputs.keys.length = (CallArg.resultArgs callArgs).length := by
      rw [CallArg.resultArgs_length_eq, hmatch.resultCount, ListMap.keys.length]
    exact WF.outputOnly_length proc.header.inputs.keys proc.header.outputs.keys
        (CallArg.resultArgs callArgs) hresLen' hmatch.outputsMatch
  have hframe := Calls.initCallFrame_callEntryStore p inputVals outOnlyVals hlenVals hlenOO
    (List.nodup_append.2 ⟨hnodupIn, hnodupOO, hdisj⟩)
  refine ⟨Calls.callEntryStore p inputVals outOnlyVals,
    ⟨inputVals, outOnlyVals, hevalIn, hreadOut, hframe⟩, ?_⟩
  obtain ⟨σA, σIO, hinitA, hinitIO, hAO⟩ := hframe
  intro z hz
  rw [hAO]
  have hAOz : Calls.withOldSnapshots (Calls.inoutParams (P := Expression) p.header) σIO z =
      σIO z :=
    Procedure.withOldSnapshots_inoutParams_eq
      (Procedure.instantiateTypes_oldNamesFresh hinst hproc.oldNamesFresh)
      (List.mem_append_right _ hz)
  by_cases hzin : z ∈ p.header.inputs.keys
  · obtain ⟨pc, hpc, hpcv⟩ := InitStates.exists_slot hinitA hinVals hzin
    have hAO' : Calls.withOldSnapshots (Calls.inoutParams (P := Expression) p.header) σIO z =
        some pc := by
      rw [hAOz]
      exact InitStatesSomeMonotone hpc hinitIO
    exact ⟨pc, hAO', hpcv⟩
  · have hzoo : z ∈ p.header.outputs.keys.filter
        (fun x => !p.header.inputs.keys.contains x) := by
      refine List.mem_filter.2 ⟨hz, ?_⟩
      have hcf : p.header.inputs.keys.contains z = false := by
        cases hcz : p.header.inputs.keys.contains z
        · rfl
        · exact absurd (List.contains_iff_mem.1 hcz) hzin
      rw [hcf]
      rfl
    obtain ⟨pc, hpc, hpcv⟩ := InitStates.exists_slot hinitIO (ReadValues.all_values hreadOut) hzoo
    have hAO' : Calls.withOldSnapshots (Calls.inoutParams (P := Expression) p.header) σIO z =
        some pc := by
      rw [hAOz]
      exact hpc
    exact ⟨pc, hAO', hpcv⟩

/-- The values a call returns pass the call's check against the caller's variables, for an end
    store `σEnd` that keeps each slot of the call frame `σAO` at the type of the value it held.
    The call is of the program's procedure `n` (the procedure table contains the program's
    procedure `n`), instantiated at the call's type arguments. The values read from the output
    formals in `σEnd` each have the type of the value the corresponding caller variable holds.

    The program being well typed ensures that the callee's output names are distinct and that
    none is named like the saved copy of an `inout` formal. -/
private theorem callExit_check_holds_of_slots {C0 : LContext CoreLParams} {ts0 : TypeScopes}
    {P : Program}
    {π : String → Option Procedure}
    {n : String} {tyArgs : Option (List Expression.Ty)} {callArgs : List (CallArg Expression)}
    {p : Procedure}
    {f : Expression.Factory} {σ σAO σEnd : CoreStore}
    {outputVals : List Expression.Val}
    (hP : ProgramWellTyped C0 ts0 P)
    {proc₀ : Procedure} (hfind : Program.Procedure.find? P n = some proc₀)
    (hmatch : WF.ArgsMatchSignature proc₀ callArgs)
    (hπ : ∀ q, Program.Procedure.find? P n = some q → π n = some q)
    (hcallee : Calls.typeInstantiatedCallee π n tyArgs = some p)
    (hentry : CallEntry f σ p callArgs σAO)
    (hslots : ∀ z pc, σAO z = some pc → HasVal.value f pc →
      ∃ v ty, σEnd z = some v ∧ HasVal.valueOfTy f pc ty ∧ HasVal.valueOfTy f v ty)
    (hread : ReadValues f σEnd p.header.outputs.keys outputVals) :
    List.Rel₂ (HasVal.valueOfStoredTy (P := Expression) f σ) (CallArg.getLhs callArgs)
      outputVals := by
  obtain ⟨-, ⟨C1, hproc⟩, hinst, hin, hout⟩ := call_callee_instance hP hfind hπ hcallee
  obtain ⟨zs, hzs⟩ : ∃ zs, ListMap.keys proc₀.header.outputs = zs := ⟨_, rfl⟩
  obtain ⟨inputs, hinputs⟩ : ∃ xs, ListMap.keys proc₀.header.inputs = xs := ⟨_, rfl⟩
  have hreadz : ReadValues f σEnd zs outputVals := by rw [← hzs, ← hout]; exact hread
  have hnodup : zs.Nodup := hzs ▸ hproc.outputsNodup
  have hrsLen : (CallArg.resultArgs callArgs).length = zs.length := by
    rw [CallArg.resultArgs_length_eq, ← hzs]
    have hcount := hmatch.resultCount
    have hkeys := ListMap.keys.length (ls := proc₀.header.outputs)
    omega
  have hvals : outputVals.length = zs.length := (ReadValuesLength hreadz).symm
  have houtM := hmatch.outputsMatch
  have hinM := hmatch.inputsMatch
  rw [hzs, hinputs] at houtM
  rw [hzs, hinputs] at hinM
  have hmz := WF.outputArgMatches_of_zip houtM
  have hentry0 := hentry
  have hfresh := Procedure.instantiateTypes_oldNamesFresh hinst hproc.oldNamesFresh
  obtain ⟨inputVals, outOnlyVals, hevalIn, -, σA, σIO, hinitA, hinitIO, hAO⟩ := hentry
  have hOO : Calls.outputOnlyParams (P := Expression) p.header =
      zs.filter (fun x => !inputs.contains x) := by
    show p.header.outputs.keys.filter (fun x => !p.header.inputs.keys.contains x) = _
    rw [hout, hin, hzs, hinputs]
  have hlen : (CallArg.getLhs callArgs).length = outputVals.length := by
    rw [← CallArg.resultArgs_length_eq, hrsLen, hvals]
  refine List.Rel₂.of_getElem? hlen ?_
  intro k w v hw hv
  have hkz : k < zs.length := by
    rw [← hrsLen, CallArg.resultArgs_length_eq]; exact (List.getElem?_eq_some_iff.1 hw).1
  obtain ⟨z, hz⟩ : ∃ z, zs[k]? = some z := ⟨zs[k], List.getElem?_eq_getElem hkz⟩
  have hkr : k < (CallArg.resultArgs callArgs).length := by
    rw [hrsLen]
    exact hkz
  obtain ⟨r, hr⟩ : ∃ r, (CallArg.resultArgs callArgs)[k]? = some r :=
    ⟨_, List.getElem?_eq_getElem hkr⟩
  obtain ⟨v', hv', hzEnd, -⟩ := ReadValues.getElem?_store hreadz hz
  have hvv : v' = v := Option.some.inj (hv'.symm.trans hv)
  subst hvv
  have hmatchz := hmz k z r hz hr
  have hAOz : σAO z = σIO z := by
    have hzp : z ∈ p.header.outputs.keys := by
      rw [hout, hzs]
      exact List.mem_iff_getElem?.2 ⟨k, hz⟩
    rw [hAO]
    exact Procedure.withOldSnapshots_inoutParams_eq hfresh (List.mem_append_right _ hzp)
  have hslot : ∃ pc, σ w = some pc ∧ HasVal.value f pc ∧ σAO z = some pc := by
    cases r with
    | inArg ex => simp only [WF.outputArgMatches, Bool.false_eq_true] at hmatchz
    | outArg w' =>
      have hww : w' = w :=
        Option.some.inj
          ((CallArg.getLhs_getElem?_of_resultArgs callArgs (Or.inr hr)).symm.trans hw)
      subst hww
      obtain ⟨j, hj1, hj2⟩ := WF.outArg_aligned inputs zs _ hmz k z w' hz hr
      rw [CallArg.getOutArgs_resultArgs] at hj2
      rw [← hOO] at hj1
      exact callEntry_outOnly_slot hentry0 hfresh hj1 hj2
    | inoutArg w' =>
      have hww : w' = w :=
        Option.some.inj
          ((CallArg.getLhs_getElem?_of_resultArgs callArgs (Or.inl hr)).symm.trans hw)
      subst hww
      have hcont : inputs.contains z = true := by
        simpa only [WF.outputArgMatches] using hmatchz
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 (List.contains_iff_mem.1 hcont)
      have hilt : i < (CallArg.inputArgs callArgs).length := by
        have hil : i < inputs.length := (List.getElem?_eq_some_iff.1 hi).1
        have hlenI : inputs.length = proc₀.header.inputs.length := by
          rw [← hinputs]; exact ListMap.keys.length
        rw [Calls.inputArgs_length_eq, hmatch.inputCount]
        omega
      obtain ⟨a, ha⟩ : ∃ a, (CallArg.inputArgs callArgs)[i]? = some a :=
        ⟨_, List.getElem?_eq_getElem hilt⟩
      have hmi := hinM (z, a) (List.mem_iff_getElem?.2 ⟨i, List.getElem?_zip_eq_some.2 ⟨hi, ha⟩⟩)
      have hidx : zs.idxOf? z = some k := by
        rw [List.idxOf?_eq_some_iff]
        refine ⟨hkz, (List.getElem?_eq_some_iff.1 hz).2, fun j hj hjz => ?_⟩
        have hjk : zs[j]? = zs[k]? := by
          rw [hz, List.getElem?_eq_getElem (Nat.lt_trans hj hkz), hjz]
        exact Nat.ne_of_lt hj ((List.Nodup.getElem?_inj (Nat.lt_trans hj hkz) hnodup).1 hjk)
      simp only [WF.inputArgMatches, hidx] at hmi
      cases a with
      | inArg ex => simp only [Bool.false_eq_true] at hmi
      | outArg x => simp only [Bool.false_eq_true] at hmi
      | inoutArg v0 =>
        have hlhs : (CallArg.getLhs callArgs)[k]? = some v0 := by
          simpa only [beq_iff_eq] using hmi
        obtain rfl : v0 = w' := Option.some.inj (hlhs.symm.trans hw)
        have hexpr := Calls.getInputExprs_getElem?_of_inputArgs callArgs ha
        obtain ⟨pv, hpv, hevalv⟩ := EvalExpressions.getElem?_eval hevalIn hexpr
        obtain ⟨hσw, hpval⟩ := Expression.eval_mkFvar_some hevalv
        have hinA : InitStates emptyStore inputs inputVals σA := by
          rw [← hinputs, ← hin]; exact hinitA
        obtain ⟨v1, hv1, hσAz⟩ := InitStates.getElem?_store hinA hi
        obtain rfl : v1 = pv := Option.some.inj (hv1.symm.trans hpv)
        have hAO' : σAO z = some v1 := by
          rw [hAOz]
          exact InitStatesSomeMonotone hσAz hinitIO
        exact ⟨v1, hσw, hpval, hAO'⟩
  obtain ⟨pc, hσw, hpcval, hσAOz⟩ := hslot
  obtain ⟨v2, ty, hv2, hpcty, hv2ty⟩ := hslots z pc hσAOz hpcval
  obtain rfl : v2 = v' := Option.some.inj (hv2.symm.trans hzEnd)
  exact ⟨pc, ty, hσw, hpcty, hv2ty⟩

/-- The values a call returns pass the call's check against the caller's variables. The call is
    of the program's procedure `n` (the procedure table contains the program's procedure `n`),
    instantiated at the call's type arguments, with a structured body. If the body runs from the
    call frame to the end store `σEnd`, then the values read from the output formals there each
    have the type of the value the corresponding caller variable holds.

    The program being well typed ensures that the callee's output names are distinct and that
    none is named like the saved copy of an `inout` formal. -/
theorem callExit_check_holds {C0 : LContext CoreLParams} {ts0 : TypeScopes} {P : Program}
    {π : String → Option Procedure}
    {n : String} {tyArgs : Option (List Expression.Ty)} {callArgs : List (CallArg Expression)}
    {p : Procedure} {ss : List Statement}
    {f : Expression.Factory} {σ σAO σEnd : CoreStore} {evs : Trace Expression}
    {outputVals : List Expression.Val}
    (hP : ProgramWellTyped C0 ts0 P)
    {proc₀ : Procedure} (hfind : Program.Procedure.find? P n = some proc₀)
    (hmatch : WF.ArgsMatchSignature proc₀ callArgs)
    (hπ : ∀ q, Program.Procedure.find? P n = some q → π n = some q)
    (hcallee : Calls.typeInstantiatedCallee π n tyArgs = some p)
    {opq : Bool} (hbody : p.body = .structured ss opq)
    (hentry : CallEntry f σ p callArgs σAO)
    (hrun : CoreBodyExecE π p.body ⟨σAO, f⟩ σEnd evs)
    (hread : ReadValues f σEnd p.header.outputs.keys outputVals) :
    List.Rel₂ (HasVal.valueOfStoredTy (P := Expression) f σ) (CallArg.getLhs callArgs)
      outputVals :=
  callExit_check_holds_of_slots hP hfind hmatch hπ hcallee hentry
    (fun _ _ hσAO hpcv => structured_run_slot hbody hrun hσAO hpcv) hread

/-- A complete run of the callee body of a well-typed call can be written back: the callee's
    final store binds every output formal, and the caller's result variables are distinct and
    bound, so the call exits. -/
private theorem callExit_exists {C0 : LContext CoreLParams} {ts0 : TypeScopes} {P : Program}
    {C : LContext CoreLParams} {S : Subst} {ts ts' : TypeScopes} {π : String → Option Procedure}
    {n : String} {tyArgs0 tyArgs : Option (List Expression.Ty)}
    {callArgs0 callArgs : List (CallArg Expression)} {md : MetaData Expression} {p : Procedure}
    {f : Expression.Factory} {σ σAO σEnd : CoreStore}
    (hP : ProgramWellTyped C0 ts0 P)
    (hc : CmdExtWellTyped C P ts (.call n tyArgs0 callArgs0 md) ts')
    (htyArgs : tyArgs = tyArgs0.map (·.map (mapLTyTys (LMonoTy.subst S))))
    (hargs : callArgs = callArgs0.map (CallArg.mapInput (mapExprTys (LMonoTy.subst S))))
    (hπ : ∀ q, Program.Procedure.find? P n = some q → π n = some q)
    (hcallee : Calls.typeInstantiatedCallee π n tyArgs = some p)
    (hentry : CallEntry f σ p callArgs σAO)
    (hbound : ∀ z ∈ p.header.outputs.keys, ∃ v, σAO z = some v ∧ HasVal.value f v)
    (hs : StoreHasTyping f σ (ts.instVarTyping S))
    (hslots : ∀ z pc, σAO z = some pc → HasVal.value f pc →
      ∃ v ty, σEnd z = some v ∧ HasVal.valueOfTy f pc ty ∧ HasVal.valueOfTy f v ty) :
    ∃ σ', CallExit f σ p callArgs σEnd σ' := by
  obtain ⟨proc, σ0, hfind, hmatch, hnodup, hlhs, -, -, -⟩ := hc.call_inv_inst htyArgs hargs
  obtain ⟨-, -, -, -, houtK⟩ := call_callee_instance hP hfind hπ hcallee
  obtain ⟨outputVals, hread⟩ : ∃ vs, ReadValues f σEnd p.header.outputs.keys vs := by
    apply ReadValues.exists_of_bound
    intro z hz
    obtain ⟨pc, hσAO, hpcv⟩ := hbound z hz
    obtain ⟨v2, ty, hv2, -, hv2ty⟩ := hslots z pc hσAO hpcv
    exact ⟨v2, hv2, LawfulHasVal.valueOfTy_isVal f v2 ty hv2ty⟩
  have hrel := callExit_check_holds_of_slots hP hfind hmatch hπ hcallee hentry hslots hread
  have hlen : (CallArg.getLhs callArgs).length = outputVals.length := by
    rw [← ReadValuesLength hread, houtK, hmatch.resultCount, ListMap.keys.length]
  have hlhsDef : SemanticStore.varsDefined (· ∈ CallArg.getLhs callArgs) σ := by
    intro w hw
    obtain ⟨ty, hty⟩ := Option.isSome_iff_exists.1 (hlhs w hw)
    obtain ⟨v, hv, -⟩ := hs w _ (TypeScopes.instVarTyping_of_find? (S := S) hty)
    rw [hv]
    rfl
  exact ⟨_, hnodup, outputVals, hread,
    Calls.updateStates_bindPositional σ _ outputVals hlen hlhsDef, hrel⟩

/-- A well-typed call, in a program whose procedure table contains the program's callee
    and holds only structured bodies or none, either steps or runs a callee that does not finish:
    a call to an opaque callee steps by its contract (`call_abstract_sem`). The
    call carries ground type arguments and runs in a store that conforms to its scopes. -/
private theorem CmdExtWellTyped.call_progress {C0 : LContext CoreLParams} {ts0 : TypeScopes}
    {P : Program} {C : LContext CoreLParams} {S : Subst} {ts ts' : TypeScopes}
    {π : String → Option Procedure} {n : String} {tyArgs0 tyArgs : Option (List Expression.Ty)}
    {callArgs0 callArgs : List (CallArg Expression)} {md : MetaData Expression}
    {ρ : Env Expression}
    (hP : ProgramWellTyped C0 ts0 P)
    (hc : CmdExtWellTyped C P ts (.call n tyArgs0 callArgs0 md) ts')
    (htyArgs : tyArgs = tyArgs0.map (·.map (mapLTyTys (LMonoTy.subst S))))
    (hargs : callArgs = callArgs0.map (CallArg.mapInput (mapExprTys (LMonoTy.subst S))))
    (hπ : ∀ q, Program.Procedure.find? P n = some q → π n = some q) (hstruct : CalleesStructured P)
    (hground : ∀ tys, tyArgs = some tys → ∀ ty ∈ tys, LTy.GroundMono ty)
    (hs : StoreHasTyping ρ.factory ρ.store (ts.instVarTyping S)) :
    (∃ evs cfg', CoreStepE π (.stmt (.cmd (.call n tyArgs callArgs md)) ρ) evs cfg') ∨
      CallDoesNotFinish π (.stmt (.cmd (.call n tyArgs callArgs md)) ρ) := by
  obtain ⟨p, hcallee, hbody⟩ := call_instance hP hc htyArgs hπ hstruct
  obtain ⟨σAO, hentry, hbound⟩ := callEntry_exists hP hc htyArgs hargs hπ hcallee hground hs
  rcases hbody with ⟨ss, hbody⟩ | ho
  · have hno : p.body.isOpaque = false := by rw [hbody]; rfl
    by_cases hrun : ∃ σEnd evs, CoreBodyExecE π p.body ⟨σAO, ρ.factory⟩ σEnd evs
    · obtain ⟨σEnd, evs, hrun⟩ := hrun
      obtain ⟨σ', hexit⟩ := callExit_exists hP hc htyArgs hargs hπ hcallee hentry hbound hs
        (fun _ _ hσAO hpcv => structured_run_slot hbody hrun hσAO hpcv)
      exact .inl ⟨_, _, .step_cmd (.call_sem hcallee hno hentry hrun hexit)⟩
    · exact .inr (.call hcallee hno hentry hrun)
  · -- An opaque callee runs its contract: the havoc of the outputs keeps their entry values,
    -- and the call frame itself is written back.
    have htyped (z) (pc) (hσAO : σAO z = some pc) (hpcv : HasVal.value ρ.factory pc) :
        ∃ v ty, σAO z = some v ∧ HasVal.valueOfTy ρ.factory pc ty ∧
          HasVal.valueOfTy ρ.factory v ty :=
      (LawfulHasVal.value_typed ρ.factory pc hpcv).elim fun ty hty => ⟨pc, ty, hσAO, hty, hty⟩
    have hhavoc : HavocVars ρ.factory σAO
        (ProcedureHeader.outputParams (P := Expression) p.header) σAO :=
      HavocVarsId fun z hz => by
        obtain ⟨pc, hσAO, hpcv⟩ := hbound z hz
        obtain ⟨v, ty, hv, hty, -⟩ := htyped z pc hσAO hpcv
        exact ⟨v, ty, hv, (Option.some.inj (hσAO.symm.trans hv)) ▸ hty⟩
    obtain ⟨σ', hexit⟩ :=
      callExit_exists hP hc htyArgs hargs hπ hcallee hentry hbound hs htyped
    exact .inl ⟨_, _, .step_cmd (.call_abstract_sem hcallee ho hentry hhavoc hexit)⟩

/-- The body of the callee of a call, started in the frame the call builds, runs through
    well-typed configurations. The call is well typed, with a type substitution `S` applied, in
    a store that conforms to its scopes with `S` applied, and carries ground type arguments. The
    callee is an instance of a procedure of the program, with the procedure's type parameters
    replaced by those type arguments, so its body is the procedure's own body with that
    replacement `S1` applied. The procedure's body is typed in the scopes of its formals over the
    ambient scopes `ts0`, which declare nothing since the frame starts from the empty store. The
    callee's frame conforms to those scopes with `S1` applied. Every declaration of the body is
    at a type whose type variables are type parameters, so the body with `S1` applied declares
    only ground types. -/
private theorem call_callee_reachable {C0 : LContext CoreLParams} {ts0 : TypeScopes}
    {P : Program} {C : LContext CoreLParams} {S : Subst} {ts ts' : TypeScopes}
    {π : String → Option Procedure} {n : String} {tyArgs0 tyArgs : Option (List Expression.Ty)}
    {callArgs0 callArgs : List (CallArg Expression)} {md : MetaData Expression} {p : Procedure}
    {ρ : Env Expression} {σAO : CoreStore}
    (hP : ProgramWellTyped C0 ts0 P) (ht0 : ∀ x, ts0.find? x = none)
    (hc : CmdExtWellTyped C P ts (.call n tyArgs0 callArgs0 md) ts')
    (htyArgs : tyArgs = tyArgs0.map (·.map (mapLTyTys (LMonoTy.subst S))))
    (hargs : callArgs = callArgs0.map (CallArg.mapInput (mapExprTys (LMonoTy.subst S))))
    (hπ : ∀ q, Program.Procedure.find? P n = some q → π n = some q) (hstruct : CalleesStructured P)
    (hground : ∀ tys, tyArgs = some tys → ∀ ty ∈ tys, LTy.GroundMono ty)
    (hcallee : Calls.typeInstantiatedCallee π n tyArgs = some p) (hno : p.body.isOpaque = false)
    (hentry : CallEntry ρ.factory ρ.store p callArgs σAO)
    (hs : StoreHasTyping ρ.factory ρ.store (ts.instVarTyping S)) :
    ∃ ss C1 S1 tsr, p.body = .structured ss false ∧ ∀ evs cfg,
      CoreStepStarE π (.stmt (Stmt.block "" ss #[]) ⟨σAO, ρ.factory⟩) evs cfg →
      cfg = .stmt (Stmt.block "" ss #[]) ⟨σAO, ρ.factory⟩ ∨
        ConfigWellTyped P ρ.factory S1 [] cfg C1 tsr tsr := by
  obtain ⟨proc, σ0, hfind, hmatch, -, -, hin, hout, htyArgs'⟩ := hc.call_inv_inst htyArgs hargs
  obtain ⟨-, ⟨C1, hproc⟩, hinst, hinK, houtK⟩ := call_callee_instance hP hfind hπ hcallee
  obtain ⟨ms, hms, hinp, houtp, hbodyp⟩ := Procedure.instantiateTypes_spec hinst
  obtain ⟨ss, hbody⟩ : ∃ ss, proc.body = .structured ss false := by
    rcases hstruct n proc hfind with ⟨ss, opq, hss⟩ | habs
    · rw [hbodyp ss opq hss] at hno
      cases hno
      exact ⟨ss, hss⟩
    · rw [Procedure.instantiateTypes_body_abstract hinst habs] at hno
      cases hno
  have hmsEq : ms = proc.header.typeArgs.map (fun a => LMonoTy.subst S
      (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ0]) (.ftvar a))) := by
    have hmapM : (tyArgs.getD []).mapM LTy.toMonoType? = some (proc.header.typeArgs.map
        (fun a => LMonoTy.subst S
          (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ0]) (.ftvar a)))) := by
      rw [htyArgs', Option.getD_some]
      exact Lambda.mapM_toMonoType?_map_forAll _ _
    exact Option.some.inj (hms.symm.trans hmapM)
  obtain ⟨S1, hS1⟩ : ∃ S1 : Subst,
      S1 = Strata.Util.HMaps.ofScopes [proc.header.typeArgs.zip ms] := ⟨_, rfl⟩
  rw [← hS1] at hinp houtp hbodyp
  have hS1g : S1 = Strata.Util.HMaps.ofScopes [proc.header.typeArgs.zip (proc.header.typeArgs.map
      (fun b => LMonoTy.subst S
        (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ0]) (.ftvar b))))] := by
    rw [hS1, hmsEq]
  have hcomp : ∀ ty ∈ proc.header.inputs.values ++ proc.header.outputs.values,
      LMonoTy.subst S1 ty =
        LMonoTy.subst S (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ0]) ty) := by
    intro ty hty
    rw [hS1g]
    exact LMonoTy.subst_ofScopes_zip_map_comp S σ0 hproc.typeArgsNodup
      (fun x hx => hproc.typeArg_of_mem_freeVars_formal hty hx)
  have hparams := call_typeParams_ground hground htyArgs'
  have hgr := call_argTypes_ground hproc hparams
  have hinV : p.header.inputs.values = proc.header.inputs.values.map (LMonoTy.subst S1) := by
    rw [hinp]
    exact ListMap.values_map_snd _ _
  have houtV : p.header.outputs.values = proc.header.outputs.values.map (LMonoTy.subst S1) := by
    rw [houtp]
    exact ListMap.values_map_snd _ _
  have hgroundIn : ∀ ty ∈ p.header.inputs.values, ty.IsGround := by
    intro ty hty
    rw [hinV] at hty
    obtain ⟨ty0, hty0, rfl⟩ := List.mem_map.1 hty
    have hmem0 : ty0 ∈ proc.header.inputs.values ++ proc.header.outputs.values :=
      List.mem_append_left _ hty0
    rw [hcomp ty0 hmem0]
    exact hgr ty0 hmem0
  have hin' : ∀ i (hi : i < (CallArg.getInputExprs callArgs).length)
      (hj : i < p.header.inputs.values.length),
      ∃ e0 τ, (CallArg.getInputExprs callArgs)[i] = mapExprTys (LMonoTy.subst S) e0 ∧
        LMonoTy.subst S τ = p.header.inputs.values[i] ∧
        match e0 with
        | .fvar _ x none => ts.find? x = some (.forAll [] τ)
        | e => ExprWellTyped C ts e τ := by
    intro i hi hj
    obtain ⟨hj', hv⟩ := List.getElem_of_eq_map hinV hj
    obtain ⟨e0, he0eq, he0⟩ := hin i hi hj'
    refine ⟨e0, _, he0eq, ?_, he0⟩
    rw [hv]
    exact (hcomp _ (List.mem_append_left _ (List.getElem_mem hj'))).symm
  have hout' : ∀ i (hi : i < (CallArg.getLhs callArgs).length)
      (hj : i < p.header.outputs.values.length),
      ∃ τ, LMonoTy.subst S τ = p.header.outputs.values[i] ∧
        ts.find? ((CallArg.getLhs callArgs)[i]) = some (.forAll [] τ) := by
    intro i hi hj
    obtain ⟨hj', hv⟩ := List.getElem_of_eq_map houtV hj
    refine ⟨_, ?_, hout i hi hj'⟩
    rw [hv]
    exact (hcomp _ (List.mem_append_right _ (List.getElem_mem hj'))).symm
  obtain ⟨hstore, hfresh⟩ := callEntry_conforms S ht0 (hmatch.of_keys_eq hinK.symm houtK.symm)
    (hinK ▸ hproc.inputsNodup) (houtK ▸ hproc.outputsNodup)
    (Procedure.instantiateTypes_oldNamesFresh hinst hproc.oldNamesFresh) hgroundIn hin' hout' hs
    hentry
  obtain ⟨hstoreR, hfreshR⟩ := instStore_conforms ht0 hinst hms hstore hfresh
  rw [← hS1] at hstoreR
  have hbt := hproc.bodyTyped
  rw [hbody] at hbt
  cases hbt with
  | structured _ C2 ts2 _ hss =>
    have hS1ground : ∀ a ∈ proc.header.typeArgs, (LMonoTy.subst S1 (.ftvar a)).IsGround := by
      intro a ha
      rw [hS1g, LMonoTy.subst_ofScopes_zip_map_ftvar (fun b => LMonoTy.subst S
        (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ0]) (.ftvar b))) hproc.typeArgsNodup ha]
      exact hparams a ha
    exact ⟨mapStmtsTys (LMonoTy.subst S1) ss, C1, S1, procBodyScopes ts0 proc,
      hbodyp ss false hbody,
      reachable_configs_wellTyped_of_typed S1 hss rfl
        (body_ground hP hfind hbody hss hS1ground) hstoreR hfreshR⟩

/-- One step of progress. A well-typed configuration, in a program whose procedure table contains
    the program's procedures and whose procedures have structured bodies or none, is finished, is
    exiting, steps, or runs next a call that does not finish. -/
theorem coreStep_progress {C0 : LContext CoreLParams} {ts0 : TypeScopes} {P : Program}
    {π : String → Option Procedure} {F : Expression.Factory} {S : Subst} {L : List String}
    {cfg : CoreConfig} {C' : LContext CoreLParams} {ts' tsf : TypeScopes}
    (hP : ProgramWellTyped C0 ts0 P)
    (hπ : ∀ (n : String) p, Program.Procedure.find? P n = some p → π n = some p)
    (hstruct : CalleesStructured P) (hty : ConfigWellTyped P F S L cfg C' ts' tsf) :
    (∃ ρ, cfg = .terminal ρ) ∨ (∃ l ρ, cfg = .exiting l ρ) ∨
      (∃ evs cfg', CoreStepE π cfg evs cfg') ∨ CallDoesNotFinish π cfg := by
  induction hty with
  | terminal => exact .inl ⟨_, rfl⟩
  | exiting => exact .inr (.inl ⟨_, _, rfl⟩)
  | @stmts L ss ss0 ρ C ts C' ts' tsf hfac hmap hstore hfresh hfloor hgr hss =>
    cases ss with
    | nil => exact .inr (.inr (.inl ⟨_, _, .step_stmts_nil⟩))
    | cons s rest => exact .inr (.inr (.inl ⟨_, _, .step_stmts_cons⟩))
  | seq hinner hfloor hmap hgr hrest ih =>
    rcases ih with ⟨ρ', rfl⟩ | ⟨l, ρ', rfl⟩ | ⟨evs, cfg', hstep⟩ | hcall
    · exact .inr (.inr (.inl ⟨_, _, .step_seq_done⟩))
    · exact .inr (.inr (.inl ⟨_, _, .step_seq_exit⟩))
    · exact .inr (.inr (.inl ⟨_, _, .step_seq_inner hstep⟩))
    · exact .inr (.inr (.inr (.seq hcall)))
  | @block L Lin label σp inner tsp Cb tsb C ts' tsf hlabels hstore hfresh hfloor hext hinner
      hequiv ih =>
    rcases ih with ⟨ρ', rfl⟩ | ⟨l, ρ', rfl⟩ | ⟨evs, cfg', hstep⟩ | hcall
    · exact .inr (.inr (.inl ⟨_, _, .step_block_done⟩))
    · by_cases hlab : label = some l
      · exact .inr (.inr (.inl ⟨_, _, .step_block_exit_match hlab⟩))
      · exact .inr (.inr (.inl ⟨_, _, .step_block_exit_mismatch hlab⟩))
    · exact .inr (.inr (.inl ⟨_, _, .step_block_body hstep⟩))
    · exact .inr (.inr (.inr (.block hcall)))
  | @stmt L s s0 ρ C ts C' ts' tsf hfac hmap hstore hfresh hfloor hgr hstmt =>
    subst hfac
    cases s with
    | cmd c =>
      obtain ⟨c0, rfl, hc0⟩ := mapStmtTys_eq_cmd hmap
      cases c with
      | cmd cc =>
        obtain ⟨c1, rfl⟩ := mapCmdTys_eq_cmd hc0
        cases hstmt with
        | cmd =>
          rename_i hcmd
          cases hcmd with
          | cmd =>
            rename_i hc
            have hinit : ∀ x xty e md, cc = .init x xty e md → LTy.GroundMono xty := by
              intro x xty e md heq
              subst heq
              exact hgr
            obtain ⟨σ', evs, heval⟩ := CmdWellTyped.progress hc hc0 hinit hstore hfresh
            exact .inr (.inr (.inl ⟨_, _, .step_cmd (.cmd_sem heval)⟩))
      | call n tyArgs' callArgs' md =>
        obtain ⟨tyArgs, callArgs, rfl, htyArgs, hargs⟩ := mapCmdTys_eq_call hc0
        cases hstmt with
        | cmd =>
          rename_i hcmd
          rcases CmdExtWellTyped.call_progress hP hcmd htyArgs hargs (hπ n) hstruct hgr hstore
            with hstep | hcall
          · exact .inr (.inr (.inl hstep))
          · exact .inr (.inr (.inr hcall))
    | block label body md =>
      exact .inr (.inr (.inl ⟨_, _, .step_block⟩))
    | ite c thenb elseb md =>
      obtain ⟨c0, tss0, ess0, rfl, hcond, -, -⟩ := mapStmtTys_eq_ite hmap
      cases hstmt with
      | ite_det =>
        rename_i hcondTy _ _ _
        simp only [ExprOrNondet.map] at hcond
        subst hcond
        obtain ⟨v, hv, hbool⟩ := eval_bool_progress_inst S hcondTy hstore
        rcases hbool with rfl | rfl
        · exact .inr (.inr (.inl ⟨_, _, .step_ite_true hv⟩))
        · exact .inr (.inr (.inl ⟨_, _, .step_ite_false hv⟩))
      | ite_nondet =>
        simp only [ExprOrNondet.map] at hcond
        subst hcond
        exact .inr (.inr (.inl ⟨_, _, .step_ite_nondet_true⟩))
    | loop g m inv body md =>
      obtain ⟨g0, m0, i0, b0, rfl, hg, -, -, -⟩ := mapStmtTys_eq_loop hmap
      cases hstmt with
      | loop =>
        rename_i hguard _ _ _ _
        cases g0 with
        | det gd =>
          simp only [ExprOrNondet.map] at hg
          subst hg
          obtain ⟨v, hv, hbool⟩ := eval_bool_progress_inst S (hguard gd rfl) hstore
          rcases hbool with rfl | rfl
          · exact .inr (.inr (.inl ⟨_, _, .step_loop_enter hv⟩))
          · exact .inr (.inr (.inl ⟨_, _, .step_loop_exit hv⟩))
        | nondet =>
          simp only [ExprOrNondet.map] at hg
          subst hg
          exact .inr (.inr (.inl ⟨_, _, .step_loop_nondet_enter⟩))
    | exit label md => exact .inr (.inr (.inl ⟨_, _, .step_exit⟩))
    | typeDecl tc md => exact .inr (.inr (.inl ⟨_, _, .step_typeDecl⟩))

/-- A well-typed configuration that runs next a call whose callee has no complete run runs a
    call whose callee runs on without finishing. After the call's entry, every configuration
    reachable in the callee is well typed, with the substitution that instantiates the callee's
    type parameters, so it steps, or it again runs next such a call. A finished configuration
    would be a complete run. -/
private theorem callRunsForever_of_wellTyped {C0 : LContext CoreLParams} {ts0 : TypeScopes}
    {P : Program} {π : String → Option Procedure} {F : Expression.Factory} {S : Subst}
    {L : List String}
    {cfg : CoreConfig} {C' : LContext CoreLParams} {ts' tsf : TypeScopes}
    (hP : ProgramWellTyped C0 ts0 P) (ht0 : ∀ x, ts0.find? x = none)
    (hπ : ∀ (n : String) p, Program.Procedure.find? P n = some p → π n = some p)
    (hstruct : CalleesStructured P)
    (hty : ConfigWellTyped P F S L cfg C' ts' tsf) (hcall : CallDoesNotFinish π cfg) :
    CallRunsForever π cfg := by
  refine CallRunsForever.coinduct π
    (fun c => (∃ F S L C' ts' tsf, ConfigWellTyped P F S L c C' ts' tsf) ∧ CallDoesNotFinish π c)
    ?_ cfg ⟨⟨F, S, L, C', ts', tsf, hty⟩, hcall⟩
  rintro a ⟨⟨F, S, L, C', ts', tsf, hty⟩, hcdnf⟩
  cases hcdnf with
  | @call n tyArgs' callArgs' md ρ p σAO hcallee hno hentry hrun =>
    cases hty with
    | stmt hfac hmap hstore hfresh hfloor hgr hstmt =>
      subst hfac
      obtain ⟨c0, rfl, hc0⟩ := mapStmtTys_eq_cmd hmap
      obtain ⟨tyArgs, callArgs, rfl, htyArgs, hargs⟩ := mapCmdTys_eq_call hc0
      cases hstmt with
      | cmd =>
        rename_i hcmd
        obtain ⟨ss, C1, S1, tsr, hbody, hreach⟩ := call_callee_reachable hP ht0 hcmd htyArgs
          hargs (hπ n) hstruct hgr hcallee hno hentry hstore
        refine .inl ⟨n, tyArgs', callArgs', md, ρ, p, σAO, ss, hcallee, hentry, hbody, ?_, rfl⟩
        intro evs cfg' hstar
        rcases hreach evs cfg' hstar with rfl | hty'
        · exact .inl ⟨_, _, .step_block⟩
        · rcases coreStep_progress hP hπ hstruct hty' with
            ⟨ρ', rfl⟩ | ⟨l, ρ', rfl⟩ | hstep | hcall'
          · exfalso
            refine hrun ⟨ρ'.store, evs, ?_⟩
            rw [hbody]
            exact .structured hstar
          · exfalso
            cases hty' with
            | exiting _ hlabel _ => exact List.not_mem_nil hlabel
          · exact .inl hstep
          · exact .inr ⟨⟨_, _, _, _, _, _, hty'⟩, hcall'⟩
  | seq hinner =>
    cases hty with
    | seq hinnerTy _ _ _ _ =>
      exact .inr (.inl ⟨_, _, ⟨⟨_, _, _, _, _, _, hinnerTy⟩, hinner⟩, rfl⟩)
  | block hinner =>
    cases hty with
    | block _ _ _ _ _ hinnerTy _ =>
      exact .inr (.inr ⟨_, _, _, ⟨⟨_, _, _, _, _, _, hinnerTy⟩, hinner⟩, rfl⟩)

/-- One step of progress, with a callee that runs on. A well-typed configuration is finished, is
    exiting, steps, or runs next a call whose callee runs on without finishing. The procedures
    may have type parameters. The hypotheses are needed for these reasons:
    * The ambient scopes `ts0` are empty. The frame of a callee starts from the empty store, so
      a variable of the ambient scopes would be unbound in it: for `q() { assert g == 0 }` with
      `g` in the ambient scopes, the callee gets stuck.
    * The procedure table contains the program's procedures.
    * The program's procedures have structured bodies or none (`CalleesStructured`), since a
      control-flow-graph body carries no typing. A call to an opaque procedure (`Body.isOpaque`)
      runs its contract: it havocs the outputs, which may keep their entry values, and writes
      them back, so it steps.
    A well-typed program also guarantees that every type variable in a body's local declarations
    and call type arguments is a type parameter of its procedure
    (`ProgramWellTyped.calleesTyVarsScoped`). -/
theorem coreStep_progress_forever {C0 : LContext CoreLParams} {ts0 : TypeScopes} {P : Program}
    {π : String → Option Procedure} {F : Expression.Factory} {S : Subst} {L : List String}
    {cfg : CoreConfig} {C' : LContext CoreLParams} {ts' tsf : TypeScopes}
    (hP : ProgramWellTyped C0 ts0 P) (ht0 : ∀ x, ts0.find? x = none)
    (hπ : ∀ (n : String) p, Program.Procedure.find? P n = some p → π n = some p)
    (hstruct : CalleesStructured P)
    (hty : ConfigWellTyped P F S L cfg C' ts' tsf) :
    (∃ ρ, cfg = .terminal ρ) ∨ (∃ l ρ, cfg = .exiting l ρ) ∨
      (∃ evs cfg', CoreStepE π cfg evs cfg') ∨ CallRunsForever π cfg := by
  rcases coreStep_progress hP hπ hstruct hty with hterm | hexit | hstep | hcall
  · exact .inl hterm
  · exact .inr (.inl hexit)
  · exact .inr (.inr (.inl hstep))
  · exact .inr (.inr (.inr
      (callRunsForever_of_wellTyped hP ht0 hπ hstruct hty hcall)))

/-- The start of a structured procedure body, a block labeled `""` around the body, steps. -/
private theorem start_steps {π : String → Option Procedure} {ss : List Statement}
    {ρ : Env Expression} :
    ∃ evs cfg, CoreStepE π (.stmt (Stmt.block "" ss #[]) ρ) evs cfg :=
  ⟨_, _, .step_block⟩

/-- No well-typed configuration without enclosing block labels is exiting: an exit targets an
    enclosing label. -/
private theorem ConfigWellTyped.not_exiting_nil {P : Program} {F : Expression.Factory}
    {S : Subst} {l : String} {ρ : Env Expression} {C' : LContext CoreLParams}
    {ts' tsf : TypeScopes} (h : ConfigWellTyped P F S [] (.exiting l ρ) C' ts' tsf) : False := by
  cases h with
  | exiting _ hlabel _ => exact List.not_mem_nil hlabel

/-- Progress for the configurations reachable from the start of a structured body, given
    progress for the well-typed configurations `W`: every reachable configuration other than the
    start is in `W`, a configuration in `W` is finished, exiting, steps, or has the property `Q`,
    and none is exiting. Then every reachable configuration is terminal, steps, or has `Q`. -/
private theorem reachable_progress {π : String → Option Procedure} {ss : List Statement}
    {ρ : Env Expression} {W Q : CoreConfig → Prop}
    (hreach : ∀ evs cfg, CoreStepStarE π (.stmt (Stmt.block "" ss #[]) ρ) evs cfg →
      cfg = .stmt (Stmt.block "" ss #[]) ρ ∨ W cfg)
    (hprog : ∀ cfg, W cfg → (∃ ρ', cfg = .terminal ρ') ∨ (∃ l ρ', cfg = .exiting l ρ') ∨
      (∃ evs cfg', CoreStepE π cfg evs cfg') ∨ Q cfg)
    (hexit : ∀ l ρ', ¬ W (.exiting l ρ')) :
    ∀ evs cfg, CoreStepStarE π (.stmt (Stmt.block "" ss #[]) ρ) evs cfg →
      (∃ ρ', cfg = .terminal ρ') ∨ (∃ evs' cfg', CoreStepE π cfg evs' cfg') ∨ Q cfg := by
  intro evs cfg hstar
  rcases hreach evs cfg hstar with hstart | hty
  · subst hstart
    exact .inr (.inl start_steps)
  · rcases hprog cfg hty with hterm | ⟨l, ρ', rfl⟩ | hstep | hq
    · exact .inl hterm
    · exact absurd hty (hexit l ρ')
    · exact .inr (.inl hstep)
    · exact .inr (.inr hq)

/-- Progress for a procedure body, with callees that run on. Run the body of an instance of a
    procedure of a well-typed program, at any ground type arguments `tys`, from a store that
    conforms to the scopes the instance's body is typed in and binds no other variable. The
    procedure may have type parameters, and the start is in the instance with those parameters
    replaced by `tys`. Every configuration reached is terminal, steps, or runs next a call whose
    callee runs on without finishing. As `coreStep_progress_forever` does, and for the reasons
    given there, it assumes empty ambient scopes, a procedure table that contains the
    program's procedures, and structured bodies or none.
    It also assumes that the type arguments are ground, since no value has a type with a type
    variable.
    A procedure without type parameters is its own instance at `tys = []`. -/
theorem reachable_configs_progress_forever {C0 : LContext CoreLParams} {ts0 : TypeScopes}
    {P : Program} {proc : Procedure} {md : MetaData Expression} {ss : List Statement}
    {π : String → Option Procedure} {ρ : Env Expression} {tys : List Expression.Ty}
    {inst : Procedure} {ssI : List Statement}
    (hP : ProgramWellTyped C0 ts0 P) (ht0 : ∀ x, ts0.find? x = none)
    (hmem : Decl.proc proc md ∈ P.decls)
    {opq : Bool} (hbody : proc.body = .structured ss opq)
    (hπ : ∀ (n : String) p, Program.Procedure.find? P n = some p → π n = some p)
    (hstruct : CalleesStructured P)
    (htys : ∀ ty ∈ tys, LTy.GroundMono ty) (hinst : proc.instantiateTypes tys = some inst)
    (hbodyI : inst.body = .structured ssI opq)
    (hρ : StoreHasTyping ρ.factory ρ.store (procBodyScopes ts0 inst).find?)
    (hfresh : StoreFresh ρ.store (procBodyScopes ts0 inst).find?) :
    ∀ evs cfg, CoreStepStarE π (.stmt (Stmt.block "" ssI #[]) ρ) evs cfg →
      (∃ ρ', cfg = .terminal ρ') ∨ (∃ evs' cfg', CoreStepE π cfg evs' cfg') ∨
        CallRunsForever π cfg := by
  have hfindP : Program.Procedure.find? P proc.header.name.name = some proc :=
    find?_of_mem_of_programNamesOfKind_nodup P proc md (hP.1 DeclKind.proc) hmem
  obtain ⟨ms, hms, -, -, hbodyp⟩ := Procedure.instantiateTypes_spec hinst
  obtain ⟨S1, hS1⟩ : ∃ S1 : Subst,
      S1 = Strata.Util.HMaps.ofScopes [proc.header.typeArgs.zip ms] := ⟨_, rfl⟩
  rw [← hS1] at hbodyp
  have hmap : ssI = mapStmtsTys (LMonoTy.subst S1) ss :=
    (Imperative.Body.structured.inj (hbodyI.symm.trans (hbodyp ss opq hbody))).1
  obtain ⟨C, hproc⟩ := hP.procWellTyped hmem
  obtain ⟨hρR, hfreshR⟩ := instStore_conforms ht0 hinst hms hρ hfresh
  rw [← hS1] at hρR
  have hS1ground : ∀ a ∈ proc.header.typeArgs, (LMonoTy.subst S1 (.ftvar a)).IsGround := by
    intro a ha
    obtain ⟨hmsLen, hmsMem⟩ := Lambda.mapM_toMonoType?_spec hms
    have hlen : proc.header.typeArgs.length = ms.length := by
      rcases Procedure.instantiateTypes_length hinst with hnil | hl
      · rw [hnil] at ha
        exact absurd ha List.not_mem_nil
      · rw [hmsLen]
        exact hl.symm
    obtain ⟨m, hm, hsub⟩ := LMonoTy.subst_ofScopes_zip_ftvar_mem hlen hproc.typeArgsNodup ha
    rw [hS1, hsub]
    obtain ⟨t, ht, htm⟩ := hmsMem m hm
    obtain ⟨τ, rfl, hτ⟩ := htys t ht
    obtain rfl : τ = m := Option.some.inj htm
    exact hτ
  have hbt := hproc.bodyTyped
  rw [hbody] at hbt
  cases hbt with
  | structured _ C2 ts2 _ hss =>
    have hground : Statements.Ground ssI := by
      rw [hmap]
      exact body_ground hP hfindP hbody hss hS1ground
    have hreach := reachable_configs_wellTyped_of_typed (π := π) S1 hss hmap hground hρR hfreshR
    exact reachable_progress hreach
      (fun _ hty => coreStep_progress_forever hP ht0 hπ hstruct hty)
      (fun _ _ hty => hty.not_exiting_nil)

end -- public section

end TypeSpec
end Core
