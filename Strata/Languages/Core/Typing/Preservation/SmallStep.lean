/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Spec.TypingSpec
public import Strata.Languages.Core.Typing.Spec.ConfigTyping
public import Strata.Languages.Core.Typing.Props.TypingSpecProps
public import Strata.DL.Imperative.CmdSemanticsProps
public import Strata.Languages.Core.StatementSemantics
public import Strata.DL.Lambda.LExprDenoteEval
import Strata.DL.Lambda.LExprDenoteEvalProps
import Strata.Languages.Core.StatementProps
import all Strata.Languages.Core.Typing.Spec.ConfigTyping
import all Strata.DL.Lambda.LTyProps
import all Strata.DL.Imperative.Cmd

/-! ## Type preservation for Core's small-step semantics

A configuration of the small-step semantics is well typed when its statements are the images
under a type substitution `S` of statements typed by the annotated typing relations, every store
it holds conforms to the scopes that type those statements with `S` applied and binds no
variable the scopes do not declare, and its declarations are at ground types
(`ConfigWellTyped`). The empty substitution gives configurations that hold the typed statements
themselves. One step, and so every run, from a well-typed configuration ends in a well-typed
configuration, whatever the procedure table is.

Key results:
* `ConfigWellTyped`: the typing of configurations.
* `coreStep_preserves_configWellTyped`, `coreStepStar_preserves_configWellTyped`: one step and
  every run preserve it.
* `reachable_configs_wellTyped`: every configuration reachable from the start of a well-typed
  structured procedure body, other than the start itself, is well typed, when the body starts in
  a store conforming to its scopes. `reachable_configs_wellTyped_of_typed` states it for the
  image under a type substitution of any well-typed structured body, and
  `reachable_configs_wellTyped_of_typed_empty` for a body that is itself well typed.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative
open Strata.Util (HMaps)

public section

/-- A declaration `init x : T`, whose type `T` is the monotype `m` with `S` applied, that ends in
    scopes equivalent to the starting scopes with `x` inserted at `m`, takes a store conforming
    to the starting scopes with `S` applied, and binding nothing outside them, to one doing the
    same for the ending scopes. -/
private theorem init_preserves_store {F : Expression.Factory} {S : Subst} {σ σ' : CoreStore}
    {ts ts' : TypeScopes} {x : Expression.Ident} {xty : LTy} {mty : LMonoTy}
    {e : ExprOrNondet Expression} {md : MetaData Expression} {evs : Trace Expression}
    (hxty : xty = .forAll [] mty)
    (hequiv : HMaps.Equiv ts' (ts.insert x (.forAll [] mty)))
    (hs : StoreHasTyping F σ (ts.instVarTyping S)) (hfresh : StoreFresh σ ts.find?)
    (he : EvalCmdE Expression F σ (.init x (mapLTyTys (LMonoTy.subst S) xty) e md) σ' evs) :
    StoreHasTyping F σ' (ts'.instVarTyping S) ∧ StoreFresh σ' ts'.find? := by
  have hΓ : ∀ y, ts'.find? y = none → y ≠ x ∧ ts.find? y = none := by
    intro y hy
    have hfind := HMaps.Equiv.find? hequiv y
    have hy' : ts'.find? y = none := hy
    have hyx : y ≠ x := by
      intro hyx
      subst hyx
      simp only [hfind, HMaps.find?_insert_self] at hy'
      exact nomatch hy'
    refine ⟨hyx, ?_⟩
    rw [HMaps.find?_insert_ne ts y x _ hyx] at hfind
    show ts.find? y = none
    rw [← hfind]
    exact hy'
  refine ⟨?_, EvalCmdE.init_storeFresh hΓ hfresh he⟩
  rw [TypeScopes.instVarTyping_insert hequiv]
  subst hxty
  exact EvalCmdE.init_storeHasTyping he hs

/-- A base command that is not an `init`, well typed to scopes equivalent to its starting scopes,
    takes a store that conforms to the starting scopes with `S` applied and binds nothing outside
    them to one that conforms to the ending scopes with `S` applied and binds nothing outside
    them. -/
private theorem preserves_store_of_not_init {F : Expression.Factory} {S : Subst}
    {σ σ' : CoreStore} {ts ts' : TypeScopes} {c : Cmd Expression} {evs : Trace Expression}
    (hequiv : HMaps.Equiv ts' ts) (he : EvalCmdE Expression F σ c σ' evs)
    (hnoinit : ∀ x ty e md, c ≠ .init x ty e md)
    (hs : StoreHasTyping F σ (ts.instVarTyping S)) (hfresh : StoreFresh σ ts.find?) :
    StoreHasTyping F σ' (ts'.instVarTyping S) ∧ StoreFresh σ' ts'.find? := by
  refine ⟨storeHasTyping_of_equiv hequiv (EvalCmdE.preserves_storeHasTyping he hnoinit hs),
    storeFresh_of_equiv hequiv fun y hy => ?_⟩
  have hdef : y ∉ Cmd.definedVars c := by
    cases c with
    | init x ty e md => exact absurd rfl (hnoinit x ty e md)
    | _ => simp only [Cmd.definedVars, List.not_mem_nil, not_false_eq_true]
  exact evalCmdE_preserves_none_of_not_def he (hfresh y hy) hdef

/-- A base command, well typed from scopes `ts` to `ts'`, and then mapped by the substitution
    `S`, takes a store conforming to `ts` with `S` applied that binds nothing outside `ts` to a
    store conforming to `ts'` with `S` applied that binds nothing outside `ts'`: the semantics
    checks the type of each value `init` and `set` write. -/
private theorem CmdWellTyped.preserves_store {F : Expression.Factory}
    {C : LContext CoreLParams} {S : Subst}
    {ts ts' : TypeScopes} {c0 c : Cmd Expression} {σ σ' : CoreStore} {evs : Trace Expression}
    (hc : CmdWellTyped C ts c0 ts')
    (hmap : (.cmd c : Command) = mapCmdTys (LMonoTy.subst S) (.cmd c0))
    (hs : StoreHasTyping F σ (ts.instVarTyping S)) (hfresh : StoreFresh σ ts.find?)
    (he : EvalCmdE Expression F σ c σ' evs) :
    StoreHasTyping F σ' (ts'.instVarTyping S) ∧ StoreFresh σ' ts'.find? := by
  cases hc with
  | init_det =>
    rename_i _ _ hxty _ _ hequiv
    simp only [mapCmdTys_init, ExprOrNondet.map] at hmap
    cases hmap
    exact init_preserves_store hxty hequiv hs hfresh he
  | init_nondet =>
    rename_i _ hxty _ hequiv
    simp only [mapCmdTys_init, ExprOrNondet.map] at hmap
    cases hmap
    exact init_preserves_store hxty hequiv hs hfresh he
  | set_det | set_nondet | assert | assume | cover =>
    rename_i hequiv
    simp only [mapCmdTys_set, mapCmdTys_assert, mapCmdTys_assume, mapCmdTys_cover,
      ExprOrNondet.map] at hmap
    cases hmap
    exact preserves_store_of_not_init hequiv he (fun _ _ _ _ hne => nomatch hne) hs hfresh

/-- A well-typed extended command, mapped by the substitution `S` and run against any procedure
    table, takes a store conforming to its starting scopes with `S` applied that binds nothing
    outside them to a store conforming to its ending scopes with `S` applied that binds nothing
    outside them. A call writes back each output at the type of the value the caller variable
    held. -/
private theorem CmdExtWellTyped.preserves_store {π : String → Option Procedure}
    {F : Expression.Factory} {C : LContext CoreLParams} {P : Program} {S : Subst}
    {ts ts' : TypeScopes} {c0 c : Command} {σ σ' : CoreStore} {evs : Trace Expression}
    (hc : CmdExtWellTyped C P ts c0 ts') (hmap : c = mapCmdTys (LMonoTy.subst S) c0)
    (hs : StoreHasTyping F σ (ts.instVarTyping S)) (hfresh : StoreFresh σ ts.find?)
    (he : EvalCommandE π F σ c σ' evs) :
    StoreHasTyping F σ' (ts'.instVarTyping S) ∧ StoreFresh σ' ts'.find? := by
  cases hc with
  | cmd =>
    rename_i c1 hcmd
    obtain ⟨c2, hc2⟩ := mapCmdTys_cmd_exists (LMonoTy.subst S) c1
    rw [hc2] at hmap
    subst hmap
    cases he with
    | cmd_sem hsem => exact CmdWellTyped.preserves_store hcmd hc2.symm hs hfresh hsem
  | call =>
    rename_i hequiv
    rw [mapCmdTys_call] at hmap
    subst hmap
    cases he with
    | call_sem _ _ _ _ hexit | call_abstract_sem _ _ _ _ hexit =>
      obtain ⟨_, outputVals, _, hupd, hrel⟩ := hexit
      refine ⟨fun y ty hy => ?_,
        storeFresh_of_equiv hequiv fun y hy => UpdateStates_preserves_none hupd (hfresh y hy)⟩
      have hy' : ts.instVarTyping S y = some ty := by
        rw [TypeScopes.instVarTyping_of_equiv hequiv] at hy
        exact hy
      have hslot := hs y ty hy'
      exact UpdateStates_typedAt hupd hrel hslot hslot

/-- A configuration that runs a statement list in a block, from the store the block keeps as its
    parent store, is well typed when the list is the image under `S` of a typed list. The block
    ends in scopes equivalent to the scopes the list is typed from. -/
private theorem blockStmts_configWellTyped {P : Program} {F : Expression.Factory} {S : Subst}
    {L Lin : List String} {label : Option String} {ρ : Env Expression}
    {C Cb : LContext CoreLParams} {ts tsb ts' tsf : TypeScopes} {ss ss0 : List Statement}
    (hlabels : ∀ l ∈ Lin, l ∈ blockLabels label L) (hfac : ρ.factory = F)
    (hmap : ss = mapStmtsTys (LMonoTy.subst S) ss0)
    (hstore : StoreHasTyping F ρ.store (ts.instVarTyping S))
    (hfresh : StoreFresh ρ.store ts.find?) (hfloor : ScopeExtends tsf ts)
    (hgr : Statements.Ground ss) (hss : StatementsWellTyped P C ts Lin ss0 Cb tsb)
    (hequiv : HMaps.Equiv ts' ts) :
    ConfigWellTyped P F S L (.block label ρ.store (.stmts ss ρ)) C ts' tsf :=
  .block hlabels hstore hfresh hfloor (StatementsWellTyped.scopeExtends hss)
    (.stmts hfac hmap hstore hfresh (fun _ _ h => h) hgr hss) hequiv

/-- A finished configuration whose store conforms to scopes `ts` with `S` applied and binds
    nothing outside them is well typed at any scopes `ts'` equivalent to `ts`. -/
private theorem terminal_configWellTyped {P : Program} {F : Expression.Factory} {S : Subst}
    {L : List String} {ρ : Env Expression} {C' : LContext CoreLParams} {ts ts' tsf : TypeScopes}
    (hfac : ρ.factory = F) (hequiv : HMaps.Equiv ts' ts)
    (hstore : StoreHasTyping F ρ.store (ts.instVarTyping S))
    (hfresh : StoreFresh ρ.store ts.find?) :
    ConfigWellTyped P F S L (.terminal ρ) C' ts' tsf :=
  .terminal hfac (storeHasTyping_of_equiv hequiv hstore) (storeFresh_of_equiv hequiv hfresh)

/-- Entering a branch of a well-typed conditional gives a well-typed configuration: the branch
    runs in a block that keeps the entry store as its parent store. The branch is the else
    branch for `false` and the then branch for `true`, whether the condition is deterministic or
    not. -/
private theorem enterIte_configWellTyped {P : Program} {F : Expression.Factory} {S : Subst}
    {L : List String} {ρ : Env Expression} {C C' : LContext CoreLParams}
    {ts ts' tsf : TypeScopes} {c : ExprOrNondet Expression} {thenb elseb : List Statement}
    {md : MetaData Expression} {s0 : Statement} (b : Bool) (hfac : ρ.factory = F)
    (hmap : (.ite c thenb elseb md : Statement) = mapStmtTys (LMonoTy.subst S) s0)
    (hstore : StoreHasTyping F ρ.store (ts.instVarTyping S))
    (hfresh : StoreFresh ρ.store ts.find?) (hfloor : ScopeExtends tsf ts)
    (hgr : Statement.Ground (.ite c thenb elseb md))
    (hstmt : StatementWellTyped P C ts L s0 C' ts') :
    ConfigWellTyped P F S L (.block none ρ.store (.stmts (cond b thenb elseb) ρ)) C' ts' tsf := by
  obtain ⟨c0, tss0, ess0, rfl, -, hthen0, helse0⟩ := mapStmtTys_eq_ite hmap
  cases hstmt with
  | ite_det | ite_nondet =>
    rename_i hthen helse hequiv
    cases b
    · exact blockStmts_configWellTyped (Lin := _) (fun _ hl => hl) hfac helse0 hstore hfresh
        hfloor hgr.2 helse hequiv
    · exact blockStmts_configWellTyped (Lin := _) (fun _ hl => hl) hfac hthen0 hstore hfresh
        hfloor hgr.1 hthen hequiv

/-- Entering the body of a well-typed loop gives a well-typed configuration: the body runs in a
    block that keeps the entry store as its parent store, followed by the loop itself. -/
private theorem enterLoop_configWellTyped {P : Program} {F : Expression.Factory} {S : Subst}
    {L : List String} {ρ : Env Expression} {C C' : LContext CoreLParams}
    {ts ts' tsf : TypeScopes} {g : ExprOrNondet Expression} {m : Option Expression.Expr}
    {inv : List (String × Expression.Expr)} {body : List Statement} {md : MetaData Expression}
    {s0 : Statement} (hfac : ρ.factory = F)
    (hmap : (.loop g m inv body md : Statement) = mapStmtTys (LMonoTy.subst S) s0)
    (hstore : StoreHasTyping F ρ.store (ts.instVarTyping S))
    (hfresh : StoreFresh ρ.store ts.find?) (hfloor : ScopeExtends tsf ts)
    (hgr : Statement.Ground (.loop g m inv body md))
    (hstmt : StatementWellTyped P C ts L s0 C' ts') :
    ConfigWellTyped P F S L
      (.seq (.block none ρ.store (.stmts body ρ)) [.loop g m inv body md]) C' ts' tsf := by
  have hloop := hstmt
  obtain ⟨g0, m0, i0, bss0, rfl, -, -, -, hbody0⟩ := mapStmtTys_eq_loop hmap
  cases hstmt with
  | loop =>
    rename_i _ _ _ hbody hequiv
    have hrest := StatementsWellTyped.cons _ _ _ _ _ _ _ _ _ hloop
      (StatementsWellTyped.nil _ _ _ _ (HMaps.Equiv.refl _))
    have hrest0 : [(.loop g m inv body md : Statement)] =
        mapStmtsTys (LMonoTy.subst S)
          [(.loop g0 m0 i0 bss0 md : Statement)] := by
      rw [mapStmtsTys_cons, mapStmtsTys_nil]
      exact congrArg (fun x => [x]) hmap
    exact .seq (blockStmts_configWellTyped (Lin := _) (fun _ hl => hl) hfac hbody0 hstore hfresh
      hfloor hgr hbody (HMaps.Equiv.refl _)) hfloor hrest0 ⟨hgr, trivial⟩ hrest

/-- A label that an exit can reach through a block that is not labeled with it is a label of the
    blocks around. -/
private theorem mem_of_mem_blockLabels {label : Option String} {l : String} {L : List String}
    (hne : label ≠ some l) (hmem : l ∈ blockLabels label L) : l ∈ L := by
  cases label with
  | none => exact hmem
  | some name =>
    simp only [blockLabels, List.mem_cons] at hmem
    rcases hmem with hl | hl
    · exact absurd (congrArg some hl.symm) hne
    · exact hl

/-- One small-step of Core preserves well-typedness of a configuration, for every procedure
    table: the semantics checks the type of each value it writes, so a call cannot store an
    ill-typed value. -/
theorem coreStep_preserves_configWellTyped {π : String → Option Procedure} {P : Program}
    {F : Expression.Factory} {S : Subst} {L : List String} {cfg cfg' : CoreConfig}
    {evs : Trace Expression} {C' : LContext CoreLParams} {ts' tsf : TypeScopes}
    (hstep : CoreStepE π cfg evs cfg') (hty : ConfigWellTyped P F S L cfg C' ts' tsf) :
    ConfigWellTyped P F S L cfg' C' ts' tsf := by
  induction hstep generalizing L C' ts' tsf with
  | step_cmd heval =>
    cases hty with
    | stmt hfac hmap hstore hfresh _ hgr hstmt =>
      subst hfac
      obtain ⟨c0, rfl, hc0⟩ := mapStmtTys_eq_cmd hmap
      cases hstmt with
      | cmd =>
        rename_i hcmd
        obtain ⟨hstore', hfresh'⟩ := CmdExtWellTyped.preserves_store hcmd hc0 hstore hfresh heval
        exact .terminal rfl hstore' hfresh'
  | step_block =>
    cases hty with
    | stmt hfac hmap hstore hfresh hfloor hgr hstmt =>
      obtain ⟨body0, rfl, hbody0⟩ := mapStmtTys_eq_block hmap
      cases hstmt with
      | block =>
        rename_i hbody hequiv
        exact blockStmts_configWellTyped (Lin := _ :: _) (fun _ hl => hl) hfac hbody0 hstore
          hfresh hfloor hgr hbody hequiv
  | step_ite_true _ =>
    cases hty with
    | stmt hfac hmap hstore hfresh hfloor hgr hstmt =>
      exact enterIte_configWellTyped true hfac hmap hstore hfresh hfloor hgr hstmt
  | step_ite_false _ =>
    cases hty with
    | stmt hfac hmap hstore hfresh hfloor hgr hstmt =>
      exact enterIte_configWellTyped false hfac hmap hstore hfresh hfloor hgr hstmt
  | step_ite_nondet_true =>
    cases hty with
    | stmt hfac hmap hstore hfresh hfloor hgr hstmt =>
      exact enterIte_configWellTyped true hfac hmap hstore hfresh hfloor hgr hstmt
  | step_ite_nondet_false =>
    cases hty with
    | stmt hfac hmap hstore hfresh hfloor hgr hstmt =>
      exact enterIte_configWellTyped false hfac hmap hstore hfresh hfloor hgr hstmt
  | step_loop_enter _ | step_loop_nondet_enter =>
    cases hty with
    | stmt hfac hmap hstore hfresh hfloor hgr hstmt =>
      exact enterLoop_configWellTyped hfac hmap hstore hfresh hfloor hgr hstmt
  | step_loop_exit _ | step_loop_nondet_exit =>
    cases hty with
    | stmt hfac hmap hstore hfresh _ hgr hstmt =>
      obtain ⟨g0, m0, i0, bss0, rfl, -, -, -, -⟩ := mapStmtTys_eq_loop hmap
      cases hstmt with
      | loop =>
        rename_i _ _ _ _ hequiv
        exact terminal_configWellTyped hfac hequiv hstore hfresh
  | step_exit =>
    cases hty with
    | stmt hfac hmap hstore hfresh hfloor hgr hstmt =>
      obtain rfl := mapStmtTys_eq_exit hmap
      cases hstmt with
      | exit =>
        rename_i hlabel _
        exact .exiting hfac hlabel (storeHasTyping_of_scopeExtends hfloor hstore)
  | step_typeDecl =>
    cases hty with
    | stmt hfac hmap hstore hfresh _ hgr hstmt =>
      obtain rfl := mapStmtTys_eq_typeDecl hmap
      cases hstmt with
      | typeDecl =>
        rename_i _ _ hequiv
        exact terminal_configWellTyped hfac hequiv hstore hfresh
  | step_stmts_nil =>
    cases hty with
    | stmts hfac hmap hstore hfresh _ hgr hss =>
      obtain rfl := mapStmtsTys_eq_nil hmap
      cases hss with
      | nil =>
        rename_i hequiv
        exact terminal_configWellTyped hfac hequiv hstore hfresh
  | step_stmts_cons =>
    cases hty with
    | stmts hfac hmap hstore hfresh hfloor hgr hss =>
      obtain ⟨s0, rest0, rfl, hs0, hrest0⟩ := mapStmtsTys_eq_cons hmap
      cases hss with
      | cons =>
        rename_i hhead hrest
        have hext : ScopeExtends _ _ :=
          fun x ty hx => StatementWellTyped.scopeExtends hhead x ty (hfloor x ty hx)
        exact .seq (.stmt hfac hs0 hstore hfresh hfloor hgr.1 hhead) hext hrest0 hgr.2 hrest
  | step_seq_inner _ ih =>
    cases hty with
    | seq hinner hfloor hmap hgr hrest => exact .seq (ih hinner) hfloor hmap hgr hrest
  | step_seq_done =>
    cases hty with
    | seq hinner hfloor hmap hgr hrest =>
      cases hinner with
      | terminal hfac hstore hfresh => exact .stmts hfac hmap hstore hfresh hfloor hgr hrest
  | step_seq_exit =>
    cases hty with
    | seq hinner _ _ _ _ =>
      cases hinner with
      | exiting hfac hlabel hstore => exact .exiting hfac hlabel hstore
  | step_block_body _ ih =>
    cases hty with
    | block hlabels hstore hfresh hfloor hext hinner hequiv =>
      exact .block hlabels hstore hfresh hfloor hext (ih hinner) hequiv
  | step_block_done =>
    cases hty with
    | block _ hstore hfresh _ hext hinner hequiv =>
      cases hinner with
      | terminal hfac hinnerStore _ =>
        have hproj := StoreHasTyping.projectStore hstore
          (storeHasTyping_of_scopeExtends hext hinnerStore)
        exact .terminal hfac (storeHasTyping_of_equiv hequiv hproj)
          (storeFresh_of_equiv hequiv (StoreFresh.projectStore hfresh))
  | step_block_exit_match _ =>
    cases hty with
    | block _ hstore hfresh _ _ hinner hequiv =>
      cases hinner with
      | exiting hfac _ hinnerStore =>
        exact .terminal hfac
          (storeHasTyping_of_equiv hequiv (StoreHasTyping.projectStore hstore hinnerStore))
          (storeFresh_of_equiv hequiv (StoreFresh.projectStore hfresh))
  | step_block_exit_mismatch hne =>
    cases hty with
    | block hlabels hstore _ hfloor _ hinner _ =>
      cases hinner with
      | exiting hfac hlabel hinnerStore =>
        exact .exiting hfac (mem_of_mem_blockLabels hne (hlabels _ hlabel))
          (storeHasTyping_of_scopeExtends hfloor
            (StoreHasTyping.projectStore hstore hinnerStore))

/-- Every run of Core's small-step semantics from a well-typed configuration ends in a
    well-typed configuration with the same substitution, enclosing labels, final context, final
    scopes and floor scopes. -/
theorem coreStepStar_preserves_configWellTyped {π : String → Option Procedure} {P : Program}
    {F : Expression.Factory} {S : Subst} {L : List String} {cfg cfg' : CoreConfig}
    {evs : Trace Expression} {C' : LContext CoreLParams} {ts' tsf : TypeScopes}
    (hstar : CoreStepStarE π cfg evs cfg') (hty : ConfigWellTyped P F S L cfg C' ts' tsf) :
    ConfigWellTyped P F S L cfg' C' ts' tsf := by
  revert hty
  induction hstar with
  | refl => exact fun hty => hty
  | step _ _ _ _ _ hstep _ ih =>
    exact fun hty => ih (coreStep_preserves_configWellTyped hstep hty)

/-- The configuration after the first step of a well-typed structured body is well typed. The
    step enters the body in a block labeled `""` that keeps the entry store as its parent store.
    The body is the image under the substitution `S` of a body typed in scopes `ts`, the entry
    store conforms to `ts` with `S` applied and binds no other variable, and the body's
    declarations are at ground types. -/
private theorem entry_configWellTyped {P : Program} {C C' : LContext CoreLParams} {S : Subst}
    {ts ts' : TypeScopes} {ss ss0 : List Statement} {ρ : Env Expression}
    (hss : StatementsWellTyped P C ts [] ss0 C' ts')
    (hmap : ss = mapStmtsTys (LMonoTy.subst S) ss0) (hground : Statements.Ground ss)
    (hρ : StoreHasTyping ρ.factory ρ.store (ts.instVarTyping S))
    (hfresh : StoreFresh ρ.store ts.find?) :
    ConfigWellTyped P ρ.factory S [] (.block (some "") ρ.store (.stmts ss ρ)) C ts ts :=
  .block (Lin := []) (fun _ hl => absurd hl List.not_mem_nil) hρ hfresh
    (fun _ _ h => h) (StatementsWellTyped.scopeExtends hss)
    (.stmts rfl hmap hρ hfresh (fun _ _ h => h) hground hss) (HMaps.Equiv.refl _)

/-- Every configuration reachable from the start of a structured body, other than the start
    itself, is well typed, when the body is the image under the substitution `S` of a
    well-typed body. The start runs the body in a block labeled `""`. The well-typed body is
    typed in scopes `ts`, the body starts in a store that conforms to `ts` with `S` applied and
    binds no other variable, and its declarations are at ground types. The procedure table is
    arbitrary. -/
theorem reachable_configs_wellTyped_of_typed {P : Program} {C C' : LContext CoreLParams}
    {ts ts' : TypeScopes} {ss0 ss : List Statement} {π : String → Option Procedure}
    {ρ : Env Expression} (S : Subst)
    (hss : StatementsWellTyped P C ts [] ss0 C' ts')
    (hmap : ss = mapStmtsTys (LMonoTy.subst S) ss0) (hground : Statements.Ground ss)
    (hρ : StoreHasTyping ρ.factory ρ.store (ts.instVarTyping S))
    (hfresh : StoreFresh ρ.store ts.find?) :
    ∀ evs cfg, CoreStepStarE π (.stmt (Stmt.block "" ss #[]) ρ) evs cfg →
      cfg = .stmt (Stmt.block "" ss #[]) ρ ∨ ConfigWellTyped P ρ.factory S [] cfg C ts ts := by
  have hblock := entry_configWellTyped hss hmap hground hρ hfresh
  intro evs cfg hstar
  cases hstar with
  | refl => exact .inl rfl
  | step _ _ _ _ _ hstep hrest =>
    refine .inr ?_
    cases hstep with
    | step_block => exact coreStepStar_preserves_configWellTyped hrest hblock

/-- Every configuration reachable from the start of a well-typed structured body, other than
    the start itself, is well typed with the empty substitution. The start runs the body in a
    block labeled `""`. The body is typed in scopes `ts`, it starts in a store that conforms to
    `ts` and binds no other variable, and its declarations are at ground types. The procedure
    table is arbitrary. -/
theorem reachable_configs_wellTyped_of_typed_empty {P : Program} {C C' : LContext CoreLParams}
    {ts ts' : TypeScopes} {ss : List Statement} {π : String → Option Procedure}
    {ρ : Env Expression}
    (hss : StatementsWellTyped P C ts [] ss C' ts') (hground : Statements.Ground ss)
    (hρ : StoreHasTyping ρ.factory ρ.store ts.find?)
    (hfresh : StoreFresh ρ.store ts.find?) :
    ∀ evs cfg, CoreStepStarE π (.stmt (Stmt.block "" ss #[]) ρ) evs cfg →
      cfg = .stmt (Stmt.block "" ss #[]) ρ ∨
        ConfigWellTyped P ρ.factory Subst.empty [] cfg C ts ts := by
  have hρ' : StoreHasTyping ρ.factory ρ.store (ts.instVarTyping Subst.empty) := by
    rw [TypeScopes.instVarTyping_empty]
    exact hρ
  exact reachable_configs_wellTyped_of_typed Subst.empty hss
    (Statements.mapStmtsTys_subst_empty ss).symm hground hρ' hfresh

/-- Every configuration reachable from the start of a well-typed structured procedure body,
    other than the start itself, is well typed with the empty substitution. The start runs the
    body in a block labeled `""` from a store that conforms to the variable scopes the body is
    typed in and binds no other variable: the scopes hold the inputs, the outputs and the `old`
    values of the in-outs. The body's declarations are at ground types. The procedure table is
    arbitrary. -/
theorem reachable_configs_wellTyped {C0 : LContext CoreLParams} {ts0 : TypeScopes}
    {P : Program} {proc : Procedure} {md : MetaData Expression} {ss : List Statement}
    {π : String → Option Procedure} {ρ : Env Expression}
    (hP : ProgramWellTyped C0 ts0 P) (hmem : Decl.proc proc md ∈ P.decls)
    {opq : Bool} (hbody : proc.body = .structured ss opq) (hground : Statements.Ground ss)
    (hρ : StoreHasTyping ρ.factory ρ.store (procBodyScopes ts0 proc).find?)
    (hfresh : StoreFresh ρ.store (procBodyScopes ts0 proc).find?) :
    ∃ C, ∀ evs cfg,
      CoreStepStarE π (.stmt (Stmt.block "" ss #[]) ρ) evs cfg →
      cfg = .stmt (Stmt.block "" ss #[]) ρ ∨
        ConfigWellTyped P ρ.factory Subst.empty [] cfg C (procBodyScopes ts0 proc)
          (procBodyScopes ts0 proc) := by
  obtain ⟨C, hproc⟩ := hP.procWellTyped hmem
  have hbt := hproc.bodyTyped
  rw [hbody] at hbt
  cases hbt with
  | structured _ C' ts' _ hss =>
    exact ⟨C, reachable_configs_wellTyped_of_typed_empty hss hground hρ hfresh⟩

end -- public section

end TypeSpec
end Core
