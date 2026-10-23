/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.DeadDefElim
public import Strata.DL.Imperative.BigStep.Sem
public import Strata.DL.Imperative.StmtProps
public import Strata.Languages.Core.Logic.LangDef
import all Strata.DL.Imperative.Cmd
import all Strata.DL.Imperative.Stmt
import all Strata.DL.Lambda.LExprWFProps

/-! # Properties of dead-definition elimination

`deadDefElimH`, one backward pass with one hash set, returns `deadDefElim`'s list
(`deadDefElimH_eq`): the hash set holds exactly the identifiers that `deadDefElim`
recomputes.

For Core statement lists, the facts the trace over-approximation (`DeadDefElimCoreCorrect`) is
built from: the correspondence of final environments (`DDOut`); a Core run of a call-free
configuration is a run over `EvalE` and back (`star_evalE`, `star_core`); and erasure keeps the
initial-environment gate `BlockInitEnvWF` of a list without loops and calls
(`blockInitEnvWF_dd`), through its defined variables (`dd_definedVars`), its `init` types
(`dd_initTypes`) and def-use well-formedness (`dd_defUse`).

Key theorems: `deadDefElimH_eq`, `star_evalE`, `star_core`, `blockInitEnvWF_dd`.

Key definitions: `Core.DeadDefElim.DDOut`, `Core.DeadDefElim.CallFree`. -/

namespace Imperative
namespace DeadDefElim

open BigStep

public section

variable {P : PureExpr} [BEq P.Ident] [LawfulBEq P.Ident] [HasFvars P] [Hashable P.Ident]

/-- `insertFV h e` holds the identifiers of `h` and the free variables of `e`. -/
private theorem mem_insertFV {h : Std.HashSet P.Ident} {e : P.Expr} {y : P.Ident} :
    y ∈ insertFV h e ↔ y ∈ h ∨ y ∈ HasFvars.getFvars e := by
  simp only [insertFV]
  induction HasFvars.getFvars e generalizing h <;>
    simp_all [or_assoc, or_left_comm, eq_comm (a := y)]

/-- `insertGuard h g` holds the identifiers of `h` and the free variables of the guard `g`. -/
private theorem mem_insertGuard {h : Std.HashSet P.Ident} {g : ExprOrNondet P} {y : P.Ident} :
    y ∈ insertGuard h g ↔ y ∈ h ∨ y ∈ g.getVars := by
  cases g <;> simp [insertGuard, ExprOrNondet.getVars, mem_insertFV]

/-- Inserting the identifiers of a list of call arguments adds exactly their identifiers. -/
private theorem mem_foldl_insertCallArg {y : P.Ident} :
    ∀ {h : Std.HashSet P.Ident} {args : List (CallArg P)},
      y ∈ args.foldl insertCallArg h ↔
        y ∈ h ∨ y ∈ (CallArg.getInArgs args).flatMap HasFvars.getFvars ++ CallArg.getLhs args
  | _, [] => by simp [CallArg.getInArgs, CallArg.getLhs]
  | _, a :: args => by
    rw [List.foldl_cons, mem_foldl_insertCallArg]
    cases a <;> simp [CallArg.getInArgs, CallArg.getLhs, insertCallArg, mem_insertFV, or_assoc,
      or_left_comm, eq_comm (a := y)]

/-- Inserting the free variables of a list of invariants adds exactly their free variables. -/
private theorem mem_foldl_insertInv {y : P.Ident} :
    ∀ {h : Std.HashSet P.Ident} {inv : List (String × P.Expr)},
      y ∈ inv.foldl (fun h p => insertFV h p.2) h ↔ y ∈ h ∨ y ∈ inv.flatMap (HasFvars.getFvars ·.2)
  | _, [] => by simp
  | _, p :: inv => by
    rw [List.foldl_cons, mem_foldl_insertInv]
    simp [mem_insertFV, or_assoc]

/-- `insertCmd h c` holds the identifiers of `h` and those of the command `c`. -/
private theorem mem_insertCmd {h : Std.HashSet P.Ident} {c : CmdExt P} {y : P.Ident} :
    y ∈ insertCmd h c ↔ y ∈ h ∨ y ∈ Stmt.idents (.cmd c : PStmt P) := by
  rcases c with (⟨_, _, _ | _, _⟩ | ⟨_, _ | _, _⟩ | _ | _ | _) | _ <;>
    simp [insertCmd, Stmt.idents, mem_insertFV, mem_foldl_insertCallArg, or_assoc, or_left_comm,
      or_comm, eq_comm (a := y)]

omit [LawfulBEq P.Ident] in
mutual
/-- `insertIdents h ss` holds the identifiers of `h` and those of `ss`. -/
private theorem mem_insertIdents [LawfulBEq P.Ident] {h : Std.HashSet P.Ident} {y : P.Ident} :
    ∀ ss : PStmts P, y ∈ insertIdents h ss ↔ y ∈ h ∨ y ∈ Block.idents ss
  | [] => by simp [insertIdents, Block.idents]
  | s :: rest => by
    simp [insertIdents, Block.idents, mem_insertIdents rest, mem_insertIdent s, or_assoc]
/-- `insertIdent h s` holds the identifiers of `h` and those of `s`. -/
private theorem mem_insertIdent [LawfulBEq P.Ident] {h : Std.HashSet P.Ident} {y : P.Ident} :
    ∀ s : PStmt P, y ∈ insertIdent h s ↔ y ∈ h ∨ y ∈ Stmt.idents s
  | .cmd c => by simp [insertIdent, mem_insertCmd]
  | .block _ ss _ => by simp [insertIdent, Stmt.idents, mem_insertIdents ss]
  | .ite c tss ess _ => by
    simp [insertIdent, Stmt.idents, mem_insertIdents tss, mem_insertIdents ess, mem_insertGuard,
      or_assoc]
  | .loop g m inv body _ => by
    cases m <;> simp [insertIdent, Stmt.idents, mem_insertIdents body, mem_foldl_insertInv,
      mem_insertFV, mem_insertGuard, or_assoc]
  | .exit _ _ | .typeDecl _ _ => by simp [insertIdent, Stmt.idents]
end

/-- From a hash set holding exactly `live`, `deadDefElimHL` returns `deadDefElim live ss` and a
    hash set holding exactly its identifiers and `live`. -/
private theorem deadDefElimHL_spec (h : Std.HashSet P.Ident) (ss : PStmts P) (live : List P.Ident)
    (hl : ∀ y, y ∈ h ↔ y ∈ live) :
    (deadDefElimHL h ss).1 = deadDefElim live ss ∧
      ∀ y, y ∈ (deadDefElimHL h ss).2 ↔ y ∈ Block.idents (deadDefElim live ss) ++ live := by
  fun_induction deadDefElimHL h ss generalizing live
  case case1 => simp [deadDefElim, Block.idents, hl]
  case case2 rest _ h1 hr x ty e md hx ih =>
    obtain ⟨rfl, ih2⟩ := hr ▸ ih live hl
    have hx' := (ih2 x).1 (by simpa using hx)
    simp [deadDefElim, erasable, hx', deadDefElimS, Block.idents, mem_insertCmd, ih2, or_comm]
  case case3 rest _ h1 hr x ty e md hx ih =>
    obtain ⟨rfl, ih2⟩ := hr ▸ ih live hl
    have hx' : x ∉ Block.idents (deadDefElim live rest) ++ live :=
      fun hm => hx (by simpa using (ih2 x).2 hm)
    simp_all [deadDefElim, erasable]
  case case4 rest _ h1 hr c hc ih =>
    obtain ⟨rfl, ih2⟩ := hr ▸ ih live hl
    have he : erasable (Block.idents (deadDefElim live rest) ++ live) (.cmd c) = false := by
      rcases c with (_ | _ | _ | _ | _) | _ <;> first | rfl | exact (hc _ _ _ _ rfl).elim
    simp [deadDefElim, he, deadDefElimS, Block.idents, mem_insertCmd, ih2, or_comm]
  case case5 rest _ h1 hr c tss ess md _ h2 he _ h3 ht ih ihe iht =>
    obtain ⟨rfl, ih2⟩ := hr ▸ ih live hl
    obtain ⟨rfl, ihe2⟩ := he ▸ ihe _ ih2
    obtain ⟨rfl, iht2⟩ := ht ▸ iht _ ihe2
    simp [deadDefElim, erasable, deadDefElimS, Block.idents, Stmt.idents, mem_insertGuard, iht2,
      or_comm]
  case case6 rest _ h1 hr l ss md _ h2 hb ih ihb =>
    obtain ⟨rfl, ih2⟩ := hr ▸ ih live hl
    obtain ⟨rfl, ihb2⟩ := hb ▸ ihb _ ih2
    simp [deadDefElim, erasable, deadDefElimS, Block.idents, Stmt.idents, ihb2]
  case case7 rest _ h1 hr g m inv body md ih =>
    obtain ⟨rfl, ih2⟩ := hr ▸ ih live hl
    simp [deadDefElim, erasable, deadDefElimS, Block.idents, mem_insertIdent, ih2, or_comm]
  all_goals
    rename_i rest _ h1 hr _ _ ih
    obtain ⟨rfl, ih2⟩ := hr ▸ ih live hl
    simp [deadDefElim, erasable, deadDefElimS, Block.idents, Stmt.idents, ih2]

/-- The one-pass hash-set version `deadDefElimH` returns the list `deadDefElim` specifies. -/
theorem deadDefElimH_eq (live : List P.Ident) (ss : PStmts P) :
    deadDefElimH live ss = deadDefElim live ss :=
  (deadDefElimHL_spec _ ss live fun y => by simp).1

end -- public section

end DeadDefElim
end Imperative

namespace Core
namespace DeadDefElim

open Imperative Imperative.BigStep Imperative.DeadDefElim Core.Logic

public section

/-! ## Final environments of the output -/

/-- The environment `ρ'` at the end of a run of the output of `deadDefElim` corresponds to the
    environment `ρ` at the end of the source run: same factory and failure flag, and the store
    of `ρ'` is the store of `ρ` with some bindings removed. -/
@[expose] def DDOut (ρ ρ' : Env Expression) : Prop :=
  ρ'.factory = ρ.factory ∧ ρ'.hasFailure = ρ.hasFailure ∧
    StoreAgreement ρ'.store ρ.store

/-! ## Call-free Core runs are runs over `EvalE` -/

/-- Every statement still to run in the configuration makes no procedure call. -/
@[expose] def CallFree : Config Expression Command → Prop
  | .stmt s _ => Statements.noCalls [s] = true
  | .stmts ss _ => Statements.noCalls ss = true
  | .terminal _ | .exiting _ _ => True
  | .block _ _ c => CallFree c
  | .seq c ss => CallFree c ∧ Statements.noCalls ss = true

/-- A Core step of a call-free configuration is a step over `EvalE` to a call-free
    configuration. -/
private theorem step_evalE {π : String → Option Procedure} {c c' : Config Expression Command}
    {e : List (Event Expression)} (hs : StepStmtE Expression (EvalCommandE π) c e c')
    (hI : CallFree c) : StepStmtE Expression EvalE c e c' ∧ CallFree c' := by
  induction hs with
  | step_cmd h =>
    rename_i cmd _ _ _
    cases h with
    | cmd_sem h => exact ⟨.step_cmd h, trivial⟩
    | call_sem => simp [CallFree, Statements.noCalls, Block.allSubstmts, Stmt.allSubstmts,
        Statement.isNotCall] at hI
  | step_admin h =>
    refine ⟨.step_admin h, ?_⟩
    induction h with
    | step_seq_inner _ ih => exact ⟨ih hI.1, hI.2⟩
    | step_block_body _ ih => exact ih hI
    | _ => simp_all [CallFree, Statements.noCalls, Block.allSubstmts, Stmt.allSubstmts]
  | step_seq_inner _ ih =>
    obtain ⟨h1, h2⟩ := ih hI.1
    exact ⟨.step_seq_inner h1, h2, hI.2⟩
  | step_block_body _ ih =>
    obtain ⟨h1, h2⟩ := ih hI
    exact ⟨.step_block_body h1, h2⟩

/-- A Core run of a call-free configuration is a run over `EvalE`. -/
theorem star_evalE {π : String → Option Procedure} {c c' : Config Expression Command}
    {tr : List (Event Expression)} (hs : (EventLang.coreBlock π).traceStar c tr c')
    (hI : CallFree c) : StepStmtStarE Expression EvalE c tr c' := by
  induction hs with
  | refl => exact .refl _
  | step _ _ _ _ _ h1 _ ih =>
    obtain ⟨h1', hI'⟩ := step_evalE h1 hI
    exact .step _ _ _ _ _ h1' (ih hI')

/-- A run over `EvalE` is a Core run. -/
theorem star_core (π : String → Option Procedure) {c c' : Config Expression Command}
    {tr : List (Event Expression)} (hs : StepStmtStarE Expression EvalE c tr c') :
    (EventLang.coreBlock π).traceStar c tr c' := by
  refine ReflTransTrace.imp (fun _ _ _ h => ?_) hs
  induction h with
  | step_cmd h =>
    rename_i cmd _ _ _
    cases cmd with
    | cmd => exact .step_cmd (EvalCmdExtE.cmd_sem h)
    | call => exact h.elim
  | step_admin h => exact .step_admin h
  | step_seq_inner _ ih => exact .step_seq_inner ih
  | step_block_body _ ih => exact .step_block_body ih

/-! ## Initial-environment well-formedness of the output -/

/-- Erasure keeps the defined variables among those of the input. -/
private theorem dd_definedVars (b : Bool) : ∀ (live : List Expression.Ident) (ss : Statements),
    ∀ n ∈ Block.definedVars (deadDefElim live ss) b, n ∈ Block.definedVars ss b
  | _, [] => by simp [deadDefElim]
  | live, .ite c t e md :: rest => by
    have iht := fun l => dd_definedVars b l t
    have ihe := fun l => dd_definedVars b l e
    have ih := dd_definedVars b live rest
    cases b <;> simp_all [deadDefElim, erasable, deadDefElimS] <;> grind
  | live, .block l bs md :: rest => by
    have ihb := fun l => dd_definedVars b l bs
    have ih := dd_definedVars b live rest
    cases b <;> simp_all [deadDefElim, erasable, deadDefElimS] <;> grind
  | live, .cmd c :: rest => by
    have ih := dd_definedVars b live rest
    simp only [deadDefElim]
    split <;> simp_all [deadDefElimS] <;> grind
  | live, .loop .. :: rest | live, .exit .. :: rest | live, .typeDecl .. :: rest => by
    have ih := dd_definedVars b live rest
    simp_all [deadDefElim, erasable, deadDefElimS] <;> grind

/-- Erasure keeps the declared types of `init`s among those of the input. -/
private theorem dd_initTypes : ∀ (live : List Expression.Ident) (ss : Statements),
    ∀ ty ∈ Block.initTypes (deadDefElim live ss), ty ∈ Block.initTypes ss
  | _, [] => by simp [deadDefElim, Block.initTypes]
  | live, .ite c t e md :: rest => by
    have iht := fun l => dd_initTypes l t
    have ihe := fun l => dd_initTypes l e
    have ih := dd_initTypes live rest
    simp_all [deadDefElim, erasable, deadDefElimS, Block.initTypes, Stmt.initTypes] <;> grind
  | live, .block l bs md :: rest => by
    have ihb := fun l => dd_initTypes l bs
    have ih := dd_initTypes live rest
    simp_all [deadDefElim, erasable, deadDefElimS, Block.initTypes, Stmt.initTypes] <;> grind
  | live, .cmd c :: rest => by
    have ih := dd_initTypes live rest
    simp only [deadDefElim]
    split <;> simp_all [deadDefElimS, Block.initTypes, Stmt.initTypes] <;> grind
  | live, .loop .. :: rest | live, .exit .. :: rest | live, .typeDecl .. :: rest => by
    have ih := dd_initTypes live rest
    simp_all [deadDefElim, erasable, deadDefElimS, Block.initTypes, Stmt.initTypes] <;> grind

/-- Erasure keeps def-use well-formedness of a list without loops and calls, also from fewer
    defined names: the output is well formed from any `D'` of names of `D` containing every
    name of `D` the output mentions, when the input is well formed from `D`. -/
private theorem dd_defUse (fs : Expression.Ident → Bool) : ∀ (live : List Expression.Ident)
    (ss : Statements) (D D' : Expression.Ident → Bool), Block.noLoops ss = true →
    Statements.noCalls ss = true → Block.defUseWellFormed D fs ss = true →
    (∀ n, D' n = true → D n = true) →
    (∀ n, D n = true → n ∈ Block.idents (deadDefElim live ss) → D' n = true) →
    Block.defUseWellFormed D' fs (deadDefElim live ss) = true
  | _, [], _, _, _, _, _, _, _ => by simp [deadDefElim, Block.defUseWellFormed]
  | live, .ite c t e md :: rest, D, D', hss, hnc, h, h1, h2 => by
    simp only [Block.noLoops_cons, Stmt.noLoops_ite, Bool.and_eq_true] at hss
    simp only [Statements.noCalls, Block.allSubstmts, Stmt.allSubstmts, Statement.isNotCall,
      Bool.true_and, Bool.and_eq_true] at hnc
    simp only [deadDefElim, erasable, Bool.false_eq_true, ↓reduceIte, deadDefElimS] at h2 ⊢
    simp only [Block.defUseWellFormed, Stmt.defUseWellFormed, Bool.and_eq_true,
      Stmt.definedVars, ↓reduceIte, List.not_mem_nil, decide_false, Bool.or_false] at h ⊢
    obtain ⟨⟨⟨⟨hc, ho⟩, ht⟩, he⟩, hr⟩ := h
    have hcv : ∀ n ∈ ExprOrNondet.getVars c, ∀ t e md,
        n ∈ Stmt.idents (P := Expression) (.ite c t e md) :=
      fun n hn _ _ _ => by simp [Stmt.idents, hn]
    have hm : ∀ n, D n = true → n ∈ Stmt.idents (Stmt.ite c (deadDefElim (Block.idents
        (deadDefElim (Block.idents (deadDefElim live rest) ++ live) e) ++
          (Block.idents (deadDefElim live rest) ++ live)) t)
        (deadDefElim (Block.idents (deadDefElim live rest) ++ live) e) md) → D' n = true :=
      fun n hn hm => h2 n hn (by simp only [Block.idents, List.mem_append]; exact .inl hm)
    refine ⟨⟨⟨⟨?_, ho⟩, dd_defUse fs _ t D D' hss.1.1 hnc.1.1 ht h1 fun n hn hk => hm n hn
      (by simp [Stmt.idents, hk])⟩, dd_defUse fs _ e D D' hss.1.2 hnc.1.2 he h1 fun n hn hk =>
      hm n hn (by simp [Stmt.idents, hk])⟩, dd_defUse fs live rest D D' hss.2 hnc.2 hr h1
      fun n hn hk => h2 n hn (by simp [Block.idents, hk])⟩
    simp only [List.all_eq_true] at hc ⊢
    exact fun n hn => hm n (hc n hn) (hcv n hn _ _ _)
  | live, .block l bs md :: rest, D, D', hss, hnc, h, h1, h2 => by
    simp only [Block.noLoops_cons, Stmt.noLoops_block, Bool.and_eq_true] at hss
    simp only [Statements.noCalls, Block.allSubstmts, Stmt.allSubstmts, Statement.isNotCall,
      Bool.true_and, Bool.and_eq_true] at hnc
    simp only [deadDefElim, erasable, Bool.false_eq_true, ↓reduceIte, deadDefElimS] at h2 ⊢
    simp only [Block.defUseWellFormed, Stmt.defUseWellFormed, Bool.and_eq_true,
      Stmt.definedVars, ↓reduceIte, List.not_mem_nil, decide_false, Bool.or_false] at h ⊢
    exact ⟨dd_defUse fs _ bs D D' hss.1 hnc.1 h.1 h1 fun n hn hk => h2 n hn
      (by simp [Block.idents, Stmt.idents, hk]), dd_defUse fs live rest D D' hss.2 hnc.2 h.2 h1
      fun n hn hk => h2 n hn (by simp [Block.idents, hk])⟩
  | _, .cmd (.call ..) :: _, _, _, _, hnc, _, _, _ => by
    simp [Statements.noCalls, Block.allSubstmts, Stmt.allSubstmts, Statement.isNotCall] at hnc
  | live, .cmd (.cmd c) :: rest, D, D', hss, hnc, h, h1, h2 => by
    simp only [Block.noLoops_cons, Stmt.noLoops_cmd, Bool.true_and] at hss
    simp only [Statements.noCalls, Block.allSubstmts, Stmt.allSubstmts, Statement.isNotCall,
      Bool.true_and] at hnc
    simp only [Block.defUseWellFormed, Bool.and_eq_true, Stmt.definedVars,
      HasVarsImp.definedVars, Command.definedVars] at h
    obtain ⟨hc, hr⟩ := h
    have hcI : ∀ n, n ∈ Cmd.getVars c ∨ n ∈ Cmd.modifiedVars c ∨ n ∈ Cmd.definedVars c →
        n ∈ Stmt.idents (P := Expression) (.cmd (.cmd c)) := by
      rcases c with ⟨x, _, _ | _, _⟩ | ⟨x, _ | _, _⟩ | _ | _ | _ <;>
        simp [Cmd.getVars, Cmd.modifiedVars, Cmd.definedVars, ExprOrNondet.getVars,
          Stmt.idents] <;> grind
    simp only [deadDefElim, deadDefElimS] at h2 ⊢
    split
    · next he =>
      rw [if_pos he] at h2
      refine dd_defUse fs live rest _ D' hss hnc hr (fun n hn => by simp [h1 n hn])
        fun n hn hk => ?_
      rcases Bool.or_eq_true_iff.1 hn with hd | hd
      · exact h2 n hd hk
      · rcases c with ⟨x, _, _, _⟩ | _ | _ | _ | _ <;>
          simp_all [erasable, Cmd.definedVars]
    · next he =>
      rw [if_neg he] at h2
      simp only [Block.defUseWellFormed, Bool.and_eq_true, Stmt.definedVars,
        HasVarsImp.definedVars, Command.definedVars]
      refine ⟨?_, dd_defUse fs live rest _ _ hss hnc hr (fun n hn => by
        rcases Bool.or_eq_true_iff.1 hn with hd | hd <;> simp [h1 n, hd]) fun n hn hk => ?_⟩
      · simp only [Stmt.defUseWellFormed, HasVarsImp.readVars, HasVarsImp.modifiedVars,
          HasVarsImp.definedVars, Command.getVars, Command.modifiedVars, Command.definedVars,
          Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc ⊢
        obtain ⟨⟨⟨hrd, hmd⟩, hdf⟩, hop⟩ := hc
        refine ⟨⟨⟨fun n hn => ?_, fun n hn => ?_⟩, fun n hn hd => hdf n hn (h1 n hd)⟩, hop⟩
        · exact h2 n (hrd n hn) (by simp [Block.idents, hcI n (.inl hn)])
        · exact h2 n (hmd n hn) (by simp [Block.idents, hcI n (.inr (.inl hn))])
      · rcases Bool.or_eq_true_iff.1 hn with hd | hd
        · simp [h2 n hd (by simp [Block.idents, hk])]
        · simp [hd]
  | _, .loop .. :: _, _, _, hss, _, _, _, _ => by
    simp [Block.noLoops_cons, Stmt.noLoops_loop] at hss
  | live, .exit .. :: rest, D, D', hss, hnc, h, h1, h2
  | live, .typeDecl .. :: rest, D, D', hss, hnc, h, h1, h2 => by
    simp only [Block.noLoops_cons, Stmt.noLoops_exit, Stmt.noLoops_typeDecl, Bool.true_and] at hss
    simp only [deadDefElim, erasable, Bool.false_eq_true, ↓reduceIte, deadDefElimS,
      Block.defUseWellFormed, Stmt.defUseWellFormed, Bool.true_and, Stmt.definedVars,
      List.not_mem_nil, decide_false, Bool.or_false, Block.idents, Stmt.idents,
      List.nil_append] at h h2 ⊢
    simp only [Statements.noCalls, Block.allSubstmts, Stmt.allSubstmts, Statement.isNotCall,
      Bool.true_and] at hnc
    exact dd_defUse fs live rest D D' hss hnc h h1 h2

/-- The output of `deadDefElim` is well formed from every environment the input is: the
    gate `BlockInitEnvWF` of the input gives that of the output. -/
theorem blockInitEnvWF_dd {params : InitEnvWFParams} {ss : Statements}
    {ρ : Env Expression} (hss : Block.noLoops ss = true) (hnc : Statements.noCalls ss = true)
    (h : BlockInitEnvWF params ss ρ) : BlockInitEnvWF params (deadDefElim [] ss) ρ := by
  have hdu := dd_defUse params.declaredFuncs [] ss _ _ hss hnc h.defUseOk (fun _ h => h)
    fun _ h _ => h
  have hdv := dd_definedVars false [] ss
  refine { h with
    readWritesDefined := fun _ hn hnd =>
      Block.defined_of_mem_touchedVars (fun _ _ h => h) hdu hn hnd
    defsUndefined := fun n hn => h.defsUndefined n (hdv n hn)
    definedVarsNotReserved := fun n hn => h.definedVarsNotReserved n (hdv n hn)
    defUseOk := hdu
    initTypesInhabited := fun ty hty => h.initTypesInhabited ty (dd_initTypes [] ss ty hty) }

end -- public section

end DeadDefElim
end Core
