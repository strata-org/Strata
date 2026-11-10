/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.Simulation
public import Strata.Transform.Passive.ProgramProps
public import Strata.Transform.Passive.SimulationProps
public import Strata.DL.Imperative.BigStep.SemProps
import Strata.Util.ExceptProps

/-! # Shadow runs: the obligation program's runs off the loop-free path

The over-approximation proof of the WP phase (`wpEntry_over`) follows a loop-free run with a
run of the obligation program.  The obligation program runs code the loop-free path does not:
a branch of an `ite` that the continuation depends on is *laid out* on the continuation's path,
so its statements run whether or not the branch is taken.  Off the path they evaluate no input
expression (each is a branch of an `ite` on a false reachability), but each `init` of the branch
still binds a value of its declared type.  The hypothesis of `wpEntry_over` makes these off-path
runs explicit:

* `ShL`/`ShS` (*shadow runs*): a statement list run that evaluates nothing, follows both
  branches of every `ite`, binds some value of the declared type at each `init` and keeps
  the value at each `set`; a continuation `K` constrains every end the run reaches;
* `DRun`/`DReach`: the big-step loop-free run/reach (`BRun`/`BReach`) annotated, at each
  `ite` and after each `exit`, with the shadow runs of what the obligation program runs off
  the path there (`VirtK`: the requirement on the untaken ends).

A loop-free run with no laid-out untaken branch (e.g. every branch not taken consists of
`assert`/`cover` only) needs no shadow run at all.  Every reach of a well-scoped loop-free list
is annotated when every type its `init`s declare has a value (`shadowOK_of_initTysOK`).

The obligation program's `init`s bind values of their declared types, so `wpEntry_over` also
assumes that the loop-free values the list reads have their declared types (`TyOK`); the
Boolean constants have the Boolean type (`bool_valueOfTy`).

Key definitions: `ShL`, `ShS`, `DRun`, `DReach`, `FailsD`, `TyOK`.

Key theorems: `shadowOK_of_initTysOK`, `DRun.imp`, `DRun.cons_inv`, `claimK_split`,
`bool_valueOfTy`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iB : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iBo : HasBool P] [iFv : HasFvar P] [iSu : HasSubstFvar P] [iId : HasIdent P]
  [iLI : LawfulHasIdent P] [iHa : Hashable P.Ident] [iFs : HasFvars P] [iW : WPLang P]
  [iOp : HasOps P] [iLF : LawfulHasFvar P] [iLFs : LawfulHasFvars P] [iLV : LawfulHasVal P]
omit iB iLB iSu iId iLI iHa iFs iW iOp iLF iLFs iLV

/-! ## Shadow runs: the obligation program's runs off the loop-free path -/

mutual
/-- A shadow run of a statement list from `σ`: every end it reaches satisfies `K`. -/
@[expose] def ShL (F : P.Factory) : (PStmts P) → SemanticStore P →
    ((Outcome P) → Prop) → Prop
  | [], σ, K => K (.normal σ)
  | s :: rest, σ, K => ShS F s σ (fun o => match o with
      | .normal σ1 => ShL F rest σ1 K
      | .exit l σ1 => K (.exit l σ1))
/-- A shadow run of one statement from `σ`.  It evaluates no expression: an `init` binds
    some value of the declared type (the obligation program's default for it), a `set` keeps
    the variable's value, and both branches of an `ite` are followed. -/
@[expose] def ShS (F : P.Factory) : (PStmt P) → SemanticStore P →
    ((Outcome P) → Prop) → Prop
  | .cmd (.cmd (.init x ty _ _)), σ, K =>
    ∃ v, HasVal.valueOfTy F v ty ∧ K (.normal (SemanticStore.update σ x v))
  | .cmd (.cmd (.set _ _ _)), σ, K => K (.normal σ)
  | .cmd (.cmd (.assume _ _ _)), σ, K => K (.normal σ)
  | .cmd (.cmd (.assert _ _ _)), σ, K => K (.normal σ)
  | .cmd (.cmd (.cover _ _ _)), σ, K => K (.normal σ)
  | .ite (.det _) tss ess _, σ, K =>
    (if isLocal tss then K ((Outcome.normal σ).proj σ) else ShL F tss σ (fun o => K (o.proj σ))) ∧
    (if isLocal ess then K ((Outcome.normal σ).proj σ) else ShL F ess σ (fun o => K (o.proj σ)))
  | .block l ss _, σ, K => ShL F ss σ (fun o => K (o.block l σ))
  | .exit l _, σ, K => K (.exit l σ)
  | .typeDecl _ _, σ, K => K (.normal σ)
  | .cmd (.call _ _ _), _, _ => False
  | .ite .nondet _ _ _, _, _ => False
  | .loop _ _ _ _ _, _, _ => False
end

/-- A shadow run of a branch: nothing for a local branch (its end is its entry). -/
@[expose] def ShB (F : P.Factory) (B : (PStmts P)) (σ : SemanticStore P)
    (K : (Outcome P) → Prop) : Prop := if isLocal B then K (.normal σ) else ShL F B σ K

/-- The requirement on an untaken end `o'` when the real run of the construct ended with
    `real`: none when both are normal ends (the real normal end is the one selected
    afterwards), `X` otherwise. -/
@[expose] def VirtK (real : (Outcome P)) (X : (Outcome P) → Prop) : (Outcome P) → Prop := fun o' =>
  match real, o' with
  | .normal _, .normal _ => True
  | _, _ => X o'

/-! ## Loop-free runs annotated with the off-path shadow runs -/

mutual
/-- A big-step run of a loop-free statement list (as `BRun`), whose untaken ends (the
    obligation program's other ends of the fragment: its normal end when the run exits,
    and every exit not taken) satisfy `X`. -/
inductive DRun (F : P.Factory) : ((Outcome P) → Prop) → (PStmts P) →
    SemanticStore P → List (Event P) → (Outcome P) → Prop where
  | nil : DRun F X [] σ [] (.normal σ)
  | cons_normal : DRunS F (VirtK (.normal σ1) X) s σ evs1 (.normal σ1) → DRun F X rest σ1 evs2 o →
      DRun F X (s :: rest) σ (evs1 ++ evs2) o
  | cons_exit : DRunS F (fun o => match o with
        | .normal σv => ShL F rest σv X
        | .exit l' σx => X (.exit l' σx)) s σ evs (.exit l σ1) →
      DRun F X (s :: rest) σ evs (.exit l σ1)

/-- A big-step run of one loop-free statement (as `BRunS`), annotated. -/
inductive DRunS (F : P.Factory) : ((Outcome P) → Prop) → (PStmt P) →
    SemanticStore P → List (Event P) → (Outcome P) → Prop where
  | cmd : EvalE F σ c σ' evs → DRunS F X (.cmd c) σ evs (.normal σ')
  | ite_true : P.eval F σ c = some (HasBool.ttVal F) →
      DRun F (fun o' => X (o'.proj σ)) tss σ evs o →
      ShB F ess σ (VirtK o (fun o' => X (o'.proj σ))) →
      DRunS F X (.ite (.det c) tss ess md) σ evs (o.proj σ)
  | ite_false : P.eval F σ c = some (HasBool.ffVal F) →
      DRun F (fun o' => X (o'.proj σ)) ess σ evs o →
      ShB F tss σ (VirtK o (fun o' => X (o'.proj σ))) →
      DRunS F X (.ite (.det c) tss ess md) σ evs (o.proj σ)
  | block : DRun F (fun o' => X (o'.block l σ)) ss σ evs o →
      DRunS F X (.block l ss md) σ evs (o.block l σ)
  | exit : DRunS F X (.exit l md) σ [] (.exit l σ)
  | typeDecl : DRunS F X (.typeDecl tc md) σ [] (.normal σ)
end

mutual
/-- A big-step reach of a loop-free statement list (as `BReach`), annotated. -/
inductive DReach (F : P.Factory) : (PStmts P) → SemanticStore P →
    List (Event P) → Prop where
  | here : DReachS F s σ evs → DReach F (s :: rest) σ evs
  | later : DRunS F (fun _ => True) s σ evs1 (.normal σ1) → DReach F rest σ1 evs2 →
      DReach F (s :: rest) σ (evs1 ++ evs2)

/-- A big-step reach of one loop-free statement (as `BReachS`), annotated. -/
inductive DReachS (F : P.Factory) : (PStmt P) → SemanticStore P →
    List (Event P) → Prop where
  | cmd : EvalE F σ c σ' evs → DReachS F (.cmd c) σ evs
  | ite_true : P.eval F σ c = some (HasBool.ttVal F) → DReach F tss σ evs →
      DReachS F (.ite (.det c) tss ess md) σ evs
  | ite_false : P.eval F σ c = some (HasBool.ffVal F) → DReach F ess σ evs →
      ShB F tss σ (fun _ => True) → DReachS F (.ite (.det c) tss ess md) σ evs
  | block : DReach F ss σ evs → DReachS F (.block l ss md) σ evs
end

/-- A loop-free statement list fails the target `t` from `σ` along an annotated reach, at an
    occurrence whose condition is `e`. -/
@[expose] def FailsD (F : P.Factory) (ss : (PStmts P)) (σ : SemanticStore P)
    (t : AssertId P) (e : P.Expr) : Prop :=
  ∃ evs ev, DReach F ss σ (evs ++ [ev]) ∧ Trace.AssumptionsHold P evalInterp () evs ∧
    FailsAt t e ev ∧ ev.condition.expr = e

variable {F : P.Factory} {Lc S : List P.Ident} {ss B : PStmts P} {r : Outcome P}
  {X X' : Outcome P → Prop} {c : CmdExt P} {s : PStmt P} {rest : PStmts P}
  {σp σ σ' : SemanticStore P} {l : String} {e v : P.Expr} {md : MetaData P} {evs : List (Event P)}
  {o : Outcome P} {K K' : Outcome P → Prop} {t : AssertId P} {a b : List (Event P)}

/-! ## Typed loop-free stores, Boolean values, and an `assume` of the obligation program -/

/-- The loop-free values of the variables in scope `S` that the continuation reads (`V`) are
    values of their declared types `tys`. -/
@[expose] def TyOK (F : P.Factory) (tys : Tys P) (S V : List P.Ident) (σ : SemanticStore P) :
    Prop :=
  ∀ x ∈ S, x ∈ V → ∀ ty, tys.get? x = some ty → ∀ w, σ x = some w → HasVal.valueOfTy F w ty

omit iDE in
/-- One `assume` of the obligation program runs, feasibly when its condition holds. -/
theorem run_assume (he : P.eval F σ' e = some (HasBool.ttVal F)) :
    ∃ tr, MainRun F [.plain (.cmd (.cmd (.assume l e md)))] σ' tr σ' ∧
        Trace.AssumptionsHold P evalInterp () tr :=
  ⟨_, .plain .eval_assume .nil, fun _ hc => by grind [evalInterp]⟩

omit iDE iFv in
/-- The Boolean constants have the Boolean type. -/
theorem bool_valueOfTy {v : P.Val} (hb : v = HasBool.ttVal F ∨ v = HasBool.ffVal F) :
    HasVal.valueOfTy F v HasBool.boolTy :=
  hb.elim (· ▸ (HasBool.boolIsValOfTy F).1) (· ▸ (HasBool.boolIsValOfTy F).2)

/-! ## Commands -/

/-- An annotated run of a command ends normally, in a store the command's evaluation
    reaches with the run's events. -/
theorem DRunS.cmd_inv (h : DRunS F X (.cmd c) σ evs o) :
    ∃ σ1, o = .normal σ1 ∧ EvalE F σ c σ1 evs :=
  match h with | .cmd hc => ⟨_, rfl, hc⟩

/-! ## Weakening the requirement on untaken ends -/

omit iDE iBo iFv in
/-- Weakening the requirement `X` to `X'` weakens the requirement `VirtK r X` on an untaken
    end to `VirtK r X'`. -/
theorem VirtK.imp (hX : ∀ o, X o → X' o) {o' : (Outcome P)} (h : VirtK r X o') : VirtK r X' o' :=
  by cases r <;> cases o' <;> simp_all [VirtK]

/-! ## Monotonicity of the requirements

Shadow runs and annotated runs are monotone in their requirements; a failing trace splits
along `++`. -/

/-- Implications between the respective branches give an implication between two `if`s on
    the same condition. -/
private theorem ite_imp {c : Prop} [Decidable c] {A B A' B' : Prop} (h : if c then A else B)
    (hA : A → A') (hB : B → B') : if c then A' else B' := by split <;> simp_all

/-- An `if` of two propositions holds when both branches do. -/
private theorem ite_intro {c : Prop} [Decidable c] {A B : Prop} (hA : A) (hB : B) :
    if c then A else B := by split <;> assumption

omit iFv in
mutual
/-- A shadow run of a list with continuation `K` is one with any weaker continuation `K'`. -/
theorem ShL.imp : ∀ (L : (PStmts P)) (σ : SemanticStore P)
    {K K' : (Outcome P) → Prop}, (∀ o, K o → K' o) → ShL F L σ K → ShL F L σ K'
  | [], _, _, _, hK, h => hK _ h
  | s :: rest, σ, _, _, hK, h =>
    ShS.imp s σ (fun | .normal σ1, ho => ShL.imp rest σ1 hK ho | .exit _ _, ho => hK _ ho) h
/-- A shadow run of a statement with continuation `K` is one with any weaker continuation
    `K'`. -/
theorem ShS.imp : ∀ (s : (PStmt P)) (σ : SemanticStore P)
    {K K' : (Outcome P) → Prop}, (∀ o, K o → K' o) → ShS F s σ K → ShS F s σ K'
  | .cmd (.cmd c), _, _, _, hK, h => by
    cases c <;> first | exact hK _ h | exact Exists.imp (fun _ h => ⟨h.1, hK _ h.2⟩) h
  | .exit _ _, _, _, _, hK, h | .typeDecl _ _, _, _, _, hK, h => hK _ h
  | .ite (.det _) tss ess _, σ, _, _, hK, ⟨ht, he⟩ =>
    ⟨ite_imp ht (hK _) (ShL.imp tss σ fun _ => hK _),
      ite_imp he (hK _) (ShL.imp ess σ fun _ => hK _)⟩
  | .block _ ss _, σ, _, _, hK, h => ShL.imp ss σ (fun _ => hK _) h
end

omit iFv in
/-- A shadow run of a branch with continuation `K` is one with any weaker continuation `K'`. -/
theorem ShB.imp (hK : ∀ o, K o → K' o) (h : ShB F B σ K) : ShB F B σ K' :=
  ite_imp h (hK _) (ShL.imp B σ hK)

mutual
/-- An annotated run whose untaken ends satisfy `X` is one whose untaken ends satisfy any
    weaker `X'`. -/
theorem DRun.imp : ∀ {X X' : (Outcome P) → Prop} {ss : (PStmts P)}
    {σ : SemanticStore P} {evs : List (Event P)} {o : (Outcome P)},
    (∀ o, X o → X' o) → DRun F X ss σ evs o → DRun F X' ss σ evs o
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, hX, .cons_normal h1 h2 =>
    .cons_normal (h1.imp fun | .normal _, _ => trivial | .exit _ _, ho => hX _ ho) (h2.imp hX)
  | _, _, _, _, _, _, hX, .cons_exit (rest := rest) h =>
    .cons_exit (h.imp fun | .normal σv, ho => ShL.imp rest σv hX ho | .exit _ _, ho => hX _ ho)
/-- An annotated statement run whose untaken ends satisfy `X` is one whose untaken ends
    satisfy any weaker `X'`. -/
theorem DRunS.imp : ∀ {X X' : (Outcome P) → Prop} {s : (PStmt P)}
    {σ : SemanticStore P} {evs : List (Event P)} {o : (Outcome P)},
    (∀ o, X o → X' o) → DRunS F X s σ evs o → DRunS F X' s σ evs o
  | _, _, _, _, _, _, _, .cmd h => .cmd h
  | _, _, _, _, _, _, hX, .ite_true hc h hsh =>
    .ite_true hc (h.imp fun _ => hX _) (ShB.imp (fun _ => VirtK.imp fun _ => hX _) hsh)
  | _, _, _, _, _, _, hX, .ite_false hc h hsh =>
    .ite_false hc (h.imp fun _ => hX _) (ShB.imp (fun _ => VirtK.imp fun _ => hX _) hsh)
  | _, _, _, _, _, _, hX, .block h => .block (h.imp fun _ => hX _)
  | _, _, _, _, _, _, _, .exit => .exit
  | _, _, _, _, _, _, _, .typeDecl => .typeDecl
/-- An annotated run of a list that emits events gives an annotated reach of the list with the
    same events. -/
theorem DRun.toReach : ∀ {X : Outcome P → Prop} {ss : PStmts P}
    {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P},
    DRun F X ss σ evs o → evs ≠ [] → DReach F ss σ evs
  | _, _, _, _, _, .nil, hne => absurd rfl hne
  | _, _, _, _, _, .cons_normal (evs2 := []) h1 _, hne =>
    (List.append_nil _).symm ▸ .here (h1.toReachS (by simpa using hne))
  | _, _, _, _, _, .cons_normal (evs2 := _ :: _) h1 h2, _ =>
    .later (h1.imp fun _ _ => trivial) (h2.toReach nofun)
  | _, _, _, _, _, .cons_exit h, hne => .here (h.toReachS hne)
/-- An annotated statement run that emits events gives an annotated reach of the statement with
    the same events. -/
theorem DRunS.toReachS : ∀ {X : Outcome P → Prop} {s : PStmt P}
    {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P},
    DRunS F X s σ evs o → evs ≠ [] → DReachS F s σ evs
  | _, _, _, _, _, .cmd h, _ => .cmd h
  | _, _, _, _, _, .ite_true hc h _, hne => .ite_true hc (h.toReach hne)
  | _, _, _, _, _, .ite_false hc h hsh, hne =>
    .ite_false hc (h.toReach hne) (ShB.imp (fun _ _ => trivial) hsh)
  | _, _, _, _, _, .block h, hne => .block (h.toReach hne)
  | _, _, _, _, _, .exit, hne | _, _, _, _, _, .typeDecl, hne => absurd rfl hne
end

omit iDE iFv in
/-- If the events `a ++ b`, with `b` nonempty, claim a failure of `t` at an event of kind `k`, then
    `a` is feasible and `b` claims it at that event. -/
theorem claimK_split {k : Bool} {v : P.Expr} (hb : b ≠ []) (h : ClaimK k t v (a ++ b)) :
    Trace.AssumptionsHold P evalInterp () a ∧ ClaimK k t v b := by
  obtain ⟨evs, e, he, hA, hf⟩ := h
  obtain ⟨b, e', rfl⟩ := (List.eq_nil_or_concat b).resolve_left hb
  obtain ⟨rfl, ⟨⟩⟩ := List.append_inj'
    (by simpa using he : a ++ b ++ [e'] = evs ++ [if k then .cover e else .assert e]) rfl
  exact ⟨fun c hc => hA c (by simp [hc]), b, e, by simp, fun c hc => hA c (by simp [hc]), hf⟩

/-! ## Inversions

What an annotated run or reach of a cons consists of. -/

/-- An annotated run of `s :: rest` either runs `s` to a normal end and then `rest`, or
    exits from `s` (the untaken ends of `s` then include the shadow run of `rest`). -/
theorem DRun.cons_inv (h : DRun F X (s :: rest) σ evs o) :
    (∃ σ1 evs1 evs2, DRunS F (VirtK (.normal σ1) X) s σ evs1 (.normal σ1) ∧
      DRun F X rest σ1 evs2 o ∧ evs = evs1 ++ evs2) ∨
    (∃ l σ1, DRunS F (fun o => match o with
        | .normal σv => ShL F rest σv X
        | .exit l' σx => X (.exit l' σx)) s σ evs (.exit l σ1) ∧ o = .exit l σ1) :=
  match h with
  | .cons_normal h1 h2 => .inl ⟨_, _, _, h1, h2, rfl⟩
  | .cons_exit h1 => .inr ⟨_, _, h1, rfl⟩

/-- An annotated reach of `s :: rest` is a reach of `s`, or a run of `s` to a normal end
    followed by a reach of `rest`. -/
theorem DReach.cons_inv (h : DReach F (s :: rest) σ evs) :
    DReachS F s σ evs ∨ (∃ σ1 evs1 evs2, DRunS F (fun _ => True) s σ evs1 (.normal σ1) ∧
      DReach F rest σ1 evs2 ∧ evs = evs1 ++ evs2) :=
  match h with
  | .here h1 => .inl h1
  | .later h1 h2 => .inr ⟨_, _, _, h1, h2, rfl⟩

/-! ## Reaches of concatenated lists -/

omit iDE in
/-- A reach of `a` is a reach of `a ++ b`. -/
theorem breach_append_left : ∀ {a b : (PStmts P)} {σ : SemanticStore P} {tr : List (Event P)},
    BReach F a σ tr → BReach F (a ++ b) σ tr
  | _ :: _, _, _, _, .here h => .here h
  | _ :: _, _, _, _, .later h1 h2 => .later h1 (breach_append_left h2)

omit iDE in
/-- A reach of `a ++ b` is a reach of `a`, or a run of `a` followed by a reach of `b`. -/
theorem breach_append_inv : ∀ {a b : (PStmts P)} {σ : SemanticStore P} {tr : List (Event P)},
    BReach F (a ++ b) σ tr → BReach F a σ tr ∨
      ∃ t1 σ1 t2, BRun F a σ t1 (.normal σ1) ∧ BReach F b σ1 t2 ∧ tr = t1 ++ t2
  | [], _, _, _, h => .inr ⟨[], _, _, .nil, h, rfl⟩
  | _ :: _, _, _, _, .here h => .inl (.here h)
  | _ :: _, _, _, _, .later h1 h2 => (breach_append_inv h2).elim (fun h => .inl (.later h1 h))
    fun ⟨_, σ1, t2, h3, h4, he⟩ => .inr ⟨_, σ1, t2, .cons_normal h1 h3, h4, by simp [he]⟩

/-! ## Off-path runs exist when the declared types have values

The shadow runs of the obligation program evaluate no expression; they only bind a value of
the declared type at each `init`.  So every loop-free run is an annotated run when every type
declared by an `init` has a value (`Block.InitTypesInhabited`). -/

omit iDE iBo iFv in
/-- A requirement that all outcomes satisfy holds, as `VirtK`, of every untaken end. -/
private theorem virtK_of_all (hX : ∀ o, X o) : ∀ o, VirtK r X o := fun o => by
  cases r <;> cases o <;> first | trivial | exact hX _

section
include iB iLB iHa iFs

omit iFv in
mutual
/-- A well-scoped statement list whose declared types have values has a shadow run for every
    requirement that all outcomes satisfy. -/
theorem shL_of_initTys : ∀ {S : List P.Ident}
    {ss : (PStmts P)} (σ : SemanticStore P) {K : (Outcome P) → Prop}, Block.WellScoped Lc S ss →
    Block.InitTypesInhabited F ss → (∀ o, K o) → ShL F ss σ K
  | _, [], _, _, _, _, hK => hK _
  | _, _ :: _, σ, _, hwf, hty, hK => shS_of_initTys σ hwf.1 (List.forall_mem_append.1 hty).1 fun
      | .normal σ1 => shL_of_initTys σ1 hwf.2 (List.forall_mem_append.1 hty).2 hK
      | .exit _ _ => hK _
/-- A well-scoped statement whose declared types have values has a shadow run for every
    requirement that all outcomes satisfy. -/
theorem shS_of_initTys : ∀ {S : List P.Ident}
    {s : (PStmt P)} (σ : SemanticStore P) {K : (Outcome P) → Prop}, Stmt.WellScoped Lc S s →
    Stmt.InitTypesInhabited F s → (∀ o, K o) → ShS F s σ K
  | _, .cmd (.cmd c), _, _, _, hty, hK => by
    cases c <;> first | exact hK _ | exact (hty _ (.head _)).elim fun v hv => ⟨v, hv, hK _⟩
  | _, .exit _ _, _, _, _, _, hK | _, .typeDecl _ _, _, _, _, _, hK => hK _
  | _, .ite (.det _) _ _ _, σ, _, hwf, hty, hK =>
    ⟨ite_intro (hK _) (shL_of_initTys σ hwf.2.1 (List.forall_mem_append.1 hty).1 fun _ => hK _),
      ite_intro (hK _) (shL_of_initTys σ hwf.2.2 (List.forall_mem_append.1 hty).2 fun _ => hK _)⟩
  | _, .block _ ss _, σ, _, hwf, hty, hK => shL_of_initTys σ hwf hty fun _ => hK _
end

omit iFv in
/-- A well-scoped branch whose declared types have values has a shadow run for every
    requirement that all outcomes satisfy. -/
theorem shB_of_initTys (σ : SemanticStore P) {K : (Outcome P) → Prop}
    (hwf : Block.WellScoped Lc S B)
    (hty : Block.InitTypesInhabited F B) (hK : ∀ o, K o) : ShB F B σ K :=
  ite_intro (hK _) (shL_of_initTys σ hwf hty hK)

/-- A run of a well-scoped loop-free statement whose declared types have values is an annotated
    run, for every requirement on untaken ends that all outcomes satisfy. -/
theorem BRunS.toDRunS : ∀ {X : (Outcome P) → Prop}
    {S : List P.Ident} {s : (PStmt P)} {σ : SemanticStore P} {evs : List (Event P)}
    {o : (Outcome P)}, BRunS F s σ evs o → Stmt.WellScoped Lc S s →
    Stmt.InitTypesInhabited F s → (∀ o, X o) → DRunS F X s σ evs o := by
  intro X S s σ evs o h
  induction h using BRunS.rec (motive_1 := fun ss σ evs o _ => ∀ (X : Outcome P → Prop) S,
    Block.WellScoped Lc S ss → Block.InitTypesInhabited F ss → (∀ o, X o) → DRun F X ss σ evs o)
    generalizing X S with
  | cons_normal _ _ ih1 ih2 X S hwf hty hX =>
    exact .cons_normal (ih1 hwf.1 (List.forall_mem_append.1 hty).1 (virtK_of_all hX))
      (ih2 X _ hwf.2 (List.forall_mem_append.1 hty).2 hX)
  | cons_exit _ ih X S hwf hty hX =>
    exact .cons_exit (ih hwf.1 (List.forall_mem_append.1 hty).1 fun
      | .normal σv => shL_of_initTys σv hwf.2 (List.forall_mem_append.1 hty).2 hX
      | .exit _ _ => hX _)
  | ite_true hc _ ih =>
    exact fun hwf hty hX => .ite_true hc
      (ih _ _ hwf.2.1 (List.forall_mem_append.1 hty).1 fun _ => hX _)
      (shB_of_initTys _ hwf.2.2 (List.forall_mem_append.1 hty).2 (virtK_of_all fun _ => hX _))
  | ite_false hc _ ih =>
    exact fun hwf hty hX => .ite_false hc
      (ih _ _ hwf.2.2 (List.forall_mem_append.1 hty).2 fun _ => hX _)
      (shB_of_initTys _ hwf.2.1 (List.forall_mem_append.1 hty).1 (virtK_of_all fun _ => hX _))
  | _ => intros; first | (constructor <;> solve_by_elim) | (exfalso; assumption)

/-- The obligation program's runs off every loop-free path from `σ` exist when every type declared
    by an `init` of the well-scoped loop-free list `ss` has a value: every big-step reach of `ss`
    from `σ` is an annotated reach (`DReach`).  That is, along every loop-free path, the shadow
    runs (`ShL`/`ShS`) exist of the laid-out branches the path skips and of the other ends of each
    statement the path leaves by an `exit`: in them every `init` binds a value of its declared
    type. -/
theorem shadowOK_of_initTysOK (hwf : Block.WellScoped Lc S ss)
    (hinh : Block.InitTypesInhabited F ss) (σ : SemanticStore P) :
    ∀ evs, BReach F ss σ evs → DReach F ss σ evs := by
  intro evs h
  induction h using BReach.rec (motive_2 := fun s σ evs _ => ∀ S : List P.Ident,
    Stmt.WellScoped Lc S s → Stmt.InitTypesInhabited F s → DReachS F s σ evs) generalizing S with
  | here _ ih => exact .here (ih _ hwf.1 (List.forall_mem_append.1 hinh).1)
  | later h1 _ ih =>
    exact .later (BRunS.toDRunS h1 hwf.1 (List.forall_mem_append.1 hinh).1 fun _ => trivial)
      (ih hwf.2 (List.forall_mem_append.1 hinh).2)
  | ite_true hc _ ih _ hwf hty => exact .ite_true hc (ih hwf.2.1 (List.forall_mem_append.1 hty).1)
  | ite_false hc _ ih _ hwf hty =>
    exact .ite_false hc (ih hwf.2.2 (List.forall_mem_append.1 hty).2)
      (shB_of_initTys _ hwf.2.1 (List.forall_mem_append.1 hty).1 fun _ => trivial)
  | _ => intros; first | (constructor <;> solve_by_elim) | (exfalso; assumption)

end

end -- public section

end WP
end Imperative
