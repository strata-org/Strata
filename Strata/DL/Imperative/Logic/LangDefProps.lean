/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Logic.LangDef
public import Strata.DL.Imperative.Logic.Termination
public import Strata.DL.Imperative.StmtSemanticsProps
import Strata.DL.Imperative.Logic.TerminationProps
import Strata.Util.RelationsProps
import Strata.DL.Imperative.Logic.TraceInterpProps

/-! # Properties of the Imperative language instances and their gates

Key results:
  * `BlockInitEnvWF.generatedNamesFresh` — no name under a reserved prefix is
    defined in a block-well-formed initial store.
  * `BlockInitEnvWF.notReserved_of_mem` — no name a block-well-formed block reads,
    modifies or defines has a reserved prefix.
  * `mustTerminateAndAssertsValid_seqE`, `mustTerminateAndAssertsValid_blockE`,
    `mustTerminateAndAssertsValid_stmts_appendE` — a sequence frame, a block frame, and a
    concatenation of statement lists must terminate with valid assertions when their parts do.
  * `mustTerminateAndAssertsValid_of_seqE` — the head of a sequence frame that must terminate
    with valid assertions must terminate with valid assertions.
  * `mustTerminateAndAssertsValid_imperativeE_of_imperativeBlockE`,
    `mustTerminateAndAssertsValid_imperativeBlockE_of_imperativeE` — `EventLang.imperativeE` and
    `EventLang.imperativeBlockE` agree on must-termination with valid assertions. -/

public section

namespace Imperative

namespace Logic

/-- No name under a reserved prefix is defined in a block-well-formed initial
store: this is the contrapositive of `reservedFresh`. -/
theorem BlockInitEnvWF.generatedNamesFresh {P : PureExpr} [HasBool P] [HasBoolOps P]
    [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] [HasSubstFvar P]
    [HasIdent P] [HasOps P] [DecidableEq P.Ident]
    {CmdT : Type} [HasVarsImp P CmdT] [HasOpsImp P CmdT]
    [HasInitTypesImp P CmdT] [HasTypedVarsImp P CmdT]
    {params : InitEnvWFParams P} {ss : List (Stmt P CmdT)} {ρ : Env P}
    (h : BlockInitEnvWF params ss ρ) :
    Env.varsUndefined (P := P)
      (fun name => ∃ pfx ∈ params.prefixIdents,
        pfx.toList.isPrefixOf name.toList) ρ := by
  intro ident hident
  obtain ⟨name, ⟨pfx, hpfx, hprefix⟩, rfl⟩ := hident
  cases hstore : ρ.store (HasIdent.ident (P := P) name) with
  | none => rfl
  | some value =>
    exact absurd hprefix
      (h.reservedFresh (HasIdent.ident (P := P) name)
        (by rw [hstore]; rfl) name rfl pfx hpfx)

/-- A name that a block-well-formed block reads, modifies or defines avoids every reserved
prefix: the gate keeps the block's own definitions off the reserved prefixes, and any other
name the block touches is bound at entry, where no binding has a reserved prefix. -/
theorem BlockInitEnvWF.notReserved_of_mem {P : PureExpr} [HasBool P] [HasBoolOps P]
    [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] [HasSubstFvar P]
    [HasIdent P] [HasOps P] [DecidableEq P.Ident]
    {CmdT : Type} [HasVarsImp P CmdT] [HasOpsImp P CmdT]
    [HasInitTypesImp P CmdT] [HasTypedVarsImp P CmdT]
    {params : InitEnvWFParams P} {ss : List (Stmt P CmdT)} {ρ : Env P}
    (h : BlockInitEnvWF params ss ρ) {name : String}
    (hn : HasIdent.ident (P := P) name ∈ Block.touchedVars ss ∨
      HasIdent.ident (P := P) name ∈ Block.definedVars ss false)
    {p : String} (hp : p ∈ params.prefixIdents) :
    ¬ p.toList.isPrefixOf name.toList := by
  by_cases hd : HasIdent.ident (P := P) name ∈ Block.definedVars ss false
  · exact h.definedVarsNotReserved _ hd name rfl p hp
  · exact h.reservedFresh _ (h.readWritesDefined _ (hn.resolve_right hd) hd) name rfl p hp

/-! ## Must-termination with valid assertions of the structured Imperative languages

`EventLang.imperativeE` and `EventLang.imperativeBlockE` share their configurations and their
step relation `StepStmtE`, so they agree on which configurations must terminate after
assumes.  The frame lemmas below are stated for `EventLang.imperativeE`, in a fixed world `w`
of a condition interpretation `I`. -/

section MustTerminateAndAssertsValid

open Strata.Logic

variable {P : PureExpr} [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P] [HasInt P]
  [HasIntOps P] [HasSubstFvar P] {CmdT : Type}
  {evalCmd : EvalCmdParamE P CmdT (Event P)}
  {initEnvWF : InitEnvWFParams P → Stmt P CmdT → Env P → Prop}
  {I : ConditionInterp P} {w : I.World}

omit [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P]
  [HasSubstFvar P] in
/-- The empty trace has no assumption. -/
private theorem assumptionsHold_nil : Trace.AssumptionsHold P I w [] :=
  fun _ h => nomatch h

omit [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P]
  [HasSubstFvar P] in
/-- The empty trace has no assertion. -/
private theorem assertionsHoldIn_nil : Trace.AssertionsHoldIn P I w [] := by
  simp [Trace.AssertionsHoldIn]

/-- Induction on must-termination with valid assertions in `EventLang.imperativeE`, with its steps
    read as `StepStmtE` steps. -/
private theorem mustTerminateAndAssertsValid_imperativeE_induction
    {motive : (cfg : Config P CmdT) →
      (EventLang.imperativeE P CmdT evalCmd initEnvWF).MustTerminateAndAssertsValid I w cfg →
        Prop}
    (terminal : ∀ ρ, motive (.terminal ρ) (.terminal ρ))
    (exiting : ∀ label ρ, motive (.exiting label ρ) (.exiting label ρ))
    (step : ∀ {cfg : Config P CmdT}
      (progress : ∃ emitted cfg', StepStmtE P evalCmd cfg emitted cfg')
      (asserts : ∀ emitted cfg', StepStmtE P evalCmd cfg emitted cfg' →
        Trace.AssertionsHoldIn P I w emitted)
      (successors : ∀ emitted cfg', StepStmtE P evalCmd cfg emitted cfg' →
        Trace.AssumptionsHold P I w emitted →
        (EventLang.imperativeE P CmdT evalCmd initEnvWF).MustTerminateAndAssertsValid I w cfg'),
      (∀ emitted cfg' (hs : StepStmtE P evalCmd cfg emitted cfg')
        (ha : Trace.AssumptionsHold P I w emitted),
        motive cfg' (successors emitted cfg' hs ha)) →
      motive cfg (.step progress asserts successors))
    {cfg : Config P CmdT}
    (h : (EventLang.imperativeE P CmdT evalCmd initEnvWF).MustTerminateAndAssertsValid I w cfg) :
    motive cfg h :=
  EventLang.MustTerminateAndAssertsValid.rec
    (EL := EventLang.imperativeE P CmdT evalCmd initEnvWF)
    (motive := motive) terminal exiting
    (fun progress asserts successors ih => step progress asserts successors ih) h

/-- A configuration that must terminate with valid assertions in `EventLang.imperativeBlockE` must
    terminate with valid assertions in `EventLang.imperativeE`. -/
theorem mustTerminateAndAssertsValid_imperativeE_of_imperativeBlockE
    {blockInitEnvWF : InitEnvWFParams P → List (Stmt P CmdT) → Env P → Prop}
    {cfg : Config P CmdT}
    (h : (EventLang.imperativeBlockE P CmdT evalCmd blockInitEnvWF).MustTerminateAndAssertsValid
      I w cfg) :
    (EventLang.imperativeE P CmdT evalCmd initEnvWF).MustTerminateAndAssertsValid I w cfg :=
  EventLang.MustTerminateAndAssertsValid.rec
    (EL := EventLang.imperativeBlockE P CmdT evalCmd blockInitEnvWF)
    (motive := fun c _ =>
      (EventLang.imperativeE P CmdT evalCmd initEnvWF).MustTerminateAndAssertsValid I w c)
    (fun ρ => .terminal ρ) (fun label ρ => .exiting label ρ)
    (fun hprog has _ ih => .step hprog has ih) h

/-- A configuration that must terminate with valid assertions in `EventLang.imperativeE` must
    terminate with valid assertions in `EventLang.imperativeBlockE`. -/
theorem mustTerminateAndAssertsValid_imperativeBlockE_of_imperativeE
    {blockInitEnvWF : InitEnvWFParams P → List (Stmt P CmdT) → Env P → Prop}
    {cfg : Config P CmdT}
    (h : (EventLang.imperativeE P CmdT evalCmd initEnvWF).MustTerminateAndAssertsValid I w cfg) :
    (EventLang.imperativeBlockE P CmdT evalCmd blockInitEnvWF).MustTerminateAndAssertsValid
      I w cfg :=
  mustTerminateAndAssertsValid_imperativeE_induction (motive := fun c _ =>
      (EventLang.imperativeBlockE P CmdT evalCmd blockInitEnvWF).MustTerminateAndAssertsValid
        I w c)
    (fun ρ => .terminal ρ) (fun label ρ => .exiting label ρ)
    (fun hprog has _ ih => .step hprog has ih) h

/-- The empty statement list must terminate with valid assertions. -/
theorem mustTerminateAndAssertsValid_stmts_nilE {ρ : Env P} :
    (EventLang.imperativeE P CmdT evalCmd initEnvWF).MustTerminateAndAssertsValid I w
      (.stmts [] ρ) :=
  .step ⟨[], _, (.step_stmts_nil : StepStmtE P evalCmd _ _ _)⟩
    (fun _ _ hs => by cases (hs : StepStmtE P evalCmd _ _ _); exact assertionsHoldIn_nil)
    fun _ _ hs _ => by
    cases (hs : StepStmtE P evalCmd _ _ _)
    exact .terminal _

/-- A non-empty statement list must terminate with valid assertions when its head, in a sequence
    frame over the rest, must terminate with valid assertions. -/
theorem mustTerminateAndAssertsValid_stmts_consE {s : Stmt P CmdT} {ss : List (Stmt P CmdT)}
    {ρ : Env P}
    (h : (EventLang.imperativeE P CmdT evalCmd initEnvWF).MustTerminateAndAssertsValid I w
      (.seq (.stmt s ρ) ss)) :
    (EventLang.imperativeE P CmdT evalCmd initEnvWF).MustTerminateAndAssertsValid I w
      (.stmts (s :: ss) ρ) :=
  .step ⟨[], _, (.step_stmts_cons : StepStmtE P evalCmd _ _ _)⟩
    (fun _ _ hs => by cases (hs : StepStmtE P evalCmd _ _ _); exact assertionsHoldIn_nil)
    fun _ _ hs _ => by
    cases (hs : StepStmtE P evalCmd _ _ _)
    exact h

/-- **Sequence frame.**  `.seq inner ss` must terminate with valid assertions in `w` when `inner`
    does and `ss` does from every environment at which a run of `inner` whose assumptions
    hold in `w` terminates. -/
theorem mustTerminateAndAssertsValid_seqE {inner : Config P CmdT} {ss : List (Stmt P CmdT)}
    (h : (EventLang.imperativeE P CmdT evalCmd initEnvWF).MustTerminateAndAssertsValid I w inner)
    (hk : ∀ tr ρ₁, StepStmtStarE P evalCmd inner tr (.terminal ρ₁) →
      Trace.AssumptionsHold P I w tr →
      (EventLang.imperativeE P CmdT evalCmd initEnvWF).MustTerminateAndAssertsValid I w
        (.stmts ss ρ₁)) :
    (EventLang.imperativeE P CmdT evalCmd initEnvWF).MustTerminateAndAssertsValid I w
      (.seq inner ss) := by
  induction h using mustTerminateAndAssertsValid_imperativeE_induction with
  | terminal ρ =>
    refine .step ⟨[], _, (.step_seq_done : StepStmtE P evalCmd _ _ _)⟩ (fun _ _ hs => ?_)
      fun _ _ hs _ => ?_
    · cases (hs : StepStmtE P evalCmd _ _ _) with
      | step_seq_done => exact assertionsHoldIn_nil
      | step_seq_inner h' => cases h'
    cases (hs : StepStmtE P evalCmd _ _ _) with
    | step_seq_done => exact hk [] ρ (.refl _) assumptionsHold_nil
    | step_seq_inner h' => cases h'
  | exiting label ρ =>
    refine .step ⟨[], _, (.step_seq_exit : StepStmtE P evalCmd _ _ _)⟩ (fun _ _ hs => ?_)
      fun _ _ hs _ => ?_
    · cases (hs : StepStmtE P evalCmd _ _ _) with
      | step_seq_exit => exact assertionsHoldIn_nil
      | step_seq_inner h' => cases h'
    cases (hs : StepStmtE P evalCmd _ _ _) with
    | step_seq_exit => exact .exiting _ _
    | step_seq_inner h' => cases h'
  | step hprog has _ ih =>
    obtain ⟨emitted, next, hnext⟩ := hprog
    refine .step ⟨emitted, _, (.step_seq_inner hnext : StepStmtE P evalCmd _ _ _)⟩
      (fun _ _ hs => ?_) fun _ _ hs ha => ?_
    · cases (hs : StepStmtE P evalCmd _ _ _) with
      | step_seq_inner h' => exact has _ _ h'
      | step_seq_done => cases (hnext : StepStmtE P evalCmd _ _ _)
      | step_seq_exit => cases (hnext : StepStmtE P evalCmd _ _ _)
    cases (hs : StepStmtE P evalCmd _ _ _) with
    | step_seq_inner h' =>
      exact ih _ _ h' ha fun tr ρ₁ hrun hA =>
        hk _ ρ₁ (.step _ _ _ _ _ h' hrun) (Trace.AssumptionsHold.append ha hA)
    | step_seq_done => cases (hnext : StepStmtE P evalCmd _ _ _)
    | step_seq_exit => cases (hnext : StepStmtE P evalCmd _ _ _)

/-- The head of a sequence frame that must terminate with valid assertions must terminate with
    valid assertions. -/
theorem mustTerminateAndAssertsValid_of_seqE {inner : Config P CmdT} {ss : List (Stmt P CmdT)}
    (h : (EventLang.imperativeE P CmdT evalCmd initEnvWF).MustTerminateAndAssertsValid I w
      (.seq inner ss)) :
    (EventLang.imperativeE P CmdT evalCmd initEnvWF).MustTerminateAndAssertsValid I w inner := by
  generalize hc : (Config.seq inner ss : Config P CmdT) = c at h
  induction h using mustTerminateAndAssertsValid_imperativeE_induction generalizing inner with
  | terminal ρ => cases hc
  | exiting label ρ => cases hc
  | step hprog has _ ih =>
    subst hc
    obtain ⟨emitted, next, hnext⟩ := hprog
    cases (hnext : StepStmtE P evalCmd _ _ _) with
    | step_seq_inner h' =>
      exact .step ⟨_, _, h'⟩ (fun e c' hc' => has e _ (.step_seq_inner hc'))
        fun e c' hc' ha => ih e _ (.step_seq_inner hc') ha rfl
    | step_seq_done => exact .terminal _
    | step_seq_exit => exact .exiting _ _

/-- **Block frame.**  `.block label σ inner` must terminate with valid assertions when `inner`
    does. -/
theorem mustTerminateAndAssertsValid_blockE {inner : Config P CmdT} {label : Option String}
    {σ : SemanticStore P}
    (h : (EventLang.imperativeE P CmdT evalCmd initEnvWF).MustTerminateAndAssertsValid I w inner) :
    (EventLang.imperativeE P CmdT evalCmd initEnvWF).MustTerminateAndAssertsValid I w
      (.block label σ inner) := by
  induction h using mustTerminateAndAssertsValid_imperativeE_induction with
  | terminal ρ =>
    refine .step ⟨[], _, (.step_block_done : StepStmtE P evalCmd _ _ _)⟩ (fun _ _ hs => ?_)
      fun _ _ hs _ => ?_
    · cases (hs : StepStmtE P evalCmd _ _ _) with
      | step_block_done => exact assertionsHoldIn_nil
      | step_block_body h' => cases h'
    cases (hs : StepStmtE P evalCmd _ _ _) with
    | step_block_done => exact .terminal _
    | step_block_body h' => cases h'
  | exiting l ρ =>
    have hprog : ∃ emitted cfg', StepStmtE P evalCmd
        (.block label σ (.exiting l ρ)) emitted cfg' := by
      by_cases hl : label = some l
      · exact ⟨[], _, .step_block_exit_match hl⟩
      · exact ⟨[], _, .step_block_exit_mismatch hl⟩
    refine .step hprog (fun _ _ hs => ?_) fun _ _ hs _ => ?_
    · cases (hs : StepStmtE P evalCmd _ _ _) with
      | step_block_exit_match _ => exact assertionsHoldIn_nil
      | step_block_exit_mismatch _ => exact assertionsHoldIn_nil
      | step_block_body h' => cases h'
    cases (hs : StepStmtE P evalCmd _ _ _) with
    | step_block_exit_match _ => exact .terminal _
    | step_block_exit_mismatch _ => exact .exiting _ _
    | step_block_body h' => cases h'
  | step hprog has _ ih =>
    obtain ⟨emitted, next, hnext⟩ := hprog
    refine .step ⟨emitted, _, (.step_block_body hnext : StepStmtE P evalCmd _ _ _)⟩
      (fun _ _ hs => ?_) fun _ _ hs ha => ?_
    · cases (hs : StepStmtE P evalCmd _ _ _) with
      | step_block_body h' => exact has _ _ h'
      | step_block_done => cases (hnext : StepStmtE P evalCmd _ _ _)
      | step_block_exit_match _ => cases (hnext : StepStmtE P evalCmd _ _ _)
      | step_block_exit_mismatch _ => cases (hnext : StepStmtE P evalCmd _ _ _)
    cases (hs : StepStmtE P evalCmd _ _ _) with
    | step_block_body h' => exact ih _ _ h' ha
    | step_block_done => cases (hnext : StepStmtE P evalCmd _ _ _)
    | step_block_exit_match _ => cases (hnext : StepStmtE P evalCmd _ _ _)
    | step_block_exit_mismatch _ => cases (hnext : StepStmtE P evalCmd _ _ _)

/-- **Concatenation.**  `ss₁ ++ ss₂` must terminate with valid assertions in `w` from `ρ` when `ss₁`
    does from `ρ` and `ss₂` does from every environment at which a run of `ss₁` from `ρ`
    whose assumptions hold in `w` terminates. -/
theorem mustTerminateAndAssertsValid_stmts_appendE {ss₂ : List (Stmt P CmdT)} :
    ∀ (ss₁ : List (Stmt P CmdT)) (ρ : Env P),
      (EventLang.imperativeE P CmdT evalCmd initEnvWF).MustTerminateAndAssertsValid I w
        (.stmts ss₁ ρ) →
      (∀ tr ρ₁, StepStmtStarE P evalCmd (.stmts ss₁ ρ) tr (.terminal ρ₁) →
        Trace.AssumptionsHold P I w tr →
        (EventLang.imperativeE P CmdT evalCmd initEnvWF).MustTerminateAndAssertsValid I w
          (.stmts ss₂ ρ₁)) →
      (EventLang.imperativeE P CmdT evalCmd initEnvWF).MustTerminateAndAssertsValid I w
        (.stmts (ss₁ ++ ss₂) ρ)
  | [], ρ, _, hk => hk [] ρ (.step _ [] _ [] _ .step_stmts_nil (.refl _)) assumptionsHold_nil
  | s :: ss₁, ρ, h, hk => by
    have hseq : (EventLang.imperativeE P CmdT evalCmd initEnvWF).MustTerminateAndAssertsValid I w
        (.seq (.stmt s ρ) ss₁) :=
      h.of_step (.step_stmts_cons : StepStmtE P evalCmd _ _ _) assumptionsHold_nil
    refine mustTerminateAndAssertsValid_stmts_consE
      (mustTerminateAndAssertsValid_seqE (mustTerminateAndAssertsValid_of_seqE hseq) ?_)
    intro tr ρ₁ hhead hA
    have hcons := stmts_cons_stepE evalCmd s ss₁ ρ ρ₁ hhead
    exact mustTerminateAndAssertsValid_stmts_appendE ss₁ ρ₁ (h.of_traceStar hcons hA)
      fun tr' ρ₂ hrest hA' =>
        hk _ ρ₂ (ReflTransTrace.trans _ hcons hrest) (Trace.AssumptionsHold.append hA hA')

end MustTerminateAndAssertsValid

end Logic

end Imperative

end -- public section
