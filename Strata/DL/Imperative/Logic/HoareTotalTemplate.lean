/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Logic.HoareTemplate
public import Strata.DL.Imperative.Logic.LangDefProps
public import Strata.DL.Imperative.Analysis.Assertions
import Strata.DL.Imperative.Logic.TerminationProps
import all Strata.DL.Imperative.Logic.HoareTemplate

/-! # A total-correctness Hoare-logic template for the Imperative dialect

The total-correctness counterpart of `Strata.DL.Imperative.Logic.HoareTemplate`. Like that
module it is a template: a language instantiates it (see
`Strata.Languages.Core.Logic.HoareTotal`) to obtain usable rules.

`Strata.Logic.HoareTotal.TripleWith` asks for termination with valid assertions
(`EventLang.TerminatesAndAssertsValid`): in every world of the condition interpretation, every
execution from an admitted entry satisfying the precondition whose `assume` events hold in that
world terminates, without diverging or getting stuck, and its assertions hold in that world.
It also asks for the postcondition at the end of every finished run whose trace is reachable,
and it gives the partial-correctness `Strata.Logic.Hoare.TripleWith` (`TripleWith.to_partial`).
Since only reachable runs owe the postcondition, an `assume` may feed it:
`{True} havoc x; assume x > 0 {x > 0}` holds.  An execution
an `assume` makes unreachable may diverge, so `{True} assume false; while (true) {} {False}`
holds as well.

## Why it is per world

A run is reachable when one world satisfies all its assumptions (`Trace.Reachable`).
Termination with valid assertions fixes a world and follows only the steps whose assumptions
hold in it, so the sequencing and loop rules compose: in a fixed world, the prefix of a run is
reachable, so the intermediate assertion or the loop invariant holds where the rest starts.
A total triple is a partial triple together with that condition, so a partial triple
`{Pre} s {Post}` and a total triple `{Pre} s {True}` give the total triple `{Pre} s {Post}`
(`TripleWith.of_partial_of_true`).

The assertions are checked step by step, so they are valid on every finite execution
(`TripleWith.allAssertsValidOnTracesWhen`), as the partial triple requires.  Without that,
`assume x > 0; assert false; assume x < 0; while (true) {}` would meet any total triple: it has
no finished run, and its divergence starts only after an assumption that no world reaching the
failing assertion satisfies.

The termination counts every step of the language, including a command that runs a whole
procedure body: in Core, a call is one step, so a triple about a call says that the call can
execute, not that every run of the callee terminates.

## Contents

`Strata.Logic.HoareTotal.TripleWith`, its relation to the partial triple
(`TripleWith.to_partial`, `TripleWith.of_partial_of_true`), the validity of every assertion on
every finite execution (`TripleWith.allAssertsValidOnTracesWhen`), and the rules `false_pre`,
`consequence`, `skip_block`, `cmd`, `seq_append`, `exit_cons`, `block`, `singleton`, `skip`,
`ite` and `while_rule`.

The rules that choose a branch (`ite`, `while_rule`) additionally require the condition to
evaluate to a Boolean, since a run whose condition does not evaluate is stuck. The loop rule
takes a natural-number measure that every iteration decreases; a loop's `decreases` clause can
supply it, read off the value the clause evaluates to.
-/

public section

section HoareTotalRules

variable {P : Imperative.PureExpr}
variable {conditionInterp : Imperative.ConditionInterp P}

namespace Strata.Logic.HoareTotal

open Imperative

section

variable (L : EventLang P (Event P))

/-- Total-correctness Hoare triple: for every initial environment satisfying `Pre` that the
    language's `initEnvWF` admits, `s` terminates with valid assertions (in every world, every
    execution whose `assume` events hold there terminates and has its assertions hold there),
    and every run of `s` that terminates normally or by an exit (`L.TerminatesAt`) with a
    reachable trace ends in an environment satisfying `Post`.  The partial-correctness
    `Strata.Logic.Hoare.TripleWith` follows (`TripleWith.to_partial`): the first part gives
    the validity of the assertions of every finite execution. -/
@[expose] def TripleWith (conditionInterp : ConditionInterp P)
    (params : L.InitEnvWFParamsTy)
    (Pre : Env P → Prop) (s : L.StmtT) (Post : Env P → Prop) : Prop :=
  ∀ ρ₀, Pre ρ₀ → L.initEnvWF params s ρ₀ →
    L.TerminatesAndAssertsValid conditionInterp s ρ₀ ∧
      ∀ ρ' trace, L.TerminatesAt s ρ₀ trace ρ' →
        Trace.Reachable P conditionInterp trace → Post ρ'

end

variable {L : EventLang P (Event P)}

/-- A total triple gives the partial triple with the same pre- and postcondition: the
    assertions of every finite execution hold in every world. -/
theorem TripleWith.to_partial {params : L.InitEnvWFParamsTy} {Pre Post : Env P → Prop}
    {s : L.StmtT} (h : TripleWith L conditionInterp params Pre s Post) :
    Strata.Logic.Hoare.TripleWith L conditionInterp params Pre s Post := by
  intro ρ₀ hpre hinit
  obtain ⟨hterm, hpost⟩ := h ρ₀ hpre hinit
  exact ⟨fun _ trace hrun => (Trace.AssertionsValid_iff_assertionsHoldIn _ trace).2 fun w =>
    (hterm w).assertionsHoldIn hrun, hpost⟩

/-- A total triple from a partial triple and termination with valid assertions from every admitted
    entry satisfying the precondition. -/
private theorem TripleWith.of_partial {params : L.InitEnvWFParamsTy}
    {Pre Post : Env P → Prop} {s : L.StmtT}
    (hpartial : Strata.Logic.Hoare.TripleWith L conditionInterp params Pre s Post)
    (hterm : ∀ ρ₀, Pre ρ₀ → L.initEnvWF params s ρ₀ →
      L.TerminatesAndAssertsValid conditionInterp s ρ₀) :
    TripleWith L conditionInterp params Pre s Post :=
  fun ρ₀ hpre hinit => ⟨hterm ρ₀ hpre hinit, (hpartial ρ₀ hpre hinit).2⟩

/-- **Partial correctness and termination give total correctness.**  A partial triple
    `{Pre} s {Post}` and a total triple `{Pre} s {True}` give the total triple
    `{Pre} s {Post}`. -/
theorem TripleWith.of_partial_of_true {params : L.InitEnvWFParamsTy}
    {Pre Post : Env P → Prop} {s : L.StmtT}
    (hpartial : Strata.Logic.Hoare.TripleWith L conditionInterp params Pre s Post)
    (hterm : TripleWith L conditionInterp params Pre s (fun _ => True)) :
    TripleWith L conditionInterp params Pre s Post :=
  TripleWith.of_partial hpartial fun ρ₀ hpre hinit => (hterm ρ₀ hpre hinit).1

/-- **A total triple validates every assertion on every finite execution.**  From every entry
    satisfying `Pre`, all of which the language admits (`hinit`), every finite execution of
    `s`, finished or not, has valid assertions. -/
theorem TripleWith.allAssertsValidOnTracesWhen {params : L.InitEnvWFParamsTy}
    {Pre Post : Env P → Prop} {s : L.StmtT}
    (h : TripleWith L conditionInterp params Pre s Post)
    (hinit : ∀ ρ₀, Pre ρ₀ → L.initEnvWF params s ρ₀) :
    Imperative.Specification.AllAssertsValidOnTracesWhen L conditionInterp Pre s :=
  fun ρ₀ _ trace hpre hrun => (Trace.AssertionsValid_iff_assertionsHoldIn _ trace).2
    fun w => ((h ρ₀ hpre (hinit ρ₀ hpre)).1 w).assertionsHoldIn hrun

end Strata.Logic.HoareTotal

local notation "I" => conditionInterp
local notation "Triple" => fun L => Strata.Logic.HoareTotal.TripleWith L conditionInterp

namespace Strata.Logic.HoareTotal

open Imperative

variable (L : EventLang P (Event P))

/-! ## Rules that do not inspect the statement -/

/-- False precondition proves anything. -/
theorem false_pre (params : L.InitEnvWFParamsTy) (s : L.StmtT) (Post : Env P → Prop) :
    Triple L params (fun _ => False) s Post :=
  fun _ hpre => absurd hpre id

/-- Consequence (weakening): strengthen precondition, weaken postconditions. -/
theorem consequence (params : L.InitEnvWFParamsTy)
    {Pre Pre' Post Post' : Env P → Prop} {s : L.StmtT}
    (h : Triple L params Pre s Post)
    (hpre : ∀ ρ, Pre' ρ → Pre ρ) (hpost : ∀ ρ, Post ρ → Post' ρ) :
    Triple L params Pre' s Post' := by
  intro ρ₀ hpre' hinit
  obtain ⟨hterm, hruns⟩ := h ρ₀ (hpre ρ₀ hpre') hinit
  exact ⟨hterm, fun ρ' trace hrun hreach => hpost ρ' (hruns ρ' trace hrun hreach)⟩

end Strata.Logic.HoareTotal

namespace Imperative.Logic.HoareTotal

open Strata.Logic Strata.Logic.HoareTotal

/-! ## Structural rules (Structured Imperative-specific) -/

section StmtRules

variable [HasFvar P] [HasFvars P] [HasBool P] [HasBoolOps P]
    [HasSubstFvar P] [HasInt P] [HasIntOps P]
variable {CmdT : Type}
variable (evalCmd : EvalCmdParamE P CmdT (Event P))
variable (initEnvWF : InitEnvWFParams P → Stmt P CmdT → Env P → Prop)
variable (blockInitEnvWF : InitEnvWFParams P → List (Stmt P CmdT) → Env P → Prop)
variable (bparams : InitEnvWFParams P)

omit [HasFvar P] [HasFvars P] [HasBool P] [HasBoolOps P] [HasSubstFvar P] [HasInt P]
  [HasIntOps P] in
/-- The empty trace has no assertion. -/
private theorem assertionsHoldIn_nil {w : conditionInterp.World} :
    Trace.AssertionsHoldIn P I w [] := by
  simp [Trace.AssertionsHoldIn]

/-- Empty statement list is skip. -/
theorem skip_block (Pre : Env P → Prop) :
    Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams Pre [] Pre :=
  TripleWith.of_partial
    (Imperative.Logic.Hoare.skip_block evalCmd blockInitEnvWF bparams Pre)
    (fun _ _ _ _ => mustTerminateAndAssertsValid_imperativeBlockE_of_imperativeE
      (initEnvWF := fun _ _ _ => True) mustTerminateAndAssertsValid_stmts_nilE)

/-- **A single command.**  `hprog` asks, for every `Pre`-environment the language admits, that
    the command can step; `h` asks that every step has valid assertions and, when its trace is
    reachable, ends in `Post`. -/
theorem cmd (params : InitEnvWFParams P) (c : CmdT)
    (Pre Post : Env P → Prop)
    (hprog : ∀ ρ₀, Pre ρ₀ → initEnvWF params (.cmd c) ρ₀ →
      ∃ σ' emitted, evalCmd ρ₀.factory ρ₀.store c σ' emitted)
    (h : ∀ ρ₀ σ' emitted, Pre ρ₀ → initEnvWF params (.cmd c) ρ₀ →
      evalCmd ρ₀.factory ρ₀.store c σ' emitted →
        Trace.AssertionsValid P I emitted ∧
          (Trace.Reachable P I emitted → Post { ρ₀ with store := σ' })) :
    Triple (EventLang.imperativeE P CmdT evalCmd initEnvWF) params Pre (.cmd c) Post :=
  TripleWith.of_partial
    (Imperative.Logic.Hoare.cmd evalCmd initEnvWF params c Pre Post h)
    (fun ρ₀ hpre hinit w => by
      obtain ⟨σ', emitted, hstep⟩ := hprog ρ₀ hpre hinit
      refine .step ⟨emitted, _, (.step_cmd hstep : StepStmtE P evalCmd _ _ _)⟩
        (fun _ _ hs => ?_) fun _ _ hs _ => ?_
      · cases (hs : StepStmtE P evalCmd _ _ _) with
        | step_cmd hs' =>
          exact (Trace.AssertionsValid_iff_assertionsHoldIn I _).1
            (h ρ₀ _ _ hpre hinit hs').1 w
      cases (hs : StepStmtE P evalCmd _ _ _)
      exact .terminal _)

/-- Sequencing: two total triples over statement lists compose into one about their
    concatenation, provided the prefix does not escape.  In a fixed world, a run of the
    prefix whose assumptions hold there is reachable, so `Mid` holds where the suffix
    starts. -/
theorem seq_append
    {ss₁ ss₂ : List (Stmt P CmdT)}
    {Pre Mid Post : Env P → Prop}
    (hheadWF : ∀ ρ, blockInitEnvWF bparams (ss₁ ++ ss₂) ρ →
      blockInitEnvWF bparams ss₁ ρ)
    (htailWF : ∀ ρ ρ' tr, blockInitEnvWF bparams (ss₁ ++ ss₂) ρ →
      StepStmtStarE P evalCmd (.stmts ss₁ ρ) tr (.terminal ρ') →
      blockInitEnvWF bparams ss₂ ρ')
    (h₁ : Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams Pre ss₁ Mid)
    (h₂ : Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams Mid ss₂ Post)
    (hSs1NoExit : Block.exitsCoveredByBlocks [] ss₁) :
    Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams Pre (ss₁ ++ ss₂) Post :=
  TripleWith.of_partial
    (Imperative.Logic.Hoare.seq_append evalCmd blockInitEnvWF bparams hheadWF htailWF
      h₁.to_partial h₂.to_partial hSs1NoExit)
    (fun ρ₀ hpre hinit w => by
      obtain ⟨hterm₁, hruns₁⟩ := h₁ ρ₀ hpre (hheadWF ρ₀ hinit)
      refine mustTerminateAndAssertsValid_imperativeBlockE_of_imperativeE
        (initEnvWF := fun _ _ _ => True)
        (mustTerminateAndAssertsValid_stmts_appendE ss₁ ρ₀
          (mustTerminateAndAssertsValid_imperativeE_of_imperativeBlockE (hterm₁ w))
          fun tr ρ₁ hrun hassume => ?_)
      exact mustTerminateAndAssertsValid_imperativeE_of_imperativeBlockE
        ((h₂ ρ₁ (hruns₁ ρ₁ tr (.inl hrun) ⟨w, hassume⟩) (htailWF ρ₀ ρ₁ tr hinit hrun)).1 w))

/-- **Exit.**  An `exit` ends the statement list where it stands, leaving the environment
    unchanged. -/
theorem exit_cons {lbl : String} {md : MetaData P} {ss : List (Stmt P CmdT)}
    {Pre : Env P → Prop} :
    Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams Pre (.exit lbl md :: ss) Pre :=
  TripleWith.of_partial
    (Imperative.Logic.Hoare.exit_cons evalCmd blockInitEnvWF bparams)
    (fun ρ₀ _ _ _ => by
      refine mustTerminateAndAssertsValid_imperativeBlockE_of_imperativeE
        (initEnvWF := fun _ _ _ => True)
        (mustTerminateAndAssertsValid_stmts_consE (mustTerminateAndAssertsValid_seqE
          (.step ⟨[], _, (.step_exit : StepStmtE P evalCmd _ _ _)⟩
            (fun _ _ hs => by cases (hs : StepStmtE P evalCmd _ _ _); exact assertionsHoldIn_nil)
            fun _ _ hs _ => ?_) ?_))
      · cases (hs : StepStmtE P evalCmd _ _ _)
        exact .exiting _ _
      · intro tr ρ₁ hrun _
        cases hrun with
        | step _ _ _ _ _ hstep hrest =>
          cases hstep with
          | step_exit =>
            obtain ⟨hc, _⟩ := stepStmtStarE_from_exiting hrest
            cases hc)

section StructuredRules

variable [HasIdent P] [DecidableEq P.Ident] [HasVarsImp P CmdT]

/-- **Block introduction.**  Wrap a statement list in a block.  `Post` must not mention the
    names the body scopes (`PostWF`); see `Imperative.Logic.Hoare.block` for the other side
    conditions. -/
theorem block (params : InitEnvWFParams P)
    {ss : List (Stmt P CmdT)} {l : String} {md : MetaData P}
    {Pre Post : Env P → Prop}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : Trace P}
      {y : P.Ident},
      evalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (hbodyWF : ∀ ρ, initEnvWF params (.block l ss md) ρ → blockInitEnvWF bparams ss ρ)
    (hbodyDefs : ∀ ρ, initEnvWF params (.block l ss md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) ss true, ρ.store x = none)
    (h : Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams Pre ss Post)
    (hpost_proj : Imperative.Logic.Hoare.PostWF ss Post) :
    Triple (EventLang.imperativeE P CmdT evalCmd initEnvWF) params Pre (.block l ss md) Post :=
  TripleWith.of_partial
    (Imperative.Logic.Hoare.block evalCmd initEnvWF blockInitEnvWF bparams params h_cmd
      hbodyWF hbodyDefs h.to_partial hpost_proj)
    (fun ρ₀ hpre hinit w =>
      .step ⟨[], _, (.step_block : StepStmtE P evalCmd _ _ _)⟩
        (fun _ _ hs => by cases (hs : StepStmtE P evalCmd _ _ _); exact assertionsHoldIn_nil)
        fun _ _ hs _ => by
        cases (hs : StepStmtE P evalCmd _ _ _)
        exact mustTerminateAndAssertsValid_blockE
          (mustTerminateAndAssertsValid_imperativeE_of_imperativeBlockE
            ((h ρ₀ hpre (hbodyWF ρ₀ hinit)).1 w)))

omit [HasIdent P] [DecidableEq P.Ident] [HasVarsImp P CmdT] in
/-- **Singleton list.**  A total triple about `s` becomes one about `[s]`.  `hstmtWF` lowers
    the block condition on `[s]` to the statement condition on `s`. -/
theorem singleton (params : InitEnvWFParams P)
    {s : Stmt P CmdT}
    {Pre Post : Env P → Prop}
    (hstmtWF : ∀ ρ, blockInitEnvWF bparams [s] ρ → initEnvWF params s ρ)
    (h : Triple (EventLang.imperativeE P CmdT evalCmd initEnvWF) params Pre s Post) :
    Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams Pre [s] Post :=
  TripleWith.of_partial
    (Imperative.Logic.Hoare.singleton evalCmd initEnvWF blockInitEnvWF bparams params hstmtWF
      h.to_partial)
    (fun ρ₀ hpre hinit w => mustTerminateAndAssertsValid_imperativeBlockE_of_imperativeE
      (mustTerminateAndAssertsValid_stmts_consE (mustTerminateAndAssertsValid_seqE
        ((h ρ₀ hpre (hstmtWF ρ₀ hinit)).1 w)
        fun _ _ _ _ => mustTerminateAndAssertsValid_stmts_nilE)))

/-- Empty block is skip. -/
theorem skip (params : InitEnvWFParams P)
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : Trace P}
      {y : P.Ident},
      evalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (l : String) (md : MetaData P) (Pre : Env P → Prop) :
    Triple (EventLang.imperativeE P CmdT evalCmd initEnvWF) params Pre (.block l [] md) Pre :=
  block evalCmd initEnvWF (fun _ _ _ => True) params params
    h_cmd (fun _ _ => trivial)
    (fun _ _ x hx => absurd hx (by simp))
    (skip_block evalCmd (fun _ _ _ => True) params Pre)
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil Pre (by simp))

/-- If-then-else rule.  `hcond` says the condition evaluates to a Boolean at every admitted
    `Pre`-environment, so the `ite` can step; see `Imperative.Logic.Hoare.ite` for the other
    side conditions. -/
theorem ite (params : InitEnvWFParams P)
    {cond : P.Expr} {tss ess : List (Stmt P CmdT)} {md : MetaData P}
    {Pre Post : Env P → Prop}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : Trace P}
      {y : P.Ident},
      evalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (hthenWF : ∀ ρ, initEnvWF params (.ite (.det cond) tss ess md) ρ →
      blockInitEnvWF bparams tss ρ)
    (helseWF : ∀ ρ, initEnvWF params (.ite (.det cond) tss ess md) ρ →
      blockInitEnvWF bparams ess ρ)
    (hthenDefs : ∀ ρ, initEnvWF params (.ite (.det cond) tss ess md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) tss true, ρ.store x = none)
    (helseDefs : ∀ ρ, initEnvWF params (.ite (.det cond) tss ess md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) ess true, ρ.store x = none)
    (hcond : ∀ ρ, Pre ρ → initEnvWF params (.ite (.det cond) tss ess md) ρ →
      P.eval ρ.factory ρ.store cond = some (HasBool.ttVal ρ.factory) ∨
        P.eval ρ.factory ρ.store cond = some (HasBool.ffVal ρ.factory))
    (ht : Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams
      (fun ρ => Pre ρ ∧ P.eval ρ.factory ρ.store cond = some (HasBool.ttVal ρ.factory)) tss Post)
    (he : Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams
      (fun ρ => Pre ρ ∧ P.eval ρ.factory ρ.store cond = some (HasBool.ffVal ρ.factory)) ess Post)
    (hthen_proj : Imperative.Logic.Hoare.PostWF tss Post)
    (helse_proj : Imperative.Logic.Hoare.PostWF ess Post) :
    Triple (EventLang.imperativeE P CmdT evalCmd initEnvWF) params Pre
      (.ite (.det cond) tss ess md) Post :=
  TripleWith.of_partial
    (Imperative.Logic.Hoare.ite evalCmd initEnvWF blockInitEnvWF bparams params h_cmd
      hthenWF helseWF hthenDefs helseDefs ht.to_partial he.to_partial hthen_proj helse_proj)
    (fun ρ₀ hpre hinit w => by
      have hprog : ∃ emitted cfg', StepStmtE P evalCmd
          (.stmt (.ite (.det cond) tss ess md) ρ₀) emitted cfg' := by
        rcases hcond ρ₀ hpre hinit with hc | hc
        · exact ⟨[], _, .step_ite_true hc⟩
        · exact ⟨[], _, .step_ite_false hc⟩
      refine .step hprog (fun _ _ hs => by
        cases (hs : StepStmtE P evalCmd _ _ _) <;> exact assertionsHoldIn_nil) fun _ _ hs _ => ?_
      cases (hs : StepStmtE P evalCmd _ _ _) with
      | step_ite_true hc =>
        exact mustTerminateAndAssertsValid_blockE
          (mustTerminateAndAssertsValid_imperativeE_of_imperativeBlockE
            ((ht ρ₀ ⟨hpre, hc⟩ (hthenWF ρ₀ hinit)).1 w))
      | step_ite_false hc =>
        exact mustTerminateAndAssertsValid_blockE
          (mustTerminateAndAssertsValid_imperativeE_of_imperativeBlockE
            ((he ρ₀ ⟨hpre, hc⟩ (helseWF ρ₀ hinit)).1 w)))

/-- **While rule.**  An invariant `Inv` that the body re-establishes while decreasing the
    natural-number measure `M` holds when the loop finishes, and the loop terminates after
    assumes.

    `hbody` is that obligation: from the invariant, a true guard and `M ρ = n`, every
    reachable run of `body` ends in the invariant with `M` below `n`.  In a fixed world, every
    iteration whose assumptions hold there is reachable, so the measure decreases on every
    iteration followed.  `hguard` says the guard evaluates to a Boolean wherever the
    invariant holds, so the loop can step.  `hInv_proj` says the invariant and the bound on
    `M` survive leaving the body's block.  `M` is any measure; the loop's own `decreases`
    clause can supply one, read off the integer it evaluates to.  The other side conditions
    are those of `Imperative.Logic.Hoare.while_rule`. -/
theorem while_rule (params : InitEnvWFParams P)
    {guard : P.Expr} {measure : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P CmdT)} {md : MetaData P}
    {Inv : Env P → Prop} (M : Env P → Nat)
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : Trace P}
      {y : P.Ident},
      evalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (hbodyDefs : ∀ ρ, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) body true, ρ.store x = none)
    (hloopBodyWF : ∀ ρ, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      blockInitEnvWF bparams body ρ)
    (hloopWF : ∀ ρ ρ_inner tr, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      StepStmtStarE P evalCmd (.stmts body ρ) tr (.terminal ρ_inner) →
      initEnvWF params (.loop (.det guard) measure inv body md)
        { ρ_inner with store := projectStore ρ.store ρ_inner.store })
    (hguard : ∀ ρ, Inv ρ → initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      P.eval ρ.factory ρ.store guard = some (HasBool.ttVal ρ.factory) ∨
        P.eval ρ.factory ρ.store guard = some (HasBool.ffVal ρ.factory))
    (hbody : ∀ n, Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams
      (fun ρ => (Inv ρ ∧ P.eval ρ.factory ρ.store guard = some (HasBool.ttVal ρ.factory)) ∧
        M ρ = n) body
      (fun ρ => Inv ρ ∧ M ρ < n))
    (hcov : Block.exitsCoveredByBlocks (P := P) (CmdT := CmdT) [] body)
    (hInv_proj : ∀ n, Imperative.Logic.Hoare.PostWF body (fun ρ => Inv ρ ∧ M ρ < n)) :
    Triple (EventLang.imperativeE P CmdT evalCmd initEnvWF) params Inv
      (.loop (.det guard) measure inv body md)
      (fun ρ => Inv ρ ∧ P.eval ρ.factory ρ.store guard = some (HasBool.ffVal ρ.factory)) := by
  -- The partial body triple without the measure, and the invariant's own projection
  -- condition.
  have hbodyInv : Strata.Logic.Hoare.TripleWith (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) I bparams
      (fun ρ => Inv ρ ∧ P.eval ρ.factory ρ.store guard = some (HasBool.ttVal ρ.factory))
      body Inv := fun ρ₀ hpre hinit =>
    let h := TripleWith.to_partial (hbody (M ρ₀)) ρ₀ ⟨hpre, rfl⟩ hinit
    ⟨h.1, fun ρ' trace hrun hreach => (h.2 ρ' trace hrun hreach).1⟩
  have hInvProj : Imperative.Logic.Hoare.PostWF body Inv := fun ρ hInv =>
    (hInv_proj (M ρ + 1) ρ ⟨hInv, Nat.lt_succ_self _⟩).1
  -- One reachable iteration from an invariant entry with a true guard ends in the invariant,
  -- with a smaller measure, at an entry the loop's gate admits.
  have hiter : ∀ ρ tr ρ₁, Inv ρ → initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      P.eval ρ.factory ρ.store guard = some (HasBool.ttVal ρ.factory) →
      StepStmtStarE P evalCmd (.block .none ρ.store (.stmts body ρ)) tr (.terminal ρ₁) →
      Trace.Reachable P I tr →
      (Inv ρ₁ ∧ M ρ₁ < M ρ) ∧ initEnvWF params (.loop (.det guard) measure inv body md) ρ₁ := by
    intro ρ tr ρ₁ hInv hinit hg hrun hreach
    have hb := hbody (M ρ) ρ ⟨⟨hInv, hg⟩, rfl⟩ (hloopBodyWF ρ hinit)
    obtain ⟨ρ_inner, hdisj, hρ₁⟩ := block_reaches_doneE (.inl hrun)
    have hbrun : StepStmtStarE P evalCmd (.stmts body ρ) tr (.terminal ρ_inner) := by
      rcases hdisj with hterm | ⟨lbl, hexit⟩
      · exact hterm
      · exact absurd hexit (stmts_exitsCoveredByBlocks_noEscapeE evalCmd
          body hcov ρ lbl ρ_inner)
    have hproj : projectStore ρ.store ρ_inner.store
        = dropVars (Block.definedVars (P := P) (C := CmdT) body true) ρ_inner.store :=
      projectStore_eq_dropVarsE h_cmd (hbodyDefs ρ hinit) (.inl hbrun)
    refine ⟨?_, ?_⟩
    · rw [hρ₁, hproj]
      exact hInv_proj (M ρ) ρ_inner (hb.2 ρ_inner tr (.inl hbrun) hreach)
    · rw [hρ₁]
      exact hloopWF ρ ρ_inner tr hinit hbrun
  -- Termination with valid assertions in a fixed world, by induction on a bound on the measure.
  have hloop : ∀ w n ρ, M ρ < n → Inv ρ →
      initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      (EventLang.imperativeE P CmdT evalCmd initEnvWF).MustTerminateAndAssertsValid I w
        (.stmt (.loop (.det guard) measure inv body md) ρ) := by
    intro w n
    induction n with
    | zero => intro _ hM; exact absurd hM (Nat.not_lt_zero _)
    | succ n ih =>
      intro ρ hM hInv hinit
      have hprog : ∃ emitted cfg', StepStmtE P evalCmd
          (.stmt (.loop (.det guard) measure inv body md) ρ) emitted cfg' := by
        rcases hguard ρ hInv hinit with hg | hg
        · exact ⟨[], _, .step_loop_enter hg⟩
        · exact ⟨[], _, .step_loop_exit hg⟩
      refine .step hprog (fun _ _ hs => by
        cases (hs : StepStmtE P evalCmd _ _ _) <;> exact assertionsHoldIn_nil) fun _ _ hs _ => ?_
      cases (hs : StepStmtE P evalCmd _ _ _) with
      | step_loop_exit _ => exact .terminal _
      | step_loop_enter hg =>
        have hb := hbody (M ρ) ρ ⟨⟨hInv, hg⟩, rfl⟩ (hloopBodyWF ρ hinit)
        refine mustTerminateAndAssertsValid_seqE
          (mustTerminateAndAssertsValid_blockE
            (mustTerminateAndAssertsValid_imperativeE_of_imperativeBlockE (hb.1 w)))
          fun tr ρ₁ hrun hassume => ?_
        obtain ⟨⟨hInv₁, hlt⟩, hinit₁⟩ := hiter ρ tr ρ₁ hInv hinit hg hrun ⟨w, hassume⟩
        exact mustTerminateAndAssertsValid_stmts_consE (mustTerminateAndAssertsValid_seqE
          (ih ρ₁ (by omega) hInv₁ hinit₁) fun _ _ _ _ => mustTerminateAndAssertsValid_stmts_nilE)
  exact TripleWith.of_partial
    (Imperative.Logic.Hoare.while_rule evalCmd initEnvWF blockInitEnvWF bparams params h_cmd
      hbodyDefs hloopBodyWF hloopWF hbodyInv hcov hInvProj)
    (fun ρ₀ hInv hinit w => hloop w (M ρ₀ + 1) ρ₀ (Nat.lt_succ_self _) hInv hinit)

end StructuredRules

end StmtRules

end Imperative.Logic.HoareTotal

end HoareTotalRules

end -- public section
