/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.BasicBlock
public import Strata.DL.Imperative.StmtSemantics

public section

---------------------------------------------------------------------

namespace Imperative

/-! ## Small-Step operational semantics for control-flow graphs

This module defines small-step operational semantics for the Imperative
dialect's control-flow graph representation, in a *per-command* style:
each step either fetches a block at a label, runs a single command from
the residual list, or fires the block transfer.
-/

/--
Configuration for small-step CFG semantics. Every configuration carries:

* the CFG program `cfg`, so the step relation need not capture a
  constructor-local program as a parameter; and
* the execution environment `ρ`, so the store, expression factory,
  and cumulative failure flag travel together exactly as in structured
  statement configurations.

The control component is one of:

- `.atBlock cfg t ρ` — about to fetch the block at label `t`;
- `.inBlock cfg t cs tr ρ` — partway through a block, with residual commands
  `cs` and transfer `tr`;
- `.terminal ρ` — execution has finished.

Active configurations carry `cfg` because it is needed for future fetches.
Terminal configurations cannot step, so retaining a program there would be
unobservable and would prevent the generic `Lang.terminalCfg` operation from
constructing exact outcomes.
-/
inductive CFGConfig (l CmdT : Type) (P : PureExpr) : Type where
  | atBlock : CFG l (DetBlock l CmdT P) → l → Env P → CFGConfig l CmdT P
  | inBlock : CFG l (DetBlock l CmdT P) → l → List CmdT → DetTransferCmd l P → Env P →
      CFGConfig l CmdT P
  | terminal : Env P → CFGConfig l CmdT P

/-- Project the execution environment from a `CFGConfig`. -/
@[expose] def CFGConfig.getEnv {l CmdT : Type} {P : PureExpr} :
    CFGConfig l CmdT P → Env P
  | .atBlock _ _ ρ => ρ
  | .inBlock _ _ _ _ ρ => ρ
  | .terminal ρ => ρ

/-- Project the running store from a `CFGConfig`. -/
@[expose] def CFGConfig.getStore {l CmdT : Type} {P : PureExpr}
    (c : CFGConfig l CmdT P) : SemanticStore P := c.getEnv.store

/-- Project the failure flag from a `CFGConfig`. -/
@[expose] def CFGConfig.getFailure {l CmdT : Type} {P : PureExpr}
    (c : CFGConfig l CmdT P) : Bool := c.getEnv.hasFailure

/--
Per-command small-step operational semantics for a deterministic CFG.

The source configuration supplies both the CFG program and execution environment.
Every constructor preserves the program and factory; command steps update only the
store and cumulative failure flag, while control-flow steps update only control.
Consequently `StepCFG` itself captures neither a factory nor a CFG program.
An unconditional `.goto k` remains the definitional special case
`.condGoto HasBool.tt k k _` and is handled by `goto_true`.
-/
inductive StepCFG
    {l CmdT : Type} [BEq l] (P : PureExpr)
    (EvalCmd : EvalCmdParam P CmdT)
    [HasBool P] [HasBoolOps P] [HasVal P] [HasFvars P] :
    CFGConfig l CmdT P → CFGConfig l CmdT P → Prop where
  /-- Fetch: turn `.atBlock t` into `.inBlock t b.cmds b.transfer`. -/
  | fetch :
      List.lookup t cfg.blocks = .some b →
      StepCFG P EvalCmd
        (.atBlock cfg t ρ)
        (.inBlock cfg t b.cmds b.transfer ρ)
  /-- Run one command from the residual list. -/
  | step_cmd :
      EvalCmd ρ.factory ρ.store c σ' f' →
      StepCFG P EvalCmd
        (.inBlock cfg t (c :: cs) tr ρ)
        (.inBlock cfg t cs tr
          { ρ with store := σ', hasFailure := ρ.hasFailure || f' })
  /-- Empty residual + true branch: jump to the true label. -/
  | goto_true :
      P.eval ρ.factory ρ.store c = .some HasBool.tt →
      StepCFG P EvalCmd
        (.inBlock cfg t [] (.condGoto c tlbl elbl md) ρ)
        (.atBlock cfg tlbl ρ)
  /-- Empty residual + false branch: jump to the false label. -/
  | goto_false :
      P.eval ρ.factory ρ.store c = .some HasBool.ff →
      StepCFG P EvalCmd
        (.inBlock cfg t [] (.condGoto c tlbl elbl md) ρ)
        (.atBlock cfg elbl ρ)
  /-- Empty residual + `finish`: halt at `.terminal`. -/
  | finish :
      StepCFG P EvalCmd
        (.inBlock cfg t [] (.finish md) ρ)
        (.terminal ρ)

/-- Reflexive-transitive execution of `StepCFG`. -/
@[expose] def StepCFGStar
    {l CmdT : Type} [BEq l]
    (P : PureExpr) (EvalCmd : EvalCmdParam P CmdT)
    [HasBool P] [HasBoolOps P] [HasVal P] [HasFvars P] :
    CFGConfig l CmdT P → CFGConfig l CmdT P → Prop :=
  ReflTrans (StepCFG P EvalCmd)

/-- Event-labeled CFG step. Command steps emit their command trace;
administrative steps reuse command-free `StepCFG` and emit no events. -/
inductive StepCFGE
    {l CmdT EventT : Type} [BEq l] (P : PureExpr)
    (EvalCmd : EvalCmdParamE P CmdT EventT)
    [HasBool P] [HasBoolOps P] [HasVal P] [HasFvars P] :
    CFGConfig l CmdT P → List EventT → CFGConfig l CmdT P → Prop where
  /-- Run one command from the residual list. -/
  | step_cmd :
      EvalCmd ρ.factory ρ.store c σ' emitted →
      StepCFGE P EvalCmd
        (.inBlock cfg t (c :: cs) tr ρ) emitted
        (.inBlock cfg t cs tr { ρ with store := σ' })
  /-- Reuse a command-free control-flow `StepCFG` step; it emits no events. -/
  | step_admin :
      StepCFG P (noCommandEvalE P CmdT) c c' →
      StepCFGE P EvalCmd c [] c'

/-- Reflexive-transitive event-trace execution of `StepCFGE`. -/
@[expose] def StepCFGStarE
    {l CmdT EventT : Type} [BEq l]
    (P : PureExpr) (EvalCmd : EvalCmdParamE P CmdT EventT)
    [HasBool P] [HasBoolOps P] [HasVal P] [HasFvars P] :
    CFGConfig l CmdT P → List EventT → CFGConfig l CmdT P → Prop :=
  ReflTransTrace (StepCFGE P EvalCmd)

/-! ## Bridge: EvalCmds and connector to per-command StepCFG

`EvalCmds` is a structured-side helper inductive used by every simulation
lemma to package up the structured evaluation of an accumulated command list.
We bridge it into the per-command `StepCFG` by lifting each
`eval_cmds_some` step into one `StepCFG.step_cmd` step inside `.inBlock`. -/

inductive EvalCmds
    {CmdT : Type}
    (P : PureExpr)
    (EvalCmdR : EvalCmdParam P CmdT) :
    P.Factory → SemanticStore P → List CmdT → SemanticStore P → Bool → Prop where
  | eval_cmds_none :
    EvalCmds P EvalCmdR δ σ [] σ false
  | eval_cmds_some :
    EvalCmdR δ σ c σ' failed →
    EvalCmds P EvalCmdR δ σ' cs σ'' failed' →
    EvalCmds P EvalCmdR δ σ (c :: cs) σ'' (failed || failed')

abbrev StepDetCFGStar {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] :
    CFGConfig String (Cmd P) P → CFGConfig String (Cmd P) P → Prop :=
  StepCFGStar P (EvalCmd P)
