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
Configuration for small-step semantics. A configuration is one of:

- `.atBlock t σ f`  — about to fetch the block at label `t`.
- `.inBlock t cs tr σ f` — partway through a block: `cs` are the residual
  commands that still need to execute, `tr` is the block's transfer.
- `.terminal σ f`   — execution has finished normally.
- `.exiting l σ f`  — execution escaped via an uncaught exit to label `l`.

The configuration is parameterised by the command type `CmdT` so that the
mid-block residual command list and the block's transfer have the right
type at the level of the configuration.
-/
inductive CFGConfig (l CmdT : Type) (P : PureExpr) : Type where
  /-- Fetch-and-start: about to look up label `l` in the CFG. -/
  | atBlock  : l → SemanticStore P → Bool → CFGConfig l CmdT P
  /-- Mid-block: residual commands `cs` and the block's transfer `tr`
      survive, with the running store and failure flag. -/
  | inBlock  : l → List CmdT → DetTransferCmd l P → SemanticStore P → Bool
              → CFGConfig l CmdT P
  /-- Halt. -/
  | terminal : SemanticStore P → Bool → CFGConfig l CmdT P
  /-- Escape via an uncaught structured exit to label `l`. A top-level
      outcome, like `terminal`, but tagged with the escaping label so that
      the outcome kind (normal halt vs. escaping exit) is observable. -/
  | exiting  : l → SemanticStore P → Bool → CFGConfig l CmdT P

/-- Project the running store from a `CFGConfig`. -/
@[expose] def CFGConfig.getStore {l CmdT : Type} {P : PureExpr} :
    CFGConfig l CmdT P → SemanticStore P
| .atBlock _ σ _       => σ
| .inBlock _ _ _ σ _   => σ
| .terminal σ _        => σ
| .exiting _ σ _       => σ

/-- Project the failure flag from a `CFGConfig`. -/
@[expose] def CFGConfig.getFailure {l CmdT : Type} {P : PureExpr} :
    CFGConfig l CmdT P → Bool
| .atBlock _ _ f       => f
| .inBlock _ _ _ _ f   => f
| .terminal _ f        => f
| .exiting _ _ f       => f

/--
Per-command small-step operational semantics for a deterministic CFG.

There are five constructors:

* `fetch`: from `.atBlock t`, look up the block at label `t` and unfold to
  `.inBlock t b.cmds b.transfer`.
* `step_cmd`: from `.inBlock t (c :: cs) tr`, evaluate the head command via
  `EvalCmd` and step to `.inBlock t cs tr`.
* `goto_true` / `goto_false`: from `.inBlock t [] (.condGoto c tlbl elbl _)`,
  evaluate the condition and jump to `.atBlock tlbl` or `.atBlock elbl`.
* `finish`: from `.inBlock t [] (.finish _)`, halt at `.terminal`.

Note: the unconditional `.goto k` transfer is the special case
`condGoto HasBool.tt k k _` (definitionally equal); we therefore do not need
a separate `goto` constructor here — proofs rewrite `.goto k` as
`.condGoto HasBool.tt k k _` and use `goto_true`.

The expression evaluator is `P.eval` (part of the `PureExpr` bundle), applied
against a single factory `fac : P.Factory` that indexes the whole relation.
Fixing one factory across the relation makes the conditional transfer rules
deterministic: for a given `condGoto`, `fac` pins the condition's value, so at
most one of `goto_true` / `goto_false` applies.
-/
inductive StepCFG
    {l CmdT : Type} [BEq l] (P : PureExpr)
    (EvalCmd   : EvalCmdParam P CmdT)
    (fac : P.Factory)
    [HasBool P] [HasBoolOps P] [HasVal P] [HasFvars P] :
    CFG l (DetBlock l CmdT P) → CFGConfig l CmdT P → CFGConfig l CmdT P → Prop where
  /-- Fetch: turn `.atBlock t` into `.inBlock t b.cmds b.transfer`. -/
  | fetch :
      List.lookup t cfg.blocks = .some b →
      StepCFG P EvalCmd fac cfg
        (.atBlock t σ f)
        (.inBlock t b.cmds b.transfer σ f)
  /-- Run one command from the residual list. -/
  | step_cmd :
      EvalCmd fac σ c σ' f' →
      StepCFG P EvalCmd fac cfg
        (.inBlock t (c :: cs) tr σ f)
        (.inBlock t cs tr σ' (f || f'))
  /-- Empty residual + true branch: jump to `.atBlock` of the true label. -/
  | goto_true :
      P.eval fac σ c = .some HasBool.tt →
      WellFormedSemanticEvalBool (P := P) fac →
      WellFormedSemanticEvalExprCongr (P := P) fac →
      StepCFG P EvalCmd fac cfg
        (.inBlock t [] (.condGoto c tlbl elbl md) σ f)
        (.atBlock tlbl σ f)
  /-- Empty residual + false branch: jump to `.atBlock` of the false label. -/
  | goto_false :
      P.eval fac σ c = .some HasBool.ff →
      WellFormedSemanticEvalBool (P := P) fac →
      WellFormedSemanticEvalExprCongr (P := P) fac →
      StepCFG P EvalCmd fac cfg
        (.inBlock t [] (.condGoto c tlbl elbl md) σ f)
        (.atBlock elbl σ f)
  /-- Empty residual + `finish`: halt at `.terminal`. -/
  | finish :
      StepCFG P EvalCmd fac cfg
        (.inBlock t [] (.finish md) σ f)
        (.terminal σ f)

/--
Operational semantics to evaluate an arbitrary number of CFG steps in
sequence — the reflexive, transitive closure of `StepCFG`.
-/
@[expose]
def StepCFGStar
    {l CmdT : Type}
    [BEq l]
    (P : PureExpr)
    (EvalCmd : EvalCmdParam P CmdT)
    (fac : P.Factory)
    [HasBool P] [HasBoolOps P] [HasVal P] [HasFvars P]
    (cfg : CFG l (DetBlock l CmdT P)) :
    CFGConfig l CmdT P → CFGConfig l CmdT P → Prop :=
  ReflTrans (StepCFG P EvalCmd fac cfg)

/-- `StepCFG` with events.  Command steps use `EvalCmdParamE` and emit the
command's events; the control-flow steps (fetch, conditional jump, finish) are the
`StepCFG` rules, reused through `noCommandEvalE` and emitting no events.  The
config's `Bool` flag is carried unchanged: a failing assert is an event, not a flag
change.  Since `StepCFG` over `noCommandEvalE` has no command step, the two
constructors never derive the same transition. -/
inductive StepCFGE
    {l CmdT EventT : Type} [BEq l] (P : PureExpr)
    (EvalCmd   : EvalCmdParamE P CmdT EventT)
    (fac : P.Factory)
    [HasBool P] [HasBoolOps P] [HasVal P] [HasFvars P] :
    CFG l (DetBlock l CmdT P) → CFGConfig l CmdT P → List EventT → CFGConfig l CmdT P → Prop where
  /-- Run one command from the residual list. -/
  | step_cmd :
      EvalCmd fac σ c σ' emitted →
      StepCFGE P EvalCmd fac cfg
        (.inBlock t (c :: cs) tr σ f) emitted
        (.inBlock t cs tr σ' f)
  /-- Reuse a command-free control-flow `StepCFG` step; it emits no events. -/
  | step_admin :
      StepCFG P (noCommandEvalE P CmdT) fac cfg c c' →
      StepCFGE P EvalCmd fac cfg c [] c'

/--
Event-trace multi-step execution for a deterministic CFG — the reflexive,
transitive closure of `StepCFGE`, concatenating each step's event list
chronologically.
-/
@[expose]
def StepCFGStarE
    {l CmdT EventT : Type}
    [BEq l]
    (P : PureExpr)
    (EvalCmd : EvalCmdParamE P CmdT EventT)
    (fac : P.Factory)
    [HasBool P] [HasBoolOps P] [HasVal P] [HasFvars P]
    (cfg : CFG l (DetBlock l CmdT P)) :
    CFGConfig l CmdT P → List EventT → CFGConfig l CmdT P → Prop :=
  ReflTransTrace (StepCFGE P EvalCmd fac cfg)

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

abbrev StepDetCFGStar {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    (fac : P.Factory)
    (cfg : CFG String (DetBlock String (Cmd P) P)) :=
  StepCFGStar P (EvalCmd P) fac cfg
