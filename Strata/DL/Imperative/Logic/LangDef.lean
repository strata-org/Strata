/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CFGSemantics
import all Strata.DL.Imperative.CmdSemantics

/-! # The abstract language bundle

`Strata.Logic.Lang P` packages the ingredients a program logic or a transform
specification needs from a language: a statement type, a configuration type, a
multi-step relation, the embeddings of statements and of terminal/exiting states
into configurations, assert detection, and an initial-environment
well-formedness predicate.  All of it is parametric over the shared
pure-expression system `P`.

Bundling these lets a statement be made once and reused across languages —
`Strata.Logic.Hoare.Triple` (in `Strata.DL.Imperative.Logic.HoareTemplate`) and the
`Overapproximates` family (in `Strata.Transform.Specification`) both quantify
over an arbitrary `Strata.Logic.Lang P`, which is what allows a result to relate
a structured source language to an unstructured CFG target.

The bundle itself lives in the language-agnostic `Strata.Logic` namespace; the
constructors for the Imperative dialect live in `Imperative.Logic`:

- `Lang.imperative` — the structured Imperative language, over `Stmt P CmdT`,
  for a given command type and evaluator.
- `Lang.imperativeBlock` — the block-body language, over `List (Stmt P CmdT)`,
  whose default initial-environment condition is `BlockInitEnvWF`.
- `Lang.cfg` — the unstructured control-flow-graph language, over
  `CFG String (DetBlock …)`; the target of `Strata.Transform`'s
  structured-to-unstructured correctness proofs.
-/

public section

/-! ## Language bundle -/

namespace Strata.Logic

open Imperative

/-- Bundles the abstract ingredients for small-step statement semantics,
    parameterized by a shared pure-expression system `P`. -/
structure Lang (P : PureExpr) where
  /-- Statement type. -/
  StmtT : Type
  /-- Configuration type. -/
  CfgT : Type
  /-- Multi-step relation. -/
  star : CfgT → CfgT → Prop
  /-- Embed a single statement and env into a config. -/
  stmtCfg : StmtT → Env P → CfgT
  /-- Terminal configuration. -/
  terminalCfg : Env P → CfgT
  /-- Exiting configuration. -/
  exitingCfg : String → Env P → CfgT
  /-- Assert detection in configurations. -/
  isAtAssert : CfgT → AssertId P → Prop
  /-- Extract env from a configuration. -/
  getEnv : CfgT → Env P
  /-- The type of parameters threaded into `initEnvWF`.
      The Core language uses a record bundling reserved
      "fresh-prefixes" and a `declaredFuncs` predicate (see
      `Core.Logic.InitEnvWFParams`). -/
  InitEnvWFParamsTy : Type
  /-- Initial environment well-formedness: The language-specific well-formedness
      parameters are passed via `InitEnvWFParamsTy`. -/
  initEnvWF : InitEnvWFParamsTy → StmtT → Env P → Prop

end Strata.Logic


/-! ## Imperative instances -/

namespace Imperative

namespace Logic

open Strata.Logic

/-- Build a `Lang` from `Imperative.Stmt`/`Config` with a given command
    type and evaluator.

    `ParamsTy` is the `InitEnvWFParamsTy` for the resulting language; it defaults
    to `Unit` (no parameters), in which case `initEnvWF` defaults to
    `WellFormedSemanticEval` on the initial env's factory.  The Core language
    overrides both. -/
abbrev Lang.imperative (P : PureExpr) [HasBool P] [HasBoolOps P]
    [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] [HasSubstFvar P]
    (CmdT : Type) (evalCmd : EvalCmdParam P CmdT) (extendFactory : ExtendFactory P)
    (isAtAssert : Config P CmdT → AssertId P → Prop)
    (ParamsTy : Type := Unit)
    -- Default: the weakest condition an evaluator-based semantics needs.  A real
    -- language overrides it (see `Core.Logic.Lang.core`).
    (initEnvWF : ParamsTy → Stmt P CmdT → Env P → Prop :=
      fun _ _ ρ => WellFormedSemanticEval (P := P) ρ.factory) :
    Lang P :=
  ⟨Stmt P CmdT, Config P CmdT, StepStmtStar P evalCmd extendFactory,
   .stmt, .terminal, .exiting, isAtAssert, Config.getEnv, ParamsTy, initEnvWF⟩

/-- Block-level initial-environment well-formedness for the imperative-block
language.

TODO: erase this.  What a well-formed initial state is depends on the language
instantiating Imperative, so an Imperative-level default is not the right thing to
have. -/
structure BlockInitEnvWF {P : PureExpr} [HasBool P] [HasBoolOps P]
    [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] [HasSubstFvar P] [HasIdent P]
    {CmdT : Type} [HasVarsImp P CmdT]
    (Q : String → Prop) (ss : List (Stmt P CmdT)) (ρ : Env P) : Prop
    extends WellFormedSemanticEval (P := P) ρ.factory where
  /-- Every variable the block defines starts undefined in `ρ`. -/
  defsUndefined : ∀ x ∈ Block.definedVars ss false, ρ.store x = none
  /-- No name satisfying `Q` is defined in the initial store. -/
  definedVarsNotReserved : Env.varsUndefined (P := P) Q ρ

/-- `Lang` for block-level (statement-list) overapproximation.
    `StmtT` is `List (Stmt P CmdT)` and `stmtCfg` embeds via `.stmts`. -/
abbrev Lang.imperativeBlock {P : PureExpr} [HasFvar P] [HasFvars P]
    [HasBool P] [HasBoolOps P] [HasInt P] [HasIntOps P] [HasSubstFvar P] [HasIdent P]
    {CmdT : Type} [HasVarsImp P CmdT]
    (evalCmd : EvalCmdParam P CmdT) (extendFactory : ExtendFactory P)
    (isAtAssertFn : Config P CmdT → AssertId P → Prop)
    -- Default: `BlockInitEnvWF`, which is slated for removal (see its doc comment).
    -- A real language overrides it (see `Core.Logic.Lang.coreBlock`).
    (wfPkg : (ParamsTy : Type) × (ParamsTy → List (Stmt P CmdT) → Env P → Prop) :=
      ⟨String → Prop, fun Q ss ρ => BlockInitEnvWF Q ss ρ⟩) : Lang P where
  StmtT := List (Stmt P CmdT)
  CfgT := Config P CmdT
  star := StepStmtStar P evalCmd extendFactory
  stmtCfg := .stmts
  terminalCfg := .terminal
  exitingCfg := .exiting
  isAtAssert := isAtAssertFn
  getEnv := Config.getEnv
  InitEnvWFParamsTy := wfPkg.1
  initEnvWF := wfPkg.2

/-- The unstructured CFG language: steps are `StepDetCFGStar` over the factory
carried in the configuration.

`isAtAssert` is `fun _ _ => False`: a CFG block can carry `assert` commands,
so a real `isAtAssert` would detect a config sitting at one. It is left trivial
because the current overapproximation results never consume the target's `isAtAssert`. -/
abbrev Lang.cfg {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasInt P] [HasIntOps P]
    (extendFactory : ExtendFactory P) : Lang P where
  StmtT := CFG String (DetBlock String (Cmd P) P)
  CfgT := P.Factory × (CFG String (DetBlock String (Cmd P) P)) × (CFGConfig String (Cmd P) P)
  star := fun c d => StepDetCFGStar extendFactory c.1 c.2.1 c.2.2 d.2.2
  stmtCfg := fun cfg ρ => (ρ.factory, cfg, .atBlock cfg.entry ρ.store ρ.hasFailure)
  terminalCfg := fun ρ => (ρ.factory, ⟨"", []⟩, .terminal ρ.store ρ.hasFailure)
  exitingCfg := fun lbl ρ => (ρ.factory, ⟨"", []⟩, CFGConfig.exiting lbl ρ.store ρ.hasFailure)
  isAtAssert := fun _ _ => False
  getEnv := fun c => { store := c.2.2.getStore, factory := c.1, hasFailure := c.2.2.getFailure }
  InitEnvWFParamsTy := Unit
  initEnvWF := fun _ _ _ => True -- TODO: add wellformedness conditions for unstructured Core

end Logic
end Imperative

end -- public section
