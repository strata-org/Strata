/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CFGSemantics
public import Strata.DL.Imperative.Procedure
public import Strata.DL.Imperative.KleeneStmtSemantics
import all Strata.DL.Imperative.CmdSemantics

/-! # The abstract language bundle

`Strata.Logic.Lang P` packages the ingredients a program logic or a transform
specification needs from a language: a statement type, a configuration type, a
multi-step relation, the embeddings of statements and of terminal/exiting states
into configurations, assert detection, and an initial-environment
well-formedness predicate.  All of it is parametric over the shared
pure-expression system `P`.

Bundling these lets a statement be made once and reused across languages —
`Strata.Logic.Hoare.TripleWith` (in `Strata.DL.Imperative.Logic.HoareTemplate`) and the
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

The event-trace variants (bundled as `EventLang`) live alongside them in the
same namespace:

- `EventLang.imperativeE` — the structured Imperative event-trace language.
- `EventLang.imperativeBlockE` — its block-body (statement-list) counterpart.
- `EventLang.cfgE` — the deterministic-CFG event-trace language.
- `EventLang.kleeneE` — the canonical event-producing Kleene language, over
  `KleeneStmt`/`KleeneConfig`, stepping by `StepKleeneE P (EvalCmdE P)`; its
  `InitEnvWFParamsTy`/`initEnvWF` are supplied explicitly by the caller.
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

/-- Language interface for event-trace semantics. It exposes one-step
transitions so clients can reason about progress and must-termination;
`EventLang.traceStar` derives chronological traced reachability. Terminal and
exiting configurations have no outgoing steps. Unlike `Lang`, assertion
observations are carried by `EventT` rather than detected from configurations. -/
structure EventLang (P : PureExpr) (EventT : Type) where
  /-- Statement type. -/
  StmtT : Type
  /-- Configuration type. -/
  CfgT : Type
  /-- One operational step and the events it emits. -/
  step : CfgT → List EventT → CfgT → Prop
  /-- Embed a statement and initial environment into a configuration. -/
  stmtCfg : StmtT → Env P → CfgT
  /-- Terminal configuration. -/
  terminalCfg : Env P → CfgT
  /-- Exiting configuration. -/
  exitingCfg : String → Env P → CfgT
  /-- Terminal configurations have no outgoing operational steps. -/
  terminal_no_step : ∀ ρ emitted cfg', ¬ step (terminalCfg ρ) emitted cfg'
  /-- Exiting configurations have no outgoing operational steps. -/
  exiting_no_step : ∀ label ρ emitted cfg', ¬ step (exitingCfg label ρ) emitted cfg'
  /-- Extract an environment from a configuration. -/
  getEnv : CfgT → Env P
  /-- Parameters threaded into `initEnvWF`. -/
  InitEnvWFParamsTy : Type
  /-- Language-specific initial-environment well-formedness. -/
  initEnvWF : InitEnvWFParamsTy → StmtT → Env P → Prop

/-- Reflexive-transitive execution with emitted events in chronological order. -/
abbrev EventLang.traceStar
    {P : PureExpr} {EventT : Type} (EL : EventLang P EventT) :
    EL.CfgT → List EventT → EL.CfgT → Prop :=
  ReflTransTrace EL.step

end Strata.Logic


/-! ## Imperative instances -/

namespace Imperative

namespace Logic

open Strata.Logic

/-- Build an event-trace language from `Imperative.Stmt`/`Config` with a given
command event evaluator. The resulting bundle exposes `StepStmtE` as its
one-step relation. -/
abbrev EventLang.imperativeE (P : PureExpr) [HasBool P] [HasBoolOps P]
    [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] [HasSubstFvar P]
    (CmdT : Type) {EventT : Type} (evalCmd : EvalCmdParamE P CmdT EventT)
    (ParamsTy : Type)
    (initEnvWF : ParamsTy → Stmt P CmdT → Env P → Prop) :
    EventLang P EventT where
  StmtT := Stmt P CmdT
  CfgT := Config P CmdT
  step := StepStmtE P evalCmd
  stmtCfg := .stmt
  terminalCfg := .terminal
  exitingCfg := .exiting
  terminal_no_step := by
    intro ρ emitted cfg hstep
    cases hstep with
    | step_admin hadmin => cases hadmin
  exiting_no_step := by
    intro label ρ emitted cfg hstep
    cases hstep with
    | step_admin hadmin => cases hadmin
  getEnv := Config.getEnv
  InitEnvWFParamsTy := ParamsTy
  initEnvWF := initEnvWF

/-- Event-trace language for block-level (statement-list) reachability.
`StmtT` is `List (Stmt P CmdT)` and `stmtCfg` embeds via `.stmts`. The
`EventLang` counterpart of `Lang.imperativeBlock`; `wfPkg` carries the
initial-environment well-formedness with no default (a real language supplies
it), so no `isAtAssert` field is needed. -/
abbrev EventLang.imperativeBlockE (P : PureExpr) [HasBool P] [HasBoolOps P]
    [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] [HasSubstFvar P]
    (CmdT : Type) {EventT : Type} (evalCmd : EvalCmdParamE P CmdT EventT)
    (wfPkg : (ParamsTy : Type) × (ParamsTy → List (Stmt P CmdT) → Env P → Prop)) :
    EventLang P EventT where
  StmtT := List (Stmt P CmdT)
  CfgT := Config P CmdT
  step := StepStmtE P evalCmd
  stmtCfg := .stmts
  terminalCfg := .terminal
  exitingCfg := .exiting
  terminal_no_step := by
    intro ρ emitted cfg hstep
    cases hstep with
    | step_admin hadmin => cases hadmin
  exiting_no_step := by
    intro label ρ emitted cfg hstep
    cases hstep with
    | step_admin hadmin => cases hadmin
  getEnv := Config.getEnv
  InitEnvWFParamsTy := wfPkg.1
  initEnvWF := wfPkg.2

/-- Event-trace language for deterministic CFGs. Active configurations carry the
CFG and every configuration carries its environment, so the one-step relation is
`StepCFGE P evalCmd` without additional captured parameters. -/
abbrev EventLang.cfgE (P : PureExpr) [HasBool P] [HasBoolOps P] [HasVal P]
    [HasFvars P] (CmdT : Type) {EventT : Type}
    (evalCmd : EvalCmdParamE P CmdT EventT) (ParamsTy : Type)
    (initEnvWF : ParamsTy → CFG String (DetBlock String CmdT P) → Env P → Prop) :
    EventLang P EventT where
  StmtT := CFG String (DetBlock String CmdT P)
  CfgT := CFGConfig String CmdT P
  step := StepCFGE P evalCmd
  stmtCfg := fun cfg ρ => .atBlock cfg cfg.entry ρ
  terminalCfg := .terminal
  exitingCfg := fun _ => .terminal
  terminal_no_step := by
    intro ρ emitted cfg hstep
    cases hstep with
    | step_admin hadmin => cases hadmin
  exiting_no_step := by
    intro _ ρ emitted cfg hstep
    cases hstep with
    | step_admin hadmin => cases hadmin
  getEnv := CFGConfig.getEnv
  InitEnvWFParamsTy := ParamsTy
  initEnvWF := initEnvWF

/-- The canonical event-producing Kleene event-trace language, over
`KleeneStmt P (Cmd P)` with the base command event evaluator `EvalCmdE P`.  Its
one-step relation is the event-producing Kleene step `StepKleeneE P (EvalCmdE P)`.
Exiting configurations are represented by terminal configurations, as
`KleeneConfig` has no exiting form.

`ParamsTy` is the `InitEnvWFParamsTy` of the resulting language and
`initEnvWF` its initial-environment well-formedness predicate; both are supplied
explicitly by the caller. -/
abbrev EventLang.kleeneE (P : PureExpr) [HasBool P] [HasBoolOps P]
    [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] [HasSubstFvar P]
    (ParamsTy : Type)
    (initEnvWF : ParamsTy → KleeneStmt P (Cmd P) → Env P → Prop) :
    EventLang P (Event P) where
  StmtT := KleeneStmt P (Cmd P)
  CfgT := KleeneConfig P (Cmd P)
  step := StepKleeneE P (EvalCmdE P)
  stmtCfg := .stmt
  terminalCfg := .terminal
  exitingCfg := fun _ ρ => .terminal ρ
  terminal_no_step := by
    intro ρ emitted cfg h
    cases h
  exiting_no_step := by
    intro label ρ emitted cfg h
    cases h
  getEnv := KleeneConfig.getEnv
  InitEnvWFParamsTy := ParamsTy
  initEnvWF := initEnvWF

/-- Build a `Lang` from `Imperative.Stmt`/`Config` with a given command
    type and evaluator.

    `ParamsTy` is the `InitEnvWFParamsTy` for the resulting language; it defaults
    to `Unit` (no parameters), in which case `initEnvWF` defaults to
    `WellFormedSemanticEval` on the initial env's factory.  The Core language
    overrides both. -/
abbrev Lang.imperative (P : PureExpr) [HasBool P] [HasBoolOps P]
    [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] [HasSubstFvar P]
    (CmdT : Type) (evalCmd : EvalCmdParam P CmdT)
    (isAtAssert : Config P CmdT → AssertId P → Prop)
    (ParamsTy : Type := Unit)
    -- Default: the weakest condition an evaluator-based semantics needs.  A real
    -- language overrides it (see `Core.Logic.Lang.core`).  The factory is read
    -- from the initial environment (`ρ.factory`).
    (initEnvWF : ParamsTy → Stmt P CmdT → Env P → Prop :=
      fun _ _ ρ => WellFormedSemanticEval (P := P) ρ.factory) :
    Lang P :=
  ⟨Stmt P CmdT, Config P CmdT, StepStmtStar P evalCmd,
   .stmt, .terminal, .exiting, isAtAssert, Config.getEnv, ParamsTy, initEnvWF⟩

/-- Initial-environment parameters shared by imperative language instances.
Reserved prefixes identify names that must be fresh, while `declaredFuncs`
records evaluator operators available at entry. -/
structure InitEnvWFParams (P : PureExpr) where
  prefixIdents : List String
  declaredFuncs : P.Ident → Bool

/-- Add reserved prefixes while preserving the declared-function predicate. -/
@[expose] def InitEnvWFParams.extend
    (base : InitEnvWFParams P) (prefixes : List String) : InitEnvWFParams P where
  prefixIdents := prefixes ++ base.prefixIdents
  declaredFuncs := base.declaredFuncs

/-- Default generic parameters reserve no prefixes and admit every operator. -/
def InitEnvWFParams.default (P : PureExpr) : InitEnvWFParams P where
  prefixIdents := []
  declaredFuncs := fun _ => true

/-- Block-level initial-environment well-formedness for the imperative-block
language. -/
structure BlockInitEnvWF {P : PureExpr} [HasBool P] [HasBoolOps P]
    [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] [HasSubstFvar P]
    [HasIdent P] [HasOps P] [DecidableEq P.Ident]
    {CmdT : Type} [HasVarsImp P CmdT] [HasOpsImp P CmdT]
    [HasInitTypesImp P CmdT]
    (params : InitEnvWFParams P)
    (ss : List (Stmt P CmdT)) (ρ : Env P) : Prop
    extends WellFormedSemanticEval (P := P) ρ.factory where
  /-- Every binding in the initial store is a semantic value. -/
  storeWellDefined : WellFormedStore ρ.store ρ.factory
  /-- Reads and updates not introduced by this block are defined at entry. -/
  readWritesDefined : ∀ x ∈ Block.touchedVars ss,
    x ∉ Block.definedVars ss false → (ρ.store x).isSome
  /-- Every variable the block defines starts undefined in `ρ`. -/
  defsUndefined : ∀ x ∈ Block.definedVars ss false,
    (ρ.store x).isNone = true
  /-- Source definitions represented by strings avoid every reserved prefix.
  The equality witness keeps this generic over identifier types that do not
  expose a string projection. -/
  definedVarsNotReserved : ∀ x ∈ Block.definedVars ss false,
    ∀ name, x = HasIdent.ident (P := P) name →
    ∀ p ∈ params.prefixIdents, ¬ p.toList.isPrefixOf name.toList
  /-- Existing string-represented bindings avoid every reserved prefix. -/
  reservedFresh : ∀ x, (ρ.store x).isSome →
    ∀ name, x = HasIdent.ident (P := P) name →
    ∀ p ∈ params.prefixIdents, ¬ p.toList.isPrefixOf name.toList
  /-- Reads and updates occur only after definition, and referenced operators
  are included in `declaredFuncs`. -/
  defUseOk : Block.defUseWellFormed
    (fun x => (ρ.store x).isSome) params.declaredFuncs ss = true
  /-- Every init-type the block declares has a value witness in the factory. -/
  initTypesInhabited : Block.InitTypesInhabited (P := P) (C := CmdT) ρ.factory ss

/-- Initial-environment well-formedness for a deterministic CFG. Unlike the
structured block gate, this gate has no list-ordered `defUseOk`; arbitrary CFG
control flow requires a path-sensitive definite-assignment analysis. -/
structure CFGInitEnvWF {P : PureExpr} [HasBool P] [HasBoolOps P]
    [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] [HasSubstFvar P]
    [HasIdent P] [HasOps P] [DecidableEq P.Ident]
    {CmdT : Type} [HasVarsImp P CmdT] [HasOpsImp P CmdT]
    [HasInitTypesImp P CmdT]
    (params : InitEnvWFParams P)
    (cfg : CFG String (DetBlock String CmdT P)) (ρ : Env P) : Prop
    extends WellFormedSemanticEval (P := P) ρ.factory where
  storeWellDefined : WellFormedStore ρ.store ρ.factory
  readWritesDefined : ∀ ident ∈
      HasVarsImp.modifiedVars (P := P) cfg ++
        HasVarsImp.definedVars (P := P) cfg false ++
        HasVarsImp.readVars (P := P) cfg,
    ident ∉ HasVarsImp.definedVars (P := P) cfg false →
      (ρ.store ident).isSome
  defsUndefined : ∀ ident ∈ HasVarsImp.definedVars (P := P) cfg false,
    (ρ.store ident).isNone
  definedVarsNotReserved :
    ∀ ident ∈ HasVarsImp.definedVars (P := P) cfg false,
      ∀ name, ident = HasIdent.ident (P := P) name →
      ∀ pfx ∈ params.prefixIdents,
        ¬ pfx.toList.isPrefixOf name.toList
  reservedFresh : ∀ ident, (ρ.store ident).isSome →
    ∀ name, ident = HasIdent.ident (P := P) name →
    ∀ pfx ∈ params.prefixIdents,
      ¬ pfx.toList.isPrefixOf name.toList
  initTypesInhabited : DetCFG.InitTypesInhabited
    (P := P) (C := CmdT) ρ.factory cfg

/-- `Lang` for block-level (statement-list) overapproximation.
    `StmtT` is `List (Stmt P CmdT)` and `stmtCfg` embeds via `.stmts`. -/
abbrev Lang.imperativeBlock {P : PureExpr} [HasFvar P] [HasFvars P]
    [HasBool P] [HasBoolOps P] [HasInt P] [HasIntOps P] [HasSubstFvar P]
    [HasIdent P] [HasOps P] [DecidableEq P.Ident]
    {CmdT : Type} [HasVarsImp P CmdT] [HasOpsImp P CmdT]
    [HasInitTypesImp P CmdT]
    (evalCmd : EvalCmdParam P CmdT)
    (isAtAssertFn : Config P CmdT → AssertId P → Prop)
    -- Default: the shared `BlockInitEnvWF` gate; Core extends it in
    -- `Core.Logic.Lang.coreBlock`.  The factory is read from the initial
    -- environment (`ρ.factory`).
    (wfPkg : (ParamsTy : Type) ×
      (ParamsTy → List (Stmt P CmdT) → Env P → Prop) :=
      ⟨InitEnvWFParams P, BlockInitEnvWF⟩) : Lang P where
  StmtT := List (Stmt P CmdT)
  CfgT := Config P CmdT
  star := StepStmtStar P evalCmd
  stmtCfg := .stmts
  terminalCfg := .terminal
  exitingCfg := .exiting
  isAtAssert := isAtAssertFn
  getEnv := Config.getEnv
  InitEnvWFParamsTy := wfPkg.1
  initEnvWF := wfPkg.2

/-- The unstructured CFG language. Active configurations carry the CFG program;
all configurations carry their execution environment. -/
abbrev Lang.cfg {P : PureExpr} [HasBool P] [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasInt P] [HasIntOps P] [HasSubstFvar P]
    : Lang P where
  StmtT := CFG String (DetBlock String (Cmd P) P)
  CfgT := CFGConfig String (Cmd P) P
  star := StepDetCFGStar
  stmtCfg := fun cfg ρ => .atBlock cfg cfg.entry ρ
  terminalCfg := .terminal
  exitingCfg := fun _ => .terminal
  isAtAssert := fun _ _ => False
  getEnv := CFGConfig.getEnv
  InitEnvWFParamsTy := Unit
  initEnvWF := fun _ _ ρ => WellFormedSemanticEval (P := P) ρ.factory

end Logic
end Imperative

end -- public section
