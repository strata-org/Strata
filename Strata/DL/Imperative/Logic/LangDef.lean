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

`Strata.Logic.EventLang P EventT` packages the ingredients a program logic or a
transform specification needs from a language: a statement type, a
configuration type, a one-step relation that emits events, the embeddings of
statements and of terminal/exiting states into configurations, and an
initial-environment well-formedness predicate.  All of it is parametric over the
shared pure-expression system `P` and the event alphabet `EventT`.

Bundling these lets a statement be made once and reused across languages —
`Strata.Logic.Hoare.TripleWith` (in `Strata.DL.Imperative.Logic.HoareTemplate`) and the
`OverapproximatesTraces` family (in `Strata.Transform.Specification`) both
quantify over an arbitrary `Strata.Logic.EventLang`, which is what allows a
result to relate a structured source language to an unstructured CFG target.

The bundle itself lives in the language-agnostic `Strata.Logic` namespace; the
constructors for the Imperative dialect live in `Imperative.Logic`:

- `EventLang.imperativeE` — the structured Imperative event-trace language.
- `EventLang.imperativeBlockE` — its block-body (statement-list) counterpart.
- `EventLang.cfgE` — the deterministic-CFG event-trace language.
- `EventLang.kleeneE` — the canonical event-producing Kleene language, over
  `KleeneStmt`/`KleeneConfig`, stepping by `StepKleeneE P (EvalCmdE P)`; its
  `InitEnvWFParamsTy`/`initEnvWF` are supplied explicitly by the caller.
-/

public section

universe u v

/-! ## Language bundle -/

namespace Strata.Logic

open Imperative

/-- Language interface for event-trace semantics. It exposes one-step
transitions so clients can reason about progress and must-termination;
`EventLang.traceStar` derives chronological traced reachability. Terminal and
exiting configurations have no outgoing steps. Assertion observations are
carried by `EventT` rather than detected from configurations. -/
structure EventLang (P : PureExpr.{u}) (EventT : Type v) where
  /-- Statement type. -/
  StmtT : Type
  /-- Configuration type. -/
  CfgT : Type u
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
  /-- Parameters threaded into `initEnvWF`. The Core languages use a record
      bundling reserved fresh prefixes and a `declaredFuncs` predicate (see
      `Core.Logic.InitEnvWFParams`). -/
  InitEnvWFParamsTy : Type
  /-- Language-specific initial-environment well-formedness. -/
  initEnvWF : InitEnvWFParamsTy → StmtT → Env P → Prop

/-- Reflexive-transitive execution with emitted events in chronological order. -/
abbrev EventLang.traceStar
    {P : PureExpr} {EventT : Type _} (EL : EventLang P EventT) :
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
    (CmdT : Type) {EventT : Type _} (evalCmd : EvalCmdParamE P CmdT EventT)
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
    cases hstep
  exiting_no_step := by
    intro label ρ emitted cfg hstep
    cases hstep
  getEnv := Config.getEnv
  InitEnvWFParamsTy := ParamsTy
  initEnvWF := initEnvWF

/-- Event-trace language for block-level (statement-list) reachability.
`StmtT` is `List (Stmt P CmdT)` and `stmtCfg` embeds via `.stmts`. `wfPkg`
carries the initial-environment well-formedness parameters and predicate, for
example `⟨InitEnvWFParams P, BlockInitEnvWF⟩`. -/
abbrev EventLang.imperativeBlockE (P : PureExpr) [HasBool P] [HasBoolOps P]
    [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] [HasSubstFvar P]
    (CmdT : Type) {EventT : Type _} (evalCmd : EvalCmdParamE P CmdT EventT)
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
    cases hstep
  exiting_no_step := by
    intro label ρ emitted cfg hstep
    cases hstep
  getEnv := Config.getEnv
  InitEnvWFParamsTy := wfPkg.1
  initEnvWF := wfPkg.2

/-- Event-trace language for deterministic CFGs. Active configurations carry the
CFG and every configuration carries its environment, so the one-step relation is
`StepCFGE P evalCmd` without additional captured parameters. -/
abbrev EventLang.cfgE (P : PureExpr) [HasBool P] [HasBoolOps P] [HasVal P]
    [HasFvars P] (CmdT : Type) {EventT : Type _}
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
    cases hstep
  exiting_no_step := by
    intro _ ρ emitted cfg hstep
    cases hstep
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
    [HasInitTypesImp P CmdT] [HasTypedVarsImp P CmdT]
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
  /-- The type annotations on the block's free-variable occurrences agree with the types of
      the values the entry store holds, and with the declared types of the block's own
      definitions.  No value has a sort with a type variable, so no typing meets this field
      when an annotation that mentions one is on a variable no earlier `init` of the block
      defines, and an `init` whose declared type mentions one fails `initTypesInhabited`.
      Either way, a procedure whose body has such an annotation has no entries, and every
      claim over its entries holds vacuously. -/
  fvarTypesOk : ∃ Γ, StoreHasTyping ρ.factory ρ.store Γ ∧ Block.fvarTypesWellAnnotated Γ ss

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

end Logic
end Imperative

end -- public section
