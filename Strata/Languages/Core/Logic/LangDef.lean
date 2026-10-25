/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.StatementSemantics
public import Strata.Languages.Core.Factory
public import Strata.DL.Imperative.Logic.LangDef
import all Strata.Languages.Core.Factory

/-! # Core language bundles and initial-environment well-formedness

The Core instances of `Strata.Logic.Lang` and `Strata.Logic.EventLang`, together
with the well-formedness predicates that gate them. Split out from
`Strata.Transform.CoreSpecification` so that Core program logics do not depend
on the transform-specification framework, mirroring
`Strata.DL.Imperative.Logic.LangDef` on the Imperative side.

## Contents

- **`InitEnvWFParams`** — reserved fresh prefixes and already-declared function
  names, shared by all Core initial-environment gates.
- **`InitEnvWF`** / **`BlockInitEnvWF`** — gates for a structured statement or
  statement list. They extend `Imperative.WellFormedSemanticEval` with Core
  store, freshness, def-use, and initialization conditions.
- **`CFGInitEnvWF`** — the corresponding gate for an unstructured CFG. Its
  CFG-wide analyses require every external read/update to have an entry slot,
  every CFG-local declaration to start undefined, and every declared init-type
  to be inhabited in the factory. Unlike the structured gates, it has no
  `defUseOk` field: arbitrary control flow requires a path-sensitive definite-
  assignment analysis rather than `Block.defUseWellFormed`'s list order.
- **`Lang.core`** / **`Lang.coreBlock`** — non-event language bundles for Core
  statements and statement lists.
- **`EventLang.core`** / **`EventLang.coreBlock`** / **`EventLang.coreCFG`** —
  event-trace bundles for statements, statement lists, and CFGs, gated by
  `InitEnvWF`, `BlockInitEnvWF`, and `CFGInitEnvWF`, respectively.
-/

public section

namespace Core.Logic

open Core Imperative Strata.Logic Imperative.Logic

/-! ## Core `Lang` bundle -/

/-- Parameters threaded into `Core.Logic.InitEnvWF` (the Core language's
    `Lang.InitEnvWFParamsTy`).

    The `prefixIdents : List String` lists "fresh-prefixes": prefixes of
    identifiers that must NOT appear in the initial environment.  Downstream
    transforms reserve such prefixes so they can introduce fresh names with
    that prefix without colliding with user names.

    The `declaredFuncs : Expression.Ident → Bool` characterizes the set of
    operator/function names already defined in the initial evaluator.  Concrete
    instantiations use this to enforce a `defUseWellFormed` invariant that all
    operator references in the program are pre-declared. -/
structure InitEnvWFParams where
  /-- Reserved "fresh-prefixes" that must not appear in the initial env. -/
  prefixIdents : List String
  /-- Predicate of operator/function names already defined in the evaluator. -/
  declaredFuncs : Expression.Ident → Bool

/-- Store-well-formedness needed for a statement `s` to execute in env `ρ` without
    getting stuck.

    Extends `Imperative.WellFormedSemanticEval` on `fac`, which
    contributes the evaluator-level conditions `bool`/`val`/`var`/`exprCongr`/`int`.
    The remaining fields are Core-specific (store definedness, reserved-prefix
    freshness, `defUse` well-formedness, factory membership). -/
structure InitEnvWF (params : InitEnvWFParams)
    (s : Statement) (ρ : Imperative.Env Expression) : Prop
    extends WellFormedSemanticEval (P := Expression) ρ.factory where
  /-- The store holds only values.  This is what unlocks the store-reading clauses
      of `WellFormedSemanticEval` — `var`, `exprCongr` and `rename` are each
      guarded by it — so without this field the gate supports no reasoning about
      what an expression evaluates to in `ρ`.  It holds of every reachable store,
      and `Core.Specification.ProcEnvWF.storeValues` asserts it at procedure
      entry.  The factory is read from the environment (`ρ.factory`). -/
  storeWellDefined : Imperative.WellFormedStore ρ.store ρ.factory
  readWritesDefined : ∀ n ∈ Stmt.touchedVars s, n ∉ Stmt.definedVars s false →
    (ρ.store n).isSome
  defsUndefined : ∀ n ∈ Stmt.definedVars s false, (ρ.store n).isNone
  /-- Source's `definedVars` don't use any of the reserved prefixes. -/
  definedVarsNotReserved : ∀ n ∈ Stmt.definedVars s false, ∀ p ∈ params.prefixIdents,
    ¬ p.toList.isPrefixOf n.name.toList
  reservedFresh : ∀ n, (ρ.store n).isSome →
    ∀ p ∈ params.prefixIdents, ¬ p.toList.isPrefixOf n.name.toList
  defUseOk : Stmt.defUseWellFormed (fun n => (ρ.store n).isSome) params.declaredFuncs s = Bool.true
  factoryDeclared : ∀ s, Core.isNameInFactory s = Bool.true →
    params.declaredFuncs ⟨s, ()⟩ = Bool.true
  /-- Every init-type the statement declares has a value witness in `ρ`'s factory. -/
  initTypesInhabited : Stmt.InitTypesInhabited (P := Expression) (C := Command) ρ.factory s

/-- Block-level analog of `InitEnvWF`: well-formedness for executing a block of
    statements `bss` from env `ρ`.  The factory is read from `ρ.factory`. -/
structure BlockInitEnvWF (params : InitEnvWFParams)
    (bss : Statements)
    (ρ : Imperative.Env Expression) : Prop
    extends WellFormedSemanticEval (P := Expression) ρ.factory where
  /-- The store holds only values; see `InitEnvWF.storeWellDefined`. -/
  storeWellDefined : Imperative.WellFormedStore ρ.store ρ.factory
  readWritesDefined : ∀ n ∈ Block.touchedVars bss, n ∉ Block.definedVars bss false →
    (ρ.store n).isSome
  defsUndefined : ∀ n ∈ Block.definedVars bss false, (ρ.store n).isNone
  definedVarsNotReserved : ∀ n ∈ Block.definedVars bss false, ∀ p ∈ params.prefixIdents,
    ¬ p.toList.isPrefixOf n.name.toList
  reservedFresh : ∀ n, (ρ.store n).isSome →
    ∀ p ∈ params.prefixIdents, ¬ p.toList.isPrefixOf n.name.toList
  defUseOk : Block.defUseWellFormed (fun n => (ρ.store n).isSome) params.declaredFuncs bss = Bool.true
  factoryDeclared : ∀ s, Core.isNameInFactory s = Bool.true →
    params.declaredFuncs ⟨s, ()⟩ = Bool.true
  /-- Every init-type the block declares has a value witness in `ρ`'s factory. -/
  initTypesInhabited : Block.InitTypesInhabited (P := Expression) (C := Command) ρ.factory bss

/-- Initial-environment well-formedness for a Core CFG. This mirrors
`BlockInitEnvWF`'s store, freshness, factory, and init-type conditions using
CFG-wide analyses. It deliberately omits `BlockInitEnvWF.defUseOk`: that check
relies on structured list order, whereas arbitrary CFG control flow needs a
path-sensitive definite-assignment analysis. -/
structure CFGInitEnvWF (params : InitEnvWFParams)
    (cfg : Core.DetCFG) (ρ : Imperative.Env Expression) : Prop
    extends WellFormedSemanticEval (P := Expression) ρ.factory where
  /-- The initial store contains only values. -/
  storeWellDefined : Imperative.WellFormedStore ρ.store ρ.factory
  /-- External reads and updates have an existing slot at CFG entry. -/
  readWritesDefined : ∀ n ∈
      HasVarsImp.modifiedVars (P := Expression) cfg ++
        HasVarsImp.definedVars (P := Expression) cfg false ++
        HasVarsImp.readVars (P := Expression) cfg,
    n ∉ HasVarsImp.definedVars (P := Expression) cfg false → (ρ.store n).isSome
  /-- CFG-local declarations start without a slot. -/
  defsUndefined : ∀ n ∈ HasVarsImp.definedVars (P := Expression) cfg false,
    (ρ.store n).isNone
  /-- CFG-local declarations avoid prefixes reserved by earlier transforms. -/
  definedVarsNotReserved :
    ∀ n ∈ HasVarsImp.definedVars (P := Expression) cfg false,
    ∀ p ∈ params.prefixIdents,
    ¬ p.toList.isPrefixOf n.name.toList
  /-- Existing variables also avoid reserved prefixes. -/
  reservedFresh : ∀ n, (ρ.store n).isSome →
    ∀ p ∈ params.prefixIdents, ¬ p.toList.isPrefixOf n.name.toList
  /-- Every builtin referenced by the CFG is included among the declared functions. -/
  factoryDeclared : ∀ s, Core.isNameInFactory s = Bool.true →
    params.declaredFuncs ⟨s, ()⟩ = Bool.true
  /-- Every init-type the CFG declares has a value witness in `ρ`'s factory.  The
      CFG analog of `BlockInitEnvWF.initTypesInhabited`; the CFG's blocks contain
      `init … .nondet` commands, so every declared type needs a value witness. -/
  initTypesInhabited : Imperative.DetCFG.InitTypesInhabited
    (P := Expression) (C := Command) ρ.factory cfg

/-- The `Lang Expression` bundle for Core small-step semantics. -/
@[expose] def Lang.core
    (π : String → Option Procedure) :
    Strata.Logic.Lang Expression :=
  Imperative.Logic.Lang.imperative
    Expression Command (EvalCommand π) coreIsAtAssert
    (ParamsTy := InitEnvWFParams) (initEnvWF := InitEnvWF)

/-- The `Lang Expression` bundle for Core small-step semantics over *statement
    lists* (block bodies): the Core counterpart of
    `Imperative.Logic.Lang.imperativeBlock`, with the generic
    `Imperative.Logic.BlockInitEnvWF` replaced by Core's own `BlockInitEnvWF`.

    `StmtT` is `Statements` and `stmtCfg` embeds via `.stmts`, so this is the
    language a block-level overapproximation or Hoare-style block judgement is
    stated over, exactly as `Lang.core` is for single statements. -/
@[expose] def Lang.coreBlock
    (π : String → Option Procedure) :
    Strata.Logic.Lang Expression :=
  Imperative.Logic.Lang.imperativeBlock
    (EvalCommand π) coreIsAtAssert
    (wfPkg := ⟨InitEnvWFParams, BlockInitEnvWF⟩)

/-! ## Core event-trace language bundles -/

/-- Core event language for single statements, gated by `InitEnvWF`. -/
@[expose] def EventLang.core
    (π : String → Option Procedure) :
    Strata.Logic.EventLang Expression (Event Expression) :=
  Imperative.Logic.EventLang.imperativeE
    Expression Command (EvalCommandE π)
    InitEnvWFParams InitEnvWF

/-- Core event language for statement lists, gated by `BlockInitEnvWF`. -/
@[expose] def EventLang.coreBlock
    (π : String → Option Procedure) :
    Strata.Logic.EventLang Expression (Event Expression) :=
  Imperative.Logic.EventLang.imperativeBlockE
    Expression Command (EvalCommandE π)
    ⟨InitEnvWFParams, BlockInitEnvWF⟩

/-- Core event language for deterministic CFG procedure bodies, gated by
`CFGInitEnvWF`. -/
@[expose] def EventLang.coreCFG
    (π : String → Option Procedure) :
    Strata.Logic.EventLang Expression (Event Expression) :=
  Imperative.Logic.EventLang.cfgE
    Expression Command (EvalCommandE π) InitEnvWFParams CFGInitEnvWF

end Core.Logic

end -- public section
