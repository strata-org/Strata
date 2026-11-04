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

The Core instances of `Strata.Logic.EventLang`, together
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
- **`EventLang.core`** / **`EventLang.coreBlock`** / **`EventLang.coreCFG`** —
  event-trace bundles for statements, statement lists, and CFGs, gated by
  `InitEnvWF`, `BlockInitEnvWF`, and `CFGInitEnvWF`, respectively.
-/

public section

namespace Core.Logic

open Core Imperative Strata.Logic Imperative.Logic

/-! ## Core initial-environment well-formedness -/

/-- Core specialization of the shared imperative initial-environment
parameters. -/
abbrev InitEnvWFParams := Imperative.Logic.InitEnvWFParams Expression

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
  /-- The type annotations on the statement's free-variable occurrences agree with the types
      of the values the entry store holds, and with the declared types of the statement's own
      definitions.  No value has a sort with a type variable, so no typing meets this field
      when an annotation that mentions one is on a variable no earlier `init` of the
      statement defines, and an `init` whose declared type mentions one fails
      `initTypesInhabited`. -/
  fvarTypesOk : ∃ Γ, StoreHasTyping ρ.factory ρ.store Γ ∧ Stmt.fvarTypesWellAnnotated Γ s

/-- Block-level analog of `InitEnvWF`: well-formedness for executing a block of
    statements `bss` from env `ρ`.  The factory is read from `ρ.factory`. -/
structure BlockInitEnvWF (params : InitEnvWFParams)
    (bss : Statements)
    (ρ : Imperative.Env Expression) : Prop
    extends Imperative.Logic.BlockInitEnvWF
      (P := Expression) (CmdT := Command) params bss ρ where
  factoryDeclared : ∀ s, Core.isNameInFactory s = Bool.true →
    params.declaredFuncs ⟨s, ()⟩ = Bool.true

/-- Initial-environment well-formedness for a Core CFG. This mirrors
`BlockInitEnvWF`'s store, freshness, factory, and init-type conditions using
CFG-wide analyses. It deliberately omits `BlockInitEnvWF.defUseOk`: that check
relies on structured list order, whereas arbitrary CFG control flow needs a
path-sensitive definite-assignment analysis. -/
structure CFGInitEnvWF (params : InitEnvWFParams)
    (cfg : Core.DetCFG) (ρ : Imperative.Env Expression) : Prop
    extends Imperative.Logic.CFGInitEnvWF
      (P := Expression) (CmdT := Command) params cfg ρ where
  /-- Every builtin referenced by the CFG is included among the declared functions. -/
  factoryDeclared : ∀ s, Core.isNameInFactory s = Bool.true →
    params.declaredFuncs ⟨s, ()⟩ = Bool.true

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
