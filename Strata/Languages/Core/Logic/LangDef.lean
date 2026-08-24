/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.StatementSemantics
public import Strata.Languages.Core.Factory
public import Strata.DL.Imperative.Logic.LangDef
import all Strata.Languages.Core.Factory

/-! # Core `Lang` bundles and their initial-environment well-formedness

The Core instances of `Strata.Logic.Lang`, together with the well-formedness
predicates that gate them.  Split out from `Strata.Transform.CoreSpecification`
so that a program logic over Core (`Strata.Languages.Core.Logic.Hoare`) can be
stated without depending on the transform-specification framework, mirroring
`Strata.DL.Imperative.Logic.LangDef` on the Imperative side.

## Contents

- **`InitEnvWFParams`** — the parameter record (reserved fresh-prefixes and the
  already-declared function names) threaded into both gates.
- **`InitEnvWF`** / **`BlockInitEnvWF`** — the statement- and block-level gates.
  Both extend `Imperative.WellFormedSemanticEval` on `ρ.factory` and add
  Core-specific store, freshness and def-use conditions.
- **`Lang.core`** — the `Lang` for Core statements, gated on `InitEnvWF`.
- **`Lang.coreBlock`** — the `Lang` for Core statement lists, gated on
  `BlockInitEnvWF`.
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
    operator references in the program are pre-declared, and any `funcDecl`
    introduces a fresh name. -/
structure InitEnvWFParams where
  /-- Reserved "fresh-prefixes" that must not appear in the initial env. -/
  prefixIdents : List String
  /-- Predicate of operator/function names already defined in the evaluator. -/
  declaredFuncs : Expression.Ident → Bool

/-- Store-well-formedness needed for a statement `s` to execute in env `ρ` without
    getting stuck.

    Extends `Imperative.WellFormedSemanticEval` on `ρ.factory`, which
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
      entry. -/
  storeWellDefined : Imperative.WellFormedStore ρ.store ρ.factory
  readWritesDefined : ∀ n ∈ Stmt.touchedVars s, n ∉ Stmt.definedVars s false →
    (ρ.store n).isSome
  defsUndefined : ∀ n ∈ Stmt.definedVars s false, (ρ.store n).isNone
  /-- Source's `definedVars` don't use any of the reserved prefixes. -/
  definedVarsNotReserved : ∀ n ∈ Stmt.definedVars s false, ∀ p ∈ params.prefixIdents,
    ¬ p.toList.isPrefixOf n.name.toList
  /-- Source's `funcDeclNames` don't use any of the reserved prefixes.
      `funcDecl` names live in the evaluator (not the store), so they aren't
      covered by `definedVarsNotReserved`. -/
  funcDeclNamesNotReserved : ∀ n ∈ Stmt.funcDeclNames s false, ∀ p ∈ params.prefixIdents,
    ¬ p.toList.isPrefixOf n.name.toList
  reservedFresh : ∀ n, (ρ.store n).isSome →
    ∀ p ∈ params.prefixIdents, ¬ p.toList.isPrefixOf n.name.toList
  defUseOk : Stmt.defUseWellFormed (fun n => (ρ.store n).isSome) params.declaredFuncs s = Bool.true
  factoryDeclared : ∀ s, Core.isNameInFactory s = Bool.true →
    params.declaredFuncs ⟨s, ()⟩ = Bool.true

/-- Block-level analog of `InitEnvWF`: well-formedness for executing a block of
    statements `bss` from env `ρ`. -/
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
  funcDeclNamesNotReserved : ∀ n ∈ Block.funcDeclNames bss false, ∀ p ∈ params.prefixIdents,
    ¬ p.toList.isPrefixOf n.name.toList
  reservedFresh : ∀ n, (ρ.store n).isSome →
    ∀ p ∈ params.prefixIdents, ¬ p.toList.isPrefixOf n.name.toList
  defUseOk : Block.defUseWellFormed (fun n => (ρ.store n).isSome) params.declaredFuncs bss = Bool.true
  factoryDeclared : ∀ s, Core.isNameInFactory s = Bool.true →
    params.declaredFuncs ⟨s, ()⟩ = Bool.true

/-- The `Lang Expression` bundle for Core small-step semantics. -/
@[expose] def Lang.core
    (π : String → Option Procedure)
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory) :
    Strata.Logic.Lang Expression :=
  Imperative.Logic.Lang.imperative
    Expression Command (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert
    (ParamsTy := InitEnvWFParams) (initEnvWF := InitEnvWF)

/-- The `Lang Expression` bundle for Core small-step semantics over *statement
    lists* (block bodies): the Core counterpart of
    `Imperative.Logic.Lang.imperativeBlock`, with the generic
    `Imperative.Logic.BlockInitEnvWF` replaced by Core's own `BlockInitEnvWF`.

    `StmtT` is `Statements` and `stmtCfg` embeds via `.stmts`, so this is the
    language a block-level overapproximation or Hoare-style block judgement is
    stated over, exactly as `Lang.core` is for single statements. -/
@[expose] def Lang.coreBlock
    (π : String → Option Procedure)
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory) :
    Strata.Logic.Lang Expression :=
  Imperative.Logic.Lang.imperativeBlock
    (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert
    (wfPkg := ⟨InitEnvWFParams, BlockInitEnvWF⟩)

end Core.Logic

end -- public section
