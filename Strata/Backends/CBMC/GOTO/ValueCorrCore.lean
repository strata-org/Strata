/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.SemanticsTautschnig
public import Strata.Languages.Core.Expressions
public import Strata.DL.Imperative.CmdSemantics

public section

/-! # Value, Store, and Eval correspondence between this branch and tautschnig

Phase 2.d (and the bridge half of Phase 0) of the
GOTO-semantics-expansion plan
(`docs/superpowers/specs/2026-05-20-goto-semantics-expansion-design.md`).

This module connects this branch's expression-valued
`Imperative.SemanticStore` (parameterized by `Core.Expression`) to
tautschnig's concrete `Value`/`String → Option Value` store,
following the pattern in `tautschnig/goto-semantics`'s
`SemanticsSim.lean`:

* `ValueCorr P` — typeclass providing `toValue : P.Expr → Option Value`
  and `fromValue : Value → Option P.Expr` for an arbitrary
  `PureExpr P`. Required for any `StoreCorr` bridge.
* `valueCorrCore : ValueCorr Core.Expression` — concrete instance.
  Coverage at this commit: booleans (via `Lambda.LConst.boolConst`)
  and integers (via `Lambda.LConst.intConst`). Other constructors
  return `none`. Strict subset; extend as proof obligations demand.
* `StoreCorr nameMap σ_imp σ_goto` — the imperative-side store and
  the GOTO-side store agree on the `nameMap`-translated keys, modulo
  `toValue`.
* `EvalCorr nameMap exprTrans δ_goto eval` — the GOTO evaluator
  `δ_goto`, instantiated by the source evaluator pre-composed with an
  expression translation `exprTrans`, agrees with the tautschnig-side
  `eval` on translated stores.

These definitions live in the `CProverGOTO.SemanticsTautschnig`
namespace (mirroring tautschnig's source) and are usable by future
Bisim.lean / CoreCFGToGOTOCorrectStore.lean modules. -/

namespace CProverGOTO.SemanticsTautschnig

open CProverGOTO

/-! ## ValueCorr typeclass -/

/-- Bidirectional correspondence between a source `PureExpr`'s
expression-valued domain and tautschnig's concrete `Value`. The two
maps are not required to be inverses of each other in general — for
constants both directions succeed and round-trip; for non-value-shaped
expressions both directions return `none`. -/
class ValueCorr (P : Imperative.PureExpr) where
  /-- Translate a source-side expression-as-value to a concrete `Value`.
  Returns `none` for source expressions that do not represent a
  ground value (variables, applications, quantifiers, …). -/
  toValue   : P.Expr → Option Value
  /-- Translate a concrete `Value` to a source-side expression-as-value.
  Returns `none` for `Value` shapes the source-side cannot express. -/
  fromValue : Value → Option P.Expr

/-! ## ValueCorr instance for Core.Expression

Coverage:

* Booleans: `Lambda.LConst.boolConst b ↔ Value.vBool b`.
* Integers: `Lambda.LConst.intConst n ↔ Value.vInt n`.

Other shapes return `none`. -/

@[expose] def coreToValue (e : Core.Expression.Expr) : Option Value :=
  match e with
  | .const _ (.boolConst b) => some (.vBool b)
  | .const _ (.intConst n) => some (.vInt n)
  | _ => none

@[expose] def coreFromValue (v : Value) : Option Core.Expression.Expr :=
  match v with
  | .vBool b => some (.boolConst () b)
  | .vInt n => some (.intConst () n)
  | _ => none

instance valueCorrCore : ValueCorr Core.Expression where
  toValue   := coreToValue
  fromValue := coreFromValue

/-- Round-trip: every `coreFromValue` output that is `some _` is
mapped back to its input by `coreToValue`. -/
theorem coreToValue_coreFromValue (v : Value) (e : Core.Expression.Expr)
    (h : coreFromValue v = some e) :
    coreToValue e = some v := by
  cases v <;> simp [coreFromValue] at h <;> rcases h with ⟨rfl⟩ <;> rfl

/-- Round-trip in the other direction: every `coreToValue` output
that is `some _` is mapped back by `coreFromValue`.

Holds because `Core.Expression`'s metadata type is `Unit`, so the
`()` filled in by `coreFromValue` matches whatever metadata the
original `.const` carried. -/
theorem coreFromValue_coreToValue (e : Core.Expression.Expr) (v : Value)
    (h : coreToValue e = some v) :
    coreFromValue v = some e := by
  unfold coreToValue at h
  split at h
  · rename_i m b
    have : v = .vBool b := by injection h with h'; exact h'.symm
    subst this
    rcases m
    rfl
  · rename_i m n
    have : v = .vInt n := by injection h with h'; exact h'.symm
    subst this
    rcases m
    rfl
  · cases h

/-! ## StoreCorr -/

/-- Store correspondence: an imperative-side store `σ_imp` (mapping
source identifiers to source expressions) agrees with a tautschnig-side
GOTO store `σ_goto` (mapping `String` symbol names to `Value`s) at
every key, after translating the source identifier through `nameMap`
and the source expression through `vc.toValue`. Either both stores
agree pointwise (the binding maps to the same value, modulo
correspondence), or both stores leave the key undefined. -/
@[expose] def StoreCorr {P : Imperative.PureExpr} [vc : ValueCorr P]
    (nameMap : P.Ident → String)
    (σ_imp : Imperative.SemanticStore P) (σ_goto : Store) : Prop :=
  ∀ x : P.Ident,
    (σ_imp x = none ∧ σ_goto (nameMap x) = none) ∨
    (∃ e v, σ_imp x = some e ∧ vc.toValue e = some v ∧
            σ_goto (nameMap x) = some v)

/-! ## EvalCorr -/

/-- Evaluator correspondence: the source-side evaluator `δ_imp`
(operating on source expressions and source stores) agrees with the
tautschnig-side `eval` (operating on GOTO expressions and concrete
`Value` stores) on every translated expression, modulo
`StoreCorr nameMap` and `vc.toValue`.

Specifically: if `δ_imp σ_imp e_imp = some v_imp`, then
`eval σ_goto (exprTrans e_imp) = vc.toValue v_imp`. -/
@[expose] def EvalCorr {P : Imperative.PureExpr} [vc : ValueCorr P]
    (nameMap : P.Ident → String)
    (exprTrans : P.Expr → Expr)
    (δ_imp : Imperative.SemanticEval P)
    (eval : ExprEval) : Prop :=
  ∀ σ_imp σ_goto e_imp v_imp,
    StoreCorr nameMap σ_imp σ_goto →
    δ_imp σ_imp e_imp = some v_imp →
    eval σ_goto (exprTrans e_imp) = vc.toValue v_imp

end CProverGOTO.SemanticsTautschnig
