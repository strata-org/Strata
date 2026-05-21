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
  Coverage at this commit: booleans (via `Lambda.LConst.boolConst`),
  integers (via `Lambda.LConst.intConst`), and the `vEmpty` sentinel
  (via `Lambda.LExpr.fvar` named `coreVEmptySentinel`). Other
  constructors return `none`. Strict subset; extend as proof
  obligations demand.
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
* `vEmpty` sentinel: `Lambda.LExpr.fvar` whose identifier name
  matches `coreVEmptySentinelName` ↔ `Value.vEmpty`.

Other shapes return `none`.

The `vEmpty` sentinel handles the `step_decl` bridge in
`Strata/Backends/CBMC/GOTO/Bisim.lean`. Tautschnig's
`StepInstr.decl` always sets the freshly-declared symbol to
`vEmpty`; this branch's `step_decl` uses an abstract `InitState`
producing some witness value. To bridge the two, the source-side
caller initialises freshly-declared variables to a sentinel
expression, and `valueCorrCore.toValue` recognises the sentinel as
`vEmpty`.

Convention: the sentinel identifier is a free variable named
`__strata_vEmpty__`. This name never appears in real source
programs because (a) it is double-underscored and (b) the `<proc>::
<scope>::<name>` renaming pass on real procedure-level identifiers
always inserts `::` separators. -/

/-- Magic name for the `vEmpty` sentinel free variable. -/
@[expose] def coreVEmptySentinelName : String := "__strata_vEmpty__"

/-- The sentinel expression: a free variable with the magic name.
Type annotation is `none` since the sentinel is type-erased on the
GOTO side (it always maps to `vEmpty`). -/
@[expose] def coreVEmptySentinel : Core.Expression.Expr :=
  Lambda.LExpr.fvar (T := ⟨⟨Core.ExpressionMetadata, Unit⟩, Lambda.LMonoTy⟩)
    () { name := coreVEmptySentinelName, metadata := () } none

@[expose] def coreToValue (e : Core.Expression.Expr) : Option Value :=
  match e with
  | .const _ (.boolConst b) => some (.vBool b)
  | .const _ (.intConst n) => some (.vInt n)
  | .fvar _ ⟨name, _⟩ none =>
    if name = coreVEmptySentinelName then some .vEmpty else none
  | _ => none

@[expose] def coreFromValue (v : Value) : Option Core.Expression.Expr :=
  match v with
  | .vBool b => some (.boolConst () b)
  | .vInt n => some (.intConst () n)
  | .vEmpty => some coreVEmptySentinel
  | _ => none

instance valueCorrCore : ValueCorr Core.Expression where
  toValue   := coreToValue
  fromValue := coreFromValue

/-- The sentinel maps to `vEmpty` under `coreToValue`. This is the
load-bearing fact for the `step_decl` bridge in `Bisim.lean`. -/
@[simp] theorem coreToValue_vEmptySentinel :
    coreToValue coreVEmptySentinel = some .vEmpty := by
  simp [coreToValue, coreVEmptySentinel]

/-- Round-trip: every `coreFromValue` output that is `some _` is
mapped back to its input by `coreToValue`. -/
theorem coreToValue_coreFromValue (v : Value) (e : Core.Expression.Expr)
    (h : coreFromValue v = some e) :
    coreToValue e = some v := by
  cases v with
  | vBool b => simp [coreFromValue] at h; rcases h with ⟨rfl⟩; rfl
  | vInt n  => simp [coreFromValue] at h; rcases h with ⟨rfl⟩; rfl
  | vEmpty  =>
    simp [coreFromValue] at h; rcases h with ⟨rfl⟩
    simp [coreToValue, coreVEmptySentinel]
  | _ => simp [coreFromValue] at h

/-- Round-trip in the other direction: every `coreToValue` output
that is `some _` is mapped back by `coreFromValue`.

Holds because `Core.Expression`'s metadata type is `Unit`, so the
`()` filled in by `coreFromValue` matches whatever metadata the
original `.const` carried, and the sentinel free variable's metadata
is also `()`. -/
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
  · -- fvar with no type annotation, conditional on the magic name.
    -- Split's destructured pattern was `.fvar _ ⟨name, _⟩ none`, so the
    -- introduced binders are m : Metadata (= Unit), name : String,
    -- and _ : IDMeta (= Unit).
    next m name idmeta =>
      split at h
      · -- name matches sentinel
        rename_i h_name
        have hv : v = .vEmpty := by injection h with h'; exact h'.symm
        subst hv
        simp only [coreFromValue, coreVEmptySentinel]
        -- Goal: LExpr.fvar () ⟨sentinelName, ()⟩ none = LExpr.fvar m ⟨name, idmeta⟩ none
        have hm : (m : Unit) = () := rfl
        have hidm : (idmeta : Unit) = () := rfl
        rw [h_name, hm, hidm]
      · cases h
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
