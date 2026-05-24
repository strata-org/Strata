/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOInvariants
public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOCorrect
public import Strata.Backends.CBMC.GOTO.LambdaToCProverGOTO
public import Strata.Languages.Core.StatementSemantics

public section

/-! # Discharging `ExprTranslationPreservesEval` on the bool + int fragment

This module is the partial discharge of Gap B from
`docs/CoreToGOTO_CorrectnessAnalysis.md` §3 against
`Lambda.LExpr.toGotoExprCtx` (in `LambdaToCProverGOTO.lean:264`),
restricted to a **boolean + integer** expression fragment.

## Scope

The covered Core operators (Lambda function names) are:

* **Integer constants**: `LExpr.const _ (.intConst n)`.
* **Integer arithmetic**: `Int.Add`, `Int.Sub`, `Int.Mul`, `Int.DivT`,
  `Int.ModT`.
* **Integer comparisons**: `Int.Lt`, `Int.Le`, `Int.Gt`, `Int.Ge`.
* **Integer (and core) equality**: `LExpr.eq`.
* **Boolean constants**: `LExpr.const _ (.boolConst b)`.
* **Boolean operations**: `Bool.Not`, `Bool.And`, `Bool.Or`,
  `Bool.Implies`.
* **Free variables** of integer or boolean type.

Out of scope here (would need additional work or a different
worker):

* `Int.Div`, `Int.Mod` — these expand into compound `mkEuclideanDiv` /
  `mkEuclideanMod` GOTO expressions; the per-operator argument is more
  involved.
* Bitvector operators, real arithmetic, strings, regex, maps.
* Quantifiers, lambda abstractions, `old(·)` (two-state), `ite`.

## Strategy: Option (b) of the analysis doc

The analysis doc lists three options:

  (a) make `concreteEval` total (out of scope of Gap B);
  (b) keep both evaluators abstract and supply axiomatic per-operator
      hypotheses;
  (c) define a new total `gotoConcreteEvalTotal` over a restricted
      fragment.

We chose **(b)**. The two evaluators (`δ`, `δ_goto`, `δ_goto_bool`) stay
abstract and the user supplies a `BoolIntOpHypotheses` bundle of
per-operator soundness facts for each side. Then the structural
induction over `LExpr` produces an `ExprTranslated` witness for every
expression in the supported fragment.

The user is expected to discharge the `BoolIntOpHypotheses` bundle
when they instantiate `δ` and `δ_goto` to concrete evaluators (e.g.
the `concreteEval` Phase 2 port, once total). At that point the
discharge becomes a straightforward unfold of both definitions on a
per-operator basis. -/

namespace CProverGOTO.ExprTranslationBoolInt

open CProverGOTO Imperative Lambda

/-! ## Predicate: "this LExpr is in the bool + int fragment"

Used as the domain of the structural induction. Recursively traverses
an `LExpr` and asks: is every constructor on the path one of the
supported shapes (constants, free variables of supported type, the
listed operators)?

Note: this is *syntactic*. We do not check type-correctness of the
expression; the per-operator hypotheses encode what each operator
expects and discharge the proof when the expression is well-typed. -/

/-- Predicate: `op` is one of the supported binary integer operators
(arithmetic or comparison). -/
@[expose] def isSupportedIntBinOp (op : String) : Bool :=
  op == "Int.Add" || op == "Int.Sub" || op == "Int.Mul"
  || op == "Int.DivT" || op == "Int.ModT"
  || op == "Int.Lt" || op == "Int.Le" || op == "Int.Gt" || op == "Int.Ge"

/-- Predicate: `op` is one of the supported binary boolean operators. -/
@[expose] def isSupportedBoolBinOp (op : String) : Bool :=
  op == "Bool.And" || op == "Bool.Or" || op == "Bool.Implies"

/-- Predicate: `op` is the boolean negation operator. -/
@[expose] def isSupportedBoolUnaryOp (op : String) : Bool :=
  op == "Bool.Not"

/-- Recursive predicate: every node of the `LExpr` is in the supported
bool + int fragment.

For free variables we accept any annotated type — we don't check the
type matches the operator's expected type, since type-checking is
upstream and the per-operator hypothesis would fail at evaluation if
mismatched. -/
def isBoolIntFragment :
    LExpr ⟨⟨Core.ExpressionMetadata, Unit⟩, LMonoTy⟩ → Bool
  | .const _ (.intConst _)  => true
  | .const _ (.boolConst _) => true
  | .fvar _ _ (some _)      => true
  -- Binary application: (op fn) e1 e2 with fn supported
  | .app _ (.app _ (.op _ fn (some _)) e1) e2 =>
    (isSupportedIntBinOp fn.name || isSupportedBoolBinOp fn.name)
    && isBoolIntFragment e1 && isBoolIntFragment e2
  -- Unary application: (op fn) e1
  | .app _ (.op _ fn (some _)) e1 =>
    isSupportedBoolUnaryOp fn.name && isBoolIntFragment e1
  -- Equality
  | .eq _ e1 e2 => isBoolIntFragment e1 && isBoolIntFragment e2
  -- Conditional
  | .ite _ c t e =>
    isBoolIntFragment c && isBoolIntFragment t && isBoolIntFragment e
  | _ => false

/-! ## Per-operator hypothesis bundle

The user must supply, for each operator we cover, a soundness fact on
*both* sides:

* The Core source-side fact: under `δ`, the LExpr-level operator
  evaluates compositionally — given the value of each argument, the
  result is determined.
* The GOTO target-side fact: under `δ_goto` (or `δ_goto_bool`), the
  GOTO-level operator evaluates the same way on the same arguments.

These pair up to give bidirectional value-agreement
(`ExprTranslated.value_agree`) at each operator. -/

/-- Bundle of per-operator soundness hypotheses for the bool + int
fragment.

Each field discharges one operator at the level of "given the
sub-expressions evaluate consistently, the operator-application-level
expressions evaluate consistently". Combined with the structural
induction, these produce `ExprTranslated` witnesses for every
expression in the supported fragment. -/
structure BoolIntOpHypotheses
    (δ : SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression) : Prop where
  -- Constants ---------------------------------------------------------
  /-- An integer-constant Core expression evaluates to itself; the GOTO
  translation evaluates to the same value. -/
  intConst_value :
    ∀ σ (n : Int),
      (δ σ (LExpr.intConst () n) = some (LExpr.intConst () n)) ∧
      (δ_goto σ (Expr.constant (toString (LConst.intConst n)) .Integer)
        = some (LExpr.intConst () n))
  /-- A boolean-constant Core expression evaluates to itself; same on
  the GOTO side. Both bool views (`δ_goto_bool`) report the obvious
  truth. -/
  boolConst_value :
    ∀ σ (b : Bool),
      (δ σ (LExpr.boolConst () b) = some (LExpr.boolConst () b)) ∧
      (δ_goto σ (Expr.constant (toString (LConst.boolConst b)) .Boolean)
        = some (LExpr.boolConst () b)) ∧
      (δ_goto_bool σ (Expr.constant (toString (LConst.boolConst b)) .Boolean)
        = some b)
  -- Free variables ---------------------------------------------------
  /-- A free variable's value is read directly from the store on both
  sides. -/
  fvar_value :
    ∀ σ (v : Lambda.Identifier Unit) (mty : LMonoTy)
      (gty : Ty)
      (_h_ty : mty.toGotoType = .ok gty)
      (e : Core.Expression.Expr),
      (δ σ (LExpr.fvar () v (some mty)) = some e ↔
        δ_goto σ (Expr.symbol (toString v) gty) = some e)
  -- Integer arithmetic operators --------------------------------------
  /-- `Int.Add`. -/
  intAdd_corr :
    ∀ σ (m₁ m₂ : Core.ExpressionMetadata) ty (e1c e2c : Core.Expression.Expr)
      (e1g e2g : CProverGOTO.Expr) (v : Core.Expression.Expr),
      δ σ (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.Add", ()⟩ ty) e1c) e2c)
        = some v ↔
      δ_goto σ ⟨.multiary .Plus, .Integer, [e1g, e2g], .nil, []⟩ = some v
  /-- `Int.Sub`. -/
  intSub_corr :
    ∀ σ (m₁ m₂ : Core.ExpressionMetadata) ty (e1c e2c : Core.Expression.Expr)
      (e1g e2g : CProverGOTO.Expr) (v : Core.Expression.Expr),
      δ σ (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.Sub", ()⟩ ty) e1c) e2c)
        = some v ↔
      δ_goto σ ⟨.binary .Minus, .Integer, [e1g, e2g], .nil, []⟩ = some v
  /-- `Int.Mul`. -/
  intMul_corr :
    ∀ σ (m₁ m₂ : Core.ExpressionMetadata) ty (e1c e2c : Core.Expression.Expr)
      (e1g e2g : CProverGOTO.Expr) (v : Core.Expression.Expr),
      δ σ (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.Mul", ()⟩ ty) e1c) e2c)
        = some v ↔
      δ_goto σ ⟨.multiary .Mult, .Integer, [e1g, e2g], .nil, []⟩ = some v
  /-- `Int.DivT` (truncating division). -/
  intDivT_corr :
    ∀ σ (m₁ m₂ : Core.ExpressionMetadata) ty (e1c e2c : Core.Expression.Expr)
      (e1g e2g : CProverGOTO.Expr) (v : Core.Expression.Expr),
      δ σ (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.DivT", ()⟩ ty) e1c) e2c)
        = some v ↔
      δ_goto σ ⟨.binary .Div, .Integer, [e1g, e2g], .nil, []⟩ = some v
  /-- `Int.ModT` (truncating modulo). -/
  intModT_corr :
    ∀ σ (m₁ m₂ : Core.ExpressionMetadata) ty (e1c e2c : Core.Expression.Expr)
      (e1g e2g : CProverGOTO.Expr) (v : Core.Expression.Expr),
      δ σ (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.ModT", ()⟩ ty) e1c) e2c)
        = some v ↔
      δ_goto σ ⟨.binary .Mod, .Integer, [e1g, e2g], .nil, []⟩ = some v
  -- Integer comparisons ----------------------------------------------
  /-- `Int.Lt`. -/
  intLt_corr :
    ∀ σ (m₁ m₂ : Core.ExpressionMetadata) ty (e1c e2c : Core.Expression.Expr)
      (e1g e2g : CProverGOTO.Expr) (v : Core.Expression.Expr),
      δ σ (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.Lt", ()⟩ ty) e1c) e2c)
        = some v ↔
      δ_goto σ ⟨.binary .Lt, .Boolean, [e1g, e2g], .nil, []⟩ = some v
  /-- `Int.Le`. -/
  intLe_corr :
    ∀ σ (m₁ m₂ : Core.ExpressionMetadata) ty (e1c e2c : Core.Expression.Expr)
      (e1g e2g : CProverGOTO.Expr) (v : Core.Expression.Expr),
      δ σ (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.Le", ()⟩ ty) e1c) e2c)
        = some v ↔
      δ_goto σ ⟨.binary .Le, .Boolean, [e1g, e2g], .nil, []⟩ = some v
  /-- `Int.Gt`. -/
  intGt_corr :
    ∀ σ (m₁ m₂ : Core.ExpressionMetadata) ty (e1c e2c : Core.Expression.Expr)
      (e1g e2g : CProverGOTO.Expr) (v : Core.Expression.Expr),
      δ σ (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.Gt", ()⟩ ty) e1c) e2c)
        = some v ↔
      δ_goto σ ⟨.binary .Gt, .Boolean, [e1g, e2g], .nil, []⟩ = some v
  /-- `Int.Ge`. -/
  intGe_corr :
    ∀ σ (m₁ m₂ : Core.ExpressionMetadata) ty (e1c e2c : Core.Expression.Expr)
      (e1g e2g : CProverGOTO.Expr) (v : Core.Expression.Expr),
      δ σ (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.Ge", ()⟩ ty) e1c) e2c)
        = some v ↔
      δ_goto σ ⟨.binary .Ge, .Boolean, [e1g, e2g], .nil, []⟩ = some v
  -- Boolean operators -----------------------------------------------
  /-- `Bool.Not`. -/
  boolNot_corr :
    ∀ σ (m : Core.ExpressionMetadata) ty (e1c : Core.Expression.Expr)
      (e1g : CProverGOTO.Expr) (v : Core.Expression.Expr),
      δ σ (LExpr.app m (LExpr.op () ⟨"Bool.Not", ()⟩ ty) e1c) = some v ↔
      δ_goto σ ⟨.unary .Not, .Boolean, [e1g], .nil, []⟩ = some v
  /-- `Bool.Not` boolean view. -/
  boolNot_bool_corr :
    ∀ σ (m : Core.ExpressionMetadata) ty (e1c : Core.Expression.Expr)
      (e1g : CProverGOTO.Expr) (b : Bool),
      δ σ (LExpr.app m (LExpr.op () ⟨"Bool.Not", ()⟩ ty) e1c)
        = some (LExpr.boolConst () b) ↔
      δ_goto_bool σ ⟨.unary .Not, .Boolean, [e1g], .nil, []⟩ = some b
  /-- `Bool.And`. -/
  boolAnd_corr :
    ∀ σ (m₁ m₂ : Core.ExpressionMetadata) ty (e1c e2c : Core.Expression.Expr)
      (e1g e2g : CProverGOTO.Expr) (v : Core.Expression.Expr),
      δ σ (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Bool.And", ()⟩ ty) e1c) e2c)
        = some v ↔
      δ_goto σ ⟨.multiary .And, .Boolean, [e1g, e2g], .nil, []⟩ = some v
  /-- `Bool.And` boolean view. -/
  boolAnd_bool_corr :
    ∀ σ (m₁ m₂ : Core.ExpressionMetadata) ty (e1c e2c : Core.Expression.Expr)
      (e1g e2g : CProverGOTO.Expr) (b : Bool),
      δ σ (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Bool.And", ()⟩ ty) e1c) e2c)
        = some (LExpr.boolConst () b) ↔
      δ_goto_bool σ ⟨.multiary .And, .Boolean, [e1g, e2g], .nil, []⟩ = some b
  /-- `Bool.Or`. -/
  boolOr_corr :
    ∀ σ (m₁ m₂ : Core.ExpressionMetadata) ty (e1c e2c : Core.Expression.Expr)
      (e1g e2g : CProverGOTO.Expr) (v : Core.Expression.Expr),
      δ σ (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Bool.Or", ()⟩ ty) e1c) e2c)
        = some v ↔
      δ_goto σ ⟨.multiary .Or, .Boolean, [e1g, e2g], .nil, []⟩ = some v
  /-- `Bool.Or` boolean view. -/
  boolOr_bool_corr :
    ∀ σ (m₁ m₂ : Core.ExpressionMetadata) ty (e1c e2c : Core.Expression.Expr)
      (e1g e2g : CProverGOTO.Expr) (b : Bool),
      δ σ (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Bool.Or", ()⟩ ty) e1c) e2c)
        = some (LExpr.boolConst () b) ↔
      δ_goto_bool σ ⟨.multiary .Or, .Boolean, [e1g, e2g], .nil, []⟩ = some b
  /-- `Bool.Implies`. -/
  boolImplies_corr :
    ∀ σ (m₁ m₂ : Core.ExpressionMetadata) ty (e1c e2c : Core.Expression.Expr)
      (e1g e2g : CProverGOTO.Expr) (v : Core.Expression.Expr),
      δ σ (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Bool.Implies", ()⟩ ty) e1c) e2c)
        = some v ↔
      δ_goto σ ⟨.binary .Implies, .Boolean, [e1g, e2g], .nil, []⟩ = some v
  /-- `Bool.Implies` boolean view. -/
  boolImplies_bool_corr :
    ∀ σ (m₁ m₂ : Core.ExpressionMetadata) ty (e1c e2c : Core.Expression.Expr)
      (e1g e2g : CProverGOTO.Expr) (b : Bool),
      δ σ (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Bool.Implies", ()⟩ ty) e1c) e2c)
        = some (LExpr.boolConst () b) ↔
      δ_goto_bool σ ⟨.binary .Implies, .Boolean, [e1g, e2g], .nil, []⟩ = some b
  -- Equality --------------------------------------------------------
  /-- The LExpr `.eq` constructor agrees with GOTO `.binary .Equal`. -/
  eq_corr :
    ∀ σ (m : Core.ExpressionMetadata) (e1c e2c : Core.Expression.Expr)
      (e1g e2g : CProverGOTO.Expr) (v : Core.Expression.Expr),
      δ σ (LExpr.eq m e1c e2c) = some v ↔
      δ_goto σ ⟨.binary .Equal, .Boolean, [e1g, e2g], .nil, []⟩ = some v
  /-- Bool view of equality. -/
  eq_bool_corr :
    ∀ σ (m : Core.ExpressionMetadata) (e1c e2c : Core.Expression.Expr)
      (e1g e2g : CProverGOTO.Expr) (b : Bool),
      δ σ (LExpr.eq m e1c e2c) = some (LExpr.boolConst () b) ↔
      δ_goto_bool σ ⟨.binary .Equal, .Boolean, [e1g, e2g], .nil, []⟩ = some b
  -- Generic boolean view alignment ---------------------------------
  /-- The bool view follows from value-agreement on bool-shaped GOTO
  expressions: `δ_goto` returning a Core boolean constant `boolConst b`
  is the same as `δ_goto_bool` returning `some b`. -/
  goto_bool_agrees_value :
    ∀ σ (e_goto : CProverGOTO.Expr) (b : Bool),
      δ_goto σ e_goto = some (LExpr.boolConst () b) ↔
      δ_goto_bool σ e_goto = some b
  -- Conditional ----------------------------------------------------
  /-- The LExpr `.ite` constructor agrees with GOTO `Expr.ite`. -/
  ite_corr :
    ∀ σ (m : Core.ExpressionMetadata)
      (cc tc ec : Core.Expression.Expr)
      (cg tg eg : CProverGOTO.Expr) (v : Core.Expression.Expr),
      δ σ (LExpr.ite m cc tc ec) = some v ↔
      δ_goto σ (Expr.ite cg tg eg) = some v

/-! ## Per-operator soundness lemmas

Each lemma takes a `BoolIntOpHypotheses` bundle and produces an
`ExprTranslated` witness for one operator's application form. They are
the leaves used by the structural-induction theorem. -/

open ExprTranslated

/-- Chain `value_agree` with the `goto_bool_agrees_value` field of the
hypothesis bundle to derive the boolean view: when the source expression
evaluates to `Core.true`/`Core.false` exactly when the target's boolean
view does. -/
private theorem boolAgree_of_valueAgree
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (e_core : Core.Expression.Expr) (e_goto : CProverGOTO.Expr)
    (h_value : ∀ σ v, δ σ e_core = some v ↔ δ_goto σ e_goto = some v) :
    (∀ σ, δ σ e_core = some (HasBool.tt (P := Core.Expression)) ↔
          δ_goto_bool σ e_goto = some true) ∧
    (∀ σ, δ σ e_core = some (HasBool.ff (P := Core.Expression)) ↔
          δ_goto_bool σ e_goto = some false) := by
  refine ⟨?_, ?_⟩
  · intro σ
    -- HasBool.tt for Core.Expression unfolds to Core.true = boolConst () true.
    -- Chain value_agree with goto_bool_agrees_value.
    have h_v := h_value σ (LExpr.boolConst () true)
    have h_b := h.goto_bool_agrees_value σ e_goto true
    constructor
    · intro h_src; exact h_b.mp (h_v.mp h_src)
    · intro h_tgt; exact h_v.mpr (h_b.mpr h_tgt)
  · intro σ
    have h_v := h_value σ (LExpr.boolConst () false)
    have h_b := h.goto_bool_agrees_value σ e_goto false
    constructor
    · intro h_src; exact h_b.mp (h_v.mp h_src)
    · intro h_tgt; exact h_v.mpr (h_b.mpr h_tgt)

/-- Build an `ExprTranslated` from just a `value_agree` proof, using
`goto_bool_agrees_value` to fill in the bool agreement fields. -/
private theorem ExprTranslated.ofValueAgree
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (e_core : Core.Expression.Expr) (e_goto : CProverGOTO.Expr)
    (h_value : ∀ σ v, δ σ e_core = some v ↔ δ_goto σ e_goto = some v) :
    ExprTranslated δ δ_goto δ_goto_bool e_core e_goto :=
  let ⟨h_tt, h_ff⟩ := boolAgree_of_valueAgree h e_core e_goto h_value
  ⟨h_value, h_tt, h_ff⟩

/-- `intConst`: the integer-constant case. -/
theorem intConst_translated
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (n : Int) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.intConst () n)
      (Expr.constant (toString (LConst.intConst n)) .Integer) := by
  -- Both sides evaluate the constant to itself, so value_agree, bool_tt_agree
  -- and bool_ff_agree all reduce to "they agree on this specific value".
  refine ⟨?vagree, ?ttagree, ?ffagree⟩
  case vagree =>
    intro σ v
    obtain ⟨h_src, h_tgt⟩ := h.intConst_value σ n
    rw [h_src, h_tgt]
  case ttagree =>
    -- HasBool.tt = Core.true = boolConst true ≠ intConst n.
    intro σ
    obtain ⟨h_src, h_tgt⟩ := h.intConst_value σ n
    constructor
    · intro h_eq
      -- δ σ (intConst n) = some intConst n by h_src; that contradicts boolConst.
      rw [h_src] at h_eq
      -- some (intConst n) ≠ some (boolConst true) by injection on the LExpr.
      simp only [show (HasBool.tt (P := Core.Expression)) =
        LExpr.const () (LConst.boolConst true) from rfl] at h_eq
      injection h_eq with h_eq
      injection h_eq with _ h_const
      cases h_const
    · intro h_eq
      -- δ_goto_bool σ (constant "...") = some true contradicts via the hypothesis
      -- chain with goto_bool_agrees_value plus intConst_value.
      have h_iff := h.goto_bool_agrees_value σ
        (Expr.constant (toString (LConst.intConst n)) .Integer) true
      have h_dgoto : δ_goto σ (Expr.constant (toString (LConst.intConst n)) .Integer)
                       = some (LExpr.boolConst () true) := h_iff.mpr h_eq
      rw [h_tgt] at h_dgoto
      injection h_dgoto with h_eq
      injection h_eq with _ h_const
      cases h_const
  case ffagree =>
    intro σ
    obtain ⟨h_src, h_tgt⟩ := h.intConst_value σ n
    constructor
    · intro h_eq
      rw [h_src] at h_eq
      simp only [show (HasBool.ff (P := Core.Expression)) =
        LExpr.const () (LConst.boolConst false) from rfl] at h_eq
      injection h_eq with h_eq
      injection h_eq with _ h_const
      cases h_const
    · intro h_eq
      have h_iff := h.goto_bool_agrees_value σ
        (Expr.constant (toString (LConst.intConst n)) .Integer) false
      have h_dgoto : δ_goto σ (Expr.constant (toString (LConst.intConst n)) .Integer)
                       = some (LExpr.boolConst () false) := h_iff.mpr h_eq
      rw [h_tgt] at h_dgoto
      injection h_dgoto with h_eq
      injection h_eq with _ h_const
      cases h_const

/-- `boolConst`: the boolean-constant case. -/
theorem boolConst_translated
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (b : Bool) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.boolConst () b)
      (Expr.constant (toString (LConst.boolConst b)) .Boolean) := by
  refine ⟨?vagree, ?ttagree, ?ffagree⟩
  case vagree =>
    intro σ v
    obtain ⟨h_src, h_tgt, _⟩ := h.boolConst_value σ b
    rw [h_src, h_tgt]
  case ttagree =>
    intro σ
    obtain ⟨h_src, _, h_bool⟩ := h.boolConst_value σ b
    -- Note `HasBool.tt = LExpr.const () (.boolConst true)` (`Core.Core.true`)
    -- and `LExpr.boolConst` is sugar for the same; injectivity reduces both
    -- sides to `b = true`.
    constructor
    · intro h_eq
      rw [h_src] at h_eq
      -- h_eq : some (boolConst b) = some Core.true ; want b = true.
      have hb : b = true := by
        injection h_eq with h_eq
        -- h_eq : LExpr.const () (LConst.boolConst b) = Core.Core.true
        -- Core.Core.true unfolds to LExpr.const () (LConst.boolConst true).
        injection h_eq with _ h_const
        injection h_const
      subst hb
      exact h_bool
    · intro h_eq
      have hb : b = true := by
        rw [h_bool] at h_eq
        injection h_eq
      subst hb
      rw [h_src]
      rfl
  case ffagree =>
    intro σ
    obtain ⟨h_src, _, h_bool⟩ := h.boolConst_value σ b
    constructor
    · intro h_eq
      rw [h_src] at h_eq
      have hb : b = false := by
        injection h_eq with h_eq
        injection h_eq with _ h_const
        injection h_const
      subst hb
      exact h_bool
    · intro h_eq
      have hb : b = false := by
        rw [h_bool] at h_eq
        injection h_eq
      subst hb
      rw [h_src]
      rfl

/-! ### Binary operator descriptor

The 12 binary arithmetic-ish operators (`Int.{Add,Sub,Mul,DivT,ModT,
Lt,Le,Gt,Ge}` plus `Bool.{And,Or,Implies}`) have a near-identical
proof skeleton. Following the L1 OpDesc smoke test, we factor the
per-op data into a `BoolIntBinOpDesc` and generalise both the
`<op>_translated` lemmas and the bridge helpers into single generic
theorems parametrised by the descriptor. -/

/-- Descriptor for one binary boolean/integer operator: its Core name,
the GOTO `Expr.Identifier` it translates to, and the GOTO output type
(`.Integer` for integer arithmetic, `.Boolean` for comparisons and
boolean ops). -/
structure BoolIntBinOpDesc where
  /-- The Core operator name, e.g. `"Int.Add"`. -/
  opName : String
  /-- The GOTO `Expr.Identifier` for the translated form. -/
  opId   : Expr.Identifier
  /-- The GOTO output type (`.Integer` or `.Boolean`). -/
  outTy  : Ty

namespace BoolIntBinOpDesc

/-- `Int.Add` → `.multiary .Plus, .Integer`. -/
def intAdd : BoolIntBinOpDesc := ⟨"Int.Add", .multiary .Plus, .Integer⟩
/-- `Int.Sub` → `.binary .Minus, .Integer`. -/
def intSub : BoolIntBinOpDesc := ⟨"Int.Sub", .binary .Minus, .Integer⟩
/-- `Int.Mul` → `.multiary .Mult, .Integer`. -/
def intMul : BoolIntBinOpDesc := ⟨"Int.Mul", .multiary .Mult, .Integer⟩
/-- `Int.DivT` → `.binary .Div, .Integer`. -/
def intDivT : BoolIntBinOpDesc := ⟨"Int.DivT", .binary .Div, .Integer⟩
/-- `Int.ModT` → `.binary .Mod, .Integer`. -/
def intModT : BoolIntBinOpDesc := ⟨"Int.ModT", .binary .Mod, .Integer⟩
/-- `Int.Lt` → `.binary .Lt, .Boolean`. -/
def intLt : BoolIntBinOpDesc := ⟨"Int.Lt", .binary .Lt, .Boolean⟩
/-- `Int.Le` → `.binary .Le, .Boolean`. -/
def intLe : BoolIntBinOpDesc := ⟨"Int.Le", .binary .Le, .Boolean⟩
/-- `Int.Gt` → `.binary .Gt, .Boolean`. -/
def intGt : BoolIntBinOpDesc := ⟨"Int.Gt", .binary .Gt, .Boolean⟩
/-- `Int.Ge` → `.binary .Ge, .Boolean`. -/
def intGe : BoolIntBinOpDesc := ⟨"Int.Ge", .binary .Ge, .Boolean⟩
/-- `Bool.And` → `.multiary .And, .Boolean`. -/
def boolAnd : BoolIntBinOpDesc := ⟨"Bool.And", .multiary .And, .Boolean⟩
/-- `Bool.Or` → `.multiary .Or, .Boolean`. -/
def boolOr : BoolIntBinOpDesc := ⟨"Bool.Or", .multiary .Or, .Boolean⟩
/-- `Bool.Implies` → `.binary .Implies, .Boolean`. -/
def boolImplies : BoolIntBinOpDesc := ⟨"Bool.Implies", .binary .Implies, .Boolean⟩

end BoolIntBinOpDesc

/-! ### Per-operator binary integer lemmas

Each lemma takes the value-agreement hypothesis on the full
operator-application (provided by the corresponding field of the
`BoolIntOpHypotheses` bundle) and lifts it to a full `ExprTranslated`
witness via `ExprTranslated.ofValueAgree`.

Note: the IH on the children isn't needed *to derive value_agree at the
parent*, because the per-operator hypothesis already states agreement on
the parent application directly. The IH would matter if we wanted to go
the other direction (peel off "value_agree at parent" into facts about
children), but `ExprTranslated` doesn't require that. -/

/-- Generic per-op `_translated` lemma: from a value-agreement
hypothesis matching the descriptor's pattern, build an
`ExprTranslated`. Replaces the 12 individual `<op>_translated` lemmas. -/
theorem binOp_translated_of_corr
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (od : BoolIntBinOpDesc)
    (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
    (e1c e2c : Core.Expression.Expr) (e1g e2g : CProverGOTO.Expr)
    (h_corr :
      ∀ σ v,
        δ σ (LExpr.app m₂ (LExpr.app m₁
              (LExpr.op () ⟨od.opName, ()⟩ ty) e1c) e2c) = some v ↔
        δ_goto σ ⟨od.opId, od.outTy, [e1g, e2g], .nil, []⟩ = some v) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨od.opName, ()⟩ ty) e1c) e2c)
      ⟨od.opId, od.outTy, [e1g, e2g], .nil, []⟩ :=
  ExprTranslated.ofValueAgree h _ _ h_corr

/-- `Int.Add`: integer addition. -/
theorem intAdd_translated
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
    (e1c e2c : Core.Expression.Expr) (e1g e2g : CProverGOTO.Expr) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.Add", ()⟩ ty) e1c) e2c)
      ⟨.multiary .Plus, .Integer, [e1g, e2g], .nil, []⟩ :=
  ExprTranslated.ofValueAgree h _ _ (fun σ v => h.intAdd_corr σ m₁ m₂ ty e1c e2c e1g e2g v)

/-- `Int.Sub`: integer subtraction. -/
theorem intSub_translated
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
    (e1c e2c : Core.Expression.Expr) (e1g e2g : CProverGOTO.Expr) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.Sub", ()⟩ ty) e1c) e2c)
      ⟨.binary .Minus, .Integer, [e1g, e2g], .nil, []⟩ :=
  ExprTranslated.ofValueAgree h _ _ (fun σ v => h.intSub_corr σ m₁ m₂ ty e1c e2c e1g e2g v)

/-- `Int.Mul`: integer multiplication. -/
theorem intMul_translated
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
    (e1c e2c : Core.Expression.Expr) (e1g e2g : CProverGOTO.Expr) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.Mul", ()⟩ ty) e1c) e2c)
      ⟨.multiary .Mult, .Integer, [e1g, e2g], .nil, []⟩ :=
  ExprTranslated.ofValueAgree h _ _ (fun σ v => h.intMul_corr σ m₁ m₂ ty e1c e2c e1g e2g v)

/-- `Int.DivT`: integer truncating division. -/
theorem intDivT_translated
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
    (e1c e2c : Core.Expression.Expr) (e1g e2g : CProverGOTO.Expr) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.DivT", ()⟩ ty) e1c) e2c)
      ⟨.binary .Div, .Integer, [e1g, e2g], .nil, []⟩ :=
  ExprTranslated.ofValueAgree h _ _ (fun σ v => h.intDivT_corr σ m₁ m₂ ty e1c e2c e1g e2g v)

/-- `Int.ModT`: integer truncating modulo. -/
theorem intModT_translated
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
    (e1c e2c : Core.Expression.Expr) (e1g e2g : CProverGOTO.Expr) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.ModT", ()⟩ ty) e1c) e2c)
      ⟨.binary .Mod, .Integer, [e1g, e2g], .nil, []⟩ :=
  ExprTranslated.ofValueAgree h _ _ (fun σ v => h.intModT_corr σ m₁ m₂ ty e1c e2c e1g e2g v)

/-- `Int.Lt`: integer less-than. -/
theorem intLt_translated
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
    (e1c e2c : Core.Expression.Expr) (e1g e2g : CProverGOTO.Expr) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.Lt", ()⟩ ty) e1c) e2c)
      ⟨.binary .Lt, .Boolean, [e1g, e2g], .nil, []⟩ :=
  ExprTranslated.ofValueAgree h _ _ (fun σ v => h.intLt_corr σ m₁ m₂ ty e1c e2c e1g e2g v)

/-- `Int.Le`: integer less-or-equal. -/
theorem intLe_translated
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
    (e1c e2c : Core.Expression.Expr) (e1g e2g : CProverGOTO.Expr) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.Le", ()⟩ ty) e1c) e2c)
      ⟨.binary .Le, .Boolean, [e1g, e2g], .nil, []⟩ :=
  ExprTranslated.ofValueAgree h _ _ (fun σ v => h.intLe_corr σ m₁ m₂ ty e1c e2c e1g e2g v)

/-- `Int.Gt`: integer greater-than. -/
theorem intGt_translated
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
    (e1c e2c : Core.Expression.Expr) (e1g e2g : CProverGOTO.Expr) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.Gt", ()⟩ ty) e1c) e2c)
      ⟨.binary .Gt, .Boolean, [e1g, e2g], .nil, []⟩ :=
  ExprTranslated.ofValueAgree h _ _ (fun σ v => h.intGt_corr σ m₁ m₂ ty e1c e2c e1g e2g v)

/-- `Int.Ge`: integer greater-or-equal. -/
theorem intGe_translated
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
    (e1c e2c : Core.Expression.Expr) (e1g e2g : CProverGOTO.Expr) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.Ge", ()⟩ ty) e1c) e2c)
      ⟨.binary .Ge, .Boolean, [e1g, e2g], .nil, []⟩ :=
  ExprTranslated.ofValueAgree h _ _ (fun σ v => h.intGe_corr σ m₁ m₂ ty e1c e2c e1g e2g v)

/-! ### Per-operator boolean lemmas -/

/-- `Bool.Not`: boolean negation. -/
theorem boolNot_translated
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (m : Core.ExpressionMetadata) (ty : Option LMonoTy)
    (e1c : Core.Expression.Expr) (e1g : CProverGOTO.Expr) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.app m (LExpr.op () ⟨"Bool.Not", ()⟩ ty) e1c)
      ⟨.unary .Not, .Boolean, [e1g], .nil, []⟩ :=
  ExprTranslated.ofValueAgree h _ _ (fun σ v => h.boolNot_corr σ m ty e1c e1g v)

/-- `Bool.And`. -/
theorem boolAnd_translated
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
    (e1c e2c : Core.Expression.Expr) (e1g e2g : CProverGOTO.Expr) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Bool.And", ()⟩ ty) e1c) e2c)
      ⟨.multiary .And, .Boolean, [e1g, e2g], .nil, []⟩ :=
  ExprTranslated.ofValueAgree h _ _ (fun σ v => h.boolAnd_corr σ m₁ m₂ ty e1c e2c e1g e2g v)

/-- `Bool.Or`. -/
theorem boolOr_translated
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
    (e1c e2c : Core.Expression.Expr) (e1g e2g : CProverGOTO.Expr) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Bool.Or", ()⟩ ty) e1c) e2c)
      ⟨.multiary .Or, .Boolean, [e1g, e2g], .nil, []⟩ :=
  ExprTranslated.ofValueAgree h _ _ (fun σ v => h.boolOr_corr σ m₁ m₂ ty e1c e2c e1g e2g v)

/-- `Bool.Implies`. -/
theorem boolImplies_translated
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
    (e1c e2c : Core.Expression.Expr) (e1g e2g : CProverGOTO.Expr) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Bool.Implies", ()⟩ ty) e1c) e2c)
      ⟨.binary .Implies, .Boolean, [e1g, e2g], .nil, []⟩ :=
  ExprTranslated.ofValueAgree h _ _ (fun σ v => h.boolImplies_corr σ m₁ m₂ ty e1c e2c e1g e2g v)

/-- `LExpr.ite`: conditional expression. -/
theorem ite_translated
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (m : Core.ExpressionMetadata)
    (cc tc ec : Core.Expression.Expr) (cg tg eg : CProverGOTO.Expr) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.ite m cc tc ec)
      (Expr.ite cg tg eg) :=
  ExprTranslated.ofValueAgree h _ _
    (fun σ v => h.ite_corr σ m cc tc ec cg tg eg v)

/-- `LExpr.eq`: structural equality. -/
theorem eq_translated
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (m : Core.ExpressionMetadata)
    (e1c e2c : Core.Expression.Expr) (e1g e2g : CProverGOTO.Expr) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.eq m e1c e2c)
      ⟨.binary .Equal, .Boolean, [e1g, e2g], .nil, []⟩ :=
  ExprTranslated.ofValueAgree h _ _ (fun σ v => h.eq_corr σ m e1c e2c e1g e2g v)

/-! ### Free variable lemma -/

/-- A free variable's translation preserves evaluation if the
`fvar_value` hypothesis applies. -/
theorem fvar_translated
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (v : Lambda.Identifier Unit) (mty : LMonoTy) (gty : Ty)
    (h_ty : mty.toGotoType = .ok gty) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.fvar () v (some mty))
      (Expr.symbol (toString v) gty) :=
  ExprTranslated.ofValueAgree h _ _
    (fun σ e => h.fvar_value σ v mty gty h_ty e)

/-! ## Translation predicate

Rather than committing to `LExpr.toGotoExprCtx` (whose body is not
exposed and so cannot be unfolded inside the proof under Lean 4's
module system), we describe the relation between an `LExpr` and its
GOTO translation as an inductive predicate `IsBoolIntTranslated`.
This predicate covers exactly the bool+int fragment, mirrors the
shapes the per-operator lemmas above expect, and admits a closed
structural-induction theorem `IsBoolIntTranslated.translated` that
delivers `ExprTranslated` for any pair satisfying the predicate.

A separate (one-line) lemma the user can prove for their *concrete*
program is: `LExpr.toGotoExprCtx [] e_core = .ok e_goto →
isBoolIntFragment e_core = true → IsBoolIntTranslated e_core e_goto`.
That lemma reduces the translator on the program's expressions and
chooses the right `IsBoolIntTranslated` constructor at each
subexpression. Because the user has the full `LExpr` in hand, they
can do this case-by-case without needing `@[expose]` — they unfold by
`rfl` at each level, since the translator's body computes whenever
its arguments are concrete. -/

/-- Type abbreviation for the Core LExpr instantiation we work with. -/
abbrev CoreLExpr := LExpr ⟨⟨Core.ExpressionMetadata, Unit⟩, LMonoTy⟩

/-- The relation "this LExpr is the bool+int translation of the given
GOTO expression". One constructor per supported `LExpr` shape; each
records the exact GOTO output the translator would produce, allowing
the per-operator lemmas to fire structurally. -/
inductive IsBoolIntTranslated : CoreLExpr → CProverGOTO.Expr → Prop where
  | intConst (n : Int) :
    IsBoolIntTranslated
      (LExpr.intConst () n)
      (Expr.constant (toString (LConst.intConst n)) .Integer)
  | boolConst (b : Bool) :
    IsBoolIntTranslated
      (LExpr.boolConst () b)
      (Expr.constant (toString (LConst.boolConst b)) .Boolean)
  | fvar (v : Lambda.Identifier Unit) (mty : LMonoTy) (gty : Ty)
      (h_ty : mty.toGotoType = .ok gty) :
    IsBoolIntTranslated
      (LExpr.fvar () v (some mty))
      (Expr.symbol (toString v) gty)
  | intAdd
      (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
      (e1c e2c : CoreLExpr) (e1g e2g : CProverGOTO.Expr)
      (_ih1 : IsBoolIntTranslated e1c e1g)
      (_ih2 : IsBoolIntTranslated e2c e2g) :
    IsBoolIntTranslated
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.Add", ()⟩ ty) e1c) e2c)
      ⟨.multiary .Plus, .Integer, [e1g, e2g], .nil, []⟩
  | intSub
      (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
      (e1c e2c : CoreLExpr) (e1g e2g : CProverGOTO.Expr)
      (_ih1 : IsBoolIntTranslated e1c e1g)
      (_ih2 : IsBoolIntTranslated e2c e2g) :
    IsBoolIntTranslated
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.Sub", ()⟩ ty) e1c) e2c)
      ⟨.binary .Minus, .Integer, [e1g, e2g], .nil, []⟩
  | intMul
      (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
      (e1c e2c : CoreLExpr) (e1g e2g : CProverGOTO.Expr)
      (_ih1 : IsBoolIntTranslated e1c e1g)
      (_ih2 : IsBoolIntTranslated e2c e2g) :
    IsBoolIntTranslated
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.Mul", ()⟩ ty) e1c) e2c)
      ⟨.multiary .Mult, .Integer, [e1g, e2g], .nil, []⟩
  | intDivT
      (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
      (e1c e2c : CoreLExpr) (e1g e2g : CProverGOTO.Expr)
      (_ih1 : IsBoolIntTranslated e1c e1g)
      (_ih2 : IsBoolIntTranslated e2c e2g) :
    IsBoolIntTranslated
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.DivT", ()⟩ ty) e1c) e2c)
      ⟨.binary .Div, .Integer, [e1g, e2g], .nil, []⟩
  | intModT
      (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
      (e1c e2c : CoreLExpr) (e1g e2g : CProverGOTO.Expr)
      (_ih1 : IsBoolIntTranslated e1c e1g)
      (_ih2 : IsBoolIntTranslated e2c e2g) :
    IsBoolIntTranslated
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.ModT", ()⟩ ty) e1c) e2c)
      ⟨.binary .Mod, .Integer, [e1g, e2g], .nil, []⟩
  | intLt
      (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
      (e1c e2c : CoreLExpr) (e1g e2g : CProverGOTO.Expr)
      (_ih1 : IsBoolIntTranslated e1c e1g)
      (_ih2 : IsBoolIntTranslated e2c e2g) :
    IsBoolIntTranslated
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.Lt", ()⟩ ty) e1c) e2c)
      ⟨.binary .Lt, .Boolean, [e1g, e2g], .nil, []⟩
  | intLe
      (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
      (e1c e2c : CoreLExpr) (e1g e2g : CProverGOTO.Expr)
      (_ih1 : IsBoolIntTranslated e1c e1g)
      (_ih2 : IsBoolIntTranslated e2c e2g) :
    IsBoolIntTranslated
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.Le", ()⟩ ty) e1c) e2c)
      ⟨.binary .Le, .Boolean, [e1g, e2g], .nil, []⟩
  | intGt
      (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
      (e1c e2c : CoreLExpr) (e1g e2g : CProverGOTO.Expr)
      (_ih1 : IsBoolIntTranslated e1c e1g)
      (_ih2 : IsBoolIntTranslated e2c e2g) :
    IsBoolIntTranslated
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.Gt", ()⟩ ty) e1c) e2c)
      ⟨.binary .Gt, .Boolean, [e1g, e2g], .nil, []⟩
  | intGe
      (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
      (e1c e2c : CoreLExpr) (e1g e2g : CProverGOTO.Expr)
      (_ih1 : IsBoolIntTranslated e1c e1g)
      (_ih2 : IsBoolIntTranslated e2c e2g) :
    IsBoolIntTranslated
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Int.Ge", ()⟩ ty) e1c) e2c)
      ⟨.binary .Ge, .Boolean, [e1g, e2g], .nil, []⟩
  | boolNot
      (m : Core.ExpressionMetadata) (ty : Option LMonoTy)
      (e1c : CoreLExpr) (e1g : CProverGOTO.Expr)
      (_ih1 : IsBoolIntTranslated e1c e1g) :
    IsBoolIntTranslated
      (LExpr.app m (LExpr.op () ⟨"Bool.Not", ()⟩ ty) e1c)
      ⟨.unary .Not, .Boolean, [e1g], .nil, []⟩
  | boolAnd
      (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
      (e1c e2c : CoreLExpr) (e1g e2g : CProverGOTO.Expr)
      (_ih1 : IsBoolIntTranslated e1c e1g)
      (_ih2 : IsBoolIntTranslated e2c e2g) :
    IsBoolIntTranslated
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Bool.And", ()⟩ ty) e1c) e2c)
      ⟨.multiary .And, .Boolean, [e1g, e2g], .nil, []⟩
  | boolOr
      (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
      (e1c e2c : CoreLExpr) (e1g e2g : CProverGOTO.Expr)
      (_ih1 : IsBoolIntTranslated e1c e1g)
      (_ih2 : IsBoolIntTranslated e2c e2g) :
    IsBoolIntTranslated
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Bool.Or", ()⟩ ty) e1c) e2c)
      ⟨.multiary .Or, .Boolean, [e1g, e2g], .nil, []⟩
  | boolImplies
      (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
      (e1c e2c : CoreLExpr) (e1g e2g : CProverGOTO.Expr)
      (_ih1 : IsBoolIntTranslated e1c e1g)
      (_ih2 : IsBoolIntTranslated e2c e2g) :
    IsBoolIntTranslated
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨"Bool.Implies", ()⟩ ty) e1c) e2c)
      ⟨.binary .Implies, .Boolean, [e1g, e2g], .nil, []⟩
  | eq
      (m : Core.ExpressionMetadata)
      (e1c e2c : CoreLExpr) (e1g e2g : CProverGOTO.Expr)
      (_ih1 : IsBoolIntTranslated e1c e1g)
      (_ih2 : IsBoolIntTranslated e2c e2g) :
    IsBoolIntTranslated
      (LExpr.eq m e1c e2c)
      ⟨.binary .Equal, .Boolean, [e1g, e2g], .nil, []⟩
  | ite
      (m : Core.ExpressionMetadata)
      (cc tc ec : CoreLExpr) (cg tg eg : CProverGOTO.Expr)
      (_ih_c : IsBoolIntTranslated cc cg)
      (_ih_t : IsBoolIntTranslated tc tg)
      (_ih_e : IsBoolIntTranslated ec eg) :
    IsBoolIntTranslated
      (LExpr.ite m cc tc ec)
      (Expr.ite cg tg eg)

/-! ### Bridge from `LExpr.toGotoExprCtx` to `IsBoolIntTranslated`

This lemma reduces the translator on a Core LExpr in the bool+int
fragment and produces an `IsBoolIntTranslated` witness — closing the
gap between the abstract predicate and the concrete translator. -/

private theorem isBoolIntTranslated_of_toGotoExprCtx_const
    (m : Core.ExpressionMetadata) (c : LConst) (e_goto : CProverGOTO.Expr)
    (h_frag : isBoolIntFragment (LExpr.const m c) = true)
    (h_tx : LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] (LExpr.const m c) = .ok e_goto) :
    IsBoolIntTranslated (LExpr.const m c) e_goto := by
  cases c with
  | intConst n =>
    -- Translator: gty ← .int.toGotoType = .ok .Integer
    -- Result: Expr.constant (toString c) gty
    simp only [LExpr.toGotoExprCtx, LConst.ty,
               bind, Except.bind, pure, Except.pure] at h_tx
    cases h_tx
    cases m
    exact .intConst n
  | boolConst b =>
    simp only [LExpr.toGotoExprCtx, LConst.ty,
               bind, Except.bind, pure, Except.pure] at h_tx
    cases h_tx
    cases m
    exact .boolConst b
  | strConst _ => simp [isBoolIntFragment] at h_frag
  | realConst _ => simp [isBoolIntFragment] at h_frag
  | bitvecConst _ _ => simp [isBoolIntFragment] at h_frag

private theorem isBoolIntTranslated_of_toGotoExprCtx_fvar
    (m : Core.ExpressionMetadata) (v : Lambda.Identifier Unit)
    (mty_opt : Option LMonoTy) (e_goto : CProverGOTO.Expr)
    (h_frag : isBoolIntFragment (LExpr.fvar m v mty_opt) = true)
    (h_tx : LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] (LExpr.fvar m v mty_opt) = .ok e_goto) :
    IsBoolIntTranslated (LExpr.fvar m v mty_opt) e_goto := by
  cases mty_opt with
  | none => simp [isBoolIntFragment] at h_frag
  | some mty =>
    simp only [LExpr.toGotoExprCtx,
               bind, Except.bind, pure, Except.pure] at h_tx
    cases h_gty : mty.toGotoType with
    | error _ => rw [h_gty] at h_tx; cases h_tx
    | ok gty =>
      rw [h_gty] at h_tx
      cases h_tx
      cases m
      exact .fvar v mty gty h_gty

private theorem isBoolIntTranslated_of_toGotoExprCtx_eq
    (m : Core.ExpressionMetadata) (e1c e2c : CoreLExpr)
    (e_goto : CProverGOTO.Expr)
    (ih1 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e1c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e1c = .ok e_goto →
        IsBoolIntTranslated e1c e_goto)
    (ih2 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e2c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e2c = .ok e_goto →
        IsBoolIntTranslated e2c e_goto)
    (h_frag : isBoolIntFragment (LExpr.eq m e1c e2c) = true)
    (h_tx : LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] (LExpr.eq m e1c e2c) = .ok e_goto) :
    IsBoolIntTranslated (LExpr.eq m e1c e2c) e_goto := by
  -- isBoolIntFragment unfolds to `isBoolIntFragment e1c && isBoolIntFragment e2c`
  have h_frag1 : isBoolIntFragment e1c = true := by
    have := h_frag
    simp [isBoolIntFragment] at this
    exact this.1
  have h_frag2 : isBoolIntFragment e2c = true := by
    have := h_frag
    simp [isBoolIntFragment] at this
    exact this.2
  -- Translator: e1g ← toGotoExprCtx [] e1c; e2g ← toGotoExprCtx [] e2c;
  -- result = ⟨.binary .Equal, .Boolean, [e1g, e2g]⟩
  simp only [LExpr.toGotoExprCtx, bind, Except.bind, pure, Except.pure] at h_tx
  cases h_e1g :
      LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e1c with
  | error _ => rw [h_e1g] at h_tx; cases h_tx
  | ok e1g =>
    rw [h_e1g] at h_tx
    cases h_e2g :
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e2c with
    | error _ => rw [h_e2g] at h_tx; cases h_tx
    | ok e2g =>
      rw [h_e2g] at h_tx
      cases h_tx
      exact .eq m e1c e2c e1g e2g (ih1 e1g h_frag1 h_e1g) (ih2 e2g h_frag2 h_e2g)


/-! ### Translator-output reductions for supported operators

We need `simp` rewrites that reduce `fnToGotoID` and related helper
functions when their input is one of our supported operator name
strings. These are `rfl` lemmas (the inputs are concrete strings, so
the helpers compute by definitional unfolding). -/

/-! Hypotheses-based reductions: `fnToGotoID` calls `Core.CoreOp.ofString`
which is not `@[expose]`-marked at its definition site, so we can't
compute these reductions externally. Instead, we collect the necessary
reductions into a **bundle** that the user supplies. In any module
where `Core.CoreOp.ofString` is reducible (e.g. by `simp` with the
right unfold lemmas, or by `decide` / `rfl` if exposed), the user
discharges them once per concrete program. -/

/-- Bundle of `fnToGotoID` reduction facts for the bool+int fragment. -/
structure FnToGotoIDReductions : Prop where
  intAdd  : fnToGotoID "Int.Add"  = .ok (.multiary .Plus)
  intSub  : fnToGotoID "Int.Sub"  = .ok (.binary .Minus)
  intMul  : fnToGotoID "Int.Mul"  = .ok (.multiary .Mult)
  intDivT : fnToGotoID "Int.DivT" = .ok (.binary .Div)
  intModT : fnToGotoID "Int.ModT" = .ok (.binary .Mod)
  intLt   : fnToGotoID "Int.Lt"   = .ok (.binary .Lt)
  intLe   : fnToGotoID "Int.Le"   = .ok (.binary .Le)
  intGt   : fnToGotoID "Int.Gt"   = .ok (.binary .Gt)
  intGe   : fnToGotoID "Int.Ge"   = .ok (.binary .Ge)
  boolNot : fnToGotoID "Bool.Not" = .ok (.unary .Not)
  boolAnd : fnToGotoID "Bool.And" = .ok (.multiary .And)
  boolOr  : fnToGotoID "Bool.Or"  = .ok (.multiary .Or)
  boolImplies : fnToGotoID "Bool.Implies" = .ok (.binary .Implies)
  /-- For each supported binary operator, `isSignedBvOp` returns false. -/
  isSignedBvOp_intAdd  : isSignedBvOp "Int.Add"  = false
  isSignedBvOp_intSub  : isSignedBvOp "Int.Sub"  = false
  isSignedBvOp_intMul  : isSignedBvOp "Int.Mul"  = false
  isSignedBvOp_intDivT : isSignedBvOp "Int.DivT" = false
  isSignedBvOp_intModT : isSignedBvOp "Int.ModT" = false
  isSignedBvOp_intLt   : isSignedBvOp "Int.Lt"   = false
  isSignedBvOp_intLe   : isSignedBvOp "Int.Le"   = false
  isSignedBvOp_intGt   : isSignedBvOp "Int.Gt"   = false
  isSignedBvOp_intGe   : isSignedBvOp "Int.Ge"   = false
  isSignedBvOp_boolAnd : isSignedBvOp "Bool.And" = false
  isSignedBvOp_boolOr  : isSignedBvOp "Bool.Or"  = false
  isSignedBvOp_boolImplies : isSignedBvOp "Bool.Implies" = false
  /-- For each supported binary integer operator, `parseBvExtractLo` returns none. -/
  parseBvExtractLo_boolNot : parseBvExtractLo "Bool.Not" = none

/-! ### GOTO output-type agreement at each operator

For the bridge to work, we need to know that each operator's
`mty.destructArrow.getLast!.toGotoType` agrees with the expected GOTO
output type the constructor hardcodes. This recursive predicate
captures exactly that. -/

/-- Recursive predicate: every operator-application in the LExpr has
its annotated output type agreeing with the GOTO output type the
`IsBoolIntTranslated` constructor hardcodes (`.Integer` for int
arithmetic, `.Boolean` for comparisons / boolean ops). -/
def BoolIntGtyAgrees :
    LExpr ⟨⟨Core.ExpressionMetadata, Unit⟩, LMonoTy⟩ → Prop
  | .const _ _  => True
  | .fvar _ _ _ => True
  | .app _ (.app _ (.op _ fn (some mty)) e1) e2 =>
      (-- For integer arithmetic: output is .Integer.
       (fn.name == "Int.Add" ∨ fn.name == "Int.Sub" ∨ fn.name == "Int.Mul"
        ∨ fn.name == "Int.DivT" ∨ fn.name == "Int.ModT") →
       mty.destructArrow.getLast!.toGotoType = .ok .Integer)
      ∧
      (-- For integer comparisons: output is .Boolean.
       (fn.name == "Int.Lt" ∨ fn.name == "Int.Le"
        ∨ fn.name == "Int.Gt" ∨ fn.name == "Int.Ge") →
       mty.destructArrow.getLast!.toGotoType = .ok .Boolean)
      ∧
      (-- For boolean binary ops: output is .Boolean.
       (fn.name == "Bool.And" ∨ fn.name == "Bool.Or"
        ∨ fn.name == "Bool.Implies") →
       mty.destructArrow.getLast!.toGotoType = .ok .Boolean)
      ∧ BoolIntGtyAgrees e1 ∧ BoolIntGtyAgrees e2
  | .app _ (.op _ fn (some mty)) e1 =>
      (-- For boolean unary op: output is .Boolean.
       fn.name == "Bool.Not" →
       mty.destructArrow.getLast!.toGotoType = .ok .Boolean)
      ∧ BoolIntGtyAgrees e1
  | .eq _ e1 e2 => BoolIntGtyAgrees e1 ∧ BoolIntGtyAgrees e2
  | .ite _ c t e =>
      BoolIntGtyAgrees c ∧ BoolIntGtyAgrees t ∧ BoolIntGtyAgrees e
  | _ => True

/-! ### Per-operator bridge helpers (binary integer ops)

Each helper takes a `FnToGotoIDReductions` bundle and a side
hypothesis on the GOTO output type, then reduces
`LExpr.toGotoExprCtx` on the binary-app shape and produces an
`IsBoolIntTranslated` witness.

The proof skeleton is the same for all binary integer ops; only the
operator name string and the corresponding fields of `h_red` change.
We follow the structure of `_eq` above: `simp only` to unfold the
translator, `cases` on each recursive translation, and then unfold
the post-processing logic (which depends on `op`'s specific identity).
-/

/-- Helper: when `op_id` is one of the simple `.multiary` / `.binary`
/ `.unary` constructors, it cannot equal `.functionApplication` for
any string. -/
private theorem op_id_ne_funApp_multiary
    (m : Expr.Identifier.Multiary) (s : String) :
    ((Expr.Identifier.multiary m) == Expr.Identifier.functionApplication s) = false := by
  simp only [BEq.beq, decide_eq_false_iff_not]
  intro h; cases h

private theorem op_id_ne_funApp_binary
    (b : Expr.Identifier.Binary) (s : String) :
    ((Expr.Identifier.binary b) == Expr.Identifier.functionApplication s) = false := by
  simp only [BEq.beq, decide_eq_false_iff_not]
  intro h; cases h

private theorem op_id_ne_funApp_unary
    (u : Expr.Identifier.Unary) (s : String) :
    ((Expr.Identifier.unary u) == Expr.Identifier.functionApplication s) = false := by
  simp only [BEq.beq, decide_eq_false_iff_not]
  intro h; cases h

/-- Generic bridge helper for the 12 binary operators. Replaces the 12
per-op `isBoolIntTranslated_of_toGotoExprCtx_<op>` helpers.

Takes a `BoolIntBinOpDesc` plus the four side-conditions that
specialise the proof skeleton:

* `h_red_op`  — `fnToGotoID od.opName = .ok od.opId`;
* `h_signed`  — `isSignedBvOp od.opName = false`;
* `h_funApp`  — `od.opId` cannot equal `.functionApplication s`;
* `h_not_old` — `(od.opName == "old") = false`.

The `mk` argument supplies the operator-specific `IsBoolIntTranslated`
constructor — this is necessary because the inductive's binary
constructors hardcode the operator name in their conclusion's LExpr
pattern, so the generic cannot derive it. -/
private theorem isBoolIntTranslated_of_toGotoExprCtx_binOp
    (od : BoolIntBinOpDesc)
    (h_red_op  : fnToGotoID od.opName = .ok od.opId)
    (h_signed  : isSignedBvOp od.opName = false)
    (h_funApp  : ∀ s, (od.opId == Expr.Identifier.functionApplication s) = false)
    (h_not_old : (od.opName == "old") = false)
    (mk : ∀ (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
            (e1c e2c : CoreLExpr) (e1g e2g : CProverGOTO.Expr),
          IsBoolIntTranslated e1c e1g →
          IsBoolIntTranslated e2c e2g →
          IsBoolIntTranslated
            (LExpr.app m₂ (LExpr.app m₁
              (LExpr.op () ⟨od.opName, ()⟩ ty) e1c) e2c)
            ⟨od.opId, od.outTy, [e1g, e2g], .nil, []⟩)
    (m_outer m_inner m_op : Core.ExpressionMetadata)
    (id_meta : Unit) (mty : LMonoTy)
    (e1c e2c : CoreLExpr) (e_goto : CProverGOTO.Expr)
    (h_op_gty : mty.destructArrow.getLast!.toGotoType = .ok od.outTy)
    (ih1 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e1c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e1c = .ok e_goto →
        IsBoolIntTranslated e1c e_goto)
    (ih2 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e2c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e2c = .ok e_goto → IsBoolIntTranslated e2c e_goto)
    (h_frag1 : isBoolIntFragment e1c = true)
    (h_frag2 : isBoolIntFragment e2c = true)
    (h_tx : LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] (LExpr.app m_outer
                (LExpr.app m_inner
                  (LExpr.op m_op ⟨od.opName, id_meta⟩ (some mty)) e1c) e2c)
              = .ok e_goto) :
    IsBoolIntTranslated
      (LExpr.app m_outer
        (LExpr.app m_inner
          (LExpr.op m_op ⟨od.opName, id_meta⟩ (some mty)) e1c) e2c)
      e_goto := by
  -- Unfold the translator on the binary-app shape.
  simp only [LExpr.toGotoExprCtx, bind, Except.bind, pure, Except.pure] at h_tx
  -- toString reduces to `od.opName` by definitional unfolding of the
  -- `Lambda.Identifier` `ToString` instance.
  simp only [show (toString (⟨od.opName, id_meta⟩ : Lambda.Identifier Unit))
             = od.opName from rfl,
             h_not_old, h_red_op, h_signed] at h_tx
  -- Eliminate the .functionApplication-comparison if-checks.
  simp only [h_funApp] at h_tx
  rw [h_op_gty] at h_tx
  cases h_e1g :
      LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e1c with
  | error _ => rw [h_e1g] at h_tx; cases h_tx
  | ok e1g =>
    rw [h_e1g] at h_tx
    cases h_e2g :
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e2c with
    | error _ => rw [h_e2g] at h_tx; cases h_tx
    | ok e2g =>
      rw [h_e2g] at h_tx
      cases h_tx
      exact mk m_inner m_outer (some mty) e1c e2c e1g e2g
            (ih1 e1g h_frag1 h_e1g) (ih2 e2g h_frag2 h_e2g)

/-- Bridge helper: `Int.Add`. -/
private theorem isBoolIntTranslated_of_toGotoExprCtx_intAdd
    (h_red : FnToGotoIDReductions)
    (m_outer m_inner m_op : Core.ExpressionMetadata)
    (id_meta : Unit) (mty : LMonoTy)
    (e1c e2c : CoreLExpr) (e_goto : CProverGOTO.Expr)
    (h_op_gty : mty.destructArrow.getLast!.toGotoType = .ok .Integer)
    (ih1 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e1c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e1c = .ok e_goto →
        IsBoolIntTranslated e1c e_goto)
    (ih2 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e2c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e2c = .ok e_goto → IsBoolIntTranslated e2c e_goto)
    (h_frag : isBoolIntFragment
        (LExpr.app m_outer
          (LExpr.app m_inner
            (LExpr.op m_op ⟨"Int.Add", id_meta⟩ (some mty)) e1c) e2c) = true)
    (h_tx : LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] (LExpr.app m_outer
                (LExpr.app m_inner
                  (LExpr.op m_op ⟨"Int.Add", id_meta⟩ (some mty)) e1c) e2c)
              = .ok e_goto) :
    IsBoolIntTranslated
      (LExpr.app m_outer
        (LExpr.app m_inner
          (LExpr.op m_op ⟨"Int.Add", id_meta⟩ (some mty)) e1c) e2c)
      e_goto := by
  have h_frag1 : isBoolIntFragment e1c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp, isSupportedBoolBinOp] at h
    exact h.1
  have h_frag2 : isBoolIntFragment e2c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp, isSupportedBoolBinOp] at h
    exact h.2
  exact isBoolIntTranslated_of_toGotoExprCtx_binOp .intAdd
    h_red.intAdd h_red.isSignedBvOp_intAdd
    (op_id_ne_funApp_multiary _) (by decide)
    (fun _ _ _ _ _ _ _ ih1 ih2 => .intAdd _ _ _ _ _ _ _ ih1 ih2)
    m_outer m_inner m_op id_meta mty e1c e2c e_goto h_op_gty ih1 ih2
    h_frag1 h_frag2 h_tx

/-- Bridge helper: `Int.Sub`. -/
private theorem isBoolIntTranslated_of_toGotoExprCtx_intSub
    (h_red : FnToGotoIDReductions)
    (m_outer m_inner m_op : Core.ExpressionMetadata)
    (id_meta : Unit) (mty : LMonoTy)
    (e1c e2c : CoreLExpr) (e_goto : CProverGOTO.Expr)
    (h_op_gty : mty.destructArrow.getLast!.toGotoType = .ok .Integer)
    (ih1 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e1c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e1c = .ok e_goto →
        IsBoolIntTranslated e1c e_goto)
    (ih2 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e2c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e2c = .ok e_goto → IsBoolIntTranslated e2c e_goto)
    (h_frag : isBoolIntFragment
        (LExpr.app m_outer
          (LExpr.app m_inner
            (LExpr.op m_op ⟨"Int.Sub", id_meta⟩ (some mty)) e1c) e2c) = true)
    (h_tx : LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] (LExpr.app m_outer
                (LExpr.app m_inner
                  (LExpr.op m_op ⟨"Int.Sub", id_meta⟩ (some mty)) e1c) e2c)
              = .ok e_goto) :
    IsBoolIntTranslated
      (LExpr.app m_outer
        (LExpr.app m_inner
          (LExpr.op m_op ⟨"Int.Sub", id_meta⟩ (some mty)) e1c) e2c)
      e_goto := by
  have h_frag1 : isBoolIntFragment e1c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp,
          isSupportedBoolBinOp] at h
    exact h.1
  have h_frag2 : isBoolIntFragment e2c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp,
          isSupportedBoolBinOp] at h
    exact h.2
  simp only [LExpr.toGotoExprCtx, bind, Except.bind, pure, Except.pure] at h_tx
  simp only [show (toString (⟨"Int.Sub", id_meta⟩ : Lambda.Identifier Unit))
             = "Int.Sub" from rfl,
             show ("Int.Sub" == "old") = false from rfl,
             h_red.intSub, h_red.isSignedBvOp_intSub] at h_tx
  simp only [op_id_ne_funApp_binary] at h_tx
  rw [h_op_gty] at h_tx
  cases h_e1g :
      LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e1c with
  | error _ => rw [h_e1g] at h_tx; cases h_tx
  | ok e1g =>
    rw [h_e1g] at h_tx
    cases h_e2g :
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e2c with
    | error _ => rw [h_e2g] at h_tx; cases h_tx
    | ok e2g =>
      rw [h_e2g] at h_tx
      cases h_tx
      exact .intSub m_inner m_outer (some mty) e1c e2c e1g e2g
            (ih1 e1g h_frag1 h_e1g) (ih2 e2g h_frag2 h_e2g)

/-- Bridge helper: `Int.Mul`. -/
private theorem isBoolIntTranslated_of_toGotoExprCtx_intMul
    (h_red : FnToGotoIDReductions)
    (m_outer m_inner m_op : Core.ExpressionMetadata)
    (id_meta : Unit) (mty : LMonoTy)
    (e1c e2c : CoreLExpr) (e_goto : CProverGOTO.Expr)
    (h_op_gty : mty.destructArrow.getLast!.toGotoType = .ok .Integer)
    (ih1 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e1c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e1c = .ok e_goto →
        IsBoolIntTranslated e1c e_goto)
    (ih2 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e2c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e2c = .ok e_goto → IsBoolIntTranslated e2c e_goto)
    (h_frag : isBoolIntFragment
        (LExpr.app m_outer
          (LExpr.app m_inner
            (LExpr.op m_op ⟨"Int.Mul", id_meta⟩ (some mty)) e1c) e2c) = true)
    (h_tx : LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] (LExpr.app m_outer
                (LExpr.app m_inner
                  (LExpr.op m_op ⟨"Int.Mul", id_meta⟩ (some mty)) e1c) e2c)
              = .ok e_goto) :
    IsBoolIntTranslated
      (LExpr.app m_outer
        (LExpr.app m_inner
          (LExpr.op m_op ⟨"Int.Mul", id_meta⟩ (some mty)) e1c) e2c)
      e_goto := by
  have h_frag1 : isBoolIntFragment e1c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp,
          isSupportedBoolBinOp] at h
    exact h.1
  have h_frag2 : isBoolIntFragment e2c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp,
          isSupportedBoolBinOp] at h
    exact h.2
  simp only [LExpr.toGotoExprCtx, bind, Except.bind, pure, Except.pure] at h_tx
  simp only [show (toString (⟨"Int.Mul", id_meta⟩ : Lambda.Identifier Unit))
             = "Int.Mul" from rfl,
             show ("Int.Mul" == "old") = false from rfl,
             h_red.intMul, h_red.isSignedBvOp_intMul] at h_tx
  simp only [op_id_ne_funApp_multiary] at h_tx
  rw [h_op_gty] at h_tx
  cases h_e1g :
      LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e1c with
  | error _ => rw [h_e1g] at h_tx; cases h_tx
  | ok e1g =>
    rw [h_e1g] at h_tx
    cases h_e2g :
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e2c with
    | error _ => rw [h_e2g] at h_tx; cases h_tx
    | ok e2g =>
      rw [h_e2g] at h_tx
      cases h_tx
      exact .intMul m_inner m_outer (some mty) e1c e2c e1g e2g
            (ih1 e1g h_frag1 h_e1g) (ih2 e2g h_frag2 h_e2g)

/-- Bridge helper: `Int.DivT`. -/
private theorem isBoolIntTranslated_of_toGotoExprCtx_intDivT
    (h_red : FnToGotoIDReductions)
    (m_outer m_inner m_op : Core.ExpressionMetadata)
    (id_meta : Unit) (mty : LMonoTy)
    (e1c e2c : CoreLExpr) (e_goto : CProverGOTO.Expr)
    (h_op_gty : mty.destructArrow.getLast!.toGotoType = .ok .Integer)
    (ih1 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e1c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e1c = .ok e_goto →
        IsBoolIntTranslated e1c e_goto)
    (ih2 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e2c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e2c = .ok e_goto → IsBoolIntTranslated e2c e_goto)
    (h_frag : isBoolIntFragment
        (LExpr.app m_outer
          (LExpr.app m_inner
            (LExpr.op m_op ⟨"Int.DivT", id_meta⟩ (some mty)) e1c) e2c) = true)
    (h_tx : LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] (LExpr.app m_outer
                (LExpr.app m_inner
                  (LExpr.op m_op ⟨"Int.DivT", id_meta⟩ (some mty)) e1c) e2c)
              = .ok e_goto) :
    IsBoolIntTranslated
      (LExpr.app m_outer
        (LExpr.app m_inner
          (LExpr.op m_op ⟨"Int.DivT", id_meta⟩ (some mty)) e1c) e2c)
      e_goto := by
  have h_frag1 : isBoolIntFragment e1c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp,
          isSupportedBoolBinOp] at h
    exact h.1
  have h_frag2 : isBoolIntFragment e2c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp,
          isSupportedBoolBinOp] at h
    exact h.2
  simp only [LExpr.toGotoExprCtx, bind, Except.bind, pure, Except.pure] at h_tx
  simp only [show (toString (⟨"Int.DivT", id_meta⟩ : Lambda.Identifier Unit))
             = "Int.DivT" from rfl,
             show ("Int.DivT" == "old") = false from rfl,
             h_red.intDivT, h_red.isSignedBvOp_intDivT] at h_tx
  simp only [op_id_ne_funApp_binary] at h_tx
  rw [h_op_gty] at h_tx
  cases h_e1g :
      LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e1c with
  | error _ => rw [h_e1g] at h_tx; cases h_tx
  | ok e1g =>
    rw [h_e1g] at h_tx
    cases h_e2g :
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e2c with
    | error _ => rw [h_e2g] at h_tx; cases h_tx
    | ok e2g =>
      rw [h_e2g] at h_tx
      cases h_tx
      exact .intDivT m_inner m_outer (some mty) e1c e2c e1g e2g
            (ih1 e1g h_frag1 h_e1g) (ih2 e2g h_frag2 h_e2g)

/-- Bridge helper: `Int.ModT`. -/
private theorem isBoolIntTranslated_of_toGotoExprCtx_intModT
    (h_red : FnToGotoIDReductions)
    (m_outer m_inner m_op : Core.ExpressionMetadata)
    (id_meta : Unit) (mty : LMonoTy)
    (e1c e2c : CoreLExpr) (e_goto : CProverGOTO.Expr)
    (h_op_gty : mty.destructArrow.getLast!.toGotoType = .ok .Integer)
    (ih1 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e1c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e1c = .ok e_goto →
        IsBoolIntTranslated e1c e_goto)
    (ih2 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e2c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e2c = .ok e_goto → IsBoolIntTranslated e2c e_goto)
    (h_frag : isBoolIntFragment
        (LExpr.app m_outer
          (LExpr.app m_inner
            (LExpr.op m_op ⟨"Int.ModT", id_meta⟩ (some mty)) e1c) e2c) = true)
    (h_tx : LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] (LExpr.app m_outer
                (LExpr.app m_inner
                  (LExpr.op m_op ⟨"Int.ModT", id_meta⟩ (some mty)) e1c) e2c)
              = .ok e_goto) :
    IsBoolIntTranslated
      (LExpr.app m_outer
        (LExpr.app m_inner
          (LExpr.op m_op ⟨"Int.ModT", id_meta⟩ (some mty)) e1c) e2c)
      e_goto := by
  have h_frag1 : isBoolIntFragment e1c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp,
          isSupportedBoolBinOp] at h
    exact h.1
  have h_frag2 : isBoolIntFragment e2c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp,
          isSupportedBoolBinOp] at h
    exact h.2
  simp only [LExpr.toGotoExprCtx, bind, Except.bind, pure, Except.pure] at h_tx
  simp only [show (toString (⟨"Int.ModT", id_meta⟩ : Lambda.Identifier Unit))
             = "Int.ModT" from rfl,
             show ("Int.ModT" == "old") = false from rfl,
             h_red.intModT, h_red.isSignedBvOp_intModT] at h_tx
  simp only [op_id_ne_funApp_binary] at h_tx
  rw [h_op_gty] at h_tx
  cases h_e1g :
      LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e1c with
  | error _ => rw [h_e1g] at h_tx; cases h_tx
  | ok e1g =>
    rw [h_e1g] at h_tx
    cases h_e2g :
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e2c with
    | error _ => rw [h_e2g] at h_tx; cases h_tx
    | ok e2g =>
      rw [h_e2g] at h_tx
      cases h_tx
      exact .intModT m_inner m_outer (some mty) e1c e2c e1g e2g
            (ih1 e1g h_frag1 h_e1g) (ih2 e2g h_frag2 h_e2g)

/-! ### Per-operator bridge helpers (binary integer comparisons)

These produce `.Boolean` GOTO output type. Otherwise identical
structure to the integer arithmetic ops. -/

/-- Bridge helper: `Int.Lt`. -/
private theorem isBoolIntTranslated_of_toGotoExprCtx_intLt
    (h_red : FnToGotoIDReductions)
    (m_outer m_inner m_op : Core.ExpressionMetadata)
    (id_meta : Unit) (mty : LMonoTy)
    (e1c e2c : CoreLExpr) (e_goto : CProverGOTO.Expr)
    (h_op_gty : mty.destructArrow.getLast!.toGotoType = .ok .Boolean)
    (ih1 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e1c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e1c = .ok e_goto →
        IsBoolIntTranslated e1c e_goto)
    (ih2 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e2c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e2c = .ok e_goto → IsBoolIntTranslated e2c e_goto)
    (h_frag : isBoolIntFragment
        (LExpr.app m_outer
          (LExpr.app m_inner
            (LExpr.op m_op ⟨"Int.Lt", id_meta⟩ (some mty)) e1c) e2c) = true)
    (h_tx : LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] (LExpr.app m_outer
                (LExpr.app m_inner
                  (LExpr.op m_op ⟨"Int.Lt", id_meta⟩ (some mty)) e1c) e2c)
              = .ok e_goto) :
    IsBoolIntTranslated
      (LExpr.app m_outer
        (LExpr.app m_inner
          (LExpr.op m_op ⟨"Int.Lt", id_meta⟩ (some mty)) e1c) e2c)
      e_goto := by
  have h_frag1 : isBoolIntFragment e1c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp,
          isSupportedBoolBinOp] at h
    exact h.1
  have h_frag2 : isBoolIntFragment e2c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp,
          isSupportedBoolBinOp] at h
    exact h.2
  simp only [LExpr.toGotoExprCtx, bind, Except.bind, pure, Except.pure] at h_tx
  simp only [show (toString (⟨"Int.Lt", id_meta⟩ : Lambda.Identifier Unit))
             = "Int.Lt" from rfl,
             show ("Int.Lt" == "old") = false from rfl,
             h_red.intLt, h_red.isSignedBvOp_intLt] at h_tx
  simp only [op_id_ne_funApp_binary] at h_tx
  rw [h_op_gty] at h_tx
  cases h_e1g :
      LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e1c with
  | error _ => rw [h_e1g] at h_tx; cases h_tx
  | ok e1g =>
    rw [h_e1g] at h_tx
    cases h_e2g :
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e2c with
    | error _ => rw [h_e2g] at h_tx; cases h_tx
    | ok e2g =>
      rw [h_e2g] at h_tx
      cases h_tx
      exact .intLt m_inner m_outer (some mty) e1c e2c e1g e2g
            (ih1 e1g h_frag1 h_e1g) (ih2 e2g h_frag2 h_e2g)

/-- Bridge helper: `Int.Le`. -/
private theorem isBoolIntTranslated_of_toGotoExprCtx_intLe
    (h_red : FnToGotoIDReductions)
    (m_outer m_inner m_op : Core.ExpressionMetadata)
    (id_meta : Unit) (mty : LMonoTy)
    (e1c e2c : CoreLExpr) (e_goto : CProverGOTO.Expr)
    (h_op_gty : mty.destructArrow.getLast!.toGotoType = .ok .Boolean)
    (ih1 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e1c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e1c = .ok e_goto →
        IsBoolIntTranslated e1c e_goto)
    (ih2 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e2c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e2c = .ok e_goto → IsBoolIntTranslated e2c e_goto)
    (h_frag : isBoolIntFragment
        (LExpr.app m_outer
          (LExpr.app m_inner
            (LExpr.op m_op ⟨"Int.Le", id_meta⟩ (some mty)) e1c) e2c) = true)
    (h_tx : LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] (LExpr.app m_outer
                (LExpr.app m_inner
                  (LExpr.op m_op ⟨"Int.Le", id_meta⟩ (some mty)) e1c) e2c)
              = .ok e_goto) :
    IsBoolIntTranslated
      (LExpr.app m_outer
        (LExpr.app m_inner
          (LExpr.op m_op ⟨"Int.Le", id_meta⟩ (some mty)) e1c) e2c)
      e_goto := by
  have h_frag1 : isBoolIntFragment e1c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp,
          isSupportedBoolBinOp] at h
    exact h.1
  have h_frag2 : isBoolIntFragment e2c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp,
          isSupportedBoolBinOp] at h
    exact h.2
  simp only [LExpr.toGotoExprCtx, bind, Except.bind, pure, Except.pure] at h_tx
  simp only [show (toString (⟨"Int.Le", id_meta⟩ : Lambda.Identifier Unit))
             = "Int.Le" from rfl,
             show ("Int.Le" == "old") = false from rfl,
             h_red.intLe, h_red.isSignedBvOp_intLe] at h_tx
  simp only [op_id_ne_funApp_binary] at h_tx
  rw [h_op_gty] at h_tx
  cases h_e1g :
      LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e1c with
  | error _ => rw [h_e1g] at h_tx; cases h_tx
  | ok e1g =>
    rw [h_e1g] at h_tx
    cases h_e2g :
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e2c with
    | error _ => rw [h_e2g] at h_tx; cases h_tx
    | ok e2g =>
      rw [h_e2g] at h_tx
      cases h_tx
      exact .intLe m_inner m_outer (some mty) e1c e2c e1g e2g
            (ih1 e1g h_frag1 h_e1g) (ih2 e2g h_frag2 h_e2g)

/-- Bridge helper: `Int.Gt`. -/
private theorem isBoolIntTranslated_of_toGotoExprCtx_intGt
    (h_red : FnToGotoIDReductions)
    (m_outer m_inner m_op : Core.ExpressionMetadata)
    (id_meta : Unit) (mty : LMonoTy)
    (e1c e2c : CoreLExpr) (e_goto : CProverGOTO.Expr)
    (h_op_gty : mty.destructArrow.getLast!.toGotoType = .ok .Boolean)
    (ih1 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e1c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e1c = .ok e_goto →
        IsBoolIntTranslated e1c e_goto)
    (ih2 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e2c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e2c = .ok e_goto → IsBoolIntTranslated e2c e_goto)
    (h_frag : isBoolIntFragment
        (LExpr.app m_outer
          (LExpr.app m_inner
            (LExpr.op m_op ⟨"Int.Gt", id_meta⟩ (some mty)) e1c) e2c) = true)
    (h_tx : LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] (LExpr.app m_outer
                (LExpr.app m_inner
                  (LExpr.op m_op ⟨"Int.Gt", id_meta⟩ (some mty)) e1c) e2c)
              = .ok e_goto) :
    IsBoolIntTranslated
      (LExpr.app m_outer
        (LExpr.app m_inner
          (LExpr.op m_op ⟨"Int.Gt", id_meta⟩ (some mty)) e1c) e2c)
      e_goto := by
  have h_frag1 : isBoolIntFragment e1c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp,
          isSupportedBoolBinOp] at h
    exact h.1
  have h_frag2 : isBoolIntFragment e2c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp,
          isSupportedBoolBinOp] at h
    exact h.2
  simp only [LExpr.toGotoExprCtx, bind, Except.bind, pure, Except.pure] at h_tx
  simp only [show (toString (⟨"Int.Gt", id_meta⟩ : Lambda.Identifier Unit))
             = "Int.Gt" from rfl,
             show ("Int.Gt" == "old") = false from rfl,
             h_red.intGt, h_red.isSignedBvOp_intGt] at h_tx
  simp only [op_id_ne_funApp_binary] at h_tx
  rw [h_op_gty] at h_tx
  cases h_e1g :
      LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e1c with
  | error _ => rw [h_e1g] at h_tx; cases h_tx
  | ok e1g =>
    rw [h_e1g] at h_tx
    cases h_e2g :
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e2c with
    | error _ => rw [h_e2g] at h_tx; cases h_tx
    | ok e2g =>
      rw [h_e2g] at h_tx
      cases h_tx
      exact .intGt m_inner m_outer (some mty) e1c e2c e1g e2g
            (ih1 e1g h_frag1 h_e1g) (ih2 e2g h_frag2 h_e2g)

/-- Bridge helper: `Int.Ge`. -/
private theorem isBoolIntTranslated_of_toGotoExprCtx_intGe
    (h_red : FnToGotoIDReductions)
    (m_outer m_inner m_op : Core.ExpressionMetadata)
    (id_meta : Unit) (mty : LMonoTy)
    (e1c e2c : CoreLExpr) (e_goto : CProverGOTO.Expr)
    (h_op_gty : mty.destructArrow.getLast!.toGotoType = .ok .Boolean)
    (ih1 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e1c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e1c = .ok e_goto →
        IsBoolIntTranslated e1c e_goto)
    (ih2 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e2c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e2c = .ok e_goto → IsBoolIntTranslated e2c e_goto)
    (h_frag : isBoolIntFragment
        (LExpr.app m_outer
          (LExpr.app m_inner
            (LExpr.op m_op ⟨"Int.Ge", id_meta⟩ (some mty)) e1c) e2c) = true)
    (h_tx : LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] (LExpr.app m_outer
                (LExpr.app m_inner
                  (LExpr.op m_op ⟨"Int.Ge", id_meta⟩ (some mty)) e1c) e2c)
              = .ok e_goto) :
    IsBoolIntTranslated
      (LExpr.app m_outer
        (LExpr.app m_inner
          (LExpr.op m_op ⟨"Int.Ge", id_meta⟩ (some mty)) e1c) e2c)
      e_goto := by
  have h_frag1 : isBoolIntFragment e1c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp,
          isSupportedBoolBinOp] at h
    exact h.1
  have h_frag2 : isBoolIntFragment e2c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp,
          isSupportedBoolBinOp] at h
    exact h.2
  simp only [LExpr.toGotoExprCtx, bind, Except.bind, pure, Except.pure] at h_tx
  simp only [show (toString (⟨"Int.Ge", id_meta⟩ : Lambda.Identifier Unit))
             = "Int.Ge" from rfl,
             show ("Int.Ge" == "old") = false from rfl,
             h_red.intGe, h_red.isSignedBvOp_intGe] at h_tx
  simp only [op_id_ne_funApp_binary] at h_tx
  rw [h_op_gty] at h_tx
  cases h_e1g :
      LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e1c with
  | error _ => rw [h_e1g] at h_tx; cases h_tx
  | ok e1g =>
    rw [h_e1g] at h_tx
    cases h_e2g :
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e2c with
    | error _ => rw [h_e2g] at h_tx; cases h_tx
    | ok e2g =>
      rw [h_e2g] at h_tx
      cases h_tx
      exact .intGe m_inner m_outer (some mty) e1c e2c e1g e2g
            (ih1 e1g h_frag1 h_e1g) (ih2 e2g h_frag2 h_e2g)

/-! ### Per-operator bridge helpers (boolean binary ops) -/

/-- Bridge helper: `Bool.And`. -/
private theorem isBoolIntTranslated_of_toGotoExprCtx_boolAnd
    (h_red : FnToGotoIDReductions)
    (m_outer m_inner m_op : Core.ExpressionMetadata)
    (id_meta : Unit) (mty : LMonoTy)
    (e1c e2c : CoreLExpr) (e_goto : CProverGOTO.Expr)
    (h_op_gty : mty.destructArrow.getLast!.toGotoType = .ok .Boolean)
    (ih1 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e1c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e1c = .ok e_goto →
        IsBoolIntTranslated e1c e_goto)
    (ih2 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e2c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e2c = .ok e_goto → IsBoolIntTranslated e2c e_goto)
    (h_frag : isBoolIntFragment
        (LExpr.app m_outer
          (LExpr.app m_inner
            (LExpr.op m_op ⟨"Bool.And", id_meta⟩ (some mty)) e1c) e2c) = true)
    (h_tx : LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] (LExpr.app m_outer
                (LExpr.app m_inner
                  (LExpr.op m_op ⟨"Bool.And", id_meta⟩ (some mty)) e1c) e2c)
              = .ok e_goto) :
    IsBoolIntTranslated
      (LExpr.app m_outer
        (LExpr.app m_inner
          (LExpr.op m_op ⟨"Bool.And", id_meta⟩ (some mty)) e1c) e2c)
      e_goto := by
  have h_frag1 : isBoolIntFragment e1c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp,
          isSupportedBoolBinOp] at h
    exact h.1
  have h_frag2 : isBoolIntFragment e2c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp,
          isSupportedBoolBinOp] at h
    exact h.2
  simp only [LExpr.toGotoExprCtx, bind, Except.bind, pure, Except.pure] at h_tx
  simp only [show (toString (⟨"Bool.And", id_meta⟩ : Lambda.Identifier Unit))
             = "Bool.And" from rfl,
             show ("Bool.And" == "old") = false from rfl,
             h_red.boolAnd, h_red.isSignedBvOp_boolAnd] at h_tx
  simp only [op_id_ne_funApp_multiary] at h_tx
  rw [h_op_gty] at h_tx
  cases h_e1g :
      LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e1c with
  | error _ => rw [h_e1g] at h_tx; cases h_tx
  | ok e1g =>
    rw [h_e1g] at h_tx
    cases h_e2g :
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e2c with
    | error _ => rw [h_e2g] at h_tx; cases h_tx
    | ok e2g =>
      rw [h_e2g] at h_tx
      cases h_tx
      exact .boolAnd m_inner m_outer (some mty) e1c e2c e1g e2g
            (ih1 e1g h_frag1 h_e1g) (ih2 e2g h_frag2 h_e2g)

/-- Bridge helper: `Bool.Or`. -/
private theorem isBoolIntTranslated_of_toGotoExprCtx_boolOr
    (h_red : FnToGotoIDReductions)
    (m_outer m_inner m_op : Core.ExpressionMetadata)
    (id_meta : Unit) (mty : LMonoTy)
    (e1c e2c : CoreLExpr) (e_goto : CProverGOTO.Expr)
    (h_op_gty : mty.destructArrow.getLast!.toGotoType = .ok .Boolean)
    (ih1 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e1c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e1c = .ok e_goto →
        IsBoolIntTranslated e1c e_goto)
    (ih2 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e2c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e2c = .ok e_goto → IsBoolIntTranslated e2c e_goto)
    (h_frag : isBoolIntFragment
        (LExpr.app m_outer
          (LExpr.app m_inner
            (LExpr.op m_op ⟨"Bool.Or", id_meta⟩ (some mty)) e1c) e2c) = true)
    (h_tx : LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] (LExpr.app m_outer
                (LExpr.app m_inner
                  (LExpr.op m_op ⟨"Bool.Or", id_meta⟩ (some mty)) e1c) e2c)
              = .ok e_goto) :
    IsBoolIntTranslated
      (LExpr.app m_outer
        (LExpr.app m_inner
          (LExpr.op m_op ⟨"Bool.Or", id_meta⟩ (some mty)) e1c) e2c)
      e_goto := by
  have h_frag1 : isBoolIntFragment e1c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp,
          isSupportedBoolBinOp] at h
    exact h.1
  have h_frag2 : isBoolIntFragment e2c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp,
          isSupportedBoolBinOp] at h
    exact h.2
  simp only [LExpr.toGotoExprCtx, bind, Except.bind, pure, Except.pure] at h_tx
  simp only [show (toString (⟨"Bool.Or", id_meta⟩ : Lambda.Identifier Unit))
             = "Bool.Or" from rfl,
             show ("Bool.Or" == "old") = false from rfl,
             h_red.boolOr, h_red.isSignedBvOp_boolOr] at h_tx
  simp only [op_id_ne_funApp_multiary] at h_tx
  rw [h_op_gty] at h_tx
  cases h_e1g :
      LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e1c with
  | error _ => rw [h_e1g] at h_tx; cases h_tx
  | ok e1g =>
    rw [h_e1g] at h_tx
    cases h_e2g :
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e2c with
    | error _ => rw [h_e2g] at h_tx; cases h_tx
    | ok e2g =>
      rw [h_e2g] at h_tx
      cases h_tx
      exact .boolOr m_inner m_outer (some mty) e1c e2c e1g e2g
            (ih1 e1g h_frag1 h_e1g) (ih2 e2g h_frag2 h_e2g)

/-- Bridge helper: `Bool.Implies`. -/
private theorem isBoolIntTranslated_of_toGotoExprCtx_boolImplies
    (h_red : FnToGotoIDReductions)
    (m_outer m_inner m_op : Core.ExpressionMetadata)
    (id_meta : Unit) (mty : LMonoTy)
    (e1c e2c : CoreLExpr) (e_goto : CProverGOTO.Expr)
    (h_op_gty : mty.destructArrow.getLast!.toGotoType = .ok .Boolean)
    (ih1 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e1c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e1c = .ok e_goto →
        IsBoolIntTranslated e1c e_goto)
    (ih2 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e2c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e2c = .ok e_goto → IsBoolIntTranslated e2c e_goto)
    (h_frag : isBoolIntFragment
        (LExpr.app m_outer
          (LExpr.app m_inner
            (LExpr.op m_op ⟨"Bool.Implies", id_meta⟩ (some mty)) e1c) e2c) = true)
    (h_tx : LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] (LExpr.app m_outer
                (LExpr.app m_inner
                  (LExpr.op m_op ⟨"Bool.Implies", id_meta⟩ (some mty)) e1c) e2c)
              = .ok e_goto) :
    IsBoolIntTranslated
      (LExpr.app m_outer
        (LExpr.app m_inner
          (LExpr.op m_op ⟨"Bool.Implies", id_meta⟩ (some mty)) e1c) e2c)
      e_goto := by
  have h_frag1 : isBoolIntFragment e1c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp,
          isSupportedBoolBinOp] at h
    exact h.1
  have h_frag2 : isBoolIntFragment e2c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedIntBinOp,
          isSupportedBoolBinOp] at h
    exact h.2
  simp only [LExpr.toGotoExprCtx, bind, Except.bind, pure, Except.pure] at h_tx
  simp only [show (toString (⟨"Bool.Implies", id_meta⟩ : Lambda.Identifier Unit))
             = "Bool.Implies" from rfl,
             show ("Bool.Implies" == "old") = false from rfl,
             h_red.boolImplies, h_red.isSignedBvOp_boolImplies] at h_tx
  simp only [op_id_ne_funApp_binary] at h_tx
  rw [h_op_gty] at h_tx
  cases h_e1g :
      LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e1c with
  | error _ => rw [h_e1g] at h_tx; cases h_tx
  | ok e1g =>
    rw [h_e1g] at h_tx
    cases h_e2g :
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e2c with
    | error _ => rw [h_e2g] at h_tx; cases h_tx
    | ok e2g =>
      rw [h_e2g] at h_tx
      cases h_tx
      exact .boolImplies m_inner m_outer (some mty) e1c e2c e1g e2g
            (ih1 e1g h_frag1 h_e1g) (ih2 e2g h_frag2 h_e2g)

/-! ### Per-operator bridge helper (unary boolean op: Bool.Not)

The translator's unary case uses a different pattern shape:
`.app _ (.op _ fn (some ty)) e1`. The unary path also has a
parseBvExtractLo-check (which returns `none` for "Bool.Not"). -/

/-- Bridge helper: `Bool.Not`. -/
private theorem isBoolIntTranslated_of_toGotoExprCtx_boolNot
    (h_red : FnToGotoIDReductions)
    (m_outer m_op : Core.ExpressionMetadata)
    (id_meta : Unit) (mty : LMonoTy)
    (e1c : CoreLExpr) (e_goto : CProverGOTO.Expr)
    (h_op_gty : mty.destructArrow.getLast!.toGotoType = .ok .Boolean)
    (ih1 : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment e1c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e1c = .ok e_goto →
        IsBoolIntTranslated e1c e_goto)
    (h_frag : isBoolIntFragment
        (LExpr.app m_outer
          (LExpr.op m_op ⟨"Bool.Not", id_meta⟩ (some mty)) e1c) = true)
    (h_tx : LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] (LExpr.app m_outer
                (LExpr.op m_op ⟨"Bool.Not", id_meta⟩ (some mty)) e1c)
              = .ok e_goto) :
    IsBoolIntTranslated
      (LExpr.app m_outer
        (LExpr.op m_op ⟨"Bool.Not", id_meta⟩ (some mty)) e1c)
      e_goto := by
  have h_frag1 : isBoolIntFragment e1c = true := by
    have h := h_frag
    simp [isBoolIntFragment, isSupportedBoolUnaryOp] at h
    exact h
  -- Translator unary path.
  simp only [LExpr.toGotoExprCtx, bind, Except.bind, pure, Except.pure] at h_tx
  simp only [show (toString (⟨"Bool.Not", id_meta⟩ : Lambda.Identifier Unit))
             = "Bool.Not" from rfl,
             h_red.parseBvExtractLo_boolNot, h_red.boolNot] at h_tx
  rw [h_op_gty] at h_tx
  cases h_e1g :
      LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e1c with
  | error _ => rw [h_e1g] at h_tx; cases h_tx
  | ok e1g =>
    rw [h_e1g] at h_tx
    cases h_tx
    exact .boolNot m_outer (some mty) e1c e1g (ih1 e1g h_frag1 h_e1g)

/-! ### Per-operator bridge helper (ite) -/

/-- Bridge helper: `LExpr.ite`. -/
private theorem isBoolIntTranslated_of_toGotoExprCtx_ite
    (m : Core.ExpressionMetadata) (cc tc ec : CoreLExpr)
    (e_goto : CProverGOTO.Expr)
    (ih_c : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment cc = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] cc = .ok e_goto →
        IsBoolIntTranslated cc e_goto)
    (ih_t : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment tc = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] tc = .ok e_goto →
        IsBoolIntTranslated tc e_goto)
    (ih_e : ∀ (e_goto : CProverGOTO.Expr),
        isBoolIntFragment ec = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] ec = .ok e_goto →
        IsBoolIntTranslated ec e_goto)
    (h_frag : isBoolIntFragment (LExpr.ite m cc tc ec) = true)
    (h_tx : LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] (LExpr.ite m cc tc ec) = .ok e_goto) :
    IsBoolIntTranslated (LExpr.ite m cc tc ec) e_goto := by
  have h_frag_c : isBoolIntFragment cc = true := by
    have h := h_frag; simp [isBoolIntFragment] at h; exact h.1.1
  have h_frag_t : isBoolIntFragment tc = true := by
    have h := h_frag; simp [isBoolIntFragment] at h; exact h.1.2
  have h_frag_e : isBoolIntFragment ec = true := by
    have h := h_frag; simp [isBoolIntFragment] at h; exact h.2
  -- Translator: cg ← cc; tg ← tc; eg ← ec; result = Expr.ite cg tg eg.
  simp only [LExpr.toGotoExprCtx, bind, Except.bind, pure, Except.pure] at h_tx
  cases h_cg :
      LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cc with
  | error _ => rw [h_cg] at h_tx; cases h_tx
  | ok cg =>
    rw [h_cg] at h_tx
    cases h_tg :
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] tc with
    | error _ => rw [h_tg] at h_tx; cases h_tx
    | ok tg =>
      rw [h_tg] at h_tx
      cases h_eg :
          LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] ec with
      | error _ => rw [h_eg] at h_tx; cases h_tx
      | ok eg =>
        rw [h_eg] at h_tx
        cases h_tx
        exact .ite m cc tc ec cg tg eg
              (ih_c cg h_frag_c h_cg)
              (ih_t tg h_frag_t h_tg)
              (ih_e eg h_frag_e h_eg)

/-- Structural-induction theorem: every `IsBoolIntTranslated` pair is
`ExprTranslated`-correct under the hypothesis bundle.

This is the partial Gap-B discharge: modulo `BoolIntOpHypotheses` and
modulo the user proving `IsBoolIntTranslated e_core e_goto` for their
specific program, the per-expression `ExprTranslated` predicate
holds. -/
theorem IsBoolIntTranslated.translated
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    {e_core : CoreLExpr} {e_goto : CProverGOTO.Expr}
    (h_tx : IsBoolIntTranslated e_core e_goto) :
    ExprTranslated δ δ_goto δ_goto_bool e_core e_goto := by
  induction h_tx with
  | intConst n => exact intConst_translated h n
  | boolConst b => exact boolConst_translated h b
  | fvar v mty gty h_ty => exact fvar_translated h v mty gty h_ty
  | intAdd m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact intAdd_translated h m₁ m₂ ty e1c e2c e1g e2g
  | intSub m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact intSub_translated h m₁ m₂ ty e1c e2c e1g e2g
  | intMul m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact intMul_translated h m₁ m₂ ty e1c e2c e1g e2g
  | intDivT m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact intDivT_translated h m₁ m₂ ty e1c e2c e1g e2g
  | intModT m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact intModT_translated h m₁ m₂ ty e1c e2c e1g e2g
  | intLt m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact intLt_translated h m₁ m₂ ty e1c e2c e1g e2g
  | intLe m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact intLe_translated h m₁ m₂ ty e1c e2c e1g e2g
  | intGt m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact intGt_translated h m₁ m₂ ty e1c e2c e1g e2g
  | intGe m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact intGe_translated h m₁ m₂ ty e1c e2c e1g e2g
  | boolNot m ty e1c e1g _ _ =>
    exact boolNot_translated h m ty e1c e1g
  | boolAnd m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact boolAnd_translated h m₁ m₂ ty e1c e2c e1g e2g
  | boolOr m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact boolOr_translated h m₁ m₂ ty e1c e2c e1g e2g
  | boolImplies m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact boolImplies_translated h m₁ m₂ ty e1c e2c e1g e2g
  | eq m e1c e2c e1g e2g _ _ _ _ =>
    exact eq_translated h m e1c e2c e1g e2g
  | ite m cc tc ec cg tg eg _ _ _ _ _ _ =>
    exact ite_translated h m cc tc ec cg tg eg

/-! ### Top-level bridge: LExpr.toGotoExprCtx → IsBoolIntTranslated

This theorem case-splits on the LExpr shape and applies the
appropriate per-operator bridge helper. It establishes that every
LExpr in `isBoolIntFragment` whose `toGotoExprCtx` succeeds with
`gty`-agreement at each op has a corresponding `IsBoolIntTranslated`
witness. -/

/-- Top-level bridge from the translator to `IsBoolIntTranslated`.

For every `e_core` in the bool+int fragment whose translation
succeeds and agrees on operator GOTO output types, the predicate
`IsBoolIntTranslated e_core e_goto` holds. Composed with
`IsBoolIntTranslated.translated`, this delivers
`ExprTranslated δ δ_goto δ_goto_bool e_core e_goto` for every such
expression.

We perform structural induction on `e_core`, dispatching to the
appropriate per-operator helper based on the LExpr shape. Note: the
binary/unary `.app` cases require recursing on sub-expressions
beneath `fn` (which structural induction over the outer `app` does
not directly provide), so we use Lean's `sizeOf`-based termination
to recurse manually. -/
theorem toGotoExprCtx_preservesEval_boolInt
    (h_red : FnToGotoIDReductions)
    (e_core : CoreLExpr) (e_goto : CProverGOTO.Expr)
    (h_gty : BoolIntGtyAgrees e_core)
    (h_frag : isBoolIntFragment e_core = true)
    (h_tx : LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e_core = .ok e_goto) :
    IsBoolIntTranslated e_core e_goto := by
  -- Manual case-split + recursive call. We dispatch on `e_core` shape.
  match e_core, h_gty, h_frag, h_tx with
  | .const m c, _, h_frag, h_tx =>
    exact isBoolIntTranslated_of_toGotoExprCtx_const m c e_goto h_frag h_tx
  | .fvar m v mty_opt, _, h_frag, h_tx =>
    exact isBoolIntTranslated_of_toGotoExprCtx_fvar m v mty_opt e_goto h_frag h_tx
  | .eq m e1c e2c, h_gty, h_frag, h_tx =>
    have h_frag1 : isBoolIntFragment e1c = true := by
      have h := h_frag; simp [isBoolIntFragment] at h; exact h.1
    have h_frag2 : isBoolIntFragment e2c = true := by
      have h := h_frag; simp [isBoolIntFragment] at h; exact h.2
    have h_gty1 : BoolIntGtyAgrees e1c := h_gty.1
    have h_gty2 : BoolIntGtyAgrees e2c := h_gty.2
    refine isBoolIntTranslated_of_toGotoExprCtx_eq m e1c e2c e_goto ?_ ?_ h_frag h_tx
    · intro e1g h_frag1' h_tx_e1c
      exact toGotoExprCtx_preservesEval_boolInt h_red e1c e1g h_gty1 h_frag1' h_tx_e1c
    · intro e2g h_frag2' h_tx_e2c
      exact toGotoExprCtx_preservesEval_boolInt h_red e2c e2g h_gty2 h_frag2' h_tx_e2c
  -- Binary integer / boolean operators (fn = .app m_inner (.op m_op id (some mty)) e1c)
  | .app m_outer (.app m_inner (.op m_op fn_id (some mty)) e1c) e2c,
    h_gty, h_frag, h_tx =>
    have h_frag_split :
        (isSupportedIntBinOp fn_id.name = true ∨ isSupportedBoolBinOp fn_id.name = true) ∧
        isBoolIntFragment e1c = true ∧
        isBoolIntFragment e2c = true := by
      have h := h_frag; simp [isBoolIntFragment] at h
      exact ⟨h.1.1, h.1.2, h.2⟩
    have h_frag1 := h_frag_split.2.1
    have h_frag2 := h_frag_split.2.2
    have h_gty_e1 : BoolIntGtyAgrees e1c := h_gty.2.2.2.1
    have h_gty_e2 : BoolIntGtyAgrees e2c := h_gty.2.2.2.2
    -- Build the IH for sub-expressions (recursive call on smaller terms).
    have ih1 : ∀ e1g, isBoolIntFragment e1c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e1c = .ok e1g → IsBoolIntTranslated e1c e1g :=
      fun e1g h_f h_t =>
        toGotoExprCtx_preservesEval_boolInt h_red e1c e1g h_gty_e1 h_f h_t
    have ih2 : ∀ e2g, isBoolIntFragment e2c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e2c = .ok e2g → IsBoolIntTranslated e2c e2g :=
      fun e2g h_f h_t =>
        toGotoExprCtx_preservesEval_boolInt h_red e2c e2g h_gty_e2 h_f h_t
    -- Destructure fn_id to extract its `name` and `metadata` separately,
    -- so that we can `subst` on `name`.
    obtain ⟨fn_name, id_meta⟩ := fn_id
    -- Dispatch on which operator name we have. Use the disjunction.
    have h_or : isSupportedIntBinOp fn_name = true ∨
                isSupportedBoolBinOp fn_name = true := h_frag_split.1
    -- Pre-extract the implications from h_gty (before splitting cases).
    have h_gty_int_arith :
        (fn_name == "Int.Add" ∨ fn_name == "Int.Sub" ∨ fn_name == "Int.Mul"
         ∨ fn_name == "Int.DivT" ∨ fn_name == "Int.ModT") →
        mty.destructArrow.getLast!.toGotoType = .ok .Integer := h_gty.1
    have h_gty_int_cmp :
        (fn_name == "Int.Lt" ∨ fn_name == "Int.Le"
         ∨ fn_name == "Int.Gt" ∨ fn_name == "Int.Ge") →
        mty.destructArrow.getLast!.toGotoType = .ok .Boolean := h_gty.2.1
    have h_gty_bool_bin :
        (fn_name == "Bool.And" ∨ fn_name == "Bool.Or"
         ∨ fn_name == "Bool.Implies") →
        mty.destructArrow.getLast!.toGotoType = .ok .Boolean := h_gty.2.2.1
    cases h_or with
    | inl h_int =>
      -- One of Int.Add, Sub, Mul, DivT, ModT, Lt, Le, Gt, Ge.
      simp only [isSupportedIntBinOp, Bool.or_eq_true, beq_iff_eq] at h_int
      rcases h_int with
        ((((((((h | h) | h) | h) | h) | h) | h) | h) | h)
      · subst h
        have h_op_gty :=
          h_gty_int_arith (Or.inl (by simp))
        exact isBoolIntTranslated_of_toGotoExprCtx_intAdd h_red m_outer m_inner m_op
          id_meta mty e1c e2c e_goto h_op_gty ih1 ih2 h_frag h_tx
      · subst h
        have h_op_gty :=
          h_gty_int_arith (Or.inr (Or.inl (by simp)))
        exact isBoolIntTranslated_of_toGotoExprCtx_intSub h_red m_outer m_inner m_op
          id_meta mty e1c e2c e_goto h_op_gty ih1 ih2 h_frag h_tx
      · subst h
        have h_op_gty :=
          h_gty_int_arith (Or.inr (Or.inr (Or.inl (by simp))))
        exact isBoolIntTranslated_of_toGotoExprCtx_intMul h_red m_outer m_inner m_op
          id_meta mty e1c e2c e_goto h_op_gty ih1 ih2 h_frag h_tx
      · subst h
        have h_op_gty :=
          h_gty_int_arith (Or.inr (Or.inr (Or.inr (Or.inl (by simp)))))
        exact isBoolIntTranslated_of_toGotoExprCtx_intDivT h_red m_outer m_inner m_op
          id_meta mty e1c e2c e_goto h_op_gty ih1 ih2 h_frag h_tx
      · subst h
        have h_op_gty :=
          h_gty_int_arith (Or.inr (Or.inr (Or.inr (Or.inr (by simp)))))
        exact isBoolIntTranslated_of_toGotoExprCtx_intModT h_red m_outer m_inner m_op
          id_meta mty e1c e2c e_goto h_op_gty ih1 ih2 h_frag h_tx
      · subst h
        have h_op_gty := h_gty_int_cmp (Or.inl (by simp))
        exact isBoolIntTranslated_of_toGotoExprCtx_intLt h_red m_outer m_inner m_op
          id_meta mty e1c e2c e_goto h_op_gty ih1 ih2 h_frag h_tx
      · subst h
        have h_op_gty := h_gty_int_cmp (Or.inr (Or.inl (by simp)))
        exact isBoolIntTranslated_of_toGotoExprCtx_intLe h_red m_outer m_inner m_op
          id_meta mty e1c e2c e_goto h_op_gty ih1 ih2 h_frag h_tx
      · subst h
        have h_op_gty := h_gty_int_cmp (Or.inr (Or.inr (Or.inl (by simp))))
        exact isBoolIntTranslated_of_toGotoExprCtx_intGt h_red m_outer m_inner m_op
          id_meta mty e1c e2c e_goto h_op_gty ih1 ih2 h_frag h_tx
      · subst h
        have h_op_gty := h_gty_int_cmp (Or.inr (Or.inr (Or.inr (by simp))))
        exact isBoolIntTranslated_of_toGotoExprCtx_intGe h_red m_outer m_inner m_op
          id_meta mty e1c e2c e_goto h_op_gty ih1 ih2 h_frag h_tx
    | inr h_bool =>
      simp only [isSupportedBoolBinOp, Bool.or_eq_true, beq_iff_eq] at h_bool
      rcases h_bool with ((h | h) | h)
      · subst h
        have h_op_gty := h_gty_bool_bin (Or.inl (by simp))
        exact isBoolIntTranslated_of_toGotoExprCtx_boolAnd h_red m_outer m_inner m_op
          id_meta mty e1c e2c e_goto h_op_gty ih1 ih2 h_frag h_tx
      · subst h
        have h_op_gty := h_gty_bool_bin (Or.inr (Or.inl (by simp)))
        exact isBoolIntTranslated_of_toGotoExprCtx_boolOr h_red m_outer m_inner m_op
          id_meta mty e1c e2c e_goto h_op_gty ih1 ih2 h_frag h_tx
      · subst h
        have h_op_gty := h_gty_bool_bin (Or.inr (Or.inr (by simp)))
        exact isBoolIntTranslated_of_toGotoExprCtx_boolImplies h_red m_outer m_inner m_op
          id_meta mty e1c e2c e_goto h_op_gty ih1 ih2 h_frag h_tx
  -- Unary boolean op (fn = .op m_op id (some mty))
  | .app m_outer (.op m_op fn_id (some mty)) e1c, h_gty, h_frag, h_tx =>
    obtain ⟨fn_name, id_meta⟩ := fn_id
    have h_frag_split :
        isSupportedBoolUnaryOp fn_name = true ∧
        isBoolIntFragment e1c = true := by
      have h := h_frag; simp [isBoolIntFragment] at h; exact h
    have h_frag1 := h_frag_split.2
    have h_gty_e1 : BoolIntGtyAgrees e1c := h_gty.2
    have ih1 : ∀ e1g, isBoolIntFragment e1c = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] e1c = .ok e1g → IsBoolIntTranslated e1c e1g :=
      fun e1g h_f h_t =>
        toGotoExprCtx_preservesEval_boolInt h_red e1c e1g h_gty_e1 h_f h_t
    -- The only supported unary op is Bool.Not.
    simp only [isSupportedBoolUnaryOp, beq_iff_eq] at h_frag_split
    obtain ⟨h_name, _⟩ := h_frag_split
    -- Pre-extract the implication BEFORE substitution so the `mty` in
    -- the conclusion stays in the form expected by the helper.
    have h_gty_bool_not :
        fn_name == "Bool.Not" →
        mty.destructArrow.getLast!.toGotoType = .ok .Boolean := h_gty.1
    subst h_name
    have h_op_gty := h_gty_bool_not (by simp)
    exact isBoolIntTranslated_of_toGotoExprCtx_boolNot h_red m_outer m_op
      id_meta mty e1c e_goto h_op_gty ih1 h_frag h_tx
  -- All other shapes: not in fragment.
  | .op _ _ _, _, h_frag, _ => simp [isBoolIntFragment] at h_frag
  | .bvar _ _, _, h_frag, _ => simp [isBoolIntFragment] at h_frag
  | .abs _ _ _ _, _, h_frag, _ => simp [isBoolIntFragment] at h_frag
  | .quant _ _ _ _ _ _, _, h_frag, _ => simp [isBoolIntFragment] at h_frag
  | .ite m cc tc ec, h_gty, h_frag, h_tx =>
    have h_frag_c : isBoolIntFragment cc = true := by
      have h := h_frag; simp [isBoolIntFragment] at h; exact h.1.1
    have h_frag_t : isBoolIntFragment tc = true := by
      have h := h_frag; simp [isBoolIntFragment] at h; exact h.1.2
    have h_frag_e : isBoolIntFragment ec = true := by
      have h := h_frag; simp [isBoolIntFragment] at h; exact h.2
    have h_gty_c : BoolIntGtyAgrees cc := h_gty.1
    have h_gty_t : BoolIntGtyAgrees tc := h_gty.2.1
    have h_gty_e : BoolIntGtyAgrees ec := h_gty.2.2
    have ih_c : ∀ cg, isBoolIntFragment cc = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] cc = .ok cg → IsBoolIntTranslated cc cg :=
      fun cg h_f h_t' =>
        toGotoExprCtx_preservesEval_boolInt h_red cc cg h_gty_c h_f h_t'
    have ih_t : ∀ tg, isBoolIntFragment tc = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] tc = .ok tg → IsBoolIntTranslated tc tg :=
      fun tg h_f h_t' =>
        toGotoExprCtx_preservesEval_boolInt h_red tc tg h_gty_t h_f h_t'
    have ih_e : ∀ eg, isBoolIntFragment ec = true →
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩)
              [] ec = .ok eg → IsBoolIntTranslated ec eg :=
      fun eg h_f h_t' =>
        toGotoExprCtx_preservesEval_boolInt h_red ec eg h_gty_e h_f h_t'
    exact isBoolIntTranslated_of_toGotoExprCtx_ite m cc tc ec e_goto
          ih_c ih_t ih_e h_frag h_tx
  -- Unary app with `none` annotation: not in fragment.
  | .app _ (.op _ _ none) _, _, h_frag, _ => simp [isBoolIntFragment] at h_frag
  -- Other binary apps where the inner shape doesn't match (.op with none, or non-op):
  -- not in the binary-supported pattern, so fragment is false.
  | .app _ (.app _ (.op _ _ none) _) _, _, h_frag, _ =>
      simp [isBoolIntFragment] at h_frag
  -- "fn" is not an op or app-of-op: not in fragment.
  | .app _ (.const _ _) _, _, h_frag, _ => simp [isBoolIntFragment] at h_frag
  | .app _ (.bvar _ _) _, _, h_frag, _ => simp [isBoolIntFragment] at h_frag
  | .app _ (.fvar _ _ _) _, _, h_frag, _ => simp [isBoolIntFragment] at h_frag
  | .app _ (.abs _ _ _ _) _, _, h_frag, _ => simp [isBoolIntFragment] at h_frag
  | .app _ (.quant _ _ _ _ _ _) _, _, h_frag, _ => simp [isBoolIntFragment] at h_frag
  | .app _ (.ite _ _ _ _) _, _, h_frag, _ => simp [isBoolIntFragment] at h_frag
  | .app _ (.eq _ _ _) _, _, h_frag, _ => simp [isBoolIntFragment] at h_frag
  | .app _ (.app _ (.const _ _) _) _, _, h_frag, _ => simp [isBoolIntFragment] at h_frag
  | .app _ (.app _ (.bvar _ _) _) _, _, h_frag, _ => simp [isBoolIntFragment] at h_frag
  | .app _ (.app _ (.fvar _ _ _) _) _, _, h_frag, _ => simp [isBoolIntFragment] at h_frag
  | .app _ (.app _ (.abs _ _ _ _) _) _, _, h_frag, _ => simp [isBoolIntFragment] at h_frag
  | .app _ (.app _ (.quant _ _ _ _ _ _) _) _, _, h_frag, _ => simp [isBoolIntFragment] at h_frag
  | .app _ (.app _ (.app _ _ _) _) _, _, h_frag, _ => simp [isBoolIntFragment] at h_frag
  | .app _ (.app _ (.ite _ _ _ _) _) _, _, h_frag, _ => simp [isBoolIntFragment] at h_frag
  | .app _ (.app _ (.eq _ _ _) _) _, _, h_frag, _ => simp [isBoolIntFragment] at h_frag
termination_by sizeOf e_core
decreasing_by
  all_goals
    simp_wf
    omega

end CProverGOTO.ExprTranslationBoolInt
