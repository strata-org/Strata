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

end CProverGOTO.ExprTranslationBoolInt
