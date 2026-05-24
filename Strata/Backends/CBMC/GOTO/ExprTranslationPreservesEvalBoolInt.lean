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
      (Expr.constant (toString (LConst.intConst n)) .Integer) :=
  ExprTranslated.ofValueAgree h _ _ <| by
    intro σ v
    obtain ⟨h_src, h_tgt⟩ := h.intConst_value σ n
    rw [h_src, h_tgt]

/-- `boolConst`: the boolean-constant case. -/
theorem boolConst_translated
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (b : Bool) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.boolConst () b)
      (Expr.constant (toString (LConst.boolConst b)) .Boolean) :=
  ExprTranslated.ofValueAgree h _ _ <| by
    intro σ v
    obtain ⟨h_src, h_tgt, _⟩ := h.boolConst_value σ b
    rw [h_src, h_tgt]

/-! ### Binary operator descriptor

The 12 binary arithmetic-ish operators (`Int.{Add,Sub,Mul,DivT,ModT,
Lt,Le,Gt,Ge}` plus `Bool.{And,Or,Implies}`) share a near-identical proof
skeleton. We factor the per-op data into a `BoolIntBinOpDesc` and
generalise the `_translated` lemmas / bridge helpers via the descriptor. -/

/-- Descriptor for one binary boolean/integer operator: its Core name,
the GOTO `Expr.Identifier` it translates to, and the GOTO output type. -/
structure BoolIntBinOpDesc where
  /-- The Core operator name, e.g. `"Int.Add"`. -/
  opName : String
  /-- The GOTO `Expr.Identifier` for the translated form. -/
  opId   : Expr.Identifier
  /-- The GOTO output type (`.Integer` or `.Boolean`). -/
  outTy  : Ty

namespace BoolIntBinOpDesc

/-- The 12 supported binary operators. Each maps a Core operator name to
its GOTO `Expr.Identifier` and output `Ty`. -/
def intAdd       : BoolIntBinOpDesc := ⟨"Int.Add", .multiary .Plus, .Integer⟩
def intSub       : BoolIntBinOpDesc := ⟨"Int.Sub", .binary .Minus, .Integer⟩
def intMul       : BoolIntBinOpDesc := ⟨"Int.Mul", .multiary .Mult, .Integer⟩
def intDivT      : BoolIntBinOpDesc := ⟨"Int.DivT", .binary .Div, .Integer⟩
def intModT      : BoolIntBinOpDesc := ⟨"Int.ModT", .binary .Mod, .Integer⟩
def intLt        : BoolIntBinOpDesc := ⟨"Int.Lt", .binary .Lt, .Boolean⟩
def intLe        : BoolIntBinOpDesc := ⟨"Int.Le", .binary .Le, .Boolean⟩
def intGt        : BoolIntBinOpDesc := ⟨"Int.Gt", .binary .Gt, .Boolean⟩
def intGe        : BoolIntBinOpDesc := ⟨"Int.Ge", .binary .Ge, .Boolean⟩
def boolAnd      : BoolIntBinOpDesc := ⟨"Bool.And", .multiary .And, .Boolean⟩
def boolOr       : BoolIntBinOpDesc := ⟨"Bool.Or", .multiary .Or, .Boolean⟩
def boolImplies  : BoolIntBinOpDesc := ⟨"Bool.Implies", .binary .Implies, .Boolean⟩

end BoolIntBinOpDesc

/-! ### Per-operator binary lemmas

Each takes a `BoolIntOpHypotheses` field (full value-agreement on the
operator-application) and produces an `ExprTranslated` witness via
`ExprTranslated.ofValueAgree`. -/

/-- Generic per-op `_translated` lemma. `h_corr` has the same shape as
the per-op fields of `BoolIntOpHypotheses`, so call sites pass the field
directly. -/
theorem binOp_translated_of_corr
    {δ : SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (od : BoolIntBinOpDesc)
    (h_corr :
      ∀ σ (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
        (e1c e2c : Core.Expression.Expr)
        (e1g e2g : CProverGOTO.Expr) (v : Core.Expression.Expr),
        δ σ (LExpr.app m₂ (LExpr.app m₁
              (LExpr.op () ⟨od.opName, ()⟩ ty) e1c) e2c) = some v ↔
        δ_goto σ ⟨od.opId, od.outTy, [e1g, e2g], .nil, []⟩ = some v)
    (m₁ m₂ : Core.ExpressionMetadata) (ty : Option LMonoTy)
    (e1c e2c : Core.Expression.Expr) (e1g e2g : CProverGOTO.Expr) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨od.opName, ()⟩ ty) e1c) e2c)
      ⟨od.opId, od.outTy, [e1g, e2g], .nil, []⟩ :=
  ExprTranslated.ofValueAgree h _ _ (h_corr · m₁ m₂ ty e1c e2c e1g e2g)

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

/-! ### Generic bridge helper for binary operators

A single generic theorem handles all 12 binary operators. It takes a
`BoolIntBinOpDesc` plus side-conditions specialising the shared proof
skeleton (see `isBoolIntTranslated_of_toGotoExprCtx_binOp` below), and
the dispatch site in `toGotoExprCtx_preservesEval_boolInt` invokes it
per-operator. -/

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
    exact binOp_translated_of_corr h .intAdd h.intAdd_corr m₁ m₂ ty e1c e2c e1g e2g
  | intSub m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact binOp_translated_of_corr h .intSub h.intSub_corr m₁ m₂ ty e1c e2c e1g e2g
  | intMul m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact binOp_translated_of_corr h .intMul h.intMul_corr m₁ m₂ ty e1c e2c e1g e2g
  | intDivT m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact binOp_translated_of_corr h .intDivT h.intDivT_corr m₁ m₂ ty e1c e2c e1g e2g
  | intModT m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact binOp_translated_of_corr h .intModT h.intModT_corr m₁ m₂ ty e1c e2c e1g e2g
  | intLt m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact binOp_translated_of_corr h .intLt h.intLt_corr m₁ m₂ ty e1c e2c e1g e2g
  | intLe m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact binOp_translated_of_corr h .intLe h.intLe_corr m₁ m₂ ty e1c e2c e1g e2g
  | intGt m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact binOp_translated_of_corr h .intGt h.intGt_corr m₁ m₂ ty e1c e2c e1g e2g
  | intGe m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact binOp_translated_of_corr h .intGe h.intGe_corr m₁ m₂ ty e1c e2c e1g e2g
  | boolNot m ty e1c e1g _ _ => exact boolNot_translated h m ty e1c e1g
  | boolAnd m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact binOp_translated_of_corr h .boolAnd h.boolAnd_corr m₁ m₂ ty e1c e2c e1g e2g
  | boolOr m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact binOp_translated_of_corr h .boolOr h.boolOr_corr m₁ m₂ ty e1c e2c e1g e2g
  | boolImplies m₁ m₂ ty e1c e2c e1g e2g _ _ _ _ =>
    exact binOp_translated_of_corr h .boolImplies h.boolImplies_corr
      m₁ m₂ ty e1c e2c e1g e2g
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
    cases c with
    | intConst n =>
      simp only [LExpr.toGotoExprCtx, LConst.ty,
                 bind, Except.bind, pure, Except.pure] at h_tx
      cases h_tx; cases m; exact .intConst n
    | boolConst b =>
      simp only [LExpr.toGotoExprCtx, LConst.ty,
                 bind, Except.bind, pure, Except.pure] at h_tx
      cases h_tx; cases m; exact .boolConst b
    | strConst _ => simp [isBoolIntFragment] at h_frag
    | realConst _ => simp [isBoolIntFragment] at h_frag
    | bitvecConst _ _ => simp [isBoolIntFragment] at h_frag
  | .fvar m v mty_opt, _, h_frag, h_tx =>
    cases mty_opt with
    | none => simp [isBoolIntFragment] at h_frag
    | some mty =>
      simp only [LExpr.toGotoExprCtx, bind, Except.bind, pure, Except.pure] at h_tx
      cases h_gty : mty.toGotoType with
      | error _ => rw [h_gty] at h_tx; cases h_tx
      | ok gty => rw [h_gty] at h_tx; cases h_tx; cases m; exact .fvar v mty gty h_gty
  | .eq m e1c e2c, h_gty, h_frag, h_tx =>
    have h_frag' := h_frag; simp [isBoolIntFragment] at h_frag'
    have h_gty1 : BoolIntGtyAgrees e1c := h_gty.1
    have h_gty2 : BoolIntGtyAgrees e2c := h_gty.2
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
        rw [h_e2g] at h_tx; cases h_tx
        exact .eq m e1c e2c e1g e2g
          (toGotoExprCtx_preservesEval_boolInt h_red e1c e1g h_gty1 h_frag'.1 h_e1g)
          (toGotoExprCtx_preservesEval_boolInt h_red e2c e2g h_gty2 h_frag'.2 h_e2g)
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
    cases h_or with
    | inl h_int =>
      -- One of Int.Add, Sub, Mul, DivT, ModT, Lt, Le, Gt, Ge.
      simp only [isSupportedIntBinOp, Bool.or_eq_true, beq_iff_eq] at h_int
      rcases h_int with
        ((((((((h | h) | h) | h) | h) | h) | h) | h) | h) <;> subst h
      · exact isBoolIntTranslated_of_toGotoExprCtx_binOp .intAdd
          h_red.intAdd h_red.isSignedBvOp_intAdd
          (op_id_ne_funApp_multiary _) (by decide)
          (fun _ _ _ _ _ _ _ ih1 ih2 => .intAdd _ _ _ _ _ _ _ ih1 ih2)
          m_outer m_inner m_op id_meta mty e1c e2c e_goto
          (h_gty.1 (by simp)) ih1 ih2 h_frag1 h_frag2 h_tx
      · exact isBoolIntTranslated_of_toGotoExprCtx_binOp .intSub
          h_red.intSub h_red.isSignedBvOp_intSub
          (op_id_ne_funApp_binary _) (by decide)
          (fun _ _ _ _ _ _ _ ih1 ih2 => .intSub _ _ _ _ _ _ _ ih1 ih2)
          m_outer m_inner m_op id_meta mty e1c e2c e_goto
          (h_gty.1 (by simp)) ih1 ih2 h_frag1 h_frag2 h_tx
      · exact isBoolIntTranslated_of_toGotoExprCtx_binOp .intMul
          h_red.intMul h_red.isSignedBvOp_intMul
          (op_id_ne_funApp_multiary _) (by decide)
          (fun _ _ _ _ _ _ _ ih1 ih2 => .intMul _ _ _ _ _ _ _ ih1 ih2)
          m_outer m_inner m_op id_meta mty e1c e2c e_goto
          (h_gty.1 (by simp)) ih1 ih2 h_frag1 h_frag2 h_tx
      · exact isBoolIntTranslated_of_toGotoExprCtx_binOp .intDivT
          h_red.intDivT h_red.isSignedBvOp_intDivT
          (op_id_ne_funApp_binary _) (by decide)
          (fun _ _ _ _ _ _ _ ih1 ih2 => .intDivT _ _ _ _ _ _ _ ih1 ih2)
          m_outer m_inner m_op id_meta mty e1c e2c e_goto
          (h_gty.1 (by simp)) ih1 ih2 h_frag1 h_frag2 h_tx
      · exact isBoolIntTranslated_of_toGotoExprCtx_binOp .intModT
          h_red.intModT h_red.isSignedBvOp_intModT
          (op_id_ne_funApp_binary _) (by decide)
          (fun _ _ _ _ _ _ _ ih1 ih2 => .intModT _ _ _ _ _ _ _ ih1 ih2)
          m_outer m_inner m_op id_meta mty e1c e2c e_goto
          (h_gty.1 (by simp)) ih1 ih2 h_frag1 h_frag2 h_tx
      · exact isBoolIntTranslated_of_toGotoExprCtx_binOp .intLt
          h_red.intLt h_red.isSignedBvOp_intLt
          (op_id_ne_funApp_binary _) (by decide)
          (fun _ _ _ _ _ _ _ ih1 ih2 => .intLt _ _ _ _ _ _ _ ih1 ih2)
          m_outer m_inner m_op id_meta mty e1c e2c e_goto
          (h_gty.2.1 (by simp)) ih1 ih2 h_frag1 h_frag2 h_tx
      · exact isBoolIntTranslated_of_toGotoExprCtx_binOp .intLe
          h_red.intLe h_red.isSignedBvOp_intLe
          (op_id_ne_funApp_binary _) (by decide)
          (fun _ _ _ _ _ _ _ ih1 ih2 => .intLe _ _ _ _ _ _ _ ih1 ih2)
          m_outer m_inner m_op id_meta mty e1c e2c e_goto
          (h_gty.2.1 (by simp)) ih1 ih2 h_frag1 h_frag2 h_tx
      · exact isBoolIntTranslated_of_toGotoExprCtx_binOp .intGt
          h_red.intGt h_red.isSignedBvOp_intGt
          (op_id_ne_funApp_binary _) (by decide)
          (fun _ _ _ _ _ _ _ ih1 ih2 => .intGt _ _ _ _ _ _ _ ih1 ih2)
          m_outer m_inner m_op id_meta mty e1c e2c e_goto
          (h_gty.2.1 (by simp)) ih1 ih2 h_frag1 h_frag2 h_tx
      · exact isBoolIntTranslated_of_toGotoExprCtx_binOp .intGe
          h_red.intGe h_red.isSignedBvOp_intGe
          (op_id_ne_funApp_binary _) (by decide)
          (fun _ _ _ _ _ _ _ ih1 ih2 => .intGe _ _ _ _ _ _ _ ih1 ih2)
          m_outer m_inner m_op id_meta mty e1c e2c e_goto
          (h_gty.2.1 (by simp)) ih1 ih2 h_frag1 h_frag2 h_tx
    | inr h_bool =>
      simp only [isSupportedBoolBinOp, Bool.or_eq_true, beq_iff_eq] at h_bool
      rcases h_bool with ((h | h) | h) <;> subst h
      · exact isBoolIntTranslated_of_toGotoExprCtx_binOp .boolAnd
          h_red.boolAnd h_red.isSignedBvOp_boolAnd
          (op_id_ne_funApp_multiary _) (by decide)
          (fun _ _ _ _ _ _ _ ih1 ih2 => .boolAnd _ _ _ _ _ _ _ ih1 ih2)
          m_outer m_inner m_op id_meta mty e1c e2c e_goto
          (h_gty.2.2.1 (by simp)) ih1 ih2 h_frag1 h_frag2 h_tx
      · exact isBoolIntTranslated_of_toGotoExprCtx_binOp .boolOr
          h_red.boolOr h_red.isSignedBvOp_boolOr
          (op_id_ne_funApp_multiary _) (by decide)
          (fun _ _ _ _ _ _ _ ih1 ih2 => .boolOr _ _ _ _ _ _ _ ih1 ih2)
          m_outer m_inner m_op id_meta mty e1c e2c e_goto
          (h_gty.2.2.1 (by simp)) ih1 ih2 h_frag1 h_frag2 h_tx
      · exact isBoolIntTranslated_of_toGotoExprCtx_binOp .boolImplies
          h_red.boolImplies h_red.isSignedBvOp_boolImplies
          (op_id_ne_funApp_binary _) (by decide)
          (fun _ _ _ _ _ _ _ ih1 ih2 => .boolImplies _ _ _ _ _ _ _ ih1 ih2)
          m_outer m_inner m_op id_meta mty e1c e2c e_goto
          (h_gty.2.2.1 (by simp)) ih1 ih2 h_frag1 h_frag2 h_tx
  -- Unary boolean op (fn = .op m_op id (some mty)) — only Bool.Not is supported.
  | .app m_outer (.op m_op fn_id (some mty)) e1c, h_gty, h_frag, h_tx =>
    obtain ⟨fn_name, id_meta⟩ := fn_id
    have h_frag1 : isBoolIntFragment e1c = true := by
      have h := h_frag; simp [isBoolIntFragment, isSupportedBoolUnaryOp] at h; exact h.2
    have h_gty_e1 : BoolIntGtyAgrees e1c := h_gty.2
    have h_name : fn_name = "Bool.Not" := by
      have h := h_frag; simp [isBoolIntFragment, isSupportedBoolUnaryOp] at h; exact h.1
    have h_gty_bool_not :
        fn_name == "Bool.Not" →
        mty.destructArrow.getLast!.toGotoType = .ok .Boolean := h_gty.1
    subst h_name
    have h_op_gty := h_gty_bool_not (by simp)
    simp only [LExpr.toGotoExprCtx, bind, Except.bind, pure, Except.pure] at h_tx
    simp only [show (toString (⟨"Bool.Not", id_meta⟩ : Lambda.Identifier Unit))
               = "Bool.Not" from rfl,
               h_red.parseBvExtractLo_boolNot, h_red.boolNot] at h_tx
    rw [h_op_gty] at h_tx
    cases h_e1g :
        LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e1c with
    | error _ => rw [h_e1g] at h_tx; cases h_tx
    | ok e1g =>
      rw [h_e1g] at h_tx; cases h_tx
      exact .boolNot m_outer (some mty) e1c e1g
        (toGotoExprCtx_preservesEval_boolInt h_red e1c e1g h_gty_e1 h_frag1 h_e1g)
  | .ite m cc tc ec, h_gty, h_frag, h_tx =>
    have h_frag' := h_frag; simp [isBoolIntFragment] at h_frag'
    have h_gty_c : BoolIntGtyAgrees cc := h_gty.1
    have h_gty_t : BoolIntGtyAgrees tc := h_gty.2.1
    have h_gty_e : BoolIntGtyAgrees ec := h_gty.2.2
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
          rw [h_eg] at h_tx; cases h_tx
          exact .ite m cc tc ec cg tg eg
            (toGotoExprCtx_preservesEval_boolInt h_red cc cg h_gty_c h_frag'.1.1 h_cg)
            (toGotoExprCtx_preservesEval_boolInt h_red tc tg h_gty_t h_frag'.1.2 h_tg)
            (toGotoExprCtx_preservesEval_boolInt h_red ec eg h_gty_e h_frag'.2 h_eg)
  -- All remaining shapes: not in fragment.
  | .op _ _ _, _, h_frag, _ | .bvar _ _, _, h_frag, _
  | .abs _ _ _ _, _, h_frag, _ | .quant _ _ _ _ _ _, _, h_frag, _
  | .app _ (.op _ _ none) _, _, h_frag, _
  | .app _ (.app _ (.op _ _ none) _) _, _, h_frag, _
  | .app _ (.const _ _) _, _, h_frag, _ | .app _ (.bvar _ _) _, _, h_frag, _
  | .app _ (.fvar _ _ _) _, _, h_frag, _ | .app _ (.abs _ _ _ _) _, _, h_frag, _
  | .app _ (.quant _ _ _ _ _ _) _, _, h_frag, _
  | .app _ (.ite _ _ _ _) _, _, h_frag, _ | .app _ (.eq _ _ _) _, _, h_frag, _
  | .app _ (.app _ (.const _ _) _) _, _, h_frag, _
  | .app _ (.app _ (.bvar _ _) _) _, _, h_frag, _
  | .app _ (.app _ (.fvar _ _ _) _) _, _, h_frag, _
  | .app _ (.app _ (.abs _ _ _ _) _) _, _, h_frag, _
  | .app _ (.app _ (.quant _ _ _ _ _ _) _) _, _, h_frag, _
  | .app _ (.app _ (.app _ _ _) _) _, _, h_frag, _
  | .app _ (.app _ (.ite _ _ _ _) _) _, _, h_frag, _
  | .app _ (.app _ (.eq _ _ _) _) _, _, h_frag, _ =>
      simp [isBoolIntFragment] at h_frag
termination_by sizeOf e_core
decreasing_by
  all_goals
    simp_wf
    omega

end CProverGOTO.ExprTranslationBoolInt
