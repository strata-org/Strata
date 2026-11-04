/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdSemantics
public import Strata.Util.ListMap

/-! # What the WP and SSA phases need from an expression language

The WP phase (loop-free program → guarded program) and the SSA phase (guarded program →
obligation program) are generic over the expression language `P`.  Besides the mainline
interfaces (`HasBool`, `HasFvar`, `HasFvars`, `HasSubstFvar`, `HasIdent` and their laws), they
run the operations of `WPOps`:

* identifier names (fresh names are built from a base name and a counter);
* a conditional expression `ite`, from which the phases build `¬`, `∧`, `∨`, guards and lazy
  merges;
* a view of conditional expressions (`iteView?`) with a size that decreases into their parts,
  and a view of Boolean literals (`boolLit?`), with which the SSA phase folds conditions whose
  value is known;
* a substitution by a lookup function (`substFn`), linear in the size of the expression.

Their correctness proofs use the laws of `WPLang`: the free variables of the literals, of a
conditional and of a substitution; the evaluation of a conditional; that the views and
`substFn` agree with the operations they view; and the empty substitution.

The laws that depend on the factory are the mainline predicates `WellFormedSemanticEvalVar`,
`WellFormedSemanticEvalVal`, `WellFormedSemanticEvalExprCongr` and `WellFormedSemanticEvalRename`
(bundled in mainline as `WellFormedSemanticEvalBase`) and `WellFormedSemanticEvalSubstLits`:
substituting variables or Boolean literals holding the values of the substituted variables
preserves evaluation (bundled with the first two for the proofs of the SSA phase as `SSALaws`).

Key definitions: `WPOps`, `WPLang`, `SSALaws`, `notE`, `andE`, `orE`. -/

namespace Imperative
namespace WP

public section

/-- The operations the WP and SSA phases run: identifier names, the conditional expression, a
    view of conditionals with a size decreasing into their parts (the termination measure of the
    SSA folding), a view of Boolean literals, and a substitution by a lookup function.  The laws of
    these operations, which only the correctness proofs use, are those of `WPLang`. -/
class WPOps (P : PureExpr) where
  /-- The name of an identifier. -/
  name : P.Ident → String
  /-- The conditional expression. -/
  ite : P.Expr → P.Expr → P.Expr → P.Expr
  /-- The parts of a conditional expression. -/
  iteView? : P.Expr → Option (P.Expr × P.Expr × P.Expr)
  /-- A size of expressions, decreasing into the parts of a conditional. -/
  size : P.Expr → Nat
  iteView?_size : ∀ {e c t f}, iteView? e = some (c, t, f) →
    size c < size e ∧ size t < size e ∧ size f < size e
  /-- The value of a Boolean literal. -/
  boolLit? : P.Expr → Option Bool
  /-- Substitution of the free variables by a lookup function. -/
  substFn : P.Expr → (P.Ident → Option P.Expr) → P.Expr
  /-- Equality of types, decided. -/
  tyBEq : P.Ty → P.Ty → Bool

/-- The laws of the operations of `WPOps` that the correctness proofs of the WP and SSA phases
    need, beyond the mainline classes: the free variables of the literals, of a conditional and of
    a substitution; the evaluation of a conditional; the views and `substFn` agreeing with the
    operations they view; the empty substitution; and the annotated free variables of a
    conditional and of a substitution, and `tyBEq` deciding type equality. -/
class WPLang (P : PureExpr) [DecidableEq P.Ident] [HasBool P] [HasFvar P] [HasFvars P]
    [HasSubstFvar P] extends WPOps P where
  getFvars_tt : HasFvars.getFvars (HasBool.tt (P := P)) = []
  getFvars_ff : HasFvars.getFvars (HasBool.ff (P := P)) = []
  getFvars_ite : ∀ c t e y, y ∈ HasFvars.getFvars (P := P) (ite c t e) ↔
    y ∈ HasFvars.getFvars c ∨ y ∈ HasFvars.getFvars t ∨ y ∈ HasFvars.getFvars e
  getFvars_substFvars : ∀ (e : P.Expr) (sm : Map P.Ident P.Expr) y,
    y ∈ HasFvars.getFvars (HasSubstFvar.substFvars e sm) →
      (y ∈ HasFvars.getFvars e ∧ Map.find? sm y = none) ∨
      ∃ x v, x ∈ HasFvars.getFvars e ∧ Map.find? sm x = some v ∧ y ∈ HasFvars.getFvars v
  /-- If `getFvar e` is `y`, then `y` is a free variable of `e`. -/
  getFvar_getFvars : ∀ {e : P.Expr} {y : P.Ident}, HasFvar.getFvar e = some y →
    y ∈ HasFvars.getFvars e
  /-- A conditional whose parts are replaced by expressions with the same values (in another
      store) keeps its value.  The law does not assume that a conditional evaluates when only
      the selected branch does: in a denotational language every part must have a value. -/
  ev_ite_congr : ∀ {F σ σ' c t e c' t' e' v}, P.eval F σ (ite c t e) = some v →
    (∀ w, P.eval F σ c = some w → P.eval F σ' c' = some w) →
    (∀ w, P.eval F σ t = some w → P.eval F σ' t' = some w) →
    (∀ w, P.eval F σ e = some w → P.eval F σ' e' = some w) →
    P.eval F σ' (ite c' t' e') = some v
  ev_ite_inv : ∀ {F σ c t e v}, P.eval F σ (ite c t e) = some v →
    (P.eval F σ c = some (HasBool.ttVal F) ∧ P.eval F σ t = some v) ∨
    (P.eval F σ c = some (HasBool.ffVal F) ∧ P.eval F σ e = some v)
  iteView?_eq : ∀ {e c t f}, iteView? e = some (c, t, f) → e = ite c t f
  boolLit?_eq : ∀ {e b}, boolLit? e = some b →
    e = if b then HasBool.tt (P := P) else HasBool.ff (P := P)
  substFn_eq : ∀ (e : P.Expr) (look : P.Ident → Option P.Expr) (sm : Map P.Ident P.Expr),
    (∀ x ∈ HasFvars.getFvars e, look x = Map.find? sm x) →
      substFn e look = HasSubstFvar.substFvars e sm
  /-- Substituting by the empty map leaves the expression unchanged. -/
  substFvars_nil : ∀ e : P.Expr, HasSubstFvar.substFvars e [] = e
  /-- `tyBEq` decides the equality of types. -/
  tyBEq_eq : ∀ {a b : P.Ty}, tyBEq a b = true → a = b
  /-- The annotated free-variable occurrences of a conditional are those of its parts. -/
  getTypedFvars_ite : ∀ c t e p, p ∈ HasFvars.getTypedFvars (P := P) (ite c t e) →
    p ∈ HasFvars.getTypedFvars c ∨ p ∈ HasFvars.getTypedFvars t ∨ p ∈ HasFvars.getTypedFvars e
  /-- An annotated free-variable occurrence of a substitution is one of the expression's, at a
      variable the substitution leaves alone, or one of the image of a substituted variable. -/
  getTypedFvars_substFn : ∀ (e : P.Expr) (g : P.Ident → Option P.Expr) p,
    p ∈ HasFvars.getTypedFvars (substFn e g) →
      (p ∈ HasFvars.getTypedFvars e ∧ g p.1 = none) ∨
      ∃ z v, z ∈ HasFvars.getFvars e ∧ g z = some v ∧ p ∈ HasFvars.getTypedFvars v

variable {P : PureExpr} [DecidableEq P.Ident] [HasBool P] [HasFvar P] [HasFvars P]
  [HasSubstFvar P]

/-- The factory laws the correctness proofs of the SSA phase use: the mainline laws for
    variables and values, and the folding law `WellFormedSemanticEvalSubstLits`. -/
structure SSALaws (f : P.Factory) : Prop where
  /-- Variables evaluate to their value in a well-formed store. -/
  var : WellFormedSemanticEvalVar (P := P) f
  /-- Results are values, and values evaluate to themselves. -/
  val : WellFormedSemanticEvalVal (P := P) f
  /-- Substituting variables or Boolean literals holding the values preserves evaluation. -/
  lits : WellFormedSemanticEvalSubstLits (P := P) f

variable [WPOps P]

/-- The Boolean literal true. -/
abbrev tt : P.Expr := HasBool.tt (P := P)
/-- The Boolean literal false. -/
abbrev ff : P.Expr := HasBool.ff (P := P)

/-- `¬ e` as an `ite`. -/
@[expose] def notE (e : P.Expr) : P.Expr := WPOps.ite e ff tt
/-- `a ∧ b` as an `ite`. -/
@[expose] def andE (a b : P.Expr) : P.Expr := WPOps.ite a b ff
/-- `a ∨ b` as an `ite`. -/
@[expose] def orE (a b : P.Expr) : P.Expr := WPOps.ite a tt b

end -- public section

end WP
end Imperative
