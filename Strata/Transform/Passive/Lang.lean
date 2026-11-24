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
* a view of literals (`lit?`, `sameLit`) and of function values (`lam?`, `recordableLam?`,
  `substLam?`), with which the SSA phase records, substitutes and compares the values of names,
  and the evaluation of an operator
  application on literals (`evalOp?`) under language-chosen operator data (`OpEnv`);
* a substitution by a lookup function (`substFn`), linear in the size of the expression.

Their correctness proofs use the laws of `WPLang`: the free variables of the literals, of a
conditional and of a substitution; the evaluation of a conditional; that the views and
`substFn` agree with the operations they view; the empty substitution; and that `evalOp?` adds no
free variable.

The laws that depend on the factory are the mainline predicates `WellFormedSemanticEvalVar`,
`WellFormedSemanticEvalVal`, `WellFormedSemanticEvalMono`, `WellFormedSemanticEvalExprCongr` and
`WellFormedSemanticEvalRename`, and `WellFormedSemanticEvalSubstExprs`: substituting expressions
holding the values of the substituted variables preserves evaluation; and
`WellFormedSemanticEvalOp`: `evalOp?` under the operator data agrees with the evaluator of the
factory.  The proofs of the SSA phase use them bundled as `SSALaws`, which fix the operator
data.

Key definitions: `WPOps`, `WPLang`, `SSALaws`, `WellFormedSemanticEvalSubstExprs`,
`WellFormedSemanticEvalOp`, `notE`, `andE`, `orE`.

Key theorem: `WellFormedSemanticEvalSubstExprs.substLits` — with the laws for variables and
values, `WellFormedSemanticEvalSubstExprs` gives `WellFormedSemanticEvalSubstLits`. -/

namespace Imperative
namespace WP

public section

/-- The operations the WP and SSA phases run: identifier names, the conditional expression, a
    view of conditionals with a size decreasing into their parts (the termination measure of the
    SSA folding), a view of Boolean literals, views of literals and of function values, the
    evaluation of operator applications on literals, and a substitution by a lookup function.
    The laws of
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
  /-- Whether the SSA phase keeps an assumption with this label when its condition folds to
      `true` (an assumption whose label the verifier reads in an obligation's path condition);
      the SSA phase drops every other such assumption. -/
  keepsTrueAssume : String → Bool := fun _ => false
  /-- Is the expression a literal (a constant of the language)? -/
  lit? : P.Expr → Bool
  /-- Is the expression a function value (an abstraction)? -/
  lam? : P.Expr → Bool
  /-- May the SSA phase record the function value?  The language accepts it only when each of
      its abstractions reads its bound variable at most once (so no beta reduction of it copies
      an argument), or when its body holds no function value. -/
  recordableLam? : P.Expr → Bool
  /-- May the SSA phase write the recorded function value `v` in place of the name `x` in the
      expression `e`, where `atom` accepts the names whose current value is no function value?
      The language accepts it only when no beta reduction of an application of `v` in the result
      copies an argument larger than a literal or a variable (in Core: when `v` reads each of its
      bound variables at most once, or `e` applies `x` only to literals, operators and variables
      `atom` accepts); otherwise `e` reads the name defined for `v`. -/
  substLam? : P.Expr → P.Ident → (P.Ident → Bool) → P.Expr → Bool
  /-- Are the two expressions the same literal? -/
  sameLit : P.Expr → P.Expr → Bool
  /-- The data the evaluation of operator applications reads (in Core, a factory of functions
      with their concrete evaluators). -/
  OpEnv : Type
  /-- The value of an operator application whose arguments are literals, as the operator data
      `oe` evaluates it. -/
  evalOp? : OpEnv → P.Expr → Option P.Expr

/-- The laws of the operations of `WPOps` that the correctness proofs of the WP and SSA phases
    need, beyond the mainline classes: the free variables of the literals, of a conditional and of
    a substitution; the evaluation of a conditional; the views and `substFn` agreeing with the
    operations they view; the empty substitution; the annotated free variables of a
    conditional and of a substitution, and `tyBEq` deciding type equality; `sameLit` holding only
    of equal expressions; and the free variables of the values `evalOp?` gives. -/
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
  iteView?_eval : ∀ {F σ e c t f}, iteView? e = some (c, t, f) →
    P.eval F σ e = P.eval F σ (ite c t f)
  iteView?_getFvars : ∀ {e c t f} (y), iteView? e = some (c, t, f) →
    (y ∈ HasFvars.getFvars e ↔ y ∈ HasFvars.getFvars (ite c t f))
  /-- The annotated free-variable occurrences of a conditional recognized by `iteView?` are
      those of the canonical conditional of its parts: the root's source location carries
      none. -/
  typedFvars_iteView : ∀ {e c t f} (p), iteView? e = some (c, t, f) →
    (p ∈ HasFvars.getTypedFvars e ↔ p ∈ HasFvars.getTypedFvars (ite c t f))
  boolLit?_eval : ∀ {F σ e b}, boolLit? e = some b →
    P.eval F σ e = P.eval F σ (if b then HasBool.tt (P := P) else HasBool.ff (P := P))
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
  /-- Expressions `sameLit` accepts have the same value.  The law is stated on values, not as
      syntactic equality: `sameLit` compares literals up to their metadata, and two occurrences
      of one literal may carry different source locations. -/
  sameLit_eval : ∀ {F σ} {a b : P.Expr}, sameLit a b = true → P.eval F σ a = P.eval F σ b
  /-- The value `evalOp?` gives an expression has no free variable the expression does not
      have. -/
  getFvars_evalOp? : ∀ {oe : OpEnv} {e r : P.Expr}, evalOp? oe e = some r →
    ∀ y ∈ HasFvars.getFvars r, y ∈ HasFvars.getFvars e
  /-- The value `evalOp?` gives an expression has no annotated free-variable occurrence the
      expression does not have. -/
  getTypedFvars_evalOp? : ∀ {oe : OpEnv} {e r : P.Expr}, evalOp? oe e = some r →
    ∀ p ∈ HasFvars.getTypedFvars r, p ∈ HasFvars.getTypedFvars e

variable {P : PureExpr} [DecidableEq P.Ident] [HasBool P] [HasFvar P] [HasFvars P]
  [HasSubstFvar P]

/-- The evaluator commutes with substituting expressions holding the values: substituting, for
    each substituted free variable `k` of `e`, an expression whose value in `σ'` is `k`'s value
    in `σ`, preserves evaluation, when the free variables not substituted agree and both stores
    are well formed.  With the laws for variables and values it gives
    `WellFormedSemanticEvalSubstLits`, whose substituted expressions are variables and Boolean
    literals. -/
@[expose] def WellFormedSemanticEvalSubstExprs (f : P.Factory) : Prop :=
  ∀ {σ σ' : SemanticStore P}, WellFormedStore σ' f → WellFormedStore σ f →
    ∀ (sm : Map P.Ident P.Expr) (e : P.Expr),
    (∀ k ∈ HasFvars.getFvars e, ∀ v, Map.find? sm k = some v →
      (σ k).isSome ∧ P.eval f σ' v = σ k) →
    (∀ x ∈ HasFvars.getFvars e, Map.find? sm x = none → σ' x = σ x) →
    P.eval f σ' (HasSubstFvar.substFvars e sm) = P.eval f σ e

/-- With the laws for variables and values, substituting expressions holding the values
    (`WellFormedSemanticEvalSubstExprs`) gives substituting variables or Boolean literals holding
    them (`WellFormedSemanticEvalSubstLits`). -/
theorem WellFormedSemanticEvalSubstExprs.substLits [HasOps P] [LawfulHasFvar P] {f : P.Factory}
    (h : WellFormedSemanticEvalSubstExprs (P := P) f) (hvar : WellFormedSemanticEvalVar (P := P) f)
    (hval : WellFormedSemanticEvalVal (P := P) f) : WellFormedSemanticEvalSubstLits (P := P) f := by
  intro σ σ' hσ' hσ sm e hsm hrest
  refine h hσ' hσ sm e (fun k _ v hv => ?_) hrest
  rcases hsm k v hv with ⟨y, rfl | ⟨ty, rfl⟩, hy, hs⟩ | ⟨rfl, hk⟩ | ⟨rfl, hk⟩
  · exact ⟨hs, (hvar _ _ _ hσ' (LawfulHasFvar.getFvar_mkFvar y)).trans hy⟩
  · exact ⟨hs, (hvar _ _ _ hσ' (LawfulHasFvar.getFvar_mkTypedFvar y ty)).trans hy⟩
  · exact ⟨by simp [hk], (hval.eval_tt σ').trans hk.symm⟩
  · exact ⟨by simp [hk], (hval.eval_ff σ').trans hk.symm⟩

/-- A free variable of any part of a conditional recognized by `iteView?` is a free variable of
    the conditional itself. -/
theorem getFvars_of_iteView [WPLang P] {e c t f : P.Expr}
    (hv : WPOps.iteView? e = some (c, t, f)) {y : P.Ident}
    (hy : y ∈ HasFvars.getFvars c ∨ y ∈ HasFvars.getFvars t ∨ y ∈ HasFvars.getFvars f) :
    y ∈ HasFvars.getFvars e :=
  (WPLang.iteView?_getFvars y hv).mpr ((WPLang.getFvars_ite c t f y).2 hy)

variable [WPOps P]

/-- The evaluator of the factory `f` agrees with `WPOps.evalOp?` under the operator data `oe`:
    an expression that `evalOp? oe` evaluates to `r` has, in every well-formed store, the value
    of `r` (both have none, or the same one). -/
@[expose] def WellFormedSemanticEvalOp (f : P.Factory) (oe : WPOps.OpEnv P) : Prop :=
  ∀ {σ : SemanticStore P} {e r : P.Expr}, WellFormedStore σ f → WPOps.evalOp? oe e = some r →
    P.eval f σ r = P.eval f σ e

/-- The factory laws the correctness proofs of the SSA phase use: the mainline laws for
    variables, values and monotonicity, the substitution law `WellFormedSemanticEvalSubstExprs`
    and the agreement of the evaluator with `WPOps.evalOp?` under the operator data `oe`. -/
structure SSALaws (f : P.Factory) (oe : WPOps.OpEnv P) : Prop where
  /-- Variables evaluate to their value in a well-formed store. -/
  var : WellFormedSemanticEvalVar (P := P) f
  /-- Results are values, and values evaluate to themselves. -/
  val : WellFormedSemanticEvalVal (P := P) f
  /-- Substituting expressions holding the values of the substituted variables preserves
      evaluation. -/
  exprs : WellFormedSemanticEvalSubstExprs (P := P) f
  /-- A value survives the growth of the store. -/
  mono : WellFormedSemanticEvalMono (P := P) f
  /-- `WPOps.evalOp? oe` agrees with the evaluator. -/
  evalOp : WellFormedSemanticEvalOp (P := P) f oe

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
