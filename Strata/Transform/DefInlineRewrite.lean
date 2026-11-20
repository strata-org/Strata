/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.CoreLang

/-! # Value-keeping rewrites of Core expressions

The normalization `rwAll fac` that the inlining of single-use definitions applies, with the
substitution of the recorded right-hand sides, to the expressions it rewrites in the WP
pipeline's rewrite loop.  It rewrites bottom up, through the
parts of applications, conditionals and equalities (not under binders), each node by `rwRoot`,
which applies in turn:

* `betaNG` (contraction of a redex that does not grow the term): `(λ x. b) a` becomes `b` with
  `a` for `x` when `a` is closed, self-typed at the type of `x`, and a variable or a literal or
  `x` occurs at most once in `b`;
* `decEq` (decided equality): `a == a` becomes `true` when `a` is *self-typed*
  (`selfTyped`: every free-variable occurrence carries a ground annotation and `a` type checks
  at a ground type), so that `a` has a value wherever its annotated variables hold values of
  their annotated types;
* `foldOp fac` (constant folding): an operator application that
  `Imperative.WP.WPOps.evalOp? fac` evaluates becomes that constant;
* `liftIte fac` (an operator into a conditional): an application or an equality with one
  conditional `ite c k₁ k₂` of literals of one type at a position where `Core.WP.opFold` can
  fold through it (`findIte`) becomes
  `ite c r₁ r₂` when the two instances with `k₁` and `k₂` in place of the conditional fold to
  the literals `r₁` and `r₂` of one type;
* `iteSame` (a conditional with equal arms): `ite c t t` becomes `t` when `c` is self-typed at
  `bool`;
* `testCtor fac` (a tester applied to a constructor): an application of a function of `fac` with
  one parameter, such as a datatype's tester, becomes the literal its body and the concrete
  evaluator of the function that body applies give it (`bodyFold`): a tester applied to a
  constructor application with no field of the datatype itself becomes `true` for its own
  constructor and `false` for the others, whatever the fields.

`rwAll fac g e` substitutes `g` into `e` and rewrites the result only when its operator,
abstraction and quantifier annotations are all ground (`annGround`).  The expressions `g`
substitutes are not rewritten again: the inlining substitutes recorded right-hand sides that it
normalized already, so an inlining step rewrites the nodes of `e` and not those of the
expressions it substitutes.

`annGroundWith fl e` is `annGround` of `e` with the ground checks of substituted expressions read
from `fl` instead of from their nodes.

Key definitions: `annGround`, `annGroundWith`, `selfTyped`, `bvarOcc`, `betaNG`, `decEq`,
`foldOp`, `findIte`, `liftIte`, `iteSame`, `constRedex`, `bodyFold`, `testCtor`, `rwRoot`,
`leafRwWith`, `rwBelowWith`, `rwAllWith`, `rwAll`, `ctorRoot`, `rwAllC`. -/

namespace Core
namespace DefInline

open Lambda Imperative

public section

/-- Is the type ground (`LMonoTy.IsGround`)? -/
@[expose] def tyGround (τ : LMonoTy) : Bool := decide τ.IsGround

/-- Are the annotations of the operators, abstractions and quantifiers of `e` all ground? -/
@[expose] def annGround : Expression.Expr → Bool
  | .const _ _ | .bvar _ _ | .fvar _ _ _ => true
  | .op _ _ ty => ty.all tyGround
  | .abs _ _ ty e => ty.all tyGround && annGround e
  | .quant _ _ _ ty tr e => ty.all tyGround && annGround tr && annGround e
  | .app _ f a => annGround f && annGround a
  | .ite _ c t e => annGround c && annGround t && annGround e
  | .eq _ a b => annGround a && annGround b

/-- `annGround` of `e` with every free variable `x` counted as ground exactly when `fl x` holds:
    with `fl x` whether the expression substituted for `x` has ground annotations, the
    annotations of the substituted expression are checked without walking the substituted
    parts. -/
@[expose] def annGroundWith (fl : Expression.Ident → Bool) : Expression.Expr → Bool
  | .const _ _ | .bvar _ _ => true
  | .fvar _ x _ => fl x
  | .op _ _ ty => ty.all tyGround
  | .abs _ _ ty e => ty.all tyGround && annGroundWith fl e
  | .quant _ _ _ ty tr e => ty.all tyGround && annGroundWith fl tr && annGroundWith fl e
  | .app _ f a => annGroundWith fl f && annGroundWith fl a
  | .ite _ c t e => annGroundWith fl c && annGroundWith fl t && annGroundWith fl e
  | .eq _ a b => annGroundWith fl a && annGroundWith fl b

/-- The ground type of a *self-typed* expression: every free-variable occurrence of `e` carries
    a ground annotation, and `e` type checks at a ground type. -/
@[expose] def selfTyped (e : Expression.Expr) : Option LMonoTy :=
  if e.freeVars.all (fun p => p.2.any tyGround) then
    match LExpr.typeCheck [] e with
    | some τ => if tyGround τ then some τ else none
    | none => none
  else none

/-- **Decided equality**, at the root: `a == a` becomes `true` when `a` is self-typed. -/
@[expose] def decEq : Expression.Expr → Expression.Expr
  | e@(.eq _ a b) => if a = b ∧ (selfTyped a).isSome then HasBool.tt else e
  | e => e

/-- **Constant folding**, at the root: an expression that is not a literal and that
    `Imperative.WP.WPOps.evalOp? fac` evaluates becomes the result. -/
@[expose] def foldOp (fac : Lambda.Factory CoreLParams) : Expression.Expr → Expression.Expr
  | e@(.const _ _) => e
  | e => (Imperative.WP.WPOps.evalOp? (P := Expression) fac e).getD e

/-- The expression itself when it is a conditional, otherwise the first conditional found in
    the parts of an application (the function before the argument) or of an equality (the left
    side before the right side), with the expression as a function of what replaces that
    conditional.  The search enters the function of an application, the argument of a Boolean
    negation (`Lambda.boolNotFunc`) and both sides of an equality; the argument of any other
    application counts only when it is itself a conditional.  These are the positions where
    replacing the conditional by a literal can let `Core.WP.opFold` fold the whole expression, so
    the search stays on the spine of the expression and does not walk its arguments. -/
@[expose] def findIte :
    Expression.Expr → Option (Expression.Expr × (Expression.Expr → Expression.Expr))
  | e@(.ite _ _ _ _) => some (e, id)
  | .app m f a =>
    match findIte f with
    | some (s, C) => some (s, fun x => .app m (C x) a)
    | none =>
      if f = (Lambda.boolNotFunc (T := CoreLParams)).opExpr then
        (findIte a).map fun (s, C) => (s, fun x => .app m f (C x))
      else
        match a with
        | .ite .. => some (a, fun x => .app m f x)
        | _ => none
  | .eq m a b =>
    match findIte a with
    | some (s, C) => some (s, fun x => .eq m (C x) b)
    | none => (findIte b).map fun (s, C) => (s, fun x => .eq m a (C x))
  | _ => none

/-- **An operator into a conditional**, at the root: when the first conditional among the parts
    of an application or an equality `e` (`findIte`) is `ite c k₁ k₂` with literals `k₁`, `k₂`
    of one type, and `e` with `k₁`, respectively `k₂`, in its place folds (`opFold fac`) to the
    literals `r₁`, `r₂` of one type, `e` becomes `ite c r₁ r₂`. -/
@[expose] def liftIte (fac : Lambda.Factory CoreLParams) (e : Expression.Expr) :
    Expression.Expr :=
  match findIte e with
  | some (.ite m c (.const m₁ k₁) (.const m₂ k₂), C) =>
    match Core.WP.opFold fac (C (.const m₁ k₁)), Core.WP.opFold fac (C (.const m₂ k₂)) with
    | some r₁, some r₂ =>
      if k₁.ty = k₂.ty ∧ r₁.ty = r₂.ty then .ite m c (.const m₁ r₁) (.const m₂ r₂) else e
    | _, _ => e
  | _ => e

/-- **A conditional with equal arms**, at the root: `ite c t t` becomes `t` when `c` is
    self-typed at `bool`. -/
@[expose] def iteSame : Expression.Expr → Expression.Expr
  | e@(.ite _ c t f) => if t = f ∧ selfTyped c = some .bool then t else e
  | e => e

/-- **A conditional with a literal condition**, at the root: `ite(true, t, f)` becomes `t` and
    `ite(false, t, f)` becomes `f`, when `t` and `f` are self-typed at one type.

    The side condition is what makes the rewrite keep the value, and not merely imply it: a
    conditional has a value only when *both* of its arms have one, of one sort
    (`LExpr.denoteEval_ite_iff`), so dropping the arm the condition does not select would make
    an expression with no value into one with a value unless the dropped arm is known to have
    one.  `selfTyped t = selfTyped f = some τ` gives both arms a value of the type `τ` wherever
    their annotated variables hold values of their annotated types, hence values of one sort.

    This is the rewrite that lets a chain of testers over one value collapse: `testCtor` folds a
    tester applied to a constructor application to a literal, and this rewrite then drops the
    arms the chain does not take, with the functions only they apply, which is what decides
    whether axiom pruning keeps those functions' quantified axioms. -/
@[expose] def iteLit : Expression.Expr → Expression.Expr
  | e@(.ite _ (.const _ (.boolConst b)) t f) =>
    if selfTyped t = selfTyped f ∧ (selfTyped t).isSome then (if b then t else f) else e
  | e => e

/-- The literal `k` of an expression built from `k` by abstractions over annotated types and
    applications, with the number of binders the applications leave unapplied:
    `(λ τ₁ … λ τₙ. k) a₁ … aₘ` gives `n - m` when `m ≤ n`. -/
@[expose] def constRedex : Expression.Expr → Option (Nat × LConst)
  | .const _ k => some (0, k)
  | .abs _ _ (some _) b => (constRedex b).map fun p => (p.1 + 1, p.2)
  | .app _ f _ =>
    match constRedex f with
    | some (n + 1, k) => some (n, k)
    | _ => none
  | _ => none

/-- The literal that an application `t a` of a function `t` of `fac` with one parameter `x`
    folds to by the body of `t` and the concrete evaluator of the function that body applies:
    the operator is annotated with the declared type of `t`, every free-variable occurrence of
    the application is annotated, the body type checks at the output type and annotates `x`
    with its declared type; the body with `a` for `x` is an application of a function of `fac`
    with a concrete evaluator, at an instance of its declared type, to arguments that the
    evaluator maps to `(λ τ₁ … λ τₙ. k) a₁ … aₙ`; and the application and that result type
    check at the type of `k`.  A tester of a datatype is such a function: its body applies the
    eliminator, and the eliminator's evaluator on a constructor application with no recursive
    field gives the case of that constructor, `λ τ₁ … λ τₙ. b`, applied to the fields, with `b`
    the literal `true` for the tested constructor and `false` for the others. -/
@[expose] def bodyFold (fac : Lambda.Factory CoreLParams) : Expression.Expr → Option LConst
  | e@(.app _ (.op _ t (some τt)) a) =>
    match fac[t.name]? with
    | some tf =>
      match tf.inputs.toList, tf.body with
      | [(x, xty)], some body =>
        if tf.name.name = t.name ∧ τt = .arrow xty tf.output ∧
            e.freeVars.all (fun p => p.2.isSome) = true ∧
            LExpr.typeCheck [] body = some tf.output ∧
            body.freeVars.all (fun p => p.1 ≠ x ∨ p.2 = some xty) = true then
          match fac.callOfLFunc (body.substFvarsBy fun y => if y = x then some a else none) with
          | some (.op _ el (some τel), args, ef) =>
            if ef.name.name = el.name ∧
                (Core.WP.tyInst? (LMonoTy.mkArrow' ef.output (ef.inputs.map Prod.snd)) τel).isSome
            then
              match ef.concreteEval.bind (fun ce => ce coreLoc (some τel) args) with
              | some r =>
                match constRedex r with
                | some (0, k) =>
                  if LExpr.typeCheck [] e = some k.ty ∧ LExpr.typeCheck [] r = some k.ty then some k
                  else none
                | _ => none
              | none => none
            else none
          | _ => none
        else none
      | _, _ => none
    | none => none
  | _ => none

/-- **A tester applied to a constructor**, at the root: an application that `bodyFold fac`
    folds becomes that literal. -/
@[expose] def testCtor (fac : Lambda.Factory CoreLParams) (e : Expression.Expr) :
    Expression.Expr :=
  match bodyFold fac e with
  | some k => .const valueLoc k
  | none => e

/-- The number of occurrences of the bound variable of index `k` in `e` (the index grows under
    binders). -/
@[expose] def bvarOcc (k : Nat) : Expression.Expr → Nat
  | .bvar _ i => if i = k then 1 else 0
  | .abs _ _ _ b => bvarOcc (k + 1) b
  | .quant _ _ _ _ tr b => bvarOcc (k + 1) tr + bvarOcc (k + 1) b
  | .app _ f a => bvarOcc k f + bvarOcc k a
  | .ite _ c t f => bvarOcc k c + bvarOcc k t + bvarOcc k f
  | .eq _ a b => bvarOcc k a + bvarOcc k b
  | .const _ _ | .op _ _ _ | .fvar _ _ _ => 0

/-- Is the expression a variable or a literal? -/
@[expose] def isAtom : Expression.Expr → Bool
  | .fvar _ _ _ | .const _ _ => true
  | _ => false

/-- **Contraction of a redex that does not grow the term**, at the root: `(λ x : aty. b) a`
    becomes `b` with `a` for `x` when `a` has no loose bound variable, is self-typed at `aty`,
    and is a variable or a literal or `x` occurs at most once in `b`. -/
@[expose] def betaNG : Expression.Expr → Expression.Expr
  | e@(.app _ (.abs _ _ (some aty) b) a) =>
    if a.lcAt 0 = true ∧ selfTyped a = some aty ∧ (isAtom a = true ∨ bvarOcc 0 b ≤ 1) then
      LExpr.subst (fun _ => a) b
    else e
  | e => e

/-- The rewrites at the root, in turn: `betaNG`, `decEq`, `foldOp fac`, `liftIte fac`,
    `iteSame`, `testCtor fac`. -/
@[expose] def rwRoot (fac : Lambda.Factory CoreLParams) (e : Expression.Expr) : Expression.Expr :=
  testCtor fac (iteSame (liftIte fac (foldOp fac (decEq (betaNG e)))))

/-- A leaf of the bottom-up rewrite at the root rewrite `root`, with the substitution `g`: a
    variable `x` that `g` maps to some `d` becomes `d`, not rewritten again; any other
    expression, with `g` substituted (`LExpr.substFvarsBy`), is rewritten by `root`. -/
@[expose] def leafRwWith (root : Expression.Expr → Expression.Expr)
    (g : Expression.Ident → Option Expression.Expr) (e : Expression.Expr) : Expression.Expr :=
  match e with
  | .fvar _ x _ => (g x).getD (root e)
  | _ => root (e.substFvarsBy g)

/-- `root` applied bottom up through the parts of applications, conditionals and equalities of
    `e` with `g` substituted; the substituted expressions are not rewritten (`leafRwWith`). The
    pass is bottom up, so the parts of a node are rewritten before the node. -/
@[expose] def rwBelowWith (root : Expression.Expr → Expression.Expr)
    (g : Expression.Ident → Option Expression.Expr) : Expression.Expr → Expression.Expr
  | .app m f a => root (.app m (rwBelowWith root g f) (rwBelowWith root g a))
  | .ite m c t e =>
    root (.ite m (rwBelowWith root g c) (rwBelowWith root g t) (rwBelowWith root g e))
  | .eq m a b => root (.eq m (rwBelowWith root g a) (rwBelowWith root g b))
  | e => leafRwWith root g e

/-- **The bottom-up rewrite at the root rewrite `root`**, with the substitution `g`:
    `rwBelowWith root g e` when the operator, abstraction and quantifier annotations of `e` with
    `g` substituted are all ground; otherwise `e` with `g` substituted. -/
@[expose] def rwAllWith (root : Expression.Expr → Expression.Expr)
    (g : Expression.Ident → Option Expression.Expr) (e : Expression.Expr) : Expression.Expr :=
  if annGround (e.substFvarsBy g) then rwBelowWith root g e else e.substFvarsBy g

/-- **The normalization of the rewrite loop**, with the substitution `g`: the bottom-up rewrite
    at `rwRoot fac`. -/
@[expose] def rwAll (fac : Lambda.Factory CoreLParams) :
    (Expression.Ident → Option Expression.Expr) → Expression.Expr → Expression.Expr :=
  rwAllWith (rwRoot fac)

/-! ## The normalization of the constructor fold

`rwAll fac` folds a tester applied to a constructor application (`testCtor`), but leaves the
conditional whose condition it so turned into a literal: `iteLit` is not among the rewrites of
`rwRoot`.  A condition built as a chain of testers over one value therefore keeps
every arm the chain does not take, and keeps naming the functions those arms apply, which is
what decides whether axiom pruning keeps a function's quantified axioms.  `rwAllC fac` is
the bottom-up rewrite at `ctorRoot fac`, which adds `iteLit` after the rewrites of `rwRoot` at
each node. -/

/-- **The root rewrite of the constructor fold**: the rewrites of `rwRoot fac`, then the collapse
    of a conditional whose condition they turned into a Boolean literal (`iteLit`).  `iteLit`
    comes last so that the folds of `rwRoot` can produce the literal condition it reads. -/
@[expose] def ctorRoot (fac : Lambda.Factory CoreLParams) (e : Expression.Expr) :
    Expression.Expr :=
  iteLit (rwRoot fac e)

/-- **The normalization of the constructor fold**, with the substitution `g`: the bottom-up
    rewrite at `ctorRoot fac`. The arms of a conditional are rewritten before its condition is
    collapsed. -/
@[expose] def rwAllC (fac : Lambda.Factory CoreLParams) :
    (Expression.Ident → Option Expression.Expr) → Expression.Expr → Expression.Expr :=
  rwAllWith (ctorRoot fac)

end -- public section

end DefInline
end Core
