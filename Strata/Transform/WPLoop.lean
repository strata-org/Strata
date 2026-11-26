/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.DefInline
public import Strata.Transform.DefInlineRewrite
public import Strata.Transform.DeadDefElim

/-! # The three-pass round of the rewrite loop of `--vcgen wp`

A *round* of this module is guard forwarding (`GuardFwd.guardFwd`), then the inlining of
single-use definitions with a normalization `norm` (`DefInline.defInline`), then the erasure of
unread definitions (`DeadDefElim.deadDefElimH`).  Each component can create work for the others:
an inlined definition exposes a guard or a foldable term, and a folded term leaves definitions
unread.  The rewrite loop of `--vcgen wp` (`Core.WPRewriteLoop`) runs this round, at the
normalization `loopNorm`, as the middle three passes of its own round.

`loopFix round fuel` repeats a round until a round leaves the body unchanged.  Its fuel, one more
than the number of statements and expression nodes of the body at loop entry (`blockSize`), only
bounds the number of rounds; a loop that runs out of fuel returns the body after the last round
and reports it.  The result is always the output of some number of rounds, whatever the fuel, so
the fuel cannot affect soundness.  `wpLoopProgramWith` runs a loop on every procedure body of a
program and records its statistics (`wpLoop.rounds`, `wpLoop.fuelExhausted`).

`wpRoundF` is the round at `loopNorm` with an inlining (`defInlineF`) that keeps with each
recorded right-hand side whether its annotations are ground and what the rewrites at the root
read below it (`RInfo`), so that a chain of inlinings reads each node once and not once per
expression it is inlined into.

Key definitions: `Core.WPLoop.wpRound`, `Core.WPLoop.blockSize`, `Core.WPLoop.loopFix`,
`Core.WPLoop.wpLoopBody`, `Core.WPLoop.wpLoopProgramWith`, `Core.WPLoop.loopNorm`,
`Core.WPLoop.rinfo`, `Core.WPLoop.rwRootI`, `Core.WPLoop.rwBelowI`, `Core.WPLoop.loopNormF`,
`Core.WPLoop.defInlineF`, `Core.WPLoop.wpRoundF`. -/

namespace Core

public section

namespace WPLoop

open Imperative

/-- **One round of the loop**: guard forwarding, then the inlining of single-use definitions
    with the normalization `norm`, then the erasure of unread definitions. -/
@[expose] def wpRound (norm : DefInline.SubstNorm Expression) (ss : Statements) : Statements :=
  DeadDefElim.deadDefElimH [] (DefInline.defInline norm (GuardFwd.guardFwd ss))

/-- The number of expression nodes an expression of a command contributes. -/
@[expose] def exprSize (e : Expression.Expr) : Nat := Lambda.LExpr.size _ e

mutual
/-- The number of statements and expression nodes of a statement list, nested ones included. -/
@[expose] def blockSize : Statements → Nat
  | [] => 0
  | s :: rest => stmtSize s + blockSize rest
/-- The number of statements and expression nodes of a statement, nested ones included. -/
@[expose] def stmtSize : Statement → Nat
  | .cmd (.cmd (.init _ _ (.det e) _)) | .cmd (.cmd (.assume _ e _))
  | .cmd (.cmd (.assert _ e _)) | .cmd (.cmd (.cover _ e _)) => 1 + exprSize e
  | .ite _ tss ess _ => 1 + blockSize tss + blockSize ess
  | .block _ ss _ => 1 + blockSize ss
  | _ => 1
end

/-- **The loop with fuel.**  `loopFix round fuel ss k` runs rounds `round` on `ss`, `k` rounds
    having run before, until a round returns its input or `fuel` rounds have run.  It returns the
    last list, the number of rounds run, and whether the fuel ran out before a round returned its
    input. -/
@[expose] def loopFix (round : Statements → Statements) :
    Nat → Statements → Nat → Statements × Nat × Bool
  | 0, ss, k => (ss, k, true)
  | fuel + 1, ss, k =>
    let ss' := round ss
    if ss' == ss then (ss, k + 1, false) else loopFix round fuel ss' (k + 1)

/-- The loop on a procedure body, with one round more than the body's number of statements and
    expression nodes as fuel (a round that changes nothing is needed to stop): the rewritten
    body, the number of rounds run, and whether the fuel ran out. -/
@[expose] def wpLoopBody (norm : DefInline.SubstNorm Expression) (ss : Statements) :
    Statements × Nat × Bool :=
  loopFix (wpRound norm) (blockSize ss + 1) ss 0

/-- The declaration with the loop `body` run on its structured procedure body, whether the loop
    ran more than one round or ran out of fuel, the number of rounds run and whether the fuel ran
    out.  For a loop of `loopFix`, whose last round returns its input unless the fuel runs out,
    the flag holds whenever the body changed, without comparing the bodies again. -/
@[expose] def wpLoopDecl (body : Statements → Statements × Nat × Bool) :
    Decl → Decl × Bool × Nat × Bool
  | .proc q md => match q.body with
    | .structured ss o =>
      let (ss', n, out) := body ss
      (.proc { q with body := .structured ss' o } md, n > 1 || out, n, out)
    | .cfg _ _ | .abstract => (.proc q md, false, 0, false)
  | d => (d, false, 0, false)

/-- Every procedure of the program with the loop `body` run on its structured body, every other
    declaration unchanged, and the change flag of `wpLoopDecl` for some body.  It adds the number
    of rounds run to the statistics counter `wpLoop.rounds` and the number of bodies whose loop
    ran out of fuel to `wpLoop.fuelExhausted`. -/
@[expose] def wpLoopProgramWith (body : Statements → Statements × Nat × Bool) (p : Program) :
    Transform.CoreTransformM (Bool × Program) := do
  let r := p.decls.map (wpLoopDecl body)
  Transform.incrementStat "wpLoop.rounds" (r.foldl (fun n d => n + d.2.2.1) 0)
  Transform.incrementStat "wpLoop.fuelExhausted" (r.countP (·.2.2.2))
  return (r.any (·.2.1), { decls := r.map (·.1) })

/-- The substituting normalization of the loop's inlining, under the factory of functions `fac`
    of the pipeline: the substitution and the rewrites of `DefInline.rwAll`, then the folding of
    the constants of a sum at the root (`DefInline.addFold`), which keeps a chain of increments
    inlined into one expression a single sum. -/
@[expose] def loopNorm (fac : Lambda.Factory CoreLParams) : DefInline.SubstNorm Expression :=
  fun g e => DefInline.addFold (DefInline.rwAll fac g e)

/-! ### The inlining at `loopNorm` with cached checks

`loopNorm fac` checks the annotations of the whole substituted expression, recorded right-hand
sides included, and its rewrites at the root read the substituted expressions below the root:
`Core.WP.constFold` through negations and equalities, `DefInline.findIte` through the function of
an application, a negated argument and both sides of an equality.  A chain of inlinings would read
each recorded right-hand side again in every expression it is inlined into.  The walk below
computes the same output while keeping, for each recorded right-hand side, whether its
annotations are ground and what those rewrites read of it (`RInfo`), and reads only the nodes of
the expression it rewrites (`annGroundWith`, `rwBelowI`). -/

/-- What the rewrites at the root read below the root of an expression: the constant it folds to
    by `Core.WP.constFold`, and whether `DefInline.findIte` finds no conditional in it. -/
abbrev RInfo := Option Lambda.LConst × Bool

/-- The `RInfo` of an expression, read from the whole expression. -/
@[expose] def rinfo (e : Expression.Expr) : RInfo :=
  (Core.WP.constFold e, (DefInline.findIte e).isNone)

/-- The `RInfo` of an application of `f` to `a`, from the `RInfo`s `i` of `f` and `j` of `a`. -/
@[expose] def rinfoApp (f a : Expression.Expr) (i j : RInfo) : RInfo :=
  (Core.WP.constFoldApp f j.1, if f = (Lambda.boolNotFunc (T := CoreLParams)).opExpr then
    i.2 && j.2 else i.2 && !(a matches .ite ..))

/-- The `RInfo` of an equality of `a` and `b`, from the `RInfo`s `i` of `a` and `j` of `b`. -/
@[expose] def rinfoEq (i j : RInfo) : RInfo :=
  (Core.WP.constFoldEq i.1 j.1, i.2 && j.2)

/-- `f e` with its `RInfo`, `i` being that of `e`: `e` with `i` when `keep` holds, a cheap
    test under which `f` leaves `e` unchanged, otherwise `f e` with `rinfo (f e)`. -/
@[expose] def withI (f : Expression.Expr → Expression.Expr) (keep : Bool) (e : Expression.Expr)
    (i : RInfo) : Expression.Expr × RInfo :=
  if keep then (e, i) else (f e, rinfo (f e))

/-- Is the expression not a redex `DefInline.betaNG` may contract? -/
@[expose] def keepBeta : Expression.Expr → Bool
  | .app _ (.abs _ _ (some _) _) _ => false
  | _ => true

/-- Is the expression not an equality of two equal sides, which `DefInline.decEq` may decide? -/
@[expose] def keepDec : Expression.Expr → Bool
  | .eq _ a b => !decide (a = b)
  | _ => true

/-- Does `DefInline.foldOp fac` leave the expression, of `RInfo` `i`, unchanged: it is a literal,
    or neither `Core.WP.constFold` nor `Core.WP.concreteFold fac` folds it? -/
@[expose] def keepFold (fac : Lambda.Factory CoreLParams) (e : Expression.Expr) (i : RInfo) :
    Bool :=
  match e with
  | .const _ _ => true
  | _ => i.1.isNone && (Core.WP.concreteFold fac e).isNone

/-- Is the expression not a conditional, which `DefInline.iteSame` may drop? -/
@[expose] def keepSame : Expression.Expr → Bool
  | .ite .. => false
  | _ => true

/-- Is the expression not a sum whose second summand is an integer literal, which
    `DefInline.addFold` may rewrite? -/
@[expose] def keepAdd : Expression.Expr → Bool
  | .app _ (.app _ (.op _ _ _) _) (.const _ (.intConst _)) => false
  | _ => true

/-- Is the expression not an application of an annotated operator, which `DefInline.testCtor` may
    fold? -/
@[expose] def keepTest : Expression.Expr → Bool
  | .app _ (.op _ _ (some _)) _ => false
  | _ => true

/-- `DefInline.rwRoot fac` on `e` of `RInfo` `i`, with the `RInfo` of the result: each rewrite
    that the cheap tests show to leave its input unchanged passes the `RInfo` on. -/
@[expose] def rwRootI (fac : Lambda.Factory CoreLParams) (e : Expression.Expr) (i : RInfo) :
    Expression.Expr × RInfo :=
  let p := withI DefInline.betaNG (keepBeta e) e i
  let p := withI DefInline.decEq (keepDec p.1) p.1 p.2
  let p := withI (DefInline.foldOp fac) (keepFold fac p.1 p.2) p.1 p.2
  let p := withI (DefInline.liftIte fac) p.2.2 p.1 p.2
  let p := withI DefInline.iteSame (keepSame p.1) p.1 p.2
  withI (DefInline.testCtor fac) (keepTest p.1) p.1 p.2

/-- `DefInline.leafRwWith (DefInline.rwRoot fac)` with the substituted expressions of `g` given
    with their `RInfo`s, and the `RInfo` of the result. -/
@[expose] def leafRwI (fac : Lambda.Factory CoreLParams)
    (g : Expression.Ident → Option (Expression.Expr × RInfo)) (e : Expression.Expr) :
    Expression.Expr × RInfo :=
  match e with
  | .fvar _ x _ => (g x).getD (DefInline.rwRoot fac e, rinfo (DefInline.rwRoot fac e))
  | _ =>
    let r := DefInline.rwRoot fac (e.substFvarsBy fun y => (g y).map (·.1))
    (r, rinfo r)

/-- `DefInline.rwBelowWith (DefInline.rwRoot fac)` with the substituted expressions of `g` given
    with their `RInfo`s, and the `RInfo` of the result, computed node by node. -/
@[expose] def rwBelowI (fac : Lambda.Factory CoreLParams)
    (g : Expression.Ident → Option (Expression.Expr × RInfo)) :
    Expression.Expr → Expression.Expr × RInfo
  | .app m f a =>
    let f' := rwBelowI fac g f
    let a' := rwBelowI fac g a
    rwRootI fac (.app m f'.1 a'.1) (rinfoApp f'.1 a'.1 f'.2 a'.2)
  | .ite m c t e =>
    rwRootI fac (.ite m (rwBelowI fac g c).1 (rwBelowI fac g t).1 (rwBelowI fac g e).1)
      (none, false)
  | .eq m a b =>
    let a' := rwBelowI fac g a
    let b' := rwBelowI fac g b
    rwRootI fac (.eq m a'.1 b'.1) (rinfoEq a'.2 b'.2)
  | e => leafRwI fac g e

/-- What the walk records of a right-hand side besides the expression: whether its annotations
    are ground, and its `RInfo`. -/
abbrev Flags := Bool × RInfo

/-- The language of the scope of that walk: its identifiers are Core identifiers and its
    expressions are Core expressions with their `Flags`.  The walk reads only identifiers and
    expressions; the other components are unused placeholders. -/
abbrev FlagExpr : PureExpr :=
  { Ident := CoreIdent, EqIdent := inferInstanceAs (DecidableEq (Lambda.Identifier Unit)),
    Expr := Expression.Expr × Flags, Ty := Unit, ExprMetadata := Unit, TyEnv := Unit,
    TyContext := Unit, Factory := Unit, Val := Unit, eval := fun _ _ _ => none }

/-- The recorded right-hand side of `y` in the scope `sc`, with its flags. -/
@[expose] def lookF (sc : GuardFwd.Scope FlagExpr) (y : Expression.Ident) :
    Option (Expression.Expr × Flags) :=
  match sc[y]? with
  | some (some d) => some d
  | _ => none

/-- `loopNorm fac` with the recorded right-hand sides of `sc` substituted into `e`, with whether
    the result has ground annotations and its `RInfo`.  The annotations of the substituted
    expression are read from the nodes of `e` and the flags of the right-hand sides
    (`annGroundWith`), and so is what the rewrites read below the root (`rwBelowI`). -/
@[expose] def loopNormF (fac : Lambda.Factory CoreLParams) (sc : GuardFwd.Scope FlagExpr)
    (e : Expression.Expr) : Expression.Expr × Flags :=
  if DefInline.annGroundWith (fun y => ((lookF sc y).map (·.2.1)).getD true) e then
    let r := rwBelowI fac (fun y => (lookF sc y).map fun d => (d.1, d.2.2)) e
    let a := withI DefInline.addFold (keepAdd r.1) r.1 r.2
    (a.1, true, a.2)
  else
    let r := DefInline.addFold (e.substFvarsBy fun y => (lookF sc y).map (·.1))
    (r, false, rinfo r)

/-- The entry of `x` with the right-hand side `e` and its flagged rewrite `r`, as
    `DefInline.entry` decides it. -/
@[expose] def entryF (cx : DefInline.ICtx Expression) (sc : GuardFwd.Scope FlagExpr)
    (x : Expression.Ident) (e : Expression.Expr) (r : Expression.Expr × Flags) :
    Option (Expression.Expr × Flags) :=
  if cx.cnt[x]? == some 1 && !WP.WPOps.lam? (P := Expression) r.1 &&
      (HasFvars.getFvars (P := Expression) e).all (fun z => sc.contains z || !cx.ini.contains z)
  then some r
  else none

mutual
/-- The walk of `DefInline.defInline (loopNorm fac)` over a statement list, on a scope of flagged
    right-hand sides. -/
@[expose] def walkF (fac : Lambda.Factory CoreLParams) (cx : DefInline.ICtx Expression)
    (st : GuardFwd.GSt FlagExpr) : Statements → Statements × GuardFwd.GSt FlagExpr
  | [] => ([], st)
  | s :: rest =>
    let (s', st) := walkSF fac cx st s
    let (rest', st) := walkF fac cx st rest
    (s' :: rest', st)
/-- The walk of `DefInline.defInline (loopNorm fac)` over a statement, on a scope of flagged
    right-hand sides. -/
@[expose] def walkSF (fac : Lambda.Factory CoreLParams) (cx : DefInline.ICtx Expression)
    (st : GuardFwd.GSt FlagExpr) : Statement → Statement × GuardFwd.GSt FlagExpr
  | .cmd (.cmd (.init x ty (.det e) md)) =>
    let r := loopNormF fac st.scope e
    (.cmd (.cmd (.init x ty (.det r.1) md)), st.push x (entryF cx st.scope x e r))
  | .cmd (.cmd (.init x ty .nondet md)) => (.cmd (.cmd (.init x ty .nondet md)), st.push x none)
  | .cmd (.cmd (.assume l e md)) => (.cmd (.cmd (.assume l (loopNormF fac st.scope e).1 md)), st)
  | .cmd (.cmd (.assert l e md)) => (.cmd (.cmd (.assert l (loopNormF fac st.scope e).1 md)), st)
  | .cmd (.cmd (.cover l e md)) => (.cmd (.cmd (.cover l (loopNormF fac st.scope e).1 md)), st)
  | .ite c tss ess md =>
    let m := st.trailLen
    let (tss', st) := walkF fac cx st tss
    let (ess', st) := walkF fac cx (st.undoTo m) ess
    (.ite c tss' ess' md, st.undoTo m)
  | .block l ss md =>
    let m := st.trailLen
    let (ss', st) := walkF fac cx st ss
    (.block l ss' md, st.undoTo m)
  | s => (s, st)
end

/-- `DefInline.defInline (loopNorm fac)` with cached checks (`walkF`). -/
@[expose] def defInlineF (fac : Lambda.Factory CoreLParams) (ss : Statements) : Statements :=
  (walkF fac ⟨GuardFwd.countB {} ss, Std.HashSet.ofList (Block.assignedVarsH ss)⟩ {} ss).1

/-- `wpRound (loopNorm fac)` with the inlining done by `defInlineF fac`. -/
@[expose] def wpRoundF (fac : Lambda.Factory CoreLParams) (ss : Statements) : Statements :=
  DeadDefElim.deadDefElimH [] (defInlineF fac (GuardFwd.guardFwd ss))

end WPLoop

end -- public section

end Core
