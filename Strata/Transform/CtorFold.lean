/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.DefInline
public import Strata.Transform.DefInlineRewrite
public import Strata.Transform.DeadDefElim
public import Strata.Transform.WPLoop
public import Strata.Transform.Passive.CoreProgram

/-! # The constructor fold on obligation programs

A front end that models a value of several shapes as one datatype asks whether a value has a
shape by a *tester* (`Any..isfrom_bool`) and reads it by a *selector* (`Any..as_bool!`), and
writes a condition over such a value as a chain of conditionals, one per shape.  When the value
is a constructor application the chain takes one arm, and the other arms are unreachable; but
the WP pipeline leaves them in place, because the name the chain reads is defined once and read
many times, and the inlining of the rewrite loop substitutes only a name read once
(`DefInline.entry`).  Those arms keep naming the functions they apply — lists, dictionaries, the
front end's `$hole` — and axiom pruning keeps a function's quantified axioms exactly when the
obligation names the function, so the solver is sent the unreachable arms' axioms and answers
`unknown` on a goal that is decided without them.  Symbolic evaluation does not lose these
refutations: it evaluates the chain, so pruning sees only what the taken arm names.

`ctorFold fac ss` closes that gap in two steps, neither of which has a threshold:

* `ctorCands fac ss` collects the names worth substituting: a name defined by an `init` with a
  deterministic right-hand side `d` that is read at least once as the argument of an application
  `DefInline.bodyFold fac` folds to a literal with `d` in its place.  A read inside an
  abstraction or a quantifier does not count, since the bottom-up rewrite does not rewrite under
  a binder and so would copy `d` there without folding it.
* `DefInline.defInlineWith (ctorNorm fac) (ctorCands fac ss)` substitutes these names,
  normalizing by `ctorNorm fac`, which folds the tester (`DefInline.testCtor`) and then collapses
  the conditional whose condition it so turned into a literal (`DefInline.iteLit`), discarding
  the arms the chain does not take.  The erasure of unread definitions then drops the `init`s
  left unread.

  What this buys is not that the condition becomes a literal — a selector applied to the
  constructor need not fold, and `Any..as_bool!(from_bool(false))` remains — but that the
  discarded arms, and the functions only they named, are gone, so axiom pruning no longer keeps
  those functions' quantified axioms.

**The output is never larger than the input**, which is the size obligation
`DefInline.defInlineWith` leaves to its caller.  It is discharged by measuring, not by
predicting: `ctorFold` keeps the result of substituting `ctorCands fac ss` exactly when it is no
larger than the body (`Core.WPLoop.blockSize`, the measure the rewrite loop already uses), and
otherwise substitutes no name.  Measuring is what the obligation needs, because a selected name may also be
read where no fold applies, and whether such a read costs anything cannot be read off the body:
a read inside an arm of a conditional whose condition a fold turns into a literal disappears
with that arm, and which conditions fold is what the rewrite computes.  The comparison is
against the body itself, so no constant enters.

For Core, `Core.CtorFold.ctorFoldProgram` runs `ctorFold` on every structured procedure body,
and `Core.ctorFoldPipelinePhase` is the pipeline phase that runs it.

Key definitions: `Core.CtorFold.ctorNorm`, `Core.CtorFold.foldsAt`, `Core.CtorFold.goodOcc`,
`Core.CtorFold.candsB`, `Core.CtorFold.ctorCands`, `Core.CtorFold.runSel`,
`Core.CtorFold.ctorFold`,
`Core.CtorFold.ctorFoldProgram`, `Core.ctorFoldPipelinePhase`. -/

namespace Core
namespace CtorFold

open Imperative Imperative.DefInline Core.DefInline

public section

/-- **The normalization of the constructor fold**: the substitution and the rewrites of
    `Core.DefInline.rwAllC fac` (those of the rewrite loop, and `iteLit` after them), then the
    folding of the constants of a sum, as `Core.WPLoop.loopNorm` does for the loop. -/
@[expose] def ctorNorm (fac : Lambda.Factory CoreLParams) : DefInline.SubstNorm Expression :=
  fun g e => DefInline.addFold (DefInline.rwAllC fac g e)

/-- Does the application of `f` to `d` fold to a literal (`DefInline.bodyFold`)?  This is what
    makes a read of a name whose recorded right-hand side is `d`, as the argument of an
    application of `f`, disappear when the name is substituted. -/
@[expose] def foldsAt (fac : Lambda.Factory CoreLParams) (m : ExpressionMetadata)
    (f d : Expression.Expr) : Bool :=
  (DefInline.bodyFold fac (.app m f d)).isSome

/-- The candidate names with a *good* occurrence in `e`: a read as the argument of an
    application that `foldsAt fac` folds with the candidate's recorded right-hand side in its
    place.  Substituting such a name makes that read disappear.  A read inside an abstraction or
    a quantifier is never good, since the bottom-up rewrite does not rewrite under a binder and
    so would leave a copy there unfolded. -/
@[expose] def goodOcc (fac : Lambda.Factory CoreLParams)
    (cand : Std.HashMap Expression.Ident Expression.Expr) :
    Expression.Expr → Std.HashSet Expression.Ident
  | .app m f a =>
    let gf := goodOcc fac cand f
    match a with
    | .fvar _ y _ =>
      match cand[y]? with
      | some d => if foldsAt fac m f d then gf.insert y else gf
      | none => gf
    | _ => gf.union (goodOcc fac cand a)
  | .ite _ c t f =>
    (goodOcc fac cand c).union ((goodOcc fac cand t).union (goodOcc fac cand f))
  | .eq _ a b => (goodOcc fac cand a).union (goodOcc fac cand b)
  | .const .. | .op .. | .bvar .. | .fvar .. | .abs .. | .quant .. => {}

mutual
/-- The candidate names of a statement list: the names its `init`s define with a deterministic
    right-hand side, each with that right-hand side. -/
@[expose] def candsB (cand : Std.HashMap Expression.Ident Expression.Expr) :
    Statements → Std.HashMap Expression.Ident Expression.Expr
  | [] => cand
  | s :: rest => candsB (candsS cand s) rest
/-- `candsB` for one statement. -/
@[expose] def candsS (cand : Std.HashMap Expression.Ident Expression.Expr) :
    Statement → Std.HashMap Expression.Ident Expression.Expr
  | .cmd (.cmd (.init x _ (.det e) _)) => cand.insert x e
  | .ite _ tss ess _ => candsB (candsB cand tss) ess
  | .block _ ss _ => candsB cand ss
  | _ => cand
end

mutual
/-- The candidate names with a good occurrence anywhere in a statement list. -/
@[expose] def goodB (fac : Lambda.Factory CoreLParams)
    (cand : Std.HashMap Expression.Ident Expression.Expr) :
    Statements → Std.HashSet Expression.Ident
  | [] => {}
  | s :: rest => (goodS fac cand s).union (goodB fac cand rest)
/-- `goodB` for one statement. -/
@[expose] def goodS (fac : Lambda.Factory CoreLParams)
    (cand : Std.HashMap Expression.Ident Expression.Expr) :
    Statement → Std.HashSet Expression.Ident
  | .cmd (.cmd (.init _ _ (.det e) _)) => goodOcc fac cand e
  | .cmd (.cmd (.assume _ e _)) => goodOcc fac cand e
  | .cmd (.cmd (.assert _ e _)) => goodOcc fac cand e
  | .cmd (.cmd (.cover _ e _)) => goodOcc fac cand e
  | .ite c tss ess _ =>
    (goodG fac cand c).union ((goodB fac cand tss).union (goodB fac cand ess))
  | .block _ ss _ => goodB fac cand ss
  | _ => {}
/-- `goodS` for the guard of a conditional. -/
@[expose] def goodG (fac : Lambda.Factory CoreLParams)
    (cand : Std.HashMap Expression.Ident Expression.Expr) :
    Imperative.ExprOrNondet Expression → Std.HashSet Expression.Ident
  | .det e => goodOcc fac cand e
  | .nondet => {}
end

/-- The names worth substituting: each name an `init` of `ss` defines with a deterministic
    right-hand side and that has at least one good occurrence in `ss`, mapped to `1` as
    `DefInline.defInlineWith` reads its argument, and no other name mapped at all. -/
@[expose] def ctorCands (fac : Lambda.Factory CoreLParams) (ss : Statements) :
    Std.HashMap Expression.Ident Nat :=
  let cand := candsB (∅ : Std.HashMap Expression.Ident Expression.Expr) ss
  let good := goodB fac cand ss
  cand.fold (fun acc y _ => if good.contains y then acc.insert y 1 else acc)
    (∅ : Std.HashMap Expression.Ident Nat)

/-- The inlining of the names `sel` selects, at the normalization `ctorNorm fac`, with the
    definitions it leaves unread erased. -/
@[expose] def runSel (fac : Lambda.Factory CoreLParams) (sel : Std.HashMap Expression.Ident Nat)
    (ss : Statements) : Statements :=
  Imperative.DeadDefElim.deadDefElimH [] (DefInline.defInlineWith (ctorNorm fac) sel ss)

/-- **The constructor fold**: the inlining of the names `ctorCands fac ss` at the normalization
    `ctorNorm fac`, then the erasure of the definitions it leaves unread (`runSel`), when its
    result is no larger than the body; otherwise the same with no name selected.  With no
    candidate, the result is that of no name selected and nothing is measured.

    A name with a good occurrence may also be read where no fold applies, and substituting it
    then leaves a copy of its right-hand side at that read.  Whether the copies a name's bad
    reads leave outweigh the folds its good reads give cannot be read off the body: a bad read
    inside an arm of a conditional whose condition a fold turns into a literal disappears with
    that arm, and which conditions fold is what the rewrite computes.  So the size obligation
    `DefInline.defInlineWith` leaves to its caller is discharged by measuring
    (`Core.WPLoop.blockSize`, the measure the rewrite loop already uses) rather than by
    predicting.  The comparison is against the body itself, so no constant enters.  Each branch
    is `runSel` for one selection, and the trace over-approximation of the inlining holds for
    every selection. -/
@[expose] def ctorFold (fac : Lambda.Factory CoreLParams) (ss : Statements) : Statements :=
  let sel := ctorCands fac ss
  if sel.isEmpty then runSel fac sel ss
  else
    let r := runSel fac sel ss
    if WPLoop.blockSize r ≤ WPLoop.blockSize ss then r
    else runSel fac (∅ : Std.HashMap Expression.Ident Nat) ss

/-- **The constructor-fold transform.**  Every procedure of the program with its structured body
    rewritten by `ctorFold` at the program's datatype factory, every other declaration
    unchanged, and whether some procedure body changed. -/
@[expose] def ctorFoldProgram (fac : Lambda.Factory CoreLParams) (p : Program) :
    Transform.CoreTransformM (Bool × Program) :=
  return p.mapStructuredBodies (ctorFold fac)

end -- public section

end CtorFold

public section

/-- The constructor-fold pipeline phase: substitutes the names a body defines as a constructor
    application and whose reads the normalization folds, collapsing a chain of conditionals over
    their testers to the arm the constructor selects, so the arms the chain does not take, and
    the functions only they name, are gone before axiom pruning reads the obligation
    (`Core.CtorFold.ctorFoldProgram`).  It requires an obligation
    program (`hasObligationForm`, `staticSingleAssignment`, no calls, loops or CFG bodies).  It
    only rewrites expressions and erases definitions it leaves unread, with free variables,
    operators and annotated variables taken from the input, so it keeps the facts of its input
    other than `noBetaRedexes`: its normalization can turn an applied conditional whose arms are
    functions into an applied arm, a redex. -/
def ctorFoldPipelinePhase
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default) : PipelinePhase :=
  modelPreservingPipelinePhase "ctorFold"
    (fun program => do
      let fac ← Transform.liftDiag (wpFactory moreFns program)
      CtorFold.ctorFoldProgram fac program)
    (requires := factSet![.noCFGBodies, .noCalls, .noLoops, .staticSingleAssignment,
                         .noPrecondsFromFuncs, .hasObligationForm, .typeAnnotated])
    (preserves := obligationRewritePreserves)

end -- public section

end Core
