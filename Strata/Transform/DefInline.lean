/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.GuardFwd

/-! # Inlining of single-use definitions on obligation programs

In an obligation program (the output of the SSA phase), a definition `init y := d` whose name
occurs once in the whole list is read by one expression only: the right-hand side of a later
`init`, an `assume` condition, or the condition of an `assert` or a `cover`.  `defInline norm ss`
substitutes the rewritten `d` for `y` in that expression, so a chain `x@k := x@(k-1) + 1` becomes
one nested term.  The definition itself stays; `deadDefElim` must follow this phase, and it
removes the definitions this phase leaves unread.

The substitution and the normalization of every rewritten expression are done by `norm`, a
*substituting normalization* the language chooses (`SubstNorm`; for this phase in Core, the
substitution followed by the folding of the constants of a sum at the root, `SubstNorm.after
Core.DefInline.addFold`, so that the chain above becomes `x@0 + k` and not `k` nested sums), which
must keep the value of the substituted expression. The rewrite keeps the value of every expression
in every store the walk can reach, so assertions and covers keep their values exactly.

The walk goes forward over the statements, carrying the *scope* of guard forwarding
(`GuardFwd.Scope`): the names defined earlier on the current path, each with the rewritten
right-hand side of its `init` when that name occurs once, the rewritten right-hand side is not a
function value (`WPOps.lam?`; substituting one could create a beta redex) and each free variable of
the right-hand side is defined earlier on the path or by no `init` of the list.  Entries made
inside an arm of an `ite` are removed when the arm ends, by the undo log of guard forwarding
(`GuardFwd.GSt`), so no map is copied.

Each node of the input is visited once by the substitution and once by the counting; a recorded
right-hand side is substituted into the one expression that reads it, so the output, once
`deadDefElim` has removed the inlined definitions, is not larger than the input.

For Core, `Core.DefInline.defInlineProgram` runs `defInline` on every structured procedure body,
and `Core.defInlinePipelinePhase` is the pipeline phase that runs it.

Key definitions: `ICtx`, `look`, `SubstNorm`, `rwE`, `walk`, `defInline`, `Core.DefInline.addFold`,
`Core.DefInline.defInlineProgram`, `Core.defInlinePipelinePhase`. -/

namespace Imperative
namespace DefInline

open WP BigStep GuardFwd

public section

variable {P : PureExpr} [BEq P.Ident] [Hashable P.Ident] [HasBool P] [HasFvar P] [HasFvars P]
  [WPOps P]

/-- What the walk reads about the whole list: the number of free-variable occurrences of each
    name, and the names some `init` (or `set`) of the list defines. -/
structure ICtx (P : PureExpr) [BEq P.Ident] [Hashable P.Ident] where
  cnt : Std.HashMap P.Ident Nat
  ini : Std.HashSet P.Ident

/-- The expression substituted for `y`: its recorded right-hand side, if any. -/
@[expose] def look (sc : Scope P) (y : P.Ident) : Option P.Expr :=
  match sc[y]? with
  | some (some d) => some d
  | _ => none

/-- A *substituting normalization*: `norm g e` is `e` with `g x` substituted for every name `x`
    that `g` maps to an expression (`WPOps.substFn e g`), normalized. -/
abbrev SubstNorm (P : PureExpr) := (P.Ident → Option P.Expr) → P.Expr → P.Expr

/-- The substituting normalization that substitutes, then applies `n`. -/
@[expose] def SubstNorm.after (n : P.Expr → P.Expr) : SubstNorm P :=
  fun g e => n (WPOps.substFn e g)

/-- The rewrite of an expression: every name with a recorded right-hand side replaced by it, and
    the result normalized, by `norm`. -/
@[expose] def rwE (norm : SubstNorm P) (sc : Scope P) (e : P.Expr) : P.Expr :=
  norm (look sc) e

/-- The entry of `x` with the right-hand side `e` and its rewrite `e'`: `e'` when `x` occurs
    once, `e'` is not a function value and each free variable of `e` is defined earlier on the
    path or by no `init` of the list.  The free variables of `e'` then satisfy the same condition,
    since those of the recorded right-hand sides do; reading those of `e`, not of the possibly
    larger `e'`, keeps the walk linear. -/
@[expose] def entry (cx : ICtx P) (sc : Scope P) (x : P.Ident) (e e' : P.Expr) :
    Option P.Expr :=
  if cx.cnt[x]? == some 1 && !WPOps.lam? e' &&
      (HasFvars.getFvars e).all (fun z => sc.contains z || !cx.ini.contains z) then some e'
  else none

mutual
/-- The walk over a statement list from the state `st`: the rewritten list and the state after
    it. -/
@[expose] def walk (norm : SubstNorm P) (cx : ICtx P) (st : GSt P) :
    PStmts P → PStmts P × GSt P
  | [] => ([], st)
  | s :: rest =>
    let (s', st) := walkS norm cx st s
    let (rest', st) := walk norm cx st rest
    (s' :: rest', st)
/-- The walk over a statement: the rewritten statement and the state after it.  The arms of an
    `ite` and the body of a block start from `st` and their entries are undone at their end. -/
@[expose] def walkS (norm : SubstNorm P) (cx : ICtx P) (st : GSt P) :
    PStmt P → PStmt P × GSt P
  | .cmd (.cmd (.init x ty (.det e) md)) =>
    let e' := rwE norm st.scope e
    (.cmd (.cmd (.init x ty (.det e') md)), st.push x (entry cx st.scope x e e'))
  | .cmd (.cmd (.init x ty .nondet md)) => (.cmd (.cmd (.init x ty .nondet md)), st.push x none)
  | .cmd (.cmd (.assume l e md)) => (.cmd (.cmd (.assume l (rwE norm st.scope e) md)), st)
  | .cmd (.cmd (.assert l e md)) => (.cmd (.cmd (.assert l (rwE norm st.scope e) md)), st)
  | .cmd (.cmd (.cover l e md)) => (.cmd (.cmd (.cover l (rwE norm st.scope e) md)), st)
  | .ite c tss ess md =>
    let m := st.trailLen
    let (tss', st) := walk norm cx st tss
    let (ess', st) := walk norm cx (st.undoTo m) ess
    (.ite c tss' ess' md, st.undoTo m)
  | .block l ss md =>
    let m := st.trailLen
    let (ss', st) := walk norm cx st ss
    (.block l ss' md, st.undoTo m)
  | s => (s, st)
end

/-- **Inlining of single-use definitions.**  The statement list with every name that occurs once
    replaced, in the expression that reads it, by the rewritten right-hand side of its `init`, the
    substitution and the normalization of every rewritten expression done by `norm`. -/
@[expose] def defInline (norm : SubstNorm P) (ss : PStmts P) : PStmts P :=
  (walk norm ⟨countB {} ss, Std.HashSet.ofList (Block.assignedVarsH ss)⟩ {} ss).1

/-- **Inlining at a caller's choice of names.**  The walk of `defInline`, with the occurrence
    counts `sel` the caller supplies instead of the real ones (`countB {} ss`).

    `entry` records the right-hand side of `x` when `sel[x]? == some 1`, so a caller selects
    exactly the names it wants substituted by mapping those, and only those, to `1`: a name
    absent from `sel` is never substituted, since `none ≠ some 1`.

    **This is a second entry point, not a replacement, and the two must stay separate.**
    `defInline` passes the real occurrence counts, so it fires only on a name read once, which is
    what keeps its output no larger than its input.  A caller of `defInlineWith` takes on that
    size obligation itself: it must choose `sel` so that substituting those names does not grow
    the list, by a criterion of its own (`Core.CtorFold.ctorFold` measures the result and keeps
    it only when it is no larger than the list it started from).  Merging the two paths back
    together would put the use-count gate back in front of those callers and silently undo what
    they do.

    Correctness does not depend on `sel`: substituting a name by the right-hand side its `init`
    gave it keeps the value whatever the name's occurrence count is. -/
@[expose] def defInlineWith (norm : SubstNorm P) (sel : Std.HashMap P.Ident Nat)
    (ss : PStmts P) : PStmts P :=
  (walk norm ⟨sel, Std.HashSet.ofList (Block.assignedVarsH ss)⟩ {} ss).1

end -- public section

end DefInline
end Imperative

/-! ## The Core phase -/

namespace Core

public section

namespace DefInline

open Imperative Imperative.DefInline

/-- The type annotation of the integer addition operator: `int → int → int`. -/
@[expose] def intAddTy : Option Lambda.LMonoTy := some (.arrow .int (.arrow .int .int))

/-- **Folding of the constants of a sum, at the root.**  `(a + c₁) + c₂`, for integer literals
    `c₁` and `c₂` and operators named `Int.Add` annotated `int → int → int`, becomes
    `a + (c₁ + c₂)`, the outer operator and metadata kept; every other expression stays.  Only
    the root is rewritten, so each call takes constant time. -/
@[expose] def addFold : Expression.Expr → Expression.Expr
  | e@(.app m (.app m' (.op mo f ty) (.app _ (.app _ (.op _ f' ty') a) (.const _ (.intConst c₁))))
      (.const mc (.intConst c₂))) =>
    if f.name = "Int.Add" ∧ f'.name = "Int.Add" ∧ ty = intAddTy ∧ ty' = intAddTy then
      .app m (.app m' (.op mo f ty) a) (.const mc (.intConst (c₁ + c₂)))
    else e
  | e => e

/-- **The inlining transform.**  Every procedure of the program with its structured body
    rewritten by `defInline norm`, every other declaration unchanged, and whether some procedure
    has a structured body (the only declarations the phase may rewrite).  It leaves the transform
    state as it is. -/
@[expose] def defInlineProgram (norm : SubstNorm Expression) (p : Program) :
    Transform.CoreTransformM (Bool × Program) :=
  return p.mapStructuredBodies (defInline norm) fun _ _ => true

end DefInline

/-- The inlining pipeline phase: substitutes each definition whose name occurs once into the
    expression that reads it and folds the constants of the sum at the root of each rewritten
    expression (`Core.DefInline.defInlineProgram (.after Core.DefInline.addFold)`).  It requires an
    obligation program (`hasObligationForm`, `staticSingleAssignment`, no calls, loops or CFG
    bodies).
    `deadDefElimPipelinePhase` must follow it: the inlined definitions are left unread, and only
    the erasure of unread definitions removes them.  It keeps the statements and only rewrites
    expressions, with free variables, operators and annotated variables taken from the input, and
    substitutes no function value, so it keeps the facts of its input. -/
def defInlinePipelinePhase : PipelinePhase :=
  modelPreservingPipelinePhase "defInline" (DefInline.defInlineProgram (.after DefInline.addFold))
    (requires := factSet![.noCFGBodies, .noCalls, .noLoops, .staticSingleAssignment,
                         .hasObligationForm])
    (preserves := Strata.Pipeline.factSetUnion obligationRewritePreserves
      factSet![.noBetaRedexes])

end -- public section

end Core
