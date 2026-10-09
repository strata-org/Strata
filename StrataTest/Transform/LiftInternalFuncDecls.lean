/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.ProgramType
meta import Strata.Transform.LiftInternalFuncDecls

meta section

open Core
open Lambda Imperative
open Strata

/-! ## `LiftInternalFuncDecls` tests

`LiftInternalFuncDecls` hoists every local `funcDecl` in a procedure body to a
closed top-level `Decl.func`.  Captured variables are snapshotted at the
declaration site and become extra *leading* parameters (lambda lifting), and any
type variables in their types become extra `typeArgs`.
-/

section LiftInternalFuncDeclsTests

private def quietOpts : Core.VerifyOptions :=
  { Core.VerifyOptions.default with verbose := .quiet }

private def liftState : Core.Transform.CoreTransformState :=
  { Core.Transform.CoreTransformState.emp with factory := Core.Factory }

/-- A boolean check that a `Function` satisfies `Lambda.LFuncClosed`: the free
    variables of its body and of every precondition are among its inputs.  These
    are exactly `FuncClosed`'s two (decidable) fields, so this both powers the
    `#guard`s below and lets `funcIsClosed_toLFuncClosed` recover the
    `LFuncClosed` proof. -/
private def funcIsClosed (f : Function) : Bool :=
  decide (∀ b, f.body = some b →
            (Lambda.LExpr.freeVars b).map (·.1.name) ⊆ f.inputs.map (·.1.name)) &&
  decide (∀ p ∈ f.preconditions,
            (Lambda.LExpr.freeVars p.expr).map (·.1.name) ⊆ f.inputs.map (·.1.name))

/-- If the boolean `funcIsClosed` holds, then the function lifted into the
    evaluator-facing `LFunc` is `Lambda.LFuncClosed` (its body and preconditions
    have no free variables beyond its inputs). -/
private theorem funcIsClosed_toLFuncClosed {f : Function} (h : funcIsClosed f = true) :
    Lambda.LFuncClosed f.toLFunc := by
  simp only [funcIsClosed, Bool.and_eq_true, decide_eq_true_eq] at h
  exact { body_freevars := h.1, precond_freevars := h.2 }

/-- Every top-level function in the program is closed. -/
private def allFuncsClosed (p : Core.Program) : Bool :=
  p.decls.all fun | .func f _ => funcIsClosed f | _ => true

/-- No procedure body contains a `funcDecl` any longer. -/
private def allBodiesNoFuncDecl (p : Core.Program) : Bool :=
  p.decls.all fun
    | .proc proc _ => match proc.body with
        | .structured ss => Imperative.Block.noFuncDecl ss
        | .cfg _ => true
    | _ => true

private def programTypechecks (p : Core.Program) : Bool :=
  match Core.typeCheck quietOpts p with
  | .ok _ => true
  | .error _ => false

/-- Run the (monadic) lifting pass on a directly-constructed program. -/
private def runLiftAst (p : Core.Program) : Option Core.Program :=
  match Core.Transform.run p LiftInternalFuncDecls.run liftState with
  | .ok p' => some p'
  | .error _ => none

/-- Run the lifting pass on a directly-constructed program, returning its error
    diagnostic as a string (or a sentinel if it unexpectedly succeeded).  Used to
    pin the exact rejection message of AST-level negative tests. -/
private def runLiftAstErr (p : Core.Program) : String :=
  match Core.Transform.run p LiftInternalFuncDecls.run liftState with
  | .ok _ => "<unexpected: lift succeeded>"
  | .error e => toString (Std.format e)

/-- The first top-level function declaration in a program (each polymorphic AST
    example hoists exactly one, whose generated name we don't want to hardcode). -/
private def soleFunc (p : Core.Program) : Option Function :=
  (p.decls.filterMap fun | .func f _ => some f | _ => none).head?

/-! ### Concrete-syntax tests removed

Core's DDM translator now lowers internal function syntax to Lambda-valued
`init` statements, so concrete programs no longer produce `.funcDecl` nodes
and cannot exercise this transform. `LiftInternalFuncDecls` will be removed
when the deprecated constructor is removed. Until then, the remaining tests
construct `.funcDecl` ASTs directly to cover the legacy transform. -/

private def tyInt : LMonoTy := .tcons "int" []

/-! ### Example 10: a captured variable used only in the `decreases` measure

The Core surface grammar cannot currently attach a `decreases` clause to a local
`funcDecl`, so this case is built as an AST rather than with `#strata` syntax.
`m`'s termination measure — and nothing else — references the enclosing `c`, so
the pass must still capture `c` (add it as a parameter) and rewrite the measure
to the snapshot variable.

Equivalent concrete syntax (if a local `decreases` clause were supported):

    procedure q(c : int) {
      function m(x : int) : int decreases c { x }
    }
-/

private def measureDecl : PureFunc Core.Expression :=
  { name := ⟨"m", ()⟩,
    inputs := [(⟨"x", ()⟩, LTy.forAll [] tyInt)],
    output := LTy.forAll [] tyInt,
    body := some (.fvar () ⟨"x", ()⟩ (some tyInt)),
    measure := some (.fvar () ⟨"c", ()⟩ (some tyInt)) }

private def measureProg : Core.Program :=
  { decls := [
      Decl.proc
        { header := { name := ⟨"q", ()⟩, typeArgs := [], inputs := [(⟨"c", ()⟩, tyInt)], outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured [Stmt.funcDecl measureDecl .empty] }
        .empty ] }

/-- `c` (referenced only in the measure) is captured — the lifted `m` gains the
    leading snapshot parameter `$__liftfncl_0 : int` (ahead of the original
    `x : int`), and its measure is rewritten to exactly that snapshot variable. -/
private def measureCaptureOk : Bool :=
  match runLiftAst measureProg with
  | some p =>
    allBodiesNoFuncDecl p &&
    (match soleFunc p with
     | some f =>
       f.inputs.map (·.1.name) == ["$__liftfncl_0", "x"] &&
       decide (f.inputs.map (·.2) = [tyInt, tyInt]) &&
       (match f.measure with
        | some m => decide (m = .fvar () ⟨"$__liftfncl_0", ()⟩ (some tyInt))
        | none => false)
     | none => false)
  | none => false

#guard measureCaptureOk

/-! ### Example 11: a recursive internal function is rejected

Built as an AST (the surface grammar/type checker already rejects recursive local
`funcDecl`s — StatementType.lean: "recursive functions are not allowed as local
declarations"). The pass rejects a recursive internal `funcDecl` outright.

Equivalent concrete syntax (which the front end already rejects):

    procedure useSum(c : int) {
      function sumTo(n : int) : int { if n == c then c else sumTo(n) }
    }
-/

private def sumToDecl : PureFunc Core.Expression :=
  { name := ⟨"sumTo", ()⟩,
    isRecursive := true,
    inputs := [(⟨"n", ()⟩, LTy.forAll [] tyInt)],
    output := LTy.forAll [] tyInt,
    body := some (.ite ()
              (.eq () (.fvar () ⟨"n", ()⟩ (some tyInt)) (.fvar () ⟨"c", ()⟩ (some tyInt)))
              (.fvar () ⟨"c", ()⟩ (some tyInt))
              (.app () (.op () ⟨"sumTo", ()⟩ none) (.fvar () ⟨"n", ()⟩ (some tyInt)))) }

private def recSumProg : Core.Program :=
  { decls := [
      Decl.proc
        { header := { name := ⟨"useSum", ()⟩, typeArgs := [], inputs := [(⟨"c", ()⟩, tyInt)], outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured [Stmt.funcDecl sumToDecl .empty] }
        .empty ] }

-- The recursive `sumTo` is rejected: `run` fails rather than lifting it.
#guard (runLiftAst recSumProg).isNone

/--
info: "LiftInternalFuncDecls: procedure 'useSum' declares recursive internal function(s) 'sumTo'; recursive internal function declarations are not supported"
-/
#guard_msgs in
#eval runLiftAstErr recSumProg

/-! ### Example 12: a captured variable with no type annotation is rejected

Exercises `capturedVars`'s hardening: an occurrence of a captured free variable
carries no `fvar` type annotation, so the pass cannot determine its type and
fails with a diagnostic.  Built as an AST because the surface type-checker always
annotates fvars, so an unannotated occurrence is unreachable from concrete
syntax; the nearest concrete analogue would be:

    procedure q(c : int) {
      function h(x : int) : int { c }   -- but here `c` would be annotated `int`
    }
-/

private def unannotatedDecl : PureFunc Core.Expression :=
  { name := ⟨"h", ()⟩,
    inputs := [(⟨"x", ()⟩, LTy.forAll [] tyInt)],
    output := LTy.forAll [] tyInt,
    body := some (.fvar () ⟨"c", ()⟩ none) }

private def unannotatedProg : Core.Program :=
  { decls := [
      Decl.proc
        { header := { name := ⟨"q", ()⟩, typeArgs := [], inputs := [(⟨"c", ()⟩, tyInt)], outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured [Stmt.funcDecl unannotatedDecl .empty] }
        .empty ] }

#guard (runLiftAst unannotatedProg).isNone

/--
info: "LiftInternalFuncDecls: captured variable 'c' has an unannotated occurrence in function 'h'"
-/
#guard_msgs in
#eval runLiftAstErr unannotatedProg

/-! ### Example 18: an internal function whose precondition captures a variable

Here `f`'s precondition is the only place the enclosing `c` is referenced, so the
pass must capture `c` from the precondition and rewrite the precondition to the
snapshot parameter.

Built as an AST and run through the lift directly because Core's DDM syntax doesn't
support precondition of an internal function.

Equivalent concrete syntax:

    procedure useF(c : int, a : int) {
      function f(x : int) : int requires x > c { x }
      var r : int := f(a);
    }
-/

private def precondCaptureDecl : PureFunc Core.Expression :=
  { name := ⟨"f", ()⟩,
    inputs := [(⟨"x", ()⟩, LTy.forAll [] tyInt)],
    output := LTy.forAll [] tyInt,
    body := some (.fvar () ⟨"x", ()⟩ (some tyInt)),
    preconditions := [{ expr := .fvar () ⟨"c", ()⟩ (some tyInt), md := () }] }

private def precondCaptureProg : Core.Program :=
  { decls := [
      Decl.proc
        { header := { name := ⟨"useF", ()⟩, typeArgs := [], inputs := [(⟨"c", ()⟩, tyInt)], outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured [Stmt.funcDecl precondCaptureDecl .empty] }
        .empty ] }

/-- `c`, referenced only in `f`'s precondition, is captured: the lifted `f` gains
    the leading snapshot parameter `$__liftfncl_0 : int`, stays closed (its
    precondition's free vars are now among its inputs), and its precondition is
    rewritten to reference that snapshot rather than the original `c`. -/
private def precondCaptureOk : Bool :=
  match runLiftAst precondCaptureProg with
  | some p =>
    allBodiesNoFuncDecl p && allFuncsClosed p &&
    (match soleFunc p with
     | some f =>
       f.inputs.map (·.1.name) == ["$__liftfncl_0", "x"] &&
       f.preconditions.any (fun pc =>
         ((Lambda.LExpr.freeVars pc.expr).map (·.1.name)).contains "$__liftfncl_0")
     | none => false)
  | none => false

#guard precondCaptureOk

/-! ### Example 19: a sibling called only from another function's precondition

Similar to Example 18, but its precondition references another internal function.

Equivalent concrete syntax:

    procedure useF(a : int) {
      function g(x : int) : int { x + 1 }
      function f(x : int) : int requires g(x) > 0 { x }
      var r : int := f(a);
    }
-/

private def gPlainDecl : PureFunc Core.Expression :=
  { name := ⟨"g", ()⟩,
    inputs := [(⟨"x", ()⟩, LTy.forAll [] tyInt)],
    output := LTy.forAll [] tyInt,
    body := some (.fvar () ⟨"x", ()⟩ (some tyInt)) }

private def fCallsGInPrecondDecl : PureFunc Core.Expression :=
  { name := ⟨"f", ()⟩,
    inputs := [(⟨"x", ()⟩, LTy.forAll [] tyInt)],
    output := LTy.forAll [] tyInt,
    body := some (.fvar () ⟨"x", ()⟩ (some tyInt)),
    preconditions :=
      [{ expr := .app () (.op () ⟨"g", ()⟩ none) (.fvar () ⟨"x", ()⟩ (some tyInt)), md := () }] }

private def precondSiblingProg : Core.Program :=
  { decls := [
      Decl.proc
        { header := { name := ⟨"useF", ()⟩, typeArgs := [], inputs := [(⟨"a", ()⟩, tyInt)], outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured
            [Stmt.funcDecl gPlainDecl .empty, Stmt.funcDecl fCallsGInPrecondDecl .empty] }
        .empty ] }

/-- Both are hoisted closed, and the `g` call inside `f`'s precondition is
    rewritten to the lifted `g`'s fresh name (`$__liftfncl_g_0`) — the original
    `g` reference is gone. -/
private def precondSiblingOk : Bool :=
  match runLiftAst precondSiblingProg with
  | some p =>
    allBodiesNoFuncDecl p && allFuncsClosed p &&
    ((p.decls.filterMap (fun | .func f _ => some f | _ => none)).any fun f =>
      f.preconditions.any fun pc =>
        ((Lambda.LExpr.getOps pc.expr).map (·.name)).contains "$__liftfncl_g_0")
  | none => false

#guard precondSiblingOk

/-! ### Polymorphic Example 1: A closed polymorphic function (built as an AST)

`function id<T>(x : T) : T { x }` declared inside a procedure.  It captures
nothing, so it is hoisted verbatim, keeping its `typeArgs = [T]`.

Equivalent concrete syntax:

    procedure usePoly() {
      function id<T>(x : T) : T { x }
    }
-/

private def tyT : LMonoTy := .ftvar "T"
private def tyV : LMonoTy := .ftvar "V"

private def idDecl : PureFunc Core.Expression :=
  { name := ⟨"id", ()⟩,
    typeArgs := ["T"],
    inputs := [(⟨"x", ()⟩, LTy.forAll [] tyT)],
    output := LTy.forAll [] tyT,
    body := some (.fvar () ⟨"x", ()⟩ (some tyT)) }

private def closedPolyProg : Core.Program :=
  { decls := [
      Decl.proc
        { header := { name := ⟨"usePoly", ()⟩, typeArgs := [], inputs := [], outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured [Stmt.funcDecl idDecl .empty] }
        .empty ] }

/-- `id` is hoisted, closed, still polymorphic in `T`, and the procedure body no
    longer contains a `funcDecl`; the resulting program type-checks.  The lifted
    signature is pinned exactly: `∀T. (x : T) → T`. -/
private def closedPolyOk : Bool :=
  match runLiftAst closedPolyProg with
  | some p =>
    allBodiesNoFuncDecl p && allFuncsClosed p && programTypechecks p &&
    (match soleFunc p with
     | some f =>
       f.typeArgs == ["T"] &&
       f.inputs.map (·.1.name) == ["x"] &&
       decide (f.inputs.map (·.2) = [tyT]) &&
       decide (f.output = tyT)
     | none => false)
  | none => false

#guard closedPolyOk

/-! ### Polymorphic Example 2: A polymorphic function capturing polymorphic locals

Mirrors the illustration in `Strata/DL/Lambda/LExpr.lean`:
```
procedure p<V>(x : V, z : V) {
  function g<T>(y : T) : T { if x == z then y else y }
  var r : V := g(x);
}
```
Lifting `g` must capture `x, z : V` as extra parameters *and* add `V` to `g`'s
type arguments, and rewrite the call `g(x)` to `g(x, x, z)`. -/

private def gDecl : PureFunc Core.Expression :=
  { name := ⟨"g", ()⟩,
    typeArgs := ["T"],
    inputs := [(⟨"y", ()⟩, LTy.forAll [] tyT)],
    output := LTy.forAll [] tyT,
    body := some (.ite ()
              (.eq () (.fvar () ⟨"x", ()⟩ (some tyV)) (.fvar () ⟨"z", ()⟩ (some tyV)))
              (.fvar () ⟨"y", ()⟩ (some tyT))
              (.fvar () ⟨"y", ()⟩ (some tyT))) }

/-- The call `g(x)` inside the body (`var r : V := g(x)`). -/
private def gCall : Core.Expression.Expr :=
  .app () (.op () ⟨"g", ()⟩ none) (.fvar () ⟨"x", ()⟩ (some tyV))

private def capturePolyProg : Core.Program :=
  { decls := [
      Decl.proc
        { header := { name := ⟨"p", ()⟩, typeArgs := ["V"],
                      inputs := [(⟨"x", ()⟩, tyV), (⟨"z", ()⟩, tyV)], outputs := [] },
          spec := { preconditions := [], postconditions := [] },
          body := .structured [
            Stmt.funcDecl gDecl .empty,
            Statement.init ⟨"r", ()⟩ (LTy.forAll [] tyV) (.det gCall) .empty ] }
        .empty ] }

/-- `g` is hoisted as `∀T V. ($__liftfncl_0 : V, $__liftfncl_1 : V, y : T) → T`,
    closed, and the procedure body has no `funcDecl` left; the whole program
    type-checks.  The exact input names/types, type args, and output are pinned:
    the two leading captured snapshots have type `V`, the trailing original
    formal `y` has type `T`. -/
private def capturePolyOk : Bool :=
  match runLiftAst capturePolyProg with
  | some p =>
    allBodiesNoFuncDecl p && allFuncsClosed p && programTypechecks p &&
    (match soleFunc p with
     | some f =>
       f.typeArgs == ["T", "V"] &&
       f.inputs.map (·.1.name) == ["$__liftfncl_0", "$__liftfncl_1", "y"] &&
       decide (f.inputs.map (·.2) = [tyV, tyV, tyT]) &&
       decide (f.output = tyT)
     | none => false)
  | none => false

#guard capturePolyOk

/-- The captured call `g(x)` is rewritten to
    `$__liftfncl_g_2($__liftfncl_0, $__liftfncl_1, x)`: the head is exactly the
    lifted `g`, and the three arguments are exactly the two snapshots followed by
    the original `x`, all `V`-typed. -/
private def capturePolyCallRewritten : Bool :=
  match runLiftAst capturePolyProg with
  | some p =>
    (match Program.Procedure.find? p ⟨"p", ()⟩ with
     | some proc => match proc.body with
        | .structured ss => (Statements.collectExprs ss).any fun e =>
            match Lambda.getLFuncCall e with
            | (.op _ nm _, args) =>
              nm.name == "$__liftfncl_g_2" &&
              args.filterMap (fun a => match a with
                | .fvar _ n _ => some n.name | _ => none)
                == ["$__liftfncl_0", "$__liftfncl_1", "x"] &&
              args.all (fun a => match a with
                | .fvar _ _ (some t) => decide (t = tyV)
                | _ => false)
            | _ => false
        | .cfg _ => false
     | none => false)
  | none => false

#guard capturePolyCallRewritten

end LiftInternalFuncDeclsTests

end
