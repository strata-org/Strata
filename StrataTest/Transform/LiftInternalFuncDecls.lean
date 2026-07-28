/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
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

private def translate (t : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

private def quietOpts : Core.VerifyOptions :=
  { Core.VerifyOptions.default with verbose := .quiet }

private def liftState : Core.Transform.CoreTransformState :=
  { Core.Transform.CoreTransformState.emp with factory := some Core.Factory }

/-- Translate, type-check (annotating types), then lift internal function
    declarations. -/
private def liftOnly (t : StrataDDM.Program) : Core.Program :=
  let program := translate t
  let annotated := match Core.typeCheck quietOpts program with
    | .ok p => p
    | .error _ => program
  match Core.Transform.run annotated Core.liftInternalFuncDecls liftState with
  | .ok (_changed, p) => p
  | .error _ => annotated

/-- As `liftOnly`, but also re-type-checks the result and formats it.  A
    successful format (with no error string) demonstrates that every hoisted
    function is closed and well-typed. -/
private def transformProgram (t : StrataDDM.Program) : Std.Format :=
  match Core.typeCheck quietOpts (liftOnly t) with
  | .error e => f!"post-lift type check failed: {Std.format e}"
  | .ok checked => Std.format checked.stripMetaData

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

/-! ### Example 1: A closed monomorphic function is hoisted verbatim -/

private def closedMonoPgm :=
#strata
program Core;
procedure useDouble(a : int)
{
  function double(x : int) : int { int.add(x, x) }
  var r : int := double(a);
  assert r == int.add(a, a);
};
#end

/--
info: program Core;

function $__liftfncl_double_0 (x : int) : int {
  int.add(x, x)
}
procedure useDouble (a : int)
{
  var r : int := $__liftfncl_double_0(a);
  assert [assert_0]: r == int.add(a, a);
};
-/
#guard_msgs in
#eval (transformProgram closedMonoPgm)

#guard allFuncsClosed (liftOnly closedMonoPgm)
#guard allBodiesNoFuncDecl (liftOnly closedMonoPgm)

/-! ### Example 2: A function capturing a local becomes an extra parameter -/

private def captureMonoPgm :=
#strata
program Core;
procedure useC(c : int, a : int)
{
  function addC(x : int) : int { int.add(x, c) }
  var r : int := addC(a);
  assert r == int.add(a, c);
};
#end

/--
info: program Core;

function $__liftfncl_addC_1 ($__liftfncl_0 : int, x : int) : int {
  int.add(x, $__liftfncl_0)
}
procedure useC (c : int, a : int)
{
  var $__liftfncl_0 : int := c;
  var r : int := $__liftfncl_addC_1($__liftfncl_0, a);
  assert [assert_0]: r == int.add(a, c);
};
-/
#guard_msgs in
#eval (transformProgram captureMonoPgm)

#guard allFuncsClosed (liftOnly captureMonoPgm)
#guard allBodiesNoFuncDecl (liftOnly captureMonoPgm)

/-
Example 2+: The rewritten call sites carry the lifted function's instantiated type.

The pass re-annotates each rewritten `.op` with the lifted function's
instantiated arrow type — the captured (leading) parameter types prepended onto
the original call-site annotation — so the pass output is well-type-annotated
without relying on the follow-up type-check.

`addC` captures `c : int`, has formal `x : int`, and returns `int`; the original
call `addC(a)` is annotated `int → int`.  After lifting, the rewritten call
`$__liftfncl_addC_1($__liftfncl_0, a)` must annotate the operator with the
captured `int` prepended: `int → int → int`. -/

private def tyInt : LMonoTy := .tcons "int" []

private def liftedCallAnnotated : Bool :=
  match Program.Procedure.find? (liftOnly captureMonoPgm) ⟨"useC", ()⟩ with
  | some proc => match proc.body with
    | .structured ss => (Statements.collectExprs ss).any fun e =>
        match Lambda.getLFuncCall e with
        | (.op _ nm (some ty), _) =>
          nm.name == "$__liftfncl_addC_1" &&
          decide (ty = .arrow tyInt (.arrow tyInt tyInt))
        | _ => false
    | .cfg _ => false
  | none => false

#guard liftedCallAnnotated

/-! ### Example 3: Two sibling functions, one calling the other -/

private def siblingsPgm :=
#strata
program Core;
procedure useTwo(a : int)
{
  function inc(x : int) : int { int.add(x, 1) }
  function inc2(x : int) : int { inc(inc(x)) }
  var r : int := inc2(a);
  assert r == int.add(a, 2);
};
#end

/--
info: program Core;

function $__liftfncl_inc_0 (x : int) : int {
  int.add(x, 1)
}
function $__liftfncl_inc2_1 (x : int) : int {
  $__liftfncl_inc_0($__liftfncl_inc_0(x))
}
procedure useTwo (a : int)
{
  var r : int := $__liftfncl_inc2_1(a);
  assert [assert_0]: r == int.add(a, 2);
};
-/
#guard_msgs in
#eval (transformProgram siblingsPgm)

#guard allFuncsClosed (liftOnly siblingsPgm)
#guard allBodiesNoFuncDecl (liftOnly siblingsPgm)

/-! ### Example 4: declaration-site value capture survives reassignment

The captured `c` is reassigned (`c := 999`) *after* the `funcDecl` but *before*
the call.  Because the snapshot `$__liftfncl…` is taken at the declaration site,
the call still sees `c`'s declaration-time value (`10`), so `r == a + 10`. -/

private def reassignPgm :=
#strata
program Core;
procedure reassign(a : int)
{
  var c : int := 10;
  function addC(x : int) : int { int.add(x, c) }
  c := 999;
  var r : int := addC(a);
  assert r == int.add(a, 10);
};
#end

/--
info: program Core;

function $__liftfncl_addC_1 ($__liftfncl_0 : int, x : int) : int {
  int.add(x, $__liftfncl_0)
}
procedure reassign (a : int)
{
  var c : int := 10;
  var $__liftfncl_0 : int := c;
  c := 999;
  var r : int := $__liftfncl_addC_1($__liftfncl_0, a);
  assert [assert_0]: r == int.add(a, 10);
};
-/
#guard_msgs in
#eval (transformProgram reassignPgm)

#guard allFuncsClosed (liftOnly reassignPgm)
#guard allBodiesNoFuncDecl (liftOnly reassignPgm)

/-! ### Example 5: internal function calling an existing external function

The internal `usesExt` refers to the top-level function `ext`.  Since `ext` is
not itself an internal `funcDecl`, references to it are left untouched; only
`usesExt` is hoisted (and renamed). -/

private def callsExternalPgm :=
#strata
program Core;
function ext(x : int) : int { int.add(x, x) }
procedure useExt(a : int)
{
  function usesExt(y : int) : int { int.add(ext(y), 1) }
  var r : int := usesExt(a);
  assert r == int.add(ext(a), 1);
};
#end

/--
info: program Core;

function ext (x : int) : int {
  int.add(x, x)
}
function $__liftfncl_usesExt_0 (y : int) : int {
  int.add(ext(y), 1)
}
procedure useExt (a : int)
{
  var r : int := $__liftfncl_usesExt_0(a);
  assert [assert_0]: r == int.add(ext(a), 1);
};
-/
#guard_msgs in
#eval (transformProgram callsExternalPgm)

#guard allFuncsClosed (liftOnly callsExternalPgm)
#guard allBodiesNoFuncDecl (liftOnly callsExternalPgm)

/-! ### Example 6: internal function declared inside an `if` branch

`twice` is declared inside the then-branch; it is hoisted to the top level and
its call (still inside the branch) is rewritten to the fresh name. -/

private def funcInIfPgm :=
#strata
program Core;
procedure inBranch(c : bool, a : int)
{
  if (c) {
    function twice(x : int) : int { int.add(x, x) }
    var r : int := twice(a);
    assert r == int.add(a, a);
  } else {
    var r : int := a;
  }
};
#end

/--
info: program Core;

function $__liftfncl_twice_0 (x : int) : int {
  int.add(x, x)
}
procedure inBranch (c : bool, a : int)
{
  if (c) {
    var r : int := $__liftfncl_twice_0(a);
    assert [assert_0]: r == int.add(a, a);
  } else {
    var r : int := a;
  }
};
-/
#guard_msgs in
#eval (transformProgram funcInIfPgm)

#guard allFuncsClosed (liftOnly funcInIfPgm)
#guard allBodiesNoFuncDecl (liftOnly funcInIfPgm)

/-! ### Example 7: a lifted function that calls a capturing sibling

`addC2` calls the capturing sibling `addC`; lifting `addC`'s call inside `addC2`
injects `addC`'s snapshot variable, so `addC2` must inherit that snapshot as a
parameter too (transitive capture over the sibling call graph).  Otherwise the
lifted `addC2` would reference a free `$__liftfncl…` and not be closed. -/

private def siblingCapturePgm :=
#strata
program Core;
procedure useTwo(c : int, a : int)
{
  function addC(x : int) : int { int.add(x, c) }
  function addC2(x : int) : int { addC(addC(x)) }
  var r : int := addC2(a);
  assert r == int.add(int.add(a, c), c);
};
#end

/--
info: program Core;

function $__liftfncl_addC_1 ($__liftfncl_0 : int, x : int) : int {
  int.add(x, $__liftfncl_0)
}
function $__liftfncl_addC2_2 ($__liftfncl_0 : int, x : int) : int {
  $__liftfncl_addC_1($__liftfncl_0, $__liftfncl_addC_1($__liftfncl_0, x))
}
procedure useTwo (c : int, a : int)
{
  var $__liftfncl_0 : int := c;
  var r : int := $__liftfncl_addC2_2($__liftfncl_0, a);
  assert [assert_0]: r == int.add(int.add(a, c), c);
};
-/
#guard_msgs in
#eval (transformProgram siblingCapturePgm)

#guard allFuncsClosed (liftOnly siblingCapturePgm)
#guard allBodiesNoFuncDecl (liftOnly siblingCapturePgm)

/-! ### Example 8: sibling capture where the caller also captures its own constant

Like Example 7, but `addC2` additionally captures its own constant `c2`.  Its
extended capture set is therefore its own `c2` *plus* `addC`'s inherited `c`, so
the lifted `addC2` takes both snapshots as leading parameters. -/

private def siblingCaptureTwoConstsPgm :=
#strata
program Core;
procedure useTwo(c : int, c2 : int, a : int)
{
  function addC(x : int) : int { int.add(x, c) }
  function addC2(x : int) : int { int.add(addC(addC(x)), c2) }
  var r : int := addC2(a);
  assert r == int.add(int.add(int.add(a, c), c), c2);
};
#end

/--
info: program Core;

function $__liftfncl_addC_2 ($__liftfncl_0 : int, x : int) : int {
  int.add(x, $__liftfncl_0)
}
function $__liftfncl_addC2_3 ($__liftfncl_1 : int, $__liftfncl_0 : int, x : int) : int {
  int.add($__liftfncl_addC_2($__liftfncl_0, $__liftfncl_addC_2($__liftfncl_0, x)), $__liftfncl_1)
}
procedure useTwo (c : int, c2 : int, a : int)
{
  var $__liftfncl_0 : int := c;
  var $__liftfncl_1 : int := c2;
  var r : int := $__liftfncl_addC2_3($__liftfncl_1, $__liftfncl_0, a);
  assert [assert_0]: r == int.add(int.add(int.add(a, c), c), c2);
};
-/
#guard_msgs in
#eval (transformProgram siblingCaptureTwoConstsPgm)

#guard allFuncsClosed (liftOnly siblingCaptureTwoConstsPgm)
#guard allBodiesNoFuncDecl (liftOnly siblingCaptureTwoConstsPgm)

/-! ### Example 9: a lifted name must not collide with an existing top-level name

The generator would name the lifted `caller` as `caller_0`, but the program
already has a top-level `caller_0`.  The pass always uses a fresh identifier so
the two top-level functions stay distinct. -/

private def nameCollisionPgm :=
#strata
program Core;
function caller_0(x : int) : int { int.add(x, 1) }
procedure userProc(a : int)
{
  function caller(x : int) : int { int.add(x, 1) }
  var r : int := caller(a);
  assert r == int.add(a, 1);
};
#end

/--
info: program Core;

function caller_0 (x : int) : int {
  int.add(x, 1)
}
function $__liftfncl_caller_0 (x : int) : int {
  int.add(x, 1)
}
procedure userProc (a : int)
{
  var r : int := $__liftfncl_caller_0(a);
  assert [assert_0]: r == int.add(a, 1);
};
-/
#guard_msgs in
#eval (transformProgram nameCollisionPgm)

#guard allFuncsClosed (liftOnly nameCollisionPgm)
#guard allBodiesNoFuncDecl (liftOnly nameCollisionPgm)

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

/-! ### Example 13: an internal function declared inside a `while` loop body

Covers the `loop` arm of `collectLiftingFuncsFromStmt`.  `twice` is declared
inside a (nondeterministic) loop body — built as an AST to keep the focus on the
loop recursion rather than surface loop-guard syntax — and captures `c`.  It is
hoisted out, so no procedure body (including the loop body, which
`allBodiesNoFuncDecl` recurses into) still contains a `funcDecl`, and it is
closed with its captured `c` as the leading parameter `$__liftfncl_0 : int`
ahead of `x : int`.

Intentionally only one case of loop (.nondet, without any invariant or measure) is used
as a test case because the auxiliary components don't contribute to the lifting algorithm.
-/

private def funcInLoopProg :=
#strata
program Core;
    procedure inLoop(c : int, a : int) {
      while * {
        function twice(x : int) : int { c }
        var r : int := twice(a);
      }
    };
#end

private def funcInLoopOk : Bool :=
  match runLiftAst (translate funcInLoopProg) with
  | some p =>
    allBodiesNoFuncDecl p && allFuncsClosed p &&
    (match soleFunc p with
     | some f =>
       f.inputs.map (·.1.name) == ["$__liftfncl_0", "x"] &&
       decide (f.inputs.map (·.2) = [tyInt, tyInt])
     | none => false)
  | none => false

#guard funcInLoopOk

/-! ### Example 14: mixing a local type declaration with an internal function is rejected

A type introduced by an in-procedure `type T;` is not in scope at the top level,
where lifted `Decl.func`s are placed, so a lifted function that mentions the type
would fail to re-type-check.  Rather than analyze which functions use which
types, the pass conservatively rejects *any* procedure that combines a local
`type` declaration with an internal `funcDecl` — the combination is unsupported.
Here `h`'s argument and return type are the local `T`. -/

/-- Translate + type-check, then run *only* the lifting pass, returning its error
    diagnostic as a string (or a sentinel if it unexpectedly succeeded).  Used to
    assert the exact rejection message, not merely that an error occurred. -/
private def liftErrorMsg (t : StrataDDM.Program) : String :=
  let program := translate t
  let annotated := match Core.typeCheck quietOpts program with
    | .ok p => p
    | .error _ => program
  match Core.Transform.run annotated Core.liftInternalFuncDecls liftState with
  | .ok _ => "<unexpected: lift succeeded>"
  | .error e => toString (Std.format e)

private def localTypeArgRetPgm :=
#strata
program Core;
procedure useLocalType(a : int)
{
  type T;
  function h(x : T) : T { x }
};
#end

/--
info: "LiftInternalFuncDecls: procedure 'useLocalType' combines local type declaration(s) 'T' with internal function declaration(s); lifting internal functions in the presence of local type declarations is not supported"
-/
#guard_msgs in
#eval liftErrorMsg localTypeArgRetPgm

/-! ### Example 15: the rejection fires even when the function ignores the local type

The internal function `h` does not mention the local `type T;` at all (it merely
captures the `int` local `a`).  The simplified rule still rejects the procedure:
the mere co-occurrence of a local type declaration and an internal function is
unsupported, regardless of whether the function references the type. -/

private def localTypeUnrelatedPgm :=
#strata
program Core;
procedure useLocalTypeUnrelated(a : int)
{
  type T;
  function h(x : int) : int { int.add(x, a) }
  var r : int := h(0);
  assert r == a;
};
#end

/--
info: "LiftInternalFuncDecls: procedure 'useLocalTypeUnrelated' combines local type declaration(s) 'T' with internal function declaration(s); lifting internal functions in the presence of local type declarations is not supported"
-/
#guard_msgs in
#eval liftErrorMsg localTypeUnrelatedPgm

/-! ### Example 16: clashing internal function names within a procedure are rejected

Two `funcDecl`s that share a name (here `f`, in disjoint `if` branches) are
type-correct on their own, but the lift pass keys its call-site rewrite on the
original source name.  Lifting both would silently retarget one branch's calls
to the other branch's lifted function, so the pass rejects the clash outright in
its collecting phase. -/

private def clashingNamesPgm :=
#strata
program Core;
procedure inBranch(cond : bool, a : int)
{
  if (cond) {
    function f(x : int) : int { int.add(x, 100) }
    var r1 : int := f(a);
    assert r1 == int.add(a, 100);
  } else {
    function f(x : int) : int { int.add(x, 200) }
    var r2 : int := f(a);
    assert r2 == int.add(a, 200);
  }
};
#end

/--
info: LiftInternalFuncDecls: procedure 'inBranch' declares multiple internal functions with the clashing name(s) 'f'; internal function declarations must have distinct names
-/
#guard_msgs in
#eval IO.println (liftErrorMsg clashingNamesPgm)

/-! ### Example 17: the same internal function name in two different procedures

Cross-procedure name reuse is fine (unlike a clash *within* one procedure): each
procedure is lifted independently and the shared generator hands out distinct
fresh top-level names, so `f` in `p1` and `f` in `p2` become `$__liftfncl_f_0`
and `$__liftfncl_f_1`. -/

private def sameNameTwoProcsPgm :=
#strata
program Core;
procedure p1(a : int)
{
  function f(x : int) : int { int.add(x, 1) }
  var r : int := f(a);
  assert r == int.add(a, 1);
};
procedure p2(a : int)
{
  function f(x : int) : int { int.add(x, 2) }
  var r : int := f(a);
  assert r == int.add(a, 2);
};
#end

/--
info: program Core;

function $__liftfncl_f_0 (x : int) : int {
  int.add(x, 1)
}
procedure p1 (a : int)
{
  var r : int := $__liftfncl_f_0(a);
  assert [assert_0]: r == int.add(a, 1);
};
function $__liftfncl_f_1 (x : int) : int {
  int.add(x, 2)
}
procedure p2 (a : int)
{
  var r : int := $__liftfncl_f_1(a);
  assert [assert_1]: r == int.add(a, 2);
};
-/
#guard_msgs in
#eval (transformProgram sameNameTwoProcsPgm)

#guard allFuncsClosed (liftOnly sameNameTwoProcsPgm)
#guard allBodiesNoFuncDecl (liftOnly sameNameTwoProcsPgm)

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

/-! ### Example 20: an internal function clashing with a top-level function is rejected

The internal `shared` shares its name with the top-level `function shared`.  The
call-site rewrite (`substOps`) keys purely on the source name, so lifting would
retarget *every* `shared(...)` reference in the body — including the call before
the `funcDecl`, which lexically resolves to the top-level `shared` — to the
lifted internal function, silently changing the program's meaning.  The pass
rejects the clash up front rather than emit such an unsound program. -/

private def topLevelClashPgm :=
#strata
program Core;
function shared(x : int) : int { int.add(x, 100) }
procedure demo(a : int)
{
  var before : int := shared(a);
  function shared(x : int) : int { int.add(x, 200) }
  var after : int := shared(a);
  assert before == int.add(a, 100);
  assert after == int.add(a, 200);
};
#end

/--
info: "LiftInternalFuncDecls: procedure 'demo' declares internal function(s) 'shared' that clash with top-level function(s); internal function declarations must not shadow top-level functions"
-/
#guard_msgs in
#eval liftErrorMsg topLevelClashPgm

/-! ### Example 20b: an internal function clashing with a top-level `rec function` is rejected

Same as Example 20 but the top-level function is a member of a `Decl.recFuncBlock`
(surface syntax: `rec function`).  The shadow-detection guard must enumerate
`recFuncBlock` members as well as plain `Decl.func`s; otherwise `substOps` would
retarget the pre-`funcDecl` call — lexically resolving to the top-level
recursive function — to the lifted internal one, silently changing meaning. -/

private def recTopLevelClashPgm :=
#strata
program Core;
datatype IntList { Nil(), Cons(hd: int, tl: IntList) };
rec function shared (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1
};
procedure demo(a : IntList)
{
  var before : int := shared(a);
  function shared(xs : IntList) : int { 999 }
  var after : int := shared(a);
};
#end

/--
info: "LiftInternalFuncDecls: procedure 'demo' declares internal function(s) 'shared' that clash with top-level function(s); internal function declarations must not shadow top-level functions"
-/
#guard_msgs in
#eval liftErrorMsg recTopLevelClashPgm



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

/-! ### Polymorphic Example 3: an enclosing type variable used only in the function's signature

Regression for a lifted function whose enclosing type variable appears *only* in
its own signature, never in a captured value's type.  `g` captures nothing but
its parameter and result are the enclosing `V`; the lifted `g` must therefore
declare `V` in its `typeArgs`, or the post-lift type check rejects a program the
surface syntax accepts.
-/

private def sigOnlyTyVarPgm :=
#strata
program Core;
procedure pC5<V>(a : int)
{
  function g(y : V) : V { y }
};
#end

/-- `g` is hoisted closed, the program type-checks, and the lifted `g` is
    polymorphic in `V` (`∀V. (y : V) → V`) — `V` collected from the signature,
    not from any captured value. -/
private def sigOnlyTyVarOk : Bool :=
  let p := liftOnly sigOnlyTyVarPgm
  allBodiesNoFuncDecl p && allFuncsClosed p && programTypechecks p &&
  (match soleFunc p with
   | some f =>
     f.typeArgs == ["V"] &&
     decide (f.inputs.map (·.2) = [tyV]) &&
     decide (f.output = tyV)
   | none => false)

#guard sigOnlyTyVarOk


end LiftInternalFuncDeclsTests

end
