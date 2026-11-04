/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Transform.Passive.CoreWPSSA
meta import Strata.Languages.Core.ObligationExtraction
meta import Strata.Languages.Core.Factory
meta import Strata.Transform.DeadDefElim
meta import StrataTest.Languages.Core.Tests.WPTestUtils

/-! # The WP and SSA phases on examples

Translates small loop-free statement lists with the WP phase, the SSA phase and dead-definition
elimination (`wpSSALoopFree`, then `deadDefElim`) and checks the output's shape
(`Block.nondetIteLast`, `NoStmtAfterAssert`, `Block.readsDefined`), the duplication checker
(`noDuplication`), the number of output paths, and the exact printed output; then checks the
program-level phases on programs with several procedures and an axiom, the absence of fake
dependencies, write-through, always-exiting arms, exits and folding, renaming, the SSA folding
on hand-written guarded programs, the records of the two phases, guarded form, and the linear
implementations against their specifications. -/

meta section

namespace WPProgramTest

open Core Core.WP Core.DeadDefElim Lambda Imperative Imperative.BigStep Imperative.WP
  Imperative.DeadDefElim Strata.WPTestUtils

def id' (name : String) : CoreIdent := ⟨name, ()⟩
def int (n : Int) : Expression.Expr := .intConst () n
def md : MetaData Expression := #[]
def iv (n : String) : Expression.Expr := .fvar () (id' n) (some .int)
def gt (a b : Expression.Expr) : Expression.Expr := .app () (.app () intGtOp a) b
def add (a b : Expression.Expr) : Expression.Expr := .app () (.app () intAddOp a) b
def intTy : Expression.Ty := .forAll [] .int

def assert' (l : String) (e : Expression.Expr) : Statement := .cmd (.cmd (.assert l e md))
def cover' (l : String) (e : Expression.Expr) : Statement := .cmd (.cmd (.cover l e md))
def assume' (l : String) (e : Expression.Expr) : Statement := .cmd (.cmd (.assume l e md))
def set' (x : String) (e : Expression.Expr) : Statement := .cmd (.cmd (.set (id' x) (.det e) md))
def havoc' (x : String) : Statement := .cmd (.cmd (.set (id' x) .nondet md))
def init' (x : String) (e : Expression.Expr) : Statement :=
  .cmd (.cmd (.init (id' x) intTy (.det e) md))
def ite' (c : Expression.Expr) (t e : Statements) : Statement := .ite (.det c) t e md
def block' (l : String) (ss : Statements) : Statement := .block l ss md
def exit' (l : String) : Statement := .exit l md

def proc (params : List String) (ss : Statements) : Procedure := {
    header := { name := id' "P", typeArgs := [],
                inputs := params.map (fun x => (id' x, (.int : LMonoTy))), outputs := [] }
    spec := { preconditions := [], postconditions := [] }
    body := .structured ss }

/-- Translate `ss` with integer parameters `params`: the WP phase, the SSA phase, then
    dead-definition elimination. -/
def tr (params : List String) (ss : Statements) : Except String Statements := do
  let (_, _, so) ← wpSSALoopFree (IdSet.ofList []) (IdSet.ofList []) (proc params ss) ss
  pure (deadDefElim [] so.out)

/-- `tr` with the WP phase run without `checkLoopFree` (`wpEntry` alone), for the lists with an
    `exit` that targets no enclosing block, which the check rejects. -/
def trW (params : List String) (ss : Statements) : Except String Statements := do
  let w ← wpEntry (P := Expression) (IdSet.ofList []) (proc params ss).paramTys ss
  let (_, so) ← ssaLoopFree (IdSet.ofList []) (proc params ss) w.lay
  pure (deadDefElim [] so.out)

/-- `tr`, the empty list on error. -/
def trOut (params : List String) (ss : Statements) : Statements :=
  match tr params ss with | .ok o => o | .error _ => []

/-- The guarded program of `ss` (the WP phase alone), the empty list on error. -/
def guardedOut (params : List String) (ss : Statements) : Statements :=
  match wpLoopFree (IdSet.ofList []) (proc params ss) ss with | .ok w => w.lay | .error _ => []

/-- The obligations of a list (label and condition), at any depth, in order. -/
partial def oblsOf : Statements → List (String × Expression.Expr)
  | [] => []
  | .cmd (.cmd (.assert l e _)) :: r | .cmd (.cmd (.cover l e _)) :: r => (l, e) :: oblsOf r
  | .ite _ t e _ :: r => oblsOf t ++ oblsOf e ++ oblsOf r
  | .block _ b _ :: r => oblsOf b ++ oblsOf r
  | _ :: r => oblsOf r

/-- The labels of the obligations of a list. -/
def oblLabels (ss : Statements) : List String := (oblsOf ss).map (·.1)

/-- The labels of the obligations of a loop-free list, in loop-free order. -/
def oblLabelsLoopFree (ss : Statements) : List String := oblLabels ss

/-- The obligation entries the SSA phase records, with their substitutions. -/
def oblSubs (obls : List (Option (LogEntry Expression))) :
    List (String × List (CoreIdent × CoreIdent × Option Expression.Ty)) :=
  obls.filterMap fun e => match e with | some (.obl l sub) => some (l, sub) | _ => none

/-- For every obligation entry `obl l sub` the SSA phase records, the obligation labelled `l` of
    its output `out` is the one of its input `lay` under `sub` (`substObl`). -/
def oblSubsMatch (lay out : Statements) (obls : List (Option (LogEntry Expression))) : Bool :=
  (oblSubs obls).all fun (l, sub) =>
    match (oblsOf lay).lookup l, (oblsOf out).lookup l with
    | some e, some e' => substObl sub e == e'
    | _, _ => false

/-- The obligation program's inputs: the parameters under their entry names. -/
def inputsOf (params : List String) (ss : Statements) : List CoreIdent :=
  match wpSSALoopFree (IdSet.ofList []) (IdSet.ofList []) (proc params ss) ss with
  | .ok (_, ρ0, _) => params.map (fun x => Ren.get ρ0 (id' x))
  | .error _ => []

/-- Does `ss` translate to an output that has the obligation-program shape, is well scoped
    in the entry names of `params` and duplicates no expression of `ss`? -/
def good (params : List String) (ss : Statements) : Bool :=
  match tr params ss with
  | .ok out =>
    Block.nondetIteLast out && Block.readsDefined (inputsOf params ss) out && noDuplication ss out
  | .error _ => false

/-- Is every `assert` of the translation of `ss` the last statement of its list? -/
def assertLast (params : List String) (ss : Statements) : Bool :=
  match tr params ss with | .ok out => NoStmtAfterAssert out | .error _ => false

/-- Number of root-to-leaf paths ending in an obligation. -/
partial def paths : Statements → Nat
  | [] => 0
  | .ite .nondet t e _ :: _ => paths t + paths e
  | s :: rest => (if Stmt.isCheck s then 1 else 0) + paths rest

/-- Number of obligation paths of the translation of `ss` (0 on error). -/
def npaths (params : List String) (ss : Statements) : Nat :=
  match tr params ss with | .ok out => paths out | .error _ => 0

-- 1. straight-line, two asserts: a chain `ite * [.. assert a1] [.. assert a2]`
def ex1 : Statements := [assert' "a1" (gt (iv "x") (int 0)), set' "x" (add (iv "x") (int 1)),
  assert' "a2" (gt (iv "x") (int 1))]

/-- The printed output of a translation, or its error. -/
def show' (r : Except String Statements) : String :=
  match r with | .ok o => toString (Std.format o) | .error e => "ERROR " ++ e

/-- The lines `ls` joined by newlines. -/
def lines (ls : List String) : String := "\n".intercalate ls

-- 2. ite with local branches
def ex2 : Statements := [ite' (gt (iv "x") (int 0)) [assert' "t" (gt (iv "y") (int 0))]
  [assert' "e" (gt (iv "y") (int 1))], assert' "after" (gt (iv "y") (int 2))]
-- 3. ite the continuation depends on
def ex3 : Statements := [ite' (gt (iv "x") (int 0))
    [set' "y" (add (iv "y") (int 1)), assert' "t" (gt (iv "y") (int 0))]
    [assume' "ea" (gt (iv "y") (int 5))],
  assert' "after" (gt (iv "y") (int 2))]
-- 4. nested ites
def ex4 : Statements := [ite' (gt (iv "x") (int 0))
    [ite' (gt (iv "x") (int 1)) [set' "y" (int 1)] [set' "y" (int 2)],
      assert' "in" (gt (iv "y") (int 0))]
    [set' "y" (int 3)],
  assert' "after" (gt (iv "y") (int 2))]
-- 5. block / exit
def ex5 : Statements := [block' "L" [ite' (gt (iv "x") (int 0)) [set' "y" (int 1), exit' "L"] [],
    set' "y" (int 2)], assert' "after" (gt (iv "y") (int 0))]
-- 6. a cover
def ex6 : Statements :=
  [havoc' "y", cover' "c" (gt (iv "y") (iv "x")), assert' "a" (gt (iv "y") (int 0))]
-- 7. trailing statements dropped
def ex7 : Statements :=
  [assert' "a" (gt (iv "x") (int 0)), set' "x" (int 1), assume' "z" (gt (iv "x") (int 0))]
-- 8. a partial expression in a branch that a path skips, the `ite` ending the list
def div' (a b : Expression.Expr) : Expression.Expr := .app () (.app () intDivOp a) b
def ex8 : Statements := [ite' (gt (iv "g") (int 0)) [set' "x" (div' (iv "y") (int 0))]
  [assert' "a" (.boolConst () false)]]
-- 8b. the same `ite` followed by an obligation
def ex8b : Statements := ex8 ++ [assert' "b" (gt (iv "y") (int 0))]
-- 9. a local of a laid-out branch
def ex9 : Statements := [ite' (gt (iv "x") (int 0))
    [init' "z" (add (iv "x") (int 1)), assume' "p" (gt (iv "z") (int 1))] [],
  assert' "a" (gt (iv "x") (int 0))]

-- 10. consecutive assertions
def ex10 : Statements := [assert' "a1" (gt (iv "x") (int 0)), assert' "a2" (gt (iv "x") (int 1)),
  set' "x" (add (iv "x") (int 1)), assert' "a3" (gt (iv "x") (int 2))]
-- 11. the reference example: a laid-out branch with a local, joined by a lazy merge
def mul (a b : Expression.Expr) : Expression.Expr := .app () (.app () intMulOp a) b
def ge (a b : Expression.Expr) : Expression.Expr := .app () (.app () intGeOp a) b
def ex11 : Statements := [.cmd (.cmd (.init (id' "z") intTy .nondet md)),
  ite' (gt (iv "x") (int 0)) [set' "z" (add (iv "x") (int 1)), set' "y" (mul (iv "z") (int 2))]
    [set' "y" (int 0)],
  assert' "pos" (ge (iv "y") (int 0))]

/-! ## Checks -/

-- Every example translates to an output that has the obligation-program shape, is well
-- scoped and duplicates no expression.
#guard good ["x"] ex1
#guard good ["x", "y"] ex2
#guard good ["x", "y"] ex3
#guard good ["x", "y"] ex4
#guard good ["x", "y"] ex5
#guard good ["x", "y"] ex6
#guard good ["x"] ex7
#guard good ["g", "x", "y"] ex8
#guard good ["g", "x", "y"] ex8b
#guard good ["x"] ex9
#guard good ["x"] ex10
#guard good ["x", "y"] ex11

-- Every `assert` is the last statement of its list, except after consecutive assertions.
#guard assertLast ["x"] ex1
#guard assertLast ["x", "y"] ex2
#guard assertLast ["x", "y"] ex3
#guard assertLast ["x", "y"] ex4
#guard assertLast ["x", "y"] ex5
#guard assertLast ["x", "y"] ex6
#guard assertLast ["x"] ex7
#guard assertLast ["g", "x", "y"] ex8
#guard assertLast ["g", "x", "y"] ex8b
#guard assertLast ["x"] ex9
#guard !assertLast ["x"] ex10
#guard assertLast ["x", "y"] ex11

-- One output path per loop-free obligation on a feasible path.
#guard npaths ["x"] ex1 == 2
#guard npaths ["x", "y"] ex2 == 3
#guard npaths ["x", "y"] ex3 == 2
#guard npaths ["x", "y"] ex4 == 2
#guard npaths ["x", "y"] ex5 == 1
#guard npaths ["x", "y"] ex6 == 2
#guard npaths ["x"] ex7 == 1
#guard npaths ["g", "x", "y"] ex8 == 1
#guard npaths ["g", "x", "y"] ex8b == 2
#guard npaths ["x"] ex9 == 1
#guard npaths ["x"] ex10 == 3
#guard npaths ["x", "y"] ex11 == 1

-- The chain shape of a straight-line program; obligations are on the SSA names.
#guard show' (tr ["x"] ex1) == lines [
    "{",
    "  if * {",
    "    assert [a1]: int.gt(x@0, 0);",
    "  }",
    "  else {",
    "    var x@1 : int := int.add(x@0, 1);",
    "    assert [a2]: int.gt(x@1, 1);",
    "  }",
    "}"]

-- Local branches become side branches: `ite * [assume g; t] [ite * [assume ¬g; e] [after]]`.
#guard show' (tr ["x", "y"] ex2) == lines [
    "{",
    "  var g@2 : bool := int.gt(x@0, 0);",
    "  if * {",
    "    assume [wp$reach]: g@2;",
    "    assert [t]: int.gt(y@1, 0);",
    "  }",
    "  else {",
    "    if * {",
    "      assume [wp$reach]: if g@2 then false else true;",
    "      assert [e]: int.gt(y@1, 1);",
    "    }",
    "    else {",
    "      assert [after]: int.gt(y@1, 2);",
    "    }",
    "  }",
    "}"]

-- A dependent branch is laid out: its assumption is `assume (r ⟹ a)`; the else arm reads
-- the entry value of `y` (saved before the then arm and restored after it), and the
-- continuation reads the then arm's guarded definition of `y`, no merge.
#guard show' (tr ["x", "y"] ex3) == lines [
    "{",
    "  var g@2 : bool := int.gt(x@0, 0);",
    "  var y@4 : int := if g@2 then int.add(y@1, 1) else y@1;",
    "  if * {",
    "    assume [wp$reach]: g@2;",
    "    assert [t]: int.gt(y@4, 0);",
    "  }",
    "  else {",
    "    assume [ea]: if g@2 then true else int.gt(y@1, 5);",
    "    assert [after]: int.gt(y@4, 2);",
    "  }",
    "}"]

-- Nested ites: the inner `ite` is laid out under the outer branch's reachability, its
-- condition and assignments evaluated only when that reachability holds; the guarded writes
-- of each arm leave `y` unchanged off it, so no merge is needed.
#guard show' (tr ["x", "y"] ex4) == lines [
    "{",
    "  var g@3 : bool := int.gt(x@0, 0);",
    "  var g@4 : bool := if g@3 then int.gt(x@0, 1) else false;",
    "  var y@5 : int := if g@4 then 1 else y@1;",
    "  var y@6 : int := if g@3 then if g@4 then y@5 else 2 else y@5;",
    "  if * {",
    "    assume [wp$reach]: g@3;",
    "    assert [in]: int.gt(y@6, 0);",
    "  }",
    "  else {",
    "    var y@7 : int := if g@3 then y@6 else 3;",
    "    assert [after]: int.gt(y@7, 2);",
    "  }",
    "}"]

-- Block / exit: after the `exit`, the block's rest is guarded by its reach (`r@4`, false on
-- the exiting path); the then arm always exits, so its write is undone for the continuing
-- path and merged at the block's end.
#guard show' (tr ["x", "y"] ex5) == lines [
    "{",
    "  var g@5 : bool := int.gt(x@0, 0);",
    "  var y@6 : int := if g@5 then 1 else y@1;",
    "  var r@8 : bool := if g@5 then false else true;",
    "  var y@9 : int := if r@8 then 2 else y@1;",
    "  var y@10 : int := if g@5 then y@6 else y@9;",
    "  assert [after]: int.gt(y@10, 0);",
    "}"]

-- A cover is an obligation like an assert; consecutive obligations share one side branch.
#guard show' (tr ["x", "y"] ex6) == lines [
    "{",
    "  var y@2 : int;",
    "  cover [c]: int.gt(y@2, x@0);",
    "  assert [a]: int.gt(y@2, 0);",
    "}"]

-- Trailing statements after the last obligation are dropped.
#guard show' (tr ["x"] ex7) == lines [
    "{",
    "  assert [a]: int.gt(x@0, 0);",
    "}"]

-- An `ite` after which no obligation follows is a real branch, each arm on its own path; the
-- then-arm reaches no obligation, so the branch is its else-arm.
#guard show' (tr ["g", "x", "y"] ex8) == lines [
    "{",
    "  var g@4 : bool := int.gt(g@1, 0);",
    "  assume [wp$reach]: if g@4 then false else true;",
    "  assert [a]: false;",
    "}"]

-- A partial expression of a laid-out branch is evaluated only when the branch is taken: the
-- assignment selects it under the guard and keeps the current value of `x` otherwise; no
-- obligation reads it, so its definition is erased.
#guard show' (tr ["g", "x", "y"] ex8b) == lines [
    "{",
    "  var g@4 : bool := int.gt(g@1, 0);",
    "  if * {",
    "    assume [wp$reach]: if g@4 then false else true;",
    "    assert [a]: false;",
    "  }",
    "  else {",
    "    assert [b]: int.gt(y@3, 0);",
    "  }",
    "}"]

-- A local of a laid-out branch gets a quantified default (`z@3`), selected when the branch is
-- not taken; the branch's assumption is evaluated only when it is taken.
#guard show' (tr ["x"] ex9) == lines [
    "{",
    "  var g@1 : bool := int.gt(x@0, 0);",
    "  var z@3 : int;",
    "  var z@4 : int := if g@1 then int.add(x@0, 1) else z@3;",
    "  assume [p]: if g@1 then int.gt(z@4, 1) else true;",
    "  assert [a]: int.gt(x@0, 0);",
    "}"]

-- Consecutive assertions form one side branch, so an `assert` is followed by a statement
-- (`NoStmtAfterAssert` does not hold).
#guard show' (tr ["x"] ex10) == lines [
    "{",
    "  if * {",
    "    assert [a1]: int.gt(x@0, 0);",
    "    assert [a2]: int.gt(x@0, 1);",
    "  }",
    "  else {",
    "    var x@1 : int := int.add(x@0, 1);",
    "    assert [a3]: int.gt(x@1, 2);",
    "  }",
    "}"]

-- The reference example: a laid-out branch with a local; the then arm's write of `y` is the
-- default of the else arm's, so the else arm's definition is the merge.
#guard show' (tr ["x", "y"] ex11) == lines [
    "{",
    "  var z@2 : int;",
    "  var g@3 : bool := int.gt(x@0, 0);",
    "  var z@4 : int := if g@3 then int.add(x@0, 1) else z@2;",
    "  var y@5 : int := if g@3 then int.mul(z@4, 2) else y@1;",
    "  var y@6 : int := if g@3 then y@5 else 0;",
    "  assert [pos]: int.ge(y@6, 0);",
    "}"]

-- The duplication checker rejects a copied expression.
#guard !noDuplication [set' "y" (add (iv "x") (int 1))]
  [set' "y" (add (iv "x") (int 1)), set' "z" (add (iv "x") (int 1))]

-- Introduced names are `b@n`, the counter skipping the names to avoid.
#guard (freshName (P := Expression) "x" 3).name == "x@3"
#guard ((freshIn (P := Expression)
  ⟨IdSet.ofList [id' "x@0", id' "x@1"], IdSet.ofList []⟩ "x" 0).1).name == "x@2"

-- A procedure whose identifiers have the form of introduced names is translated: the
-- introduced names skip them.
def ex12 : Statements := [set' "x" (add (iv "x") (iv "x@0")),
  assert' "a" (gt (iv "x") (iv "x@1"))]
#guard good ["x", "x@0", "x@1"] ex12
#guard show' (tr ["x", "x@0", "x@1"] ex12) == lines [
    "{",
    "  var x@5 : int := int.add(x@2, x@0@3);",
    "  assert [a]: int.gt(x@5, x@1@4);",
    "}"]

-- An `ite` ending the procedure is a real branch: each arm is translated on its own path, so
-- the else-arm's obligation does not carry the then-arm's definition of `x`.
def ex13 : Statements := [ite' (gt (iv "c") (int 0))
  [set' "x" (int 1), assert' "a1" (gt (iv "x") (int 0))]
  [set' "x" (int 2), assert' "a2" (gt (iv "x") (int 1))]]
#guard good ["c", "x"] ex13
#guard npaths ["c", "x"] ex13 == 2
#guard show' (tr ["c", "x"] ex13) == lines [
    "{",
    "  var g@2 : bool := int.gt(c@0, 0);",
    "  if * {",
    "    assume [wp$reach]: g@2;",
    "    var x@3 : int := 1;",
    "    assert [a1]: int.gt(x@3, 0);",
    "  }",
    "  else {",
    "    assume [wp$reach]: if g@2 then false else true;",
    "    var x@4 : int := 2;",
    "    assert [a2]: int.gt(x@4, 1);",
    "  }",
    "}"]

-- The same `ite` after an `exit` that may leave the enclosing block: it is translated under
-- the reach of the block's rest (`r@5`), each arm assuming it with its guard.
def ex14 : Statements := [block' "l" [ite' (gt (iv "c") (int 0)) [exit' "l"] [],
  ite' (gt (iv "d") (int 0))
    [set' "x" (int 1), assert' "a1" (gt (iv "x") (int 0))]
    [set' "x" (int 2), assert' "a2" (gt (iv "x") (int 1))]]]
#guard good ["c", "d", "x"] ex14
#guard npaths ["c", "d", "x"] ex14 == 2
#guard show' (tr ["c", "d", "x"] ex14) == lines [
    "{",
    "  var g@6 : bool := int.gt(c@0, 0);",
    "  var r@8 : bool := if g@6 then false else true;",
    "  var g@9 : bool := if r@8 then int.gt(d@1, 0) else false;",
    "  if * {",
    "    assume [wp$reach]: g@9;",
    "    var x@10 : int := 1;",
    "    assert [a1]: int.gt(x@10, 0);",
    "  }",
    "  else {",
    "    assume [wp$reach]: if r@8 then if g@9 then false else true else false;",
    "    var x@11 : int := 2;",
    "    assert [a2]: int.gt(x@11, 1);",
    "  }",
    "}"]

/-! ## Rejected loop-free lists

The translation fails on a list that does not pass `checkLoopFree`: one that reads a variable
that is neither a parameter nor a local in scope, that is not well scoped (`Block.wellScopedB`),
or that has an `exit` targeting no enclosing block (`Block.checkExitsCoveredByBlocks`). -/

/-- The error of the translation of `ss` with integer parameters `params`, if it fails. -/
def err (params : List String) (ss : Statements) : String :=
  match tr params ss with | .ok _ => "ok" | .error e => e

-- A read of a variable that is not a parameter.
#guard err ["x"] [assert' "a" (gt (iv "y") (int 0))] ==
  "WP: procedure 'P': 'y' is read but is neither a parameter nor a local in scope"
-- A read of a local after the block that declares it, and an assignment to it (an
-- assignment reads the variable's current value).
#guard err ["x"] [block' "L" [init' "z" (int 0)], assert' "a" (gt (iv "z") (int 0))] ==
  "WP: procedure 'P': 'z' is read but is neither a parameter nor a local in scope"
#guard err ["x"] [block' "L" [init' "z" (int 0)], set' "z" (int 1)] ==
  "WP: procedure 'P': 'z' is read but is neither a parameter nor a local in scope"

/-- The error for a list that is not well scoped. -/
def notWellScoped : String :=
  "WP: procedure 'P': not well scoped (a local declared twice in a scope or \
    named as a parameter, or a variable read or assigned outside the scope of its declaration)"

-- A local declared twice in one scope.
#guard err ["x"] [init' "z" (int 0), init' "z" (int 1), assert' "a" (gt (iv "z") (iv "x"))] ==
  notWellScoped
-- A local named as a parameter.
#guard err ["x"] [init' "x" (int 0), assert' "a" (gt (iv "x") (int 0))] == notWellScoped
-- A loop, a nondeterministic guard: rejected by the check, and by the WP phase itself.
#guard err ["x"] [.loop (.det (gt (iv "x") (int 0))) none [] [] md] == notWellScoped
#guard err ["x"] [.ite .nondet [] [] md] == notWellScoped

/-- The error for a list with an `exit` that targets no enclosing block. -/
def uncoveredExit : String := "WP: procedure 'P': an 'exit' targets no enclosing block"

-- An `exit` outside every block, and one whose label names no enclosing block.
#guard err ["x"] [exit' "L"] == uncoveredExit
#guard err ["x"] [block' "L" [assert' "a" (gt (iv "x") (int 0))], exit' "L"] == uncoveredExit
#guard err ["x"] [block' "L" [exit' "M"]] == uncoveredExit
-- An `exit` targeting an enclosing block is accepted.
#guard err ["x"] [block' "L" [exit' "L"]] == "ok"

/-- The error of the WP phase on `ss`, without the check, if it fails. -/
def errW (ss : Statements) : String :=
  match wpEntry (P := Expression) (IdSet.ofList []) [] ss with
  | .ok _ => "ok"
  | .error e => e

#guard errW [.loop (.det (gt (iv "x") (int 0))) none [] [] md] == "WP: loop (run loopElim first)"
#guard errW [.ite .nondet [] [] md] == "WP: nondeterministic guard (run nondetElim first)"

-- An in-out parameter that the list does not assign is accepted: `old x` and `x` share the
-- fresh entry name `x@0`.
def inoutProc : Procedure :=
  { proc ["x"] [] with header := { (proc ["x"] []).header with outputs := [(id' "x", .int)] } }
#guard match wpSSALoopFree (IdSet.ofList []) (IdSet.ofList []) inoutProc
    [assert' "a" (gt (iv "x") (int 0))] with
  | .ok (_, ρ0, _) => (Ren.get ρ0 (CoreIdent.mkOld "x")).name == "x@0" &&
      (Ren.get ρ0 (id' "x")).name == "x@0"
  | .error _ => false

-- Every parameter gets a fresh entry name, and the entry names avoid the global names: with
-- a global `x@0`, the parameter `x` starts as `x@1`.
#guard show' (tr ["x"] [assert' "a" (gt (iv "x") (int 0))]) == lines [
    "{",
    "  assert [a]: int.gt(x@0, 0);",
    "}"]
#guard match wpSSALoopFree (IdSet.ofList []) (IdSet.ofList [id' "x@0"]) (proc ["x"] [])
    [assert' "a" (gt (iv "x") (int 0))] with
  | .ok (_, ρ0, _) => (Ren.get ρ0 (id' "x")).name == "x@1" | .error _ => false


/-! ## One obligation procedure per source procedure -/

def namedProc (n : String) (ss : Statements) : Procedure :=
  { proc ["x"] ss with header := { (proc ["x"] ss).header with name := id' n } }

def twoProcs : Program :=
  { decls := [.proc (namedProc "P" [assert' "p1" (gt (iv "x") (int 0))]) .empty,
              .proc (namedProc "Q" [assert' "q1" (gt (iv "x") (int 1)),
                assert' "q2" (gt (iv "x") (int 2))]) .empty] }

def procNames (p : Program) : List String :=
  p.decls.filterMap fun d => match d with | .proc q _ => some q.header.name.name | _ => none

-- Two source procedures give two obligation procedures, with the same names.
#guard match wpSSAProgramWith [] { decls := [] } [] twoProcs with
  | .ok p => procNames p == ["P", "Q"] | .error _ => false

-- Extraction accepts several obligation procedures: one assert obligation per assert, in
-- source order.
#guard match wpSSAProgramWith [] { decls := [] } [] twoProcs with
  | .ok p => match Core.ObligationExtraction.extractObligations p with
    | .ok obs => obs.toList.map (fun (o : ProofObligation Expression) => (o.label, o.property))
        == [("p1", .assert), ("q1", .assert), ("q2", .assert)]
    | .error _ => false
  | .error _ => false

-- Axiom scope: each obligation procedure is preceded by exactly the axioms its source
-- procedure is preceded by (axioms are kept in place, not hoisted before every procedure).
def procAxProc : Program :=
  { decls := [.proc (namedProc "P" [assert' "p1" (gt (iv "x") (int 0))]) .empty,
              .ax { name := "A", e := .true () } .empty,
              .proc (namedProc "Q" [assert' "q1" (gt (iv "x") (int 1))]) .empty] }

#guard match wpSSAProgramWith [] { decls := [] } [] procAxProc with
  | .ok p => (Program.axiomScopes p).map (fun (n, axs) => (n, axs.length)) == [("P", 0), ("Q", 1)]
      && axiomScopesAgree procAxProc p
  | .error _ => false

-- The global names of a program: its functions (constants included), procedures and types,
-- and the constructors, testers and destructors of its datatypes.  With a function `x@0`,
-- the obligation procedure of `P` reads its parameter `x` as `x@1`.  The program-level
-- declarations (`declProgram`) carry the function, as `wpProgram` builds them.
def globalProg : Program :=
  { decls := [.func (Core.Function.const (id' "x@0") .int) .empty,
              .proc (namedProc "P" [assert' "p1" (gt (iv "x") (int 0))]) .empty] }
#guard (declNames globalProg).map (·.name) == ["x@0", "P"]
/-- The body of the procedure `n` of a program. -/
def procBody (n : String) (r : Except String Program) : Except String Statements := do
  let p ← r
  let body? : Option Procedure.Body := p.decls.findSome? fun d => match d with
    | .proc q _ => if q.header.name.name == n then some q.body else none
    | _ => none
  match body? with
  | some (.structured ss) => pure ss
  | _ => throw s!"no procedure {n}"

#guard show' (procBody "P" (wpSSAProgramWith [] { decls := globalProg.decls.take 1 } []
    globalProg)) == lines [
    "{",
    "  assert [p1]: int.gt(x@1, 0);",
    "}"]

/-! ## No fake dependency

The else arm of a laid-out `ite` reads the values the then arm's guarded writes leave off the
then arm: the variables the then arm assigns and the else arm reads are saved before the then arm
and restored after it, so the else arm's definitions read the entry values, and the then arm's
definitions they would otherwise read are erased. -/

def havocInit (x : String) : Statement := .cmd (.cmd (.init (id' x) intTy .nondet md))
def eq' (a b : Expression.Expr) : Expression.Expr := .eq () a b
def le' (a b : Expression.Expr) : Expression.Expr := .app () (.app () intLeOp a) b
def c0 (c : String) : Expression.Expr := gt (iv c) (int 0)

/-- Does an identifier of `ss` equal `x`? -/
def mentions (ss : Statements) (x : CoreIdent) : Bool := (Block.idents ss).contains x

/-- The entry name of the parameter `x` in the translation of `ss`. -/
def entryOf (params : List String) (ss : Statements) (x : String) : CoreIdent :=
  match wpSSALoopFree (IdSet.ofList []) (IdSet.ofList []) (proc params ss) ss with
  | .ok (_, ρ0, _) => Ren.get ρ0 (id' x)
  | .error _ => id' x

/-- The number of `init`s of `ss`, at any depth. -/
def nInits (ss : Statements) : Nat := (stmtsInits ss).length

/-- The number of `init`s of `ss` of a name with base `b` (`b@n`), at any depth: the
    definitions of the loop-free variable `b`. -/
def nDefs (ss : Statements) (b : String) : Nat :=
  ((stmtsInits ss).filter fun x => (x.name.splitOn "@").head? == some b).length

def elseReadsTemp : Statements := [havocInit "x", init' "y" (iv "b"),
  ite' (c0 "c") [set' "x" (add (iv "x") (iv "a"))] [set' "y" (add (iv "x") (int 1))],
  assert' "a" (gt (iv "y") (int 0))]
#guard good ["a", "b", "c"] elseReadsTemp
#guard !mentions (trOut ["a", "b", "c"] elseReadsTemp) (entryOf ["a", "b", "c"] elseReadsTemp "a")
#guard show' (tr ["a", "b", "c"] elseReadsTemp) == lines [
    "{",
    "  var x@4 : int;",
    "  var g@5 : bool := int.gt(c@2, 0);",
    "  var y@7 : int := if g@5 then b@1 else int.add(x@4, 1);",
    "  assert [a]: int.gt(y@7, 0);",
    "}"]

def elseObl : Statements := [ite' (c0 "c") [set' "x" (int 1)]
    [set' "x" (int 2), assert' "e" (eq' (iv "x") (int 2))],
  assert' "after" (gt (iv "x") (int 0))]
#guard good ["c", "x"] elseObl
#guard show' (tr ["c", "x"] elseObl) == lines [
    "{",
    "  var g@2 : bool := int.gt(c@0, 0);",
    "  var x@4 : int := if g@2 then 1 else x@1;",
    "  var x@5 : int := if g@2 then x@1 else 2;",
    "  if * {",
    "    assume [wp$reach]: if g@2 then false else true;",
    "    assert [e]: x@5 == 2;",
    "  }",
    "  else {",
    "    var x@6 : int := if g@2 then x@4 else x@5;",
    "    assert [after]: int.gt(x@6, 0);",
    "  }",
    "}"]

def elseNested : Statements := [ite' (c0 "c1") [ite' (c0 "c2") [set' "x" (int 1)] []]
    [assert' "e" (gt (iv "x") (int 0))],
  assert' "after" (ge (iv "x") (int 0))]
#guard good ["c1", "c2", "x"] elseNested
#guard show' (tr ["c1", "c2", "x"] elseNested) == lines [
    "{",
    "  var g@3 : bool := int.gt(c1@0, 0);",
    "  var g@4 : bool := if g@3 then int.gt(c2@1, 0) else false;",
    "  var x@6 : int := if g@4 then 1 else x@2;",
    "  if * {",
    "    assume [wp$reach]: if g@3 then false else true;",
    "    assert [e]: int.gt(x@2, 0);",
    "  }",
    "  else {",
    "    assert [after]: int.ge(x@6, 0);",
    "  }",
    "}"]

/-! ## Write-through

A guarded write leaves the variable unchanged off its arm, so a variable assigned in one arm
needs no merge, and one assigned in both arms needs none when the else arm does not read it. -/

def oneArm : Statements := [ite' (c0 "c") [set' "x" (int 1)] [],
  assert' "a" (gt (iv "x") (int 0))]
#guard nDefs (trOut ["c", "x"] oneArm) "x" == 1
#guard show' (tr ["c", "x"] oneArm) == lines [
    "{",
    "  var g@2 : bool := int.gt(c@0, 0);",
    "  var x@3 : int := if g@2 then 1 else x@1;",
    "  assert [a]: int.gt(x@3, 0);",
    "}"]

def twoArm : Statements := [ite' (c0 "c") [set' "x" (int 1)] [set' "x" (int 2)],
  assert' "a" (gt (iv "x") (int 0))]
#guard nDefs (trOut ["c", "x"] twoArm) "x" == 2
#guard show' (tr ["c", "x"] twoArm) == lines [
    "{",
    "  var g@2 : bool := int.gt(c@0, 0);",
    "  var x@3 : int := if g@2 then 1 else x@1;",
    "  var x@4 : int := if g@2 then x@3 else 2;",
    "  assert [a]: int.gt(x@4, 0);",
    "}"]

def chain3 : Statements := [ite' (c0 "c1") [set' "x" (int 1)] [set' "x" (int 2)],
  ite' (c0 "c2") [set' "x" (int 3)] [set' "x" (int 4)],
  ite' (c0 "c3") [set' "x" (int 5)] [set' "x" (int 6)], assert' "a" (gt (iv "x") (int 0))]
#guard nDefs (trOut ["c1", "c2", "c3", "x"] chain3) "x" == 6
#guard show' (tr ["c1", "c2", "c3", "x"] chain3) == lines [
    "{",
    "  var g@5 : bool := int.gt(c1@0, 0);",
    "  var x@6 : int := if g@5 then 1 else x@3;",
    "  var x@7 : int := if g@5 then x@6 else 2;",
    "  var g@8 : bool := int.gt(c2@1, 0);",
    "  var x@9 : int := if g@8 then 3 else x@7;",
    "  var x@10 : int := if g@8 then x@9 else 4;",
    "  var g@11 : bool := int.gt(c3@2, 0);",
    "  var x@12 : int := if g@11 then 5 else x@10;",
    "  var x@13 : int := if g@11 then x@12 else 6;",
    "  assert [a]: int.gt(x@13, 0);",
    "}"]

/-! ## Always-exiting arms

After an arm that always exits, its assignments are undone for the continuing paths and
delivered by one merge per variable at the end of the innermost block its exits target. -/

def axBlock : Statements := [block' "L" [ite' (c0 "c") [set' "x" (int 1), exit' "L"] [],
    assert' "in" (eq' (iv "x") (int 0))],
  assert' "after" (ge (iv "x") (int 0))]
#guard good ["c", "x"] axBlock
#guard nDefs (trOut ["c", "x"] axBlock) "x" == 2
#guard show' (tr ["c", "x"] axBlock) == lines [
    "{",
    "  var g@5 : bool := int.gt(c@0, 0);",
    "  var x@6 : int := if g@5 then 1 else x@1;",
    "  var r@8 : bool := if g@5 then false else true;",
    "  if * {",
    "    assume [wp$reach]: r@8;",
    "    assert [in]: x@1 == 0;",
    "  }",
    "  else {",
    "    var x@9 : int := if g@5 then x@6 else x@1;",
    "    assert [after]: int.ge(x@9, 0);",
    "  }",
    "}"]

def axTwoDepths : Statements := [block' "t" [block' "u" [
    ite' (c0 "c1") [set' "x" (int 1), exit' "u"] [],
    ite' (c0 "c2") [set' "x" (int 2), exit' "t"] []]],
  assert' "a" (eq' (iv "x") (int 0))]
#guard good ["c1", "c2", "x"] axTwoDepths
#guard show' (tr ["c1", "c2", "x"] axTwoDepths) == lines [
    "{",
    "  var g@5 : bool := int.gt(c1@0, 0);",
    "  var x@6 : int := if g@5 then 1 else x@2;",
    "  var r@10 : bool := if g@5 then false else true;",
    "  var g@11 : bool := if r@10 then int.gt(c2@1, 0) else false;",
    "  var x@12 : int := if g@11 then 2 else x@2;",
    "  var x@15 : int := if g@5 then x@6 else x@2;",
    "  var x@17 : int := if g@11 then x@12 else x@15;",
    "  assert [a]: x@17 == 0;",
    "}"]

-- An `exit` that targets no enclosing block: `checkLoopFree` rejects the list, and the WP phase
-- alone assumes away the paths that take it.
def axTop : Statements := [ite' (c0 "c") [set' "x" (int 1), exit' "Z"] [],
  assert' "a" (eq' (iv "x") (int 0))]
#guard err ["c", "x"] axTop == uncoveredExit
#guard show' (trW ["c", "x"] axTop) == lines [
    "{",
    "  var g@2 : bool := int.gt(c@0, 0);",
    "  assume [wp$join]: if g@2 then false else true;",
    "  assert [a]: x@1 == 0;",
    "}"]

def axTwoExits : Statements := [block' "L" [
    ite' (c0 "c") [set' "x" (int 1), ite' (c0 "d") [exit' "L"] [exit' "L"]] [],
    assert' "in" (eq' (iv "x") (int 0))],
  assert' "after" (ge (iv "x") (int 0))]
#guard good ["c", "d", "x"] axTwoExits
#guard show' (tr ["c", "d", "x"] axTwoExits) == lines [
    "{",
    "  var g@4 : bool := int.gt(c@0, 0);",
    "  var x@5 : int := if g@4 then 1 else x@2;",
    "  var r@12 : bool := if g@4 then false else true;",
    "  if * {",
    "    assume [wp$reach]: r@12;",
    "    assert [in]: x@2 == 0;",
    "  }",
    "  else {",
    "    var x@13 : int := if g@4 then x@5 else x@2;",
    "    assert [after]: int.ge(x@13, 0);",
    "  }",
    "}"]

def axTwoTargets : Statements := [block' "L2" [block' "L1" [
    ite' (c0 "c") [set' "x" (int 1), ite' (c0 "d") [exit' "L1"] [exit' "L2"]] [],
    assert' "in" (eq' (iv "x") (int 0))], assert' "mid" (ge (iv "x") (int 0))],
  assert' "out" (ge (iv "x") (int 0))]
#guard good ["c", "d", "x"] axTwoTargets
#guard show' (tr ["c", "d", "x"] axTwoTargets) == lines [
    "{",
    "  var g@4 : bool := int.gt(c@0, 0);",
    "  var x@5 : int := if g@4 then 1 else x@2;",
    "  var g@6 : bool := if g@4 then int.gt(d@1, 0) else false;",
    "  var r@12 : bool := if g@4 then false else true;",
    "  if * {",
    "    assume [wp$reach]: r@12;",
    "    assert [in]: x@2 == 0;",
    "  }",
    "  else {",
    "    var x@13 : int := if g@4 then x@5 else x@2;",
    "    var r@14 : bool := if r@12 then true else g@6;",
    "    if * {",
    "      assume [wp$reach]: r@14;",
    "      assert [mid]: int.ge(x@13, 0);",
    "    }",
    "    else {",
    "      assert [out]: int.ge(x@13, 0);",
    "    }",
    "  }",
    "}"]

def axNested : Statements := [block' "A" [block' "B" [
    ite' (c0 "c") [set' "x" (int 1), ite' (c0 "d") [set' "x" (int 2), exit' "B"] [],
      exit' "A"] [],
    assert' "inB" (eq' (iv "x") (int 0))], assert' "afterB" (le' (iv "x") (int 2))],
  assert' "afterA" (ge (iv "x") (int 0))]
#guard good ["c", "d", "x"] axNested
#guard show' (tr ["c", "d", "x"] axNested) == lines [
    "{",
    "  var g@5 : bool := int.gt(c@0, 0);",
    "  var x@6 : int := if g@5 then 1 else x@2;",
    "  var g@7 : bool := if g@5 then int.gt(d@1, 0) else false;",
    "  var x@9 : int := if g@7 then 2 else x@6;",
    "  var r@13 : bool := if g@5 then false else true;",
    "  if * {",
    "    assume [wp$reach]: r@13;",
    "    assert [inB]: x@2 == 0;",
    "  }",
    "  else {",
    "    var x@14 : int := if g@5 then x@6 else x@2;",
    "    var x@15 : int := if g@7 then x@9 else x@14;",
    "    var r@16 : bool := if r@13 then true else g@7;",
    "    if * {",
    "      assume [wp$reach]: r@16;",
    "      assert [afterB]: int.le(x@15, 2);",
    "    }",
    "    else {",
    "      assert [afterA]: int.ge(x@15, 0);",
    "    }",
    "  }",
    "}"]

/-! ## Exits and folding

The rest of a list after a statement that always exits is discarded by the WP walk; code that a
later reach makes unreachable is guarded by a reach the SSA phase folds to `false`. -/

/-- Does the label occur as an obligation of `ss`? -/
def hasObl (ss : Statements) (l : String) : Bool :=
  (oblLabels ss).contains l

def deadAfterExit : Statements := [block' "L" [set' "x" (int 1), exit' "L", set' "x" (int 2),
    assert' "p" (eq' (iv "x") (int 2))],
  assert' "q" (eq' (iv "x") (int 1))]
#guard !hasObl (trOut ["x"] deadAfterExit) "p"
#guard show' (tr ["x"] deadAfterExit) == lines [
    "{",
    "  var x@3 : int := 1;",
    "  assert [q]: x@3 == 1;",
    "}"]

def exitThenSet : Statements := [block' "L" [ite' (c0 "c") [exit' "L"] [], set' "x" (int 2)],
  assert' "a" (gt (iv "x") (int 0))]
#guard nInits (trOut ["c", "x"] exitThenSet) == 3
#guard show' (tr ["c", "x"] exitThenSet) == lines [
    "{",
    "  var g@5 : bool := int.gt(c@0, 0);",
    "  var r@7 : bool := if g@5 then false else true;",
    "  var x@8 : int := if r@7 then 2 else x@1;",
    "  assert [a]: int.gt(x@8, 0);",
    "}"]

def andNegDead : Statements := [block' "L" [ite' (c0 "c1") [exit' "L"] [],
    ite' (c0 "c2") [set' "y" (int 1)] [exit' "L", assert' "p" (gt (iv "y") (int 5))]],
  assert' "q" (gt (iv "y") (int 0))]
#guard !hasObl (trOut ["c1", "c2", "y"] andNegDead) "p"
#guard show' (tr ["c1", "c2", "y"] andNegDead) == lines [
    "{",
    "  var g@5 : bool := int.gt(c1@0, 0);",
    "  var r@8 : bool := if g@5 then false else true;",
    "  var g@9 : bool := if r@8 then int.gt(c2@1, 0) else false;",
    "  var y@10 : int := if g@9 then 1 else y@2;",
    "  assert [q]: int.gt(y@10, 0);",
    "}"]

def exitOuter : Statements := [block' "O" [block' "I" [ite' (c0 "c") [exit' "O"] []],
    set' "x" (int 1)],
  assert' "a" (gt (iv "x") (int 0))]
#guard good ["c", "x"] exitOuter
#guard show' (tr ["c", "x"] exitOuter) == lines [
    "{",
    "  var g@5 : bool := int.gt(c@0, 0);",
    "  var r@7 : bool := if g@5 then false else true;",
    "  var x@8 : int := if r@7 then 1 else x@1;",
    "  assert [a]: int.gt(x@8, 0);",
    "}"]

def bothExit : Statements := [block' "L" [
    ite' (c0 "c") [set' "x" (int 1), exit' "L"] [set' "x" (int 2), exit' "L"],
    assert' "p" (gt (iv "x") (int 5))],
  assert' "a" (gt (iv "x") (int 0))]
#guard !hasObl (trOut ["c", "x"] bothExit) "p"
#guard show' (tr ["c", "x"] bothExit) == lines [
    "{",
    "  var g@6 : bool := int.gt(c@0, 0);",
    "  var x@9 : int := if g@6 then 1 else x@1;",
    "  var x@12 : int := if g@6 then x@1 else 2;",
    "  var x@16 : int := if if g@6 then false else true then x@12 else x@1;",
    "  var x@17 : int := if g@6 then x@9 else x@16;",
    "  assert [a]: int.gt(x@17, 0);",
    "}"]

-- An `exit` that targets no enclosing block: `checkLoopFree` rejects the list, and the WP phase
-- alone assumes away the paths that take it.
def topExitArm : Statements := [ite' (c0 "c") [exit' "Z"] [], assert' "a" (gt (iv "x") (int 0))]
#guard err ["c", "x"] topExitArm == uncoveredExit
#guard show' (trW ["c", "x"] topExitArm) == lines [
    "{",
    "  var g@2 : bool := int.gt(c@0, 0);",
    "  assume [wp$join]: if g@2 then false else true;",
    "  assert [a]: int.gt(x@1, 0);",
    "}"]

-- An `exit` that targets no enclosing block: `checkLoopFree` rejects the list, and the WP phase
-- alone assumes away the paths that take it.
def topExit : Statements := [assert' "a" (gt (iv "x") (int 0)), exit' "Z",
  assert' "b" (gt (iv "x") (int 1))]
#guard err ["x"] topExit == uncoveredExit
#guard show' (trW ["x"] topExit) == lines [
    "{",
    "  assert [a]: int.gt(x@0, 0);",
    "}"]

-- An `exit` that targets no enclosing block: `checkLoopFree` rejects the list, and the WP phase
-- alone assumes away the paths that take it.
def realBranchExits : Statements := [ite' (c0 "c")
    [block' "L" [ite' (c0 "d") [exit' "L"] [], assert' "t1" (gt (iv "x") (int 0))],
      assert' "t2" (gt (iv "x") (int 1))]
    [ite' (c0 "d") [exit' "Out"] [], assert' "e1" (gt (iv "x") (int 2))]]
#guard err ["c", "d", "x"] realBranchExits == uncoveredExit
#guard show' (trW ["c", "d", "x"] realBranchExits) == lines [
    "{",
    "  var g@4 : bool := int.gt(c@0, 0);",
    "  if * {",
    "    assume [wp$reach]: g@4;",
    "    var g@7 : bool := int.gt(d@1, 0);",
    "    var r@9 : bool := if g@7 then false else true;",
    "    if * {",
    "      assume [wp$reach]: r@9;",
    "      assert [t1]: int.gt(x@2, 0);",
    "    }",
    "    else {",
    "      assert [t2]: int.gt(x@2, 1);",
    "    }",
    "  }",
    "  else {",
    "    assume [wp$reach]: if g@4 then false else true;",
    "    var g@10 : bool := int.gt(d@1, 0);",
    "    assume [wp$join]: if g@10 then false else true;",
    "    assert [e1]: int.gt(x@2, 2);",
    "  }",
    "}"]

def shadowLabel : Statements := [block' "L" [block' "L" [exit' "L"],
  assert' "p" (gt (iv "x") (int 0))]]
#guard hasObl (trOut ["x"] shadowLabel) "p"
#guard show' (tr ["x"] shadowLabel) == lines [
    "{",
    "  assert [p]: int.gt(x@0, 0);",
    "}"]

/-! ## Renaming

Earlier declarations of a name declared again later get WP names, so every name of the guarded
program has one `init`; the record maps them back to the loop-free names. -/

def redeclared : Statements := [ite' (c0 "c") [init' "z" (int 1), assert' "t" (gt (iv "z") (int 0))]
    [init' "z" (int 2), assume' "e" (gt (iv "z") (int 1))],
  init' "z" (int 3), assert' "a" (gt (iv "z") (int 2))]
#guard good ["c"] redeclared
#guard (stmtsInits (guardedOut ["c"] redeclared)).Nodup
#guard show' (tr ["c"] redeclared) == lines [
    "{",
    "  var g@1 : bool := int.gt(c@0, 0);",
    "  var z@6 : int;",
    "  var z@7 : int := if g@1 then 1 else z@6;",
    "  if * {",
    "    assume [wp$reach]: g@1;",
    "    assert [t]: int.gt(z@7, 0);",
    "  }",
    "  else {",
    "    var z@8 : int;",
    "    var z@9 : int := if g@1 then z@8 else 2;",
    "    assume [e]: if g@1 then true else int.gt(z@9, 1);",
    "    var z@10 : int := 3;",
    "    assert [a]: int.gt(z@10, 2);",
    "  }",
    "}"]

def blockRedeclared : Statements := [block' "L" [init' "z" (iv "x"),
    assert' "t" (gt (iv "z") (int 0))],
  init' "z" (int 1), assert' "a" (gt (iv "z") (int 0))]
#guard good ["x"] blockRedeclared
#guard show' (tr ["x"] blockRedeclared) == lines [
    "{",
    "  if * {",
    "    assert [t]: int.gt(x@0, 0);",
    "  }",
    "  else {",
    "    var z@4 : int := 1;",
    "    assert [a]: int.gt(z@4, 0);",
    "  }",
    "}"]

-- The SSA phase's substitution maps the name of the guarded program, and `substObl sub e` is the
-- emitted condition.
#guard match wpSSALoopFree (IdSet.ofList []) (IdSet.ofList []) (proc ["c"] redeclared) redeclared with
  | .ok (w, _, so) => oblSubsMatch w.lay so.out so.obls
  | .error _ => false

-- No renaming when a name is declared once.
#guard (Block.idents (guardedOut ["x"] ex9)).contains (id' "z")

/-! ## Types -/

def saveLocal : Statements := [init' "z" (iv "x"),
  ite' (c0 "c") [set' "z" (int 1)] [assert' "e" (gt (iv "z") (int 0))],
  assert' "a" (gt (iv "z") (int 0))]
#guard good ["c", "x"] saveLocal
#guard show' (tr ["c", "x"] saveLocal) == lines [
    "{",
    "  var g@2 : bool := int.gt(c@0, 0);",
    "  var z@4 : int := if g@2 then 1 else x@1;",
    "  if * {",
    "    assume [wp$reach]: if g@2 then false else true;",
    "    assert [e]: int.gt(x@1, 0);",
    "  }",
    "  else {",
    "    assert [a]: int.gt(z@4, 0);",
    "  }",
    "}"]

def oldRead : Statements := [set' "x" (add (iv "x") (int 1)),
  assert' "a" (gt (iv "x") (.fvar () (CoreIdent.mkOld "x") (some .int)))]
#guard show' (do
    let (_, _, so) ← wpSSALoopFree (IdSet.ofList []) (IdSet.ofList []) inoutProc oldRead
    pure (deadDefElim [] so.out)) == lines [
    "{",
    "  var x@1 : int := int.add(x@0, 1);",
    "  assert [a]: int.gt(x@1, x@0);",
    "}"]

/-! ## SSA folding

The SSA phase on hand-written guarded programs: conditions with literal parts fold, true
assumptions are dropped, an arm assuming `false` is kept (its obligations are reported, as
symbolic evaluation reports those of a branch whose condition is `false`), an empty arm is
dropped with the other inline, an assignment of a literal defines a name for it, which
obligations read, and a copy from a name not annotated with the copy's declared type is
defined by a fresh `init`. -/

/-- The SSA phase on a guarded program, without free-variable types and entry renaming. -/
def ssa (lay : Statements) : Except String Statements := do
  let (_, so) ← ssaEntry (P := Expression) (IdSet.ofList []) [] [] [] lay
  pure so.out

def bv (n : String) : Expression.Expr := .fvar () (id' n) (some .bool)
def initB (x : String) (e : Expression.Expr) : Statement :=
  .cmd (.cmd (.init (id' x) (.forAll [] .bool) (.det e) md))
def tt' : Expression.Expr := .boolConst () true
def ff' : Expression.Expr := .boolConst () false

#guard show' (ssa [init' "y" (.ite () tt' (iv "a") (iv "b")), assert' "p" (gt (iv "y") (int 0))])
  == lines [
    "{",
    "  assert [p]: int.gt(a, 0);",
    "}"]
#guard show' (ssa [assume' "t" tt', assert' "p" (gt (iv "a") (int 0))]) == lines [
    "{",
    "  assert [p]: int.gt(a, 0);",
    "}"]
#guard show' (ssa [assume' "i" (.ite () ff' (gt (iv "a") (int 0)) tt'),
  assert' "p" (gt (iv "a") (int 0))]) == lines [
    "{",
    "  assert [p]: int.gt(a, 0);",
    "}"]
#guard show' (ssa [.ite .nondet [assume' "r" ff', assert' "p" (gt (iv "a") (int 0))]
  [assert' "q" (gt (iv "a") (int 1))] md]) == lines [
    "{",
    "  if * {",
    "    assume [r]: false;",
    "    assert [p]: int.gt(a, 0);",
    "  }",
    "  else {",
    "    assert [q]: int.gt(a, 1);",
    "  }",
    "}"]
#guard show' (ssa [.ite .nondet [] [assert' "q" (gt (iv "a") (int 1))] md]) == lines [
    "{",
    "  assert [q]: int.gt(a, 1);",
    "}"]
#guard show' (ssa [initB "b" tt', initB "c" (bv "b"), assert' "p" (eq' (bv "c") tt')]) == lines [
    "{",
    "  var b@0 : bool := true;",
    "  var c@1 : bool := true;",
    "  assert [p]: c@1 == true;",
    "}"]
#guard show' (ssa [initB "g" (.ite () (bv "q") ff' ff'), assume' "r" (bv "g"),
  assert' "p" (gt (iv "a") (int 0))]) == lines [
    "{",
    "  var g@0 : bool := false;",
    "  assume [r]: false;",
    "  assert [p]: int.gt(a, 0);",
    "}"]
#guard show' (ssa [ite' tt' [] []]) == "ERROR SSA: deterministic `ite` (the input is not in tree form)"
#guard show' (ssa [block' "L" []]) == "ERROR SSA: `block` (the input is not in tree form)"
#guard show' (ssa [.ite .nondet [] [] md, assert' "p" tt']) == "ERROR SSA: `ite *` followed by a statement (the input is not in tree form)"
-- A copy from a name annotated with the declared type of the copy is recorded: later reads of
-- the copy read the name.
#guard show' (ssa [init' "y" (iv "a"), assert' "p" (gt (iv "y") (int 0))]) == lines [
    "{",
    "  assert [p]: int.gt(a, 0);",
    "}"]
-- A copy from a name without an annotation, or annotated with another type than the declared
-- type of the copy, is not propagated: a fresh `init` defines the copy.
#guard show' (ssa [init' "y" (.fvar () (id' "a") none), assert' "p" (gt (iv "y") (int 0))]) ==
  lines [
    "{",
    "  var y@0 : int := a;",
    "  assert [p]: int.gt(y@0, 0);",
    "}"]
#guard show' (ssa [init' "y" (bv "c"), assert' "p" (gt (iv "y") (int 0))]) == lines [
    "{",
    "  var y@0 : int := c;",
    "  assert [p]: int.gt(y@0, 0);",
    "}"]

/-! ## The records of the two phases -/

/-- Does the SSA phase on the guarded program of `ss` record one entry per obligation of the
    guarded program, in order, each one the emitted obligation under its substitution? -/
def recordOK (params : List String) (ss : Statements) : Bool :=
  match wpSSALoopFree (IdSet.ofList []) (IdSet.ofList []) (proc params ss) ss with
  | .ok (w, _, so) =>
    (oblSubs so.obls).map (·.1) == oblLabels w.lay && oblSubsMatch w.lay so.out so.obls
  | .error _ => false

#guard [(["x"], ex1), (["x", "y"], ex2), (["x", "y"], ex3), (["x", "y"], ex4),
  (["x", "y"], ex5), (["x", "y"], ex6), (["x"], ex7), (["g", "x", "y"], ex8),
  (["g", "x", "y"], ex8b), (["x"], ex9), (["x"], ex10), (["x", "y"], ex11),
  (["c", "x"], ex13), (["c", "d", "x"], ex14), (["a", "b", "c"], elseReadsTemp),
  (["c", "x"], axBlock), (["c1", "c2", "x"], axTwoDepths), (["c", "d", "x"], axNested),
  (["c1", "c2", "y"], andNegDead), (["c"], redeclared)].all fun (ps, e) => recordOK ps e

-- No record for dropped code: the WP skeleton has no havoc or guard after an `exit`, and the SSA
-- phase records only the obligation `q`.
def droppedRecord : Statements := [block' "L" [exit' "L", havocInit "h",
    ite' (c0 "c") [assert' "p" (gt (iv "h") (int 0))] []],
  assert' "q" (gt (iv "c") (int 0))]
#guard match wpSSALoopFree (IdSet.ofList []) (IdSet.ofList []) (proc ["c"] droppedRecord)
    droppedRecord with
  | .ok (w, _, so) => skNames w.sk == [] && (oblSubs so.obls).map (·.1) == ["q"]
  | .error _ => false

-- A guard that folds to a literal is recorded by the SSA phase with its literal value.
def litGuard : Statements := [ite' tt' [assert' "t" (gt (iv "x") (int 0))]
  [assert' "e" (gt (iv "x") (int 1))], assert' "a" (gt (iv "x") (int 2))]
#guard match wpSSALoopFree (IdSet.ofList []) (IdSet.ofList []) (proc ["x"] litGuard) litGuard with
  | .ok (_, _, so) => so.defs.any fun (_, v) => match v with | .lit true _ => true | _ => false
  | .error _ => false

/-! ## Tree form -/

#guard [(["x"], ex1), (["x", "y"], ex2), (["x", "y"], ex3), (["x", "y"], ex4),
  (["x", "y"], ex5), (["x", "y"], ex11), (["c", "d", "x"], ex14),
  (["c", "x"], axBlock), (["c1", "c2", "y"], andNegDead)].all fun (ps, e) =>
    Statements.treeForm (guardedOut ps e) && Block.treeForm (guardedOut ps e)
#guard !Statements.treeForm [.ite .nondet [] [] md, assert' "p" tt']

/-! ## Linear implementations against their specifications

Each function the executable code uses, or its specification, is compared here with a copy of
the specification's body. -/

def specExprFV (e : Expression.Expr) : List CoreIdent := (HasFvars.getFvars e).eraseDups

mutual
def specStmtsIdents : Statements → List CoreIdent
  | [] => []
  | s :: rest => specStmtIdents s ++ specStmtsIdents rest
def specStmtIdents : Statement → List CoreIdent
  | .cmd (.cmd (.init x _ (.det e) _)) | .cmd (.cmd (.set x (.det e) _)) =>
    x :: HasFvars.getFvars e
  | .cmd (.cmd (.init x _ .nondet _)) | .cmd (.cmd (.set x .nondet _)) => [x]
  | .cmd (.cmd (.assume _ e _)) | .cmd (.cmd (.assert _ e _)) | .cmd (.cmd (.cover _ e _)) =>
    HasFvars.getFvars e
  | .cmd (.call _ args _) =>
    (CallArg.getInArgs args).flatMap HasFvars.getFvars ++ CallArg.getLhs args
  | .block _ ss _ => specStmtsIdents ss
  | .ite c tss ess _ =>
    (match c with | .det c => HasFvars.getFvars c | .nondet => []) ++ specStmtsIdents tss ++
      specStmtsIdents ess
  | .loop g m inv body _ =>
    (match g with | .det g => HasFvars.getFvars g | .nondet => []) ++
      (m.map HasFvars.getFvars).getD [] ++ inv.flatMap (HasFvars.getFvars ·.2) ++
      specStmtsIdents body
  | .exit _ _ | .typeDecl _ _ => []
end

mutual
def specStmtsFV : Statements → List CoreIdent
  | [] => []
  | s :: rest =>
    match s with
    | .cmd (.cmd (.init x _ e _)) =>
      (match e with | .det e => specExprFV e | .nondet => []) ++
        (specStmtsFV rest).filter (· != x)
    | _ => specStmtFV s ++ specStmtsFV rest
def specStmtFV : Statement → List CoreIdent
  | .cmd (.cmd (.init _ _ (.det e) _)) => specExprFV e
  | .cmd (.cmd (.init _ _ .nondet _)) => []
  | .cmd (.cmd (.set x (.det e) _)) => x :: specExprFV e
  | .cmd (.cmd (.set x .nondet _)) => [x]
  | .cmd (.cmd (.assume _ e _)) | .cmd (.cmd (.assert _ e _)) | .cmd (.cmd (.cover _ e _)) =>
    specExprFV e
  | .cmd (.call _ _ _) => []
  | .block _ ss _ => specStmtsFV ss
  | .ite c tss ess _ =>
    (match c with | .det c => specExprFV c | .nondet => []) ++ specStmtsFV tss ++ specStmtsFV ess
  | .loop _ _ _ body _ => specStmtsFV body
  | .exit _ _ | .typeDecl _ _ => []
end

mutual
def specStmtsAssigned : Statements → List CoreIdent
  | [] => []
  | s :: rest => specStmtAssigned s ++ specStmtsAssigned rest
def specStmtAssigned : Statement → List CoreIdent
  | .cmd (.cmd (.init x _ _ _)) | .cmd (.cmd (.set x _ _)) => [x]
  | .block _ ss _ => specStmtsAssigned ss
  | .ite _ tss ess _ => specStmtsAssigned tss ++ specStmtsAssigned ess
  | .loop _ _ _ body _ => specStmtsAssigned body
  | _ => []
end

mutual
def specWflB (Lc : List CoreIdent) : List CoreIdent → Statements → Bool
  | _, [] => true
  | S, s :: rest => specWfs1B Lc S s && specWflB Lc (Stmt.topInits s ++ S) rest
def specWfs1B (Lc : List CoreIdent) (S : List CoreIdent) : Statement → Bool
  | .cmd (.cmd (.init x _ (.det e) _)) =>
    !S.contains x && Lc.contains x && (specExprFV e).all S.contains
  | .cmd (.cmd (.init x _ .nondet _)) => !S.contains x && Lc.contains x
  | .cmd (.cmd (.set x (.det e) _)) => S.contains x && (specExprFV e).all S.contains
  | .cmd (.cmd (.set x .nondet _)) => S.contains x
  | .cmd (.cmd (.assume _ e _)) | .cmd (.cmd (.assert _ e _)) | .cmd (.cmd (.cover _ e _)) =>
    (specExprFV e).all S.contains
  | .ite (.det c) tss ess _ =>
    (specExprFV c).all S.contains && specWflB Lc S tss && specWflB Lc S ess
  | .block _ ss _ => specWflB Lc S ss
  | .exit _ _ | .typeDecl _ _ => true
  | _ => false
end

mutual
def specDDE (live : List CoreIdent) : Statements → Statements
  | [] => []
  | s :: rest =>
    let rest' := specDDE live rest
    if erasable (specStmtsIdents rest' ++ live) s then rest'
    else specDDES (specStmtsIdents rest' ++ live) s :: rest'
def specDDES (live : List CoreIdent) : Statement → Statement
  | .ite c tss ess md =>
    let ess' := specDDE live ess
    .ite c (specDDE (specStmtsIdents ess' ++ live) tss) ess' md
  | .block l ss md => .block l (specDDE live ss) md
  | s => s
end

def specAxiomScopes (p : Program) : List (String × List Decl) :=
  (p.decls.foldl (init := (([] : List Decl), ([] : List (String × List Decl))))
    fun (axs, acc) d => match d with
      | .ax _ _ => (axs ++ [d], acc)
      | .proc q _ => (axs, acc ++ [(q.header.name.name, axs)])
      | .lemma l _ => (axs, acc ++ [(l.name, axs)])
      | _ => (axs, acc)).2

/-- The corpus of the differential tests: the loop-free lists above and their guarded and
    obligation programs. -/
def corpus : List (List String × Statements) := [(["x"], ex1), (["x", "y"], ex2),
  (["x", "y"], ex3), (["x", "y"], ex4), (["x", "y"], ex5), (["x", "y"], ex6), (["x"], ex7),
  (["g", "x", "y"], ex8), (["g", "x", "y"], ex8b), (["x"], ex9), (["x"], ex10),
  (["x", "y"], ex11), (["c", "x"], ex13), (["c", "d", "x"], ex14),
  (["a", "b", "c"], elseReadsTemp), (["c", "x"], axBlock), (["c1", "c2", "x"], axTwoDepths),
  (["c", "d", "x"], axNested), (["c1", "c2", "y"], andNegDead), (["c"], redeclared),
  (["x"], blockRedeclared), (["c", "x"], saveLocal)]

def corpusLists : List Statements :=
  corpus.flatMap fun (ps, e) => [e, guardedOut ps e, trOut ps e]

#guard corpusLists.all fun ss => Block.idents ss == specStmtsIdents ss
#guard corpusLists.all fun ss => Block.freeVars ss == specStmtsFV ss
#guard corpusLists.all fun ss => Block.assignedVars ss == specStmtsAssigned ss
#guard corpusLists.all fun ss => (stmtsExprs ss).all fun e => exprFV e == specExprFV e
#guard corpusLists.all fun ss => deadDefElim [] ss == specDDE [] ss
#guard corpus.all fun (ps, e) =>
  let S := (proc ps e).paramTys.map (·.1)
  Block.wellScopedB (Block.assignedVars e) S e == specWflB (Block.assignedVars e) S e
#guard !Block.wellScopedB [] [] [assert' "a" (gt (iv "y") (int 0))] &&
  !specWflB [] [] [assert' "a" (gt (iv "y") (int 0))]
#guard [twoProcs, procAxProc, globalProg].all fun p =>
  match wpProgramWith [] { decls := [] } [] p with
  | .ok q => axiomScopesAgree p q == (specAxiomScopes q == specAxiomScopes p) &&
      axiomScopesAgree p q && !axiomScopesAgree p { decls := q.decls.reverse } ==
        !(specAxiomScopes { decls := q.decls.reverse } == specAxiomScopes p)
  | .error _ => false
-- `LExpr.substFvarsBy` against `substFvars`, on the expressions of the corpus with a renaming of
-- their free variables.
#guard corpusLists.all fun ss => (stmtsExprs ss).all fun e =>
  let sm : Map CoreIdent Expression.Expr := (exprFV e).map fun x => (x, iv (x.name ++ "'"))
  LExpr.substFvarsBy e (fun x => sm.find? x) == LExpr.substFvars e sm

end WPProgramTest

end -- meta section
