/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Transform.DeadDefElim
meta import Strata.Languages.Core.Factory
meta import Strata.Languages.Core

/-! # Dead-definition elimination on examples

`deadDefElimH` on hand-written statement lists: unread `init`s are erased whatever their
right-hand side, to the fixpoint in one pass, at any depth; an `init` read later, in the
enclosing list, in the `else` branch of a later `ite *`, by a call argument or by a loop's
guard, measure or invariant, is kept; the phase selected by name gives the same output and
reports whether it erased an `init`; and the traces of a list and of its erasure correspond
event for event, the erasure's events carrying stores without the erased bindings. -/

meta section

namespace DeadDefElimTest

open Core Core.DeadDefElim Lambda Imperative Imperative.DeadDefElim

def id' (name : String) : CoreIdent := ⟨name, ()⟩
def int (n : Int) : Expression.Expr := .intConst () n
def md : MetaData Expression := #[]
def iv (n : String) : Expression.Expr := .fvar () (id' n) (some .int)
def gt (a b : Expression.Expr) : Expression.Expr := .app () (.app () intGtOp a) b
def add (a b : Expression.Expr) : Expression.Expr := .app () (.app () intAddOp a) b
def div' (a b : Expression.Expr) : Expression.Expr := .app () (.app () intDivOp a) b
def assert' (l : String) (e : Expression.Expr) : Statement := .cmd (.cmd (.assert l e md))
def assume' (l : String) (e : Expression.Expr) : Statement := .cmd (.cmd (.assume l e md))
def block' (l : String) (ss : Statements) : Statement := .block l ss md
def ndIte (t e : Statements) : Statement := .ite .nondet t e md

/-- The lines `ls` joined by newlines. -/
def lines (ls : List String) : String := "\n".intercalate ls

/-- The printed list after the dead-definition phase. -/
def dd (ss : Statements) : String := toString (Std.format (deadDefElimH [] ss))
def bv' (n : String) : Expression.Expr := .fvar () (id' n) (some .bool)
def mv (n : String) : Expression.Expr := .fvar () (id' n) (some (mapTy .int .int))
def initT (x : String) (ty : Lambda.LMonoTy) (e : Expression.Expr) : Statement :=
  .cmd (.cmd (.init (id' x) (.forAll [] ty) (.det e) md))
def havocT (x : String) (ty : Lambda.LMonoTy) : Statement :=
  .cmd (.cmd (.init (id' x) (.forAll [] ty) .nondet md))
def lam : Expression.Expr := .abs () "" (some .int) (.bvar () 0)
def u8 : Expression.Expr := .fvar () (id' "u@1") (some (.bitvec 8))
def opApp (o : Expression.Expr) (a : Expression.Expr) : Expression.Expr := .app () o a
def fOp : Expression.Expr := .op () (id' "f") (some (.arrow .int .int))

-- Unread copies, merges, operator applications, `==` at `int`, and nondeterministic
-- `int`/`bool` inits are erased, to the fixpoint (`a@1` once `a@2` is erased).
def erasedDefs : Statements := [initT "x@3" .int (iv "y@1"),
  initT "y@9" .int (.ite () (bv' "g") (iv "y@7") (iv "y@8")),
  initT "s@1" .int (add (iv "y@1") (int 1)), havocT "z@2" .int, havocT "b@2" .bool,
  initT "a@1" .int (iv "y@1"), initT "a@2" .int (iv "a@1"),
  initT "e@1" .bool (.eq () (iv "y@1") (int 3))]
#guard dd (erasedDefs ++ [assert' "a" (gt (iv "y@1") (int 0))]) == lines [
    "{",
    "  assert [a]: int.gt(y@1, 0);",
    "}"]

-- Erased as well when unread, whatever the right-hand side: `int.div`, a quantifier, a
-- lambda, a beta-redex, `==` at a map type, a bit-vector shift, a program-defined function,
-- an unannotated variable, a nondeterministic map.
def otherDefs : Statements := [initT "d@1" .int (div' (iv "y@1") (int 2)),
  initT "q@1" .bool (.quant () .all "" (some .int) (.bvar () 0)
    (.eq () (.bvar () 0) (.bvar () 0))),
  initT "l@1" (.arrow .int .int) lam, initT "r@1" .int (.app () lam (int 1)),
  initT "e@1" .bool (.eq () (mv "m@1") (mv "m@2")),
  initT "h@1" (.bitvec 8) (.app () (opApp bv8ShlOp u8) u8),
  initT "f@1" .int (opApp fOp (iv "y@1")), initT "c@1" .int (.fvar () (id' "y@1") none),
  havocT "m@3" (mapTy .int .int)]
#guard otherDefs.all fun s =>
  dd [s, assert' "a" (gt (iv "y@1") (int 0))] == lines [
    "{",
    "  assert [a]: int.gt(y@1, 0);",
    "}"]
#guard dd (otherDefs ++ erasedDefs ++ [assert' "a" (gt (iv "y@1") (int 0))]) == lines [
    "{",
    "  assert [a]: int.gt(y@1, 0);",
    "}"]

-- One pass reaches the fixpoint.
#guard let ss := otherDefs ++ erasedDefs ++ [assert' "a" (gt (iv "y@1") (int 0))]
  dd (deadDefElimH [] ss) == dd ss

-- A definition read in a branch is kept.
#guard dd [initT "t@1" .int (iv "y@1"),
    .ite .nondet [assert' "a" (gt (iv "t@1") (int 0))] [assert' "b" (gt (iv "y@1") (int 0))]
      md] == lines [
    "{",
    "  var t@1 : int := y@1;",
    "  if * {",
    "    assert [a]: int.gt(t@1, 0);",
    "  }",
    "  else {",
    "    assert [b]: int.gt(y@1, 0);",
    "  }",
    "}"]

-- A definition read only by a call argument, or only by a loop's guard, measure or
-- invariant, is kept.
#guard dd [initT "x" .int (int 1), .cmd (.call "P" [.inArg (iv "x"), .outArg (id' "r")] md)] ==
  lines ["{", "  var x : int := 1;", "  call P(x, out r);", "}"]
#guard dd [initT "x" .int (int 1), .loop (.det (gt (iv "x") (int 0))) none [] [] md] == lines [
    "{", "  var x : int := 1;", "  while int.gt(x, 0) (none) [] {}", "}"]
#guard dd [initT "x" .int (int 1), .loop .nondet (some (iv "x")) [] [] md] == lines [
    "{", "  var x : int := 1;", "  while * (some x) [] {}", "}"]
#guard dd [initT "x" .int (int 1), .loop .nondet none [("i", gt (iv "x") (int 0))] [] md] ==
  lines ["{", "  var x : int := 1;", "  while * (none) [[i]: int.gt(x, 0)] {}", "}"]

/-! ## Unread definitions, at any depth -/

-- An unread `init x := e` and an unread `init h := *` are erased.
#guard dd [initT "x" .int (add (iv "y") (int 1)), havocT "h" .int,
    assert' "a" (gt (iv "y") (int 0))] == lines [
    "{",
    "  assert [a]: int.gt(y, 0);",
    "}"]

-- A chain of copies with the last unread: all three erased, in one pass.
#guard dd [initT "a" .int (int 1), initT "b" .int (iv "a"), initT "c" .int (iv "b"),
    assert' "p" (gt (iv "y") (int 0))] == lines [
    "{",
    "  assert [p]: int.gt(y, 0);",
    "}"]

-- An unread `init` inside nested `ite *` and `block` bodies is erased; one read after the
-- enclosing statement is kept.
#guard dd [initT "k" .int (int 2), ndIte [block' "L" [initT "u" .int (int 1)]]
    [assert' "e" (gt (iv "y") (int 0))], assert' "a" (gt (iv "k") (int 0))] == lines [
    "{",
    "  var k : int := 2;",
    "  if * {",
    "    L : {}",
    "  }",
    "  else {",
    "    assert [e]: int.gt(y, 0);",
    "  }",
    "  assert [a]: int.gt(k, 0);",
    "}"]

-- An `init` read only in the `else` branch of the next `ite *` is kept.
#guard dd [initT "t" .int (iv "y"),
    ndIte [assert' "a" (gt (iv "y") (int 0))] [assert' "b" (gt (iv "t") (int 0))]] == lines [
    "{",
    "  var t : int := y;",
    "  if * {",
    "    assert [a]: int.gt(y, 0);",
    "  }",
    "  else {",
    "    assert [b]: int.gt(t, 0);",
    "  }",
    "}"]

-- An `init` of a `then` branch read only in the `else` branch is kept (the `then` branch is
-- processed with the identifiers of the processed `else` branch).
#guard dd [.ite (.det (gt (iv "c") (int 0))) [initT "w" .int (int 1)]
    [assert' "b" (gt (iv "w") (int 0))] md] == lines [
    "{",
    "  if int.gt(c, 0) {",
    "    var w : int := 1;",
    "  }",
    "  else {",
    "    assert [b]: int.gt(w, 0);",
    "  }",
    "}"]

/-- Obligation programs with nested nondeterministic branches. -/
def oblProgs : List Statements := [
  erasedDefs ++ [assert' "a" (gt (iv "y@1") (int 0))],
  [initT "t@1" .int (iv "y@1"), initT "s@1" .int (int 2),
    ndIte [initT "u@1" .int (iv "t@1"), assert' "a" (gt (iv "u@1") (int 0))]
      [initT "v@1" .int (int 3), assert' "b" (gt (iv "y@1") (int 0))]],
  [ndIte [ndIte [initT "u@1" .int (int 1), assert' "a" (gt (iv "u@1") (int 0))] []]
    [initT "v@1" .int (iv "y@1"), assert' "b" (gt (iv "v@1") (int 0))]]]

/-! ## The phase selected by name -/

/-- A program with one procedure of body `ss`. -/
def progOf (ss : Statements) : Program :=
  { decls := [.proc {
      header := { name := id' "P", typeArgs := [], inputs := [], outputs := [] },
      spec := { preconditions := [], postconditions := [] },
      body := .structured ss } .empty] }

#guard match Strata.Core.resolvePhases (Strata.Core.nameablePhases Core.VerifyOptions.quiet)
    ["deadDefElim"] with
  | .ok [ph] =>
    let ss := otherDefs ++ erasedDefs ++ [assert' "a" (gt (iv "y@1") (int 0))]
    match ((ph.transform (progOf ss)).run .emp).1 with
    | .ok (true, p) =>
      toString (Std.format p) == toString (Std.format (progOf (deadDefElimH [] ss)))
    | _ => false
  | _ => false

-- The transform reports a change exactly when it erases an `init`.
#guard match ((deadDefElimProgram (progOf (erasedDefs ++
    [assert' "a" (gt (iv "y@1") (int 0))]))).run .emp).1 with
  | .ok (changed, _) => changed
  | .error _ => false
#guard match ((deadDefElimProgram (progOf [initT "t@1" .int (iv "y@1"),
    assert' "a" (gt (iv "t@1") (int 0))])).run .emp).1 with
  | .ok (changed, _) => !changed
  | .error _ => false

/-! ## Trace correspondence

A symbolic run of an obligation program: the store maps each defined name to its defining
expression with the store substituted (a havoc to a placeholder named after it); every
`assume`, `assert` and `cover` emits an event with its kind, label, condition and the store; an
`ite *` runs either branch.  The traces of a list and of its erasure, path by path, have events
of the same kinds, labels and conditions, the erasure's store being the list's without some
bindings and agreeing with it on the condition's free variables. -/

/-- A symbolic store. -/
abbrev SStore := List (CoreIdent × Expression.Expr)

/-- An event of a symbolic run: kind, label, condition, store. -/
abbrev SEvent := String × String × Expression.Expr × SStore

/-- The symbolic traces of a list from a store, one per path. -/
partial def symTraces (σ : SStore) : Statements → List (List SEvent)
  | [] => [[]]
  | .cmd (.cmd (.init x _ (.det e) _)) :: rest =>
    symTraces ((x, LExpr.substFvars e σ) :: σ) rest
  | .cmd (.cmd (.init x _ .nondet _)) :: rest =>
    symTraces ((x, .fvar () (id' ("?" ++ x.name)) none) :: σ) rest
  | .cmd (.cmd (.assume l e _)) :: rest => (symTraces σ rest).map (("assume", l, e, σ) :: ·)
  | .cmd (.cmd (.assert l e _)) :: rest => (symTraces σ rest).map (("assert", l, e, σ) :: ·)
  | .cmd (.cmd (.cover l e _)) :: rest => (symTraces σ rest).map (("cover", l, e, σ) :: ·)
  | .ite .nondet t e _ :: rest =>
    ((symTraces σ t).map fun tr => (symTraces σ rest).map (tr ++ ·)).flatten ++
      ((symTraces σ e).map fun tr => (symTraces σ rest).map (tr ++ ·)).flatten
  | _ :: rest => symTraces σ rest

/-- Two events correspond: same kind, label and condition; the second store is the first
    without some bindings and agrees with it on the condition's free variables. -/
def eventRel (a b : SEvent) : Bool :=
  a.1 == b.1 && a.2.1 == b.2.1 && a.2.2.1 == b.2.2.1 &&
    b.2.2.2.all (fun (x, v) => a.2.2.2.lookup x == some v) &&
    (Imperative.HasFvars.getFvars a.2.2.1).all fun x => a.2.2.2.lookup x == b.2.2.2.lookup x

/-- The traces of `ss` and of its erasure correspond path by path, event for event. -/
def tracesCorrespond (ss : Statements) : Bool :=
  let a := symTraces [] ss
  let b := symTraces [] (deadDefElimH [] ss)
  a.length == b.length && (a.zip b).all fun (ta, tb) =>
    ta.length == tb.length && (ta.zip tb).all fun (ea, eb) => eventRel ea eb

#guard tracesCorrespond (erasedDefs ++ [assert' "a" (gt (iv "y@1") (int 0))])
#guard oblProgs.all tracesCorrespond
-- The erasure's assert event carries the store without the erased binding.
#guard match symTraces [] (deadDefElimH [] [initT "x" .int (int 1),
    assert' "a" (gt (iv "y") (int 0))]) with
  | [[("assert", "a", _, σ)]] => σ.lookup (id' "x") == none
  | _ => false
#guard tracesCorrespond [initT "x" .int (int 1), assert' "a" (gt (iv "y") (int 0))]

end DeadDefElimTest

end -- meta section
