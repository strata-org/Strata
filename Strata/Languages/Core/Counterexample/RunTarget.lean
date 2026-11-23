/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Statement

/-! # Counterexample target identifiers

The obligation a counterexample is lifted for: an assertion of the program (`AssertId`,
firing on a replay event), a loop verification condition (`LoopVCId`), which is not a
statement of the source program but a property of a loop's invariants or measure, a
check at a statement (`PointCheckId`), or a check about a declaration (`DeclCheckId`).  The
validity of a claim for each kind of target is `genuineFeasibleT`
(`Strata.Languages.Core.Counterexample.Run`).

Key definitions: `Target`, `LoopVCId`, `PointCheckId`, `DeclCheckId`. -/

namespace Core

open Imperative

public section

/-- Which verification condition of a loop. -/
inductive LoopVCKind where
  /-- Invariant `i` holds when the loop is reached from outside it. -/
  | entryInvariant (i : Nat)
  /-- Invariant `i` holds when the loop head is reached again after an iteration. -/
  | maintainInvariant (i : Nat)
  /-- The measure is non-negative when an iteration starts. -/
  | measureLowerBound
  /-- The measure decreased across an iteration. -/
  | measureDecrease
  deriving DecidableEq, Repr, Inhabited

/-- A loop verification condition: the loop, identified by its metadata (which every
    pass copies verbatim), and the kind of VC.  The VC's expression is read off the
    matched loop. -/
structure LoopVCId where
  loopMd : MetaData Expression
  kind : LoopVCKind
  deriving DecidableEq

/-- A check that belongs at a statement of the program but is not a statement of it: a
    precondition of a partial function called in the statement's expressions
    (`precondElim`'s call-site checks).  The statement is identified by its metadata, the
    check by its expression (evaluated in the store just before the statement runs). -/
structure PointCheckId where
  stmtMd : MetaData Expression
  expr : Expression.Expr
  deriving DecidableEq

/-- What a check about a declaration (not an execution) checks. -/
inductive DeclCheckKind where
  /-- A partial call in a contract clause of a procedure is well-defined. -/
  | contractWF
  /-- A partial call in a function's preconditions or body is well-defined. -/
  | funcWF
  /-- A recursive call of a function decreases its measure. -/
  | terminates
  /-- The obligation of a lemma declaration holds. -/
  | lemma
  deriving DecidableEq, Repr, Inhabited

/-- A check about a declaration: the declaration's name, the kind of check, the *derived
    unit* — a statement list for the declaration whose runs from the declaration's inputs are
    the counterexamples — and the check's assertion in that unit. -/
structure DeclCheckId where
  decl : String
  kind : DeclCheckKind
  unit : List Statement
  check : AssertId Expression

/-- The target a counterexample is lifted for. -/
inductive Target where
  /-- An assertion (or cover) of the program, firing on a replay event. -/
  | assert (id : AssertId Expression)
  /-- A loop verification condition, firing at a loop head. -/
  | loopVC (id : LoopVCId)
  /-- A check that belongs at a statement, firing just before the statement runs. -/
  | atPoint (id : PointCheckId)
  /-- A check about a declaration, firing on its assertion in the derived unit. -/
  | declCheck (id : DeclCheckId)

/-- The assertion id of a target, if it is one. -/
@[expose] def Target.assertId? : Target → Option (AssertId Expression)
  | .assert a => some a
  | _ => none

/-- Rewrite the assertion id of an assertion target; other targets are unchanged. -/
@[expose] def Target.mapAssert (u : AssertId Expression → AssertId Expression) : Target → Target
  | .assert a => .assert (u a)
  | t => t

/-- A natural-language description of a loop verification condition, for diagnostics. -/
def LoopVCKind.describe : LoopVCKind → String
  | .entryInvariant i => s!"invariant {i} does not hold when the loop is entered"
  | .maintainInvariant i => s!"invariant {i} is not maintained by an iteration of the loop"
  | .measureLowerBound => "the measure is negative at the start of an iteration"
  | .measureDecrease => "the measure does not decrease across an iteration"

/-- A natural-language description of a declaration check, for diagnostics. -/
def DeclCheckKind.describe : DeclCheckKind → String
  | .contractWF => "a contract clause calls a partial function outside its precondition"
  | .funcWF => "the function calls a partial function outside its precondition"
  | .terminates => "a recursive call does not decrease the measure"
  | .lemma => "the lemma's obligation does not hold"

end -- public section

end Core
