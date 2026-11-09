/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.Factory
import StrataTest.Languages.Core.Tests.ReparseTestUtils

/-! # Printer coverage for the `Set` and `Sequence` operators

The programs below are built as ASTs. Each one with annotated empty
collections prints without a conversion error, and the printed text parses back
to a program that prints the same way. The sequence program covers the
operators the grammar groups under one wrapper. An empty collection without a
matching type annotation prints with a placeholder element type and a
conversion error.
-/

open Lambda Core Strata Strata.CoreDDM
open Strata.Test.CoreReparse (reprintsSame)

namespace Strata.Test.CollectionPrinter

private def intLit (i : Int) : Expression.Expr := .const () (.intConst i)

private def opApp (name : String) (args : List Expression.Expr) :
    Expression.Expr :=
  LExpr.mkApp () (.op () ⟨name, ()⟩ none) args

private def emptyIntSet : Expression.Expr :=
  .op () ⟨"Set.empty", ()⟩ (some (setTy .int))

/-- A program with one procedure `P`, without parameters, whose body is
    `body`. -/
private def procProg (body : List Statement) : Core.Program :=
  { decls := [.proc {
      header := { name := ⟨"P", ()⟩, typeArgs := [], inputs := [],
                  outputs := [] }
      spec := { preconditions := [], postconditions := [] }
      body := .structured body } #[]] }

/-- Declares an uninitialized variable of type `Set int`. -/
private def setVarProg : Core.Program :=
  procProg [Statement.init "x" (.forAll [] (setTy .int)) .nondet .empty]

/-- Declares the variable `name` of type `ty`, initialized to `e`. -/
private def initVar (name : String) (ty : LMonoTy) (e : Expression.Expr) :
    Statement :=
  Statement.init name (.forAll [] ty) (.det e) .empty

/-- Declares one variable initialized with each `Set.*` operator, plus empty
    sets of `bool` and of `Sequence int` elements. -/
private def setOpsProg : Core.Program :=
  let s := emptyIntSet
  let emptySet (ety : LMonoTy) : Expression.Expr :=
    .op () ⟨"Set.empty", ()⟩ (some (setTy ety))
  procProg [
    initVar "eb" (setTy .bool) (emptySet .bool),
    initVar "eq" (setTy (seqTy .int)) (emptySet (seqTy .int)),
    initVar "b" .bool (opApp "Set.contains" [s, intLit 1]),
    initVar "e" (setTy .int) s,
    initVar "i" (setTy .int) (opApp "Set.insert" [s, intLit 1]),
    initVar "r" (setTy .int) (opApp "Set.remove" [s, intLit 1]),
    initVar "u" (setTy .int) (opApp "Set.union" [s, s]),
    initVar "n" (setTy .int) (opApp "Set.intersect" [s, s]),
    initVar "d" (setTy .int) (opApp "Set.difference" [s, s])]

/-- Declares variables initialized with empty collections whose annotation
    is missing or names the other collection, to check that the printer
    reports each missing element type. -/
private def missingElemTyEmptyProg : Core.Program :=
  procProg [
    initVar "x" (setTy .int) (.op () ⟨"Set.empty", ()⟩ none),
    initVar "y" (seqTy .int) (.op () ⟨"Sequence.empty", ()⟩ none),
    initVar "z" (setTy .int) (.op () ⟨"Set.empty", ()⟩ (some (seqTy .int)))]

/-- Declares one variable initialized with each grouped `Sequence.*`
    operator. -/
private def seqOpsProg : Core.Program :=
  let q : Expression.Expr := .op () ⟨"Sequence.empty", ()⟩ (some (seqTy .int))
  let one := intLit 1
  procProg [
    initVar "a" .int (opApp "Sequence.select" [q, one]),
    initVar "b" .int (opApp "Sequence.select!" [q, one]),
    initVar "c" (seqTy .int) (opApp "Sequence.take" [q, one]),
    initVar "d" (seqTy .int) (opApp "Sequence.take!" [q, one]),
    initVar "e" (seqTy .int) (opApp "Sequence.drop" [q, one]),
    initVar "f" (seqTy .int) (opApp "Sequence.drop!" [q, one]),
    initVar "g" (seqTy .int) (opApp "Sequence.update" [q, one, one]),
    initVar "h" (seqTy .int) (opApp "Sequence.update!" [q, one, one])]

/-- The printed program followed by its AST-to-CST conversion errors, one per
    line, or `[]` when there are none. -/
private def printWithErrors (p : Core.Program) : String :=
  let errs := (programToCST (M := StrataDDM.SourceRange) p).1.errors.toList.map
    fun | .unsupportedConstruct fn desc _ _ => s!"\n  {fn}: {desc}"
  let text := CoreReparse.withoutErrorBlock (Core.formatProgram p).pretty
  s!"{text}\nerrors:{if errs.isEmpty then " []" else String.join errs}"

/-- info: program Core;

procedure P ()
{
  var x : (Set int);
};

errors: []
-/
#guard_msgs in
#eval IO.println (printWithErrors setVarProg)

/-- info: program Core;

procedure P ()
{
  var eb : Set bool := Set.empty<bool>();
  var eq : Set (Sequence int) := Set.empty<Sequence int>();
  var b : bool := Set.contains(Set.empty<int>(), 1);
  var e : Set int := Set.empty<int>();
  var i : Set int := Set.insert(Set.empty<int>(), 1);
  var r : Set int := Set.remove(Set.empty<int>(), 1);
  var u : Set int := Set.union(Set.empty<int>(), Set.empty<int>());
  var n : Set int := Set.intersect(Set.empty<int>(), Set.empty<int>());
  var d : Set int := Set.difference(Set.empty<int>(), Set.empty<int>());
};

errors: []
-/
#guard_msgs in
#eval IO.println (printWithErrors setOpsProg)

/-- info: program Core;

procedure P ()
{
  var a : int := Sequence.select(Sequence.empty<int>(), 1);
  var b : int := Sequence.select!(Sequence.empty<int>(), 1);
  var c : Sequence int := Sequence.take(Sequence.empty<int>(), 1);
  var d : Sequence int := Sequence.take!(Sequence.empty<int>(), 1);
  var e : Sequence int := Sequence.drop(Sequence.empty<int>(), 1);
  var f : Sequence int := Sequence.drop!(Sequence.empty<int>(), 1);
  var g : Sequence int := Sequence.update(Sequence.empty<int>(), 1, 1);
  var h : Sequence int := Sequence.update!(Sequence.empty<int>(), 1, 1);
};

errors: []
-/
#guard_msgs in
#eval IO.println (printWithErrors seqOpsProg)

/-- info: program Core;

procedure P ()
{
  var x : Set int := Set.empty<$__unknown_type>();
  var y : Sequence int := Sequence.empty<$__unknown_type>();
  var z : Set int := Set.empty<$__unknown_type>();
};

errors:
  lexprToExpr: empty collection without element type: Set.empty
  lexprToExpr: empty collection without element type: Sequence.empty
  lexprToExpr: empty collection without element type: Set.empty
-/
#guard_msgs in
#eval IO.println (printWithErrors missingElemTyEmptyProg)

/-- info: set variable round-trips: true
set operators round-trip: true
sequence operators round-trip: true
-/
#guard_msgs in
#eval do
  IO.println s!"set variable round-trips: {← reprintsSame setVarProg}"
  IO.println s!"set operators round-trip: {← reprintsSame setOpsProg}"
  IO.println s!"sequence operators round-trip: {← reprintsSame seqOpsProg}"

end Strata.Test.CollectionPrinter
