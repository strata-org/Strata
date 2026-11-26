/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Core.DDMTransform.ASTtoCST
import StrataTest.Languages.Core.Tests.ReparseTestUtils

/-! # Printing identifiers named like Core keywords

The program below is built as an AST whose variables are named like keywords of
the Core grammar. The printer pipe-quotes each of them, and the printed text
parses back to a program that prints the same way.
-/

open Lambda Core Strata
open Strata.Test.CoreReparse (reprintsSame)

namespace Strata.Test.KeywordIdentPrinter

private abbrev testLoc : ExprSourceLoc := ExprSourceLoc.synthesized "test"

private def var (name : String) : Expression.Expr := .fvar testLoc ⟨name, ()⟩ none

private def intLit (i : Int) : Expression.Expr := .const testLoc (.intConst i)

/-- Declares variables named like keywords, assigns them from one another and
    asserts a fact about them under a label named like a keyword. `x` is an
    ordinary name, printed bare. -/
private def keywordVarsProg : Core.Program :=
  let init (name : String) (e : Expression.Expr) : Statement :=
    Statement.init name (.forAll [] .int) (.det e) .empty
  { decls := [.proc {
      header := { name := ⟨"P", ()⟩, typeArgs := [], inputs := [],
                  outputs := [] }
      spec := { preconditions := [], postconditions := [] }
      body := .structured [
        init "const" (intLit 1),
        init "var" (var "const"),
        init "procedure" (var "var"),
        init "while" (var "procedure"),
        init "old" (var "while"),
        init "x" (var "old"),
        init "assert" (intLit 2),
        Statement.set "assert" (var "x") .empty,
        Statement.assert "in" (.eq testLoc (var "assert") (var "const")) .empty] false } #[]] }

/-- info: program Core;

procedure P ()
{
  var |const| : int := 1;
  var |var| : int := |const|;
  var |procedure| : int := |var|;
  var |while| : int := |procedure|;
  var |old| : int := |while|;
  var x : int := |old|;
  var |assert| : int := 2;
  |assert| := x;
  assert [|in|]: |assert| == |const|;
};
-/
#guard_msgs in
#eval IO.println (Core.formatProgram keywordVarsProg)

/-- The names that the statements of procedure bodies in `p` declare, assign
    or use as assert labels, in order. -/
private def stmtNames (p : Core.Program) : List String :=
  p.decls.flatMap fun
    | .proc proc _ =>
      match proc.body with
      | .structured ss _ => ss.filterMap fun
        | .cmd (.cmd (.init name ..)) => some name.name
        | .cmd (.cmd (.set name ..)) => some name.name
        | .cmd (.cmd (.assert label ..)) => some label
        | _ => none
      | _ => []
    | _ => []

-- The printed program parses back to the same names, without the pipes.
/-- info: [const, var, procedure, while, old, x, assert, assert, in] -/
#guard_msgs in
#eval do
  match ← Strata.Test.CoreReparse.parseAndTranslate
      (Core.formatProgram keywordVarsProg).pretty with
  | .ok ast => IO.println (stmtNames ast)
  | .error e => IO.println s!"error: {e}"

#guard stmtNames keywordVarsProg ==
  ["const", "var", "procedure", "while", "old", "x", "assert", "assert", "in"]

/-- info: keyword-named variables round-trip: true -/
#guard_msgs in
#eval do
  IO.println s!"keyword-named variables round-trip: {← reprintsSame keywordVarsProg}"

/-! The bitvector type former `bv` prints pipe-quoted. The DDM quotes
conservatively: it quotes every name that starts like a token, here `bv{8}(`,
whatever position the name is printed in, so `bv W8` would also parse bare.
The quoted form parses as the built-in bitvector type, not as a user type
named `bv`. -/

/-- The declared type of the alias `Byte` and the input types of `P`. -/
private def bvTypes (p : Core.Program) : List String :=
  p.decls.flatMap fun
    | .type (.syn s) _ => [s!"{repr s.type}"]
    | .proc d _ => d.header.inputs.map fun (_, t) => s!"{repr t}"
    | _ => []

/--
info: printed:
type Byte := |bv| W8;
procedure P (x : |bv| W8, b : Byte)
{
  var y : |bv| W8 := bv8.add(x, b);
};

types: [Lambda.LMonoTy.bitvec 8, Lambda.LMonoTy.bitvec 8, Lambda.LMonoTy.tcons "Byte" []]
reprints same: true
-/
#guard_msgs in
#eval do
  match ← Strata.Test.CoreReparse.parseAndTranslate
      "type Byte := bv W8;\nprocedure P(x : bv W8, b : Byte) { var y : bv W8 := bv8.add(x, b); };\n" with
  | .error e => IO.println s!"error: {e}"
  | .ok p =>
    let printed := (Core.formatProgram p).pretty
    IO.println s!"printed:\n{(printed.drop "program Core;\n\n".length).toString}"
    match ← Strata.Test.CoreReparse.parseAndTranslate printed with
    | .error e => IO.println s!"reparse error: {e}"
    | .ok q =>
      IO.println s!"types: {bvTypes q}"
      IO.println s!"reprints same: {(bvTypes q == bvTypes p) && (← reprintsSame p)}"

/-! Names in the other positions a name can take: declarations of types,
datatypes, constructors, fields, functions and procedures, type parameters,
calls, block and exit labels, quantifier and lambda binders, and names that
hold the pipe or the escape character. Each is spelled like a Core keyword or
holds a character that needs escaping, so each prints quoted, and the printed
text parses back to a program that prints the same way. -/

/-- A program that uses keyword-named or escaped names in every position. -/
private def keywordPositionsSrc : String :=
  "type |var|;
datatype |procedure| { |assert|(|old| : int), |true|() };
function |forall|<|const|>(x : |const|) : |const| { x }
function |old|(x : int) : int { x }
procedure |call|(a : int, out r : int) { r := a; };
procedure P(out r : int) {
  var |a\\|b| : int := 1;
  var |a\\\\b| : int := 2;
  var g : int := |old|(1);
  |while|: { exit |while|; }
  call |call|(1, out r);
  assert [q]: forall |exists| : int :: |exists| == |exists|;
  assert [l]: (fun |old| : int => |old|)(1) == 1;
};
"

/-- The names that the declarations of `p` introduce, in order. -/
private def declNames (p : Core.Program) : List String :=
  p.decls.flatMap fun d => d.names.map (·.name)

/-- info: reprints same: true -/
#guard_msgs in
#eval do
  match ← Strata.Test.CoreReparse.parseAndTranslate keywordPositionsSrc with
  | .error e => IO.println s!"error: {e}"
  | .ok p => IO.println s!"reprints same: {← reprintsSame p}"

-- The declared names come back without the pipes, after a print and a parse.
#eval do
  match ← Strata.Test.CoreReparse.parseAndTranslate keywordPositionsSrc with
  | .error e => throw <| IO.userError s!"error: {e}"
  | .ok p =>
    match ← Strata.Test.CoreReparse.parseAndTranslate (Core.formatProgram p).pretty with
    | .error e => throw <| IO.userError s!"reparse error: {e}"
    | .ok q =>
      unless declNames q == declNames p do
        throw <| IO.userError s!"names changed: {declNames p} vs {declNames q}"
      unless ["var", "procedure", "forall", "old", "call"].all (declNames p).contains do
        throw <| IO.userError s!"missing names in {declNames p}"

end Strata.Test.KeywordIdentPrinter
