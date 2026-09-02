/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.DDMTransform.ASTtoCST
meta import Strata.Languages.Core.DDMTransform.Translate
meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init
import StrataDDM.Integration.Lean.HashCommands

meta section
open StrataDDM (Program initDialect)

/-!
# Core Roundtrip Tests

Tests that `Core.formatProgram` produces output that can be parsed back to the
same AST. The roundtrip is: parse → translate → format → re-parse → re-translate
→ compare.
-/

namespace Strata.Test.Roundtrip

open Strata
open Strata.CoreDDM
open Core
open Lean.Parser (InputContext)

/-- Parse a string as a Core program and translate to AST. -/
private def parseAndTranslate (input : String) : IO Core.Program := do
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Core]
  -- Strip "program Core;\n\n" header if present
  let body := if input.startsWith "program Core;\n\n" then
    (input.drop "program Core;\n\n".length).toString
  else input
  let inputCtx := StrataDDM.Parser.stringInputContext ⟨"roundtrip-test"⟩ body
  let strataProgram ← StrataDDM.Elab.parseStrataProgramFromDialect dialects "Core" inputCtx
  let (ast, errs) := TransM.run Inhabited.default (translateProgram strataProgram)
  if !errs.isEmpty then
    throw (IO.userError s!"Translation errors: {errs}")
  pure ast

/-- Perform a roundtrip test: parse → format → re-parse → compare.
    Prints OK or FAIL with details. -/
def roundtrip (program : StrataDDM.Program) : IO Unit := do
  -- First pass: translate to AST
  let (ast1, errs1) := TransM.run Inhabited.default (translateProgram program)
  if !errs1.isEmpty then
    IO.println s!"FAIL: First translation errors: {errs1}"
    return
  -- Format back to text
  let formatted := (Core.formatProgram ast1).pretty
  -- Second pass: re-parse and re-translate
  let ast2 ← parseAndTranslate formatted
  -- Compare: format both ASTs and check they match
  let formatted2 := (Core.formatProgram ast2).pretty
  if formatted == formatted2 then
    IO.println "OK"
  else
    IO.println s!"FAIL: Roundtrip mismatch.\nFirst format:\n{formatted}\nSecond format:\n{formatted2}"

-------------------------------------------------------------------------------
-- Test: Basic types and type aliases
-------------------------------------------------------------------------------

private def testTypesRoundtrip : Program :=
#strata
program Core;

type T0;
type Byte := bv W8;
type IntMap := Map int int;
type T1 (x : Type);
type MyMap (a : Type, b : Type);
type Foo (a : Type, b : Type) := Map b a;
#end

/-- info: OK -/
#guard_msgs in
#eval roundtrip testTypesRoundtrip

-------------------------------------------------------------------------------
-- Test: Polymorphic datatypes with parameterized types
-------------------------------------------------------------------------------

private def testDatatypesRoundtrip : Program :=
#strata
program Core;

datatype List (a : Type) {
  Nil(),
  Cons(head : a, tail : List a)
};

datatype Tree (a : Type) {
  Leaf(val : a),
  Node(left : Tree a, right : Tree a)
};
#end

/--
info: program Core;

datatype List (a : Type) {
  Nil(),
  Cons(head : a, tail : List a)
};
datatype Tree (a : Type) {
  Leaf(val : a),
  Node(left : Tree a, right : Tree a)
};
-/
#guard_msgs in
#eval do
  let (ast, _) := TransM.run Inhabited.default (translateProgram testDatatypesRoundtrip)
  IO.println f!"{Core.formatProgram ast}"

/-- info: OK -/
#guard_msgs in
#eval roundtrip testDatatypesRoundtrip

-------------------------------------------------------------------------------
-- Test: Functions and axioms with quantifiers
-------------------------------------------------------------------------------

private def testFunctionsRoundtrip : Program :=
#strata
program Core;

function f1(x : int) : int;
axiom [f1_ax]: (forall x : int :: int.gt(f1(x), x));

function f2(x : int, y : bool) : bool;
axiom [f2_ax]: (forall x : int, y : bool ::
                  {f2(x, true), f2(x, false)}
                  f2(x, true) == true);

function f3<T1, T2>(x : T1) : Map T1 T2;
#end

/-- info: OK -/
#guard_msgs in
#eval roundtrip testFunctionsRoundtrip

-------------------------------------------------------------------------------
-- Test: Procedures with specs
-------------------------------------------------------------------------------

private def testProceduresRoundtrip : Program :=
#strata
program Core;

procedure Test(x : bool, out y : bool)
spec {
  requires x == true;
  ensures y == x;
} {
  y := x;
};
#end

/-- info: OK -/
#guard_msgs in
#eval roundtrip testProceduresRoundtrip

-------------------------------------------------------------------------------
-- Test: Inline functions
-------------------------------------------------------------------------------

private def testInlineFunctionRoundtrip : Program :=
#strata
program Core;

inline function double(x : int) : int {
  int.add(x, x)
}
#end

/-- info: OK -/
#guard_msgs in
#eval roundtrip testInlineFunctionRoundtrip

-------------------------------------------------------------------------------
-- Test: Constants
--
-- Either form of `const` is sugar for a nullary function, and is formatted back
-- as one, so a constant reads as a parenthesized call at its use sites.
-------------------------------------------------------------------------------

-- The valueless form, which takes no type arguments.
private def testConstRoundtrip : Program :=
#strata
program Core;

const x : int;
const b : bool;
#end

/-- info: OK -/
#guard_msgs in
#eval roundtrip testConstRoundtrip

/--
info: program Core;

function x () : int;
function b () : bool;
-/
#guard_msgs in
#eval do
  let (ast, _) := TransM.run Inhabited.default
    (translateProgram testConstRoundtrip)
  IO.println f!"{Core.formatProgram ast}"

private def testConstWithValueRoundtrip : Program :=
#strata
program Core;

const x : int := 5;
const b : bool := true;
#end

/-- info: OK -/
#guard_msgs in
#eval roundtrip testConstWithValueRoundtrip

private def testInlineConstWithValueRoundtrip : Program :=
#strata
program Core;

const x : int := 5;
inline const y : int := int.add(x, 2);
#end

/-- info: OK -/
#guard_msgs in
#eval roundtrip testInlineConstWithValueRoundtrip

/--
info: program Core;

function x () : int {
  5
}
inline function y () : int {
  int.add(x, 2)
}
-/
#guard_msgs in
#eval do
  let (ast, _) := TransM.run Inhabited.default
    (translateProgram testInlineConstWithValueRoundtrip)
  IO.println f!"{Core.formatProgram ast}"

-- An operator-heavy right-hand side: nested arithmetic and a comparison under a
-- conditional are where the pretty-printer would add spurious parentheses.
private def testConstValueOperatorsRoundtrip : Program :=
#strata
program Core;

const base : int := int.mul(int.add(2, 3), int.sub(10, 4));
const flag : bool := if int.lt(base, 100) then true else false;
#end

/-- info: OK -/
#guard_msgs in
#eval roundtrip testConstValueOperatorsRoundtrip

/--
info: program Core;

function base () : int {
  int.mul(int.add(2, 3), int.sub(10, 4))
}
function flag () : bool {
  if int.lt(base, 100) then true else false
}
-/
#guard_msgs in
#eval do
  let (ast, _) := TransM.run Inhabited.default
    (translateProgram testConstValueOperatorsRoundtrip)
  IO.println f!"{Core.formatProgram ast}"

-------------------------------------------------------------------------------
-- Test: Parameterized type arguments (the reversed-args bug)
-------------------------------------------------------------------------------

private def testTypeArgsRoundtrip : Program :=
#strata
program Core;

type Pair (a : Type, b : Type);

function f(x : Pair int bool) : int;
function g(x : Map int bool) : int;
#end

/-- info: OK -/
#guard_msgs in
#eval roundtrip testTypeArgsRoundtrip

-------------------------------------------------------------------------------
-- Test: Array assignment (lhsArray: m[k] := v)
-------------------------------------------------------------------------------

private def testLhsArrayRoundtrip : Program :=
#strata
program Core;

procedure MapUpdate(m : Map int int, out m : Map int int)
spec {
  ensures true;
} {
  m[0] := 1;
};
#end

/-- info: OK -/
#guard_msgs in
#eval roundtrip testLhsArrayRoundtrip

-------------------------------------------------------------------------------
-- Test: Sequence.empty with explicit type annotation
-------------------------------------------------------------------------------

private def testSeqEmptyRoundtrip : Program :=
#strata
program Core;

function f(s : Sequence int) : bool;
axiom [f_ax]: f(Sequence.empty<int>()) == true;
#end

/-- info: OK -/
#guard_msgs in
#eval roundtrip testSeqEmptyRoundtrip

-------------------------------------------------------------------------------
-- Test: Arrow type as a type-constructor argument (the dropped-parens bug)
--
-- `Map int (int -> int)` must reprint *with* the parentheses. Without them the
-- string parses back as `(Map int int) -> int` because type application binds
-- tighter than `->`, breaking the round-trip.
-------------------------------------------------------------------------------

private def testArrowTypeArgRoundtrip : Program :=
#strata
program Core;

function f() : Map int (int -> int);
function g() : Sequence (Map int int -> bool);
function h() : Map (int -> int) int;
function i() : Sequence (Map int (int -> int));
function j() : Map (Sequence (int -> int)) int;
#end

/--
info: program Core;

function f () : Map int (int -> int);
function g () : Sequence (Map int int -> bool);
function h () : Map (int -> int) int;
function i () : Sequence (Map int (int -> int));
function j () : Map (Sequence (int -> int)) int;
-/
#guard_msgs in
#eval do
  let (ast, _) := TransM.run Inhabited.default (translateProgram testArrowTypeArgRoundtrip)
  IO.println f!"{Core.formatProgram ast}"

/-- info: OK -/
#guard_msgs in
#eval roundtrip testArrowTypeArgRoundtrip


-------------------------------------------------------------------------------
-- Test: context-sensitive `old x` vs `|old x|` round-trip
--
-- An `old x` free variable is printed as the CST `old x` construct only when
-- its base `x` is an in-scope inout variable (a genuine pre-state binding).
-- Otherwise the name is a plain free variable, printed `|old x|`. `old x` and
-- `|old x|` both translate back to the same AST name "old x".
-------------------------------------------------------------------------------

-- `x` is inout, so `old x` denotes its pre-state and prints as `old x`.
private def oldInoutPgm : Program :=
#strata
program Core;
procedure P(inout x : int)
{
  assert [a]: old x == x;
};
#end

/--
info: program Core;

procedure P (inout x : int)
{
  assert [a]: old x == x;
};
-/
#guard_msgs in
#eval show IO Unit from do
  let (ast, errs) := TransM.run Inhabited.default (translateProgram oldInoutPgm)
  for e in errs do IO.println s!"error: {e}"
  IO.println (Core.formatProgram ast).pretty

/-- info: OK -/
#guard_msgs in
#eval roundtrip oldInoutPgm

-- `x` is an `in` (not inout) parameter, so `old x` is not a pre-state binding:
-- it prints pipe-quoted as `|old x|`, not the `old` construct. This pins the
-- printer's decision only — a bare `old x` on a non-inout variable is not a real
-- pre-state reference, so the `|old x|` output is not itself re-parseable.
private def oldFlatPgm : Program :=
#strata
program Core;
procedure Q(x : int)
{
  assert [b]: old x == x;
};
#end

/--
info: program Core;

procedure Q (x : int)
{
  assert [b]: |old x| == x;
};
-/
#guard_msgs in
#eval show IO Unit from do
  let (ast, errs) := TransM.run Inhabited.default (translateProgram oldFlatPgm)
  for e in errs do IO.println s!"error: {e}"
  IO.println (Core.formatProgram ast).pretty

-- Shadowing: with an inout `x` AND a local `|old x|`, an `old x` reference binds
-- to the nearest binding named "old x" — the local `|old x|` assigned 10 — not a
-- fresh pre-state of `x`. Both surface forms denote the same name, so it
-- round-trips.
private def oldShadowPgm : Program :=
#strata
program Core;
procedure P(inout x : int)
{
  var |old x| : int := 10;
  assert [c]: old x == 11;
};
#end

/--
info: program Core;

procedure P (inout x : int)
{
  var |old x| : int := 10;
  assert [c]: |old x| == 11;
};
-/
#guard_msgs in
#eval show IO Unit from do
  let (ast, errs) := TransM.run Inhabited.default (translateProgram oldShadowPgm)
  for e in errs do IO.println s!"error: {e}"
  IO.println (Core.formatProgram ast).pretty

/-- info: OK -/
#guard_msgs in
#eval roundtrip oldShadowPgm


-------------------------------------------------------------------------------
-- Test: every named operator roundtrips
-------------------------------------------------------------------------------
/-!
Translate and FormatCore each maintain a hand-written table mapping the
grammar's named operators to internal Core ops and back. A transposed or
missing arm in either table is invisible to the type checker, so this test
generates one use of every named operator and roundtrips the whole program:
parse → translate → format → re-parse → re-translate → compare.
-/

private def bvWidths : List Nat := [1, 8, 16, 32, 64, 128]

/-- One statement per operator, at every width. Results land in typed local
    variables so the program is well-formed for Core's own type checker too. -/
private def allOpsProgramText : String := Id.run do
  let mut ls : List String := []
  -- int
  let intBin := ["add", "sub", "mul", "div", "mod", "safeDiv", "safeMod",
                 "divT", "modT", "safeDivT", "safeModT"]
  let intCmp := ["le", "lt", "ge", "gt"]
  for o in intBin do
    ls := ls ++ [s!"  var i_{o} : int := int.{o}(xi, yi);"]
  for o in intCmp do
    ls := ls ++ [s!"  var i_{o} : bool := int.{o}(xi, yi);"]
  ls := ls ++ ["  var i_neg : int := int.neg(xi);"]
  -- real
  for o in ["add", "sub", "mul", "div"] do
    ls := ls ++ [s!"  var r_{o} : real := real.{o}(xr, yr);"]
  for o in intCmp do
    ls := ls ++ [s!"  var r_{o} : bool := real.{o}(xr, yr);"]
  ls := ls ++ ["  var r_neg : real := real.neg(xr);"]
  -- bv families at every width
  for w in bvWidths do
    let bv := s!"bv{w}"
    let a := s!"a{w}"
    let b := s!"b{w}"
    let ty := s!"bv W{w}"
    for o in ["neg", "not", "safeNeg", "safeUNeg"] do
      ls := ls ++ [s!"  var {bv}_{o} : {ty} := {bv}.{o}({a});"]
    for o in ["sNegOverflow", "uNegOverflow"] do
      ls := ls ++ [s!"  var {bv}_{o} : bool := {bv}.{o}({a});"]
    for o in ["add", "sub", "mul", "and", "or", "xor", "shl", "uShr", "sShr",
              "uDiv", "uMod", "sDiv", "sMod",
              "safeAdd", "safeSub", "safeMul", "safeUAdd", "safeUSub",
              "safeUMul", "safeSDiv", "safeSMod"] do
      ls := ls ++ [s!"  var {bv}_{o} : {ty} := {bv}.{o}({a}, {b});"]
    for o in ["uLe", "uLt", "uGe", "uGt", "sLe", "sLt", "sGe", "sGt",
              "sAddOverflow", "sSubOverflow", "sMulOverflow", "sDivOverflow",
              "uAddOverflow", "uSubOverflow", "uMulOverflow"] do
      ls := ls ++ [s!"  var {bv}_{o} : bool := {bv}.{o}({a}, {b});"]
    for o in ["toUInt", "toInt"] do
      ls := ls ++ [s!"  var {bv}_{o} : int := {bv}.{o}({a});"]
    ls := ls ++ [s!"  var {bv}_from_int : {ty} := as_bv{w}(xi);"]
  let header := String.intercalate "\n" <|
    ["procedure allOps(xi : int, yi : int, xr : real, yr : real"]
    ++ (bvWidths.map fun w => s!"  , a{w} : bv W{w}, b{w} : bv W{w}")
    ++ [")", "{"]
  return header ++ "\n" ++ String.intercalate "\n" ls ++ "\n};\n"

/-- Parse program text, translate, format, re-parse, re-translate, compare. -/
private def roundtripText (text : String) : IO Unit := do
  let ast1 ← parseAndTranslate text
  let formatted := (Core.formatProgram ast1).pretty
  let ast2 ← parseAndTranslate formatted
  let formatted2 := (Core.formatProgram ast2).pretty
  if formatted == formatted2 then
    IO.println "OK"
  else
    -- Report the first differing line so a broken arm is identifiable.
    let l1 := formatted.splitOn "\n"
    let l2 := formatted2.splitOn "\n"
    for (a, b) in l1.zip l2 do
      if a ≠ b then
        IO.println s!"FAIL first diff:\n  first : {a}\n  second: {b}"
        return
    IO.println s!"FAIL: length mismatch {l1.length} vs {l2.length}"

/-- info: OK -/
#guard_msgs in
#eval roundtripText allOpsProgramText

-------------------------------------------------------------------------------
-- Test: a negative real literal prints as `real.neg(<positive>)`, so a leading
-- minus is always a parenthesized `real.neg` that re-parses. Surface syntax has
-- no negative-real-literal token, so these ASTs are built directly.
-------------------------------------------------------------------------------

/-- `Real.Neg` applied to expression `e`. -/
private def rNeg (e : Core.Expression.Expr) : Core.Expression.Expr :=
  .app () (.op () ⟨"Real.Neg", ()⟩ (some (.arrow .real .real))) e

/-- A bare negative real literal, and `Real.Neg` applied to one. -/
private def negRealLitPgm : Core.Program := { decls := [
  .func { name := "negLit", typeArgs := [], inputs := [], output := .real,
          body := some (.realConst () (-3 : Rat)) } .empty,
  .func { name := "negNegLit", typeArgs := [], inputs := [], output := .real,
          body := some (rNeg (.realConst () (-3 : Rat))) } .empty
]}

/--
info: program Core;

function negLit () : real {
  real.neg(3.0)
}
function negNegLit () : real {
  real.neg(real.neg(3.0))
}
-/
#guard_msgs in
#eval do IO.println f!"{Core.formatProgram negRealLitPgm}"

/-- info: OK -/
#guard_msgs in
#eval roundtripText (Core.formatProgram negRealLitPgm).pretty

end Strata.Test.Roundtrip

end
