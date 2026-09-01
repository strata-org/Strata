/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Checked
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import StrataDDM.Integration.Lean.HashCommands

meta import Strata.Languages.Laurel.Checked
meta import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator

/-!
# Checked Laurel API tests

Covers the public checked interface:
- expression literals and `Builder` combinators, reified into procedures and asserted
  against their rendered Laurel (`formatStmtExpr` / `formatProcedure`);
- `derive_laurel_ops` over a small hand-written theory, with `#print` pinning each
  generated combinator.

Calls use the generated `Set` combinators (`setEmpty`/`setInsert`/`setContains`) rather
than the raw `Expr.rawCall` escape hatch; `Expr.rawLocalRef` is used only to reference
parameters.
-/

open Strata Strata.Laurel Strata.Laurel.Checked

/-! ## Expression literals -/

/-- info: 3 -/
#guard_msgs in #eval IO.println (toString (formatStmtExpr (Expr.intLit 3).node))

/-- info: true -/
#guard_msgs in #eval IO.println (toString (formatStmtExpr (Expr.boolLit true).node))

/-- info: "hi" -/
#guard_msgs in #eval IO.println (toString (formatStmtExpr (Expr.strLit "hi").node))

/-! ## Builder combinators -/

def buildSet : Procedure :=
  reifyValueProc "buildSet" #[] #[] do
    let s ← letLocal "s" (setInsert setEmpty (Expr.intLit 3))
    let t ← letLocal "t" (setInsert s (Expr.intLit 4))
    pure t

/--
info: procedure buildSet(): Set
{
  var s$0: Set := setInsert(setEmpty(), 3);
  var t$1: Set := setInsert(s$0, 4);
  return t$1
};
-/
#guard_msgs in #eval IO.println (toString (formatProcedure buildSet))

def classify : Procedure :=
  reifyUnitProc "classify" #[("s", Set .int)] #[] do
    let s : Expr (Set .int) := Expr.rawLocalRef "s"
    lifElse (setContains s (Expr.intLit 0))
      (do let _ ← letLocal "hi" (setInsert s (Expr.intLit 1)); pure ())
      (do let _ ← letLocal "lo" (setEmpty (T := .int)); pure ())

/--
info: procedure classify(s: Set)
{
  if setContains(s, 0)
    then {
      var hi$0: Set := setInsert(s, 1)
    }
    else {
      var lo$1: Set := setEmpty()
    }
};
-/
#guard_msgs in #eval IO.println (toString (formatProcedure classify))

def spin : Procedure :=
  reifyUnitProc "spin" #[("s", Set .int)] #[] do
    let s : Expr (Set .int) := Expr.rawLocalRef "s"
    lwhile (setContains s (Expr.intLit 0))
      (do let _ ← letLocal "step" (setInsert s (Expr.intLit 1)); pure ())

/--
info: procedure spin(s: Set)
{
  while(setContains(s, 0)) {
    var step$0: Set := setInsert(s, 1)
  }
};
-/
#guard_msgs in #eval IO.println (toString (formatProcedure spin))

def guarded : Procedure :=
  reifyValueProc "guarded" #[("s", Set .int)]
    #[setContains (Expr.rawLocalRef (α := Set .int) "s") (Expr.intLit 0)] do
    pure (Expr.rawLocalRef (α := Set .int) "s")

/--
info: procedure guarded(s: Set): Set
  requires setContains(s, 0)
return s;
-/
#guard_msgs in #eval IO.println (toString (formatProcedure guarded))

-- The no-`else` `ll:if` expansion (`lif`), distinct from the `lifElse` path above.
def noElseIf : Procedure :=
  reifyUnitProc "noElseIf" #[("s", Set .int)] #[] do
    let s : Expr (Set .int) := Expr.rawLocalRef "s"
    ll:if (setContains s (Expr.intLit 0)) then
      let _ ← letLocal "hi" (setInsert s (Expr.intLit 1))
      pure ()

/--
info: procedure noElseIf(s: Set)
{
  if setContains(s, 0)
    then {
      var hi$0: Set := setInsert(s, 1)
    }
};
-/
#guard_msgs in #eval IO.println (toString (formatProcedure noElseIf))

-- `ll:set recv.field val` → `Expr.rawSetField` → a field assignment statement.
def setField : Procedure :=
  reifyUnitProc "setField" #[("s", Set .int)] #[] do
    let s : Expr (Set .int) := Expr.rawLocalRef "s"
    ll:set s.contents (setInsert s (Expr.intLit 5))

/--
info: procedure setField(s: Set)
{
  s#contents := setInsert(s, 5)
};
-/
#guard_msgs in #eval IO.println (toString (formatProcedure setField))

-- `Expr.rawGetField` — the read-side counterpart of `ll:set`/`rawSetField`.
def getField : Procedure :=
  reifyValueProc "getField" #[("s", Set .int)] #[] do
    let s : Expr (Set .int) := Expr.rawLocalRef "s"
    pure (Expr.rawGetField s "contents" .int)

/--
info: procedure getField(s: Set): int
return s#contents;
-/
#guard_msgs in #eval IO.println (toString (formatProcedure getField))

/-! ## `derive_laurel_ops`

A small theory — one opaque type, one polymorphic datatype, one external procedure —
with `#print` pinning each generated combinator.
-/

def smallTheoryDDM := #strata
program Laurel;

opaque Box<T>

opaque My$Thing

datatype Pair<A, B> {
  MkPair(fst: A, snd: B)
}

type IntBox = Box<int>

procedure boxOf(x: int) : Box<int> external;

procedure doNothing(x: int) external;
#end

/-- The theory above as a Laurel `Program`, parsed at compile time. -/
def smallTheory : Program :=
  match TransM.run (Uri.file "<#strata>") (parseProgram smallTheoryDDM) with
  | .ok p => p
  | .error e => panic! s!"smallTheory parse error: {e}"

derive_laurel_ops smallTheory

/--
info: private def Box : Ty → Ty :=
fun T => Ty.named "Box" [T]
-/
#guard_msgs in #print Box

-- A `$` in a Laurel name is stripped from the generated Lean identifier (`sanitizedName` /
-- `leanIdentOf`) but preserved in the `Ty.named` string that names the Laurel type.
/--
info: private def MyThing : Ty :=
Ty.named "My$Thing"
-/
#guard_msgs in #print MyThing

/--
info: private def Pair : Ty → Ty → Ty :=
fun A B => Ty.named "Pair" [A, B]
-/
#guard_msgs in #print Pair

/--
info: private def MkPair : {A B : Ty} → Expr A → Expr B → Expr (Pair A B) :=
fun {A B} fst snd => Expr.rawCall "MkPair" [fst.node, snd.node]
-/
#guard_msgs in #print MkPair

/--
info: private def Pair.isMkPair : {A B : Ty} → Expr (Pair A B) → Expr Ty.bool :=
fun {A B} x => Expr.rawCall "Pair..isMkPair" [x.node]
-/
#guard_msgs in #print Pair.isMkPair

/--
info: private def Pair.fst : {A B : Ty} → Expr (Pair A B) → Expr A :=
fun {A B} x => Expr.rawCall "Pair..fst" [x.node]
-/
#guard_msgs in #print Pair.fst

/--
info: private def Pair.snd : {A B : Ty} → Expr (Pair A B) → Expr B :=
fun {A B} x => Expr.rawCall "Pair..snd" [x.node]
-/
#guard_msgs in #print Pair.snd

/--
info: private def boxOf : Expr Ty.int → Expr (Box Ty.int) :=
fun x => Expr.rawCall "boxOf" [x.node]
-/
#guard_msgs in #print boxOf

-- A zero-output procedure: the derive's `[] => Ty.none` result-type branch. Its combinator
-- returns `Expr Ty.none` (a void, statement-like call).
/--
info: private def doNothing : Expr Ty.int → Expr Ty.none :=
fun x => Expr.rawCall "doNothing" [x.node]
-/
#guard_msgs in #print doNothing

-- The `.Alias` generation branch: `type IntBox = Box<int>` gets a `Ty` def like an opaque
-- (the target is unfolded later by Laurel's alias-elimination pass).
/--
info: private def IntBox : Ty :=
Ty.named "IntBox"
-/
#guard_msgs in #print IntBox

/-! ### Name-collision handling

Laurel forbids duplicate top-level names, but `derive_laurel_ops` reads the *parsed* program
(before resolution), so a repeated value-constructor name is skipped with a `logInfo` rather
than aborting the whole command with a raw "already declared" error. -/

def collisionTheoryDDM := #strata
program Laurel;
datatype AA { Shared() }
datatype BB { Shared() }
#end

def collisionTheory : Program :=
  match TransM.run (Uri.file "<#strata>") (parseProgram collisionTheoryDDM) with
  | .ok p => p
  | .error e => panic! s!"collisionTheory parse error: {e}"

/--
info: derive_laurel_ops: skipping constructor 'Shared': name collides with an already-generated definition
-/
#guard_msgs in derive_laurel_ops collisionTheory

-- Same-datatype constructor collision: the second `Sh` skips its *whole* combinator set (value
-- constructor, tester, and getters), so the duplicate tester `D.isSh` is not emitted either.
def collisionSameDatatypeDDM := #strata
program Laurel;
datatype D { Sh(), Sh() }
#end

def collisionSameDatatype : Program :=
  match TransM.run (Uri.file "<#strata>") (parseProgram collisionSameDatatypeDDM) with
  | .ok p => p
  | .error e => panic! s!"collisionSameDatatype parse error: {e}"

/--
info: derive_laurel_ops: skipping constructor 'Sh': name collides with an already-generated definition
-/
#guard_msgs in derive_laurel_ops collisionSameDatatype

/-! ### `keep` filter

The optional `keep` clause restricts which declarations are emitted. -/

def keepTheoryDDM := #strata
program Laurel;
opaque KeepMe
opaque DropMe
#end

def keepTheory : Program :=
  match TransM.run (Uri.file "<#strata>") (parseProgram keepTheoryDDM) with
  | .ok p => p
  | .error e => panic! s!"keepTheory parse error: {e}"

derive_laurel_ops keepTheory keep (· == "KeepMe")

/--
info: private def KeepMe : Ty :=
Ty.named "KeepMe"
-/
#guard_msgs in #print KeepMe

-- `DropMe` was filtered out by `keep`, so no combinator was generated for it.
/--
error: Unknown constant `DropMe`
-/
#guard_msgs in #print DropMe
