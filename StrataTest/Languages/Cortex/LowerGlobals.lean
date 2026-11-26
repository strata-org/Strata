/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataTest.Languages.Cortex.HandBuilt

/-!
# The `LowerGlobals` pass on postconditions

`bump` writes the global `g`, which becomes a parameter that is both an input and
an output, so its postcondition keeps `old g`. `peek` only reads `g`, which becomes
an input, so `old g` in its postcondition becomes `g`. `ToCore` emits both
postconditions as Core `ensures`.
-/

meta section

namespace Cortex.LowerGlobalsTest

open Imperative Lambda Cortex.HandBuilt

/-- A program with the global `g`, and the procedures `bump` and `peek`. -/
def globalsProgram : UnorderedProgram :=
  { composites := [], globals := [(idn "g", mono .int)],
    procedures := [
      { name := "bump", inputs := [], outputs := [], throws := none,
        ensures := [{ label := "grew", cond := mkCall "Int.Gt" [mkFvar "g", mkFvar "old g"] }],
        body := some { handlers := [], cfg := { entry := "E", blocks := [("E", blk
          [.cmd (.set (idn "g") (.det (mkCall "Int.Add" [mkFvar "g", intLit 1])) .empty)] fin)] } } },
      { name := "peek", inputs := [], outputs := [(idn "r", mono .int)], throws := none,
        ensures := [{ label := "same", cond := .eq Core.coreLoc (mkFvar "r") (mkFvar "old g") }],
        body := some { handlers := [], cfg := { entry := "E", blocks := [("E", blk
          [setV "r" "g"] fin)] } } }] }

/--
info: program Core;

procedure bump (inout g : int)
spec {
  ensures [grew]: int.gt(g, old g);
  } cfg E {
  E: {
    g := int.add(g, 1);
    return;
  }
};
procedure peek (g : int, out r : int)
spec {
  ensures [same]: r == g;
  } cfg E {
  E: {
    r := g;
    return;
  }
};

type check ok
-/
#guard_msgs in
#eval report (passes := [LowerGlobals.pass, Ordering.pass]) (print := true) globalsProgram

/-- An entry procedure whose postcondition reads `old g`, which has no meaning once the
entry initializes `g` itself. -/
def entryOld : UnorderedProgram :=
  { composites := [], globals := [(idn "g", mono .int)],
    procedures := [
      { name := "main", inputs := [], outputs := [], throws := none,
        md := (MetaData.empty : MD).pushElem MetaData.interpretEntry (.switch true),
        ensures := [{ label := "grew", cond := mkCall "Int.Gt" [mkFvar "g", mkFvar "old g"] }],
        body := some { handlers := [], cfg := { entry := "E", blocks := [("E", blk [] fin)] } } }] }

/--
info: LowerGlobals: the postconditions of the entry procedure 'main' read a global
-/
#guard_msgs in
#eval report (passes := [LowerGlobals.pass, Ordering.pass]) entryOld

/-- An entry procedure whose postcondition reads the global `g` itself. The entry's globals
are locals of its body, so `g` is out of scope in the postcondition and the pass rejects
the program instead of leaving a variable that Core cannot type check. -/
def entryPlainGlobal : UnorderedProgram :=
  { composites := [], globals := [(idn "g", mono .int)],
    procedures := [
      { name := "main", inputs := [], outputs := [], throws := none,
        md := (MetaData.empty : MD).pushElem MetaData.interpretEntry (.switch true),
        ensures := [{ label := "positive", cond := mkCall "Int.Gt" [mkFvar "g", intLit 0] }],
        body := some { handlers := [], cfg := { entry := "E", blocks := [("E", blk [] fin)] } } }] }

/--
info: LowerGlobals: the postconditions of the entry procedure 'main' read a global
-/
#guard_msgs in
#eval report (passes := [LowerGlobals.pass, Ordering.pass]) entryPlainGlobal

end Cortex.LowerGlobalsTest
