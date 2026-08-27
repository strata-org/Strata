/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Unit tests for the global-variable effect analysis (`GlobalVarAnalysis`).

Computes deterministic reader/writer summaries for direct effects, framing,
transitive calls, recursion, contracts, shadowing, increments, `invokeOn`, and
`modifies`.
-/

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel.GlobalVarAnalysis
import Strata.Languages.Laurel.Resolution

open Strata
open StrataTest.Util

namespace Strata.Laurel

private def parseAndResolve (program : StrataDDM.Program) : IO (Program × SemanticModel) := do
  let laurelProgram ← translateLaurel program
  let result := resolve (withBuiltins laurelProgram)
  for diagnostic in result.errors do
    IO.println s!"resolution diagnostic: {diagnostic.message}"
  pure (result.program, result.model)

/-- Render a `global → {procs}` map as sorted lines `global: p1, p2, …`, with
    both the globals and their procedure sets sorted by name so the golden is
    deterministic. Globals with an empty set are printed as `global: (none)`. -/
private def renderMap (globals : List Field) (procedures : List Procedure)
    (m : Std.HashMap Nat (Std.HashSet Nat)) : String := Id.run do
  let mut out := ""
  for f in globals do
    let ids := match f.name.uniqueId with
      | some id => m.getD id {}
      | none => {}
    let procs := procedures.filterMap fun proc =>
      proc.name.uniqueId.bind fun id => if ids.contains id then some proc.name.text else none
    let sorted := (procs.toArray.qsort (· < ·)).toList
    let rhs := if sorted.isEmpty then "(none)" else ", ".intercalate sorted
    out := out ++ s!"{f.name.text}: {rhs}\n"
  pure out

/-- Parse + resolve, then print the reader and writer sets for every global. -/
private def testGlobalEffects (program : StrataDDM.Program) : IO Unit := do
  let (prog, model) ← parseAndResolve program
  let effects := computeGlobalEffectsByProcId model prog.staticProcedures prog.staticFields
  IO.println "readers:"
  IO.print (renderMap prog.staticFields prog.staticProcedures effects.readers)
  IO.println "writers:"
  IO.print (renderMap prog.staticFields prog.staticProcedures effects.writers)

/-! ## Direct read and write classification, per-global framing -/

/--
info: readers:
counter: reader
other: (none)
writers:
counter: writer
other: (none)
-/
#guard_msgs in
#eval testGlobalEffects
#strata
program Laurel;
var counter: int := 0
var other: int := 0
procedure reader() returns (r: int) opaque {
  return counter + 1
};
procedure writer() opaque {
  counter := 3
};
#end

/-! ## Transitivity + framing: pure-read and pure-write effects propagate
    independently up the call graph, keyed per global.

    `readLeaf` only reads `g`; `writeLeaf` only writes `g`. A caller that calls
    `readLeaf` becomes a reader but not a writer, and vice versa. `both` calls
    each once and so is both. `other` is never touched. -/

/--
info: readers:
g: both, callsReader, readLeaf
other: (none)
writers:
g: both, callsWriter, writeLeaf
other: (none)
-/
#guard_msgs in
#eval testGlobalEffects
#strata
program Laurel;
var g: int := 0
var other: int := 0
procedure readLeaf() returns (r: int) opaque {
  return g + 1
};
procedure writeLeaf() opaque {
  g := 3
};
procedure callsReader() returns (r: int) opaque {
  return readLeaf()
};
procedure callsWriter() opaque {
  writeLeaf()
};
procedure both() returns (r: int) opaque {
  writeLeaf();
  return readLeaf()
};
#end

/-! ## Self-recursion: a recursive writer classifies without diverging -/

/--
info: readers:
g: recur
writers:
g: recur
-/
#guard_msgs in
#eval testGlobalEffects
#strata
program Laurel;
var g: int := 0
procedure recur(n: int) returns (r: int) opaque {
  g := g + n;
  if n > 0 then {
    var x: int := recur(n - 1)
  } else { };
  return g
};
#end

/-! ## Mutual recursion: effects propagate around the cycle -/

/--
info: readers:
g: ping, pong
writers:
g: ping, pong
-/
#guard_msgs in
#eval testGlobalEffects
#strata
program Laurel;
var g: int := 0
procedure ping(n: int) returns (r: int) opaque {
  g := g + 1;
  var x: int := pong(n);
  return g
};
procedure pong(n: int) returns (r: int) opaque {
  var y: int := ping(n);
  return g
};
#end

/-! ## A global read only in a postcondition still counts as a read -/

/--
info: readers:
g: spec
writers:
g: (none)
-/
#guard_msgs in
#eval testGlobalEffects
#strata
program Laurel;
var g: int := 0
procedure spec() returns (r: int)
  opaque
  ensures r == g;
#end

/-! ## Shadow-correctness: a local shadowing a global is not an effect -/

/--
info: readers:
g: (none)
writers:
g: (none)
-/
#guard_msgs in
#eval testGlobalEffects
#strata
program Laurel;
var g: int := 0
procedure shadows() returns (r: int) opaque {
  var g: int := 7;
  g := g + 1;
  return g
};
#end

/-! ## IncrDecr on a global (`g++`) counts as both a read and a write. -/

/--
info: readers:
g: incr
writers:
g: incr
-/
#guard_msgs in
#eval testGlobalEffects
#strata
program Laurel;
var g: int := 0
procedure incr() opaque {
  g++
};
#end

/-! ## A global read only in a `requires` precondition still counts as a read:
    the precondition is scanned by `analyzeProcGlobals`, so `needsG` becomes a
    reader (and after the pass would take `g` as an input parameter). -/

/--
info: readers:
g: needsG
writers:
g: (none)
-/
#guard_msgs in
#eval testGlobalEffects
#strata
program Laurel;
var g: int := 0
procedure needsG(v: int)
  requires v == g
  opaque
  ensures true;
#end

/-! ## Procedure metadata participates in global-read analysis -/

/--
info: readers:
g: trigger
cell: touch
writers:
g: (none)
cell: (none)
-/
#guard_msgs in
#eval testGlobalEffects
#strata
program Laurel;
composite Cell {
  var value: int
}
var g: int := 0
var cell: Cell := new Cell
procedure P(x: int): bool;
procedure trigger()
  invokeOn P(g)
  opaque
  ensures true
{
};
procedure touch()
  opaque
  modifies cell
{
};
#end

/-! ## Compound assignment on a global reads and writes it. -/

/--
info: readers:
g: compound
writers:
g: compound
-/
#guard_msgs in
#eval testGlobalEffects
#strata
program Laurel;
var g: int := 0
procedure compound() opaque {
  g += 1
};
#end

/-! ## A field assignment through a composite-valued global reads the global
    reference but does not replace the global itself. Heap parameterization,
    rather than global parameterization, owns the field write. -/

/--
info: readers:
cell: mutateField
writers:
cell: (none)
-/
#guard_msgs in
#eval testGlobalEffects
#strata
program Laurel;
composite Cell {
  var value: int
}
var cell: Cell := new Cell
procedure mutateField() opaque {
  cell#value := 9
};
#end

end Strata.Laurel
