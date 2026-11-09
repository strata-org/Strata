/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.Verifier
import StrataDDM.Integration.Lean.HashCommands

meta section
open StrataDDM (Program)

/-! # Type inference annotates the map and sequence operators

`Core.Specification.Analysis.TypeCheckAnnotates` states that every expression of a program
that `Core.typeCheck` accepts carries a type on each operator and free variable. The
translator from the Strata dialect emits the map operators `Select` and `Update` and
`Sequence.length` without a type.
On a program that uses them, the translated program is not fully annotated, and the
type-checked program is.
-/

namespace Strata.TypeCheckAnnotatesTest

private def mapSeqPgm : Program :=
#strata
program Core;

procedure test(m : Map int int, k : int, v : int) {
  var m2 : Map int int := m[k := v];
  var s : Sequence int := Sequence.empty<int>();
  var n : int := Sequence.length(s);
  assert [sel]: m2[k] == v;
};
#end

private def translated : Core.Program :=
  (TransM.run Inhabited.default (translateProgram mapSeqPgm)).fst

/-- The expressions of `p` that miss a type on an operator or a free variable. -/
private def unannotated (p : Core.Program) : List String :=
  p.decls.flatMap fun d =>
    ((Core.Statements.allExprs d.statements).filter (! Lambda.LExpr.fullyAnnotated ·)).map
      fun e => toString (Std.format e)

-- The translator leaves `Update`, `Select` and `Sequence.length` without a type.
#guard unannotated translated = ["m[k:=v]", "Sequence.length(s)", "m2[k] == v"]

-- Type inference annotates every expression.
#guard match Core.typeCheck .quiet translated with
  | .ok p => p.allExprs Lambda.LExpr.fullyAnnotated
  | .error _ => false

end Strata.TypeCheckAnnotatesTest
