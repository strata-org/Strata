/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Transform.GenOpaqueTypeParams

/-! # Closing a lemma's type variables avoids every declared name

`genOpaqueTypeParams` closes each type variable left in a lemma's annotations with a fresh opaque
type named `$__free_<lemma>_<i>`. Declarations share one namespace of names, so the fresh name
avoids every name the program declares with that prefix, a function's as well as a type's. Here a
function is named `$__free_L_0`, the name closing lemma `L`'s type variable would take: the
opaque type gets another name, and both declarations stay.

Type checking rejects a written lemma typed at a type variable it does not declare, so the
lemma here is built directly, as a pass that generates lemmas after type checking would. -/

meta section

namespace Core.CloseAvoidsDeclNamesTests

open Core Strata

private def basePgm :=
#strata
program Core;
function $__free_L_0 () : int { 1 }
lemma [L] <a>: forall x : a, y : a :: x == y;
lemma [M]: $__free_L_0() == 1;
#end

private def baseProgram : Core.Program :=
  (TransM.run Inhabited.default (translateProgram basePgm)).fst

/-- `basePgm` with lemma `L`'s type parameter dropped, so `a` is left open in its annotations. -/
private def openProgram : Core.Program :=
  { decls := baseProgram.decls.map fun
      | .lemma l md => if l.name == "L" then .lemma { l with typeArgs := [] } md else .lemma l md
      | d => d }

/-- The names `q` declares. -/
private def names (q : Core.Program) : List String := q.getNames.map (·.name)

-- Closing adds one opaque type, not named like the function.
#guard match Core.Transform.run openProgram genOpaqueTypeParams with
  | .ok (_, q) => names q == ["$__free_L_0", "$__free_L_0_1", "L", "M"] && (names q).Nodup
  | .error _ => false

-- Both lemmas get the verdicts the program deserves: `L` is false at some type, `M` holds.
/--
info:
Obligation: L
Property: assert
Result: ❌ fail

Obligation: M
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify basePgm (options := .quiet)

end Core.CloseAvoidsDeclNamesTests

end
