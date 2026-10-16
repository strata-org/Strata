/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
open StrataDDM (Program)

/-! ## Test: names are escaped before they are emitted as SMT-LIB symbols

Core names are arbitrary strings, while SMT-LIB symbols have their own lexical
rules. Interpolating a name into a command lets it supply that command's
*structure*, so these tests run a real solver: they check a verdict, not a
rendering.

The first is the one that matters. A name that closes the parens of the
`declare-datatype` it sits in can append commands of its own, and
`(assert false)` discharges every obligation, because a VC asserts the negation
of its goal and reads `unsat` as proved. The obligation below is false, so
anything other than `❌ fail` means a name has been executed as script.
-/

/-! ### What in these expectations is ours and what is the solver's

The verdict is what this file is testing, and it follows from the script we emit.
The `Model:` line is only partly ours: the *keys* are our names, escaped and read
back by us, while the witness values and the names a solver invents for the elements
of an uninterpreted sort, along with the order it assigns them, are its own choice.
SMT-LIB does not fix any of that, so a solver upgrade can move those without
anything being wrong here. Pinning them anyway follows the convention of the
examples under `StrataTest/Languages/Core/Examples`, and it is what makes a lost
counterexample visible.

If one of these diffs after a solver upgrade, the question to ask is whether the
*keys* still read as the source spells them. That is our part, and it is pinned
independently of any solver by `ofSolverSymbol` in `StrataTest/DL/SMT/SymbolTests`.
-/

namespace Strata

/-- A constructor name that closes its own declaration and appends
    `(assert false)`, followed by a well-formed decoy datatype to consume the
    trailing parens. Nothing references the constructor: only the declaration
    site can be at fault. -/
private def constructorInjection : Program :=
#strata
program Core;
type S;
datatype Box { |MkBox) ) ) (assert false) (declare-datatype Junk ((J|(f: int) };
procedure Test(a : S, b : S, out r : int)
spec {
  ensures a == b;
}
{
  r := 0;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: Test_ensures_0
Property: assert
Obligation:
a@1 == b@1

---
info:
Obligation: Test_ensures_0
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify constructorInjection

---------------------------------------------------------------------

/-- A selector name holding a character both solvers reject unquoted. Reaching
    the solver bare, this ends the enclosing command early. -/
private def apostropheSelector : Program :=
#strata
program Core;
datatype Box { MkBox(x': int) };
procedure Test(b : Box, out r : int)
spec {
  ensures r == Box..x'(b);
}
{
  r := 0;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: Test_ensures_0
Property: assert
Obligation:
0 == |Box..x'|(b@1)

---
info:
Obligation: Test_ensures_0
Property: assert
Result: ❌ fail
Model:
(b@1, MkBox(int.neg(1)))
-/
#guard_msgs in
#eval Core.verify apostropheSelector

---------------------------------------------------------------------

/-- A name containing `|`. SMT-LIB quoted symbols may not contain `|` and give
    no way to escape it, so this name has no legal emitted spelling and must be
    encoded. Emitting DDM's `\|` instead makes cvc5 end the symbol at the inner
    bar while z3 accepts it, so the two solvers disagree about this program. -/
private def pipeInName : Program :=
#strata
program Core;
procedure Test(|a\|b| : int, out r : int)
spec {
  ensures r == |a\|b|;
}
{
  r := 0;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: Test_ensures_0
Property: assert
Obligation:
0 == |a\|b@1|

---
info:
Obligation: Test_ensures_0
Property: assert
Result: ❌ fail
Model:
(a|b@1, int.neg(1))
-/
#guard_msgs in
#eval Core.verify pipeInName

---------------------------------------------------------------------

/-- A sort name containing a space. Emitted bare this reads as two tokens, so
    the declaration's arity is lost. A name controlling the command's shape
    rather than merely being an illegal token. -/
private def spaceInSortName : Program :=
#strata
program Core;
type |a b|;
procedure Test(a : |a b|, b : |a b|, out r : int)
spec {
  ensures a == b;
}
{
  r := 0;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: Test_ensures_0
Property: assert
Obligation:
a@1 == b@1

---
info:
Obligation: Test_ensures_0
Property: assert
Result: ❌ fail
Model:
(a@1, |@_a b__0|) (b@1, |@_a b__1|)
-/
#guard_msgs in
#eval Core.verify spaceInSortName

---------------------------------------------------------------------

/-- A variable whose name needs quoting. The solver echoes a symbol in the
    spelling it was emitted with, so reading a model back means undoing that
    spelling: comparing it to the encoder's id directly matches nothing, and the
    counterexample is then dropped for exactly the names that needed quoting.
    A missing `Model:` line here is the regression. -/
private def modelReadBack : Program :=
#strata
program Core;
procedure Test(v' : int, out r : int)
spec {
  ensures r == v';
}
{
  r := 0;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: Test_ensures_0
Property: assert
Obligation:
0 == |v'@1|

---
info:
Obligation: Test_ensures_0
Property: assert
Result: ❌ fail
Model:
(v'@1, int.neg(1))
-/
#guard_msgs in
#eval Core.verify modelReadBack

---------------------------------------------------------------------

/-- A sort name whose first character is reserved. SMT-LIB reserves the leading
    `@` and `.` for solver-generated symbols, and quoting does not lift that:
    cvc5 rejects `@x` and `|@x|` alike, so this needs escaping rather than
    quoting. A `@N` suffix could not have fixed it either, since it cannot change
    a first character. -/
private def reservedFirstCharSort : Program :=
#strata
program Core;
type |@x|;
procedure Test(a : |@x|, b : |@x|, out r : int)
spec {
  ensures a == b;
}
{
  r := 0;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: Test_ensures_0
Property: assert
Obligation:
a@1 == b@1

---
info:
Obligation: Test_ensures_0
Property: assert
Result: ❌ fail
Model:
(a@1, |@_`40x__0|) (b@1, |@_`40x__1|)
-/
#guard_msgs in
#eval Core.verify reservedFirstCharSort

---------------------------------------------------------------------

/-- A variable whose name begins with `.`, the other reserved first character.

    The `Model:` line is the point of this case. Every name here needs escaping,
    and an escaped name contains a backtick, which cannot appear in a bare SMT-LIB
    simple symbol, so the solver echoes it pipe-quoted, and a quoted symbol is one
    the answer parser can read. Escaping with a character SMT-LIB admits bare
    instead would have the solver echo it bare and the answer fail to parse,
    losing the counterexample silently. -/
private def reservedFirstCharVar : Program :=
#strata
program Core;
procedure Test(|.v| : int, out r : int)
spec {
  ensures r == |.v|;
}
{
  r := 0;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: Test_ensures_0
Property: assert
Obligation:
0 == |.v@1|

---
info:
Obligation: Test_ensures_0
Property: assert
Result: ❌ fail
Model:
(.v@1, int.neg(1))
-/
#guard_msgs in
#eval Core.verify reservedFirstCharVar

---------------------------------------------------------------------

end Strata

end
