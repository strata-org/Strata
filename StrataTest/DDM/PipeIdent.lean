/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean

open Strata

-- Test dialect for pipe-delimited identifiers (SMT-LIB 2.6 syntax)
#dialect
dialect PipeIdent;

category Expression;

op var (name : Ident) : Expression => name;
op assign (lhs : Ident, rhs : Expression) : Command => lhs:0 " := " rhs ";";
op add (a : Expression, b : Expression) : Expression => @[prec(10), leftassoc] a " + " b;
op or (a : Expression, b : Expression) : Expression => @[prec(5), leftassoc] a " || " b;
op bitwiseOr (a : Expression, b : Expression) : Expression => @[prec(6), leftassoc] a " | " b;
op intLit (n : Num) : Expression => @[prec(0)] n;

#end

namespace PipeIdent

#strata_gen PipeIdent

end PipeIdent

-- Various special characters in pipe-delimited identifiers
/--
info: program PipeIdent;
result := |special-name| + |name with spaces| + |name@with#special$chars| + |123numeric| + |name-with-émojis-🎉| + regularName;
-/
#guard_msgs in
#eval (#strata
program PipeIdent;
result := |special-name| + |name with spaces| + |name@with#special$chars| + |123numeric| + |name-with-émojis-🎉| + regularName;
#end).format

-- || operator is not confused with pipe-delimited identifiers
/--
info: program PipeIdent;
result := |special-name| || regularName;
-/
#guard_msgs in
#eval (#strata
program PipeIdent;
result := |special-name| || regularName;
#end).format

-- Operator-like identifiers
/--
info: program PipeIdent;
result := |++| + |--| + |**|;
-/
#guard_msgs in
#eval (#strata
program PipeIdent;
result := |++| + |--| + |**|;
#end).format

-- Escape sequences (SMT-LIB 2.6 spec)
/--
info: program PipeIdent;
result := |name\|with\|pipes| + |path\\to\\file|;
-/
#guard_msgs in
#eval (#strata
program PipeIdent;
result := |name\|with\|pipes| + |path\\to\\file|;
#end).format

-- Single | operator coexists with |identifier|
/--
info: program PipeIdent;
result := |x-value| | |y-value| | regularVar;
-/
#guard_msgs in
#eval (#strata
program PipeIdent;
result := |x-value| | |y-value| | regularVar;
#end).format

-- Test that we can construct expressions programmatically
def manualConstruction : PipeIdent.Expression Unit :=
  .add ()
    (.var () ⟨(), "special-name"⟩)
    (.var () ⟨(), "another-name"⟩)

-- Test that the AST structure is correct
example : PipeIdent.Expression Unit := .var () ⟨(), "x-coordinate"⟩
example : PipeIdent.Expression Unit := .var () ⟨(), "name with spaces"⟩
example : PipeIdent.Expression Unit := .var () ⟨(), "123numeric"⟩
