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
-- Including «» which tests that Lean's «» notation is properly stripped
/--
info: program PipeIdent;
result := |special-name| + |name with spaces| + |name@with#special$chars| + |123numeric| + |name-with-émojis-🎉| + |name«with»guillemets| + regularName;
-/
#guard_msgs in
#eval (#strata
program PipeIdent;
result := |special-name| + |name with spaces| + |name@with#special$chars| + |123numeric| + |name-with-émojis-🎉| + |name«with»guillemets| + regularName;
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
result := |++| + |--|
  + |**|;
#end).format

-- Escape sequences (SMT-LIB 2.6 spec)
/--
info: program PipeIdent;
result := |name\|with\|pipes| + |path\\to\\file|;
-/
#guard_msgs in
#eval (#strata
program PipeIdent;
result := |name\|with\|pipes| +
  |path\\to\\file|;
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

-- Identifiers with dots don't require pipe delimiters
/--
info: program PipeIdent;
result := qualified.name + another.dotted.identifier + x.y;
-/
#guard_msgs in
#eval (#strata
program PipeIdent;
result := qualified.name + another.dotted.identifier + x.y;
#end).format

-- Identifiers with consecutive dots
/--
info: program PipeIdent;
result := a..b + x...y + trailing..end;
-/
#guard_msgs in
#eval (#strata
program PipeIdent;
result := a..b + x...y + trailing..end;
#end).format

-- Verify escape sequences are unescaped in AST (not just round-trip)
def testEscapeAST := #strata
program PipeIdent;
x := |name\|with\|pipes|;
y := |path\\to\\file|;
#end

-- Extract identifier from var operation in RHS
def getRHSIdent (op : Operation) : String :=
  match op.args[1]! with
  | .op varOp =>
    match varOp.args[0]! with
    | .ident _ s => s
    | _ => ""
  | _ => ""

-- Verify: \| is unescaped to | in AST (stored with Lean's «» notation)
#guard (getRHSIdent testEscapeAST.commands[0]!) == "«name|with|pipes»"

-- Verify: \\ is unescaped to single \ in AST (stored with Lean's «» notation)
#guard (getRHSIdent testEscapeAST.commands[1]!) == "«path\\to\\file»"

-- Verify dots are preserved in AST
def testDotIdent := #strata
program PipeIdent;
x := qualified.name;
y := another.dotted.identifier;
z := a..b;
w := x...y;
v := trailing..end;
#end

-- Verify: dots are preserved in identifier names in AST (stored with Lean's «» notation)
#guard (getRHSIdent testDotIdent.commands[0]!) == "«qualified.name»"
#guard (getRHSIdent testDotIdent.commands[1]!) == "«another.dotted.identifier»"
#guard (getRHSIdent testDotIdent.commands[2]!) == "«a..b»"
#guard (getRHSIdent testDotIdent.commands[3]!) == "«x...y»"
#guard (getRHSIdent testDotIdent.commands[4]!) == "«trailing..end»"

-- Test dialect with | operator that has NO spaces in syntax definition
#dialect
dialect PipeIdentNoSpace;

category Expression;

op var (name : Ident) : Expression => name;
op bitwiseOr (a : Expression, b : Expression) : Expression => @[prec(6), leftassoc] a "|" b;
op exprStmt (e : Expression) : Command => e ";";

#end

-- Edge case: | operator without spaces can create ambiguous output
-- "normalId|pipe" is parsed as normalId followed by unterminated pipe-delimited identifier
/--
error: unterminated pipe-delimited identifier
-/
#guard_msgs in
#eval (#strata
program PipeIdentNoSpace;
normalId|pipe;
#end).format
