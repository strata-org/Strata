/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

import Strata.DDM.Integration.Lean
---------------------------------------------------------------------

/-! # Getting Started with `ArithPrograms`

## Concrete Syntax Definition using Strata's DDM

Strata's Dialect Definition Mechanism (DDM) offers the ability to define a
dialect's concrete syntax in a declarative fashion, after which we get parsing
and preliminary type checking.
-/

#dialect
dialect ArithPrograms;

// Types
type bool;
type num;

// Literals
fn numLit (n : Num) : num => n;
fn btrue : bool => "true";
fn bfalse : bool => "false";

// Expressions
fn add_expr (a : num, b : num) : num => @[prec(25), leftassoc] a "+" b;
fn mul_expr (a : num, b : num) : num => @[prec(27), leftassoc] a "*" b;
fn eq_expr (tp : Type, a : tp, b : tp) : bool => @[prec(20)] a "==" b;

category Label;
op label (l : Ident) : Label => "[" l "]:";

@[declare(v, tp)]
op init   (v : Ident, tp : Type, e : tp) : Command => "init " v " : " tp " := " e ";\n";
@[declare(v, tp)]
op var    (v : Ident, tp : Type) : Command => "var " v " : " tp";\n";
op assign (v : Ident, e : Expr) : Command => v " := " e ";\n";
op assume (label : Label, c : bool) : Command => "assume " label c ";\n";
op assert (label : Label, c : bool) : Command => "assert " label c ";\n";
op havoc  (v : Ident) : Command => "havoc " v ";\n";

#end

/-- Example: syntax of a program in the `ArithPrograms` dialect -/
private def testEnv :=
#strata
program ArithPrograms;
init x : num := 0;
assert [test]: (x == 0);
#end

---------------------------------------------------------------------

namespace ArithPrograms

/- Automatically generate Lean types from the DDM definitions above. -/

-- set_option trace.Strata.generator true
-- set_option trace.Strata.DDM.syntax true
#strata_gen ArithPrograms
-- #print Command.toAst
-- #print Command.ofAst

end ArithPrograms

---------------------------------------------------------------------
