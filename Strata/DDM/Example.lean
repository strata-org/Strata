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
import Strata.DDM.Util.Format

#dialect
dialect B3Lite;

type Pred;
fn btrue : Pred => "true";
fn implies (p : Pred, q : Pred) : Pred => @[prec(20), rightassoc] p " ==> " q;

type Nat;

category Statement;
category Block;

@[declare(v, tp)]
op assign (tp : Type, v : Ident, a : tp) : Statement => "assign" "(" tp:40 ", " v:40 ", " a:40 ")" ";\n";
op if (c : Pred, t : Block, f : Block) : Statement => "if " "(" c:0 ")" t:50 "else " f:50;

op block (c : Seq Statement) : Block => " {\n" indent(2, c:40) "}\n";

category Binding;
@[declare(name, tp)]
op mkBinding (name : Ident, tp : Type) : Binding => @[prec(40)] name ":" tp;

category Bindings;
@[scope(bindings)]
op mkBindings (bindings : CommaSepBy Binding) : Bindings => "(" bindings ")";

op assert (p : Pred) : Command => @[prec(10)] "assert " p ";\n";
op procedure (name : Ident, b : Bindings, @[scope(b)] c : Block) : Command => @[prec(10)] "procedure " name b c;
#end

def b3Env :=
#strata
program B3Lite;
assert true;
assert (true ==> true) ==> true;
assert true ==> (true ==> true);

procedure add (x : Nat, y : Nat, c : Pred) {
  assign(Pred, a, c);
  if (a) {
    assign(Pred, b, a);
    assign(Pred, c, b);
  } else {
    assign(Pred, b, a);
    assign(Pred, c, b);
  }
}
#end

/--
info: assert true;
assert (true ==> true) ==> true;
assert true ==> true ==> true;
procedure add(x:Nat, y:Nat, c:Pred) {
  assign(Pred, a, c);
  if (a) {
    assign(Pred, b, a);
    assign(Pred, c, b);
  }
  else  {
    assign(Pred, b, a);
    assign(Pred, c, b);
  }
}
-/
#guard_msgs in
#eval IO.println b3Env.format.render
