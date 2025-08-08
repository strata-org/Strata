/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
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
info: program B3Lite;
assert true;
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
