/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.B3.DDMFormatTests

namespace B3

open Std (Format)
open Strata
open Strata.B3CST

-- Helper to extract declaration from a program and reformat it
def reformatDecl (p : Program) : Format :=
  match p.commands.toList with
  | [op] =>
    if op.name.name == "command_decl" then
      match op.args.toList with
      | [ArgF.op decl] =>
        let ctx := p.formatContext {}
        let state := p.formatState
        cformat (ArgF.op decl) ctx state
      | _ => "Error: expected decl op"
    else s!"Error: expected command_decl, got {op.name.name}"
  | _ => "Error: expected single command"

section DeclarationFormatTests

-- Type declarations
/--
info: type MyType
-/
#guard_msgs in
#eval reformatDecl $ #strata program B3CST; type MyType #end

-- Tagger declarations
/--
info: tagger MyTagger for MyType
-/
#guard_msgs in
#eval reformatDecl $ #strata program B3CST; tagger MyTagger for MyType #end

-- Simple axiom declarations
/--
info: axiom x > 0
-/
#guard_msgs in
#eval reformatDecl $ #strata program B3CST; axiom x > 0 #end

/--
info: axiom forall i : int i >= 0
-/
#guard_msgs in
#eval reformatDecl $ #strata program B3CST; axiom forall i : int i >= 0 #end

-- Axiom with explains clause
/--
info: axiom explains MyFunc,
  x > 0
-/
#guard_msgs in
#eval reformatDecl $ #strata program B3CST; axiom explains MyFunc, x > 0 #end

-- Function declarations
/--
info: function Double(x : int) : int {
  x + x
}
-/
#guard_msgs in
#eval reformatDecl $ #strata program B3CST; function Double(x : int) : int { x + x } #end

/--
info: function Add(x : int, y : int) : int {
  x + y
}
-/
#guard_msgs in
#eval reformatDecl $ #strata program B3CST; function Add(x : int, y : int) : int { x + y } #end

/--
info: function IsPositive(x : int) : bool {
  x > 0
}
-/
#guard_msgs in
#eval reformatDecl $ #strata program B3CST; function IsPositive(x : int) : bool { x > 0 } #end

-- Function with injective parameter
/--
info: function MapCoordinate(injective x : int, injective y : int, label : int) : int {
  x + y
}
-/
#guard_msgs in
#eval reformatDecl $ #strata program B3CST; function MapCoordinate(injective x : int, injective y : int, label : int) : int { x + y } #end

-- Procedure declarations
/--
info: procedure Increment(inout x : int)
  requires x >= 0
  ensures x > 0 {
  x := x + 1
}
-/
#guard_msgs in
#eval reformatDecl $ #strata program B3CST; procedure Increment(inout x : int) requires x >= 0 ensures x > 0 { x := x + 1 } #end

/--
info: procedure Swap(inout x : int, inout y : int) {
  var temp : int := x
  x := y
  y := temp
}
-/
#guard_msgs in
#eval reformatDecl $ #strata program B3CST; procedure Swap(inout x : int, inout y : int) { var temp : int := x x := y y := temp } #end

/--
info: procedure GetValue(out result : int)
  ensures result == 42 {
  result := 42
}
-/
#guard_msgs in
#eval reformatDecl $ #strata program B3CST; procedure GetValue(out result : int) ensures result == 42 { result := 42 } #end

end DeclarationFormatTests

end B3
