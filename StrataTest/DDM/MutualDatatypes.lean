/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean

/-!
# Tests for mutual datatype blocks in DDM

Tests that mutually recursive datatypes can be declared via forward
declarations and mutual blocks.
-/

#dialect
dialect TestMutual;

metadata declareDatatype (name : Ident, typeParams : Ident, constructors : Ident);

type int;

category Binding;
@[declare(name, tp)]
op mkBinding (name : Ident, tp : TypeP) : Binding => @[prec(40)] name ":" tp;

category Bindings;
@[scope(bindings)]
op mkBindings (bindings : CommaSepBy Binding) : Bindings => "(" bindings ")";

category Constructor;
category ConstructorList;

@[constructor(name, fields)]
op constructor_mk (name : Ident, fields : Option (CommaSepBy Binding)) : Constructor =>
  name "(" fields ")";

@[constructorListAtom(c)]
op constructorListAtom (c : Constructor) : ConstructorList => c;

@[constructorListPush(cl, c)]
op constructorListPush (cl : ConstructorList, c : Constructor) : ConstructorList =>
  cl ", " c;

@[declareTypeForward(name, none)]
op command_forward (name : Ident) : Command =>
  "forward type " name ";\n";

@[declareDatatype(name, typeParams, constructors)]
op command_datatype (name : Ident,
                     typeParams : Option Bindings,
                     @[scopeDatatype(name, typeParams)] constructors : ConstructorList) : Command =>
  "datatype " name typeParams " { " constructors " };\n";

@[scope(commands)]
op command_mutual (commands : SpacePrefixSepBy Command) : Command =>
  "mutual\n" indent(2, commands) "end;\n";

#end

---------------------------------------------------------------------
-- Test 1: Basic mutual recursion (Tree/Forest)
---------------------------------------------------------------------

def mutualBasicPgm :=
#strata
program TestMutual;
forward type Tree;
forward type Forest;
mutual
  datatype Tree { Node(val: int, children: Forest) };
  datatype Forest { FNil(), FCons(head: Tree, tail: Forest) };
end;
#end

/--
info: program TestMutual;
forward type Tree;
forward type Forest;
mutual
   datatype Tree { Node(val:int, children:Forest) };
   datatype Forest { (FNil()), (FCons(head:Tree, tail:Forest)) };
end;
-/
#guard_msgs in
#eval IO.println mutualBasicPgm

---------------------------------------------------------------------
-- Test 2: Single datatype in mutual block (should not actually be used)
---------------------------------------------------------------------

def mutualSinglePgm :=
#strata
program TestMutual;
forward type List;
mutual
  datatype List { Nil(), Cons(head: int, tail: List) };
end;
#end

/--
info: program TestMutual;
forward type List;
mutual
   datatype List { (Nil()), (Cons(head:int, tail:List)) };
end;
-/
#guard_msgs in
#eval IO.println mutualSinglePgm

---------------------------------------------------------------------
-- Test 3: Three-way mutual recursion
---------------------------------------------------------------------

def mutualThreeWayPgm :=
#strata
program TestMutual;
forward type A;
forward type B;
forward type C;
mutual
  datatype A { MkA(toB: B) };
  datatype B { MkB(toC: C) };
  datatype C { MkC(toA: A), CBase() };
end;
#end

/--
info: program TestMutual;
forward type A;
forward type B;
forward type C;
mutual
   datatype A { MkA(toB:B) };
   datatype B { MkB(toC:C) };
   datatype C { (MkC(toA:A)), (CBase()) };
end;
-/
#guard_msgs in
#eval IO.println mutualThreeWayPgm
