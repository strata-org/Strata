/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DDM.Integration.Lean

/-!
# Tests for mutual datatype blocks in DDM

Tests that mutually recursive datatypes can be declared via
pre-registration and mutual blocks.
-/

#dialect
dialect TestMutual;

metadata declareDatatype (name : Ident, typeParams : Ident,
  constructors : Ident, testerTemplate : FunctionTemplate,
  accessorTemplate : FunctionTemplate);

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
  @[prec(30), leftassoc] cl ", " c;

@[declareDatatype(name, typeParams, constructors,
    perConstructor([.literal "..is", .constructor],
                   [.datatype], .builtin "bool"),
    perField([.datatype, .literal "..", .field], [.datatype], .fieldType))]
op command_datatype (name : Ident,
                     typeParams : Option Bindings,
                     @[scopeDatatype(name, typeParams)] constructors : ConstructorList) : Command =>
  "datatype " name typeParams " { " constructors " };\n";

@[scope(commands), preRegisterTypes(commands)]
op command_mutual (commands : SpacePrefixSepBy Command) : Command =>
  "mutual\n" indent(2, commands) "end;\n";

#end

---------------------------------------------------------------------
-- Test 1: Types from mutual block visible after the block
---------------------------------------------------------------------

def mutualVisibleAfterPgm :=
#strata
program TestMutual;
mutual
  datatype Tree { Node(val: int, children: Forest) };
  datatype Forest { FNil(), FCons(head: Tree, tail: Forest) };
end;
datatype Wrapper { MkWrapper(t: Tree, f: Forest) };
#end

/--
info: program TestMutual;
mutual
   datatype Tree { Node(val:int, children:Forest) };
   datatype Forest { FNil(), FCons(head:Tree, tail:Forest) };
end;
datatype Wrapper { MkWrapper(t:Tree, f:Forest) };
-/
#guard_msgs in
#eval IO.println mutualVisibleAfterPgm

---------------------------------------------------------------------
-- Test 2: Single datatype in mutual block (allowed but not common)
---------------------------------------------------------------------

def mutualSinglePgm :=
#strata
program TestMutual;
mutual
  datatype List { Nil(), Cons(head: int, tail: List) };
end;
#end

/--
info: program TestMutual;
mutual
   datatype List { Nil(), Cons(head:int, tail:List) };
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
mutual
  datatype A { MkA(toB: B) };
  datatype B { MkB(toC: C) };
  datatype C { MkC(toA: A), CBase() };
end;
#end

/--
info: program TestMutual;
mutual
   datatype A { MkA(toB:B) };
   datatype B { MkB(toC:C) };
   datatype C { MkC(toA:A), CBase() };
end;
-/
#guard_msgs in
#eval IO.println mutualThreeWayPgm

---------------------------------------------------------------------
-- Test 4: Empty mutual block
---------------------------------------------------------------------

def mutualEmptyPgm :=
#strata
program TestMutual;
mutual
end;
#end

/--
info: program TestMutual;
mutual
end;
-/
#guard_msgs in
#eval IO.println mutualEmptyPgm

---------------------------------------------------------------------
-- Test 5: Function templates expand for mutual types
-- The perConstructor/perField templates on declareDatatype generate
-- tester and accessor functions (e.g., Tree..isNode, Tree..val).
-- This test verifies template expansion succeeds for mutual types
-- with multiple constructors and fields.
---------------------------------------------------------------------

def mutualTemplatesPgm :=
#strata
program TestMutual;
mutual
  datatype Expr { Lit(val: int), Add(lhs: Expr, rhs: Expr),
                  Call(tag: int, args: ExprList) };
  datatype ExprList { ENil(), ECons(head: Expr, tail: ExprList) };
end;
datatype Program { MkProgram(body: Expr) };
#end

/--
info: program TestMutual;
mutual
   datatype Expr { Lit(val:int), Add(lhs:Expr, rhs:Expr), Call(tag:int, args:ExprList) };
   datatype ExprList { ENil(), ECons(head:Expr, tail:ExprList) };
end;
datatype Program { MkProgram(body:Expr) };
-/
#guard_msgs in
#eval IO.println mutualTemplatesPgm

---------------------------------------------------------------------
-- Negative Tests
---------------------------------------------------------------------

-- Test: Reference to undefined type inside mutual block
/-- error: Undeclared type or category Bogus. -/
#guard_msgs in
def mutualUndefinedRefPgm :=
#strata
program TestMutual;
mutual
  datatype A { MkA(x: Bogus) };
end;
#end

-- Test: Duplicate type name in mutual block
/-- error: Type 'Dup' is already declared. -/
#guard_msgs in
def mutualDuplicatePgm :=
#strata
program TestMutual;
mutual
  datatype Dup { MkDup1() };
  datatype Dup { MkDup2() };
end;
#end

-- Test: Mutual type clashes with previously defined type
/-- error: Type 'Existing' is already declared. -/
#guard_msgs in
def mutualClashPgm :=
#strata
program TestMutual;
datatype Existing { MkExisting() };
mutual
  datatype Existing { MkClash() };
end;
#end

-- Test: Duplicate constructor name across mutual datatypes
/--
error: Mk already defined.
-/
#guard_msgs in
#eval #strata
program TestMutual;
mutual
  datatype A { Mk() };
  datatype B { Mk() };
end;
#end
