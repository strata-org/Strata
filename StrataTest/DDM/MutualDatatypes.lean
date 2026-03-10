/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DDM.Integration.Lean

/-!
# Tests for datatype blocks in DDM

Tests that datatypes (single and mutually recursive) can be declared via
a `command_datatypes` operation using `preRegisterTypes`.
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

category DatatypeDecl;

@[declareDatatype(name, typeParams, constructors,
    perConstructor([.literal "..is", .constructor],
                   [.datatype], .builtin "bool"),
    perField([.datatype, .literal "..", .field], [.datatype], .fieldType))]
op datatype_decl (name : Ident,
                  typeParams : Option Bindings,
                  @[scopeTVar(typeParams)] constructors : ConstructorList) : DatatypeDecl =>
  "datatype " name typeParams " { " constructors " }";

@[scope(datatypes), preRegisterTypes(datatypes)]
op command_datatypes (datatypes : NewlineSepBy DatatypeDecl) : Command =>
  datatypes ";\n";

#end

---------------------------------------------------------------------
-- Test 1: Mutually recursive types
---------------------------------------------------------------------

def mutualVisibleAfterPgm :=
#strata
program TestMutual;
  datatype Tree { Node(val: int, children: Forest) }
  datatype Forest { FNil(), FCons(head: Tree, tail: Forest) };
  datatype Wrapper { MkWrapper(t: Tree, f: Forest) };
#end

/--
info: program TestMutual;
datatype Tree { Node(val:int, children:Forest) }
datatype Forest { FNil(), FCons(head:Tree, tail:Forest) };
datatype Wrapper { MkWrapper(t:Tree, f:Forest) };
-/
#guard_msgs in
#eval IO.println mutualVisibleAfterPgm

---------------------------------------------------------------------
-- Test 2: Single recursive datatype
---------------------------------------------------------------------

def singleRecursivePgm :=
#strata
program TestMutual;
  datatype List { Nil(), Cons(head: int, tail: List) };
#end

/--
info: program TestMutual;
datatype List { Nil(), Cons(head:int, tail:List) };
-/
#guard_msgs in
#eval IO.println singleRecursivePgm

---------------------------------------------------------------------
-- Test 3: Three-way mutual recursion
---------------------------------------------------------------------

def mutualThreeWayPgm :=
#strata
program TestMutual;
  datatype A { MkA(toB: B) }
  datatype B { MkB(toC: C) }
  datatype C { MkC(toA: A), CBase() };
#end

/--
info: program TestMutual;
datatype A { MkA(toB:B) }
datatype B { MkB(toC:C) }
datatype C { MkC(toA:A), CBase() };
-/
#guard_msgs in
#eval IO.println mutualThreeWayPgm

---------------------------------------------------------------------
-- Test 4: Comments and blank lines between mutual types
---------------------------------------------------------------------

def mutualWithCommentsPgm :=
#strata
program TestMutual;
  datatype Tree2 { Leaf(), Branch(left: Tree2, right: Forest2) }

  // a comment between mutual types
  datatype Forest2 { FNil2(), FCons2(head: Tree2, tail: Forest2) };
#end

/--
info: program TestMutual;
datatype Tree2 { Leaf(), Branch(left:Tree2, right:Forest2) }
datatype Forest2 { FNil2(), FCons2(head:Tree2, tail:Forest2) };
-/
#guard_msgs in
#eval IO.println mutualWithCommentsPgm

---------------------------------------------------------------------
-- Test 5: Function templates expand for mutual types
---------------------------------------------------------------------

def mutualTemplatesPgm :=
#strata
program TestMutual;
  datatype Expr { Lit(val: int), Add(lhs: Expr, rhs: Expr),
                  Call(tag: int, args: ExprList) }
  datatype ExprList { ENil(), ECons(head: Expr, tail: ExprList) };
  datatype Program { MkProgram(body: Expr) };
#end

/--
info: program TestMutual;
datatype Expr { Lit(val:int), Add(lhs:Expr, rhs:Expr), Call(tag:int, args:ExprList) }
datatype ExprList { ENil(), ECons(head:Expr, tail:ExprList) };
datatype Program { MkProgram(body:Expr) };
-/
#guard_msgs in
#eval IO.println mutualTemplatesPgm

---------------------------------------------------------------------
-- Negative Tests
---------------------------------------------------------------------

-- Test: Reference to undefined type inside datatype
/-- error: Undeclared type or category Bogus. -/
#guard_msgs in
def undefinedRefPgm :=
#strata
program TestMutual;
  datatype A { MkA(x: Bogus) };
#end

-- Test: Duplicate type name in mutual block
/-- error: Type 'Dup' is already declared. -/
#guard_msgs in
def duplicatePgm :=
#strata
program TestMutual;
  datatype Dup { MkDup1() }
  datatype Dup { MkDup2() };
#end

-- Test: Datatype clashes with previously defined type
/-- error: Type 'Existing' is already declared. -/
#guard_msgs in
def clashPgm :=
#strata
program TestMutual;
  datatype Existing { MkExisting() };
  datatype Existing { MkClash() };
#end

-- Test: Duplicate constructor name across mutual datatypes
/--
error: Mk already defined.
-/
#guard_msgs in
#eval #strata
program TestMutual;
  datatype A { Mk() }
  datatype B { Mk() };
#end
