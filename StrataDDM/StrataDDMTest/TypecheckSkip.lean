/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean

/-!
# Tests for `dialect_option typecheck off;`

When a dialect sets `dialect_option typecheck off;`, elaboration skips
`inferType` and `unifyTypes` for expression arguments. Implicit type
parameter slots are filled with anonymous type placeholders (`.tvar _ ""`).

This allows programs to elaborate even when the type checker cannot infer
all type arguments — e.g., when a template-generated accessor with tvar
return type is composed with a polymorphic function that needs concrete
type arguments for unification.
-/

---------------------------------------------------------------------
-- Dialect with typecheck ON (default).
-- Includes parameterized types (Lst), polymorphic functions with
-- implicit Type params (lst_select), and perField accessor templates
-- on parameterized datatypes (Maybe).
---------------------------------------------------------------------

#dialect
dialect TestTCOn;

type Boole;
fn equal (tp : Type, a : tp, b : tp) : Boole => @[prec(15)] a " == " b;

type Inte;
fn natToInt (n : Num) : Inte => n;

type Lst (elem : Type);
fn lst_select (A : Type, s : Lst A, i : Inte) : A =>
  "Lst.sel" "(" s ", " i ")";

category Binding;
@[declare(name, tp)]
op mkBinding (name : Ident, tp : TypeP) : Binding =>
  @[prec(40)] name " : " tp;

category Bindings;
@[scope(bindings)]
op mkBindings (bindings : CommaSepBy Binding) : Bindings =>
  " (" bindings ")";

category Constructor;
category ConstructorList;

@[constructor(name, fields)]
op constructor_mk (name : Ident, fields : Option (CommaSepBy Binding)) :
    Constructor => @[prec(50)] name "(" fields ")";

@[constructorListAtom(c)]
op constructorListAtom (c : Constructor) : ConstructorList => "\n  " c;

@[constructorListPush(cl, c)]
op constructorListPush (cl : ConstructorList, c : Constructor)
    : ConstructorList => cl ",\n  " c;

category TypeVar;
@[declareTVar(name)]
op type_var (name : Ident) : TypeVar => name;

category TypeArgs;
@[scope(args)]
op type_args (args : CommaSepBy TypeVar) : TypeArgs => "<" args ">";

category DatatypeDecl;
metadata declareDatatype (name : Ident, typeParams : Ident,
  constructors : Ident, accessorTemplate : FunctionTemplate);

@[declareDatatype(name, typeParams, constructors,
    perField([.datatype, .literal "..", .field],
             [.datatype], .fieldType))]
op datatype_decl (name : Ident,
                  typeParams : Option Bindings,
                  @[scopeTVar(typeParams)] constructors : ConstructorList)
      : DatatypeDecl =>
      "datatype " name typeParams " {" constructors "\n}";

@[scope(datatypes), preRegisterTypes(datatypes)]
op command_datatypes (datatypes : NewlineSepBy DatatypeDecl) : Command =>
  datatypes ";\n";

@[declare(name, r)]
op command_constdecl (name : Ident, r : Type) : Command =>
  "const " name ":" r ";\n";

category Label;
op label (l : Ident) : Label => "[" l "]: ";

category Statement;
category Block;

op assert_stmt (label : Option Label, c : Boole) : Statement =>
  "assert " label c ";\n";

@[scope(c)]
op block (c : SemicolonSepBy Statement) : Block =>
  "{\n  " indent(2, c) "}";

op command_procedure (name : Ident,
                      b : Bindings,
                      @[scope(b)] body : Block) :
  Command =>
  "procedure " name b " returns ()\n" body ";\n";
#end

---------------------------------------------------------------------
-- Same dialect with typecheck OFF.
-- Imports all declarations from TestTCOn but disables type checking.
-- The typecheck flag is a property of the program's primary dialect;
-- imported dialects' flags are not consulted during elaboration.
---------------------------------------------------------------------

#dialect
dialect TestTCOff;
import TestTCOn;
dialect_option typecheck off;
#end

---------------------------------------------------------------------
-- Test 1: Accessor result feeds into polymorphic fn.
--
-- `Maybe..val(m)` returns `tvar "a"` (unresolved) because the
-- accessor template stores its type with tvars. When this flows into
-- `lst_select`, the type checker cannot infer the implicit `A : Type`
-- parameter via unification, producing an error.
--
-- With typecheck off, no unification is attempted — the implicit type
-- param is filled with a skip placeholder and elaboration succeeds.
---------------------------------------------------------------------

/--
error: Could not infer type parameter 2 for TestTCOn.lst_select
---
error: Expression has type Inte when .|| expected.
-/
#guard_msgs in
def typecheckOnFails :=
#strata
program TestTCOn;

datatype Maybe (a : Type) { Nothing(), Just(val: a) };

const m: Maybe (Lst Inte);

procedure Test () returns ()
{
  assert [t1]: Lst.sel(Maybe..val(m), 0) == 0;
};
#end

-- Same program with typecheck off — elaboration succeeds because
-- inferType/unifyTypes are skipped entirely for expression arguments.
def typecheckOffSucceeds :=
#strata
program TestTCOff;

datatype Maybe (a : Type) { Nothing(), Just(val: a) };

const m: Maybe (Lst Inte);

procedure Test () returns ()
{
  assert [t1]: Lst.sel(Maybe..val(m), 0) == 0;
};
#end

---------------------------------------------------------------------
-- Test 2: Unresolved identifiers still fail with typecheck off.
--
-- `typecheck off` only skips type inference/unification — name
-- resolution still operates normally.
---------------------------------------------------------------------

/--
error: Unknown expr identifier undefined_name
-/
#guard_msgs in
def typecheckOffStillCatchesUndefined :=
#strata
program TestTCOff;

procedure Test () returns ()
{
  assert [t1]: undefined_name == 0;
};
#end

---------------------------------------------------------------------
-- Test 3: Invalid dialect_option values produce clean errors.
---------------------------------------------------------------------

/--
error: Expected 'on' or 'off' for option 'typecheck'.
-/
#guard_msgs in
#dialect
dialect BadOptionValue;
dialect_option typecheck maybe;
#end

/--
error: Unknown option 'nonsense'.
-/
#guard_msgs in
#dialect
dialect BadOptionName;
dialect_option nonsense on;
#end
