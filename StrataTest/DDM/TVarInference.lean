/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DDM.Integration.Lean

/-!
# Regression test: tvar inference through fvar accessors

When a template-generated accessor (perField) on a parameterized datatype is
composed with a polymorphic function that has an implicit Type parameter,
`inferType` must resolve tvars in the accessor's return type so that the
implicit Type parameter can be inferred.

Without the fix, the following sequence panics in `inferType`:

    lst_select( Maybe..val(m), 0 )

because `Maybe..val` returns `tvar "a"` (unresolved), which prevents
`lst_select`'s implicit `A : Type` parameter from being inferred.
-/

-- Dialect with all four essential ingredients:
--   (a) Parameterized built-in type (Lst)
--   (b) Polymorphic fn with implicit Type param (lst_select)
--   (c) perField accessor template (.fieldType return)
--   (d) Parameterized datatype (Maybe)
#dialect
dialect TestTVarInfer;

type Boole;
fn equal (tp : Type, a : tp, b : tp) : Boole => @[prec(15)] a " == " b;

type Inte;
fn natToInt (n : Num) : Inte => n;

type Lst (elem : Type);
fn lst_select (A : Type, s : Lst A, i : Inte) : A =>
  "Lst.sel" "(" s ", " i ")";

fn coerce (A : Type, B : Type, x : A, y : Lst B) : B =>
  "coerce" "(" x ", " y ")";

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
-- Test 1: Accessor result feeds into polymorphic fn (the panic case)
---------------------------------------------------------------------

def tvarInferencePgm :=
#strata
program TestTVarInfer;

datatype Maybe (a : Type) { Nothing(), Just(val: a) };

const m: Maybe (Lst Inte);

procedure Test () returns ()
{
  assert [t1]: Lst.sel(Maybe..val(m), 0) == 0;
};
#end

/--
info: program TestTVarInfer;
datatype Maybe (a : Type) {(
  (Nothing())),
  (Just(val : a))
};
const m:Maybe (Lst Inte);
procedure Test () returns ()
{
  assert [t1]: Lst.sel(Maybe..val(m), 0) == 0;
};
-/
#guard_msgs in
#eval IO.println tvarInferencePgm

---------------------------------------------------------------------
-- Test 2: Accessor alone works (no implicit Type inference needed)
---------------------------------------------------------------------

def accessorOnlyPgm :=
#strata
program TestTVarInfer;

datatype Maybe (a : Type) { Nothing(), Just(val: a) };

const m: Maybe Inte;

procedure Test () returns ()
{
  assert [t1]: Maybe..val(m) == 0;
};
#end

/--
info: program TestTVarInfer;
datatype Maybe (a : Type) {(
  (Nothing())),
  (Just(val : a))
};
const m:Maybe Inte;
procedure Test () returns ()
{
  assert [t1]: Maybe..val(m) == 0;
};
-/
#guard_msgs in
#eval IO.println accessorOnlyPgm

---------------------------------------------------------------------
-- Test 3: Polymorphic fn alone works (no accessor involved)
---------------------------------------------------------------------

def polyFnOnlyPgm :=
#strata
program TestTVarInfer;

datatype Maybe (a : Type) { Nothing(), Just(val: a) };

const s: Lst Inte;

procedure Test () returns ()
{
  assert [t1]: Lst.sel(s, 0) == 0;
};
#end

/--
info: program TestTVarInfer;
datatype Maybe (a : Type) {(
  (Nothing())),
  (Just(val : a))
};
const s:Lst Inte;
procedure Test () returns ()
{
  assert [t1]: Lst.sel(s, 0) == 0;
};
-/
#guard_msgs in
#eval IO.println polyFnOnlyPgm

---------------------------------------------------------------------
-- Test 4: User-defined fn with uncovered result tvar.
-- `coerce` has result type B, but B only appears in param `y : Lst B`.
-- Passing an Inte for `y` causes matchTVars to fail on that param,
-- leaving B unresolved.  The type mismatch is caught by unifyTypes
-- before the bare tvar can trigger a panic in instTypeM.
---------------------------------------------------------------------

/--
error: Encountered Inte expression when Lst bvar!1 expected.
-/
#guard_msgs in
def uncoveredTVarPgm :=
#strata
program TestTVarInfer;

datatype Maybe (a : Type) { Nothing(), Just(val: a) };

const n: Inte;

procedure Test () returns ()
{
  assert [t1]: Lst.sel(coerce(n, n), 0) == 0;
};
#end

---------------------------------------------------------------------
-- Test 5: Multi-parameter datatype — confirms args.reverse handles
-- 2+ type params correctly.  Pair..snd(p) should resolve tvar "b"
-- to Lst Inte (not Inte), so lst_select's A = Lst Inte works.
---------------------------------------------------------------------

def multiParamPgm :=
#strata
program TestTVarInfer;

datatype Pair (a : Type, b : Type) {
  MkPair(fst: a, snd: b)
};

const p: Pair Inte (Lst Inte);

procedure Test () returns ()
{
  assert [t1]: Lst.sel(Pair..snd(p), 0) == 0;
};
#end

/--
info: program TestTVarInfer;
datatype Pair (a : Type, b : Type) {
  (MkPair(fst : a, snd : b))
};
const p:Pair Inte (Lst Inte);
procedure Test () returns ()
{
  assert [t1]: Lst.sel(Pair..snd(p), 0) == 0;
};
-/
#guard_msgs in
#eval IO.println multiParamPgm

---------------------------------------------------------------------
-- Test 6: Chained accessors — Maybe..val(Maybe..val(m)) where
-- m : Maybe (Maybe Inte).  Exercises tvar resolution on an arg
-- whose type is itself the result of tvar resolution.
---------------------------------------------------------------------

def chainedAccessorPgm :=
#strata
program TestTVarInfer;

datatype Maybe (a : Type) { Nothing(), Just(val: a) };

const m: Maybe (Maybe Inte);

procedure Test () returns ()
{
  assert [t1]: Maybe..val(Maybe..val(m)) == 0;
};
#end

/--
info: program TestTVarInfer;
datatype Maybe (a : Type) {(
  (Nothing())),
  (Just(val : a))
};
const m:Maybe (Maybe Inte);
procedure Test () returns ()
{
  assert [t1]: Maybe..val(Maybe..val(m)) == 0;
};
-/
#guard_msgs in
#eval IO.println chainedAccessorPgm

---------------------------------------------------------------------
-- Test 7: Nested parameterized field type — Wrapper(a) with field
-- inner : Lst a.  Exercises substTVars inside an ident type
-- constructor (Lst(tvar "a") → Lst Inte).
---------------------------------------------------------------------

def nestedFieldTypePgm :=
#strata
program TestTVarInfer;

datatype Wrapper (a : Type) {
  MkWrapper(inner: Lst a)
};

const w: Wrapper Inte;

procedure Test () returns ()
{
  assert [t1]: Lst.sel(Wrapper..inner(w), 0) == 0;
};
#end

/--
info: program TestTVarInfer;
datatype Wrapper (a : Type) {
  (MkWrapper(inner : (Lst a)))
};
const w:Wrapper Inte;
procedure Test () returns ()
{
  assert [t1]: Lst.sel(Wrapper..inner(w), 0) == 0;
};
-/
#guard_msgs in
#eval IO.println nestedFieldTypePgm

---------------------------------------------------------------------
-- Test 8: Multi-param, wrong field — Pair..fst(p) returns Inte,
-- not Lst Inte, so feeding into lst_select should fail.
---------------------------------------------------------------------

/--
error: Encountered Inte expression when Lst bvar!0 expected.
-/
#guard_msgs in
def multiParamWrongFieldPgm :=
#strata
program TestTVarInfer;

datatype Pair (a : Type, b : Type) {
  MkPair(fst: a, snd: b)
};

const p: Pair Inte (Lst Inte);

procedure Test () returns ()
{
  assert [t1]: Lst.sel(Pair..fst(p), 0) == 0;
};
#end

