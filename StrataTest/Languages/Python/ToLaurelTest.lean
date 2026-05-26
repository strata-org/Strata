/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Python.Specs.ToLaurel
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator

/-! # PySpec → Laurel Translation Tests

Tests for `signaturesToLaurel`: translating PySpec function/class/type
signatures into Laurel programs.
-/

namespace Strata.Python.Specs.ToLaurel.Tests

open Strata.Python.Specs
open Strata.Laurel

/-! ## Test Infrastructure -/

private def assertEq [BEq α] [ToString α] (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw <| .userError s!"expected: {expected}\n  actual: {actual}"

private def loc : SourceRange := default

/-! ### Output Formatting -/

private def fmtHighType : HighType → String
  | .TVoid => "TVoid"
  | .TBool => "TBool"
  | .TInt => "TInt"
  | .TReal => "TReal"
  | .TFloat64 => "TFloat64"
  | .TString => "TString"
  | .THeap => "THeap"
  | .TTypedField _ => "TTypedField"
  | .TSet _ => "TSet"
  | .TMap _ _ => "TMap"
  | .UserDefined name => s!"UserDefined({name})"
  | .Applied _ _ => "Applied"
  | .Pure _ => "Pure"
  | .Intersection _ => "Intersection"
  | .TBv n => s!"TBv({n})"
  | .TCore s => s!"TCore({s})"
  | .Unknown => "Unknown"
  | .MultiValuedExpr _ => "MultiValuedExpr"

private def fmtParam (p : Parameter) : String :=
  s!"{p.name}:{fmtHighType p.type.val}"

private def fmtProc (p : Procedure) : String :=
  let inputs := ", ".intercalate (p.inputs.map fmtParam)
  let returns := ", ".intercalate (p.outputs.map fmtParam)
  if returns.isEmpty then
    s!"procedure {p.name}({inputs})"
  else
    s!"procedure {p.name}({inputs}) returns({returns})"

private def fmtTypeDef : TypeDefinition → String
  | .Composite ty => s!"type {ty.name}"
  | .Constrained ty => s!"constrained {ty.name}"
  | .Datatype ty => s!"datatype {ty.name}"
  | .Alias ty => s!"alias {ty.name}"

/-! ### Test Runners -/

/-- Run signaturesToLaurel and print formatted output.
    Prints warnings (if any) before procedures so `#guard_msgs` can verify them. -/
private def runTest (sigs : Array Signature) (modulePrefix : String := "") : IO Unit := do
  let result := signaturesToLaurel "<test>" sigs modulePrefix
  for err in result.errors do
    IO.println s!"warning: {err.kind.phase}.{err.kind.category}: {err.message}"
  for td in result.program.types do
    IO.println (fmtTypeDef td)
  for proc in result.program.staticProcedures do
    IO.println (fmtProc proc)

/-- Run signaturesToLaurel expecting errors. Print error messages. -/
private def runTestErrors (sigs : Array Signature) (modulePrefix : String := "") : IO Unit := do
  let result := signaturesToLaurel "<test>" sigs modulePrefix
  assert! result.errors.size > 0
  for err in result.errors do
    IO.println err.message

/-- Run signaturesToLaurel and print warning kinds (phase.category: message). -/
private def runTestWarningKinds (sigs : Array Signature) (modulePrefix : String := "") : IO Unit := do
  let result := signaturesToLaurel "<test>" sigs modulePrefix
  assert! result.errors.size > 0
  for err in result.errors do
    IO.println s!"{err.kind.phase}.{err.kind.category}: {err.message}"

/-- Run signaturesToLaurel and print the full result: Laurel output,
    dispatch table, and method registry. Sorts by key for stable output. -/
private def runFullTest (sigs : Array Signature) (modulePrefix : String := "") : IO Unit := do
  let result := signaturesToLaurel "<test>" sigs modulePrefix
  if result.errors.size > 0 then
    IO.println s!"errors: {result.errors.size}"
    for err in result.errors do
      IO.println s!"  {err.message}"
  for td in result.program.types do
    IO.println (fmtTypeDef td)
  for proc in result.program.staticProcedures do
    IO.println (fmtProc proc)
  let overloadEntries := result.overloads.toArray.qsort (·.1 < ·.1)
  for (funcName, fnOverloads) in overloadEntries do
    IO.println s!"dispatch {funcName}:"
    let sorted := fnOverloads.entries.toArray.qsort (·.1 < ·.1)
    for (litVal, retType) in sorted do
      IO.println s!"  \"{litVal}\" -> {retType}"

/-- Run extractOverloads and print the dispatch table. -/
private def runDispatchTest (sigs : Array Signature) : IO Unit := do
  let (overloads, errors) := extractOverloads "<test>" sigs
  if errors.size > 0 then
    IO.println s!"errors: {errors.size}"
    for err in errors do
      IO.println s!"  {err.message}"
  let entries := overloads.toArray.qsort (·.1 < ·.1)
  for (funcName, fnOverloads) in entries do
    IO.println s!"dispatch {funcName}:"
    let sorted := fnOverloads.entries.toArray.qsort (·.1 < ·.1)
    for (litVal, retType) in sorted do
      IO.println s!"  \"{litVal}\" -> {retType}"

/-! ### Signature Builders

Concise helpers for constructing PySpec signatures.
Type shorthands: `str`, `int`, `bool_`, `float_`, `bytes`, `any`, `none_`, `list_`, `dict_`.
-/

private def str := SpecType.ident loc .builtinsStr
private def int := SpecType.ident loc .builtinsInt
private def bool_ := SpecType.ident loc .builtinsBool
private def float_ := SpecType.ident loc .builtinsFloat
private def bytes := SpecType.ident loc .builtinsBytes
private def bytearray := SpecType.ident loc .builtinsBytearray
private def complex_ := SpecType.ident loc .builtinsComplex
private def any := SpecType.ident loc .typingAny
private def none_ := SpecType.noneType loc
private def list_ := SpecType.ident loc .typingList
private def dict_ := SpecType.ident loc .typingDict
private def listOf (t : SpecType) := SpecType.ident loc .typingList #[t]
private def dictOf (k v : SpecType) := SpecType.ident loc .typingDict #[k, v]
private def mkUnion (types : Array SpecType) := SpecType.unionArray loc types
private def pyClass (name : String) := SpecType.ident loc (PythonIdent.mk "" name)
private def externIdent (mod name : String) := PythonIdent.mk mod name

private def arg (name : String) (type : SpecType) (default : Option SpecDefault := none) : Arg :=
  { name, type, default := default }
private def optArg (name : String) (type : SpecType) : Arg :=
  { name, type, default := some .none }

private def func (name : String) (ret : SpecType) (args : Array Arg := #[])
    (kwonly : Array Arg := #[])
    (preconditions : Array Assertion := #[])
    (postconditions : Array SpecExpr := #[])
    (kwargs : Option (String × SpecType) := none) : Signature :=
  .functionDecl {
    loc, nameLoc := loc, name
    args := { args, kwonly, kwargs }
    returnType := ret
    isOverload := false
    preconditions, postconditions
  }

private def overload (name : String) (ret : SpecType) (args : Array Arg := #[]) : Signature :=
  .functionDecl {
    loc, nameLoc := loc, name
    args := { args, kwonly := #[] }
    returnType := ret
    isOverload := true
    preconditions := #[], postconditions := #[]
  }

private def classDef (name : String) (methods : Array FunctionDecl := #[]) : Signature :=
  .classDef { loc, name, methods }

private def method (name : String) (ret : SpecType) (args : Array Arg := #[]) : FunctionDecl :=
  { loc, nameLoc := loc, name
    args := { args := #[arg "self" str] ++ args, kwonly := #[] }
    returnType := ret
    isOverload := false
    preconditions := #[], postconditions := #[] }

private def typeDef (name : String) (definition : SpecType) : Signature :=
  .typeDef { loc, nameLoc := loc, name, definition }

private def externType (name : String) (ident : PythonIdent) : Signature :=
  .externTypeDecl name ident

/-! ## All function params and returns map to Any -/

/--
info: procedure returns_int(x:UserDefined(Any)) returns(result:UserDefined(Any))
procedure returns_bool(a:UserDefined(Any), b:UserDefined(Any)) returns(result:UserDefined(Any))
procedure returns_real(flag:UserDefined(Any)) returns(result:UserDefined(Any))
procedure with_kwonly(x:UserDefined(Any), verbose:UserDefined(Any)) returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  func "returns_int" int (args := #[arg "x" str]),
  func "returns_bool" bool_ (args := #[arg "a" int, arg "b" float_]),
  func "returns_real" float_ (args := #[arg "flag" bool_]),
  func "with_kwonly" str
    (args := #[arg "x" int])
    (kwonly := #[optArg "verbose" bool_])
]

/-! ## Complex types (Any, List, Dict, bytes) -/

/--
info: procedure takes_any(x:UserDefined(Any)) returns(result:UserDefined(Any))
procedure takes_list(items:UserDefined(Any)) returns(result:UserDefined(Any))
procedure returns_dict() returns(result:UserDefined(Any))
procedure typed_list() returns(result:UserDefined(Any))
procedure typed_dict() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  func "takes_any" int (args := #[arg "x" any]),
  func "takes_list" bool_ (args := #[arg "items" list_]),
  func "returns_dict" dict_,
  func "typed_list" (listOf str),
  func "typed_dict" (dictOf str int)
]

/-! ## Literal types, TypedDict, and string-literal unions → Any -/

/--
info: warning: pySpecToLaurel.unsupportedUnion: TypedDict 'TypedDict(f : builtins.str)' approximated as DictStrAny in type 'TypedDict(f : builtins.str)'
procedure int_literal_ret() returns(result:UserDefined(Any))
procedure str_literal_ret() returns(result:UserDefined(Any))
procedure typed_dict_ret() returns(result:UserDefined(Any))
procedure str_enum() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  func "int_literal_ret" (SpecType.intLiteral loc 42),
  func "str_literal_ret" (SpecType.stringLiteral loc "hello"),
  func "typed_dict_ret" (SpecType.typedDict loc #["f"] #[str] #[true]),
  func "str_enum"
    (mkUnion #[SpecType.stringLiteral loc "A", SpecType.stringLiteral loc "B",
               SpecType.stringLiteral loc "C"])
]

/-! ## Optional type patterns (Union[None, T]) → Any -/

/--
info: warning: pySpecToLaurel.unsupportedUnion: TypedDict 'TypedDict(x : builtins.str)' approximated as DictStrAny in type 'Union[_types.NoneType, TypedDict(x : builtins.str)]'
procedure opt_str() returns(result:UserDefined(Any))
procedure opt_int() returns(result:UserDefined(Any))
procedure opt_bool(x:UserDefined(Any)) returns(result:UserDefined(Any))
procedure opt_typed_dict() returns(result:UserDefined(Any))
procedure opt_str_enum() returns(result:UserDefined(Any))
procedure opt_int_enum() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  func "opt_str" (mkUnion #[none_, str]),
  func "opt_int" (mkUnion #[none_, int]),
  func "opt_bool" (mkUnion #[none_, bool_])
    (args := #[arg "x" (mkUnion #[none_, str])]),
  func "opt_typed_dict"
    (mkUnion #[none_, SpecType.typedDict loc #["x"] #[str] #[true]]),
  func "opt_str_enum"
    (mkUnion #[none_, SpecType.stringLiteral loc "A",
               SpecType.stringLiteral loc "B"]),
  func "opt_int_enum"
    (mkUnion #[none_, SpecType.intLiteral loc 1, SpecType.intLiteral loc 2])
]

/-! ## Error cases (updated to verify WarningKind) -/

/--
info: procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f" (SpecType.ident loc (PythonIdent.mk "foo" "Bar"))]

/--
info: procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f" (mkUnion #[str, int])]

/--
info: warning: pySpecToLaurel.unsupportedUnion: No type tester for 'foo.Bar' in type 'Union[_types.NoneType, foo.Bar]'
procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f"
    (mkUnion #[none_, SpecType.ident loc (PythonIdent.mk "foo" "Bar")])]

/-! ## Class and type definitions -/

/--
info: type MyClass
type MyAlias
procedure my_func(x:UserDefined(Any), y:UserDefined(Any)) returns(result:UserDefined(Any))
procedure MyClass@get_value() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  func "my_func" bool_ (args := #[arg "x" int, optArg "y" str]),
  classDef "MyClass" (methods := #[method "get_value" str]),
  typeDef "MyAlias" str
]

/-! ## NoneType and void return -/

/--
info: procedure returns_none() returns(result:UserDefined(Any))
procedure takes_none(x:UserDefined(Any)) returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  func "returns_none" none_,
  func "takes_none" none_ (args := #[arg "x" none_])
]

/-! ## Class types as UserDefined -/

/--
info: type Foo
procedure uses_class(x:UserDefined(Foo)) returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  classDef "Foo",
  func "uses_class" (pyClass "Foo") (args := #[arg "x" (pyClass "Foo")])
]

/-! ## Empty input -/

#guard_msgs in
#eval runTest #[]

/-! ## Overload dispatch and method registry -/

-- A realistic service spec: extern type imports, a factory function with
-- overloads dispatching on string literals, a service class with methods,
-- and a regular function.
/--
info: type SvcClient
procedure SvcClient@do_thing(x:UserDefined(Any)) returns(result:UserDefined(Any))
procedure helper() returns(result:UserDefined(Any))
dispatch create_client:
  "svc_a" -> mod.client.SvcClient
  "svc_b" -> mod.other.OtherClient
-/
#guard_msgs in
#eval runFullTest #[
  externType "SvcClient" (externIdent "mod.client" "SvcClient"),
  externType "OtherClient" (externIdent "mod.other" "OtherClient"),
  overload "create_client"
    (SpecType.ident loc (externIdent "mod.client" "SvcClient"))
    (args := #[arg "name" (SpecType.stringLiteral loc "svc_a")]),
  overload "create_client"
    (SpecType.ident loc (externIdent "mod.other" "OtherClient"))
    (args := #[arg "name" (SpecType.stringLiteral loc "svc_b")]),
  classDef "SvcClient" (methods := #[method "do_thing" int (args := #[arg "x" str])]),
  func "helper" bool_
]

-- Overloads with locally-defined class return types.
/--
info: type Alpha
type Beta
dispatch make:
  "a" -> .Alpha
  "b" -> .Beta
-/
#guard_msgs in
#eval runFullTest #[
  classDef "Alpha",
  classDef "Beta",
  overload "make" (pyClass "Alpha")
    (args := #[arg "kind" (SpecType.stringLiteral loc "a")]),
  overload "make" (pyClass "Beta")
    (args := #[arg "kind" (SpecType.stringLiteral loc "b")])
]

-- extractOverloads only processes externTypeDecl and @overload functions,
-- ignoring class defs, type defs, and regular functions.
/--
info: dispatch factory:
  "x" -> pkg.Foo
-/
#guard_msgs in
#eval runDispatchTest #[
  externType "Foo" (externIdent "pkg" "Foo"),
  overload "factory"
    (SpecType.ident loc (externIdent "pkg" "Foo"))
    (args := #[arg "k" (SpecType.stringLiteral loc "x")]),
  classDef "Ignored",
  func "also_ignored" int,
  typeDef "AlsoIgnored" str
]

-- Overload with no arguments produces an error.
/--
info: errors: 1
  Overloaded function 'bad' has no arguments
-/
#guard_msgs in
#eval runDispatchTest #[
  overload "bad" str
]

-- externTypeDecl produces no errors (regression test).
#guard_msgs in
#eval runFullTest #[externType "Foo" (externIdent "pkg" "Foo")]

/-! ## Nested dict access in preconditions (issue #800) -/

-- Regression test for issue #800: nested dict access `kwargs["Outer"]["Inner"]`
-- should generate `Any_get` (dict lookup), not `FieldSelect`.
/--
info: body contains Any_get: true
body contains FieldSelect: false
-/
#guard_msgs in
#eval do
  let kwargsTy := SpecType.typedDict loc #["Outer"] #[dict_] #[true]
  let result := signaturesToLaurel "<test>" #[
    func "f" str
      (args := #[arg "x" str])
      (kwargs := some ("kwargs", kwargsTy))
      (preconditions := #[{
        message := #[.str "nested dict"]
        formula := .intGe
          (.getIndex (.getIndex (.var "kwargs" loc) "Outer" loc) "Inner" loc)
          (.intLit 0 loc)
          loc
      }])
  ] ""
  assert! result.errors.size = 0
  match result.program.staticProcedures with
  | proc :: _ =>
    let bodyStr := match proc.body with
      | .Transparent body => toString (Strata.Laurel.formatStmtExpr body)
      | .Opaque _ (some body) _ => toString (Strata.Laurel.formatStmtExpr body)
      | _ => ""
    IO.println s!"body contains Any_get: {bodyStr.contains "Any_get"}"
    IO.println s!"body contains FieldSelect: {bodyStr.contains "#"}"
  | [] => IO.println "no procedures"

/-! ## Warning kind tests -/

-- bytes, bytearray, complex now map to Any (matching PythonToLaurel)
/--
info: procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f" bytes]

/--
info: procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f" bytearray]

/--
info: procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f" complex_]

-- Optional patterns now map to Any without warnings
/--
info: procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f" (mkUnion #[none_, float_])]

/--
info: procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f" (mkUnion #[none_, list_])]

/--
info: procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f" (mkUnion #[none_, dict_])]

/--
info: procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f" (mkUnion #[none_, any])]

/--
info: procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f" (mkUnion #[none_, bytes])]

-- Precondition: placeholderExpr
/--
info: pySpecToLaurel.placeholderExpr: Placeholder expression not translatable
-/
#guard_msgs in
#eval runTestWarningKinds
  #[func "f" str
    (preconditions := #[{ message := #[], formula := .placeholder loc }])]

-- Precondition: floatLiteral
/--
info: pySpecToLaurel.floatLiteral: Float literals not yet supported in preconditions
-/
#guard_msgs in
#eval runTestWarningKinds
  #[func "f" str
    (preconditions := #[{ message := #[], formula := .floatLit "3.14" loc }])]

-- Precondition: isinstanceUnsupported
/--
info: pySpecToLaurel.isinstanceUnsupported: isinstance check for 'MyType' not yet supported in preconditions
-/
#guard_msgs in
#eval runTestWarningKinds
  #[func "f" str
    (preconditions := #[{ message := #[], formula := .isInstanceOf (.var "x" loc) "MyType" loc }])]

-- Precondition: forallListUnsupported
/--
info: pySpecToLaurel.forallListUnsupported: forallList quantifier not yet supported in preconditions
-/
#guard_msgs in
#eval runTestWarningKinds
  #[func "f" str
    (preconditions := #[{ message := #[], formula := .forallList (.var "xs" loc) "x" (.var "x" loc) loc }])]

-- Precondition: forallDictUnsupported
/--
info: pySpecToLaurel.forallDictUnsupported: forallDict quantifier not yet supported in preconditions
-/
#guard_msgs in
#eval runTestWarningKinds
  #[func "f" str
    (preconditions := #[{ message := #[], formula := .forallDict (.var "d" loc) "k" "v" (.var "k" loc) loc }])]

-- Declaration: missingMethodSelf
/--
info: pySpecToLaurel.missingMethodSelf: Method 'bad_method' has no arguments (expected 'self' as first parameter)
-/
#guard_msgs in
#eval runTestWarningKinds
  #[.classDef {
    loc := loc, name := "C"
    methods := #[
      { loc := loc, nameLoc := loc, name := "bad_method"
        args := { args := #[], kwonly := #[] }
        returnType := str
        isOverload := false
        preconditions := #[], postconditions := #[] }
    ]
  }]

-- Declaration: kwargsExpansionError
/--
info: pySpecToLaurel.kwargsExpansionError: **kw has non-TypedDict type; kwargs not expanded
-/
#guard_msgs in
#eval runTestWarningKinds
  #[.functionDecl {
    loc := loc, nameLoc := loc, name := "f"
    args := { args := #[], kwonly := #[],
              kwargs := some ("kw", str) }
    returnType := str
    isOverload := false
    preconditions := #[], postconditions := #[]
  }]

-- Declaration: postconditions now translated (no warning)
/--
info: procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f" str
    (postconditions := #[.intGe (.var "result" loc) (.intLit 0 loc) loc])]

-- Overload: overloadNoArgs
/--
info: pySpecToLaurel.overloadNoArgs: Overloaded function 'bad' has no arguments
-/
#guard_msgs in
#eval runTestWarningKinds
  #[overload "bad" str]

-- Overload: union arg type (not a singleton) → overloadArgNotStringLiteral
/--
info: pySpecToLaurel.overloadArgNotStringLiteral: Overloaded function 'bad': first argument type 'Union[Literal["a"], Literal["b"]]' is not a string literal (only string literal dispatch is currently supported)
-/
#guard_msgs in
#eval runTestWarningKinds
  #[overload "bad" str
    (args := #[arg "x" (mkUnion #[SpecType.stringLiteral loc "a", SpecType.stringLiteral loc "b"])])]

-- Overload: overloadArgNotStringLiteral
/--
info: pySpecToLaurel.overloadArgNotStringLiteral: Overloaded function 'bad': first argument type 'builtins.str' is not a string literal (only string literal dispatch is currently supported)
-/
#guard_msgs in
#eval runTestWarningKinds
  #[overload "bad" str
    (args := #[arg "x" str])]

-- Overload: union return type (not a singleton) → overloadReturnNotClass
/--
info: pySpecToLaurel.overloadReturnNotClass: Overloaded function 'bad': return type 'Union[builtins.int, builtins.str]' is not a class type
-/
#guard_msgs in
#eval runTestWarningKinds
  #[overload "bad"
    (mkUnion #[str, int])
    (args := #[arg "x" (SpecType.stringLiteral loc "a")])]

-- Overload: overloadReturnNotClass
/--
info: pySpecToLaurel.overloadReturnNotClass: Overloaded function 'bad': return type 'Literal["hello"]' is not a class type
-/
#guard_msgs in
#eval runTestWarningKinds
  #[overload "bad"
    (SpecType.stringLiteral loc "hello")
    (args := #[arg "x" (SpecType.stringLiteral loc "a")])]

/-! ## Precondition integration tests

End-to-end tests that precondition formulas translate to the expected Laurel
operations.  Each test runs `signaturesToLaurel` with a precondition and
checks that the formatted procedure body contains the correct operation
names (concrete Laurel syntax).  These catch bugs where `TypedStmtExpr`
wrappers emit wrong operations or wrong return types that cause assertions
to be silently dropped. -/

/-- Extract formatted body text from the first procedure in a translation result.
    Returns `none` if there are no procedures or the body is opaque/empty. -/
private def getBody (result : TranslationResult) : Option String :=
  match result.program.staticProcedures with
  | proc :: _ => match proc.body with
    | .Transparent body => some (toString (Strata.Laurel.formatStmtExpr body))
    | .Opaque _ (some body) _ => some (toString (Strata.Laurel.formatStmtExpr body))
    | _ => none
  | [] => none

/-- Translate a single function with preconditions. -/
private def translatePrecondResult (preconditions : Array Assertion)
    (args : Array Arg := #[]) : TranslationResult :=
  signaturesToLaurel "<test>" #[
    .functionDecl {
      loc, nameLoc := loc, name := "f"
      args := { args, kwonly := #[] }
      returnType := str, isOverload := false
      preconditions, postconditions := #[]
    }] ""

/-- Translate a single function with preconditions and return
    `(bodyString, errorCount)`. -/
private def translatePrecond (preconditions : Array Assertion)
    (args : Array Arg := #[]) : String × Nat :=
  let result := translatePrecondResult preconditions args
  (getBody result |>.getD "", result.errors.size)

-- enumMember: or and eq via `|` and `==` infix syntax
#eval do
  let (body, errs) := translatePrecond
    #[{ message := #[], formula :=
          .enumMember (.var "x" loc) #["a", "b"] loc }]
    (args := #[arg "x" str])
  assert! errs == 0
  -- `or` renders as `|`, `eq` as `==`; would have been `<=` before fix #1
  assert! body.contains " | "
  assert! body.contains "=="
  assert! !body.contains "<="

-- implies: `==>` infix syntax
#eval do
  let (body, errs) := translatePrecond
    #[{ message := #[], formula :=
          .implies
            (.intGe (.var "x" loc) (.intLit 0 loc) loc)
            (.intGe (.var "y" loc) (.intLit 0 loc) loc)
            loc }]
    (args := #[arg "x" str, arg "y" str])
  assert! errs == 0
  -- `implies` renders as `==>`; would have been `<=` before fix #1
  assert! body.contains "==>"

-- not via containsKey on kwargs: `!` prefix syntax
#eval do
  let kwargsTy := SpecType.typedDict loc #["key"] #[str] #[false]
  let result := signaturesToLaurel "<test>" #[
    .functionDecl {
      loc := loc, nameLoc := loc, name := "f"
      args := { args := #[], kwonly := #[],
                kwargs := some ("kw", kwargsTy) }
      returnType := str, isOverload := false
      preconditions := #[{
        message := #[], formula :=
          .containsKey (.var "kwargs" loc) "key" loc }]
      postconditions := #[] }] ""
  let body := getBody result |>.getD ""
  assertEq result.errors.size 0
  assert! body.contains "result := <??>"
  assert! body.contains "Any..isfrom_None(key) | Any..isfrom_str(key)"
  assert! body.contains "assert !Any..isfrom_None(key) summary \"precondition 0\""
  assert! body.contains "assume Any..isfrom_str(result)"

-- containsKey on a non-kwargs dict: DictStrAny_contains in an assert
-- (would have been silently dropped before fix #2)
#eval do
  let (body, errs) := translatePrecond
    #[{ message := #[], formula :=
          .containsKey (.var "d" loc) "mykey" loc }]
    (args := #[arg "d" str])
  assert! errs == 0
  assert! body.contains "DictStrAny_contains"


/-! ## typeError warning coverage -/

private def hasTypeError (result : TranslationResult) : Bool :=
  result.errors.any fun e => e.kind == .typeError

-- Unknown identifier triggers typeError
#eval do
  let result := translatePrecondResult
    #[{ message := #[], formula := .var "unknown_name" loc }]
  assert! hasTypeError result

-- Non-Bool precondition formula (intLit returns Any, not Bool) triggers typeError
#eval do
  let result := translatePrecondResult
    #[{ message := #[], formula := .intLit 42 loc }]
  assert! hasTypeError result

/-! ## Body structure tests

Verify the havoc + assert + assume pattern generated by `buildSpecBody`. -/

/-- Translate a function declaration and return `(bodyString, errorCount)`. -/
private def translateFunc (args : Array Arg := #[])
    (returnType : SpecType := str)
    (preconditions : Array Assertion := #[])
    (postconditions : Array SpecExpr := #[]) : String × Nat :=
  let result := signaturesToLaurel "<test>" #[
    .functionDecl {
      loc := loc, nameLoc := loc, name := "f"
      args := { args := args, kwonly := #[] }
      returnType, isOverload := false
      preconditions, postconditions
    }] ""
  (getBody result |>.getD "", result.errors.size)

-- No args, no preconditions: body has havoc + return type assume
#eval do
  let (body, errs) := translateFunc
  assert! errs == 0
  assert! body.contains "result := <??>"
  assert! body.contains "assume Any..isfrom_str(result)"

-- Int arg with no default: type assert (implies not-None, so no separate check)
#eval do
  let (body, errs) := translateFunc
    (args := #[arg "x" int])
  assert! errs == 0
  assert! body.contains "assert Any..isfrom_int(x)"
  assert! !body.contains "isfrom_None"

-- Optional bool arg (has default): type assert uses Or, no required-param assert
#eval do
  let (body, errs) := translateFunc
    (args := #[arg "flag" bool_ (some .none)])
  assert! errs == 0
  assert! body.contains "Any..isfrom_None(flag) | Any..isfrom_bool(flag)"
  assert! !body.contains "'flag' is required"

-- Float return type: assume Any..isfrom_float(result)
#eval do
  let (body, errs) := translateFunc
    (returnType := float_)
  assert! errs == 0
  assert! body.contains "assume Any..isfrom_float(result)"

-- Composite return type: no assume (no tester for user-defined types)
#eval do
  let (body, errs) := translateFunc
    (returnType := SpecType.ident loc (PythonIdent.mk "mod" "Cls"))
  assert! errs == 0
  assert! !body.contains "assume"

-- Postcondition: assume in body
#eval do
  let (body, errs) := translateFunc
    (args := #[arg "x" int])
    (postconditions := #[.intGe (.var "result" loc) (.intLit 0 loc) loc])
  assert! errs == 0
  assert! body.contains "assume"
  assert! body.contains "Any..as_int!"

-- Precondition and postcondition together
#eval do
  let geZero (v : String) : SpecExpr := .intGe (.var v loc) (.intLit 0 loc) loc
  let pre : Assertion := { message := #[.str "n >= 0"], formula := geZero "n" }
  let (body, errs) := translateFunc
    (args := #[arg "n" int])
    (preconditions := #[pre])
    (postconditions := #[geZero "result"])
  assert! errs == 0
  -- type assert for n (implies not-None, so no separate check)
  assert! body.contains "assert Any..isfrom_int(n)"
  assert! !body.contains "isfrom_None(n)"
  -- user precondition
  assert! body.contains "assert" && body.contains "summary \"n >= 0\""
  -- postcondition as assume
  assert! body.contains "assume"
  -- return type assume
  assert! body.contains "assume Any..isfrom_str(result)"

end Strata.Python.Specs.ToLaurel.Tests
