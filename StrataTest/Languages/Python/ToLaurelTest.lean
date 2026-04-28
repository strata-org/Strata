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

/-- Run signaturesToLaurel and print formatted output. Asserts no errors. -/
private def runTest (sigs : Array Signature) (modulePrefix : String := "") : IO Unit := do
  let result := signaturesToLaurel "<test>" sigs modulePrefix
  assert! result.errors.size = 0
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

/-- Helper to make a function signature with preconditions. -/
private def funcWithPrecond (name : String) (ret : SpecType)
    (preconditions : Array Assertion) (args : Array Arg := #[]) : Signature :=
  .functionDecl {
    loc, nameLoc := loc, name
    args := { args, kwonly := #[] }
    returnType := ret
    isOverload := false
    preconditions, postconditions := #[]
  }

/-- Helper to make a function signature with postconditions. -/
private def funcWithPostcond (name : String) (ret : SpecType)
    (postconditions : Array SpecExpr) : Signature :=
  .functionDecl {
    loc, nameLoc := loc, name
    args := { args := #[], kwonly := #[] }
    returnType := ret
    isOverload := false
    preconditions := #[], postconditions
  }

/-- Run signaturesToLaurel and print the full result: Laurel output,
    dispatch table, and method registry. -/
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

private def str := SpecType.ofAtom loc (.ident .builtinsStr #[])
private def int := SpecType.ofAtom loc (.ident .builtinsInt #[])
private def bool_ := SpecType.ofAtom loc (.ident .builtinsBool #[])
private def float_ := SpecType.ofAtom loc (.ident .builtinsFloat #[])
private def bytes := SpecType.ofAtom loc (.ident .builtinsBytes #[])
private def bytearray := SpecType.ofAtom loc (.ident .builtinsBytearray #[])
private def complex_ := SpecType.ofAtom loc (.ident .builtinsComplex #[])
private def any := SpecType.ofAtom loc (.ident .typingAny #[])
private def none_ := SpecType.ofAtom loc .noneType
private def list_ := SpecType.ofAtom loc (.ident .typingList #[])
private def dict_ := SpecType.ofAtom loc (.ident .typingDict #[])
private def listOf (t : SpecType) := SpecType.ofAtom loc (.ident .typingList #[t])
private def dictOf (k v : SpecType) := SpecType.ofAtom loc (.ident .typingDict #[k, v])
private def optional (t : SpecAtomType) : SpecType := { atoms := #[.noneType, t], loc }
private def union (atoms : Array SpecAtomType) : SpecType := { atoms, loc }
private def strLit (s : String) := SpecAtomType.stringLiteral s
private def intLit (n : Int) := SpecAtomType.intLiteral n
private def identAtom (id : PythonIdent) := SpecAtomType.ident id #[]
private def noneAtom := SpecAtomType.noneType
private def typedDict (fields : Array String) (types : Array SpecType) (req : Array Bool) :=
  SpecType.ofAtom loc (.typedDict fields types req)
private def pyClass (name : String) := SpecType.ofAtom loc (.ident (PythonIdent.mk "" name) #[])
private def externIdent (mod name : String) := PythonIdent.mk mod name

private def arg (name : String) (type : SpecType) : Arg := { name, type }
private def optArg (name : String) (type : SpecType) : Arg := { name, type, default := some .none }

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

/-! ## Primitive and builtin types as args and return types -/

/--
info: procedure returns_int(x:TString) returns(result:TInt)
procedure returns_bool(a:TInt, b:TReal) returns(result:TBool)
procedure returns_real(flag:TBool) returns(result:TReal)
procedure with_kwonly(x:TInt, verbose:TBool) returns(result:TString)
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
info: procedure takes_any(x:UserDefined(Any)) returns(result:TInt)
procedure takes_list(items:UserDefined(Any)) returns(result:TBool)
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

/-! ## Literal types, TypedDict, and string-literal unions -/

/--
info: procedure int_literal_ret() returns(result:TInt)
procedure str_literal_ret() returns(result:TString)
procedure typed_dict_ret() returns(result:UserDefined(DictStrAny))
procedure str_enum() returns(result:TString)
-/
#guard_msgs in
#eval runTest #[
  func "int_literal_ret" (SpecType.ofAtom loc (intLit 42)),
  func "str_literal_ret" (SpecType.ofAtom loc (strLit "hello")),
  func "typed_dict_ret" (typedDict #["f"] #[str] #[true]),
  func "str_enum" (union #[strLit "A", strLit "B", strLit "C"])
]

/-! ## Optional type patterns (Union[None, T]) -/

/--
info: procedure opt_str() returns(result:UserDefined(StrOrNone))
procedure opt_int() returns(result:UserDefined(IntOrNone))
procedure opt_bool(x:UserDefined(StrOrNone)) returns(result:UserDefined(BoolOrNone))
procedure opt_typed_dict() returns(result:UserDefined(DictStrAny))
procedure opt_str_enum() returns(result:UserDefined(StrOrNone))
procedure opt_int_enum() returns(result:UserDefined(IntOrNone))
-/
#guard_msgs in
#eval runTest #[
  func "opt_str" (optional (.ident .builtinsStr #[])),
  func "opt_int" (optional (.ident .builtinsInt #[])),
  func "opt_bool" (optional (.ident .builtinsBool #[]))
    (args := #[arg "x" (optional (.ident .builtinsStr #[]))]),
  func "opt_typed_dict"
    (union #[.noneType, .typedDict #["x"] #[str] #[true]]),
  func "opt_str_enum" (union #[.noneType, strLit "A", strLit "B"]),
  func "opt_int_enum" (union #[.noneType, intLit 1, intLit 2])
]

/-! ## NoneType and void return -/

/--
info: procedure returns_none() returns(result:UserDefined(Any))
procedure takes_none(x:TVoid) returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  func "returns_none" none_,
  func "takes_none" none_ (args := #[arg "x" none_])
]

/-! ## Class types as UserDefined -/

/--
info: type Foo
procedure uses_class(x:UserDefined(Foo)) returns(result:UserDefined(Foo))
-/
#guard_msgs in
#eval runTest #[
  classDef "Foo",
  func "uses_class" (pyClass "Foo") (args := #[arg "x" (pyClass "Foo")])
]

/-! ## Error cases (updated to verify WarningKind) -/

/--
info: procedure f() returns(result:UserDefined(Bar))
-/
#guard_msgs in
#eval runTest
  #[func "f" (SpecType.ofAtom loc (.ident (PythonIdent.mk "foo" "Bar") #[]))]

/--
info: pySpecToLaurel.emptyType: Empty type (no atoms) encountered in Laurel conversion
-/
#guard_msgs in
#eval runTestWarningKinds
  #[func "f" { atoms := #[], loc }]

/--
info: pySpecToLaurel.unsupportedUnion: Union type (builtins.str | builtins.int) not yet supported in Laurel
-/
#guard_msgs in
#eval runTestWarningKinds
  #[func "f" (union #[.ident .builtinsStr #[], .ident .builtinsInt #[]])]

/--
info: pySpecToLaurel.unsupportedUnion: Union type (None | foo.Bar) not yet supported in Laurel
-/
#guard_msgs in
#eval runTestWarningKinds
  #[func "f" (union #[.noneType, .ident (PythonIdent.mk "foo" "Bar") #[]])]

/-! ## Empty input -/

#guard_msgs in
#eval runTest #[]

/-! ## Class and type definitions -/

/--
info: type MyClass
type MyAlias
procedure my_func(x:TInt, y:TString) returns(result:TBool)
procedure MyClass@get_value() returns(result:TString)
-/
#guard_msgs in
#eval runTest #[
  func "my_func" bool_ (args := #[arg "x" int, optArg "y" str]),
  classDef "MyClass" (methods := #[method "get_value" str]),
  typeDef "MyAlias" str
]

/-! ## Overload dispatch and method registry -/

-- A realistic service spec: extern type imports, a factory function with
-- overloads dispatching on string literals, a service class with methods,
-- and a regular function.
/--
info: type SvcClient
procedure SvcClient@do_thing(x:TString) returns(result:TInt)
procedure helper() returns(result:TBool)
dispatch create_client:
  "svc_a" -> mod.client.SvcClient
  "svc_b" -> mod.other.OtherClient
-/
#guard_msgs in
#eval runFullTest #[
  externType "SvcClient" (externIdent "mod.client" "SvcClient"),
  externType "OtherClient" (externIdent "mod.other" "OtherClient"),
  overload "create_client"
    (SpecType.ofAtom loc (.ident (externIdent "mod.client" "SvcClient") #[]))
    (args := #[arg "name" (SpecType.ofAtom loc (strLit "svc_a"))]),
  overload "create_client"
    (SpecType.ofAtom loc (.ident (externIdent "mod.other" "OtherClient") #[]))
    (args := #[arg "name" (SpecType.ofAtom loc (strLit "svc_b"))]),
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
  overload "make" (pyClass "Alpha") (args := #[arg "kind" (SpecType.ofAtom loc (strLit "a"))]),
  overload "make" (pyClass "Beta") (args := #[arg "kind" (SpecType.ofAtom loc (strLit "b"))])
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
    (SpecType.ofAtom loc (.ident (externIdent "pkg" "Foo") #[]))
    (args := #[arg "k" (SpecType.ofAtom loc (strLit "x"))]),
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
  let kwargsTy := SpecType.ofAtom loc (.typedDict #["Outer"] #[dict_] #[true])
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

-- Unsupported Optional patterns
/--
info: pySpecToLaurel.unsupportedOptionalFloat: Optional[float] mapped to TString
-/
#guard_msgs in
#eval runTestWarningKinds
  #[func "f" (union #[noneAtom, identAtom .builtinsFloat])]

/--
info: pySpecToLaurel.unsupportedOptionalList: Optional[List] mapped to TString
-/
#guard_msgs in
#eval runTestWarningKinds
  #[func "f" (union #[noneAtom, identAtom .typingList])]

/--
info: pySpecToLaurel.unsupportedOptionalDict: Optional[Dict] mapped to TString
-/
#guard_msgs in
#eval runTestWarningKinds
  #[func "f" (union #[noneAtom, identAtom .typingDict])]

/--
info: pySpecToLaurel.unsupportedOptionalAny: Optional[Any] mapped to TString
-/
#guard_msgs in
#eval runTestWarningKinds
  #[func "f" (union #[noneAtom, identAtom .typingAny])]

/--
info: pySpecToLaurel.unsupportedOptionalBytes: Optional[bytes] mapped to TString
-/
#guard_msgs in
#eval runTestWarningKinds
  #[func "f" (union #[noneAtom, identAtom .builtinsBytes])]

-- Precondition: placeholderExpr
/--
info: pySpecToLaurel.placeholderExpr: Placeholder expression not translatable
-/
#guard_msgs in
#eval runTestWarningKinds
  #[funcWithPrecond "f" str
    #[{ message := #[], formula := .placeholder loc }]]

-- Precondition: floatLiteral
/--
info: pySpecToLaurel.floatLiteral: Float literals not yet supported in preconditions
-/
#guard_msgs in
#eval runTestWarningKinds
  #[funcWithPrecond "f" str
    #[{ message := #[], formula := .floatLit "3.14" loc }]]

-- Precondition: isinstanceUnsupported
/--
info: pySpecToLaurel.isinstanceUnsupported: isinstance check for 'MyType' not yet supported in preconditions
-/
#guard_msgs in
#eval runTestWarningKinds
  #[funcWithPrecond "f" str
    #[{ message := #[], formula := .isInstanceOf (.var "x" loc) "MyType" loc }]]

-- Precondition: forallListUnsupported
/--
info: pySpecToLaurel.forallListUnsupported: forallList quantifier not yet supported in preconditions
-/
#guard_msgs in
#eval runTestWarningKinds
  #[funcWithPrecond "f" str
    #[{ message := #[], formula := .forallList (.var "xs" loc) "x" (.var "x" loc) loc }]]

-- Precondition: forallDictUnsupported
/--
info: pySpecToLaurel.forallDictUnsupported: forallDict quantifier not yet supported in preconditions
-/
#guard_msgs in
#eval runTestWarningKinds
  #[funcWithPrecond "f" str
    #[{ message := #[], formula := .forallDict (.var "d" loc) "k" "v" (.var "k" loc) loc }]]

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

-- Declaration: postconditionUnsupported
/--
info: pySpecToLaurel.postconditionUnsupported: Postconditions not yet supported
-/
#guard_msgs in
#eval runTestWarningKinds
  #[funcWithPostcond "f" str
    #[.intGe (.var "result" loc) (.intLit 0 loc) loc]]

-- Overload: overloadNoArgs
/--
info: pySpecToLaurel.overloadNoArgs: Overloaded function 'bad' has no arguments
-/
#guard_msgs in
#eval runTestWarningKinds
  #[overload "bad" str]

-- Overload: overloadArgArity
/--
info: pySpecToLaurel.overloadArgArity: Overloaded function 'bad': first argument has 2 type atoms, expected 1
-/
#guard_msgs in
#eval runTestWarningKinds
  #[overload "bad" str
    (args := #[arg "x" (union #[.stringLiteral "a", .stringLiteral "b"])])]

-- Overload: overloadArgNotStringLiteral
/--
info: pySpecToLaurel.overloadArgNotStringLiteral: Overloaded function 'bad': first argument type 'builtins.str' is not a string literal (only string literal dispatch is currently supported)
-/
#guard_msgs in
#eval runTestWarningKinds
  #[overload "bad" str
    (args := #[arg "x" str])]

-- Overload: overloadReturnArity
/--
info: pySpecToLaurel.overloadReturnArity: Overloaded function 'bad': return type has 2 type atoms, expected 1
-/
#guard_msgs in
#eval runTestWarningKinds
  #[overload "bad"
    (union #[identAtom .builtinsStr, identAtom .builtinsInt])
    (args := #[arg "x" (SpecType.ofAtom loc (strLit "a"))])]

-- Overload: overloadReturnNotClass
/--
info: pySpecToLaurel.overloadReturnNotClass: Overloaded function 'bad': return type 'Literal["hello"]' is not a class type
-/
#guard_msgs in
#eval runTestWarningKinds
  #[overload "bad"
    (SpecType.ofAtom loc (strLit "hello"))
    (args := #[arg "x" (SpecType.ofAtom loc (strLit "a"))])]

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
  let kwargsTy := SpecType.ofAtom loc
    (.typedDict #["key"] #[str] #[false])
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
  assertEq body "{ assert !Any..isfrom_None(key) summary \"precondition 0\" }"

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

end Strata.Python.Specs.ToLaurel.Tests
