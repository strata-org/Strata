/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Python.Specs.ToLaurel
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator

namespace Strata.Python.Specs.ToLaurel.Tests

open Strata.Python.Specs
open Strata.Laurel

/-! ## Test Infrastructure -/

private def assertEq [BEq α] [ToString α] (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw <| .userError s!"expected: {expected}\n  actual: {actual}"

private def loc : SourceRange := default

private def identType (nm : PythonIdent) : SpecType :=
  SpecType.ident default nm

private def noneType : SpecType := SpecType.noneType default

private def mkUnion (types : Array SpecType) : SpecType :=
  SpecType.unionArray default types

private def mkArg (name : String) (type : SpecType) (default : Option SpecDefault := none) : Arg :=
  { name, type, default := default }

private def mkFuncSig (name : String) (returnType : SpecType)
    (args : Array Arg := #[]) (kwonly : Array Arg := #[])
    : Signature :=
  .functionDecl {
    loc := loc, nameLoc := loc, name := name
    args := { args := args, kwonly := kwonly }
    returnType := returnType
    isOverload := false
    preconditions := #[], postconditions := #[]
  }

/-! ## Output Formatting -/

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
private def mkFuncSigWithPrecond (name : String) (returnType : SpecType)
    (preconditions : Array Assertion) (args : Array Arg := #[]) : Signature :=
  .functionDecl {
    loc := loc, nameLoc := loc, name := name
    args := { args := args, kwonly := #[] }
    returnType := returnType
    isOverload := false
    preconditions := preconditions, postconditions := #[]
  }

/-- Helper to make a function signature with postconditions. -/
private def mkFuncSigWithPostcond (name : String) (returnType : SpecType)
    (postconditions : Array SpecExpr) : Signature :=
  .functionDecl {
    loc := loc, nameLoc := loc, name := name
    args := { args := #[], kwonly := #[] }
    returnType := returnType
    isOverload := false
    preconditions := #[], postconditions := postconditions
  }


/-! ## All function params and returns map to Any -/

/--
info: procedure returns_int(x:UserDefined(Any)) returns(result:UserDefined(Any))
procedure returns_bool(a:UserDefined(Any), b:UserDefined(Any)) returns(result:UserDefined(Any))
procedure returns_real(flag:UserDefined(Any)) returns(result:UserDefined(Any))
procedure with_kwonly(x:UserDefined(Any), verbose:UserDefined(Any)) returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  mkFuncSig "returns_int" (identType .builtinsInt)
    (args := #[mkArg "x" (identType .builtinsStr)]),
  mkFuncSig "returns_bool" (identType .builtinsBool)
    (args := #[mkArg "a" (identType .builtinsInt),
               mkArg "b" (identType .builtinsFloat)]),
  mkFuncSig "returns_real" (identType .builtinsFloat)
    (args := #[mkArg "flag" (identType .builtinsBool)]),
  mkFuncSig "with_kwonly" (identType .builtinsStr)
    (args := #[mkArg "x" (identType .builtinsInt)])
    (kwonly := #[mkArg "verbose" (identType .builtinsBool) (default := some .none)])
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
  mkFuncSig "takes_any" (identType .builtinsInt)
    (args := #[mkArg "x" (identType .typingAny)]),
  mkFuncSig "takes_list" (identType .builtinsBool)
    (args := #[mkArg "items" (identType .typingList)]),
  mkFuncSig "returns_dict" (identType .typingDict),
  mkFuncSig "typed_list"
    (SpecType.ident loc .typingList #[identType .builtinsStr]),
  mkFuncSig "typed_dict"
    (SpecType.ident loc .typingDict
      #[identType .builtinsStr, identType .builtinsInt])
]

/-! ## Literal types, TypedDict, and string-literal unions → Any -/

/--
info: procedure int_literal_ret() returns(result:UserDefined(Any))
procedure str_literal_ret() returns(result:UserDefined(Any))
procedure typed_dict_ret() returns(result:UserDefined(Any))
procedure str_enum() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  mkFuncSig "int_literal_ret" (SpecType.intLiteral loc 42),
  mkFuncSig "str_literal_ret"
    (SpecType.stringLiteral loc "hello"),
  mkFuncSig "typed_dict_ret"
    (SpecType.typedDict loc #["f"]
      #[identType .builtinsStr] #[true]),
  mkFuncSig "str_enum"
    (mkUnion #[SpecType.stringLiteral loc "A", SpecType.stringLiteral loc "B",
               SpecType.stringLiteral loc "C"])
]

/-! ## Optional type patterns (Union[None, T]) → Any -/

/--
info: procedure opt_str() returns(result:UserDefined(Any))
procedure opt_int() returns(result:UserDefined(Any))
procedure opt_bool(x:UserDefined(Any)) returns(result:UserDefined(Any))
procedure opt_typed_dict() returns(result:UserDefined(Any))
procedure opt_str_enum() returns(result:UserDefined(Any))
procedure opt_int_enum() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  mkFuncSig "opt_str"
    (mkUnion #[noneType, identType .builtinsStr]),
  mkFuncSig "opt_int"
    (mkUnion #[noneType, identType .builtinsInt]),
  mkFuncSig "opt_bool"
    (mkUnion #[noneType, identType .builtinsBool])
    (args := #[mkArg "x"
      (mkUnion #[noneType, identType .builtinsStr])]),
  mkFuncSig "opt_typed_dict"
    (mkUnion #[noneType,
      SpecType.typedDict loc #["x"] #[identType .builtinsStr] #[true]]),
  mkFuncSig "opt_str_enum"
    (mkUnion #[noneType, SpecType.stringLiteral loc "A",
               SpecType.stringLiteral loc "B"]),
  mkFuncSig "opt_int_enum"
    (mkUnion #[noneType, SpecType.intLiteral loc 1, SpecType.intLiteral loc 2])
]

/-! ## Error cases (updated to verify WarningKind) -/

/--
info: procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[mkFuncSig "f"
    (identType (PythonIdent.mk "foo" "Bar"))]
-- Note: Bar maps to Any because the return type always maps to Any

-- Union types now map to Any without warnings
/--
info: procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[mkFuncSig "f"
    (mkUnion #[identType .builtinsStr,
               identType .builtinsInt])]

/--
info: procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[mkFuncSig "f"
    (mkUnion #[noneType,
      identType (PythonIdent.mk "foo" "Bar")])]

/-! ## Class and type definitions -/

/--
info: type MyClass
type MyAlias
procedure my_func(x:UserDefined(Any), y:UserDefined(Any)) returns(result:UserDefined(Any))
procedure MyClass@get_value() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  mkFuncSig "my_func" (identType .builtinsBool)
    (args := #[mkArg "x" (identType .builtinsInt),
               mkArg "y" (identType .builtinsStr) (some .none)]),
  .classDef {
    loc := loc, name := "MyClass"
    methods := #[
      { loc := loc, nameLoc := loc, name := "get_value"
        args := { args := #[mkArg "self" (identType .builtinsStr)], kwonly := #[] }
        returnType := identType .builtinsStr
        isOverload := false
        preconditions := #[]
        postconditions := #[] }
    ]
  },
  .typeDef {
    loc := loc, nameLoc := loc
    name := "MyAlias"
    definition := identType .builtinsStr
  }
]

/-! ## NoneType and void return -/

/--
info: procedure returns_none() returns(result:UserDefined(Any))
procedure takes_none(x:UserDefined(Any)) returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  mkFuncSig "returns_none" noneType,
  mkFuncSig "takes_none" noneType
    (args := #[mkArg "x" noneType])
]

/-! ## Class types as UserDefined -/

/--
info: type Foo
procedure uses_class(x:UserDefined(Foo)) returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  .classDef {
    loc := loc, name := "Foo"
    methods := #[]
  },
  mkFuncSig "uses_class" (identType (PythonIdent.mk "" "Foo"))
    (args := #[mkArg "x" (identType (PythonIdent.mk "" "Foo"))])
]

/-! ## Empty input -/

#guard_msgs in
#eval runTest #[]

/-! ## Overload dispatch and method registry -/

/-- Helper to make an @overload function signature. -/
private def mkOverload (name : String) (returnType : SpecType)
    (args : Array Arg := #[]) : Signature :=
  .functionDecl {
    loc := loc, nameLoc := loc, name := name
    args := { args := args, kwonly := #[] }
    returnType := returnType
    isOverload := true
    preconditions := #[], postconditions := #[]
  }

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
  .externTypeDecl "SvcClient" (PythonIdent.mk "mod.client" "SvcClient"),
  .externTypeDecl "OtherClient" (PythonIdent.mk "mod.other" "OtherClient"),
  mkOverload "create_client"
    (identType (PythonIdent.mk "mod.client" "SvcClient"))
    (args := #[mkArg "name" (SpecType.stringLiteral loc "svc_a")]),
  mkOverload "create_client"
    (identType (PythonIdent.mk "mod.other" "OtherClient"))
    (args := #[mkArg "name" (SpecType.stringLiteral loc "svc_b")]),
  .classDef {
    loc := loc, name := "SvcClient"
    methods := #[
      { loc := loc, nameLoc := loc, name := "do_thing"
        args := { args := #[mkArg "self" (identType .builtinsStr), mkArg "x" (identType .builtinsStr)]
                  kwonly := #[] }
        returnType := identType .builtinsInt
        isOverload := false
        preconditions := #[], postconditions := #[] }
    ]
  },
  mkFuncSig "helper" (identType .builtinsBool)
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
  .classDef { loc := loc, name := "Alpha", methods := #[] },
  .classDef { loc := loc, name := "Beta", methods := #[] },
  mkOverload "make" (identType (PythonIdent.mk "" "Alpha"))
    (args := #[mkArg "kind" (SpecType.stringLiteral loc "a")]),
  mkOverload "make" (identType (PythonIdent.mk "" "Beta"))
    (args := #[mkArg "kind" (SpecType.stringLiteral loc "b")])
]

-- extractOverloads only processes externTypeDecl and @overload functions,
-- ignoring class defs, type defs, and regular functions.
/--
info: dispatch factory:
  "x" -> pkg.Foo
-/
#guard_msgs in
#eval runDispatchTest #[
  .externTypeDecl "Foo" (PythonIdent.mk "pkg" "Foo"),
  mkOverload "factory"
    (identType (PythonIdent.mk "pkg" "Foo"))
    (args := #[mkArg "k" (SpecType.stringLiteral loc "x")]),
  .classDef { loc := loc, name := "Ignored", methods := #[] },
  mkFuncSig "also_ignored" (identType .builtinsInt),
  .typeDef { loc := loc, nameLoc := loc,
             name := "AlsoIgnored",
             definition := identType .builtinsStr }
]

-- Overload with no arguments produces an error.
/--
info: errors: 1
  Overloaded function 'bad' has no arguments
-/
#guard_msgs in
#eval runDispatchTest #[
  mkOverload "bad" (identType .builtinsStr)
]

-- externTypeDecl produces no errors (regression test).
#guard_msgs in
#eval runFullTest #[.externTypeDecl "Foo" (PythonIdent.mk "pkg" "Foo")]

/-! ## Nested dict access in preconditions (issue #800) -/

-- Regression test for issue #800: nested dict access `kwargs["Outer"]["Inner"]`
-- should generate `Any_get` (dict lookup), not `FieldSelect`.
/--
info: body contains Any_get: true
body contains FieldSelect: false
-/
#guard_msgs in
#eval do
  let strTy := identType .builtinsStr
  let dictTy := identType .typingDict
  -- kwargs must be a TypedDict so expandKwargsArgs can expand it
  let kwargsTy := SpecType.typedDict loc #["Outer"] #[dictTy] #[true]
  let result := signaturesToLaurel "<test>" #[
    .functionDecl {
      loc := loc, nameLoc := loc, name := "f"
      args := { args := #[mkArg "x" strTy],
                kwonly := #[], kwargs := some ("kwargs", kwargsTy) }
      returnType := strTy
      isOverload := false
      preconditions := #[{
        message := #[.str "nested dict"]
        formula := .intGe
          (.getIndex (.getIndex (.var "kwargs" loc) "Outer" loc) "Inner" loc)
          (.intLit 0 loc)
          loc
      }]
      postconditions := #[]
    }
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
  #[mkFuncSig "f" (identType .builtinsBytes)]

/--
info: procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[mkFuncSig "f" (identType .builtinsBytearray)]

/--
info: procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[mkFuncSig "f" (identType .builtinsComplex)]

-- Optional patterns now map to Any without warnings
/--
info: procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[mkFuncSig "f" (mkUnion #[noneType, identType .builtinsFloat])]

/--
info: procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[mkFuncSig "f" (mkUnion #[noneType, identType .typingList])]

/--
info: procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[mkFuncSig "f" (mkUnion #[noneType, identType .typingDict])]

/--
info: procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[mkFuncSig "f" (mkUnion #[noneType, identType .typingAny])]

/--
info: procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[mkFuncSig "f" (mkUnion #[noneType, identType .builtinsBytes])]

-- Precondition: placeholderExpr
/--
info: pySpecToLaurel.placeholderExpr: Placeholder expression not translatable
-/
#guard_msgs in
#eval runTestWarningKinds
  #[mkFuncSigWithPrecond "f" (identType .builtinsStr)
    #[{ message := #[], formula := .placeholder loc }]]

-- Precondition: floatLiteral
/--
info: pySpecToLaurel.floatLiteral: Float literals not yet supported in preconditions
-/
#guard_msgs in
#eval runTestWarningKinds
  #[mkFuncSigWithPrecond "f" (identType .builtinsStr)
    #[{ message := #[], formula := .floatLit "3.14" loc }]]

-- Precondition: isinstanceUnsupported
/--
info: pySpecToLaurel.isinstanceUnsupported: isinstance check for 'MyType' not yet supported in preconditions
-/
#guard_msgs in
#eval runTestWarningKinds
  #[mkFuncSigWithPrecond "f" (identType .builtinsStr)
    #[{ message := #[], formula := .isInstanceOf (.var "x" loc) "MyType" loc }]]

-- Precondition: forallListUnsupported
/--
info: pySpecToLaurel.forallListUnsupported: forallList quantifier not yet supported in preconditions
-/
#guard_msgs in
#eval runTestWarningKinds
  #[mkFuncSigWithPrecond "f" (identType .builtinsStr)
    #[{ message := #[], formula := .forallList (.var "xs" loc) "x" (.var "x" loc) loc }]]

-- Precondition: forallDictUnsupported
/--
info: pySpecToLaurel.forallDictUnsupported: forallDict quantifier not yet supported in preconditions
-/
#guard_msgs in
#eval runTestWarningKinds
  #[mkFuncSigWithPrecond "f" (identType .builtinsStr)
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
        returnType := identType .builtinsStr
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
              kwargs := some ("kw", identType .builtinsStr) }
    returnType := identType .builtinsStr
    isOverload := false
    preconditions := #[], postconditions := #[]
  }]

-- Declaration: postconditions now translated (no warning)
/--
info: procedure f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[mkFuncSigWithPostcond "f" (identType .builtinsStr)
    #[.intGe (.var "result" loc) (.intLit 0 loc) loc]]

-- Overload: overloadNoArgs
/--
info: pySpecToLaurel.overloadNoArgs: Overloaded function 'bad' has no arguments
-/
#guard_msgs in
#eval runTestWarningKinds
  #[mkOverload "bad" (identType .builtinsStr)]

-- Overload: union arg type (not a singleton) → overloadArgNotStringLiteral
/--
info: pySpecToLaurel.overloadArgNotStringLiteral: Overloaded function 'bad': first argument type 'Union[Literal["a"], Literal["b"]]' is not a string literal (only string literal dispatch is currently supported)
-/
#guard_msgs in
#eval runTestWarningKinds
  #[mkOverload "bad" (identType .builtinsStr)
    (args := #[mkArg "x" (mkUnion #[SpecType.stringLiteral loc "a", SpecType.stringLiteral loc "b"])])]

-- Overload: overloadArgNotStringLiteral
/--
info: pySpecToLaurel.overloadArgNotStringLiteral: Overloaded function 'bad': first argument type 'builtins.str' is not a string literal (only string literal dispatch is currently supported)
-/
#guard_msgs in
#eval runTestWarningKinds
  #[mkOverload "bad" (identType .builtinsStr)
    (args := #[mkArg "x" (identType .builtinsStr)])]

-- Overload: union return type (not a singleton) → overloadReturnNotClass
/--
info: pySpecToLaurel.overloadReturnNotClass: Overloaded function 'bad': return type 'Union[builtins.int, builtins.str]' is not a class type
-/
#guard_msgs in
#eval runTestWarningKinds
  #[mkOverload "bad"
    (mkUnion #[identType .builtinsStr, identType .builtinsInt])
    (args := #[mkArg "x" (SpecType.stringLiteral loc "a")])]

-- Overload: overloadReturnNotClass
/--
info: pySpecToLaurel.overloadReturnNotClass: Overloaded function 'bad': return type 'Literal["hello"]' is not a class type
-/
#guard_msgs in
#eval runTestWarningKinds
  #[mkOverload "bad"
    (SpecType.stringLiteral loc "hello")
    (args := #[mkArg "x" (SpecType.stringLiteral loc "a")])]

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
  let strTy := identType .builtinsStr
  signaturesToLaurel "<test>" #[
    .functionDecl {
      loc := loc, nameLoc := loc, name := "f"
      args := { args := args, kwonly := #[] }
      returnType := strTy, isOverload := false
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
    (args := #[mkArg "x" (identType .builtinsStr)])
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
    (args := #[mkArg "x" (identType .builtinsStr),
               mkArg "y" (identType .builtinsStr)])
  assert! errs == 0
  -- `implies` renders as `==>`; would have been `<=` before fix #1
  assert! body.contains "==>"

-- not via containsKey on kwargs: `!` prefix syntax
#eval do
  let strTy := identType .builtinsStr
  let kwargsTy := SpecType.typedDict loc #["key"] #[strTy] #[false]
  let result := signaturesToLaurel "<test>" #[
    .functionDecl {
      loc := loc, nameLoc := loc, name := "f"
      args := { args := #[], kwonly := #[],
                kwargs := some ("kw", kwargsTy) }
      returnType := strTy, isOverload := false
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
    (args := #[mkArg "d" (identType .builtinsStr)])
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
    (returnType : SpecType := identType .builtinsStr)
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
    (args := #[mkArg "x" (identType .builtinsInt)])
  assert! errs == 0
  assert! body.contains "assert Any..isfrom_int(x)"
  assert! !body.contains "isfrom_None"

-- Optional bool arg (has default): type assert uses Or, no required-param assert
#eval do
  let (body, errs) := translateFunc
    (args := #[mkArg "flag" (identType .builtinsBool) (some .none)])
  assert! errs == 0
  assert! body.contains "Any..isfrom_None(flag) | Any..isfrom_bool(flag)"
  assert! !body.contains "'flag' is required"

-- Float return type: assume Any..isfrom_float(result)
#eval do
  let (body, errs) := translateFunc
    (returnType := identType .builtinsFloat)
  assert! errs == 0
  assert! body.contains "assume Any..isfrom_float(result)"

-- Composite return type: no assume (no tester for user-defined types)
#eval do
  let (body, errs) := translateFunc
    (returnType := identType (PythonIdent.mk "mod" "Cls"))
  assert! errs == 0
  assert! !body.contains "assume"

-- Postcondition: assume in body
#eval do
  let (body, errs) := translateFunc
    (args := #[mkArg "x" (identType .builtinsInt)])
    (postconditions := #[.intGe (.var "result" loc) (.intLit 0 loc) loc])
  assert! errs == 0
  assert! body.contains "assume"
  assert! body.contains "Any..as_int!"

-- Precondition and postcondition together
#eval do
  let geZero (v : String) : SpecExpr := .intGe (.var v loc) (.intLit 0 loc) loc
  let pre : Assertion := { message := #[.str "n >= 0"], formula := geZero "n" }
  let (body, errs) := translateFunc
    (args := #[mkArg "n" (identType .builtinsInt)])
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
