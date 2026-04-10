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

private def loc : SourceRange := default

private def mkType (atom : SpecAtomType) : SpecType :=
  SpecType.ofAtom default atom

private def mkUnion (atoms : Array SpecAtomType) : SpecType :=
  { atoms := atoms, loc := default }

private def identAtom (nm : PythonIdent) : SpecAtomType :=
  .ident nm #[]

private def identType (nm : PythonIdent) : SpecType :=
  mkType (identAtom nm)

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
  | .TCore s => s!"TCore({s})"
  | HighType.Unknown => "Unknown"

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

private def noneAtom := SpecAtomType.noneType

/-! ## Primitive and builtin types as args and return types -/

/--
info: procedure returns_int(x:TString) returns(result:TInt)
procedure returns_bool(a:TInt, b:TReal) returns(result:TBool)
procedure returns_real(flag:TBool) returns(result:TReal)
procedure with_kwonly(x:TInt, verbose:TBool) returns(result:TString)
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
info: procedure takes_any(x:UserDefined(Any)) returns(result:TInt)
procedure takes_list(items:UserDefined(ListStr)) returns(result:TBool)
procedure returns_dict() returns(result:UserDefined(DictStrAny))
procedure returns_bytes() returns(result:TString)
procedure typed_list() returns(result:UserDefined(ListStr))
procedure typed_dict() returns(result:UserDefined(DictStrAny))
-/
#guard_msgs in
#eval runTest #[
  mkFuncSig "takes_any" (identType .builtinsInt)
    (args := #[mkArg "x" (identType .typingAny)]),
  mkFuncSig "takes_list" (identType .builtinsBool)
    (args := #[mkArg "items" (identType .typingList)]),
  mkFuncSig "returns_dict" (identType .typingDict),
  mkFuncSig "returns_bytes" (identType .builtinsBytes),
  mkFuncSig "typed_list"
    (mkType (.ident .typingList #[identType .builtinsStr])),
  mkFuncSig "typed_dict"
    (mkType (.ident .typingDict
      #[identType .builtinsStr, identType .builtinsInt]))
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
  mkFuncSig "int_literal_ret" (mkType (.intLiteral 42)),
  mkFuncSig "str_literal_ret"
    (mkType (.stringLiteral "hello")),
  mkFuncSig "typed_dict_ret"
    (mkType (.typedDict #["f"]
      #[identType .builtinsStr] #[true])),
  mkFuncSig "str_enum"
    (mkUnion #[.stringLiteral "A", .stringLiteral "B",
               .stringLiteral "C"])
]

/-! ## Optional type patterns (Union[None, T]) -/

/--
info: procedure opt_str() returns(result:UserDefined(StrOrNone))
procedure opt_int() returns(result:UserDefined(IntOrNone))
procedure opt_bool(x:UserDefined(StrOrNone)) returns(result:UserDefined(BoolOrNone))
procedure opt_float() returns(result:TString)
procedure opt_list() returns(result:TString)
procedure opt_dict() returns(result:TString)
procedure opt_any() returns(result:TString)
procedure opt_bytes() returns(result:TString)
procedure opt_typed_dict() returns(result:UserDefined(DictStrAny))
procedure opt_str_enum() returns(result:UserDefined(StrOrNone))
procedure opt_int_enum() returns(result:UserDefined(IntOrNone))
-/
#guard_msgs in
#eval runTest #[
  mkFuncSig "opt_str"
    (mkUnion #[noneAtom, identAtom .builtinsStr]),
  mkFuncSig "opt_int"
    (mkUnion #[noneAtom, identAtom .builtinsInt]),
  mkFuncSig "opt_bool"
    (mkUnion #[noneAtom, identAtom .builtinsBool])
    (args := #[mkArg "x"
      (mkUnion #[noneAtom, identAtom .builtinsStr])]),
  mkFuncSig "opt_float"
    (mkUnion #[noneAtom, identAtom .builtinsFloat]),
  mkFuncSig "opt_list"
    (mkUnion #[noneAtom, identAtom .typingList]),
  mkFuncSig "opt_dict"
    (mkUnion #[noneAtom, identAtom .typingDict]),
  mkFuncSig "opt_any"
    (mkUnion #[noneAtom, identAtom .typingAny]),
  mkFuncSig "opt_bytes"
    (mkUnion #[noneAtom, identAtom .builtinsBytes]),
  mkFuncSig "opt_typed_dict"
    (mkUnion #[noneAtom,
      .typedDict #["x"] #[identType .builtinsStr] #[true]]),
  mkFuncSig "opt_str_enum"
    (mkUnion #[noneAtom, .stringLiteral "A",
               .stringLiteral "B"]),
  mkFuncSig "opt_int_enum"
    (mkUnion #[noneAtom, .intLiteral 1, .intLiteral 2])
]

/-! ## Error cases -/

/--
info: Unknown type 'foo.Bar' mapped to TString
-/
#guard_msgs in
#eval runTestErrors
  #[mkFuncSig "f"
    (identType (PythonIdent.mk "foo" "Bar"))]

/--
info: Empty type (no atoms) encountered in Laurel conversion
-/
#guard_msgs in
#eval runTestErrors
  #[mkFuncSig "f" { atoms := #[], loc := default }]

/--
info: Union type (builtins.str | builtins.int) not yet supported in Laurel
-/
#guard_msgs in
#eval runTestErrors
  #[mkFuncSig "f"
    (mkUnion #[identAtom .builtinsStr,
               identAtom .builtinsInt])]

/--
info: Union type (None | foo.Bar) not yet supported in Laurel
-/
#guard_msgs in
#eval runTestErrors
  #[mkFuncSig "f"
    (mkUnion #[noneAtom,
      identAtom (PythonIdent.mk "foo" "Bar")])]

/-! ## Class and type definitions -/

/--
info: type MyClass
type MyAlias
procedure my_func(x:TInt, y:TString) returns(result:TBool)
procedure MyClass@get_value() returns(result:TString)
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
procedure takes_none(x:TVoid) returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  mkFuncSig "returns_none" (mkType .noneType),
  mkFuncSig "takes_none" (identType .noneType)
    (args := #[mkArg "x" (mkType .noneType)])
]

/-! ## Class types as UserDefined -/

/--
info: type Foo
procedure uses_class(x:UserDefined(Foo)) returns(result:UserDefined(Foo))
-/
#guard_msgs in
#eval runTest #[
  .classDef {
    loc := loc, name := "Foo"
    methods := #[]
  },
  mkFuncSig "uses_class" (.pyClass loc "Foo" #[])
    (args := #[mkArg "x" (.pyClass loc "Foo" #[])])
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
    let sorted := fnOverloads.toArray.qsort (·.1 < ·.1)
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
    let sorted := fnOverloads.toArray.qsort (·.1 < ·.1)
    for (litVal, retType) in sorted do
      IO.println s!"  \"{litVal}\" -> {retType}"

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
  .externTypeDecl "SvcClient" (PythonIdent.mk "mod.client" "SvcClient"),
  .externTypeDecl "OtherClient" (PythonIdent.mk "mod.other" "OtherClient"),
  mkOverload "create_client"
    (mkType (.ident (PythonIdent.mk "mod.client" "SvcClient") #[]))
    (args := #[mkArg "name" (mkType (.stringLiteral "svc_a"))]),
  mkOverload "create_client"
    (mkType (.ident (PythonIdent.mk "mod.other" "OtherClient") #[]))
    (args := #[mkArg "name" (mkType (.stringLiteral "svc_b"))]),
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

-- Overloads with locally-defined class return types (.pyClass).
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
  mkOverload "make" (.pyClass loc "Alpha" #[])
    (args := #[mkArg "kind" (mkType (.stringLiteral "a"))]),
  mkOverload "make" (.pyClass loc "Beta" #[])
    (args := #[mkArg "kind" (mkType (.stringLiteral "b"))])
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
    (mkType (.ident (PythonIdent.mk "pkg" "Foo") #[]))
    (args := #[mkArg "k" (mkType (.stringLiteral "x"))]),
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
  let kwargsTy := SpecType.ofAtom loc (.typedDict #["Outer"] #[dictTy] #[true])
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

end Strata.Python.Specs.ToLaurel.Tests
