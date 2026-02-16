/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Python.Specs.ToCore

namespace Strata.Python.Specs.ToCore.Tests

open Strata.Python.Specs

/-! ## Test Infrastructure -/

/-- Default source range for test construction. -/
private def loc : SourceRange := default

/-- Build a SpecType from a single atom. -/
private def mkType (atom : SpecAtomType) : SpecType :=
  SpecType.ofAtom loc atom

/-- Build a SpecType from multiple atoms (union). -/
private def mkUnion (atoms : Array SpecAtomType) : SpecType :=
  { atoms := atoms, loc := loc }

/-- Shorthand for an ident atom with no args. -/
private def identAtom (nm : PythonIdent) : SpecAtomType :=
  .ident nm #[]

/-- Shorthand for an ident SpecType with no args. -/
private def identType (nm : PythonIdent) : SpecType :=
  mkType (identAtom nm)

/-- Shorthand for building an Arg. -/
private def mkArg (name : String) (type : SpecType)
    (hasDefault := false) : Arg :=
  { name, type, hasDefault }

/-- Build a function signature with the given return type. -/
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

private def preludeOut : String := toString Python.corePrelude

/-- Run signaturesToCore and print output beyond the CorePrelude.
    Asserts no errors were produced. -/
private def runTest (sigs : Array Signature) : IO Unit := do
  let (pgm, errors) := signaturesToCore "<test>" sigs
  assert! errors.size = 0
  let out := toString pgm
  assert! preludeOut.isPrefixOf out
  match out.dropPrefix? preludeOut with
  | some rest => IO.print rest
  | none => panic! "Invalid return"

/-- Run signaturesToCore expecting errors. Prints error messages. -/
private def runTestErrors (sigs : Array Signature)
    : IO Unit := do
  let (_, errors) := signaturesToCore "<test>" sigs
  assert! errors.size > 0
  for err in errors do
    IO.println err.message

private def noneAtom := SpecAtomType.noneType

/-! ## Primitive and builtin types as args and return types -/

/--
info: procedure returns_int(x:string)returns(return:int)
;
procedure returns_bool(a:int, b:real)returns(return:bool)
;
procedure returns_real(flag:bool)returns(return:real)
;
procedure with_kwonly(x:int, verbose:bool)returns(return:string)
;
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
    (kwonly := #[mkArg "verbose" (identType .builtinsBool)
                   (hasDefault := true)])
]

/-! ## Complex types (Any, List, Dict, bytes) map to string -/

/--
info: procedure takes_any(x:string)returns(return:int)
;
procedure takes_list(items:string)returns(return:bool)
;
procedure returns_dict()returns(return:string)
;
procedure returns_bytes()returns(return:string)
;
procedure typed_list()returns(return:string)
;
procedure typed_dict()returns(return:string)
;
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
info: procedure int_literal_ret()returns(return:int)
;
procedure str_literal_ret()returns(return:string)
;
procedure typed_dict_ret()returns(return:DictStrAny)
;
procedure str_enum()returns(return:string)
;
-/
#guard_msgs in
#eval runTest #[
  mkFuncSig "int_literal_ret" (mkType (.intLiteral 42)),
  mkFuncSig "str_literal_ret"
    (mkType (.stringLiteral "hello")),
  mkFuncSig "typed_dict_ret"
    (mkType (.typedDict #["f"]
      #[identType .builtinsStr] true)),
  mkFuncSig "str_enum"
    (mkUnion #[.stringLiteral "A", .stringLiteral "B",
               .stringLiteral "C"])
]

/-! ## Optional type patterns (Union[None, T]) -/

/--
info: procedure opt_str()returns(return:StrOrNone)
;
procedure opt_int()returns(return:IntOrNone)
;
procedure opt_bool(x:StrOrNone)returns(return:BoolOrNone)
;
procedure opt_list()returns(return:string)
;
procedure opt_dict()returns(return:string)
;
procedure opt_any()returns(return:string)
;
procedure opt_bytes()returns(return:string)
;
procedure opt_typed_dict()returns(return:DictStrAny)
;
procedure opt_str_enum()returns(return:StrOrNone)
;
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
      .typedDict #["x"] #[identType .builtinsStr] true]),
  mkFuncSig "opt_str_enum"
    (mkUnion #[noneAtom, .stringLiteral "A",
               .stringLiteral "B"])
]

/-! ## Error cases -/

/--
info: Unknown type 'foo.Bar' mapped to string - should generate opaque type declaration
-/
#guard_msgs in
#eval runTestErrors
  #[mkFuncSig "f"
    (identType (PythonIdent.mk "foo" "Bar"))]

/--
info: Empty type (no atoms) encountered in CoreDDM conversion
-/
#guard_msgs in
#eval runTestErrors
  #[mkFuncSig "f" { atoms := #[], loc := loc }]

/--
info: Union type (builtins.str | builtins.int) not yet supported in CoreDDM [atoms: #[builtins.str, builtins.int]]
-/
#guard_msgs in
#eval runTestErrors
  #[mkFuncSig "f"
    (mkUnion #[identAtom .builtinsStr,
               identAtom .builtinsInt])]

/--
info: Union type (None | foo.Bar) not yet supported in CoreDDM [atoms: #[None, foo.Bar]]
-/
#guard_msgs in
#eval runTestErrors
  #[mkFuncSig "f"
    (mkUnion #[noneAtom,
      identAtom (PythonIdent.mk "foo" "Bar")])]

/-! ## Class and type definitions -/

/--
info: procedure my_func(x:int, y:string)returns(return:bool)
;
type MyClass;
procedure MyClass_get_value()returns(return:string)
;
type MyAlias:=string;
-/
#guard_msgs in
#eval runTest #[
  mkFuncSig "my_func" (identType .builtinsBool)
    (args := #[mkArg "x" (identType .builtinsInt),
               mkArg "y" (identType .builtinsStr)
                 (hasDefault := true)]),
  .classDef {
    loc := loc, name := "MyClass"
    methods := #[
      { loc := loc, nameLoc := loc, name := "get_value"
        args := { args := #[], kwonly := #[] }
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

/-! ## Empty input -/

#guard_msgs in
#eval runTest #[]

end Strata.Python.Specs.ToCore.Tests
