/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Boogie

namespace Strata
namespace Python

inductive PyType where
| AnyOrNone
| BoolOrNone
| BoolOrStrOrNone
| BytesOrStrOrNone
| DictStrAny
| IntOrNone
| ListStr
| MappingStrStrOrNone
| StrOrNone
| Str
deriving Inhabited

namespace PyType

def toString (atp : PyType) : String :=
  match atp with
  | AnyOrNone => "AnyOrNone"
  | BoolOrNone => "BoolOrNone"
  | BoolOrStrOrNone => "BoolOrStrOrNone"
  | BytesOrStrOrNone => "BytesOrStrOrNone"
  | DictStrAny => "DictStrAny"
  | IntOrNone => "IntOrNone"
  | ListStr => "ListStr"
  | MappingStrStrOrNone => "MappingStrStrOrNone"
  | StrOrNone => "StrOrNone"
  | Str => "string"

def allowNone (atp : PyType) : Bool :=
  match atp with
  | Str => False
  | _ => True

end PyType

def TypeStrToBoogieExpr (ty: String) : Boogie.Expression.Expr :=
  if !ty.endsWith "OrNone" then
    panic! s!"Should only be called for possibly None types. Called for: {ty}"
  else
    match ty with
    | "StrOrNone" => .app () (.op () "StrOrNone_mk_none" none) (.op () "None_none" none)
    | "BoolOrNone" => .app () (.op () "BoolOrNone_mk_none" none) (.op () "None_none" none)
    | "BoolOrStrOrNone" => .app () (.op () "BoolOrStrOrNone_mk_none" none) (.op () "None_none" none)
    | "AnyOrNone" => .app () (.op () "AnyOrNone_mk_none" none) (.op () "None_none" none)
    | "IntOrNone" => .app () (.op () "IntOrNone_mk_none" none) (.op () "None_none" none)
    | "BytesOrStrOrNone" => .app () (.op () "BytesOrStrOrNone_mk_none" none) (.op () "None_none" none)
    | "MappingStrStrOrNone" => .app () (.op () "MappingStrStrOrNone_mk_none" none) (.op () "None_none" none)
    | _ => panic! s!"unsupported type: {ty}"


structure FuncSignature where
  args : Array (String × PyType)
  required_arg_count : Nat := args.size
  indexMap : Std.HashMap String Nat
deriving Inhabited

namespace FuncSignature

def ofArray (args : Array (String × PyType)) : FuncSignature where
  args := args
  indexMap := args.foldl (init := {}) fun m (name, _) => m.insert name m.size

end FuncSignature

/--
Global database of function signatures
-/
structure FuncSigDB where
  -- TODO: Migrate from a map from String to a map that incorporates Python module
  -- information.
  map : Std.HashMap String FuncSignature := {}
deriving Inhabited

namespace FuncSigDB

instance : GetElem? FuncSigDB String FuncSignature (fun db name => name ∈ db.map) where
  getElem db nm p := db.map[nm]'p
  getElem? db nm := db.map[nm]?
  getElem! db nm := db.map[nm]!

def add! (db : FuncSigDB) (name : String) (args : List (String × PyType)) :=
    assert! name ∉ db.map
    { db with map := db.map.insert name (.ofArray args.toArray) }

end FuncSigDB

def funcSigs (db : FuncSigDB := {}) : FuncSigDB := Prod.snd <| Id.run <| StateT.run (s := db) do
  let arg (name : String) (tp : PyType) : String × PyType := (name, tp)
  let add name args := modify (·.add! name args)
  add "input" [
    arg "msg" .Str,
  ]
  add "json_dumps" [
    arg "msg" .DictStrAny,
    arg "opt_indent" .IntOrNone,
  ]
  add "json_loads" [
    arg "msg" .Str
  ]
  add "print" [
    arg "msg" .Str,
    arg "opt" .StrOrNone,
  ]
  add "random_choice" [
    arg "l" .ListStr
  ]
  add "test_helper_procedure" [
    arg "req_name" .Str,
    arg "opt_name" .StrOrNone,
  ]

end Python
end Strata
