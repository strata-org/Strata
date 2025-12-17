/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Boogie

namespace Strata
namespace Python

-- We should extract the function signatures from the prelude:
def getFuncSigOrder (fname: String) : List String :=
  match fname with
  | "test_helper_procedure" => ["req_name", "opt_name"]
  | "print" => ["msg", "opt"]
  | "json_dumps" => ["msg", "opt_indent"]
  | "json_loads" => ["msg"]
  | "input" => ["msg"]
  | "random_choice" => ["l"]
  | "datetime_now" => []
  | "datetime_utcnow" => []
  | "datetime_date" => ["dt"]
  | "timedelta" => ["days", "hours"]
  | "datetime_strptime" => ["time", "format"]
  | "str_to_float" => ["s"]
  | _ => panic! s!"Missing function signature : {fname}"

-- We should extract the function signatures from the prelude:
def getFuncSigType (fname: String) (arg: String) : String :=
  match fname with
  | "test_helper_procedure" =>
    match arg with
    | "req_name" => "string"
    | "opt_name" => "StrOrNone"
    | _ => panic! s!"Unrecognized arg : {arg}"
  | "print" =>
    match arg with
    | "msg" => "string"
    | "opt" => "StrOrNone"
    | _ => panic! s!"Unrecognized arg : {arg}"
  | "json_dumps" =>
    match arg with
    | "msg" => "DictStrAny"
    | "opt_indent" => "IntOrNone"
    | _ => panic! s!"Unrecognized arg : {arg}"
  | "json_loads" =>
    match arg with
    | "msg" => "string"
    | _ => panic! s!"Unrecognized arg : {arg}"
  | "input" =>
    match arg with
    | "msg" => "string"
    | _ => panic! s!"Unrecognized arg : {arg}"
  | "random_choice" =>
    match arg with
    | "l" => "ListStr"
    | _ => panic! s!"Unrecognized arg : {arg}"
  | "datetime_now" =>
    match arg with
    | _ => panic! s!"Unrecognized arg : {arg}"
  | "datetime_utcnow" =>
    match arg with
    | _ => panic! s!"Unrecognized arg : {arg}"
  | "datetime_date" =>
    match arg with
    | "dt" => "Datetime"
    | _ => panic! s!"Unrecognized arg : {arg}"
  | "timedelta" =>
    match arg with
    | "days" => "IntOrNone"
    | "hours" => "IntOrNone"
    | _ => panic! s!"Unrecognized arg : {arg}"
  | "datetime_strptime" =>
    match arg with
    | "time" => "string"
    | "format" => "string"
    | _ => panic! s!"Unrecognized arg : {arg}"
  | "str_to_float" =>
    match arg with
    | "s" => "string"
    | _ => panic! s!"Unrecognized arg : {arg}"
  | _ => panic! s!"Missing function signature : {fname}"

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
    | "DictStrStrOrNone" => .app () (.op () "DictStrStrOrNone_mk_none" none) (.op () "None_none" none)
    | _ => panic! s!"unsupported type: {ty}"

end Python
end Strata
