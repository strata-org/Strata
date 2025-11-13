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
  | _ => panic! s!"Missing function signature : {fname}"

-- We should extract the function signatures from the prelude:
def getFuncSigType (fname: String) (arg: String) : String :=
  match fname with
  | "test_helper_procedure" =>
    match arg with
    | "req_name" => "string"
    | "opt_name" => "StrOrNone"
    | _ => panic! s!"Unrecognized arg : {arg}"
  | _ => panic! s!"Missing function signature : {fname}"

def TypeStrToBoogieExpr (ty: String) : Boogie.Expression.Expr :=
  if !ty.endsWith "OrNone" then
    panic! s!"Should only be called for possibly None types. Called for: {ty}"
  else
    match ty with
    | "StrOrNone" => .app (.op "StrOrNone_mk_none" none) (.op "None_none" none)
    | "BoolOrNone" => .app (.op "BoolOrNone_mk_none" none) (.op "None_none" none)
    | "BoolOrStrOrNone" => .app (.op "BoolOrStrOrNone_mk_none" none) (.op "None_none" none)
    | "AnyOrNone" => .app (.op "AnyOrNone_mk_none" none) (.op "None_none" none)
    | "IntOrNone" => .app (.op "IntOrNone_mk_none" none) (.op "None_none" none)
    | "BytesOrStrOrNone" => .app (.op "BytesOrStrOrNone_mk_none" none) (.op "None_none" none)
    | "MappingStrStrOrNone" => .app (.op "MappingStrStrOrNone_mk_none" none) (.op "None_none" none)
    | _ => panic! s!"unsupported type: {ty}"

end Python
end Strata
