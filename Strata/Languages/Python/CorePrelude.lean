/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Core.DDMTransform.Parse
import Strata.Languages.Core.Verifier

namespace Strata
namespace Python

def corePrelude :=
#strata
program Core;
datatype None () {
  None_none()
};

datatype StrOrNone () {
  StrOrNone_mk_str(str_val: string),
  StrOrNone_mk_none(none_val: None)
};

datatype ExceptOrNone () {
  ExceptOrNone_mk_code(code_val: string),
  ExceptOrNone_mk_none(none_val: None)
};

datatype Client () {
  Client_S3(),
  Client_CW()
};

type DictStrAny;
function DictStrAny_mk(s : string) : (DictStrAny);

procedure test_helper_procedure(req_name : string, opt_name : StrOrNone) returns (maybe_except: ExceptOrNone)
spec {
  //requires [req_opt_name_none_or_str]: (if (!StrOrNone..isStrOrNone_mk_none(opt_name)) then (StrOrNone..isStrOrNone_mk_str(opt_name)) else true);
  requires [req_false]: (StrOrNone..isStrOrNone_mk_none(opt_name));
}
{
};

#end

def Core.prelude : Core.Program :=
   Core.getProgram corePrelude |>.fst

end Python
end Strata
