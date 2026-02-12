import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Core.DDMTransform.Parse
import Strata.Languages.Core.Verifier

namespace Strata
namespace Python

def minEx :=
#strata
program Core;

datatype None () {
  None_none()
};

datatype StrOrNone () {
  StrOrNone_mk_str(str_val: string),
  StrOrNone_mk_none(none_val: None)
};

procedure foo(req_param: string, opt_param: StrOrNone) returns ()
spec{
    requires [my_req]: (StrOrNone..isStrOrNone_mk_none(opt_param));
}
{
};

procedure bar() returns ()
spec{
}
{
    call foo("foo", StrOrNone_mk_none(None_none()));
};

#end

-- #eval f!"{minEx}"

#eval TransM.run Inhabited.default (translateProgram minEx)

#eval verify "cvc5" minEx
