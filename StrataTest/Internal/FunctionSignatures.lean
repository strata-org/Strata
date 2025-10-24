
import Strata.Languages.Boogie.Boogie

namespace Strata
namespace Python
namespace Internal

-- We should extract the function signatures from the prelude:
def getFuncSigOrder (fname: String) : List String :=
  panic! s!"Missing function signature : {fname}"

-- We should extract the function signatures from the prelude:
def getFuncSigType (fname: String) (arg: String) : String :=
  panic! s!"Missing function signature : {fname}"

def TypeStrToBoogieExpr (ty: String) : Boogie.Expression.Expr :=
  panic! "unsupported type"

end Internal
end Python
end Strata
