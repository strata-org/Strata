import Strata.DL.Call.Call
import Strata.DL.HigherOrder.HigherOrder

namespace CallHigherOrder

-- Combined statement type that can handle both Call and HigherOrder operations
inductive CallHigherOrderStatement where
  | callStmt : Call.CallStrataStatement → CallHigherOrderStatement
  | higherOrderStmt : HigherOrder.HigherOrderStrataStatement → CallHigherOrderStatement
  deriving Repr

end CallHigherOrder
