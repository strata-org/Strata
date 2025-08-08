/-
TypeScript Strata Statement: TypeScript-specific aliases for CallHeap statements
-/

import Strata.DL.CallHeap.CallHeapStrataStatement

---------------------------------------------------------------------

namespace TSStrata

open CallHeap

-- TypeScript uses the generic CallHeap statements
abbrev TSStrataStatement := CallHeapStrataStatement
abbrev TSStrataStatements := CallHeapStrataStatements
abbrev TSStrataCommand := CallHeapStrataCommand
abbrev TSStrataExpression := CallHeapStrataExpression

end TSStrata
