/-
Python Strata Statement: Python-specific aliases for CallHeap statements
-/

import Strata.DL.CallHeap.CallHeapStrataStatement

---------------------------------------------------------------------

namespace PythonStrata

open CallHeap

-- Python uses the generic CallHeap statements
abbrev PythonStrataStatement := CallHeapStrataStatement
abbrev PythonStrataStatements := CallHeapStrataStatements
abbrev PythonStrataCommand := CallHeapStrataCommand
abbrev PythonStrataExpression := CallHeapStrataExpression

end PythonStrata
