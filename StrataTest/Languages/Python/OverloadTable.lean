module

import Std.Data.HashMap.Basic

/--
All overloads for a single function name: maps a string literal
argument value to the return type (`PythonIdent`).

N.B. Current limitations: dispatch is always on the first positional argument,
and only string literal values are extracted. -/
@[expose] abbrev FunctionOverloads := Std.HashMap String PythonIdent

/-- Dispatch table: function name → its overloads. -/
@[expose] abbrev OverloadTable := Std.HashMap String FunctionOverloads
