/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Std.Data.HashMap.Basic
public import Strata.Languages.Python.Specs.Decls

public section

namespace Strata.Python.Specs

/--
All overloads for a single function name: maps a string literal
argument value to the return type (`PythonIdent`).

N.B. Current limitations: dispatch is always on the first positional argument,
and only string literal values are extracted. -/
@[expose] abbrev FunctionOverloads := Std.HashMap String PythonIdent

/-- Dispatch table: function name → its overloads. -/
@[expose] abbrev OverloadTable := Std.HashMap String FunctionOverloads

end Strata.Python.Specs

end -- public section
