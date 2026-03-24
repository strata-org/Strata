/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Std.Data.HashMap.Basic

public section

namespace Strata.Python

/--
A fully-qualified Python identifier consisting of a module path and a name.
For example, `typing.List` has module "typing" and name "List".
-/
structure PythonIdent where
  pythonModule : String
  name : String
  deriving DecidableEq, Hashable, Inhabited, Ord, Repr

namespace PythonIdent

protected def ofString (s : String) : Option PythonIdent :=
  match s.revFind? '.' with
  | none => none
  | some idx =>
    some {
      pythonModule := s.extract s.startPos idx
      name := s.extract idx.next! s.endPos
    }

instance : ToString PythonIdent where
  toString i := s!"{i.pythonModule}.{i.name}"

end PythonIdent

/--
All overloads for a single function name: maps a string literal
argument value to the return type (`PythonIdent`).

N.B. Current limitations: dispatch is always on the first positional argument,
and only string literal values are extracted. -/
@[expose] abbrev FunctionOverloads := Std.HashMap String PythonIdent

/-- Dispatch table: function name → its overloads. -/
@[expose] abbrev OverloadTable := Std.HashMap String FunctionOverloads

end Strata.Python

end -- public section
