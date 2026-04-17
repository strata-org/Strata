/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DDM.Util.Format

open Std

namespace Strata.Format.Tests

/-- A `nest` block whose content ends with a newline, followed by a sibling.
    Lean's `.pretty` would indent the closing brace at the *inner* level;
    `Strata.renderFormat` correctly reverts to the outer level. -/
private def nestThenSibling : Std.Format :=
  .append (.nest 2 (.text "var x : int;\n")) (.text "}")

-- `.pretty` incorrectly indents `}` at column 2 (the inner nest level)
/--
info: true
-/
#guard_msgs in
#eval IO.println (nestThenSibling.pretty.endsWith "  }")

-- `renderFormat` correctly places `}` at column 0
/--
info: var x : int;
}
-/
#guard_msgs in
#eval IO.println (Strata.renderFormat nestThenSibling)

/-- Two levels of nesting: both closing braces should revert to their correct outer level. -/
private def nestedTwoLevels : Std.Format :=
  .append
    (.nest 2 (.append (.text "{\n") (.append (.nest 2 (.text "var x : int;\n")) (.text "}\n"))))
    (.text "}")

/--
info: {
    var x : int;
  }
}
-/
#guard_msgs in
#eval IO.println (Strata.renderFormat nestedTwoLevels)

end Strata.Format.Tests
