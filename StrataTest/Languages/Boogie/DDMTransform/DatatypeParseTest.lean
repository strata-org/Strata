/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.DDMTransform.Parse

/-!
# Datatype Syntax Parsing Tests

This module contains tests for the datatype syntax parsing in Boogie DDM.

## Tests

1. **Simple datatype parsing**: `datatype Bool { True(), False() };`
2. **Datatype with fields**: `datatype Point { Point(x: int, y: int) };`

**Validates: Requirements 1.1, 1.2, 1.3, 1.4, 1.5, 8.1**
-/

namespace Boogie.DDMTransform.DatatypeParseTest

/-! ## Test 1: Simple Datatype Parsing -/

/--
Test that simple datatype syntax parses correctly.
datatype Bool { True(), False() };
-/
def test_simple_datatype_parsing :=
#strata
program Boogie;
datatype Bool { True(), False() };
#end

/-- info: true -/
#guard_msgs in
#eval test_simple_datatype_parsing.commands.size > 0

/-! ## Test 2: Datatype with Fields -/

/--
Test that datatype with fields parses correctly.
datatype Point { Point(x: int, y: int) };
-/
def test_datatype_with_fields :=
#strata
program Boogie;
datatype Point { Point(x: int, y: int) };
#end

/-- info: true -/
#guard_msgs in
#eval test_datatype_with_fields.commands.size > 0

end Boogie.DDMTransform.DatatypeParseTest
