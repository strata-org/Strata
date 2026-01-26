/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import all Strata.DDM.Util.String

/-! ## Tests for String utilities -/

namespace String

/--
info: [" ab", "cd", "", "de", ""]
-/
#guard_msgs in
#eval " ab\ncd\n\nde\n".splitLines

/--
info: [""]
-/
#guard_msgs in
#eval "".splitLines

end String
