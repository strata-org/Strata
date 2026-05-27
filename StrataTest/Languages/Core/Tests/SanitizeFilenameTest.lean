/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-! # Tests: sanitizeFilename -/

#guard Core.SMT.sanitizeFilename "foo(bar) baz/qux\\quux" == "foo_bar__baz_qux_quux"
#guard Core.SMT.sanitizeFilename "a\"b'c" == "abc"
#guard Core.SMT.sanitizeFilename "simple_label_0" == "simple_label_0"
#guard Core.SMT.sanitizeFilename "" == ""
#guard Core.SMT.sanitizeFilename "<dead_branch: foo>" == "_dead_branch__foo_"
#guard Core.SMT.sanitizeFilename "a:b|c?d*e" == "a_b_c_d_e"
