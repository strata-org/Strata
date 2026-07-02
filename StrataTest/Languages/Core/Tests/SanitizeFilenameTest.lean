/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.Verifier

meta section

/-! # Tests: sanitizeFilename -/

#guard Core.SMT.sanitizeFilename "foo(bar) baz/qux\\quux" == "foo_bar__baz_qux_quux"
#guard Core.SMT.sanitizeFilename "a\"b'c" == "abc"
#guard Core.SMT.sanitizeFilename "simple_label_0" == "simple_label_0"
#guard Core.SMT.sanitizeFilename "" == ""
#guard Core.SMT.sanitizeFilename "<dead_branch: foo>" == "_dead_branch__foo_"
#guard Core.SMT.sanitizeFilename "a:b|c?d*e" == "a_b_c_d_e"

/-! # Tests: sanitizeFilenameCapped

Labels within the cap pass through byte-identically to `sanitizeFilename`;
longer ones are truncated and hashed so the filename stays within `NAME_MAX`. -/

-- Short labels pass through unchanged (identical to `sanitizeFilename`).
#guard Core.SMT.sanitizeFilenameCapped "foo(bar) baz/qux\\quux" == "foo_bar__baz_qux_quux"
#guard Core.SMT.sanitizeFilenameCapped "simple_label_0" == "simple_label_0"
#guard Core.SMT.sanitizeFilenameCapped "" == ""
#guard Core.SMT.sanitizeFilenameCapped "a:b|c?d*e" == Core.SMT.sanitizeFilename "a:b|c?d*e"

-- A label longer than the 128-char cap is truncated and a hash appended, so the
-- result exceeds 128 chars but stays bounded well within `NAME_MAX`.
#guard (Core.SMT.sanitizeFilenameCapped (String.ofList (List.replicate 200 'a'))).length ≤ 160
#guard 128 < (Core.SMT.sanitizeFilenameCapped (String.ofList (List.replicate 200 'a'))).length

end
