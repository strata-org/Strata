/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.Languages.Core.Verifier

/-! ## Tests: per-VC SMT filename stays within `NAME_MAX` (ENAMETOOLONG)

Obligation labels are derived from procedure names, and the per-obligation
SMT filename was `sanitizeFilename label`. A procedure whose name exceeds the
filesystem `NAME_MAX` (255 bytes) produced a `.smt2` filename that `open`
rejected with errno 63 (`ENAMETOOLONG`), aborting the whole run before any
goal could be discharged.

`sanitizeFilenameCapped` caps the filename component: labels within the cap
pass through byte-identically to `sanitizeFilename`; longer ones are truncated
and disambiguated with a hex hash of the full label, so the generated filename
stays within `NAME_MAX` while remaining unique and stable per label.

These checks pin the cap contract directly, driven by `bigName` — the exact
385-character procedure name whose `_ensures_0` obligation label overflowed the
filename limit before the cap. -/

---------------------------------------------------------------------
namespace Strata


/-- The offending procedure name (`P` + `_verylongsegment` × 24 = 385 chars):
    once the `_ensures_0` obligation suffix and `.smt2` extension are appended,
    the pre-cap filename exceeded `NAME_MAX` and aborted the run with errno 63. -/
private def bigName : String :=
  "P" ++ String.join (List.replicate 24 "_verylongsegment")

/-- Two distinct labels that share a 128-character prefix (so both truncate to
    the same prefix): distinctness must come from the appended hash. -/
private def sharedPrefixA : String := String.ofList (List.replicate 128 'z') ++ "AAAA"
private def sharedPrefixB : String := String.ofList (List.replicate 128 'z') ++ "BBBB"

-- Short labels (≤ cap) pass through byte-identically to `sanitizeFilename`.
#guard Core.SMT.sanitizeFilenameCapped "simple_label_0" == Core.SMT.sanitizeFilename "simple_label_0"
#guard Core.SMT.sanitizeFilenameCapped "foo(bar) baz/qux\\quux" == Core.SMT.sanitizeFilename "foo(bar) baz/qux\\quux"
#guard Core.SMT.sanitizeFilenameCapped "simple_label_0" == "simple_label_0"

-- The offending 385-char name is capped well within `NAME_MAX`: it is truncated
-- to the 128-char cap and (being longer) carries the appended hash suffix, so it
-- is bounded and no longer the raw sanitized string that overflowed the limit.
#guard (Core.SMT.sanitizeFilenameCapped bigName).length ≤ 160
#guard 128 < (Core.SMT.sanitizeFilenameCapped bigName).length
#guard Core.SMT.sanitizeFilenameCapped bigName ≠ Core.SMT.sanitizeFilename bigName

-- Uniqueness: two labels sharing the truncated 128-char prefix still map to
-- distinct capped names, because the hash is taken over the full label.
#guard Core.SMT.sanitizeFilenameCapped sharedPrefixA ≠ Core.SMT.sanitizeFilenameCapped sharedPrefixB


end Strata
