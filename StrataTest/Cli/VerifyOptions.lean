/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Cli.VerifyOptions

/-! ## Tests for `keepAllFilesBaseName`

`--keep-all-files <dir>` derives a per-run base name inside the directory from
the input file's path, following Strata's `<name>.<dialect>.st[.ion]` naming
convention: the trailing `st` component and the dialect token before it are
dropped, so intermediate files read as `<dir>/<baseName>.<n>.<phase>.core.st`.
These pin that derivation. -/

meta section

-- `.st`-family inputs: drop both the `st` and the dialect component.
#guard keepAllFilesBaseName (some "Foo.core.st") == "Foo"
#guard keepAllFilesBaseName (some "/tmp/x/Foo.csimp.st") == "Foo"
#guard keepAllFilesBaseName (some "Foo.python.st.ion") == "Foo"
-- A bare `.st` keeps at least the first component.
#guard keepAllFilesBaseName (some "Foo.st") == "Foo"
-- Dots in the stem are preserved; only the dialect + `st` are stripped.
#guard keepAllFilesBaseName (some "a.b.core.st") == "a.b"
#guard keepAllFilesBaseName (some "Foo.st.ion") == "Foo"
-- No `st` component (e.g. Python Ion): fall back to the first component.
#guard keepAllFilesBaseName (some "Foo.py.ion") == "Foo"
-- No dots at all (extensionless input): the whole name is the base.
#guard keepAllFilesBaseName (some "Foo") == "Foo"
-- `st` mid-name is *not* the sentinel: only a terminal `st` (or last-before
-- `ion`) triggers dialect stripping, so these fall back to the first component
-- instead of dropping the real trailing extension as a dialect token.
#guard keepAllFilesBaseName (some "Foo.st.txt") == "Foo"
#guard keepAllFilesBaseName (some "Foo.b3.st.backup") == "Foo"
-- Dot-prefixed inputs whose derived base would be empty (first component is
-- ""): fall back to the fixed stdin name rather than emitting hidden files
-- like `<dir>/.1.phase.core.st`.
#guard keepAllFilesBaseName (some ".st") == "program"
#guard keepAllFilesBaseName (some ".st.ion") == "program"
#guard keepAllFilesBaseName (some "..st") == "program"
-- `st` alone: last component IS `st` but length < 2, so the `.st`-family
-- branch is not taken (guards the `&&` boundary) and the whole name is kept.
#guard keepAllFilesBaseName (some "st") == "st"
-- A genuinely hidden file with a real stem keeps its (dotted) stem — only the
-- empty-first-component case falls back.
#guard keepAllFilesBaseName (some ".hidden.core.st") == ".hidden"
-- No input file (e.g. stdin): fall back to a fixed name.
#guard keepAllFilesBaseName none == "program"

end
