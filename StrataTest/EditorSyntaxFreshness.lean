/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import CoreSyntaxGen

/-!
# Editor syntax-highlighting freshness test

Verifies that the checked-in editor syntax files
(`editors/vscode/syntaxes/core-st.tmLanguage.json` and
`editors/emacs/core-st-mode.el`) are up to date with the `Core` DDM grammar.

It runs as an elaboration-time test in the `StrataTest` library (like
`StrataTest.EmbeddedDataFreshness`), so it fires during `lake test` and fails
the build when the generated files drift from the grammar.

Regenerate with:

```
lake env lean --run editors/GenSyntax.lean all
```
-/

#eval show IO Unit from do
  let stale ← CoreSyntaxGen.staleSyntaxFiles
  if stale.isEmpty then
    IO.println s!"✓ Editor syntax files are up to date ({CoreSyntaxGen.generatedSyntaxFiles.length} files)."
  else
    IO.eprintln s!"{stale.size} editor syntax file(s) are out of date:"
    for p in stale do
      IO.eprintln s!"  {p}"
    throw <| IO.userError
      "Editor syntax files are out of date with the Core grammar. \
       Run 'lake env lean --run editors/GenSyntax.lean all' and commit the result."
