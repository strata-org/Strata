/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import CoreSyntaxGen

/-!
# Auto-generate editor syntax highlighting from the Core DDM grammar

Usage:
  lake env lean --run editors/GenSyntax.lean vscode   # writes editors/vscode/syntaxes/core-st.tmLanguage.json
  lake env lean --run editors/GenSyntax.lean emacs    # writes editors/emacs/core-st-mode.el
  lake env lean --run editors/GenSyntax.lean all      # writes both (default)
  lake env lean --run editors/GenSyntax.lean --check  # verify the checked-in files are up to date

The generation logic lives in `CoreSyntaxGen`; this file is just the CLI.
The `--check` mode reports whether the checked-in files are up to date without
rewriting them (the same comparison `StrataTest.EditorSyntaxFreshness` makes).
-/

open CoreSyntaxGen

/-! ## Main -/

def main (args : List String) : IO UInt32 := do
  let target := args.head?.getD "all"
  -- Freshness check: regenerate in memory and compare against the checked-in files.
  if target == "--check" then
    let stale ← staleSyntaxFiles
    if stale.isEmpty then
      IO.println "✓ Editor syntax files are up to date."
      return 0
    else
      IO.eprintln s!"✗ {stale.size} editor syntax file(s) are out of date:"
      for p in stale do
        IO.eprintln s!"  {p}"
      IO.eprintln ""
      IO.eprintln "To fix: run 'lake env lean --run editors/GenSyntax.lean all' and commit the result."
      return 1
  if target == "vscode" || target == "all" then
    IO.FS.writeFile vscodeSyntaxPath vscodeContent
    IO.println s!"Wrote {vscodeSyntaxPath}"
  if target == "emacs" || target == "all" then
    IO.FS.writeFile emacsSyntaxPath emacsContent
    IO.println s!"Wrote {emacsSyntaxPath}"
  if target != "vscode" && target != "emacs" && target != "all" then
    IO.eprintln s!"Usage: lake env lean --run editors/GenSyntax.lean [vscode|emacs|all|--check]"
    return 1
  return 0
