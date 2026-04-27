/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Lean

/-! # Purity Plugin

A Lean compiler plugin that registers a linter to detect impure commands
during elaboration. When loaded via `lean --plugin`, it writes `.impure`
marker files next to `.olean` files for modules that use impure commands.

Configure in lakefile.toml:
```toml
[[lean_lib]]
name = "PurityPlugin"
plugins = ["PurityPlugin"]
```
-/

open Lean

namespace Strata.PurityPlugin

/-- Commands whose elaboration is known to be pure. -/
private def pureCommandKinds : Std.HashSet SyntaxNodeKind := .ofList [
  ``Lean.Parser.Command.declaration, ``Lean.Parser.Command.«deriving»,
  ``Lean.Parser.Command.«section», ``Lean.Parser.Command.«namespace»,
  ``Lean.Parser.Command.«end», ``Lean.Parser.Command.«variable»,
  ``Lean.Parser.Command.«universe», ``Lean.Parser.Command.«open»,
  ``Lean.Parser.Command.«export», ``Lean.Parser.Command.«import»,
  ``Lean.Parser.Command.«mutual», ``Lean.Parser.Command.«in»,
  ``Lean.Parser.Command.«include», ``Lean.Parser.Command.«omit»,
  ``Lean.Parser.Command.withWeakNamespace, ``Lean.Parser.Command.withExporting,
  ``Lean.Parser.Command.«set_option», ``Lean.Parser.Command.«attribute»,
  ``Lean.Parser.Command.check, ``Lean.Parser.Command.check_failure,
  ``Lean.Parser.Command.print, ``Lean.Parser.Command.printSig,
  ``Lean.Parser.Command.printAxioms, ``Lean.Parser.Command.printEqns,
  ``Lean.Parser.Command.printTacTags, ``Lean.Parser.Command.«where»,
  ``Lean.Parser.Command.version, ``Lean.Parser.Command.synth,
  ``Lean.Parser.Command.assertNotExists, ``Lean.Parser.Command.assertNotImported,
  ``Lean.Parser.Command.checkAssertions,
  ``Lean.Parser.Command.moduleDoc, ``Lean.Parser.Command.addDocString,
  ``Lean.Parser.Command.«register_tactic_tag»,
  ``Lean.Parser.Command.«tactic_extension»,
  ``Lean.Parser.Command.«recommended_spelling»,
  ``Lean.Parser.Command.genInjectiveTheorems,
  ``Lean.Parser.Command.registerErrorExplanationStx,
  ``Lean.Parser.Command.«init_quot», ``Lean.Parser.Command.exit,
  ``Lean.Parser.Command.eoi,
  `Lean.Option.registerOption, `Lean.Option.registerBuiltinOption
]

private def pureCommandPrefixes : Array Name := #[
  `Lean.Parser.Command.syntax, `Lean.Parser.Command.syntaxAbbrev,
  `Lean.Parser.Command.syntaxCat, `Lean.Parser.Command.notation,
  `Lean.Parser.Command.macro, `Lean.Parser.Command.macro_rules,
  `Lean.Parser.Command.elab, `Lean.Parser.Command.elab_rules,
  `Lean.Parser.Command.«scoped», `Lean.Parser.Command.«local»,
  `Lean.Parser.Command.simproc, `Lean.Parser.Command.builtin_simproc,
  `Lean.Parser.Command.dsimproc, `Lean.Parser.Command.builtin_dsimproc,
  `Lean.Parser.Command.register_simp_attr,
  `Lean.Parser.Command.register_option, `Lean.Parser.Command.register_builtin_option,
  `Lean.Parser.Command.register_label_attr,
  `Lean.Parser.Command.«infix», `Lean.Parser.Command.«infixl»,
  `Lean.Parser.Command.«infixr», `Lean.Parser.Command.«prefix»,
  `Lean.Parser.Command.«postfix»,
  `Lean.Parser.Command.declare_syntax_cat, `Lean.Parser.Command.declare_config_elab,
  `Lean.Parser.Command.declare_command_config_elab,
  `Lean.Parser.Command.declare_config_getter,
  `Lean.Parser.Command.declare_simp_like_tactic,
  `Lean.Parser.Command.declare_tagged_region,
  `Lean.Parser.Command.mixfix, `Lean.Parser.Command.grindPattern,
  `Lean.Parser.Command.binderPredicate
]

private def isPureCommand (kind : SyntaxNodeKind) : Bool :=
  pureCommandKinds.contains kind ||
  pureCommandPrefixes.any (fun pfx => pfx.isPrefixOf kind) ||
  kind == nullKind

/-- Delete build artifacts for a single .impure marker. -/
private def cleanMarker (marker : System.FilePath) : IO Unit := do
  let src := marker.toString.dropRight 7  -- strip ".impure"
  let stem := (if src.endsWith ".lean" then (src.dropEnd 5).toString else src)
  for suffix in #[".trace"] do
    try IO.FS.removeFile s!".lake/build/lib/lean/{stem}{suffix}" catch _ => pure ()
  try IO.FS.removeFile marker catch _ => pure ()

/-- Recursively find and clean .impure markers. -/
private partial def cleanImpureInDir (root : System.FilePath) : IO Unit := do
  if ← root.isDir then
    for entry in ← root.readDir do
      if entry.path.extension == some "impure" then
        cleanMarker entry.path
      else if ← entry.path.isDir then
        cleanImpureInDir entry.path

/-- Scan for .impure markers from the previous build and delete the
corresponding build artifacts so Lake re-elaborates those modules. -/
private def cleanPreviousImpureMarkers : IO Unit := do
  for dir in #["Strata", "StrataTest"] do
    let path : System.FilePath := dir
    if ← path.isDir then
      cleanImpureInDir path
  let marker : System.FilePath := "StrataMain.lean.impure"
  if ← marker.pathExists then
    cleanMarker marker

initialize cleanPreviousImpureMarkers

/-- Global ref tracking impure commands in the current module. -/
initialize impureRef : IO.Ref (Array SyntaxNodeKind) ← IO.mkRef #[]

/-- Register the purity linter. When an impure command is detected, write a
`.impure` marker file. The marker path is derived from the source file name
available in the elaboration context. -/
initialize Lean.addLinter {
  name := `Strata.purityPlugin
  run := fun stx => do
    let kind := stx.getKind
    if kind != nullKind && !isPureCommand kind then
      impureRef.modify (·.push kind)
      let ctx ← readThe Lean.Elab.Command.Context
      let fileName := ctx.fileName
      if !fileName.isEmpty then
        -- Write marker file for diagnostics
        let markerPath := fileName ++ ".impure"
        let existing ← try IO.FS.readFile markerPath catch _ => pure ""
        IO.FS.writeFile markerPath (existing ++ toString kind ++ "\n")
        -- Delete the .olean trace file so Lake rebuilds this module next time.
        -- Source: Strata/Foo/Bar.lean → Trace: .lake/build/lib/lean/Strata/Foo/Bar.trace
        let srcPath := fileName
        let stem := if srcPath.endsWith ".lean" then (srcPath.dropEnd 5).toString else srcPath
        let tracePath := s!".lake/build/lib/lean/{stem}.trace"
        try IO.FS.removeFile tracePath catch _ => pure ()
}

end Strata.PurityPlugin
