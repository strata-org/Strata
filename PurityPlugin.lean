/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Lean

/-! # Purity Plugin

A Lean compiler plugin that ensures impure modules are always re-elaborated.

## How it works

1. **At plugin load** (start of each `lake build`): For every `.lean` source file
   that does NOT have a `.pure` marker in `.lake/build/lib/lean/`, delete its
   `.trace` file so Lake rebuilds it.

2. **During elaboration**: A linter runs after each command. It optimistically
   writes a `.pure` marker. If any impure command is detected, it deletes the
   marker. At the end of elaboration, only pure modules retain their marker.

Markers live in `.lake/build/lib/lean/` alongside `.olean` files, so they're
automatically cleaned by `lake clean` and ignored by git.

**Safe by default**: no `.pure` marker = rebuild.
-/

open Lean

namespace Strata.PurityPlugin

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

/-- Convert a source path to the build artifact stem.
`Strata/DDM/Elab/Env.lean` → `.lake/build/lib/lean/Strata/DDM/Elab/Env`
Handles absolute paths by stripping the CWD prefix. -/
private def toBuildStem (srcPath : String) : IO String := do
  let cwd ← IO.currentDir
  let rel := if srcPath.startsWith cwd.toString
    then ((srcPath.drop cwd.toString.length).dropWhile (· == '/')).toString
    else srcPath
  let stem := if rel.endsWith ".lean" then (rel.dropEnd 5).toString else rel
  return s!".lake/build/lib/lean/{stem}"

private partial def findLeanFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut result := #[]
  if ← root.isDir then
    for entry in ← root.readDir do
      result := result ++ (← findLeanFiles entry.path)
  else if root.extension == some "lean" then
    result := result.push root
  return result

/-- At plugin load: delete traces for modules without .pure markers. -/
private def invalidateImpureTraces : IO Unit := do
  let lockFile : System.FilePath := ".lake/build/purity_cleanup.lock"
  if ← lockFile.pathExists then return
  try IO.FS.writeFile lockFile "" catch _ => return
  for dir in #["Strata", "StrataTest"] do
    let path : System.FilePath := dir
    if ← path.isDir then
      let files ← findLeanFiles path
      for file in files do
        let stem ← toBuildStem file.toString
        let pureMarker : System.FilePath := stem ++ ".pure"
        unless ← pureMarker.pathExists do
          try IO.FS.removeFile (stem ++ ".trace") catch _ => pure ()
  for extra in #["StrataMain.lean"] do
    let file : System.FilePath := extra
    if ← file.pathExists then
      let stem ← toBuildStem extra
      let pureMarker : System.FilePath := stem ++ ".pure"
      unless ← pureMarker.pathExists do
        try IO.FS.removeFile (stem ++ ".trace") catch _ => pure ()
  try IO.FS.removeFile lockFile catch _ => pure ()

initialize invalidateImpureTraces

/-- Linter: optimistically write .pure marker on first pure command.
Delete it if any impure command is seen. -/
initialize Lean.addLinter {
  name := `Strata.purityPlugin
  run := fun stx => do
    let ctx ← readThe Lean.Elab.Command.Context
    let fileName := ctx.fileName
    if fileName.isEmpty then return
    let stem ← toBuildStem fileName
    let pureMarker := stem ++ ".pure"
    let kind := stx.getKind
    if kind == nullKind then return
    if !isPureCommand kind then
      try IO.FS.removeFile pureMarker catch _ => pure ()
    else
      let markerExists ← (System.FilePath.mk pureMarker).pathExists
      unless markerExists do
        let parent := (System.FilePath.mk pureMarker).parent.getD "."
        try IO.FS.createDirAll parent catch _ => pure ()
        IO.FS.writeFile pureMarker ""
}

end Strata.PurityPlugin
