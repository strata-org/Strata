/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.CoreMatch.Verify
import Strata.Languages.CoreMatch.DDMTransform.StrataGen
import Strata.DDM.Elab

/-!
Per-file iteration helper for the CoreMatch dialect. Invoked as
`lake exe coreMatchCheck <file.coreMatch.st> [--show-decls]`; prints
`OK: <N> decls` on success or `ERR: <message>` on failure.
-/

open Strata
open Lambda

private def declSummary (d : Core.Decl) : String :=
  match d with
  | .type t _ =>
    match t with
    | .data block =>
      let names := block.map (·.name)
      s!"  type (data) {names}"
    | .con tc => s!"  type {tc.name}"
    | .syn ts => s!"  type {ts.name} (synonym)"
  | .ax a _ => s!"  axiom {a.name}"
  | .distinct n _ _ => s!"  distinct {n.name}"
  | .proc p _ => s!"  procedure {p.header.name.name}"
  | .func f _ =>
    let kind := if f.isRecursive then "rec function" else "function"
    s!"  {kind} {f.name.name}"
  | .recFuncBlock fs _ =>
    let names := fs.map (·.name.name)
    s!"  rec block {names}"

private def runOnFile (path : System.FilePath) (showDecls : Bool) : IO UInt32 := do
  let content ← IO.FS.readFile path
  let input := Strata.Parser.stringInputContext path content
  let dialects :=
    Strata.Elab.LoadedDialects.ofDialects!
      #[Strata.initDialect, Strata.Core, Strata.CoreMatch]
  let leanEnv ← Lean.mkEmptyEnvironment 0
  let prog ←
    match Strata.Elab.elabProgram dialects leanEnv input with
    | .ok p => pure p
    | .error errors =>
      let mut msg : String := "ERR: parse failed:"
      for e in errors do
        msg := msg ++ s!"\n  {e.pos.line}:{e.pos.column}: {← e.data.toString}"
      IO.eprintln msg
      return (1 : UInt32)
  match Strata.CoreMatch.Verify.parseToCore prog path.toString with
  | .error e =>
    IO.eprintln s!"ERR: lowering failed: {e.format none}"
    return (1 : UInt32)
  | .ok cp =>
    IO.println s!"OK: {cp.decls.length} decls"
    if showDecls then
      for d in cp.decls do
        IO.println (declSummary d)
    return (0 : UInt32)

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["--help"] =>
    IO.println "Usage: lake exe coreMatchCheck <file.coreMatch.st> [--show-decls]"
    return (0 : UInt32)
  | path :: rest =>
    let showDecls := rest.contains "--show-decls"
    runOnFile path showDecls
