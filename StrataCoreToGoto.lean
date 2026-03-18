/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.CoreToGOTOPipeline
import Strata.Backends.CBMC.GOTO.DefaultSymbols
import Strata.Backends.CBMC.CollectSymbols
import Strata.Languages.Core.Verifier
import Strata.Transform.CallElim
import Strata.Util.IO

open Strata

def usageMessage : Std.Format :=
  f!"Usage: StrataCoreToGoto [OPTIONS] <file.core.st>{Std.Format.line}\
  {Std.Format.line}\
  Translates a Strata Core program to CProver GOTO JSON files.{Std.Format.line}\
  {Std.Format.line}\
  Options:{Std.Format.line}\
  {Std.Format.line}  \
  --output-dir <dir>    Directory for output files (default: current directory){Std.Format.line}  \
  --program-name <name> Program name for GOTO output (default: derived from filename){Std.Format.line}  \
  --no-call-elim        Skip call elimination (keep raw calls for external DFCC)"

structure GotoOptions where
  outputDir : String := "."
  programName : Option String := none
  callElim : Bool := true

def parseOptions (args : List String) : Except Std.Format (GotoOptions × String) :=
  go {} args
  where
    go : GotoOptions → List String → Except Std.Format (GotoOptions × String)
    | opts, "--output-dir" :: dir :: rest => go {opts with outputDir := dir} rest
    | opts, "--program-name" :: name :: rest => go {opts with programName := some name} rest
    | opts, "--no-call-elim" :: rest => go {opts with callElim := false} rest
    | opts, [file] => .ok (opts, file)
    | _, [] => .error "StrataCoreToGoto requires a .core.st file as input"
    | _, args => .error f!"Unknown options: {args}"

def deriveBaseName (file : String) : String :=
  let name := System.FilePath.fileName file |>.getD file
  if name.endsWith ".core.st" then (name.dropEnd 8).toString
  else if name.endsWith ".st" then (name.dropEnd 3).toString
  else name

def main (args : List String) : IO UInt32 := do
  match parseOptions args with
  | .ok (opts, file) =>
    unless file.endsWith ".core.st" do
      IO.println "Error: expected a .core.st file"
      IO.println f!"{usageMessage}"
      return 1
    let baseName := deriveBaseName file
    let programName := opts.programName.getD baseName
    let dir := System.FilePath.mk opts.outputDir
    IO.FS.createDirAll dir

    let text ← Strata.Util.readInputSource file
    let inputCtx := Lean.Parser.mkInputContext text (Strata.Util.displayName file)
    let dctx := Elab.LoadedDialects.builtin
    let dctx := dctx.addDialect! Core
    let leanEnv ← Lean.mkEmptyEnvironment 0
    match Strata.Elab.elabProgram dctx leanEnv inputCtx with
    | .error errors =>
      for e in errors do
        let msg ← e.toString
        IO.println s!"Error: {msg}"
      return 1
    | .ok pgm =>
      -- Type check (translates DDM Program → Core.Program)
      let Ctx := { Lambda.LContext.default with
        functions := Core.Factory, knownTypes := Core.KnownTypes }
      let Env := Lambda.TEnv.default
      let tcPgm ← match Strata.typeCheck inputCtx pgm with
        | .ok p => pure p
        | .error e => IO.println s!"Type check error: {e.message}"; return 1
      IO.println "[Strata.Core] Type Checking Succeeded!"

      -- Apply call elimination to inline contracts (assert requires / assume ensures)
      let tcPgm ← if opts.callElim then
        match Core.Transform.run tcPgm (fun p => do
              let (_, p) ← Core.CallElim.callElim' p; return p) with
        | .ok p => pure p
        | .error e => IO.println s!"Call elimination error: {e}"; return 1
      else pure tcPgm

      -- Re-type-check after call elimination (discovers new variables)
      let tcPgm ← match Core.typeCheck .default tcPgm with
        | .ok p => pure p
        | .error e => IO.println s!"Re-type-check error: {e}"; return 1

      -- Apply GOTO pipeline passes
      let tcPgm := inlineFuncDefsInProgram tcPgm
      let tcPgm := inlineRecFuncDefsInProgram tcPgm
      let tcPgm := partialEvalDatatypesInProgram tcPgm

      -- Collect procedures and functions
      let procs := tcPgm.decls.filterMap fun d => d.getProc?
      let funcs := tcPgm.decls.filterMap fun d =>
        match d.getFunc? with
        | some f =>
          let name := Core.CoreIdent.toPretty f.name
          if f.body.isSome && f.typeArgs.isEmpty
            && name != "Int.DivT" && name != "Int.ModT"
          then some f else none
        | none => none

      if procs.isEmpty && funcs.isEmpty then
        IO.println "Error: No procedures or functions found"
        return 1

      -- Collect axioms and type symbols
      let axioms := tcPgm.decls.filterMap fun d => d.getAxiom?
      let dtAxioms := generateDatatypeAxioms tcPgm
      let recAxioms := generateRecFuncAxioms tcPgm (unrollDepth := 0)
      let axioms := axioms ++ dtAxioms ++ recAxioms
      let distincts := tcPgm.decls.filterMap fun d => match d with
        | .distinct name es _ => some (name, es) | _ => none
      let typeSyms ← match collectExtraSymbols tcPgm with
        | .ok s => pure s
        | .error e => IO.println s!"Error collecting symbols: {e}"; return 1
      let gotoDtInfo := collectGotoDatatypeInfo tcPgm

      -- Translate each procedure and function to GOTO
      let mut symtabPairs : List (String × Lean.Json) := []
      let mut gotoFns : Array Lean.Json := #[]
      -- Seed type environment with global variable types
      let globalVarEntries : Map Core.Expression.Ident Core.Expression.Ty :=
        tcPgm.decls.filterMap fun d =>
          match d with
          | .var name ty _ _ => some (name, ty)
          | _ => none
      let Env := Lambda.TEnv.addInNewestContext
        (T := ⟨Core.ExpressionMetadata, Unit⟩) Env globalVarEntries

      let mut allLiftedFuncs : List Core.Function := []

      for p in procs do
        let procName := Core.CoreIdent.toPretty p.header.name
        match procedureToGotoCtx Env p (axioms := axioms) (distincts := distincts)
              (varTypes := tcPgm.getVarTy?) with
        | .error e => IO.println s!"Warning: skipping procedure {procName}: {e}"
        | .ok (ctx, liftedFuncs) =>
          allLiftedFuncs := allLiftedFuncs ++ liftedFuncs
          let ctx := rewriteDatatypeExprsInCtx gotoDtInfo ctx
          let ctx ← lowerAddressOfInCtx ctx
          let json ← IO.ofExcept (CoreToGOTO.CProverGOTO.Context.toJson procName ctx)
          match json.symtab with
          | .obj m => symtabPairs := symtabPairs ++ m.toList
          | _ => pure ()
          match json.goto with
          | .obj m =>
            match m.toList.find? (·.1 == "functions") with
            | some (_, .arr fns) => gotoFns := gotoFns ++ fns
            | _ => pure ()
          | _ => pure ()

      for f in funcs ++ allLiftedFuncs do
        let funcName := Core.CoreIdent.toPretty f.name
        match functionToGotoCtx Env f with
        | .error e => IO.println s!"Warning: skipping function {funcName}: {e}"
        | .ok ctx =>
          let json ← IO.ofExcept (CoreToGOTO.CProverGOTO.Context.toJson funcName ctx)
          match json.symtab with
          | .obj m => symtabPairs := symtabPairs ++ m.toList
          | _ => pure ()
          match json.goto with
          | .obj m =>
            match m.toList.find? (·.1 == "functions") with
            | some (_, .arr fns) => gotoFns := gotoFns ++ fns
            | _ => pure ()
          | _ => pure ()

      -- Add type symbols
      match Lean.toJson typeSyms with
      | .obj m => symtabPairs := symtabPairs ++ m.toList
      | _ => pure ()

      -- Deduplicate symbol table
      let mut seen : Std.HashSet String := {}
      let mut dedupPairs : List (String × Lean.Json) := []
      for (k, v) in symtabPairs do
        if !seen.contains k then
          seen := seen.insert k
          dedupPairs := dedupPairs ++ [(k, v)]

      -- Add CBMC default symbols
      for (k, v) in CProverGOTO.defaultSymbols (moduleName := programName) do
        if !seen.contains k then
          seen := seen.insert k
          dedupPairs := dedupPairs ++ [(k, Lean.toJson v)]

      let symtab := Lean.Json.mkObj [("symbolTable", Lean.Json.mkObj dedupPairs)]
      let goto := Lean.Json.mkObj [("functions", Lean.Json.arr gotoFns)]

      let symTabFile := dir / s!"{programName}.symtab.json"
      let gotoFile := dir / s!"{programName}.goto.json"
      IO.FS.writeFile symTabFile symtab.pretty
      IO.FS.writeFile gotoFile goto.pretty
      IO.println s!"Translated {procs.length} procedures and {funcs.length} functions"
      IO.println s!"Written {symTabFile} and {gotoFile}"
      return 0
  | .error msg =>
    IO.println f!"{msg}"
    IO.println f!"{usageMessage}"
    return 1
