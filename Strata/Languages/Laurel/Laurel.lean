/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Core
public import Strata.Languages.Laurel.LaurelAST
public import Strata.Languages.Laurel.LaurelCompilationPipeline
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import StrataDDM.Elab

/-! ## Strata Laurel API

Reading, translating, and analyzing Laurel programs.
-/

public section

namespace Strata

/-! ### File I/O -/

/--
Read a Laurel source file in textual format and parse it into
a `Laurel.Program`. Handles dialect loading, parsing, and
AST translation in one step.
-/
def parseLaurelText (path : System.FilePath) (content : String)
    : IO Laurel.Program := do
  let input := StrataDDM.Parser.stringInputContext path content
  let dialects :=
    StrataDDM.Elab.LoadedDialects.ofDialects!
      #[StrataDDM.initDialect, Strata.Laurel.Laurel]
  let strataProgram ←
    StrataDDM.Elab.parseStrataProgramFromDialect
      dialects Strata.Laurel.Laurel.name input
  let uri := Strata.Uri.file path.toString
  match Strata.Laurel.TransM.run uri
      (Strata.Laurel.parseProgram strataProgram) with
  | .ok program => pure program
  | .error errors =>
    throw (IO.userError s!"Laurel translation errors: {errors}")

def readLaurelTextFile (path : System.FilePath)
    : IO Laurel.Program := do
  let content ← IO.FS.readFile path
  parseLaurelText path content

/--
Deserialize Laurel Ion bytes (possibly containing multiple files)
into a list of `StrataFile`s. Useful for per-file operations like
printing.
-/
def readLaurelIonFiles (bytes : ByteArray)
    : IO (List StrataDDM.StrataFile) := do
  match StrataDDM.Program.filesFromIon Strata.Laurel.Laurel_map bytes with
  | .ok files => pure files
  | .error msg => throw (IO.userError msg)

/--
Deserialize Laurel Ion bytes and parse all files into a single
combined `Laurel.Program`.
-/
def readLaurelIonProgram (bytes : ByteArray)
    : IO Laurel.Program := do
  let files ← readLaurelIonFiles bytes
  let mut combined : Laurel.Program := {
    staticProcedures := []
    staticFields := []
    types := []
  }
  for file in files do
    match Strata.Laurel.TransM.run
        (Strata.Uri.file file.filePath)
        (Strata.Laurel.parseProgram file.program) with
    | .ok pgm =>
      combined := {
        staticProcedures :=
          combined.staticProcedures ++ pgm.staticProcedures
        staticFields :=
          combined.staticFields ++ pgm.staticFields
        types := combined.types ++ pgm.types
      }
    | .error errors =>
      throw (IO.userError
        s!"Translation errors in {file.filePath}: {errors}")
  pure combined

/-! ### Transformation between generic and dialect-specific representation -/

/--
Translate a program in the dialect-specific AST for Laurel into the generic Strata
AST. Usually useful as a step before serialization.
-/
def laurelToStrataProgram (p : Laurel.Program) : StrataDDM.Program :=
  Laurel.programToStrata p

/--
Translate a program in the generic AST for Strata into the dialect-specific AST
for Laurel. This can fail with an error message if the input is not a
well-structured instance of the Laurel dialect.

TODO: possibly add an input context argument
-/
def strataProgramToLaurel (p : StrataDDM.Program) : Except String Laurel.Program :=
  Laurel.TransM.run .none (Laurel.parseProgram p)

/-! ### Transformation between dialects -/

/--
Translate a program represented in the dialect-specific AST for the Laurel
dialect into the dialect-specific AST for the Core dialect. This can fail with
an error message if the input program contains constructs that are not yet
supported.
-/
def laurelToCore (p : Laurel.Program) : IO (Except String Core.Program) := do
  let (coreOpt, diags) ← Laurel.translate { emitResolutionErrors := true } p
  match coreOpt with
  | some core => return .ok core
  | none => return .error s!"Laurel to Core translation failed: {diags.map (·.message)}"

/-! ### Analysis of Laurel programs -/

/--
Analyze a Laurel program by translating to Core and running
verification. Returns VC results (if translation succeeded)
and any translation diagnostics.
-/
def Laurel.verifyProgram
    (program : Laurel.Program)
    (options : Core.VerifyOptions := .default)
    : IO (Option Core.VCResults × List DiagnosticModel) :=
  Strata.Laurel.verifyToVcResults program { verifyOptions := options }

/--
Analyze a Laurel program and return structured diagnostic models
(combining translation errors and verification results).
-/
def Laurel.analyzeToDiagnosticModels
    (program : Laurel.Program)
    (options : Core.VerifyOptions := .default)
    : IO (Array DiagnosticModel) :=
  Strata.Laurel.verifyToDiagnosticModels program { verifyOptions := options }

end Strata

end -- public section
