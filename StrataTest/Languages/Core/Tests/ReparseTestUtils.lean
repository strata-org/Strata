/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.Languages.Core.DDMTransform.ASTtoCST
public meta import Strata.Languages.Core.DDMTransform.Translate
public meta import StrataDDM.Elab
public meta import StrataDDM.BuiltinDialects.Init

/-! # Parsing printed Core programs back, for printer tests -/

meta section

public section

namespace Strata.Test.CoreReparse

open Strata.CoreDDM

/-- Parses printed Core program text and translates it to a program. The
    `program Core;` header that `Core.formatProgram` prints is dropped first.
    A parse failure or translation error is returned as `.error` with its
    message instead of being thrown. -/
def parseAndTranslate (text : String) : IO (Except String Core.Program) := do
  let header := "program Core;\n\n"
  let body :=
    if text.startsWith header then (text.drop header.length).toString
    else text
  let dialects :=
    StrataDDM.Elab.LoadedDialects.ofDialects! #[StrataDDM.initDialect, Core]
  let inputCtx := StrataDDM.Parser.stringInputContext ⟨"core-reparse"⟩ body
  try
    let sp ←
      StrataDDM.Elab.parseStrataProgramFromDialect dialects "Core" inputCtx
    let (ast, errs) := TransM.run Inhabited.default (translateProgram sp)
    if errs.isEmpty then pure (.ok ast)
    else pure (.error s!"Translation errors: {errs}")
  catch e => pure (.error (toString e))

/-- The program part of `Core.formatProgram` output: the text before the block
    of conversion errors that the printer appends when it records any. -/
def withoutErrorBlock (printed : String) : String :=
  (printed.splitOn "\n\n-- Errors encountered during conversion:").headD printed

/-- Whether the printed text of `p` parses and translates back to a program
    that prints as the same text. -/
def reprintsSame (p : Core.Program) : IO Bool := do
  let printed := (Core.formatProgram p).pretty
  match ← parseAndTranslate printed with
  | .ok ast => pure ((Core.formatProgram ast).pretty == printed)
  | .error _ => pure false

end Strata.Test.CoreReparse

end -- public section
end
