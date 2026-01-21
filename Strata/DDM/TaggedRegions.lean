/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Lean.PrettyPrinter.Formatter
import Lean.PrettyPrinter.Parenthesizer
import all Strata.DDM.Util.String

public meta import Lean.Elab.Syntax

open Lean (SourceInfo Syntax SyntaxNodeKind Name format)
open Lean.Elab.Command (CommandElab CommandElabM liftTermElabM elabCommand)
open Lean.Elab.Term (addCategoryInfo)
open Lean.Parser (Parser ParserFn isParserCategory node symbol)
open Lean.Syntax (Term)
open Lean.Syntax.MonadTraverser (getCur goLeft)
open Lean.PrettyPrinter.Formatter (pushToken withMaybeTag throwBacktrack)

public section
namespace Strata.ExternParser

private def parserFn (endToken : String) : ParserFn := fun c s => Id.run do
  if s.hasError then
    return s
  let startPos := s.pos
  let some stopPos := c.inputString.indexOfRaw endToken s.pos
        | s.setError { unexpected := s!"Could not find end token {endToken}" }
  let s := s.setPos stopPos
  let leading   := c.mkEmptySubstringAt startPos
  let trailing  := c.mkEmptySubstringAt stopPos
  let info      := SourceInfo.original leading startPos trailing stopPos
  s.pushSyntax (Syntax.atom info "")

def mkParser (n : SyntaxNodeKind) (startToken endToken : String) : Parser :=
  node n (symbol startToken >> { fn := parserFn endToken } >> symbol endToken)

private def SourceInfo.getExprPos? : SourceInfo → Option String.Pos.Raw
  | SourceInfo.synthetic (pos := pos) .. => pos
  | _ => none

@[combinator_formatter mkParser]
def mkParser.formatter (sym : Name) := do
  let stx ← getCur
  if stx.getKind != sym then do
    trace[PrettyPrinter.format.backtrack] "unexpected syntax '{format stx}', expected symbol '{sym}'"
    throwBacktrack
  let Syntax.node info _ args := stx
      | unreachable!
  -- FIXME
  withMaybeTag (SourceInfo.getExprPos? info) (pushToken info stx[0].getId.toString false)
  goLeft

@[combinator_parenthesizer mkParser]
def mkParser.parenthesizer (_ : Name) :=
  -- FIXME
  Lean.PrettyPrinter.Parenthesizer.symbolNoAntiquot.parenthesizer

/--
This declares a parse for a known category.

- `stx` Is the syntax whose source location is used for the declaration.
- `cat` Is the category for the node
- `stxNodeKind` is the name for the node kind produced by this parser.
-/
private meta def declareParser (stx : Syntax) (cat : Name) (stxNodeKind : Name) (val : Term) : CommandElabM Unit := do
  unless (isParserCategory (← Lean.getEnv) cat) do
    throwErrorAt stx "unknown category '{cat}'"
  liftTermElabM <| addCategoryInfo stx cat
  let catParserId := Lean.mkIdentFrom stx (cat.appendAfter "_parser")
  let declName := Lean.mkIdentFrom stx stxNodeKind (canonical := true)
  let attrInstances : Syntax.TSepArray `Lean.Parser.Term.attrInstance "," := { elemsAndSeps := #[] }
  let attrInstance ← `(Lean.Parser.Term.attrInstance| $catParserId:ident $(Lean.quote 1000):num)
  let attrInstances := attrInstances.push attrInstance
  let d ← `(@[$attrInstances,*] def $declName:ident : Lean.Parser.Parser := $val)
  elabCommand d

/--
This creates declares a parser that recognizes text within a set of tags.
-/
syntax (name := declareTaggedRegion) (docComment)? "declare_tagged_region" ident ident str str : command -- declare the syntax

@[command_elab declareTaggedRegion]
meta def declareTaggedRegionImpl: CommandElab := fun stx => do -- declare and register the elaborator
  let `(declare_tagged_region $catStx $cmdStx $startToken $endToken) := stx
    | Lean.Elab.throwUnsupportedSyntax
  let cat : Name := catStx.getId
  let cmd : Term := Lean.quote cmdStx.getId
  let cmd : Term := ⟨cmd.raw.setInfo cmdStx.raw.getHeadInfo⟩
  let decl ← `(ExternParser.mkParser $cmd $startToken $endToken)
  declareParser stx cat cmdStx.getId decl

initialize
  Lean.registerTraceClass `Strata.DDM.syntax

end Strata.ExternParser
end
