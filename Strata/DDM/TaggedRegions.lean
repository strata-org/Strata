/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Lean.Elab.Syntax
import Strata.DDM.Util.String

open Lean Elab.Command Parser

namespace Strata

namespace ExternParser

def parserFn (endToken : String) : ParserFn := fun c s => Id.run do
  if s.hasError then
    return s
  let startPos := s.pos
  let some stopPos := c.inputString.indexOf endToken s.pos
        | s.setError { unexpected := s!"Could not find end token {endToken}" }
  let s := s.setPos stopPos
  let leading   := c.mkEmptySubstringAt startPos
  let trailing  := c.mkEmptySubstringAt stopPos
  let info      := SourceInfo.original leading startPos trailing stopPos
  s.pushSyntax (Syntax.atom info "")

def mkParser (n : SyntaxNodeKind) (startToken endToken : String) : Parser :=
  node n (symbol startToken >> { fn := parserFn endToken } >> symbol endToken)

open Syntax Syntax.MonadTraverser
open Lean.PrettyPrinter.Formatter

private def SourceInfo.getExprPos? : SourceInfo → Option String.Pos
  | SourceInfo.synthetic (pos := pos) .. => pos
  | _ => none

@[combinator_formatter mkParser] def mkParser.formatter (sym : Name) := do
  let stx ← getCur
  if stx.getKind != sym then do
    trace[PrettyPrinter.format.backtrack] "unexpected syntax '{format stx}', expected symbol '{sym}'"
    throwBacktrack
  let Syntax.node info _ args := stx
      | unreachable!
  -- FIXME
  withMaybeTag (SourceInfo.getExprPos? info) (pushToken info stx[0].getId.toString false)
  goLeft

@[combinator_parenthesizer mkParser] def mkParser.parenthesizer (_ : Name) :=
  -- FIXME
  PrettyPrinter.Parenthesizer.symbolNoAntiquot.parenthesizer

/--
This declares a parse for a known category.

- `stx` Is the syntax whose source location is used for the declaration.
- `cat` Is the category for the node
- `stxNodeKind` is the name for the node kind produced by this parser.
-/
def declareParser (stx : Syntax) (cat : Name) (stxNodeKind : Name) (val : Term) : CommandElabM Unit := do
  unless (isParserCategory (← getEnv) cat) do
    throwErrorAt stx "unknown category '{cat}'"
  liftTermElabM <| Elab.Term.addCategoryInfo stx cat
  let catParserId := mkIdentFrom stx (cat.appendAfter "_parser")
  let declName := mkIdentFrom stx stxNodeKind (canonical := true)
  let attrInstances : Syntax.TSepArray `Lean.Parser.Term.attrInstance "," := { elemsAndSeps := #[] }
  let attrInstance ← `(Lean.Parser.Term.attrInstance| $catParserId:ident $(quote 1000):num)
  let attrInstances := attrInstances.push attrInstance
  let d ← `(@[$attrInstances,*] def $declName:ident : Lean.Parser.Parser := $val)
  elabCommand d

/--
This creates declares a parser that recognizes text within a set of tags.
-/
syntax (name := declareTaggedRegion) (docComment)? "declare_tagged_region" ident ident str str : command -- declare the syntax

@[command_elab declareTaggedRegion]
def declareTaggedRegionImpl: CommandElab := fun stx => do -- declare and register the elaborator
  let `(declare_tagged_region $catStx $cmdStx $startToken $endToken) := stx
    | Elab.throwUnsupportedSyntax
  let cat : Name := catStx.getId
  let cmd : Term := quote cmdStx.getId
  let cmd : Term := ⟨cmd.raw.setInfo cmdStx.raw.getHeadInfo⟩
  let decl ← `(ExternParser.mkParser $cmd $startToken $endToken)
  declareParser stx cat cmdStx.getId decl

initialize
  registerTraceClass `Strata.DDM.syntax

end ExternParser
end Strata
