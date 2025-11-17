/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Std.Data.HashSet
import Strata.DDM.Format
import Strata.DDM.Elab.Env
import Strata.DDM.Util.PrattParsingTables

open Lean
open Parser (
    LeadingIdentBehavior
    ParserContext
    ParserFn
    ParserModuleContext
    ParserState
    PrattParsingTables
    SyntaxStack
    Token
    TokenMap
    TokenTable
    TrailingParser
    andthenFn
    checkLhsPrec
    checkPrec
    getNext
    runLongestMatchParser
    longestMatchStep
    noFirstTokenInfo
    manyFn
    manyNoAntiquot
    mkAtomicInfo
    mkIdent
    nodeInfo
    optionalInfo
    quotedCharFn
    quotedStringFn
    sepByInfo
    sepByFn
    setLhsPrec
    symbolInfo
    takeUntilFn
    takeWhileFn
    trailingLoop
    trailingNodeAux
    trailingNodeFn
    )

namespace Lean.Parser.SyntaxStack

def ofArray (a:Array Syntax) : SyntaxStack :=
  a.foldl SyntaxStack.push .empty

def toArray (s : SyntaxStack) : Array Syntax :=
  s.toSubarray.toArray

instance : Repr SyntaxStack where
  reprPrec s  _ := "SyntaxStack.ofArray " ++ repr s.toArray

instance : Repr SyntaxStack where
  reprPrec a p := reprPrec (a.toSubarray) p

end Lean.Parser.SyntaxStack

namespace Lean.Parser.TokenTable

def addParser (tt : TokenTable) (p : Parser) : TokenTable :=
  let tkns := p.info.collectTokens []
  tkns.foldl (λtt t => tt.insert t t) tt

end Lean.Parser.TokenTable

namespace Strata.Parser

export Lean.Parser (
    InputContext
    Parser
    maxPrec
    minPrec
    skip
    )

def nodeFn (n : SyntaxNodeKind) (p : ParserFn) : ParserFn := fun c s =>
  let iniSz := s.stackSize
  let s     := p c s
  s.mkNode n iniSz

private def emptySourceInfo (c : ParserContext) (pos : String.Pos) : SourceInfo :=
  let empty := c.mkEmptySubstringAt pos
  .original empty pos empty pos

private def optionalFn (p : ParserFn) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let s      := p c s
  let s      := if s.hasError && s.pos == iniPos then s.restore iniSz iniPos else s
  if s.stackSize == iniSz then
    if s.pos != iniPos then
      @panic _ ⟨s⟩ "Unexpected position"
    else
      s.pushSyntax <| .node (emptySourceInfo c s.pos) nullKind #[]
  else
    s.mkNode nullKind iniSz

private def optionalNoAntiquot (p : Parser) : Parser := {
  info := optionalInfo p.info
  fn   := optionalFn p.fn
}

private def node (n : SyntaxNodeKind) (p : Parser) : Parser := {
  info := nodeInfo n p.info,
  fn   := nodeFn n p.fn
}

/--
Create an input context from a string.
-/
def stringInputContext (fileName : System.FilePath) (contents : String) : InputContext where
  inputString := contents
  fileName := fileName.toString
  fileMap  := FileMap.ofString contents

private def isIdFirstOrBeginEscape (c : Char) : Bool :=
  isIdFirst c || isIdBeginEscape c

private def isToken (idStartPos idStopPos : String.Pos) (tk : Option Token) : Bool :=
  match tk with
  | none    => false
  | some tk =>
     -- if a token is both a symbol and a valid identifier (i.e. a keyword),
     -- we want it to be recognized as a symbol
    tk.endPos ≥ idStopPos - idStartPos

/--
Create a trailing node

Note.  The parser maintains the invariant that an argument with minimum precedence p
is filled by a term with precedence q, then q >= p.

Parenthesis can be used to boost precedence in some contexts.

s.lhsPrec is used in trailing nodes to indicate the precedence of the leading node.
To respect the invariant, we need to check that the lhsPrec is at least the minimum
first argument precedence.
-/
def trailingNode (n : SyntaxNodeKind) (prec minLhsPrec : Nat) (p : Parser) : TrailingParser :=
  { info := nodeInfo n p.info
    fn :=
      fun c s =>
        if c.prec ≥ prec then
          s.mkUnexpectedError "unexpected token at this precedence level; consider parenthesizing the term"
        else if s.lhsPrec < minLhsPrec then
          s.mkUnexpectedError "unexpected token at this precedence level; consider parenthesizing the term"
        else
          let s := trailingNodeFn n p.fn c s
          if s.hasError then
            s
          else
            { s with lhsPrec := prec }
  }

variable (pushMissingOnError : Bool) in
partial def finishCommentBlock : ParserFn := fun c s =>
  let i     := s.pos
  if h : c.atEnd i then
    eoi s
  else
    let curr := c.get' i h
    let i    := c.next' i h
    if curr == '*' then
      if h : c.atEnd i then eoi s
      else
        let curr := c.get' i h
        if curr == '/' then -- "*/" end of comment
          s.next' c i h
        else
          finishCommentBlock c (s.setPos i)
    else
      finishCommentBlock c (s.setPos i)
where
  eoi s := s.mkUnexpectedError (pushMissing := pushMissingOnError) "unterminated comment"

/--
Parses a sequence of the form `many (many '_' >> many1 digit)`, but if `needDigit` is true the parsed result must be nonempty.

Note: this does not report that it is expecting `_` if we reach EOI or an unexpected character.
Rationale: this error happens if there is already a `_`, and while sequences of `_` are allowed, it's a bit perverse to suggest extending the sequence.
-/
partial def takeDigitsFn (isDigit : Char → Bool) (expecting : String) (needDigit : Bool) : ParserFn := fun c s =>
  let i     := s.pos
  if h : c.atEnd i then
    if needDigit then
      s.mkEOIError [expecting]
    else
      s
  else
    let curr := c.get' i h
    if curr == '_' then takeDigitsFn isDigit expecting true c (s.next' c i h)
    else if isDigit curr then takeDigitsFn isDigit expecting false c (s.next' c i h)
    else if needDigit then s.mkUnexpectedError "unexpected character" (expected := [expecting])
    else s

/-- Consume whitespace and comments -/
partial def whitespace : ParserFn := fun c s =>
  let i     := s.pos
  if h : c.atEnd i then s
  else
    let curr := c.get' i h
    if curr == '\t' then
      s.mkUnexpectedError (pushMissing := false) "tabs are not allowed; please configure your editor to expand them"
    else if curr == '\r' then
      s.mkUnexpectedError (pushMissing := false) "isolated carriage returns are not allowed"
    else if curr.isWhitespace then whitespace c (s.next' c i h)
    else if curr == '/' then
      let j    := c.next' i h
      let curr := c.get j
      match curr with
      | '/' =>
        match c.tokens.matchPrefix c.inputString i with
        | some _ => s
        | none =>
          andthenFn (takeUntilFn (fun c => c = '\n')) whitespace c (s.next c j)
      | '*' =>
        match c.tokens.matchPrefix c.inputString i with
        | some _ => s
        | none =>
          let j := c.next j
          andthenFn (finishCommentBlock (pushMissingOnError := false)) whitespace c (s.next c j)
      | _ =>
        s
    else s

def mkIdResult (startPos : String.Pos) (val : String) : ParserFn := fun c s =>
  let stopPos         := s.pos
  let rawVal          := c.substring startPos stopPos
  let s               := whitespace c s
  let trailingStopPos := s.pos
  let leading         := c.mkEmptySubstringAt startPos
  let trailing        := c.substring (startPos := stopPos) (stopPos := trailingStopPos)
  let info            := SourceInfo.original leading startPos trailing stopPos
  let atom            := mkIdent info rawVal (.str .anonymous val)
  s.pushSyntax atom

/-- Push `(Syntax.node tk <new-atom>)` onto syntax stack if parse was successful. -/
def mkNodeToken (n : SyntaxNodeKind) (startPos : String.Pos) : ParserFn := fun c s => Id.run do
  if s.hasError then
    return s
  let stopPos   := s.pos
  let leading   := c.mkEmptySubstringAt startPos
  let val       := c.extract startPos stopPos
  let s         := whitespace c s
  let wsStopPos := s.pos
  let trailing  := c.substring (startPos := stopPos) (stopPos := wsStopPos)
  let info      := SourceInfo.original leading startPos trailing stopPos
  s.pushSyntax (Syntax.mkLit n val info)

def mkTokenAndFixPos (startPos : String.Pos) (tk : Option Token) : ParserFn := fun c s =>
  match tk with
  | none    => s.mkErrorAt "token" startPos
  | some tk =>
    if c.forbiddenTk? == some tk then
      s.mkErrorAt "forbidden token" startPos
    else
      let leading   := c.mkEmptySubstringAt startPos
      let stopPos   := startPos + tk
      let s         := s.setPos stopPos
      let s         := whitespace c s
      let wsStopPos := s.pos
      let trailing  := c.substring (startPos := stopPos) (stopPos := wsStopPos)
      let atom      := Parser.mkAtom (SourceInfo.original leading startPos trailing stopPos) tk
      s.pushSyntax atom

def charLitFnAux (startPos : String.Pos) : ParserFn := fun c s =>
  let i     := s.pos
  if h : c.atEnd i then s.mkEOIError
  else
    let curr := c.get' i h
    let s    := s.setPos (c.next' i h)
    let s    := if curr == '\\' then quotedCharFn c s else s
    if s.hasError then s
    else
      let i    := s.pos
      let curr := c.get i
      let s    := s.setPos (c.next i)
      if curr == '\'' then mkNodeToken charLitKind startPos c s
      else s.mkUnexpectedError "missing end of character literal"

def identFnAux (startPos : String.Pos) (tk : Option Token) : ParserFn := fun c s =>
  let i     := s.pos
  if h : c.atEnd i then
    s.mkEOIError
  else
    let curr := c.get' i h
    if isIdBeginEscape curr then
      let startPart := c.next' i h
      let s         := takeUntilFn isIdEndEscape c (s.setPos startPart)
      if h : c.atEnd s.pos then
        s.mkUnexpectedErrorAt "unterminated identifier escape" startPart
      else
        let stopPart  := s.pos
        let s         := s.next' c s.pos h
        if isToken startPos s.pos tk then
          mkTokenAndFixPos startPos tk c s
        else
          let val := c.extract startPart stopPart
          mkIdResult startPos val c s
    else if isIdFirst curr then
      let startPart := i
      let s         := takeWhileFn isIdRest c (s.next c i)
      let stopPart  := s.pos
      if isToken startPos s.pos tk then
        mkTokenAndFixPos startPos tk c s
      else
        let val := c.extract startPart stopPart
        mkIdResult startPos val c s
    else
      mkTokenAndFixPos startPos tk c s

def decimalNumberFn (startPos : String.Pos) (c : ParserContext) : ParserState → ParserState := fun s =>
  let s     := takeDigitsFn (fun c => c.isDigit) "decimal number" false c s
  let i     := s.pos
  if h : c.atEnd i then
    mkNodeToken numLitKind startPos c s
  else
    let curr := c.get' i h
    if curr == '.' || curr == 'e' || curr == 'E' then
      parseScientific s
    else
      mkNodeToken numLitKind startPos c s
where
  parseScientific s :=
    let s := parseOptDot s
    let s := parseOptExp s
    mkNodeToken scientificLitKind startPos c s

  parseOptDot s :=
    let i     := s.pos
    let curr  := c.get i
    if curr == '.' then
      let i    := c.next i
      let curr := c.get i
      if curr.isDigit then
        takeDigitsFn (fun c => c.isDigit) "decimal number" false c (s.setPos i)
      else
        s.setPos i
    else
      s

  parseOptExp s :=
    let i     := s.pos
    let curr  := c.get i
    if curr == 'e' || curr == 'E' then
      let i    := c.next i
      let i    := if c.get i == '-' || c.get i == '+' then c.next i else i
      let curr := c.get i
      if curr.isDigit then
        takeDigitsFn (fun c => c.isDigit) "decimal number" false c (s.setPos i)
      else
        s.mkUnexpectedError "missing exponent digits in scientific literal"
    else
      s

def binNumberFn (startPos : String.Pos) : ParserFn := fun c s =>
  let s := takeDigitsFn (fun c => c == '0' || c == '1') "binary number" true c s
  mkNodeToken numLitKind startPos c s

def octalNumberFn (startPos : String.Pos) : ParserFn := fun c s =>
  let s := takeDigitsFn (fun c => '0' ≤ c && c ≤ '7') "octal number" true c s
  mkNodeToken numLitKind startPos c s

def hexNumberFn (startPos : String.Pos) : ParserFn := fun c s =>
  let s := takeDigitsFn (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')) "hexadecimal number" true c s
  mkNodeToken numLitKind startPos c s

def numberFnAux : ParserFn := fun c s =>
  let startPos := s.pos
  if h : c.atEnd startPos then s.mkEOIError
  else
    let curr := c.get' startPos h
    if curr == '0' then
      let i    := c.next' startPos h
      let curr := c.get i
      if curr == 'b' || curr == 'B' then
        binNumberFn startPos c (s.next c i)
      else if curr == 'o' || curr == 'O' then
        octalNumberFn startPos c (s.next c i)
      else if curr == 'x' || curr == 'X' then
        hexNumberFn startPos c (s.next c i)
      else
        decimalNumberFn startPos c (s.setPos i)
    else if curr.isDigit then
      decimalNumberFn startPos c (s.next c startPos)
    else
      s.mkError "numeral"

partial def strLitFnAux (startPos : String.Pos) : ParserFn := fun c s =>
  let i     := s.pos
  if h : c.atEnd i then s.mkUnexpectedErrorAt "unterminated string literal" startPos
  else
    let curr := c.get' i h
    let s    := s.setPos (c.next' i h)
    if curr == '\"' then
      mkNodeToken strLitKind startPos c s
    else if curr == '\\' then andthenFn quotedStringFn (strLitFnAux startPos) c s
    else strLitFnAux startPos c s

private def tokenFnAux : ParserFn := fun c s =>
  let i     := s.pos
  let curr  := c.get i
  if curr == '\"' then
    strLitFnAux i c (s.next c i)
  else if curr == '\'' && getNext c.inputString i != '\'' then
    charLitFnAux i c (s.next c i)
  else if curr.isDigit then
    numberFnAux c s
  else
    let tk := c.tokens.matchPrefix c.inputString i
    identFnAux i tk c s

private def updateTokenCache (startPos : String.Pos) (s : ParserState) : ParserState :=
  -- do not cache token parsing errors, which are rare and usually fatal and thus not worth an extra field in `TokenCache`
  match s with
  | ⟨stack, lhsPrec, pos, ⟨_, catCache⟩, none, errs⟩ =>
    if stack.size == 0 then s
    else
      let tk := stack.back
      ⟨stack, lhsPrec, pos, ⟨{ startPos := startPos, stopPos := pos, token := tk }, catCache⟩, none, errs⟩
  | other => other

def tokenFn (expected : List String := []) : ParserFn := fun c s =>
  let i     := s.pos
  if c.atEnd i then
    s.mkEOIError expected
  else
    let tkc := s.cache.tokenCache
    if tkc.startPos == i then
      let s := s.pushSyntax tkc.token
      s.setPos tkc.stopPos
    else
      let s := tokenFnAux c s
      updateTokenCache i s

/--
  Parses a token and asserts the result is of the given kind.
  `desc` is used in error messages as the token kind. -/
def expectTokenFn (k : SyntaxNodeKind) (desc : String) : ParserFn := fun c s =>
  let s := tokenFn [desc] c s
  if !s.hasError && !(s.stxStack.back.isOfKind k) then s.mkUnexpectedTokenError desc else s

def satisfySymbolFn (p : String → Bool) (expected : List String) : ParserFn := fun c s => Id.run do
  let iniPos := s.pos
  let s := tokenFn expected c s
  if s.hasError then
    return s
  if let .atom _ sym := s.stxStack.back then
    if p sym then
      return s
  -- this is a very hot `mkUnexpectedTokenErrors` call, so explicitly pass `iniPos`
  s.mkUnexpectedTokenErrors expected iniPos

def symbolFnAux (sym : String) (errorMsg : String) : ParserFn :=
  satisfySymbolFn (fun s => s == sym) [errorMsg]

def symbolFn (sym : String) : ParserFn :=
  symbolFnAux sym ("'" ++ sym ++ "'")

def symbolNoAntiquot (sym : String) : Parser :=
  { info := symbolInfo sym
    fn   := symbolFn sym }

def identifier : Parser := {
  fn   := fun ctx s =>
    let s := tokenFn ["identifier"] ctx s
    if s.hasError then
      s
    else if let .ident _ _ (.str .anonymous _) _ := s.stxStack.back then
      s
    else
      s.mkUnexpectedTokenError "identifier"
  info := mkAtomicInfo "ident"
}

def numLit : Parser := {
  fn   := expectTokenFn numLitKind "numeral"
  info := mkAtomicInfo "num"
}

def decimalLit : Parser := {
  fn   := expectTokenFn scientificLitKind "scientific number"
  info := mkAtomicInfo "scientific"
}

def strLit : Parser := {
  fn   := expectTokenFn strLitKind "string literal"
  info := mkAtomicInfo "str"
}

def identName (nm : QualifiedIdent) : Lean.Name :=
  Name.anonymous |>.str nm.dialect |>.str nm.name

def peekTokenAux (c : ParserContext) (s : ParserState) : ParserState × Except ParserState Syntax :=
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let s      := tokenFn [] c s
  if let some _ := s.errorMsg then (s.restore iniSz iniPos, .error s)
  else
    let stx := s.stxStack.back
    (s.restore iniSz iniPos, .ok stx)

def peekToken (c : ParserContext) (s : ParserState) : ParserState × Except ParserState Syntax :=
  let tkc := s.cache.tokenCache
  if tkc.startPos == s.pos then
    (s, .ok tkc.token)
  else
    peekTokenAux c s

def indexed {α : Type} (map : TokenMap α) (c : ParserContext) (s : ParserState) (behavior : LeadingIdentBehavior) : ParserState × List α :=
  let (s, stx) := peekToken c s
  let find (n : Name) : ParserState × List α := (s,  map.getD n [])
  match stx with
  | .ok (.atom _ sym)      => find (.mkSimple sym)
  | .ok (.ident _ _ val _) =>
    match behavior with
    | .default => find identKind
    | .symbol =>
      match map.get? val with
      | some as => (s, as)
      | none    => find identKind
    | .both =>
      match map.get? val with
      | some as =>
        if val == identKind then
          (s, as)  -- avoid running the same parsers twice
        else
          match map.get? identKind with
          | some as' => (s, as ++ as')
          | _        => (s, as)
      | none    => find identKind
  | .ok (.node _ k _) => find k
  | .ok _             => (s, [])
  | .error s'         => (s', [])

def longestMatchMkResult (startSize : Nat) (s : ParserState) : ParserState :=
  if s.stackSize > startSize + 1 then s.mkNode choiceKind startSize else s

def longestMatchFnAux (left? : Option Syntax) (startSize startLhsPrec : Nat) (startPos : String.Pos) (prevPrio : Nat) (ps : List (Parser × Nat)) : ParserFn :=
  let rec parse (prevPrio : Nat) (ps : List (Parser × Nat)) :=
    match ps with
    | []    => fun _ s => longestMatchMkResult startSize s
    | p::ps => fun c s =>
      let (s, prevPrio) := longestMatchStep left? startSize startLhsPrec startPos prevPrio p.2 p.1.fn c s
      parse prevPrio ps c s
  parse prevPrio ps

def longestMatchFn (left? : Option Syntax) : List (Parser × Nat) → ParserFn
  | []    => fun _ s => s.mkError "longestMatch: empty list"
  | [p]   => fun c s => runLongestMatchParser left? s.lhsPrec p.1.fn c s
  | p::ps => fun c s =>
    let startSize := s.stackSize
    let startLhsPrec := s.lhsPrec
    let startPos  := s.pos
    let s         := runLongestMatchParser left? s.lhsPrec p.1.fn c s
    longestMatchFnAux left? startSize startLhsPrec startPos p.2 ps c s

def leadingParserAux (cat : QualifiedIdent) (tables : PrattParsingTables) (behavior : LeadingIdentBehavior) : ParserFn := fun c s => Id.run do
  let iniSz   := s.stackSize
  let (s, ps) := indexed tables.leadingTable c s behavior
  if s.hasError then
    return s
  let ps      := tables.leadingParsers ++ ps
  if ps.isEmpty then
    -- if there are no applicable parsers, consume the leading token and flag it as unexpected at this position
    let s := tokenFn [cat.fullName] c s
    if s.hasError then
      return s
    return s.mkUnexpectedTokenError cat.fullName
  let s := longestMatchFn none ps c s
  if s.stackSize == iniSz + 1 then
    s
  else
    s.setError (panic! "Unexpected stack size")

partial def trailingLoop (cat : QualifiedIdent) (tables : PrattParsingTables) (c : ParserContext) (s : ParserState) : ParserState := Id.run do
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let (s, ps)       := indexed tables.trailingTable c s LeadingIdentBehavior.default
  if s.hasError then
    -- Discard token parse errors and break the trailing loop instead.
    -- The error will be flagged when the next leading position is parsed, unless the token
    -- is in fact valid there (e.g. EOI at command level, no-longer forbidden token)
    return s.restore iniSz iniPos
  if ps.isEmpty && tables.trailingParsers.isEmpty then
    return s -- no available trailing parser
  let left   := s.stxStack.back
  let s      := s.popSyntax
  let ps     := ps ++ tables.trailingParsers
  let s      := longestMatchFn left ps c s
  if s.hasError then
    -- Discard non-consuming parse errors and break the trailing loop instead, restoring `left`.
    -- This is necessary for fallback parsers like `app` that pretend to be always applicable.
    return if s.pos == iniPos then s.restore (iniSz - 1) iniPos |>.pushSyntax left else s
  trailingLoop cat tables c s

/--

  Implements a variant of Pratt's algorithm. In Pratt's algorithms tokens have a right and left binding power.
  In our implementation, parsers have precedence instead. This method selects a parser (or more, via
  `longestMatchFn`) from `leadingTable` based on the current token. Note that the unindexed `leadingParsers` parsers
  are also tried. We have the unidexed `leadingParsers` because some parsers do not have a "first token". Example:
  ```
  syntax term:51 "≤" ident "<" term "|" term : index
  ```
  Example, in principle, the set of first tokens for this parser is any token that can start a term, but this set
  is always changing. Thus, this parsing rule is stored as an unindexed leading parser at `leadingParsers`.
  After processing the leading parser, we chain with parsers from `trailingTable`/`trailingParsers` that have precedence
  at least `c.prec` where `c` is the `ParsingContext`. Recall that `c.prec` is set by `categoryParser`.

  Note that in the original Pratt's algorithm, precedences are only checked before calling trailing parsers. In our
  implementation, leading *and* trailing parsers check the precedence. We claim our algorithm is more flexible,
  modular and easier to understand.

  `antiquotParser` should be a `mkAntiquot` parser (or always fail) and is tried before all other parsers.
  It should not be added to the regular leading parsers because it would heavily
  overlap with antiquotation parsers nested inside them. -/
def prattParser (cat : QualifiedIdent) (tables : PrattParsingTables) (behavior : LeadingIdentBehavior) : ParserFn := fun c s =>
  let s := leadingParserAux cat tables behavior c s
  if s.hasError then
    s
  else
    trailingLoop cat tables c s

def dynamicParser (cat : QualifiedIdent) : Parser :=
  { fn := fun c s =>
    let parserState := parserExt.getState c.env
    match parserState[cat]? with
    | some tables =>
      prattParser cat tables .both c s
    | none =>
      s.mkUnexpectedError s!"Unknown category {cat.fullName}"
  }

/--
Describes the atoms in a pattern to identify left-recusive
syntax.
-/
inductive LhsRec where
/-- This atom is not left-recursive and uses the `seq` atoms. -/
| isLeading (atoms : List SyntaxDefAtom)
/--
This atom is left-recursive  The initial argument must have
precedence ≥ prec.  The remaining syntax is given.
-/
| isTrailing (minArgPrec : Nat) (remaining : List SyntaxDefAtom)
/-- Classification failed with message -/
| invalid (message : StrataFormat)
deriving Inhabited

private partial
def checkLeftRec (thisCatName : QualifiedIdent) (argDecls : ArgDecls) (as : List SyntaxDefAtom) : LhsRec :=
  match as with
  | [] =>
    .isLeading []
  | .indent _ as :: bs =>
    checkLeftRec thisCatName argDecls (as.toList ++ bs)
  | .str _ :: _ =>
    .isLeading as
  | .ident v argPrec :: rest => Id.run do
    let .isTrue lt := inferInstanceAs (Decidable (v < argDecls.size))
      | return panic! "Invalid index"
    let cat := argDecls[v].kind.categoryOf
    match cat.name with
    | q`Init.CommaSepBy =>
      assert! cat.args.size = 1
      let c := cat.args[0]!
      if c.name == thisCatName then
        .invalid mf!"Leading symbol cannot be recursive call to {c}"
      else
        .isLeading as
    | q`Init.Option =>
      assert! cat.args.size = 1
      let c := cat.args[0]!
      if c.name == thisCatName then
        .invalid mf!"Leading symbol cannot be recursive call to {c}"
      else
        .isLeading as
    | q`Init.Seq =>
      assert! cat.args.size = 1
      let c := cat.args[0]!
      if c.name == thisCatName then
        .invalid mf!"Leading symbol cannot be recursive call to {c}"
      else
        .isLeading as
    | qid =>
      if cat.args.size > 0 then
        panic! s!"Unknown parametric category '{eformat cat}' is not supported."
      if qid == thisCatName then
        .isTrailing (min (argPrec+1) maxPrec) rest
      else
        .isLeading as

/--
Information about a parser.
-/
structure DeclParser where
  category : QualifiedIdent
  outerPrec : Nat
  isLeading : Bool
  parser : Parser

class ParsingContext where
  fixedParsers : Std.HashMap QualifiedIdent Parser := {}
  deriving Inhabited

namespace ParsingContext

def add (ctx : ParsingContext) (cat : QualifiedIdent) (p : Parser) : ParsingContext :=
  assert! cat ∉ ctx.fixedParsers
  { fixedParsers := ctx.fixedParsers.insert cat p }

/-- Parser function for given syntax category -/
def atomCatParser (ctx : ParsingContext) (cat : QualifiedIdent) : Parser :=
  if let some p := ctx.fixedParsers[cat]? then
    p
  else
    dynamicParser cat

private def sepByParser (p sep : Parser) (allowTrailingSep : Bool := false) : Parser := {
  info := sepByInfo p.info sep.info
  fn   := fun c s =>
    let s := sepByFn allowTrailingSep p.fn sep.fn c s
    if s.hasError then
      s
    else
      match s.stxStack.back with
      | .node .none k args =>
        if args.isEmpty then
          s.popSyntax.pushSyntax (.node (emptySourceInfo c s.pos) k args)
        else
          s
      | _ =>
        s
}

def manyParser (p : Parser) : Parser := {
  info := noFirstTokenInfo p.info
  fn   := fun c s =>
    let s := manyFn p.fn c s
    if s.hasError then
      s
    else
      match s.stxStack.back with
      | .node .none k args =>
        if args.isEmpty then
          s.popSyntax.pushSyntax (.node (emptySourceInfo c s.pos) k args)
        else
          s
      | _ =>
        s
}

/-- Parser function for given syntax category -/
partial def catParser (ctx : ParsingContext) (cat : SyntaxCat) : Except SyntaxCat Parser :=
  match cat.name with
  | q`Init.CommaSepBy =>
    assert! cat.args.size = 1
    (sepByParser · (symbolNoAntiquot ",")) <$> catParser ctx cat.args[0]!
  | q`Init.Option =>
    assert! cat.args.size = 1
    optionalNoAntiquot <$> catParser ctx cat.args[0]!
  | q`Init.Seq =>
    assert! cat.args.size = 1
    manyParser <$> catParser ctx cat.args[0]!
  | qid =>
    if cat.args.isEmpty then
      .ok (atomCatParser ctx qid)
    else
      .error cat
/-
This walks the SyntaxDefAtomParser and prepends extracted parser to state.

This is essentially a right-to-left fold and is implemented so that the parser starts with
the first symbol.
-/
private def prependSyntaxDefAtomParser (ctx : ParsingContext) (argDecls : ArgDecls) (o : SyntaxDefAtom) (r : Parser) : Parser :=
  match o with
  | .ident v prec => Id.run do
    let .isTrue lt := inferInstanceAs (Decidable (v < argDecls.size))
      | return panic! s!"Invalid ident index {v} in bindings {eformat argDecls}"
    let addParser (p : Parser) :=
      let q : Parser := Lean.Parser.adaptCacheableContext ({ · with prec }) p
      q >> r
    match catParser ctx argDecls[v].kind.categoryOf with
    | .ok p =>
      addParser p
    | .error c =>
      panic! s!"Category '{eformat c}' is not supported."
  | .str l =>
    let l := l.trim
    if l.isEmpty then
      r
    else
      symbolNoAntiquot l >> r
  | .indent _ p =>
    p.attach.foldr (init := r) fun ⟨e, _⟩ r => prependSyntaxDefAtomParser ctx argDecls e r

private def liftToKind (ctx : ParsingContext) (o : List SyntaxDefAtom) (argDecls : ArgDecls) : Parser :=
  o.foldr (init := skip) (prependSyntaxDefAtomParser ctx argDecls)

def opSyntaxParser (ctx : ParsingContext)
                   (category : QualifiedIdent)
                   (ident : QualifiedIdent)
                   (argDecls : ArgDecls)
                   (opStx : SyntaxDef) : Except StrataFormat DeclParser := do
  let n := identName ident
  let prec := opStx.prec
  match checkLeftRec category argDecls opStx.atoms.toList with
  | .invalid mf => throw mf
  | .isTrailing minLeftPrec args =>
    if args.isEmpty then
      throw mf!"invalid atomic left recursive syntax"
    let p := liftToKind ctx args argDecls
    -- Run parsers so far and append parser for next op.
    -- Parser for creating top level node
    pure {
      category,
      outerPrec := prec,
      isLeading := false,
      parser := trailingNode n prec minLeftPrec p
    }
  | .isLeading [] =>
    let fn (c : ParserContext) (s : ParserState) : ParserState :=
      s.pushSyntax (.atom (emptySourceInfo c s.pos) "")
    pure {
      category,
      outerPrec := prec,
      isLeading := true,
      parser := node n { fn := fn } >> setLhsPrec prec
    }
  | .isLeading args =>
    let p := liftToKind ctx args argDecls
    -- Parser for creating top level node
    pure {
      category,
      outerPrec := prec,
      isLeading := true,
      parser := node n p >> setLhsPrec prec
    }

def fnDeclParser (ctx : ParsingContext) (dialect : DialectName) (decl : FunctionDecl) : Except StrataFormat DeclParser := do
  let ident := { dialect, name := decl.name }
  ctx.opSyntaxParser q`Init.Expr ident decl.argDecls decl.syntaxDef

def opDeclParser (ctx : ParsingContext) (dialect : DialectName) (decl : OpDecl) : Except StrataFormat DeclParser := do
  let cat := decl.category
  let ident := { dialect, name := decl.name }
  ctx.opSyntaxParser cat ident decl.argDecls decl.syntaxDef

def mkDialectParsers (ctx : ParsingContext) (d : Dialect) : Except StrataFormat (Array DeclParser) := do
  let dialect := d.name
  let addParser (a : Array DeclParser) (decl : Decl) : Except StrataFormat (Array DeclParser) :=
        match decl with
        -- Types and syncats are not stored in parset state.
        | .type _ | .syncat _ | .metadata _ => pure a
        | .function decl => return a.push (← ctx.fnDeclParser dialect decl)
        | .op decl => return a.push (← ctx.opDeclParser dialect decl)
  d.declarations.foldlM (init := #[]) addParser

end ParsingContext

structure ParserState where
  -- Dynamic parser categories
  categoryMap : PrattParsingTableMap := {}
  deriving Inhabited

def runCatParser (tokenTable : TokenTable)
                 (parsingTableMap : PrattParsingTableMap)
                 (leanEnv : Lean.Environment)
                 (inputContext : InputContext)
                 (pos stopPos : String.Pos) (cat : QualifiedIdent) : Lean.Parser.ParserState :=
  let leanEnv := parserExt.modifyState leanEnv (fun _ => parsingTableMap)
  let pmc : ParserModuleContext := { env := leanEnv, options := {} }
  let leanParserState : Lean.Parser.ParserState := {
    pos      := pos
    cache    := {
        tokenCache := { startPos := stopPos + ' ' }
        parserCache := {}
    }
  }
  let p := dynamicParser cat
  p.fn.run inputContext pmc tokenTable leanParserState

end Strata.Parser
