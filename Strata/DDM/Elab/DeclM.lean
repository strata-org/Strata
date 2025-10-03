/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab.LoadedDialects
import Strata.DDM.Parser
import Strata.DDM.Util.Lean

set_option autoImplicit false

open Lean (Syntax Message)

open Strata.Parser (DeclParser InputContext Parser ParsingContext ParserState)

namespace Strata

def infoSourceRange (info : Lean.SourceInfo) : Option SourceRange :=
  match info with
  | .original (pos := pos) (endPos := endPos) ..
  | .synthetic (pos := pos) (endPos := endPos) .. =>
    some { start := pos, stop := endPos }
  | .none  => none

def sourceLocPos (stx:Syntax) : Option String.Pos :=
  match stx with
  | .atom info .. | .ident info .. =>
    infoSourceRange info |>.map (·.start)
  | .node info _kind args  =>
    match infoSourceRange info with
    | some loc =>
      some loc.start
    | .none  =>
      if h : args.size > 0 then
        sourceLocPos args[0]
      else
        none
  | .missing => none

def sourceLocEnd (stx:Syntax) : Option String.Pos :=
  match stx with
  | .atom info ..  | .ident info .. =>
    infoSourceRange info |>.map (·.stop)
  | .node info _kind args  =>
    match infoSourceRange info with
    | some loc =>
      some loc.stop
    | .none  =>
      if h : args.size > 0 then
        sourceLocEnd args[args.size - 1]
      else
        none
  | .missing => none

def mkSourceRange? (stx:Syntax) : Option SourceRange :=
  match stx with
  | .atom info ..  | .ident info .. =>
    infoSourceRange info
  | .node info _kind args  =>
    match infoSourceRange info with
    | some loc => some loc
    | none  =>
      match h : args.size with
      | 0 => none
      | 1 => mkSourceRange? args[0]
      | Nat.succ n => Id.run do
        let some s := sourceLocPos args[0]
          | return none
        let some t := sourceLocEnd args[n]
          | return none
        some { start := s, stop := t }
  | .missing => none

namespace PrattParsingTableMap

def addSynCat! (tables : PrattParsingTableMap) (dialect : String) (decl : SynCatDecl) : PrattParsingTableMap :=
  let cat : QualifiedIdent := { dialect, name := decl.name }
  if cat ∈ tables then
    panic! s!"{cat} already declared."
  else
    tables.insert cat {}

def addParserToCat! (tables : PrattParsingTableMap) (dp : DeclParser) : PrattParsingTableMap :=
  tables.alter dp.category fun mtables =>
    match mtables with
    | none => panic s!"Category {dp.category.fullName} not declared."
    | some tables =>
      let r := tables |>.addParser dp.isLeading dp.parser dp.outerPrec
      some r

def addDialect! (tables : PrattParsingTableMap) (dialect : Dialect) (parsers : Array DeclParser) : PrattParsingTableMap :=
  dialect.syncats.fold (init := tables) (·.addSynCat! dialect.name ·)
  |> parsers.foldl PrattParsingTableMap.addParserToCat!

end PrattParsingTableMap

namespace Elab

-- Metadata syntax

syntax "md{" withoutPosition(sepBy(term, ", ")) "}" : term

macro_rules
  | `(md{ $elems,* }) => `(Metadata.ofArray (List.toArray [ $elems,* ]))

-- ElabClass

class ElabClass (m : Type → Type) extends Monad m where
  getInputContext : m InputContext
  getDialects : m DialectMap
  getOpenDialects : m (Std.HashSet DialectName)
  getGlobalContext : m GlobalContext
  getErrorCount : m Nat
  logErrorMessage : Message → m Unit

export ElabClass (logErrorMessage)

/-
Runs action and returns result along with Bool that is true if
action ran without producing errors.
-/
def runChecked {m α} [ElabClass m] (action : m α) : m (α × Bool) := do
  let errorCount ← ElabClass.getErrorCount
  let r ← action
  return (r, errorCount = (← ElabClass.getErrorCount))

def logError {m} [ElabClass m] (loc : SourceRange) (msg : String) : m Unit := do
  let inputCtx ← ElabClass.getInputContext
  let m := Lean.mkStringMessage inputCtx loc.start msg
  let m := if loc.isNone then m else { m with endPos := inputCtx.fileMap.toPosition loc.stop }
  logErrorMessage m

def logErrorMF {m} [ElabClass m] (loc : SourceRange) (msg : StrataFormat) : m Unit := do
  let c : FormatContext := .ofDialects (← ElabClass.getDialects) (← ElabClass.getGlobalContext) {}
  let s : FormatState := { openDialects := ← ElabClass.getOpenDialects }
  logError loc (msg c s |>.format |>.pretty)

-- DeclM

structure DeclContext where
  inputContext : InputContext
  stopPos : String.Pos
  -- Map from dialect names to the dialect definition
  loader : LoadedDialects

namespace DeclContext

def empty : DeclContext where
  inputContext := default
  loader := .empty
  stopPos := 0

end DeclContext

/-- Represents an entity with some form of unique string name. -/
class NamedValue (α : Type) where
  name : α → String

abbrev ValueWithName (α : Type) [NamedValue α] (name : String) :=
  { d : α // NamedValue.name d = name }

/--
  Map metadata attribute names to any declarations with that name that
  are in the current scope.
-/
structure NamedValueMap (α : Type) [NamedValue α] where
  map : Std.DHashMap String (λname => Array (DialectName × ValueWithName α name)) := {}
deriving Inhabited

/--
  Map metadata attribute names to any declarations with that name that
  are in the current scope.
-/
structure MetadataDeclMap where
  map : Std.DHashMap String fun name =>
          Array (DialectName × { d : MetadataDecl // d.name = name }) :=
    {}
deriving Inhabited

namespace MetadataDeclMap

def add (m : MetadataDeclMap) (dialect : DialectName) (decl : MetadataDecl) : MetadataDeclMap where
  map := m.map.alter decl.name fun ma => some <| ma.getD #[] |>.push (dialect, ⟨decl, rfl⟩)

def addDialect (m : MetadataDeclMap) (dialect : Dialect) :=
  dialect.metadata.fold (init := m) (·.add dialect.name ·)

def get (m : MetadataDeclMap) (name : String) : Array (DialectName × { d : MetadataDecl // d.name = name }) :=
  m.map.getD name #[]

end MetadataDeclMap

inductive TypeOrCatDecl where
| syncat (d : SynCatDecl)
| type (d : TypeDecl)
deriving Inhabited

def TypeOrCatDecl.name : TypeOrCatDecl → String
| .syncat d => d.name
| .type d => d.name

def TypeOrCatDecl.decl : TypeOrCatDecl → Decl
| .syncat d => .syncat d
| .type d => .type d

/--
  Map metadata attribute names to any declarations with that name that
  are in the current scope.
-/
structure TypeOrCatDeclMap where
  map : Std.DHashMap String fun name =>
          Array (DialectName × { d : TypeOrCatDecl // d.name = name }) :=
    {}
deriving Inhabited

namespace TypeOrCatDeclMap

def add (m : TypeOrCatDeclMap) (dialect : DialectName) (decl : TypeOrCatDecl) : TypeOrCatDeclMap where
  map := m.map.alter decl.name fun ma => some <| ma.getD #[] |>.push (dialect, ⟨decl, rfl⟩)

def addSynCat (m : TypeOrCatDeclMap) (dialect : DialectName) (d : SynCatDecl) :=
  m.add dialect (.syncat d)

def addType (m : TypeOrCatDeclMap) (dialect : DialectName) (d : TypeDecl) :=
  m.add dialect (.type d)

def addDialect (m : TypeOrCatDeclMap) (dialect : Dialect) :=
  let m := dialect.syncats.fold (init := m) (·.addSynCat dialect.name ·)
  dialect.types.fold (init := m) (·.addType dialect.name ·)

def get (m : TypeOrCatDeclMap) (name : String) : Array (DialectName × { d : TypeOrCatDecl // d.name = name }) :=
  m.map.getD name #[]

end TypeOrCatDeclMap

structure DeclState where
  -- Fixed parser map
  fixedParsers : ParsingContext := {}
  -- Dialects considered open for pretty-printing purposes.
  openDialects : Array DialectName := #["Init"]
  -- List of dialects considered open.
  openDialectSet : Std.HashSet DialectName := .ofArray openDialects
  /-- Map for looking up types and categories by name. -/
  typeOrCatDeclMap : TypeOrCatDeclMap := {}
  /-- Map for looking up metadata by name. -/
  metadataDeclMap : MetadataDeclMap := {}
  -- Dynamic parser categories
  parserMap : PrattParsingTableMap := {}
  -- Token table for parsing
  tokenTable : Lean.Parser.TokenTable := {}
  -- Operations at the global level
  globalContext : GlobalContext := {}
  -- String position in file.
  pos : String.Pos := 0
  -- Errors found in elaboration.
  errors : Array Message := #[]
  deriving Inhabited

namespace DeclState

def addParserToCat! (s : DeclState) (dp : DeclParser) : DeclState :=
  assert! dp.category ∈ s.parserMap
  { s with
      tokenTable := s.tokenTable.addParser dp.parser
      parserMap := s.parserMap.addParserToCat! dp
  }

def addSynCat! (s : DeclState) (dialect : String) (decl : SynCatDecl) : DeclState :=
  { s with parserMap := s.parserMap.addSynCat! dialect decl }

/--
Opens the dialect definition dialect in the parser so it is visible to parser, but not
part of environment.  This is used for dialect definitions.
-/
def openParserDialect! (s : DeclState) (loader : LoadedDialects) (dialect : Dialect) : DeclState :=
  let name := dialect.name
  let parsers := loader.dialectParsers.getD name #[]
  { s with
    metadataDeclMap := s.metadataDeclMap.addDialect dialect
    parserMap := s.parserMap.addDialect! dialect parsers
    tokenTable := parsers.foldl (init := s.tokenTable) (·.addParser ·.parser)
  }

mutual

partial def ensureLoaded! (s : DeclState) (loaded : LoadedDialects) (dialect : DialectName) : DeclState :=
  if dialect ∈ s.openDialectSet then
    s
  else
    match loaded.dialects[dialect]? with
    | none => panic! s!"Unknown dialect {dialect}"
    | some d => addDialect! s loaded d

/--
Opens the dialect (not must not already be open)
-/
partial def addDialect! (s : DeclState) (loaded : LoadedDialects) (dialect : Dialect) : DeclState :=
  assert! dialect.name ∉ s.openDialectSet
  let s := dialect.imports.foldl (init := s) fun s d =>
      assert! d ≠ dialect.name
      ensureLoaded! s loaded d
  let s := { s with
    openDialects := s.openDialects.push dialect.name
    openDialectSet := s.openDialectSet.insert dialect.name
    typeOrCatDeclMap := s.typeOrCatDeclMap.addDialect dialect
  }
  s.openParserDialect! loaded dialect

end

/--
Opens the dialect (not must not already be open)
-/
partial def openLoadedDialect! (s : DeclState) (loaded : LoadedDialects) (dialect : Dialect) : DeclState :=
  if dialect.name ∈ s.openDialectSet then
    panic s!"Dialect {dialect.name} already open"
  else
    s.addDialect! loaded dialect

end DeclState

@[reducible]
def DeclM := ReaderT DeclContext (StateM DeclState)

namespace DeclM

instance : ElabClass DeclM where
  getInputContext := return (←read).inputContext
  getDialects := return (←read).loader.dialects
  getOpenDialects := return (←get).openDialectSet
  getGlobalContext := return (←get).globalContext
  getErrorCount := return (←get).errors.size
  logErrorMessage msg :=
    modify fun s => { s with errors := s.errors.push msg }

end DeclM

def addTypeOrCatDecl (dialect : DialectName) (tpcd : TypeOrCatDecl) : DeclM Unit := do
  modify fun s => {
    s with typeOrCatDeclMap := s.typeOrCatDeclMap.add dialect tpcd
  }
