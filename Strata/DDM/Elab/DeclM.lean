/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

import Strata.DDM.Parser
import Strata.DDM.Util.Lean

open Lean (Syntax Message)

open Strata.Parser (DeclParser InputContext Parser ParsingContext ParserState)

namespace Strata

namespace Elab

/--
Describes an elaboration relationship between a argument in the bindings and
the syntax node.
-/
structure ArgElaborator where
  -- Index of this argument to elaborator in syntax tree.
  syntaxLevel : Nat
  -- Level of argument in bindings.
  argLevel : Nat
  -- Index of argument to use for typing context (if specified, must be less than argIndex)
  contextLevel : Option (Fin argLevel) := .none
deriving Inhabited, Repr

def mkArgElab (bindings : DeclBindings) (syntaxLevel : Nat) (argLevel : Fin bindings.size) : ArgElaborator :=
  let contextLevel : Option (Fin argLevel) := bindings.argScopeLevel argLevel
  { argLevel := argLevel.val, syntaxLevel, contextLevel }

def addElaborators (bindings : DeclBindings) (p : Nat × Array ArgElaborator) (a : SyntaxDefAtom) : Nat × Array ArgElaborator :=
  match a with
  | .ident level _prec =>
    let (si, es) := p
    if h : level < bindings.size then
      let argElab := mkArgElab bindings si ⟨level, h⟩
      (si + 1, es.push argElab)
    else
      panic! "Invalid index"
  | .str _ =>
    let (si, es) := p
    (si + 1, es)
  | .indent _ as =>
    as.attach.foldl (init := p) (fun p ⟨a, _⟩ => addElaborators bindings p a)

/-- Information needed to elaborator operations or functions. -/
structure SyntaxElaborator where
  argElaborators : Array ArgElaborator
  resultScope : Option Nat
deriving Inhabited, Repr

def mkElaborators (bindings : DeclBindings) (as : Array SyntaxDefAtom) : Array ArgElaborator :=
  let init : Array ArgElaborator := Array.mkEmpty bindings.size
  let (_, es) := as.foldl (init := (0, init)) (addElaborators bindings)
  es.qsort (fun x y => x.argLevel < y.argLevel)

def mkSyntaxElab (bindings : DeclBindings) (stx : SyntaxDef) (opMd : Metadata) : SyntaxElaborator := {
    argElaborators := mkElaborators bindings stx.atoms,
    resultScope := opMd.resultLevel bindings.size,
  }

def opDeclElaborator (decl : OpDecl) : SyntaxElaborator :=
  mkSyntaxElab decl.argDecls decl.syntaxDef decl.metadata

def fnDeclElaborator (decl : FunctionDecl) : SyntaxElaborator :=
  mkSyntaxElab decl.argDecls decl.syntaxDef decl.metadata

abbrev SyntaxElabMap := Std.HashMap QualifiedIdent SyntaxElaborator

def SyntaxElabMap.add (m : SyntaxElabMap) (dialect : String) (name : String) (se : SyntaxElaborator) : SyntaxElabMap :=
  m.insert { dialect, name := name } se

def SyntaxElabMap.addDecl (m : SyntaxElabMap) (dialect : String) (d : Decl) : SyntaxElabMap :=
  match d with
  | .op d => m.add dialect d.name (opDeclElaborator d)
  | .function d => m.add dialect d.name (fnDeclElaborator d)
  | _ => m

def SyntaxElabMap.addDialect (m : SyntaxElabMap) (d : Dialect) : SyntaxElabMap :=
  d.declarations.foldl (·.addDecl d.name) m

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
  logErrorMessage : Syntax → Message → m Unit

export ElabClass (logErrorMessage)

/-
Runs action and returns result along with Bool that is true if
action ran without producing errors.
-/
def runChecked [ElabClass m] (action : m α) : m (α × Bool) := do
  let errorCount ← ElabClass.getErrorCount
  let r ← action
  return (r, errorCount = (← ElabClass.getErrorCount))

def logError [ElabClass m] (stx : Syntax) (msg : String) : m Unit := do
  let pos := stx.getHeadInfo.getPos?.getD 0
  let inputCtx ← ElabClass.getInputContext
  logErrorMessage stx <| Lean.mkStringMessage inputCtx pos msg

def logErrorMF [ElabClass m] (stx : Syntax) (msg : StrataFormat) : m Unit := do
  let c : FormatContext := .ofDialects (← ElabClass.getDialects) (← ElabClass.getGlobalContext) {}
  let s : FormatState := { openDialects := ← ElabClass.getOpenDialects }
  logError stx (msg c s |>.format |>.pretty)

-- DeclM

structure DeclContext where
  inputContext : InputContext
  stopPos : String.Pos

def DeclContext.empty : DeclContext where
  inputContext := default
  stopPos := 0

abbrev DialectParsers := Std.HashMap DialectName (Array DeclParser)
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





def DialectParsers.addDialect! (pm : DialectParsers) (pctx : ParsingContext) (dialect : Dialect) : DialectParsers :=
  match pctx.mkDialectParsers dialect with
  | .error msg =>
    @panic _ ⟨pm⟩ s!"Could not add open dialect: {eformat msg |>.pretty}"
  | .ok parsers => pm.insert dialect.name parsers

structure DialectLoader where
  /--- Map from dialect names to the dialect definition. -/
  dialects : DialectMap := {}
  /-- Parsers for dialects in map. -/
  dialectParsers : DialectParsers := {}
  /--/ Map for elaborating operations and functions. -/
  syntaxElabMap : SyntaxElabMap := {}
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
  -- Map from dialect names to the dialect definition
  loader : DialectLoader := {}
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
  -- Top level commands in file.
  commands : Array Operation := #[]
  -- Operations at the global level
  globalContext : GlobalContext := {}
  -- String position in file.
  pos : String.Pos := 0
  -- Errors found in elaboration.
  errors : Array (Syntax × Message) := #[]
  deriving Inhabited

namespace DeclState

def dialects (s : DeclState) := s.loader.dialects

/-- Parsers for dialects in map. -/
def dialectParsers (s : DeclState) := s.loader.dialectParsers

/-- Map for elaborating operations and functions -/
def syntaxElabMap (s : DeclState) := s.loader.syntaxElabMap

def mkEnv (s : DeclState) : Environment := {
      dialects := s.dialects -- FIXME.  Compute only reachable dialects.
      openDialects := s.openDialects
      commands := s.commands
      globalContext := s.globalContext
    }

end DeclState

def addParserToCat (s : DeclState) (dp : DeclParser) : DeclState :=
  assert! dp.category ∈ s.parserMap
  { s with
      tokenTable := s.tokenTable.addTokens dp.parser
      parserMap :=
        s.parserMap.alter dp.category fun mtables =>
          match mtables with
          | none => panic s!"Category {dp.category.fullName} not declared."
          | some tables =>
            let r := tables |>.addParser dp.isLeading dp.parser dp.outerPrec
            some r,
  }

def addSynCat (dialect : String) (decl : SynCatDecl) (s : DeclState) : DeclState :=
  let cat : QualifiedIdent := { dialect, name := decl.name }
  if cat ∈ s.parserMap then
    panic! s!"{cat} already declared."
  else
    { s with parserMap := s.parserMap.insert cat {} }

def openParserDialectImpl (s : DeclState) (dialect : DialectName) (syncats : Collection SynCatDecl) : DeclState :=
  let ds := syncats.fold (init := s) (fun ps decl => addSynCat dialect decl ps)
  let parsers := s.dialectParsers.getD dialect #[]
  parsers.foldl (init := ds) addParserToCat

/--
Opens the dialect (not must not already be open)
-/
def openDialect! (dialect : DialectName) (s : DeclState) : DeclState :=
  if dialect ∈ s.openDialectSet then
    @panic _ ⟨s⟩ s!"Dialect {dialect} already open"
  else
    match s.dialects[dialect]? with
    | none =>
      @panic _ ⟨s⟩ s!"Unknown dialect {dialect}"
    | some d =>
      let s := { s with
        openDialects := s.openDialects.push dialect
        openDialectSet := s.openDialectSet.insert dialect
        metadataDeclMap := s.metadataDeclMap.addDialect d
        typeOrCatDeclMap := s.typeOrCatDeclMap.addDialect d
      }
      openParserDialectImpl s dialect d.syncats

@[reducible]
def DeclM := ReaderT DeclContext (StateM DeclState)

namespace DeclM

instance : ElabClass DeclM where
  getInputContext := return (←read).inputContext
  getDialects := return (←get).dialects
  getOpenDialects := return (←get).openDialectSet
  getGlobalContext := return (←get).globalContext
  getErrorCount := return (←get).errors.size
  logErrorMessage stx msg :=
    modify fun s => { s with errors := s.errors.push (stx, msg) }

def run (action : DeclM Unit) (init : DeclState := {}) : DeclState :=
  (action DeclContext.empty init).snd

end DeclM

def addTypeOrCatDecl (dialect : DialectName) (tpcd : TypeOrCatDecl) : DeclM Unit := do
  modify fun s => {
    s with typeOrCatDeclMap := s.typeOrCatDeclMap.add dialect tpcd
  }
