/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Std.Data.HashSet
public import Strata.DDM.AST
import all Strata.DDM.Util.Format
import all Strata.DDM.Util.Nat
import all Strata.DDM.Util.String

open Std (Format format)

public section
namespace Strata

/--
Check if a character is valid for starting a regular identifier.
Regular identifiers must start with a letter or underscore.
-/
private def isIdBegin (c : Char) : Bool :=
  c.isAlpha || c == '_'

/--
Check if a character is valid for continuing a regular identifier.
-/
private def isIdContinue (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '.' || c == '?' || c == '!'

/--
Check if a string needs pipe delimiters when formatted as an identifier.
Returns true if the string contains special characters, spaces, or starts with a digit.
-/
private def needsPipeDelimiters (s : String) : Bool :=
  if h : s.isEmpty then
    true
  else
    let firstChar := s.startPos.get (by simp_all)
    !isIdBegin firstChar || s.any (fun c => !isIdContinue c)

/--
Escape a string for use in pipe-delimited identifiers (SMT-LIB 2.6).
Escapes \ as \\ and | as \|
-/
private def escapePipeIdent (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    if c == '\\' then acc ++ "\\\\"
    else if c == '|' then acc ++ "\\|"
    else acc.push c

/--
Format a string as an identifier, using pipe delimiters if needed.
Strips Lean's «» notation if present.
Follows SMT-LIB 2.6 specification for quoted symbols.
-/
private def formatIdent (s : String) : Format :=
  -- Strip Lean's «» notation if present
  let s := if s.startsWith "«" && s.endsWith "»" then
             s.drop 1 |>.dropEnd 1 |>.toString
           else
             s
  if needsPipeDelimiters s then
    Format.text ("|" ++ escapePipeIdent s ++ "|")
  else
    Format.text s

structure PrecFormat where
  format : Format
  prec : Nat
deriving Inhabited

namespace PrecFormat

private def atom (format : Format) : PrecFormat := { format, prec := maxPrec + 1 }

private def ofFormat {α} [Std.ToFormat α] (x : α) (prec : Nat := maxPrec) : PrecFormat := { format := Std.format x, prec }

end PrecFormat

/--
Options to control parenthesis
-/
structure FormatOptions where
  /-- Always add parenthesis when feasible. -/
  alwaysParen : Bool := false

/--
A format context provides callbacks and information needed to
properly pretty-print Strata AST types.
-/
structure FormatContext where
  private opts : FormatOptions
  private getFnDecl : QualifiedIdent → Option FunctionDecl
  private getOpDecl : QualifiedIdent → Option OpDecl
  private globalContext : GlobalContext

namespace FormatContext

/-- A format context that uses no syntactic sugar. -/
private def explicit : FormatContext where
  opts := {}
  getFnDecl _ := none
  getOpDecl _ := none
  globalContext := {}

private def fvarName (ctx : FormatContext) (idx : FreeVarIndex) : String :=
  if let some name := ctx.globalContext.nameOf? idx then
    name
  else
    s!"fvar!{idx}"

protected def ofDialects (dialects : DialectMap) (globalContext : GlobalContext := {}) (opts : FormatOptions := {}) : FormatContext where
  opts := opts
  getFnDecl sym := Id.run do
    let .function f := dialects.decl! sym
      | return panic! s!"Unknown function {sym}"
    some f
  getOpDecl i := Id.run do
    let .op op := dialects.decl! i
      | panic! s!"Unknown op {i}"; return default
    some op
  globalContext := globalContext

end FormatContext

/-- Format state  -/
structure FormatState where
  openDialects : Std.HashSet String
  bindings : Array String := #[]

namespace FormatState

/-- A format context that uses no syntactic sugar. -/
def empty : FormatState where
  openDialects := {}

instance : Inhabited FormatState where
  default := .empty

def pushBinding (s : FormatState) (ident : String) : FormatState :=
  { s with bindings := s.bindings.push ident }

private def lvlVarName (s : FormatState) (lvl : Nat) : String :=
  let b := s.bindings
  if h : lvl < b.size then
    b[lvl]
  else
    s!"bvar!{s.bindings.size - (lvl + 1)}"

private def bvarName (s : FormatState) (idx : Nat) : String :=
  let b := s.bindings
  if h : idx < b.size then
    b[b.size - (idx + 1)]
  else
    s!"bvar!{idx}"

end FormatState

/--
A StrataFormat is a closure which given contextual information
produces a format operation as well as a precedence.  This
is used for auto-inserting parenthesis when needed.

Formats should return `maxPrec` when parenthesis are not
required.
-/
@[expose] def StrataFormat := FormatContext → FormatState → PrecFormat

class ToStrataFormat (α : Type u) where
  mformat : α → StrataFormat

export ToStrataFormat (mformat)

private def cformat [ToStrataFormat α] (a : α) (c : FormatContext) (s : FormatState) : Format := mformat a c s |>.format

def eformat [ToStrataFormat α] (a : α) : Format := mformat a .explicit .empty |>.format

instance : ToStrataFormat String where
  mformat s _ _ := private .ofFormat s

instance : ToStrataFormat Format where
  mformat s _ _ := private .atom s

instance : ToStrataFormat StrataFormat where
  mformat := id

instance : ToStrataFormat Nat where
  mformat n _ _ := private .ofFormat n (maxPrec + 1)

instance : ToStrataFormat Decimal where
  mformat n _ _ := private .ofFormat n (maxPrec + 1)

namespace StrataFormat

private protected def nil : StrataFormat := fun _ _ => .atom .nil

/-- Pretty print a free variable with the given index -/
private protected def fvar (fvarIdx : Nat) : StrataFormat := fun c _ => .atom (c.fvarName fvarIdx)

/-- Pretty print a bound variable with the given deBruijn index -/
private protected def lvlVar (lvl : Nat) : StrataFormat := fun _ s => .atom (s.lvlVarName lvl)

/-- Pretty print a bound variable with the given deBruijn index -/
private protected def bvar (idx : Nat) : StrataFormat := fun _ s => .atom (s.bvarName idx)

/--
Join together elements in list with no separator between adjacent elements.
-/
private def join [ToStrataFormat α] (a : List α) : StrataFormat :=
  match a with
  | [] => .nil
  | [x] => mformat x
  | _ => fun c s => .atom (Format.join (a.map (fun e => mformat e c s |>.format)))

/--
Join together elements in list with a separator between adjacent elements.
-/
private def sepBy [ToStrataFormat α] (a : Array α) (sep : String) : StrataFormat :=
  match p : a.size with
  | 0 => .nil
  | 1 =>
    mformat a[0]
  | n + 2 => fun c s =>
    let sep := format sep
    let append f e := f ++ sep ++ (mformat e c s).format
    .atom (a.foldl (start := 1) append (mformat a[0] c s).format)

instance : Append StrataFormat where
  append x y ctx s := private
    let xf := x ctx s |>.format
    let yf := y ctx s |>.format
    .atom (xf ++ yf)

/-- Set the precedence of the `fmt` to `prec` without changing format. -/
private def setPrec (fmt : StrataFormat) (prec : Nat) : StrataFormat := fun c s =>
  { format := fmt c s |>.format, prec := prec }

/-- Add parenthesis as needed to `fmt` to ensure precedence at least `p` -/
private def ensurePrec (fmt : StrataFormat) (prec : Nat) : StrataFormat := fun c s =>
  let r := fmt c s
  if r.prec < prec then
    .atom f!"({r.format})"
  else
    r

def withState (f : FormatState → FormatState) (fmt : StrataFormat) : StrataFormat := fun c s =>
  fmt c (f s)

private def nest (n : Nat) (fmt : StrataFormat) : StrataFormat := fun c s =>
  let ⟨r, p⟩ := fmt c s
  ⟨.nest n r, p⟩

end StrataFormat

syntax:max "mf!" interpolatedStr(term) : term

macro_rules
  | `(mf! $interpStr) => do interpStr.expandInterpolatedStr (← `(StrataFormat)) (← `(mformat))

instance : ToStrataFormat QualifiedIdent where
  mformat (ident : QualifiedIdent) _ s := private
    if ident.dialect ∈ s.openDialects then
      .atom (formatIdent ident.name)
    else
      .atom f!"{ident.dialect}.{formatIdent ident.name}"

namespace TypeExprF

private protected def mformat : TypeExprF α → StrataFormat
| .ident _ tp a => a.attach.foldl (init := mformat tp) fun m ⟨e, _⟩ =>
  mf!"{m} {e.mformat.ensurePrec (appPrec + 1)}".setPrec appPrec
| .bvar _ idx => .bvar idx
| .tvar _ name => mf!"{name}"
| .fvar _ idx a => a.attach.foldl (init := .fvar idx) fun m ⟨e, _⟩ =>
  mf!"{m} {e.mformat.ensurePrec (appPrec + 1)}".setPrec appPrec
| .arrow _ a r => mf!"{a.mformat.ensurePrec (arrowPrec+1)} -> {r.mformat.ensurePrec arrowPrec}"

instance {α} : ToStrataFormat (TypeExprF α) where
  mformat e := private e.mformat

end TypeExprF

namespace PreType

private protected def mformat : PreType → StrataFormat
| .ident _ tp a => a.attach.foldl (init := mformat tp) (fun m ⟨e, _⟩ => mf!"{m} {e.mformat}")
| .bvar _ idx => .bvar idx
| .tvar _ name => mf!"{name}"
| .fvar _ idx a => a.attach.foldl (init := .fvar idx) (fun m ⟨e, _⟩ => mf!"{m} {e.mformat}")
| .arrow _ a r => mf!"{a.mformat} -> {r.mformat}"
| .funMacro _ idx r => mf!"fnOf({StrataFormat.bvar idx}, {r.mformat})"

instance : ToStrataFormat PreType where
  mformat := private PreType.mformat

end PreType

namespace SyntaxCatF

private protected def mformat {α} (cat : SyntaxCatF α) : StrataFormat :=
  let init := mformat cat.name
  cat.args.foldl (init := init) (fun f a => mf!"{f} {a.mformat.ensurePrec (appPrec+1)}")
  decreasing_by
    rw [SyntaxCatF.sizeOf_spec cat]
    decreasing_tactic

instance {α} : ToStrataFormat (SyntaxCatF α)  where
  mformat := private SyntaxCatF.mformat

end SyntaxCatF

/--
This pretty prints the argument an op atom has.
-/
private def SyntaxDefAtom.formatArgs (opts : FormatOptions) (args : Array PrecFormat) (stx : SyntaxDefAtom) : Format :=
  match stx with
  | .ident lvl prec =>
    if h : lvl ≥ args.size then
      panic! s!"ident level {lvl} out of bounds"
    else
      let ⟨r, innerPrec⟩ := args[lvl]
      if prec > 0 ∧ (innerPrec ≤ prec ∨ opts.alwaysParen) then
        f!"({r})"
      else
        r
  | .str s => format s
  | .indent n f =>
    let r := Format.join (f.attach.map (fun ⟨a, _⟩ => a.formatArgs opts args) |>.toList)
    .nest n r

private def ppOp (opts : FormatOptions) (stx : SyntaxDef) (args : Array PrecFormat) : PrecFormat :=
  match stx with
  | .passthrough =>
    if h : args.size = 1 then
      args[0]
    else
      panic! "passthrough requires one argument"
  | .std atoms prec => ⟨Format.join ((·.formatArgs opts args) <$> atoms).toList, prec⟩

private abbrev FormatM := ReaderT FormatContext (StateM FormatState)

private def pformat {α} [ToStrataFormat α] (a : α) : FormatM PrecFormat :=
  fun c s => (mformat a c s, s)

mutual

/- Renders expression to format and precedence of outmost operator. -/
private partial def ExprF.mformatM (e : ExprF α) (rargs : Array (ArgF α)  := #[]) : FormatM PrecFormat :=
  let ppArgs (f : Format) : FormatM PrecFormat :=
        if rargs.isEmpty then
          pure <| .atom f
        else do
          let args := (←rargs.reverse.mapM (·.mformatM)) |>.map (·.format)
          let args := Format.joinSep args.toList f!", "
          pure <| .mk f!"{f}({args})" callPrec
  match e with
  | .bvar _ idx => do
    ppArgs (← pformat (StrataFormat.bvar idx)).format
  | .fvar _ idx => do
    ppArgs (← pformat (StrataFormat.fvar idx)).format
  | .fn _ f => do
      match (←read).getFnDecl f with
      | some op =>
        let args := rargs.reverse
        let bindings := op.argDecls
        let .isTrue bsize := decEq args.size bindings.size
              | return panic! "Mismatch betweeen binding and arg size"
        let argResults := formatArguments (← read) (← get) bindings ⟨args, bsize⟩
        pure <| ppOp (← read).opts op.syntaxDef (Prod.fst <$> argResults)
      | none => ppArgs f.fullName
  | .app _ f a => f.mformatM (rargs.push a)

private partial def ArgF.mformatM {α} : ArgF α → FormatM PrecFormat
| .op o => o.mformatM
| .expr e => e.mformatM
| .type e => pformat e
| .cat e => pformat e
| .ident _ x => return .atom (formatIdent x)
| .num _ x => pformat x
| .decimal _ v => pformat v
| .strlit _ s => return .atom (.text <| escapeStringLit s)
| .bytes _ v => return .atom <| .text <| ByteArray.escapeBytes v
| .option _ ma =>
  match ma with
  | none => pure (.atom .nil)
  | some a => a.mformatM
| .seq _ sep entries => do
  match sep with
  | .none =>
    .atom <$> entries.foldlM (init := .nil) fun p a =>
      return (p ++ (← a.mformatM).format)
  | .comma =>
    if z : entries.size = 0 then
      pure (.atom .nil)
    else do
      let f i q s := return s ++ ", " ++ (← entries[i].mformatM).format
      let a := (← entries[0].mformatM).format
      .atom <$> entries.size.foldlM f (start := 1) a
  | .space =>
    if z : entries.size = 0 then
      pure (.atom .nil)
    else do
      let f i q s := return s ++ " " ++ (← entries[i].mformatM).format
      let a := (← entries[0].mformatM).format
      .atom <$> entries.size.foldlM f (start := 1) a
  | .spacePrefix =>
    .atom <$> entries.foldlM (init := .nil) fun p a =>
      return (p ++ " " ++ (← a.mformatM).format)
  | .newline =>
    if z : entries.size = 0 then
      pure (.atom .nil)
    else do
      let f i q s := return s ++ "\n" ++ (← entries[i].mformatM).format
      let a := (← entries[0].mformatM).format
      .atom <$> entries.size.foldlM f (start := 1) a

private partial def ppArgs (f : StrataFormat) (rargs : Array Arg) : FormatM PrecFormat :=
  if rargs.isEmpty then
    pformat f
  else do
    let f := (← pformat f).format
    let pf := (← rargs.back!.mformatM).format
    let init := f!"{f}({pf}"
    let rargs := rargs.pop
    let r ← rargs.foldrM (init := init) (fun a r => return f!"{r},{(←a.mformatM).format})")
    pure <| .atom f!"{r})"

private partial def formatArguments (c : FormatContext) (initState : FormatState) (argDecls : ArgDecls) (args : Vector (ArgF α) argDecls.size) :=
  let rec aux (a : Array (PrecFormat × FormatState)) :=
        let lvl := a.size
        if h : lvl < argDecls.size then
          let s :=
                match argDecls.argScopeLevel ⟨lvl, h⟩ with
                | none =>
                  initState
                | some ⟨alvl, aisLt⟩  =>
                  have _ : alvl < a.size := by simp at aisLt; omega
                  a[alvl].snd
          aux (a.push (args[lvl].mformatM c s))
        else
          a
  aux (.mkEmpty argDecls.size)

private partial def OperationF.mformatM (op : OperationF α) : FormatM PrecFormat := do
  match (← read).getOpDecl op.name with
  | some decl =>
    let bindings := decl.argDecls
    let .isTrue bsize := decEq op.args.size bindings.size
          | return panic! "Mismatch betweeen binding and arg size"
    let args : Vector _ bindings.size := ⟨op.args, bsize⟩
    let argResults := formatArguments (← read) (← get) bindings args
    let fmt := ppOp (← read).opts decl.syntaxDef (Prod.fst <$> argResults)
    match decl.metadata.resultLevel bindings.size with
    | some idx =>
      if h : idx.val < argResults.size then
        set argResults[idx.val].snd
      else
        panic! "result scope index out of bounds"
    | none => pure ()
    for b in decl.newBindings do
      match args[b.nameIndex.toLevel] with
      | .ident _ e =>
        modify (·.pushBinding e)
      | _ =>
        return panic! s!"Expected ident at {b.nameIndex.toLevel}."
    return fmt
  | none =>
    -- FIXME: Consider reporting error here.
    let initCtx ← read
    let initState ← get
    let args := op.args |>.map (ArgF.mformatM · initCtx initState |>.fst |>.format) |>.toList
    return .atom f!"{op.name.fullName}({Format.joinSep args ", "});"

end

instance ExprF.instToStrataFormat {α} : ToStrataFormat (ExprF α) where
  mformat e c s := private e.mformatM #[] c s |>.fst

instance ArgF.instToStrataFormat {α} : ToStrataFormat (ArgF α) where
  mformat a c s := private a.mformatM c s |>.fst


namespace OperationF

instance {α} : ToStrataFormat (OperationF α) where
  mformat o c s := private o.mformatM c s |>.fst

/--
This renders an operation returning its string representation and new state.
-/
def render {α} (op : OperationF α) (ctx : FormatContext) (s : FormatState) : String × FormatState :=
  let (f, s) := op.mformatM ctx s
  (f.format.render, s)

end OperationF

namespace MetadataArg

private protected def mformat : MetadataArg → StrataFormat
| .bool b => if b then mf!"true" else mf!"false"
| .num n => mformat n
| .catbvar idx => StrataFormat.bvar idx
| .option ma =>
  match ma with
  | none => mf!"none"
  | some a => a.mformat
| .functionTemplate t => mf!"functionTemplate({repr t})"

instance : ToStrataFormat MetadataArg where
  mformat := private MetadataArg.mformat

end MetadataArg

namespace MetadataAttr

instance : ToStrataFormat MetadataAttr where
  mformat a := private
    if a.args.isEmpty then
      mformat a.ident
    else
      mf!"{a.ident}({StrataFormat.sepBy a.args ","})"

end MetadataAttr

instance Metadata.instToStrataFormat : ToStrataFormat Metadata where
  mformat m := private
    if m.toArray.isEmpty then
      .nil
    else
      mf!"@[{StrataFormat.sepBy m.toArray ", "}]"

namespace ArgDeclKind

instance : ToStrataFormat ArgDeclKind where
  mformat private
  | .cat c => mformat c
  | .type tp => mformat tp

end ArgDeclKind

namespace ArgDecl

instance : ToStrataFormat ArgDecl where
  mformat b := private
    let r := mf!"{b.ident} : {b.kind}"
    if b.metadata.isEmpty then
      r
    else
      mf!"{b.metadata} {r}"

end ArgDecl

namespace ArgDecls

private def mformatAux (f : Format) (c : FormatContext) (s : FormatState) (a : ArgDecls) (idx : Nat) : Format × FormatState :=
  if h : idx < a.size then
    let b := a[idx]
    mformatAux (f ++ ", " ++ cformat b c s) c (s.pushBinding b.ident) a (idx + 1)
  else
    (f ++ ")", s)

private protected def mformat (c : FormatContext) (s : FormatState) (l : ArgDecls) : Format × FormatState :=
  if h : 0 < l.size then
    let b := l[0]
    mformatAux ("(" ++ cformat b c s) c (s.pushBinding b.ident) l 1
  else
    ("()", s)

instance : ToStrataFormat ArgDecls where
  mformat l c s := private .atom (l.mformat c s |>.fst)

/- Format `fmt` in a context with additional bindings `b`. -/
private protected def formatIn [ToStrataFormat α] (b : ArgDecls) (fmt : α) : StrataFormat := fun c s =>
  Strata.mformat fmt c (b.toArray.foldl (init := s) (·.pushBinding ·.ident))

end ArgDecls

namespace SyntaxDefAtom

private protected def mformat : SyntaxDefAtom → StrataFormat
| .ident lvl prec => mf!"{StrataFormat.lvlVar lvl}:{prec}" -- FIXME.  This may be wrong.
| .str lit => mformat (escapeStringLit lit)
| .indent n f =>
  let r := f.attach.map fun ⟨a, _⟩ => a.mformat
  let f := StrataFormat.sepBy r " "
  mf!"indent({n}, {f})"

instance : ToStrataFormat SyntaxDefAtom where
  mformat := private SyntaxDefAtom.mformat

end SyntaxDefAtom

namespace SyntaxDef

instance : ToStrataFormat SyntaxDef where
  mformat := private fun
    | .std atoms _ => .sepBy atoms " "
    | .passthrough => mf!"{StrataFormat.lvlVar 0}:{0}"

end SyntaxDef

instance SynCatDecl.instToStrataFormat : ToStrataFormat SynCatDecl where
  mformat d := private
    let args : StrataFormat := .join <| d.argNames.map (mf!" {·}") |>.toList
    mf!"category {d.name}{args};\n"

namespace OpDecl

instance : ToStrataFormat OpDecl where
  mformat d := private
    let argDecls := d.argDecls
    let mdf := if d.metadata.isEmpty then .nil else mf!"{argDecls.formatIn d.metadata} "
    let argDeclsF := if argDecls.isEmpty then mf!"" else mf!" {argDecls}"
    mf!"{mdf}op {d.name}{argDeclsF} : {d.category} => {argDecls.formatIn d.syntaxDef};\n"

end OpDecl

instance TypeDecl.instToStrataFormat : ToStrataFormat TypeDecl where
  mformat d := private
    let params := d.argNames
    let params := if params.isEmpty then
                    mf!""
                  else
                    let p := d.argNames.map fun anm => mf!"{anm.val} : Type"
                    mf! " " ++ StrataFormat.sepBy p ", "
    mf!"type {d.name}{params};\n"

instance FunctionDecl.instToStrataFormat : ToStrataFormat FunctionDecl where
  mformat d := private
    let argDecls := d.argDecls
    let mdf := if d.metadata.isEmpty then .nil else mf!"{argDecls.formatIn d.metadata} "
    let argDeclsF := if argDecls.isEmpty then mf!"" else mf!" {argDecls}"
    let result := argDecls.formatIn d.result
    mf!"{mdf}fn {d.name}{argDeclsF} : {result} => {d.argDecls.formatIn d.syntaxDef};\n"

namespace MetadataArgType

private protected def mformat : MetadataArgType → StrataFormat
| .num => mf!"Num"
| .ident => mf!"Ident"
| .bool => mf!"Bool"
| .opt tp => mf!"Option {tp.mformat |>.ensurePrec (appPrec + 1)}" |>.setPrec appPrec
| .functionTemplate => mf!"FunctionTemplate"

instance : ToStrataFormat MetadataArgType where
  mformat := private MetadataArgType.mformat

end MetadataArgType

instance MetadataDecl.instToStrataFormat : ToStrataFormat MetadataDecl where
  mformat d := private
    if d.args.isEmpty then
      mf!"metadata {d.name};\n"
    else
      let ppArg a := mf! "{a.ident} : {a.type}"
      mf!"metadata {d.name}({StrataFormat.sepBy (d.args |>.map ppArg) ", "});\n"

instance Decl.instToStrataFormat : ToStrataFormat Decl where
  mformat private
  | .syncat d => mformat d
  | .op d => mformat d
  | .type d => mformat d
  | .function d => mformat d
  | .metadata d => mformat d

namespace DialectMap

/--
Pretty print the dialect with the given name in the map.
-/
protected def format (dialects : DialectMap) (name : DialectName) (mem : name ∈ dialects) (opts : FormatOptions := {}) : Format :=
  let d := dialects[name]
  let c := FormatContext.ofDialects dialects {} opts
  let imports := dialects.importedDialects name mem
  let s : FormatState := { openDialects := imports.toList.foldl (init := {}) fun s d => s.insert d.name }
  let f := f!"dialect {name};\n"
  let f := d.imports.foldl (init := f) fun f i =>
    if i = "Init" then
      f
    else
      f!"{f}import {i}\n"
  d.declarations.foldl (init := f) fun f d => f ++ (mformat d c s).format

end DialectMap

namespace Program

protected def formatContext (p : Program) (opts : FormatOptions) : FormatContext :=
  .ofDialects p.dialects p.globalContext opts

protected def formatState (p : Program) : FormatState where
  openDialects := p.dialects.toList.foldl (init := {}) fun a d => a.insert d.name

protected def format (p : Program) (opts : FormatOptions := {}) : Format :=
  let c := p.formatContext opts
  let s := p.formatState
  p.commands.foldl (init := f!"program {p.dialect};\n") fun f cmd =>
    f ++ (mformat cmd c s).format

protected def toString (p : Program) (opts : FormatOptions := {}) : String :=
  p.format opts |>.render

instance : ToString Program where
  toString p := p.toString
protected def ppDialect! (p : Program) (name : DialectName := p.dialect) (opts : FormatOptions := {}) : Format :=
  if mem : name ∈ p.dialects then
    p.dialects.format name mem opts
  else
    panic! s!"Unknown dialect {name}"

end Program

end Strata
end
