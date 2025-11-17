/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST
import Strata.DDM.Util.Fin
import Strata.DDM.Util.Format
import Strata.DDM.Util.Nat
import Std.Data.HashSet

open Std (Format format)

namespace Strata

structure PrecFormat where
  format : Format
  prec : Nat
deriving Inhabited

namespace PrecFormat

def atom (format : Format) : PrecFormat := { format, prec := maxPrec }

def ofFormat [Std.ToFormat α] (x : α) (prec : Nat := maxPrec) : PrecFormat := { format := Std.format x, prec }

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
  opts : FormatOptions
  getFnDecl : QualifiedIdent → Option FunctionDecl
  getOpDecl : QualifiedIdent → Option OpDecl
  globalContext : GlobalContext

namespace FormatContext

/-- A format context that uses no syntactic sugar. -/
def explicit : FormatContext where
  opts := {}
  getFnDecl _ := none
  getOpDecl _ := none
  globalContext := {}

def fvarName (ctx : FormatContext) (idx : FreeVarIndex) : String :=
  if let some name := ctx.globalContext.nameOf? idx then
    name
  else
    s!"fvar!{idx}"

protected def ofDialects (dialects : DialectMap) (globalContext : GlobalContext) (opts : FormatOptions) : FormatContext where
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

/-- Format state includes local information -/
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

def lvlVarName (s : FormatState) (lvl : Nat) : String :=
  let b := s.bindings
  if h : lvl < b.size then
    b[lvl]
  else
    s!"bvar!{s.bindings.size - (lvl + 1)}"

def bvarName (s : FormatState) (idx : Nat) : String :=
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
def StrataFormat := FormatContext → FormatState → PrecFormat

class ToStrataFormat (α : Type u) where
  mformat : α → StrataFormat

export ToStrataFormat (mformat)

def cformat [ToStrataFormat α] (a : α) (c : FormatContext) (s : FormatState) : Format := mformat a c s |>.format

def eformat [ToStrataFormat α] (a : α) : Format := mformat a .explicit .empty |>.format

instance : ToStrataFormat String where
  mformat s _ _ := .ofFormat s

instance : ToStrataFormat Format where
  mformat s _ _ := .atom s

instance : ToStrataFormat StrataFormat where
  mformat := id

instance : ToStrataFormat Nat where
  mformat n _ _ := .ofFormat n

instance : ToStrataFormat Decimal where
  mformat n _ _ := .ofFormat n

namespace StrataFormat

protected def nil : StrataFormat := fun _ _ => .atom .nil

/-- Pretty print a free variable with the given index -/
protected def fvar (fvarIdx : Nat) : StrataFormat := fun c _ => .atom (c.fvarName fvarIdx)

/-- Pretty print a bound variable with the given deBruijn index -/
protected def lvlVar (lvl : Nat) : StrataFormat := fun _ s => .atom (s.lvlVarName lvl)

/-- Pretty print a bound variable with the given deBruijn index -/
protected def bvar (idx : Nat) : StrataFormat := fun _ s => .atom (s.bvarName idx)

/--
Join together elements in list with no separator between adjacent elements.
-/
def join [ToStrataFormat α] (a : List α) : StrataFormat :=
  match a with
  | [] => .nil
  | [x] => mformat x
  | _ => fun c s => .atom (Format.join (a.map (fun e => mformat e c s |>.format)))

/--
Join together elements in list with a separator between adjacent elements.
-/
def sepBy [ToStrataFormat α] (a : Array α) (sep : String) : StrataFormat :=
  match p : a.size with
  | 0 => .nil
  | 1 =>
    mformat a[0]
  | n + 2 => fun c s =>
    let sep := format sep
    let append f e := f ++ sep ++ (mformat e c s).format
    .atom (a.foldl (start := 1) append (mformat a[0] c s).format)

instance : Append StrataFormat where
  append x y ctx s :=
    let xf := x ctx s |>.format
    let yf := y ctx s |>.format
    .atom (xf ++ yf)

/-- Set the precedence of the `fmt` to `prec` without changing format. -/
def setPrec (fmt : StrataFormat) (prec : Nat) : StrataFormat := fun c s =>
  { format := fmt c s |>.format, prec := prec }

/-- Add parenthesis as needed to `fmt` to ensure precedence at least `p` -/
def ensurePrec (fmt : StrataFormat) (prec : Nat) : StrataFormat := fun c s =>
  let r := fmt c s
  if r.prec < prec then
    .atom f!"({r.format})"
  else
    r

def withState (f : FormatState → FormatState) (fmt : StrataFormat) : StrataFormat := fun c s =>
  fmt c (f s)

def nest (n : Nat) (fmt : StrataFormat) : StrataFormat := fun c s =>
  let ⟨r, p⟩ := fmt c s
  ⟨.nest n r, p⟩

end StrataFormat

syntax:max "mf!" interpolatedStr(term) : term

macro_rules
  | `(mf! $interpStr) => do interpStr.expandInterpolatedStr (← `(StrataFormat)) (← `(mformat))

instance : ToStrataFormat QualifiedIdent where
  mformat (ident : QualifiedIdent) _ s :=
    if ident.dialect ∈ s.openDialects then
      .ofFormat ident.name
    else
      .atom f!"{ident.dialect}.{ident.name}"

namespace TypeExprF

protected def mformat : TypeExprF α → StrataFormat
| .ident _ tp a => a.attach.foldl (init := mformat tp) fun m ⟨e, _⟩ =>
  mf!"{m} {e.mformat.ensurePrec (appPrec + 1)}".setPrec appPrec
| .bvar _ idx => .bvar idx
| .fvar _ idx a => a.attach.foldl (init := .fvar idx) fun m ⟨e, _⟩ =>
  mf!"{m} {e.mformat.ensurePrec (appPrec + 1)}".setPrec appPrec
| .arrow _ a r => mf!"{a.mformat.ensurePrec (arrowPrec+1)} -> {r.mformat.ensurePrec arrowPrec}"

instance : ToStrataFormat (TypeExprF α) where
  mformat e := e.mformat

end TypeExprF

namespace PreType

protected def mformat : PreType → StrataFormat
| .ident _ tp a => a.attach.foldl (init := mformat tp) (fun m ⟨e, _⟩ => mf!"{m} {e.mformat}")
| .bvar _ idx => .bvar idx
| .fvar _ idx a => a.attach.foldl (init := .fvar idx) (fun m ⟨e, _⟩ => mf!"{m} {e.mformat}")
| .arrow _ a r => mf!"{a.mformat} -> {r.mformat}"
| .funMacro _ idx r => mf!"fnOf({StrataFormat.bvar idx}, {r.mformat})"

instance : ToStrataFormat PreType where
  mformat := PreType.mformat

end PreType

namespace SyntaxCatF

protected def mformat {α} (cat : SyntaxCatF α) : StrataFormat :=
  let init := mformat cat.name
  cat.args.foldl (init := init) (fun f a => mf!"{f} {a.mformat.ensurePrec (appPrec+1)}")
  decreasing_by
    rw [SyntaxCatF.sizeOf_spec cat]
    decreasing_tactic

instance {α} : ToStrataFormat (SyntaxCatF α)  where
  mformat := SyntaxCatF.mformat

end SyntaxCatF

/--
This pretty prints the argument an op atom has.
-/
private def SyntaxDefAtom.formatArgs (opts : FormatOptions) (args : Array PrecFormat) (stx : SyntaxDefAtom) : Format :=
  match stx with
  | .ident lvl prec =>
    let ⟨r, innerPrec⟩ := args[lvl]!
    if prec > 0 ∧ (innerPrec ≤ prec ∨ opts.alwaysParen) then
      f!"({r})"
    else
      r
  | .str s => format s
  | .indent n f =>
    let r := Format.join (f.attach.map (fun ⟨a, _⟩ => a.formatArgs opts args) |>.toList)
    .nest n r

private def ppOp (opts : FormatOptions) (stx : SyntaxDef) (args : Array PrecFormat) : PrecFormat :=
  ⟨Format.join ((·.formatArgs opts args) <$> stx.atoms).toList, stx.prec⟩

abbrev FormatM := ReaderT FormatContext (StateM FormatState)

def pformat {α} [ToStrataFormat α] (a : α) : FormatM PrecFormat :=
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
| .ident _ x => pformat x
| .num _ x => pformat x
| .decimal _ v => pformat v
| .strlit _ s => return .atom (.text <| escapeStringLit s)
| .bytes _ v => return .atom <| .text <| ByteArray.escapeBytes v
| .option _ ma =>
  match ma with
  | none => pure (.atom .nil)
  | some a => a.mformatM
| .seq _ entries => do
  .atom <$> entries.foldlM (init := .nil) fun p a =>
    return (p ++ (← a.mformatM).format)
| .commaSepList _ entries => do
  if z : entries.size = 0 then
    pure (.atom .nil)
  else do
    let f i q s := return s ++ ", " ++ (← entries[i].mformatM).format
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
    | some idx => set argResults[idx]!.snd
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

instance Expr.instToStrataFormat : ToStrataFormat Expr where
  mformat e c s := e.mformatM #[] c s |>.fst

instance Arg.instToStrataFormat : ToStrataFormat Arg where
  mformat a c s := a.mformatM c s |>.fst

instance Operation.instToStrataFormat : ToStrataFormat Operation where
  mformat o c s := o.mformatM c s |>.fst

namespace MetadataArg

protected def mformat : MetadataArg → StrataFormat
| .bool b => if b then mf!"true" else mf!"false"
| .num n => mformat n
| .catbvar idx => StrataFormat.bvar idx
| .option ma =>
  match ma with
  | none => mf!"none"
  | some a => a.mformat

instance : ToStrataFormat MetadataArg where
  mformat := MetadataArg.mformat

end MetadataArg

namespace MetadataAttr

instance : ToStrataFormat MetadataAttr where
  mformat a :=
    if a.args.isEmpty then
      mformat a.ident
    else
      mf!"{a.ident}({StrataFormat.sepBy a.args ","})"

end MetadataAttr

instance Metadata.instToStrataFormat : ToStrataFormat Metadata where
  mformat m :=
    if m.toArray.isEmpty then
      .nil
    else
      mf!"@[{StrataFormat.sepBy m.toArray ", "}]"

namespace ArgDeclKind

instance : ToStrataFormat ArgDeclKind where
  mformat
  | .cat c => mformat c
  | .type tp => mformat tp

end ArgDeclKind

namespace ArgDecl

instance : ToStrataFormat ArgDecl where
  mformat b :=
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

protected def mformat (c : FormatContext) (s : FormatState) (l : ArgDecls) : Format × FormatState :=
  if h : 0 < l.size then
    let b := l[0]
    mformatAux ("(" ++ cformat b c s) c (s.pushBinding b.ident) l 1
  else
    ("()", s)

instance : ToStrataFormat ArgDecls where
  mformat l c s := .atom (l.mformat c s |>.fst)

/- Format `fmt` in a context with additional bindings `b`. -/
protected def formatIn [ToStrataFormat α] (b : ArgDecls) (fmt : α) : StrataFormat := fun c s =>
  mformat fmt c (b.toArray.foldl (init := s) (·.pushBinding ·.ident))

end ArgDecls

namespace SyntaxDefAtom

protected def mformat : SyntaxDefAtom → StrataFormat
| .ident lvl prec => mf!"{StrataFormat.lvlVar lvl}:{prec}" -- FIXME.  This may be wrong.
| .str lit => mformat (escapeStringLit lit)
| .indent n f =>
  let r := f.attach.map fun ⟨a, _⟩ => a.mformat
  let f := StrataFormat.sepBy r " "
  mf!"indent({n}, {f})"

instance : ToStrataFormat SyntaxDefAtom where
  mformat := SyntaxDefAtom.mformat

end SyntaxDefAtom

namespace SyntaxDef

instance : ToStrataFormat SyntaxDef where
  mformat s := .sepBy s.atoms " "

end SyntaxDef

instance SynCatDecl.instToStrataFormat : ToStrataFormat SynCatDecl where
  mformat d :=
    let args : StrataFormat := .join <| d.argNames.map (mf!" {·}") |>.toList
    mf!"category {d.name}{args};\n"

namespace OpDecl

instance : ToStrataFormat OpDecl where
  mformat d :=
    let argDecls := d.argDecls
    let mdf := if d.metadata.isEmpty then .nil else mf!"{argDecls.formatIn d.metadata} "
    let argDeclsF := if argDecls.isEmpty then mf!"" else mf!" {argDecls}"
    mf!"{mdf}op {d.name}{argDeclsF} : {d.category} => {argDecls.formatIn d.syntaxDef};\n"

end OpDecl

instance TypeDecl.instToStrataFormat : ToStrataFormat TypeDecl where
  mformat d :=
    let params := d.argNames
    let params := if params.isEmpty then
                    mf!""
                  else
                    let p := d.argNames.map fun anm => mf!"{anm.val} : Type"
                    mf! " " ++ StrataFormat.sepBy p ", "
    mf!"type {d.name}{params};\n"

instance FunctionDecl.instToStrataFormat : ToStrataFormat FunctionDecl where
  mformat d :=
    let argDecls := d.argDecls
    let mdf := if d.metadata.isEmpty then .nil else mf!"{argDecls.formatIn d.metadata} "
    let argDeclsF := if argDecls.isEmpty then mf!"" else mf!" {argDecls}"
    let result := argDecls.formatIn d.result
    mf!"{mdf}fn {d.name}{argDeclsF} : {result} => {d.argDecls.formatIn d.syntaxDef};\n"

namespace MetadataArgType

protected def mformat : MetadataArgType → StrataFormat
  | .num => mf!"Num"
  | .ident => mf!"Ident"
  | .bool => mf!"Bool"
  | .opt tp => mf!"Option {tp.mformat |>.ensurePrec (appPrec + 1)}" |>.setPrec appPrec

instance : ToStrataFormat MetadataArgType where
  mformat := MetadataArgType.mformat

end MetadataArgType

instance MetadataDecl.instToStrataFormat : ToStrataFormat MetadataDecl where
  mformat d :=
    if d.args.isEmpty then
      mf!"metadata {d.name};\n"
    else
      let ppArg a := mf! "{a.ident} : {a.type}"
      mf!"metadata {d.name}({StrataFormat.sepBy (d.args |>.map ppArg) ", "});\n"

instance Decl.instToStrataFormat : ToStrataFormat Decl where
  mformat
  | .syncat d => mformat d
  | .op d => mformat d
  | .type d => mformat d
  | .function d => mformat d
  | .metadata d => mformat d

namespace Dialect

protected def format (dialects : DialectMap) (d : Dialect) (opts : FormatOptions := {}) : Format :=
  assert! d.name ∈ dialects
  let c := FormatContext.ofDialects dialects {} opts
  let imports := dialects.importedDialects! d.name
  let s : FormatState := { openDialects := imports.map.fold (init := {}) fun s n _ => s.insert n }
  let f := f!"dialect {d.name};\n"
  let f := d.imports.foldl (init := f) fun f i =>
    if i = "Init" then
      f
    else
      f!"{f}import {i}\n"
  d.declarations.foldl (init := f) fun f d => f ++ (mformat d c s).format

end Dialect

namespace Program

protected def formatContext (p : Program) (opts : FormatOptions) : FormatContext :=
  .ofDialects p.dialects p.globalContext opts

protected def formatState (p : Program) : FormatState where
  openDialects := .ofArray p.dialects.map.keysArray

protected def format (p : Program) (opts : FormatOptions := {}) : Format :=
  let c := p.formatContext opts
  let s := p.formatState
  p.commands.foldl (init := f!"program {p.dialect};\n") fun f cmd =>
    f ++ (mformat cmd c s).format

instance : ToString Program where
  toString p := p.format |>.render

protected def ppDialect! (p : Program) (name : DialectName := p.dialect) (opts : FormatOptions := {}) : Format :=
  match p.dialects[name]? with
  | some d => d.format p.dialects opts
  | none => panic! s!"Unknown dialect {name}"

end Program

end Strata
