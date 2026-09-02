/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Env
public import Strata.Languages.Core.DDMTransform.FracLit
open StrataDDM


---------------------------------------------------------------------
namespace Strata

/- Translating concrete syntax into abstract syntax -/

open Core
open Lambda Imperative Lean.Parser
open Std (ToFormat Format format)

public section

---------------------------------------------------------------------

/- Translation Monad -/

structure TransState where
  inputCtx : InputContext
  errors : Array String
  globalContext : GlobalContext := {}

@[expose]
def TransM := StateM TransState
  deriving Monad

@[expose]
def TransM.run (ictx : InputContext) (m : TransM α) (gctx : GlobalContext := {}) : (α × Array String) :=
  let (v, s) := StateT.run m { inputCtx := ictx, errors := #[], globalContext := gctx }
  (v, s.errors)

def TransM.error [Inhabited α] (msg : String) : TransM α := do
  fun s => ((), { s with errors := s.errors.push msg })
  return panic msg

/-- Record a translation error without panicking, then continue with `fallback`.
    Use for malformed user input (as opposed to internal invariant violations,
    which use `TransM.error`). -/
def TransM.recordError (msg : String) (fallback : α) : TransM α := do
  fun s => ((), { s with errors := s.errors.push msg })
  return fallback

---------------------------------------------------------------------

/- Metadata -/

def SourceRange.toMetaData (ictx : InputContext) (sr : SourceRange) : Imperative.MetaData Core.Expression :=
  Imperative.MetaData.ofSourceRange (.file ictx.fileName) sr

def getOpMetaData (op : Operation) : TransM (Imperative.MetaData Core.Expression) :=
  return SourceRange.toMetaData (← StateT.get).inputCtx op.ann

def getArgMetaData (arg : Arg) : TransM (Imperative.MetaData Core.Expression) :=
  return SourceRange.toMetaData (← StateT.get).inputCtx arg.ann

---------------------------------------------------------------------

def checkOp (op : Operation) (name : QualifiedIdent) (argc : Nat) :
  TransM (Option α) := do
  if op.name != name then
    TransM.error s!"Op name mismatch! \n\
                   Name: {repr name}\n\
                   Op: {repr op}"
  if op.args.size != argc then
    TransM.error s!"Op args size mismatch! \n\
                    Argc: {argc}\n\
                    Op arg size: {op.args.size}\n\
                    Op: {repr op}"
  return none

def checkOpArg (arg : Arg) (name : QualifiedIdent) (argc : Nat) : TransM (Array Arg) := do
  let .op op := arg
    | return .ofFn fun (_ : Fin argc) => default
  if op.name != name then
    panic! s!"Expected {name} when given {op.name}"
  if op.args.size != argc then
    panic! s!"Expected {name} to have {argc} arguments but {op.args.size} given"
  assert! op.name == name
  assert! op.args.size == argc
  pure op.args

---------------------------------------------------------------------

def translateCommaSep [Inhabited α] (f : Arg → TransM α) (arg : Arg) :
  TransM (Array α) := do
  let .seq _ .comma args := arg
    | TransM.error s!"Expected commaSepList: {repr arg}"
  args.mapM f

def translateOption [Inhabited α] (f : Option Arg → TransM α) (arg : Arg) :
  TransM α := do
  let .option _ maybe_arg := arg
    | TransM.error s!"Expected Option: {repr arg}"
  f maybe_arg

---------------------------------------------------------------------

def translateIdent (Identifier : Type) [Coe String Identifier] [Inhabited Identifier]
  (arg : Arg) : TransM Identifier := do
  let .ident _ name := arg
    | TransM.error s!"Expected ident: {repr arg}"
  pure name

/-- Translate an optional `Core.label` argument, returning the user-supplied
    label name if one was written, or `none` otherwise. -/
def translateOptionLabel? (arg : Arg) : TransM (Option String) := do
  translateOption (fun maybe_arg => do
                    match maybe_arg with
                    | none => return none
                    | some lop => let args ← checkOpArg lop q`Core.label 1
                                  return some (← translateIdent String args[0]!))
                  arg

def translateOptionLabel (default : String) (arg : Arg) : TransM String := do
  return (← translateOptionLabel? arg).getD default

def translateNat (arg : Arg) : TransM Nat := do
  let .num _ n := arg
    | TransM.error s!"translateNat expects num lit"
  return n

def translateBitVec (width : Nat) (arg : Arg) : TransM Nat := do
  let .num _ n := arg
    | TransM.error s!"translateBitVec expects num lit"
  return (n % (2 ^ width))

def translateStr (arg : Arg) : TransM String := do
  let .strlit _ s := arg
    | TransM.error s!"translateStr expects string lit"
  return s

def translateReal (arg : Arg) : TransM Decimal := do
  let .decimal _ d := arg
    | TransM.error s!"translateReal expects decimal lit"
  return d

---------------------------------------------------------------------

/- MetadataAnn Translation -/

/-- Translate a MetadataAnnKey to a string (bare or dialect-prefixed). -/
def translateMetadataAnnKey (arg : Arg) : TransM String := do
  let .op op := arg
    | TransM.error s!"translateMetadataAnnKey expected op {repr arg}"
  match op.name, op.args with
  | q`Core.mdAnnKeyBare, #[nameArg] =>
    translateIdent String nameArg
  | q`Core.mdAnnKeyPrefixed, #[dialectArg, nameArg] =>
    let dialect ← translateIdent String dialectArg
    let name ← translateIdent String nameArg
    return s!"{dialect}.{name}"
  | _, _ => TransM.error s!"translateMetadataAnnKey: unexpected {repr op.name}"

/-- Parse the flat-string form of a `Provenance` back into structured data.

Provenance values are the only `MetaDataElem.Value` variant that carries
structured data (Uri + byte range, or synthesized origin) serialized as a flat
string in the grammar. Without re-parsing, they'd be stored as `.msg` and break
`getProvenance`/`getFileRange`/`getRelatedFileRanges`.

Two string forms are accepted, matching how `Provenance` is formatted:
- Synthesized origin: `<synthesized:BODY>`, where `BODY` is parsed by
  `SynthesizedOrigin.ofFormatString` (e.g. `<synthesized:smt-encode>`).
- Source location: `PATH:START-STOP`, where `START`/`STOP` are byte offsets
  (`Nat`) and `PATH` is the file path. The path may itself contain colons
  (e.g. a URI), so we split off only the final `:`-segment as the range and
  rejoin the rest as the path (e.g. `s3://bucket/foo.st:100-200`).

Returns `none` if the string matches neither form (the caller then falls back
to storing the raw string as `.msg`). -/
private def parseProvenanceString (s : String) : Option Strata.Provenance :=
  if s.startsWith "<synthesized:" && s.endsWith ">" then
    let inner := ((s.drop "<synthesized:".length).dropEnd 1).toString
    match Strata.SynthesizedOrigin.ofFormatString inner with
    | some origin => some (.synthesized origin)
    | none => none
  else
    let parts := s.splitOn ":"
    if parts.length < 2 then none
    else
      let rangeStr := parts.getLast!
      let path := String.intercalate ":" (parts.dropLast)
      match rangeStr.splitOn "-" with
      | [startStr, stopStr] =>
        match startStr.toNat?, stopStr.toNat? with
        | some start, some stop =>
          let sr : StrataDDM.SourceRange := { start := ⟨start⟩, stop := ⟨stop⟩ }
          some (.loc (.file path) sr)
        | _, _ => none
      | _ => none

/-- Translate a MetadataAnnEntry to a MetaDataElem (flags and string values only;
    expression values are not yet supported). -/
def translateMetadataAnnEntry (arg : Arg) :
    TransM (Imperative.MetaDataElem Core.Expression) := do
  let .op op := arg
    | TransM.error s!"translateMetadataAnnEntry expected op {repr arg}"
  match op.name, op.args with
  | q`Core.mdAnnFlag, #[keyArg] =>
    let key ← translateMetadataAnnKey keyArg
    return { fld := .label key, value := .switch true }
  | q`Core.mdAnnKV, #[keyArg, valArg] =>
    let key ← translateMetadataAnnKey keyArg
    let .op valOp := valArg
      | TransM.error s!"translateMetadataAnnEntry: expected op for value {repr valArg}"
    match valOp.name, valOp.args with
    | q`Core.mdAnnValStr, #[strArg] =>
      let s ← translateStr strArg
      let fld : Imperative.MetaDataElem.Field Core.Expression := .label key
      if fld == Imperative.MetaData.provenanceField ||
         fld == Imperative.MetaData.relatedFileRange ||
         fld == (.label Imperative.MetaData.invariantProvenanceLabel) then
        match parseProvenanceString s with
        | some prov => return { fld, value := .provenance prov }
        | none => return { fld, value := .msg s }
      else
        return { fld := .label key, value := .msg s }
    | q`Core.mdAnnValExpr, _ =>
      TransM.error "translateMetadataAnnEntry: expression values not yet supported"
    | _, _ => TransM.error s!"translateMetadataAnnEntry: unexpected value {repr valOp.name}"
  | _, _ => TransM.error s!"translateMetadataAnnEntry: unexpected {repr op.name}"

/-- Translate an Option MetadataAnn argument into MetaData.
    Returns empty metadata if the annotation is absent. -/
def translateOptMetadataAnn (arg : Arg) :
    TransM (Imperative.MetaData Core.Expression) := do
  let .option _ ann := arg
    | TransM.error s!"translateOptMetadataAnn unexpected {repr arg}"
  match ann with
  | none => return Imperative.MetaData.empty
  | some annArg =>
    let .op annOp := annArg
      | TransM.error s!"translateOptMetadataAnn expected op {repr annArg}"
    let _ ← checkOpArg annArg q`Core.mdAnn 1
    let entries ← translateCommaSep translateMetadataAnnEntry annOp.args[0]!
    return entries

/-- Merge explicit annotation metadata (`annMd`) into source-position metadata
    (`md`).

    `getOpMetaData` derives a `provenance` element from the op's DDM source
    position. There is only ever one `provenance`, so an explicit
    `@[provenance = …]` replaces that derived one instead of being appended
    and ignored. Other keys stay additive. A future metadata validator can
    reject bad input like duplicate `provenance`; for now the last one wins. -/
def mergeAnnMetaData (md annMd : Imperative.MetaData Core.Expression) :
    Imperative.MetaData Core.Expression :=
  let provField : Imperative.MetaDataElem.Field Core.Expression :=
    Imperative.MetaData.provenanceField
  annMd.foldl (init := md) fun acc elem =>
    if elem.fld == provField then
      (acc.eraseElem provField).push elem
    else acc.push elem

/-- Merge explicit annotation metadata into source-position metadata from an op.
    Combines `getOpMetaData` (source positions) with `translateOptMetadataAnn`
    (user-supplied annotations). -/
def getMetaDataWithAnn (op : Operation) (annotsArg : Arg) :
    TransM (Imperative.MetaData Core.Expression) := do
  let annMd ← translateOptMetadataAnn annotsArg
  let md ← getOpMetaData op
  return mergeAnnMetaData md annMd

---------------------------------------------------------------------

inductive GenKind where
  | var_def | axiom_def | assume_def | assert_def | cover_def
  deriving DecidableEq

/--
Counters for assigning default names for various definitions.
-/
structure GenNum where
  var_def : Nat
  axiom_def : Nat
  assume_def : Nat
  assert_def : Nat
  cover_def : Nat
  deriving Repr

/-- A scoped frame of the translator. :) -/
structure TransBindings where
  boundTypeVars : Array TyIdentifier := #[]
  boundVars : Array (LExpr Core.CoreLParams.mono) := #[]
  freeVars  : Array Core.Decl := #[]
  gen : GenNum := (GenNum.mk 0 0 0 0 0)

def getGenCount (gen_kind : GenKind) (g : GenNum) : Nat :=
  match gen_kind with
  | .var_def => g.var_def
  | .axiom_def => g.axiom_def
  | .assume_def => g.assume_def
  | .assert_def => g.assert_def
  | .cover_def => g.cover_def

def incrNum (gen_kind : GenKind) (b : TransBindings) : TransBindings :=
  let gen := b.gen
  let new_gen :=
    match gen_kind with
    | .var_def => { gen with var_def := gen.var_def + 1 }
    | .axiom_def => { gen with axiom_def := gen.axiom_def + 1 }
    | .assume_def => { gen with assume_def := gen.assume_def + 1 }
    | .assert_def => { gen with assert_def := gen.assert_def + 1 }
    | .cover_def => { gen with cover_def := gen.cover_def + 1 }
  { b with gen := new_gen }

/-- Generate a default label and increment the counter for the given kind. -/
def nextLabel (namePrefix : String) (kind : GenKind) (labelArg : Arg)
    (bindings : TransBindings) : TransM (String × TransBindings) := do
  let default_name := s!"{namePrefix}_{getGenCount kind bindings.gen}"
  let bindings := incrNum kind bindings
  let l ← translateOptionLabel default_name labelArg
  return (l, bindings)

instance : ToFormat TransBindings where
  format b := f!"BoundTypeVars: {b.boundTypeVars}\
                {Format.line}\
                BoundVars: {b.boundVars}\
                {Format.line}\
                FreeVars: {b.freeVars}\
                {Format.line}\
                Gen: {repr b.gen}"

instance : Inhabited (List Core.Statement × TransBindings) where
  default := ([], {})

instance : Inhabited Core.Decl where
  default := .type (.con { name := "badguy", params := [] }) .empty

instance : Inhabited (Core.Procedure.CheckAttr) where
  default := .Default

instance : Inhabited (Core.Decl × TransBindings) where
  default := (.type (.con { name := "badguy", params := [] }) .empty, {})

instance : Inhabited (Core.Decls × TransBindings) where
  default := ([], {})

instance : Inhabited (List Core.CoreIdent × TransBindings) where
  default := ([], {})

instance : Inhabited (List TyIdentifier × TransBindings) where
  default := ([], {})

---------------------------------------------------------------------

def translateTypeBinding (bindings : TransBindings) (op : Arg) :
  TransM (TyIdentifier × TransBindings) := do
  -- (FIXME) Account for metadata.
  let bargs ← checkOpArg op q`Core.mkBinding 2
  let id ← translateIdent TyIdentifier bargs[0]!
  -- (TODO) It looks like other elements of `bargs` are irrelevant here?
  -- Perhaps we should not using `Bindings` for type declarations.
  let bindings := { bindings with boundTypeVars := bindings.boundTypeVars ++ [id]}
  return (id, bindings)

def translateTypeBindings (bindings : TransBindings) (ops : Array Arg) :
  TransM ((Array TyIdentifier) × TransBindings) := do
  let (ans, bindings) ← go bindings ops.toList
  return (ans.toArray, bindings)
  where go bindings ops : TransM ((List TyIdentifier) × TransBindings) := do
  match ops with
  | [] => return ([], bindings)
  | op :: orest =>
    let (id, bindings) ← translateTypeBinding bindings op
    let (rid, bindings) ← go bindings orest
    return (id :: rid, bindings)

mutual
partial def translateLMonoTy (bindings : TransBindings) (arg : Arg) :
  TransM LMonoTy := do
  let .type tp := arg
    | TransM.error s!"translateLMonoTy expected type {repr arg}"
  match tp with
  -- Bitvectors are `bv W`, where the width marker `W1 … W128` fixes the width.
  | .ident _ q`Core.bv #[.ident _ q`Core.W1 #[]] => pure <| .bitvec 1
  | .ident _ q`Core.bv #[.ident _ q`Core.W8 #[]] => pure <| .bitvec 8
  | .ident _ q`Core.bv #[.ident _ q`Core.W16 #[]] => pure <| .bitvec 16
  | .ident _ q`Core.bv #[.ident _ q`Core.W32 #[]] => pure <| .bitvec 32
  | .ident _ q`Core.bv #[.ident _ q`Core.W64 #[]] => pure <| .bitvec 64
  | .ident _ q`Core.bv #[.ident _ q`Core.W128 #[]] => pure <| .bitvec 128
  -- A width marker is only meaningful as the argument to `bv`; a bare marker
  -- (or `bv` applied to anything else) is malformed user input, so record the
  -- error and continue with a fallback type rather than panicking.
  | .ident _ q`Core.W1 _ | .ident _ q`Core.W8 _ | .ident _ q`Core.W16 _
  | .ident _ q`Core.W32 _ | .ident _ q`Core.W64 _ | .ident _ q`Core.W128 _ =>
      TransM.recordError s!"bitvector width marker used outside `bv`: {repr tp}" (.bitvec 8)
  | .ident _ q`Core.bv argst =>
      TransM.recordError s!"`bv` expects a width marker `W1 … W128`, got {repr argst}" (.bitvec 8)
  | .ident _ i argst =>
      let argst' ← translateLMonoTys bindings (argst.map ArgF.type)
      pure <| (.tcons i.name argst'.toList.reverse)
  | .fvar _ i argst =>
    assert! i < bindings.freeVars.size
    let decl := bindings.freeVars[i]!
    let ty_core ← match decl with
                  | .type (.con tcons) _md =>
                    -- Type Declaration
                    let ty := tcons.toType
                    -- While the "unsafe" below looks scary, we should be alright as far as
                    -- Core is concerned. See `Core.TypeConstructor`, where there is no
                    -- facility for providing the type arguments.
                    pure ty.toMonoTypeUnsafe
                  | .type (.syn syn) _md =>
                    let ty := syn.toLHSLMonoTy
                    pure ty
                  | .type (.data block) _md =>
                    -- Datatype Declaration (possibly mutual)
                    -- Look up the type name from the GlobalContext using the fvar index
                    let gctx := (← StateT.get).globalContext
                    let ldatatype : LDatatype Unit := match gctx.nameOf? i, block with
                      | some name, _ =>
                        match block.find? (fun (d : LDatatype Unit) => d.name == name) with
                        | some d => d
                        | none => panic! s!"Error: datatype {name} not found in block"
                      | none, d :: _ => d
                      | none, [] => panic! "Empty datatype block"
                    let args := ldatatype.typeArgs.map LMonoTy.ftvar
                    pure (.tcons ldatatype.name args)
                  | _ =>
                    TransM.error
                      s!"translateLMonoTy not yet implemented for this declaration: \
                         {format decl}\n\
                         ty: {repr tp} bindings: {format bindings}"
    match argst with
    | #[] => return ty_core
    | _ =>
      let argst' ← translateLMonoTys bindings (argst.map ArgF.type)
      match ty_core with
      -- (TODO) Is ignoring the args of `.tcons` safe here?
      | .tcons name _ => return (.tcons name argst'.toList.reverse)
      | _ => TransM.error s!"translateLMonoTy not yet implemented {repr tp}"
  | .bvar _ i =>
    assert! i < bindings.boundTypeVars.size
    let var := bindings.boundTypeVars[bindings.boundTypeVars.size - (i+1)]!
    return (.ftvar var)
  | .tvar _ name =>
    return (.ftvar name)
  | .arrow _ arg res =>
    let arg' ← translateLMonoTy bindings (.type arg)
    let res' ← translateLMonoTy bindings (.type res)
    return (.arrow arg' res')

partial def translateLMonoTys (bindings : TransBindings) (args : Array Arg) :
  TransM (Array LMonoTy) :=
  args.mapM (fun a => translateLMonoTy bindings a)
end

def translateTypeVar (op : Arg) : TransM TyIdentifier := do
  let args ← checkOpArg op q`Core.type_var 1
  translateIdent TyIdentifier args[0]!

def translateTypeArgs (op : Arg) : TransM (Array TyIdentifier) := do
  translateOption (fun x => do match x with
                  | none => return Array.empty
                  | some a =>
                    let args ← checkOpArg a q`Core.type_args 1
                    translateCommaSep translateTypeVar args[0]!)
                  op

def translateTypeSynonym (bindings : TransBindings) (op : Operation) :
  TransM (Core.Decl × TransBindings) := do
  let _ ← @checkOp (Core.Decl × TransBindings) op q`Core.command_typesynonym 5
  let annotsArg := op.args[0]!
  let name ← translateIdent TyIdentifier op.args[1]!
  let (targs, bindings) ←
    translateOption
      (fun maybearg =>
            do match maybearg with
            | none => pure ([], bindings)
            | some arg =>
              let bargs ← checkOpArg arg q`Core.mkBindings 1
              let args ←
                  match bargs[0]! with
                  | .seq _ .comma args =>
                    let (arr, bindings) ← translateTypeBindings bindings args
                    return (arr.toList, bindings)
                  | _ => TransM.error
                          s!"translateTypeSynonym expects a comma separated list: {repr bargs[0]!}")
                    op.args[2]!
  let typedef ← translateLMonoTy bindings op.args[4]!
  let md ← getMetaDataWithAnn op annotsArg
  let decl := Core.Decl.type (.syn { name := name, typeArgs := targs, type := typedef }) md
  return (decl, { bindings with freeVars := bindings.freeVars.push decl })


def translateTypeDecl (bindings : TransBindings) (op : Operation) :
  TransM (Core.Decl × TransBindings) := do
  let _ ← @checkOp (Core.Decl × TransBindings) op q`Core.command_typedecl 3
  let annotsArg := op.args[0]!
  let name ← translateIdent TyIdentifier op.args[1]!
  let params ←
    translateOption
      (fun maybearg =>
            do match maybearg with
            | none => pure []
            | some arg =>
              let bargs ← checkOpArg arg q`Core.mkBindings 1
              match bargs[0]! with
              | .seq _ .comma args => do
                args.toList.mapM fun argOp => do
                  let bindArgs ← checkOpArg argOp q`Core.mkBinding 2
                  translateIdent String bindArgs[0]!
              | _ => TransM.error
                      s!"translateTypeDecl expects a comma separated list: {repr bargs[0]!}")
                    op.args[2]!
  let md ← getMetaDataWithAnn op annotsArg
  let decl := Core.Decl.type (.con { name := name, params := params }) md
  return (decl, { bindings with freeVars := bindings.freeVars.push decl })

---------------------------------------------------------------------

def translateBindMk (bindings : TransBindings) (arg : Arg) :
   TransM (Core.CoreIdent × List TyIdentifier × LMonoTy) := do
  let .op op := arg
    | TransM.error s!"translateBindMk expected op {repr arg}"
  match op.name, op.args with
  | q`Core.bind_mk, #[ida, targsa, tpa] =>
    let id ← translateIdent Core.CoreIdent ida
    let args ← translateTypeArgs targsa
    let tp ← translateLMonoTy bindings tpa
    return (id, args.toList, tp)
  | _, _ =>
    TransM.error s!"translateBindMk unimplemented for {repr arg}"

def translateMonoBindMk (bindings : TransBindings) (arg : Arg) :
   TransM (Core.CoreIdent × LMonoTy) := do
  let .op op := arg
    | TransM.error s!"translateMonoBindMk expected op {repr arg}"
  match op.name, op.args with
  | q`Core.mono_bind_mk, #[ida, tpa] =>
    let id ← translateIdent Core.CoreIdent ida
    let tp ← translateLMonoTy bindings tpa
    return (id, tp)
  | _, _ =>
    TransM.error s!"translateMonoBindMk unimplemented for {repr arg}"

partial def translateDeclList (bindings : TransBindings) (arg : Arg) :
  TransM (ListMap Core.Expression.Ident LTy) := do
  let .op op := arg
    | TransM.error s!"translateDeclList expects an op {repr arg}"
  match op.name with
  | q`Core.declAtom =>
    let args ← checkOpArg arg q`Core.declAtom 1
    let (id, targs, mty) ← translateBindMk bindings args[0]!
    let lty := .forAll targs mty
    pure [(id, lty)]
  | q`Core.declPush =>
    let args ← checkOpArg arg q`Core.declPush 2
    let fst ← translateDeclList bindings args[0]!
    let (id, targs, mty) ← translateBindMk bindings args[1]!
    let lty : LTy := .forAll targs mty
    pure (fst ++ ListMap.ofList [(id, lty)])
  | _ => TransM.error s!"translateDeclList unimplemented for {repr op}"

partial def translateMonoDeclList (bindings : TransBindings) (arg : Arg) :
  TransM (ListMap Core.Expression.Ident LMonoTy) := do
  let .op op := arg
    | TransM.error s!"translateMonoDeclList expects an op {repr arg}"
  match op.name with
  | q`Core.monoDeclAtom =>
    let args ← checkOpArg arg q`Core.monoDeclAtom 1
    let (id, mty) ← translateMonoBindMk bindings args[0]!
    pure [(id, mty)]
  | q`Core.monoDeclPush =>
    let args ← checkOpArg arg q`Core.monoDeclPush 2
    let fst ← translateMonoDeclList bindings args[0]!
    let (id, mty) ← translateMonoBindMk bindings args[1]!
    pure (fst ++ ListMap.ofList [(id, mty)])
  | q`Core.mkBindings =>
    let args ← checkOpArg arg q`Core.mkBindings 1
    let .seq _ _ bindingSeq := args[0]!
      | TransM.error s!"mkBindings expects seq {repr args[0]!}"
    let bindings ← bindingSeq.mapM (fun bindingArg => do
      let .op bindingOp := bindingArg
        | TransM.error s!"Expected binding op {repr bindingArg}"
      if bindingOp.name == q`Core.mkBinding then
        let bindingArgs ← checkOpArg bindingArg q`Core.mkBinding 2
        let id ← translateIdent Core.CoreIdent bindingArgs[0]!
        let mty ← translateLMonoTy bindings bindingArgs[1]!
        pure (id, mty)
      else
        TransM.error s!"Expected mkBinding, got {bindingOp.name}")
    pure bindings.toList
  | _ => TransM.error s!"translateMonoDeclList unimplemented for {repr op}"

def translateOptionMonoDeclList (bindings : TransBindings) (arg : Arg) :
  TransM (ListMap Core.Expression.Ident LMonoTy) :=
  translateOption
    (fun maybedecls => do match maybedecls with
        | none => return []
        | some decls => translateMonoDeclList bindings decls)
    arg
---------------------------------------------------------------------

partial def dealiasTypeExpr (p : Program) (te : TypeExpr) : TypeExpr :=
  match te with
  | (.fvar _ idx #[]) =>
    match p.globalContext.kindOf! idx with
    | .expr te => dealiasTypeExpr p te
    | .type [] (.some te) => dealiasTypeExpr p te
    | _ => te
  | _ => te

/-- Hash map from each Core builtin function's qualified identifier to its
    monomorphic Core operator expression; consumed by `translateFn`. Adding a
    new builtin is a one-line entry. The mapping depends only on the
    identifier, not on the expected type. -/
private def translateFnTable : Std.HashMap QualifiedIdent Core.Expression.Expr := .ofList [
  (q`Core.equiv, Core.boolEquivOp),
  (q`Core.implies, Core.boolImpliesOp),
  (q`Core.and, Core.boolAndOp),
  (q`Core.or, Core.boolOrOp),
  (q`Core.not, Core.boolNotOp),

  -- int
  (q`Core.int_neg, Core.intNegOp),
  (q`Core.int_add, Core.intAddOp),
  (q`Core.int_sub, Core.intSubOp),
  (q`Core.int_mul, Core.intMulOp),
  (q`Core.int_div, Core.intDivOp),
  (q`Core.int_mod, Core.intModOp),
  (q`Core.int_safeDiv, Core.intSafeDivOp),
  (q`Core.int_safeMod, Core.intSafeModOp),
  (q`Core.int_divT, Core.intDivTOp),
  (q`Core.int_modT, Core.intModTOp),
  (q`Core.int_safeDivT, Core.intSafeDivTOp),
  (q`Core.int_safeModT, Core.intSafeModTOp),
  (q`Core.int_le, Core.intLeOp),
  (q`Core.int_lt, Core.intLtOp),
  (q`Core.int_ge, Core.intGeOp),
  (q`Core.int_gt, Core.intGtOp),
  -- real
  (q`Core.real_neg, Core.realNegOp),
  (q`Core.real_add, Core.realAddOp),
  (q`Core.real_sub, Core.realSubOp),
  (q`Core.real_mul, Core.realMulOp),
  (q`Core.real_div, Core.realDivOp),
  (q`Core.real_le, Core.realLeOp),
  (q`Core.real_lt, Core.realLtOp),
  (q`Core.real_ge, Core.realGeOp),
  (q`Core.real_gt, Core.realGtOp),
  -- bv1
  (q`Core.bv1_neg, Core.bv1NegOp),
  (q`Core.bv1_add, Core.bv1AddOp),
  (q`Core.bv1_sub, Core.bv1SubOp),
  (q`Core.bv1_mul, Core.bv1MulOp),
  (q`Core.bv1_uDiv, Core.bv1UDivOp),
  (q`Core.bv1_uMod, Core.bv1UModOp),
  (q`Core.bv1_sDiv, Core.bv1SDivOp),
  (q`Core.bv1_sMod, Core.bv1SModOp),
  (q`Core.bv1_not, Core.bv1NotOp),
  (q`Core.bv1_and, Core.bv1AndOp),
  (q`Core.bv1_or, Core.bv1OrOp),
  (q`Core.bv1_xor, Core.bv1XorOp),
  (q`Core.bv1_shl, Core.bv1ShlOp),
  (q`Core.bv1_uShr, Core.bv1UShrOp),
  (q`Core.bv1_sShr, Core.bv1SShrOp),
  (q`Core.bv1_uLe, Core.bv1ULeOp),
  (q`Core.bv1_uLt, Core.bv1ULtOp),
  (q`Core.bv1_uGe, Core.bv1UGeOp),
  (q`Core.bv1_uGt, Core.bv1UGtOp),
  (q`Core.bv1_sLe, Core.bv1SLeOp),
  (q`Core.bv1_sLt, Core.bv1SLtOp),
  (q`Core.bv1_sGe, Core.bv1SGeOp),
  (q`Core.bv1_sGt, Core.bv1SGtOp),
  (q`Core.bv1_safeAdd, Core.bv1SafeAddOp),
  (q`Core.bv1_safeSub, Core.bv1SafeSubOp),
  (q`Core.bv1_safeMul, Core.bv1SafeMulOp),
  (q`Core.bv1_safeUAdd, Core.bv1SafeUAddOp),
  (q`Core.bv1_safeUSub, Core.bv1SafeUSubOp),
  (q`Core.bv1_safeUMul, Core.bv1SafeUMulOp),
  (q`Core.bv1_safeNeg, Core.bv1SafeNegOp),
  (q`Core.bv1_safeUNeg, Core.bv1SafeUNegOp),
  (q`Core.bv1_safeSDiv, Core.bv1SafeSDivOp),
  (q`Core.bv1_safeSMod, Core.bv1SafeSModOp),
  (q`Core.bv1_sNegOverflow, Core.bv1SNegOverflowOp),
  (q`Core.bv1_uNegOverflow, Core.bv1UNegOverflowOp),
  (q`Core.bv1_sAddOverflow, Core.bv1SAddOverflowOp),
  (q`Core.bv1_sSubOverflow, Core.bv1SSubOverflowOp),
  (q`Core.bv1_sMulOverflow, Core.bv1SMulOverflowOp),
  (q`Core.bv1_sDivOverflow, Core.bv1SDivOverflowOp),
  (q`Core.bv1_uAddOverflow, Core.bv1UAddOverflowOp),
  (q`Core.bv1_uSubOverflow, Core.bv1USubOverflowOp),
  (q`Core.bv1_uMulOverflow, Core.bv1UMulOverflowOp),
  -- bv8
  (q`Core.bv8_neg, Core.bv8NegOp),
  (q`Core.bv8_add, Core.bv8AddOp),
  (q`Core.bv8_sub, Core.bv8SubOp),
  (q`Core.bv8_mul, Core.bv8MulOp),
  (q`Core.bv8_uDiv, Core.bv8UDivOp),
  (q`Core.bv8_uMod, Core.bv8UModOp),
  (q`Core.bv8_sDiv, Core.bv8SDivOp),
  (q`Core.bv8_sMod, Core.bv8SModOp),
  (q`Core.bv8_not, Core.bv8NotOp),
  (q`Core.bv8_and, Core.bv8AndOp),
  (q`Core.bv8_or, Core.bv8OrOp),
  (q`Core.bv8_xor, Core.bv8XorOp),
  (q`Core.bv8_shl, Core.bv8ShlOp),
  (q`Core.bv8_uShr, Core.bv8UShrOp),
  (q`Core.bv8_sShr, Core.bv8SShrOp),
  (q`Core.bv8_uLe, Core.bv8ULeOp),
  (q`Core.bv8_uLt, Core.bv8ULtOp),
  (q`Core.bv8_uGe, Core.bv8UGeOp),
  (q`Core.bv8_uGt, Core.bv8UGtOp),
  (q`Core.bv8_sLe, Core.bv8SLeOp),
  (q`Core.bv8_sLt, Core.bv8SLtOp),
  (q`Core.bv8_sGe, Core.bv8SGeOp),
  (q`Core.bv8_sGt, Core.bv8SGtOp),
  (q`Core.bv8_safeAdd, Core.bv8SafeAddOp),
  (q`Core.bv8_safeSub, Core.bv8SafeSubOp),
  (q`Core.bv8_safeMul, Core.bv8SafeMulOp),
  (q`Core.bv8_safeUAdd, Core.bv8SafeUAddOp),
  (q`Core.bv8_safeUSub, Core.bv8SafeUSubOp),
  (q`Core.bv8_safeUMul, Core.bv8SafeUMulOp),
  (q`Core.bv8_safeNeg, Core.bv8SafeNegOp),
  (q`Core.bv8_safeUNeg, Core.bv8SafeUNegOp),
  (q`Core.bv8_safeSDiv, Core.bv8SafeSDivOp),
  (q`Core.bv8_safeSMod, Core.bv8SafeSModOp),
  (q`Core.bv8_sNegOverflow, Core.bv8SNegOverflowOp),
  (q`Core.bv8_uNegOverflow, Core.bv8UNegOverflowOp),
  (q`Core.bv8_sAddOverflow, Core.bv8SAddOverflowOp),
  (q`Core.bv8_sSubOverflow, Core.bv8SSubOverflowOp),
  (q`Core.bv8_sMulOverflow, Core.bv8SMulOverflowOp),
  (q`Core.bv8_sDivOverflow, Core.bv8SDivOverflowOp),
  (q`Core.bv8_uAddOverflow, Core.bv8UAddOverflowOp),
  (q`Core.bv8_uSubOverflow, Core.bv8USubOverflowOp),
  (q`Core.bv8_uMulOverflow, Core.bv8UMulOverflowOp),
  -- bv16
  (q`Core.bv16_neg, Core.bv16NegOp),
  (q`Core.bv16_add, Core.bv16AddOp),
  (q`Core.bv16_sub, Core.bv16SubOp),
  (q`Core.bv16_mul, Core.bv16MulOp),
  (q`Core.bv16_uDiv, Core.bv16UDivOp),
  (q`Core.bv16_uMod, Core.bv16UModOp),
  (q`Core.bv16_sDiv, Core.bv16SDivOp),
  (q`Core.bv16_sMod, Core.bv16SModOp),
  (q`Core.bv16_not, Core.bv16NotOp),
  (q`Core.bv16_and, Core.bv16AndOp),
  (q`Core.bv16_or, Core.bv16OrOp),
  (q`Core.bv16_xor, Core.bv16XorOp),
  (q`Core.bv16_shl, Core.bv16ShlOp),
  (q`Core.bv16_uShr, Core.bv16UShrOp),
  (q`Core.bv16_sShr, Core.bv16SShrOp),
  (q`Core.bv16_uLe, Core.bv16ULeOp),
  (q`Core.bv16_uLt, Core.bv16ULtOp),
  (q`Core.bv16_uGe, Core.bv16UGeOp),
  (q`Core.bv16_uGt, Core.bv16UGtOp),
  (q`Core.bv16_sLe, Core.bv16SLeOp),
  (q`Core.bv16_sLt, Core.bv16SLtOp),
  (q`Core.bv16_sGe, Core.bv16SGeOp),
  (q`Core.bv16_sGt, Core.bv16SGtOp),
  (q`Core.bv16_safeAdd, Core.bv16SafeAddOp),
  (q`Core.bv16_safeSub, Core.bv16SafeSubOp),
  (q`Core.bv16_safeMul, Core.bv16SafeMulOp),
  (q`Core.bv16_safeUAdd, Core.bv16SafeUAddOp),
  (q`Core.bv16_safeUSub, Core.bv16SafeUSubOp),
  (q`Core.bv16_safeUMul, Core.bv16SafeUMulOp),
  (q`Core.bv16_safeNeg, Core.bv16SafeNegOp),
  (q`Core.bv16_safeUNeg, Core.bv16SafeUNegOp),
  (q`Core.bv16_safeSDiv, Core.bv16SafeSDivOp),
  (q`Core.bv16_safeSMod, Core.bv16SafeSModOp),
  (q`Core.bv16_sNegOverflow, Core.bv16SNegOverflowOp),
  (q`Core.bv16_uNegOverflow, Core.bv16UNegOverflowOp),
  (q`Core.bv16_sAddOverflow, Core.bv16SAddOverflowOp),
  (q`Core.bv16_sSubOverflow, Core.bv16SSubOverflowOp),
  (q`Core.bv16_sMulOverflow, Core.bv16SMulOverflowOp),
  (q`Core.bv16_sDivOverflow, Core.bv16SDivOverflowOp),
  (q`Core.bv16_uAddOverflow, Core.bv16UAddOverflowOp),
  (q`Core.bv16_uSubOverflow, Core.bv16USubOverflowOp),
  (q`Core.bv16_uMulOverflow, Core.bv16UMulOverflowOp),
  -- bv32
  (q`Core.bv32_neg, Core.bv32NegOp),
  (q`Core.bv32_add, Core.bv32AddOp),
  (q`Core.bv32_sub, Core.bv32SubOp),
  (q`Core.bv32_mul, Core.bv32MulOp),
  (q`Core.bv32_uDiv, Core.bv32UDivOp),
  (q`Core.bv32_uMod, Core.bv32UModOp),
  (q`Core.bv32_sDiv, Core.bv32SDivOp),
  (q`Core.bv32_sMod, Core.bv32SModOp),
  (q`Core.bv32_not, Core.bv32NotOp),
  (q`Core.bv32_and, Core.bv32AndOp),
  (q`Core.bv32_or, Core.bv32OrOp),
  (q`Core.bv32_xor, Core.bv32XorOp),
  (q`Core.bv32_shl, Core.bv32ShlOp),
  (q`Core.bv32_uShr, Core.bv32UShrOp),
  (q`Core.bv32_sShr, Core.bv32SShrOp),
  (q`Core.bv32_uLe, Core.bv32ULeOp),
  (q`Core.bv32_uLt, Core.bv32ULtOp),
  (q`Core.bv32_uGe, Core.bv32UGeOp),
  (q`Core.bv32_uGt, Core.bv32UGtOp),
  (q`Core.bv32_sLe, Core.bv32SLeOp),
  (q`Core.bv32_sLt, Core.bv32SLtOp),
  (q`Core.bv32_sGe, Core.bv32SGeOp),
  (q`Core.bv32_sGt, Core.bv32SGtOp),
  (q`Core.bv32_safeAdd, Core.bv32SafeAddOp),
  (q`Core.bv32_safeSub, Core.bv32SafeSubOp),
  (q`Core.bv32_safeMul, Core.bv32SafeMulOp),
  (q`Core.bv32_safeUAdd, Core.bv32SafeUAddOp),
  (q`Core.bv32_safeUSub, Core.bv32SafeUSubOp),
  (q`Core.bv32_safeUMul, Core.bv32SafeUMulOp),
  (q`Core.bv32_safeNeg, Core.bv32SafeNegOp),
  (q`Core.bv32_safeUNeg, Core.bv32SafeUNegOp),
  (q`Core.bv32_safeSDiv, Core.bv32SafeSDivOp),
  (q`Core.bv32_safeSMod, Core.bv32SafeSModOp),
  (q`Core.bv32_sNegOverflow, Core.bv32SNegOverflowOp),
  (q`Core.bv32_uNegOverflow, Core.bv32UNegOverflowOp),
  (q`Core.bv32_sAddOverflow, Core.bv32SAddOverflowOp),
  (q`Core.bv32_sSubOverflow, Core.bv32SSubOverflowOp),
  (q`Core.bv32_sMulOverflow, Core.bv32SMulOverflowOp),
  (q`Core.bv32_sDivOverflow, Core.bv32SDivOverflowOp),
  (q`Core.bv32_uAddOverflow, Core.bv32UAddOverflowOp),
  (q`Core.bv32_uSubOverflow, Core.bv32USubOverflowOp),
  (q`Core.bv32_uMulOverflow, Core.bv32UMulOverflowOp),
  -- bv64
  (q`Core.bv64_neg, Core.bv64NegOp),
  (q`Core.bv128_neg, Core.bv128NegOp),
  (q`Core.bv64_add, Core.bv64AddOp),
  (q`Core.bv128_add, Core.bv128AddOp),
  (q`Core.bv64_sub, Core.bv64SubOp),
  (q`Core.bv128_sub, Core.bv128SubOp),
  (q`Core.bv64_mul, Core.bv64MulOp),
  (q`Core.bv128_mul, Core.bv128MulOp),
  (q`Core.bv64_uDiv, Core.bv64UDivOp),
  (q`Core.bv128_uDiv, Core.bv128UDivOp),
  (q`Core.bv64_uMod, Core.bv64UModOp),
  (q`Core.bv128_uMod, Core.bv128UModOp),
  (q`Core.bv64_sDiv, Core.bv64SDivOp),
  (q`Core.bv128_sDiv, Core.bv128SDivOp),
  (q`Core.bv64_sMod, Core.bv64SModOp),
  (q`Core.bv128_sMod, Core.bv128SModOp),
  (q`Core.bv64_not, Core.bv64NotOp),
  (q`Core.bv128_not, Core.bv128NotOp),
  (q`Core.bv64_and, Core.bv64AndOp),
  (q`Core.bv128_and, Core.bv128AndOp),
  (q`Core.bv64_or, Core.bv64OrOp),
  (q`Core.bv128_or, Core.bv128OrOp),
  (q`Core.bv64_xor, Core.bv64XorOp),
  (q`Core.bv128_xor, Core.bv128XorOp),
  (q`Core.bv64_shl, Core.bv64ShlOp),
  (q`Core.bv128_shl, Core.bv128ShlOp),
  (q`Core.bv64_uShr, Core.bv64UShrOp),
  (q`Core.bv128_uShr, Core.bv128UShrOp),
  (q`Core.bv64_sShr, Core.bv64SShrOp),
  (q`Core.bv128_sShr, Core.bv128SShrOp),
  (q`Core.bv64_uLe, Core.bv64ULeOp),
  (q`Core.bv128_uLe, Core.bv128ULeOp),
  (q`Core.bv64_uLt, Core.bv64ULtOp),
  (q`Core.bv128_uLt, Core.bv128ULtOp),
  (q`Core.bv64_uGe, Core.bv64UGeOp),
  (q`Core.bv128_uGe, Core.bv128UGeOp),
  (q`Core.bv64_uGt, Core.bv64UGtOp),
  (q`Core.bv128_uGt, Core.bv128UGtOp),
  (q`Core.bv64_sLe, Core.bv64SLeOp),
  (q`Core.bv128_sLe, Core.bv128SLeOp),
  (q`Core.bv64_sLt, Core.bv64SLtOp),
  (q`Core.bv128_sLt, Core.bv128SLtOp),
  (q`Core.bv64_sGe, Core.bv64SGeOp),
  (q`Core.bv128_sGe, Core.bv128SGeOp),
  (q`Core.bv64_sGt, Core.bv64SGtOp),
  (q`Core.bv128_sGt, Core.bv128SGtOp),
  (q`Core.bv64_safeAdd, Core.bv64SafeAddOp),
  (q`Core.bv128_safeAdd, Core.bv128SafeAddOp),
  (q`Core.bv64_safeSub, Core.bv64SafeSubOp),
  (q`Core.bv128_safeSub, Core.bv128SafeSubOp),
  (q`Core.bv64_safeMul, Core.bv64SafeMulOp),
  (q`Core.bv128_safeMul, Core.bv128SafeMulOp),
  (q`Core.bv64_safeUAdd, Core.bv64SafeUAddOp),
  (q`Core.bv128_safeUAdd, Core.bv128SafeUAddOp),
  (q`Core.bv64_safeUSub, Core.bv64SafeUSubOp),
  (q`Core.bv128_safeUSub, Core.bv128SafeUSubOp),
  (q`Core.bv64_safeUMul, Core.bv64SafeUMulOp),
  (q`Core.bv128_safeUMul, Core.bv128SafeUMulOp),
  (q`Core.bv64_safeNeg, Core.bv64SafeNegOp),
  (q`Core.bv128_safeNeg, Core.bv128SafeNegOp),
  (q`Core.bv64_safeUNeg, Core.bv64SafeUNegOp),
  (q`Core.bv128_safeUNeg, Core.bv128SafeUNegOp),
  (q`Core.bv64_safeSDiv, Core.bv64SafeSDivOp),
  (q`Core.bv128_safeSDiv, Core.bv128SafeSDivOp),
  (q`Core.bv64_safeSMod, Core.bv64SafeSModOp),
  (q`Core.bv128_safeSMod, Core.bv128SafeSModOp),
  (q`Core.bv64_sNegOverflow, Core.bv64SNegOverflowOp),
  (q`Core.bv128_sNegOverflow, Core.bv128SNegOverflowOp),
  (q`Core.bv64_uNegOverflow, Core.bv64UNegOverflowOp),
  (q`Core.bv128_uNegOverflow, Core.bv128UNegOverflowOp),
  (q`Core.bv64_sAddOverflow, Core.bv64SAddOverflowOp),
  (q`Core.bv128_sAddOverflow, Core.bv128SAddOverflowOp),
  (q`Core.bv64_sSubOverflow, Core.bv64SSubOverflowOp),
  (q`Core.bv128_sSubOverflow, Core.bv128SSubOverflowOp),
  (q`Core.bv64_sMulOverflow, Core.bv64SMulOverflowOp),
  (q`Core.bv128_sMulOverflow, Core.bv128SMulOverflowOp),
  (q`Core.bv64_sDivOverflow, Core.bv64SDivOverflowOp),
  (q`Core.bv128_sDivOverflow, Core.bv128SDivOverflowOp),
  (q`Core.bv64_uAddOverflow, Core.bv64UAddOverflowOp),
  (q`Core.bv128_uAddOverflow, Core.bv128UAddOverflowOp),
  (q`Core.bv64_uSubOverflow, Core.bv64USubOverflowOp),
  (q`Core.bv128_uSubOverflow, Core.bv128USubOverflowOp),
  (q`Core.bv64_uMulOverflow, Core.bv64UMulOverflowOp),
  (q`Core.bv128_uMulOverflow, Core.bv128UMulOverflowOp),
  -- bitvector -> int casts
  (q`Core.bv1_toUInt, .op () ⟨"Bv1.ToUInt", ()⟩ (.some (.arrow (.bitvec 1) .int))),
  (q`Core.bv1_toInt, .op () ⟨"Bv1.ToInt",  ()⟩ (.some (.arrow (.bitvec 1) .int))),
  (q`Core.bv8_toUInt, .op () ⟨"Bv8.ToUInt", ()⟩ (.some (.arrow (.bitvec 8) .int))),
  (q`Core.bv8_toInt, .op () ⟨"Bv8.ToInt",  ()⟩ (.some (.arrow (.bitvec 8) .int))),
  (q`Core.bv16_toUInt, .op () ⟨"Bv16.ToUInt", ()⟩ (.some (.arrow (.bitvec 16) .int))),
  (q`Core.bv16_toInt, .op () ⟨"Bv16.ToInt",  ()⟩ (.some (.arrow (.bitvec 16) .int))),
  (q`Core.bv32_toUInt, .op () ⟨"Bv32.ToUInt", ()⟩ (.some (.arrow (.bitvec 32) .int))),
  (q`Core.bv32_toInt, .op () ⟨"Bv32.ToInt",  ()⟩ (.some (.arrow (.bitvec 32) .int))),
  (q`Core.bv64_toUInt, .op () ⟨"Bv64.ToUInt", ()⟩ (.some (.arrow (.bitvec 64) .int))),
  (q`Core.bv64_toInt, .op () ⟨"Bv64.ToInt",  ()⟩ (.some (.arrow (.bitvec 64) .int))),
  (q`Core.bv128_toUInt, .op () ⟨"Bv128.ToUInt", ()⟩ (.some (.arrow (.bitvec 128) .int))),
  (q`Core.bv128_toInt, .op () ⟨"Bv128.ToInt",  ()⟩ (.some (.arrow (.bitvec 128) .int))),

  (q`Core.bvconcat8, Core.bv8ConcatOp),
  (q`Core.bvconcat16, Core.bv16ConcatOp),
  (q`Core.bvconcat32, Core.bv32ConcatOp),
  (q`Core.bvextract_7_7, Core.bv8Extract_7_7_Op),
  (q`Core.bvextract_15_15, Core.bv16Extract_15_15_Op),
  (q`Core.bvextract_31_31, Core.bv32Extract_31_31_Op),
  (q`Core.bvextract_7_0_16, Core.bv16Extract_7_0_Op),
  (q`Core.bvextract_7_0_32, Core.bv32Extract_7_0_Op),
  (q`Core.bvextract_15_0_32, Core.bv32Extract_15_0_Op),
  (q`Core.bvextract_7_0_64, Core.bv64Extract_7_0_Op),
  (q`Core.bvextract_15_0_64, Core.bv64Extract_15_0_Op),
  (q`Core.bvextract_31_0_64, Core.bv64Extract_31_0_Op),




  (q`Core.str_len, Core.strLengthOp),
  (q`Core.str_concat, Core.strConcatOp),
  (q`Core.str_substr, Core.strSubstrOp),
  (q`Core.str_toregex, Core.strToRegexOp),
  (q`Core.str_inregex, Core.strInRegexOp),
  (q`Core.str_prefixof, Core.strPrefixOfOp),
  (q`Core.str_suffixof, Core.strSuffixOfOp),
  (q`Core.str_contains, Core.strContainsOp),
  (q`Core.str_indexof, Core.strIndexOfOp),
  (q`Core.str_replace, Core.strReplaceOp),
  (q`Core.str_at, Core.strAtOp),
  (q`Core.str_lt, Core.strLtOp),
  (q`Core.str_le, Core.strLeOp),
  (q`Core.re_all, Core.reAllOp),
  (q`Core.re_allchar, Core.reAllCharOp),
  (q`Core.re_range, Core.reRangeOp),
  (q`Core.re_concat, Core.reConcatOp),
  (q`Core.re_star, Core.reStarOp),
  (q`Core.re_plus, Core.rePlusOp),
  (q`Core.re_loop, Core.reLoopOp),
  (q`Core.re_union, Core.reUnionOp),
  (q`Core.re_inter, Core.reInterOp),
  (q`Core.re_comp, Core.reCompOp),
  (q`Core.re_none, Core.reNoneOp),
]

def translateFn (ty? : Option LMonoTy) (q : QualifiedIdent) : TransM Core.Expression.Expr :=
  match translateFnTable[q]? with
  | some op => return op
  | none => TransM.error s!"translateFn: Unknown/unimplemented function {repr q} at type {repr ty?}"

/-- Extract the operator name from a grouped-operator wrapper's first argument.

Type-specific operators (`int.add`, `bv8.uLt`, …) are grouped in the grammar: a
handful of wrapper `fn`s in `Expr` (`binaryArithBasic`, `unaryArith`, …) each take
a leading category argument (`BinaryArithBasic`, `UnaryArith`, …) whose nullary op
*is* the operator name (`Core.int_add`, `Core.bv8_uLt`, …). This reads that name so
`translateFn` can map it to the monomorphic Core op. -/
private def translateOpGroupName (a : Arg) : TransM QualifiedIdent := do
  let .op op := a
    | TransM.error s!"translateOpGroupName expected op {repr a}"
  match op.args with
  | #[] => return op.name
  | _ => TransM.error s!"translateOpGroupName: expected nullary op, got {repr op.name}"

mutual

/-- Shared binding setup for lambdas and quantifiers: translates the declaration list,
    creates scoped bound variables, and translates the body in the extended scope. -/
partial
def withScopedBindings
  (p : Program)
  (bindings : TransBindings) (xsa : Arg) (bodya : Arg) :
  TransM (ListMap Core.Expression.Ident Core.Expression.Ty × TransBindings × Core.Expression.Expr) := do
    let xsArray ← translateDeclList bindings xsa
    let n := xsArray.size
    let newBoundVars := List.toArray (xsArray.mapIdx (fun i _ => LExpr.bvar () (n - 1 - i)))
    let boundVars' := bindings.boundVars ++ newBoundVars
    let xbindings := { bindings with boundVars := boundVars' }
    let b ← translateExpr p xbindings bodya
    return (xsArray, xbindings, b)

partial
def translateLambda
  (p : Program)
  (bindings : TransBindings) (xsa : Arg) (bodya : Arg) :
  TransM Core.Expression.Expr := do
    let (xsArray, _, b) ← withScopedBindings p bindings xsa bodya
    let buildLambda := fun (name, ty) e =>
      match ty with
      | .forAll [] mty =>
        .abs () name.name (.some mty) e
      | _ => panic! s!"Expected monomorphic type in lambda, got: {ty}" -- nopanic:ok
    return xsArray.foldr buildLambda (init := b)

/-- Translate a `have x : T = value in body` binding. `body` is translated with
    `x` in scope (reusing `withScopedBindings`, as `lambda` does); `value` is
    translated in the outer scope. Desugars to `(λ x : T. body) value` via
    `LExpr.mkHave`. -/
partial
def translateHave
  (p : Program)
  (bindings : TransBindings) (xsa : Arg) (vala : Arg) (bodya : Arg) :
  TransM Core.Expression.Expr := do
    let (xsArray, _, body) ← withScopedBindings p bindings xsa bodya
    let (name, ty) ← match xsArray.toList with
      | [b] => pure b
      | _ => TransM.error s!"have binding expects exactly one variable, got {xsArray.toList.length}"
    let mty ← match ty with
      | .forAll [] mty => pure mty
      | _ => TransM.error s!"Expected monomorphic type in have binding, got: {ty}"
    let value ← translateExpr p bindings vala
    return LExpr.mkHave () name.name (.some mty) value body

partial
def translateQuantifier
  (qk: QuantifierKind)
  (p : Program)
  (bindings : TransBindings) (xsa : Arg) (triggersa: Option Arg) (bodya: Arg) :
  TransM Core.Expression.Expr := do
    let (xsArray, xbindings, b) ← withScopedBindings p bindings xsa bodya

    -- Handle triggers if present
    let triggers ← match triggersa with
      | none => pure (LExpr.noTrigger ())
      | some tsa => translateTriggers p xbindings tsa

    -- Create one quantifier constructor per variable
    -- Trigger attached to only the innermost quantifier
    let buildQuantifier := fun (name, ty) (e, first) =>
      match ty with
      | .forAll [] mty =>
        let triggers := if first then
            triggers
          else
            LExpr.noTrigger ()
        (.quant () qk name.name (.some mty) triggers e, false)
      | _ => panic! s!"Expected monomorphic type in quantifier, got: {ty}"

    return xsArray.foldr buildQuantifier (init := (b, true)) |>.1

partial
def translateTriggerGroup (p: Program) (bindings : TransBindings) (arg : Arg) :
  TransM Core.Expression.Expr := do
  let .op op := arg
    | TransM.error s!"translateTriggerGroup expected op, got {repr arg}"
  match op.name, op.args with
  | q`Core.trigger, #[tsa] => do
   let ts  ← translateCommaSep (fun t => translateExpr p bindings t) tsa
   return ts.foldl (fun g t => .app () (.app () Core.addTriggerOp t) g) Core.emptyTriggerGroupOp
  | _, _ => panic! s!"Unexpected operator in trigger group"

partial
def translateTriggers (p: Program) (bindings : TransBindings) (arg : Arg) :
  TransM Core.Expression.Expr := do
  let .op op := arg
    | TransM.error s!"translateTriggers expected op, got: {repr arg}"
  match op.name, op.args with
  | q`Core.triggersAtom, #[group] =>
    let g ← translateTriggerGroup p bindings group
    return .app () (.app () Core.addTriggerGroupOp g) Core.emptyTriggersOp
  | q`Core.triggersPush, #[triggers, group] => do
    let ts ← translateTriggers p bindings triggers
    let g ← translateTriggerGroup p bindings group
    return .app () (.app () Core.addTriggerGroupOp g) ts
  | _, _ => panic! s!"Unexpected operator in trigger"

/-- Resolve a function from a `recFuncBlock` by its global-context index. -/
partial def resolveRecFunc (funcs : List Core.Function) (idx : Nat) : TransM Core.Function := do
  let gctx := (← StateT.get).globalContext
  match gctx.nameOf? idx with
  | some name =>
    match funcs.find? (fun f => f.name.name == name) with
    | some f => pure f
    | none => TransM.error s!"function {name} not found in recFuncBlock"
  | none => TransM.error s!"resolveRecFunc: no name for index {idx} in global context"

partial def translateExpr (p : Program) (bindings : TransBindings) (arg : Arg) :
  TransM Core.Expression.Expr := do
  let .expr expr := arg
    | TransM.error s!"translateExpr expected expr {repr arg}"
  let (op, args) := expr.flatten
  match op, args with
  -- Constants/Literals
  | .fn _ q`Core.btrue, [] =>
    return .true ()
  | .fn _ q`Core.bfalse, [] =>
    return .false ()
  | .fn _ q`Core.natToInt, [xa] =>
    let n ← translateNat xa
    return .intConst () n
  | .fn _ q`Core.bv1Lit, [xa] =>
    let n ← translateBitVec 1 xa
    return .bitvecConst () 1 n
  | .fn _ q`Core.bv8Lit, [xa] =>
    let n ← translateBitVec 8 xa
    return .bitvecConst () 8 n
  | .fn _ q`Core.bv16Lit, [xa] =>
    let n ← translateBitVec 16 xa
    return .bitvecConst () 16 n
  | .fn _ q`Core.bv32Lit, [xa] =>
    let n ← translateBitVec 32 xa
    return .bitvecConst () 32 n
  | .fn _ q`Core.bv64Lit, [xa] =>
    let n ← translateBitVec 64 xa
    return .bitvecConst () 64 n
  | .fn _ q`Core.bv128Lit, [xa] =>
    let n ← translateBitVec 128 xa
    return .bitvecConst () 128 n
  | .fn _ q`Core.strLit, [xa] =>
    let x ← translateStr xa
    return .strConst () x
  | .fn _ q`Core.realLit, [xa] =>
    let x ← translateReal xa
    return .realConst () (StrataDDM.Decimal.toRat x)
  | .fn _ q`Core.fracLit, [na, da] =>
    let num ← translateNat na
    let den ← translateNat da
    if den == 0 then
      -- A zero denominator is invalid user input, so record the error
      -- and fall back to `realConst 0`.
      TransM.recordError "fracLit: denominator must be non-zero" (.realConst () 0)
    else
      return .realConst () (Core.FracLit.fracDecode num den)
  -- Equality
  | .fn _ q`Core.equal, [_tpa, xa, ya] =>
    let x ← translateExpr p bindings xa
    let y ← translateExpr p bindings ya
    return .eq () x y
  | .fn _ q`Core.not_equal, [_tpa, xa, ya] =>
    let x ← translateExpr p bindings xa
    let y ← translateExpr p bindings ya
    return (.app () Core.boolNotOp (.eq () x y))
  -- Int → Bv casts
  | .fn _ q`Core.as_bv1,   [xa] => return .app () (.op () ⟨"Int.ToBv1",   ()⟩ (.some (.arrow .int (.bitvec 1))))   (← translateExpr p bindings xa)
  | .fn _ q`Core.as_bv8,   [xa] => return .app () (.op () ⟨"Int.ToBv8",   ()⟩ (.some (.arrow .int (.bitvec 8))))   (← translateExpr p bindings xa)
  | .fn _ q`Core.as_bv16,  [xa] => return .app () (.op () ⟨"Int.ToBv16",  ()⟩ (.some (.arrow .int (.bitvec 16))))  (← translateExpr p bindings xa)
  | .fn _ q`Core.as_bv32,  [xa] => return .app () (.op () ⟨"Int.ToBv32",  ()⟩ (.some (.arrow .int (.bitvec 32))))  (← translateExpr p bindings xa)
  | .fn _ q`Core.as_bv64,  [xa] => return .app () (.op () ⟨"Int.ToBv64",  ()⟩ (.some (.arrow .int (.bitvec 64))))  (← translateExpr p bindings xa)
  | .fn _ q`Core.as_bv128, [xa] => return .app () (.op () ⟨"Int.ToBv128", ()⟩ (.some (.arrow .int (.bitvec 128)))) (← translateExpr p bindings xa)
  -- If-then-else expression
  | .fn _ q`Core.if, [_tpa, ca, ta, fa] =>
    let c ← translateExpr p bindings ca
    let t ← translateExpr p bindings ta
    let f ← translateExpr p bindings fa
    return .ite () c t f
  -- Re.AllChar
  | .fn _ q`Core.re_allchar, [] =>
    let fn ← translateFn .none q`Core.re_allchar
    return fn
  -- Re.None
  | .fn _ q`Core.re_none, [] =>
    let fn ← translateFn .none q`Core.re_none
    return fn
  -- Re.All
  | .fn _ q`Core.re_all, [] =>
    let fn ← translateFn .none q`Core.re_all
    return fn
  -- Sequence.empty (1 type arg, 0 value args)
  | .fn _ q`Core.seq_empty, [atp] =>
     let ety ← translateLMonoTy bindings atp
     let fn : LExpr Core.CoreLParams.mono :=
       Core.coreOpExpr (.seq .Empty)
         (.some (Core.seqTy ety))
     return fn
  -- Unary function applications
  | .fn _ fni, [xa] =>
    match fni with
    | q`Core.not
    | q`Core.bvextract_7_7
    | q`Core.bvextract_15_15
    | q`Core.bvextract_31_31
    | q`Core.bvextract_7_0_16
    | q`Core.bvextract_7_0_32
    | q`Core.bvextract_15_0_32
    | q`Core.bvextract_7_0_64
    | q`Core.bvextract_15_0_64
    | q`Core.bvextract_31_0_64
    | q`Core.str_len
    | q`Core.str_toregex
    | q`Core.re_star
    | q`Core.re_plus
    | q`Core.re_comp => do
      let fn ← translateFn .none fni
      let x ← translateExpr p bindings xa
      return .mkApp () fn [x]
    | _ => TransM.error s!"translateExpr unimplemented {repr op} {repr args}"
  -- Grouped type-specific unary operators. The wrapper's first arg names
  -- the operation (`int.neg`, `bv8.not`, `bv8.toUInt`, …); `translateFn` maps it
  -- to the monomorphic Core op.
  | .fn _ q`Core.unaryArithInt, [fa, xa]
  | .fn _ q`Core.unaryArithReal, [fa, xa]
  -- Bitvector unary wrappers are width-polymorphic (`unaryArithBv (W : Type, f,
  -- a : bv W)`); the `W` slot is a placeholder `resolve` fills from the operand,
  -- so it is ignored here. The operation (including width) is the nullary op
  -- `fa` (e.g. `Core.bv8_neg`), which `translateFn` matches to a Core op.
  | .fn _ q`Core.unaryArithBv, [_, fa, xa]
  | .fn _ q`Core.unarySafeBv, [_, fa, xa]
  | .fn _ q`Core.unaryOverflowBv, [_, fa, xa]
  | .fn _ q`Core.castBv, [_, fa, xa] =>
    let fn ← translateFn .none (← translateOpGroupName fa)
    let x ← translateExpr p bindings xa
    return .mkApp () fn [x]
  -- Grouped type-specific binary operators. The wrapper's first arg names
  -- the operation (`int.add`, `bv8.uLt`, `bv8.sAddOverflow`, …).
  | .fn _ q`Core.binaryArithBasicInt, [fa, xa, ya]
  | .fn _ q`Core.binaryArithBasicReal, [fa, xa, ya]
  | .fn _ q`Core.binaryArithDivModInt, [fa, xa, ya]
  | .fn _ q`Core.binaryArithDivModReal, [fa, xa, ya]
  | .fn _ q`Core.binarySafeInt, [fa, xa, ya]
  | .fn _ q`Core.binaryTruncInt, [fa, xa, ya]
  | .fn _ q`Core.binaryCmpBaseInt, [fa, xa, ya]
  | .fn _ q`Core.binaryCmpBaseReal, [fa, xa, ya]
  -- Bitvector binary wrappers are width-polymorphic (`… (W : Type, f, a b : bv
  -- W)`); the `W` slot is a placeholder `resolve` fills from the operands, so it
  -- is ignored here. The operation (including width) is the nullary op `fa`
  -- (e.g. `Core.bv8_uLt`), which `translateFn` matches to a Core op.
  | .fn _ q`Core.binaryArithBasicBv, [_, fa, xa, ya]
  | .fn _ q`Core.binaryArithDivModBv, [_, fa, xa, ya]
  | .fn _ q`Core.binaryBitwiseBv, [_, fa, xa, ya]
  | .fn _ q`Core.binarySafeBv, [_, fa, xa, ya]
  | .fn _ q`Core.binaryCmpBaseBv, [_, fa, xa, ya]
  | .fn _ q`Core.binaryCmpSignedBv, [_, fa, xa, ya]
  | .fn _ q`Core.binaryOverflowBv, [_, fa, xa, ya] =>
    let fn ← translateFn .none (← translateOpGroupName fa)
    let x ← translateExpr p bindings xa
    let y ← translateExpr p bindings ya
    return .mkApp () fn [x, y]
  -- Strings
  | .fn _ q`Core.str_concat, [xa, ya] =>
     let x ← translateExpr p bindings xa
     let y ← translateExpr p bindings ya
     return .mkApp () Core.strConcatOp [x, y]
  | .fn _ q`Core.str_substr, [xa, ia, na] =>
     let x ← translateExpr p bindings xa
     let i ← translateExpr p bindings ia
     let n ← translateExpr p bindings na
     return .mkApp () Core.strSubstrOp [x, i, n]
  | .fn _ q`Core.str_indexof, [xa, ya, ia] =>
     let x ← translateExpr p bindings xa
     let y ← translateExpr p bindings ya
     let i ← translateExpr p bindings ia
     return .mkApp () Core.strIndexOfOp [x, y, i]
  | .fn _ q`Core.str_replace, [xa, ya, za] =>
     let x ← translateExpr p bindings xa
     let y ← translateExpr p bindings ya
     let z ← translateExpr p bindings za
     return .mkApp () Core.strReplaceOp [x, y, z]
  | .fn _ q`Core.old, [_tp, xa] =>
     let x ← translateExpr p bindings xa
     match x with
     | .fvar m ident ty => return .fvar m (Core.CoreIdent.mkOld ident.name) ty
     | _ => TransM.error s!"old: expected an identifier, got {x}"
  -- Map get/set: key and value types are implicit in the surface syntax. Like
  -- the seq operators, the type arguments are left as placeholders and Core's
  -- `resolve` recovers them from the map argument. (map_const below keeps its
  -- annotation — its key type cannot be recovered from the value argument.)
  | .fn _ q`Core.map_get, [_ktp, _vtp, ma, ia] =>
     let fn : LExpr Core.CoreLParams.mono := Core.coreOpExpr (.map .Select)
     let m ← translateExpr p bindings ma
     let i ← translateExpr p bindings ia
     return .mkApp () fn [m, i]
  | .fn _ q`Core.map_set, [_ktp, _vtp, ma, ia, xa] =>
     let fn : LExpr Core.CoreLParams.mono := Core.coreOpExpr (.map .Update)
     let m ← translateExpr p bindings ma
     let i ← translateExpr p bindings ia
     let x ← translateExpr p bindings xa
     return .mkApp () fn [m, i, x]
  | .fn _ q`Core.map_const, [ktp, vtp, va] =>
     let kty ← translateLMonoTy bindings ktp
     let vty ← translateLMonoTy bindings vtp
     let fn : LExpr Core.CoreLParams.mono := (Core.coreOpExpr (.map .Const) (.some (LMonoTy.mkArrow vty [Core.mapTy kty vty])))
     let v ← translateExpr p bindings va
     return .mkApp () fn [v]
  -- Seq operations. The type parameter is implicit in the surface syntax, so
  -- the type argument is left as a placeholder; Core's `resolve` recovers the
  -- element type from the sequence argument.
  | .fn _ q`Core.seq_length, [_, sa] =>
     let fn : LExpr Core.CoreLParams.mono := Core.coreOpExpr (.seq .Length)
     let s ← translateExpr p bindings sa
     return .mkApp () fn [s]
  | .fn _ q`Core.seq_select, [_, sa, ia] =>
     let fn : LExpr Core.CoreLParams.mono := Core.coreOpExpr (.seq .Select)
     let s ← translateExpr p bindings sa
     let i ← translateExpr p bindings ia
     return .mkApp () fn [s, i]
  | .fn _ q`Core.seq_select_unsafe, [_, sa, ia] =>
     let fn : LExpr Core.CoreLParams.mono := Core.coreOpExpr (.seq .SelectUnsafe)
     let s ← translateExpr p bindings sa
     let i ← translateExpr p bindings ia
     return .mkApp () fn [s, i]
  | .fn _ q`Core.seq_append, [_, s1a, s2a] =>
     let fn : LExpr Core.CoreLParams.mono := Core.coreOpExpr (.seq .Append)
     let s1 ← translateExpr p bindings s1a
     let s2 ← translateExpr p bindings s2a
     return .mkApp () fn [s1, s2]
  | .fn _ q`Core.seq_build, [_, sa, va] =>
     let fn : LExpr Core.CoreLParams.mono := Core.coreOpExpr (.seq .Build)
     let s ← translateExpr p bindings sa
     let v ← translateExpr p bindings va
     return .mkApp () fn [s, v]
  | .fn _ q`Core.seq_update, [_, sa, ia, va] =>
     let fn : LExpr Core.CoreLParams.mono := Core.coreOpExpr (.seq .Update)
     let s ← translateExpr p bindings sa
     let i ← translateExpr p bindings ia
     let v ← translateExpr p bindings va
     return .mkApp () fn [s, i, v]
  | .fn _ q`Core.seq_update_unsafe, [_, sa, ia, va] =>
     let fn : LExpr Core.CoreLParams.mono := Core.coreOpExpr (.seq .UpdateUnsafe)
     let s ← translateExpr p bindings sa
     let i ← translateExpr p bindings ia
     let v ← translateExpr p bindings va
     return .mkApp () fn [s, i, v]
  | .fn _ q`Core.seq_contains, [_, sa, va] =>
     let fn : LExpr Core.CoreLParams.mono := Core.coreOpExpr (.seq .Contains)
     let s ← translateExpr p bindings sa
     let v ← translateExpr p bindings va
     return .mkApp () fn [s, v]
  | .fn _ q`Core.seq_take, [_, sa, na] =>
     let fn : LExpr Core.CoreLParams.mono := Core.coreOpExpr (.seq .Take)
     let s ← translateExpr p bindings sa
     let n ← translateExpr p bindings na
     return .mkApp () fn [s, n]
  | .fn _ q`Core.seq_take_unsafe, [_, sa, na] =>
     let fn : LExpr Core.CoreLParams.mono := Core.coreOpExpr (.seq .TakeUnsafe)
     let s ← translateExpr p bindings sa
     let n ← translateExpr p bindings na
     return .mkApp () fn [s, n]
  | .fn _ q`Core.seq_drop, [_, sa, na] =>
     let fn : LExpr Core.CoreLParams.mono := Core.coreOpExpr (.seq .Drop)
     let s ← translateExpr p bindings sa
     let n ← translateExpr p bindings na
     return .mkApp () fn [s, n]
  | .fn _ q`Core.seq_drop_unsafe, [_, sa, na] =>
     let fn : LExpr Core.CoreLParams.mono := Core.coreOpExpr (.seq .DropUnsafe)
     let s ← translateExpr p bindings sa
     let n ← translateExpr p bindings na
     return .mkApp () fn [s, n]
  -- Lambda abstraction
  | .fn _ q`Core.lambda, [_, xsa, ba] =>
    translateLambda p bindings xsa ba
  -- "have" binding: have x : T = value in body
  | .fn _ q`Core.have_expr, [_, _, xsa, vala, ba] =>
    translateHave p bindings xsa vala ba
  -- Expression application: (f)(x)
  | .fn _ q`Core.apply_expr, [_, _, fa, xa] => do
    let f ← translateExpr p bindings fa
    let x ← translateExpr p bindings xa
    return .app () f x
  -- Quantifiers
  | .fn _ q`Core.forall, [xsa, ba] =>
    translateQuantifier .all p bindings xsa .none ba
  | .fn _ q`Core.exists, [xsa, ba] =>
    translateQuantifier .exist p bindings xsa .none ba
  | .fn _ q`Core.forallT, [xsa, tsa, ba] =>
    translateQuantifier .all p bindings xsa (.some tsa) ba
  | .fn _ q`Core.existsT, [xsa, tsa, ba] =>
    translateQuantifier .exist p bindings xsa (.some tsa) ba
  -- Binary function applications (monomorphic)
  | .fn _ fni, [xa, ya] =>
    let fn ← translateFn .none fni
    let x ← translateExpr p bindings xa
    let y ← translateExpr p bindings ya
    return .mkApp () fn [x, y]
  | .fn _ q`Core.re_loop, [xa, ya, za] =>
    let fn ← translateFn .none q`Core.re_loop
    let x ← translateExpr p bindings xa
    let y ← translateExpr p bindings ya
    let z ← translateExpr p bindings za
    return .mkApp () fn [x, y, z]
  -- NOTE: Bound and free variables are numbered differently. Bound variables
  -- ascending order (so closer to deBrujin levels).
  | .bvar _ i, argsa => do
    if i < bindings.boundVars.size then
      let expr := bindings.boundVars[bindings.boundVars.size - (i+1)]!
      match argsa with
      | [] =>
        match expr with
        | .bvar m _ => return .bvar m i
        | _ => return expr
      | _ =>
        let args ← translateExprs p bindings argsa.toArray
        return .mkApp () expr args.toList
    else
      -- Bound variable index exceeds boundVars - check if it's a local function
      let funcIndex := i - bindings.boundVars.size
      if funcIndex < bindings.freeVars.size then
        let decl := bindings.freeVars[funcIndex]!
        match decl with
        | .func func _md =>
          match argsa with
          | [] => return func.opExpr
          | _ =>
            let args ← translateExprs p bindings argsa.toArray
            return .mkApp () func.opExpr args.toList
        | .recFuncBlock funcs _md =>
          let func ← resolveRecFunc funcs funcIndex
          match argsa with
          | [] => return func.opExpr
          | _ =>
            let args ← translateExprs p bindings argsa.toArray
            return .mkApp () func.opExpr args.toList
        | _ => TransM.error s!"translateExpr out-of-range bound variable: {i}"
      else
        TransM.error s!"translateExpr out-of-range bound variable: {i}"
  | .fvar _ i, [] =>
    assert! i < bindings.freeVars.size
    let decl := bindings.freeVars[i]!
    let ty? ← match p.globalContext.kindOf! i with
              |.expr te => pure (some (← translateLMonoTy bindings (.type te)))
              | _ => pure none
    match decl with
    | .func func _md =>
      -- 0-ary Function
      return (.op () func.name ty?)
    | .recFuncBlock funcs _md =>
      let func ← resolveRecFunc funcs i
      return (.op () func.name ty?)
    | _ =>
      TransM.error s!"translateExpr unimplemented fvar decl (no args): {format decl}"
  | .fvar _ i, argsa =>
    -- Call of a function declared/defined in Core.
    assert! i < bindings.freeVars.size
    let decl := bindings.freeVars[i]!
    match decl with
    | .func func _md =>
      let args ← translateExprs p bindings argsa.toArray
      return .mkApp () func.opExpr args.toList
    | .recFuncBlock funcs _md =>
      let func ← resolveRecFunc funcs i
      let args ← translateExprs p bindings argsa.toArray
      return .mkApp () func.opExpr args.toList
    | _ =>
     TransM.error s!"translateExpr unimplemented fvar decl: {format decl} \nargs:{repr argsa}"
  | op, args =>
    TransM.error s!"translateExpr unimplemented op:\n\
                     Op: {repr op}\n\
                     Args: {repr args}\n\
                     Bindings: {format bindings}}"

partial def translateExprs (p : Program) (bindings : TransBindings) (args : Array Arg) :
  TransM (Array Core.Expression.Expr) :=
  args.mapM (fun a => translateExpr p bindings a)
end

---------------------------------------------------------------------

def translateInvariant (p : Program) (bindings : TransBindings) (arg : Arg) :
    TransM (List (String × Core.Expression.Expr)) := do
  match arg with
  | .option _ (.some m) => do
    -- invariant takes: label (Option Label), e (Expr)
    let args ← checkOpArg m q`Core.invariant 2
    let label ← translateOptionLabel "" args[0]!
    let e ← translateExpr p bindings args[1]!
    pure [(label, e)]
  | _ => pure []

partial def translateInvariants (p : StrataDDM.Program) (bindings : TransBindings) (arg : Arg) :
  TransM (List (String × Core.Expression.Expr)) := do
  let .op op := arg
    | TransM.error s!"translateInvariants expects an op {repr arg}"
  match op.name with
  | q`Core.nilInvariants =>
    pure []
  | q`Core.consInvariants =>
    -- consInvariants takes: label (Option Label), e (Expr), is (Invariants)
    let args ← checkOpArg arg q`Core.consInvariants 3
    let label ← translateOptionLabel "" args[0]!
    let i ← translateExpr p bindings args[1]!
    let is ← translateInvariants p bindings args[2]!
    pure ((label, i)::is)
  | _ => TransM.error s!"translateInvariants unimplemented for {repr op}"

def translateMeasure (p : Program) (bindings : TransBindings) (arg : Arg) :
    TransM (Option Core.Expression.Expr) := do
  match arg with
  | .option _ (.some m) =>
    let args ← checkOpArg m q`Core.measure_mk 1
    let e ← translateExpr p bindings args[0]!
    pure (some e)
  | _ => pure none


def initVarStmts (tpids : ListMap Core.Expression.Ident LTy) (bindings : TransBindings)
    (md : MetaData Core.Expression):
  TransM ((List Core.Statement) × TransBindings) := do
  match tpids with
  | [] => return ([], bindings)
  | (id, tp) :: rest =>
    let s := Core.Statement.init id tp .nondet md
    let (stmts, bindings) ← initVarStmts rest bindings md
    return ((s :: stmts), bindings)

def translateVarStatement (bindings : TransBindings) (annotsArg : Arg) (decls : Array Arg)
    (md : MetaData Core.Expression):
  TransM ((List Core.Statement) × TransBindings) := do
  if decls.size != 1 then
    TransM.error s!"translateVarStatement unexpected decls length {repr decls}"
  else
    let md := mergeAnnMetaData md (← translateOptMetadataAnn annotsArg)
    let tpids ← translateDeclList bindings decls[0]!
    let (stmts, bindings) ← initVarStmts tpids bindings md
    let newVars ← tpids.mapM (fun (id, ty) =>
                    if h: ty.isMonoType then
                      return ((LExpr.fvar () id (ty.toMonoType h)): LExpr Core.CoreLParams.mono)
                    else
                      TransM.error s!"translateVarStatement requires {id} to have a monomorphic type, but it has type {ty}")
    let bbindings := bindings.boundVars ++ newVars
    return (stmts, { bindings with boundVars := bbindings })

def translateInitStatement (p : Program) (bindings : TransBindings) (annotsArg : Arg)
    (args : Array Arg) (md : MetaData Core.Expression):
  TransM ((List Core.Statement) × TransBindings) := do
  if args.size != 3 then
    TransM.error "translateInitStatement unexpected arg length {repr decls}"
  else
    let md := mergeAnnMetaData md (← translateOptMetadataAnn annotsArg)
    let mty ← translateLMonoTy bindings args[0]!
    let lhs ← translateIdent Core.CoreIdent args[1]!
    let val ← translateExpr p bindings args[2]!
    let ty := (.forAll [] mty)
    let newBinding: LExpr Core.CoreLParams.mono := LExpr.fvar () lhs mty
    let bbindings := bindings.boundVars ++ [newBinding]
    return ([.init lhs ty (.det val) md], { bindings with boundVars := bbindings })


/-- Translate an ExprOrNondet argument to ExprOrNondet. -/
private def translateCondBool (p : Program) (bindings : TransBindings) (a : Arg) :
    TransM (Imperative.ExprOrNondet Core.Expression) := do
  let .op op := a
    | TransM.error s!"translateCondBool expected op {repr a}"
  match op.name, op.args with
  | q`Core.condNondet, #[] => pure .nondet
  | q`Core.condDet, #[ca] => pure (.det (← translateExpr p bindings ca))
  | _, _ => TransM.error s!"translateCondBool: unexpected {repr op.name}"

/-- Build a nested map-update expression: `nestMapUpdate base [i1, i2] v` produces
    `map_update(base, i1, map_update(map_select(base, i1), i2, v))`. -/
private def nestMapUpdate (base : Core.Expression.Expr) (idxs : List Core.Expression.Expr)
    (rhs : Core.Expression.Expr) : Core.Expression.Expr :=
  let selectOp := Core.coreOpExpr (.map .Select)
  let updateOp := Core.coreOpExpr (.map .Update)
  match idxs with
  | [] => rhs
  | [i] => .mkApp () updateOp [base, i, rhs]
  | i :: rest =>
    let inner := .mkApp () selectOp [base, i]
    let updatedInner := nestMapUpdate inner rest rhs
    .mkApp () updateOp [base, i, updatedInner]

/-- Decompose an LHS into a base identifier and a (reversed) list of index
    expressions. For `m[k1][k2]`, returns `(m, [k2, k1])`. -/
partial def translateLhsParts (p : Program) (bindings : TransBindings) (arg : Arg) :
    TransM (Core.CoreIdent × List Core.Expression.Expr) := do
  let .op op := arg
    | TransM.error s!"translateLhsParts expected op {repr arg}"
  match op.name, op.args with
  | q`Core.lhsIdent, #[id] =>
    let ident ← translateIdent Core.CoreIdent id
    return (ident, [])
  | q`Core.lhsArray, #[_tpa, lhsa, idxa] =>
    let (ident, idxsRev) ← translateLhsParts p bindings lhsa
    let idx ← translateExpr p bindings idxa
    return (ident, idx :: idxsRev)
  | _, _ => TransM.error s!"translateLhsParts: unimplemented for {repr arg}"

mutual
partial def translateFnPreconds (p : Program) (name : Core.CoreIdent) (bindings : TransBindings) (arg : Arg) :
  TransM (List (Strata.DL.Util.FuncPrecondition Core.Expression.Expr Core.Expression.ExprMetadata)) := do
  let .seq _ sep args := arg
    | TransM.error s!"translateFnPreconds expected seq {repr arg}"
  if sep != .none && sep != .spacePrefix then
    TransM.error s!"translateFnPreconds unexpected separator {repr sep}"
  let preconds ← args.foldlM (init := ([], 0)) fun (acc, count) specElt => do
    let .op op := specElt
      | TransM.error s!"translateFnPreconds expected op {repr specElt}"
    match op.name with
    | q`Core.requires_spec =>
      let args ← checkOpArg specElt q`Core.requires_spec 3
      let _l ← translateOptionLabel s!"{name.name}_requires_{count}" args[0]!
      let e ← translateExpr p bindings args[2]!
      return (acc ++ [⟨e, ()⟩], count + 1)
    | _ => TransM.error s!"translateFnPreconds: only requires allowed, got {repr op.name}"
  return preconds.1

/-- Translate an assert/cover/assume statement with optional metadata annotations. -/
partial def translateLabeledCheck (p : Program) (bindings : TransBindings) (op : Operation)
    (namePrefix : String) (kind : GenKind) (annotsArg la ca : Arg)
    (mk : String → Core.Expression.Expr → MetaData Core.Expression → Core.Statement)
    (promoteLabelToSummary : Bool := false) :
    TransM (List Core.Statement × TransBindings) := do
  let c ← translateExpr p bindings ca
  let userLabel? ← translateOptionLabel? la
  let (l, bindings) ← nextLabel namePrefix kind la bindings
  let md ← getMetaDataWithAnn op annotsArg
  -- A user-written label (`assert [name]: ...`) is the author's own description
  -- of the obligation, so record it as the user-facing property summary (unless
  -- one is already set). Failed-VC diagnostics then describe the assertion by
  -- that summary rather than exposing the internal obligation label; obligations
  -- with no user label keep the generic description and are told apart by their
  -- source location. Auto-generated labels (`assert_N`) are not promoted.
  let md := match promoteLabelToSummary, userLabel? with
    | true, some ul => if md.getPropertySummary.isSome then md else md.withPropertySummary ul
    | _, _ => md
  return ([mk l c md], bindings)

partial def translateStmt (p : Program) (bindings : TransBindings) (arg : Arg) :
  TransM (List Core.Statement × TransBindings) := do
  let .op op := arg
    | TransM.error s!"translateStmt expected op {repr arg}"

  match op.name, op.args with
  | q`Core.varStatement, #[annotsArg, declsArg] =>
    translateVarStatement bindings annotsArg #[declsArg] (← getOpMetaData op)
  | q`Core.initStatement, #[annotsArg, tpa, va, ea] =>
    translateInitStatement p bindings annotsArg #[tpa, va, ea] (← getOpMetaData op)
  | q`Core.assign, #[annotsArg, _tpa, lhsa, ea] =>
    let (lhs, idxsRev) ← translateLhsParts p bindings lhsa
    let val ← translateExpr p bindings ea
    let md ← getMetaDataWithAnn op annotsArg
    let rhs := match idxsRev.reverse with
      | [] => val
      | idxs => nestMapUpdate (.fvar () lhs none) idxs val
    return ([.set lhs rhs md], bindings)
  | q`Core.havoc_statement, #[annotsArg, ida] =>
    let id ← translateIdent Core.CoreIdent ida
    let md ← getMetaDataWithAnn op annotsArg
    return ([.havoc id md], bindings)
  | q`Core.assert, #[annotsArg, la, ca] =>
    translateLabeledCheck p bindings op "assert" .assert_def annotsArg la ca .assert
      (promoteLabelToSummary := true)
  | q`Core.cover, #[annotsArg, la, ca] =>
    translateLabeledCheck p bindings op "cover" .cover_def annotsArg la ca .cover
  | q`Core.assume, #[annotsArg, la, ca] =>
    translateLabeledCheck p bindings op "assume" .assume_def annotsArg la ca .assume
  | q`Core.if_statement, #[annotsArg, ca, ta, fa] =>
    let (tss, thenBindings) ← translateBlock p bindings ta
    let (fss, elseBindings) ← translateElse p { bindings with gen := thenBindings.gen } fa
    let md ← getMetaDataWithAnn op annotsArg
    let cond ← translateCondBool p bindings ca
    return ([.ite cond tss fss md], { bindings with gen := elseBindings.gen })
  | q`Core.while_statement, #[annotsArg, ca, ma, ia, ba] =>
    let measure ← translateMeasure p bindings ma
    let invs ← translateInvariants p bindings ia
    let (bodyss, bindings) ← translateBlock p bindings ba
    let md ← getMetaDataWithAnn op annotsArg
    let guard ← translateCondBool p bindings ca
    return ([.loop guard measure invs bodyss md], bindings)
  | q`Core.call_statement, #[annotsArg, fa, callArgsa] =>
    let f ← translateIdent String fa
    let .seq _ .comma rawArgs := callArgsa
      | TransM.error s!"Expected comma-separated call args: {repr callArgsa}"
    let mut callArgs : List (Core.CallArg Core.Expression) := []
    for a in rawArgs do
      let .op aop := a
        | TransM.error s!"translateCallArg expects an op: {repr a}"
      match aop.name with
      | q`Core.callArgOut =>
        let bargs ← checkOpArg a q`Core.callArgOut 1
        callArgs := callArgs ++ [.outArg (← translateIdent Core.CoreIdent bargs[0]!)]
      | q`Core.callArgInout =>
        let bargs ← checkOpArg a q`Core.callArgInout 1
        callArgs := callArgs ++ [.inoutArg (← translateIdent Core.CoreIdent bargs[0]!)]
      | q`Core.callArgExpr =>
        let bargs ← checkOpArg a q`Core.callArgExpr 1
        callArgs := callArgs ++ [.inArg (← translateExpr p bindings bargs[0]!)]
      | _ => TransM.error s!"translateCallArg: unexpected op {repr aop.name}"
    let md ← getMetaDataWithAnn op annotsArg
    return ([.call f callArgs md], bindings)
  | q`Core.block_statement, #[annotsArg, la, ba] =>
    let l ← translateIdent String la
    let (ss, innerBindings) ← translateBlock p bindings ba
    let md ← getMetaDataWithAnn op annotsArg
    return ([.block l ss md], { bindings with gen := innerBindings.gen })
  | q`Core.exit_statement, #[annotsArg, la] =>
    let l ← translateIdent String la
    let md ← getMetaDataWithAnn op annotsArg
    return ([.exit l md], bindings)
  | q`Core.funcDecl_statement, #[annotsArg, namea, _typeArgsa, bindingsa, returna, precondsa, bodya, _inlinea] =>
    let name ← translateIdent Core.CoreIdent namea
    let inputs ← translateMonoDeclList bindings bindingsa
    let outputMono ← translateLMonoTy bindings returna
    let output : Core.Expression.Ty := .forAll [] outputMono
    let inputsConverted : ListMap Core.Expression.Ident Core.Expression.Ty :=
      inputs.map (fun (id, mty) => (id, .forAll [] mty))

    -- The DDM parser's @[scope(b)] on the body adds only the parameters.
    -- The function name is NOT in scope inside the body (declareFn adds it
    -- for subsequent statements only). So body bindings = outer + parameters.
    let funcType := Lambda.LMonoTy.mkArrow' outputMono inputs.values
    let funcBinding : LExpr Core.CoreLParams.mono := .op () name (some funcType)
    let in_bindings := (inputs.map (fun (v, ty) => (LExpr.fvar () v ty))).toArray

    let bodyBindings := { bindings with boundVars := bindings.boundVars ++ in_bindings }
    -- Translate preconditions
    let preconds ← translateFnPreconds p name bodyBindings precondsa

    let body ← match bodya with
      | .option _ (.some bodyExpr) => do
        let expr ← translateExpr p bodyBindings bodyExpr
        pure (some expr)
      | .option _ .none => pure none
      | _ => do
        let expr ← translateExpr p bodyBindings bodya
        pure (some expr)

    let decl : PureFunc Core.Expression := {
      name := name,
      inputs := inputsConverted,
      output := output,
      body := body,
      axioms := [],
      preconditions := preconds
    }
    let md ← getMetaDataWithAnn op annotsArg
    -- Add the function to boundVars for subsequent statements.
    let updatedBindings := { bindings with boundVars := bindings.boundVars.push funcBinding }
    return ([.funcDecl decl md], updatedBindings)
  | q`Core.typeDecl_statement, #[annotsArg, namea, argsa] =>
    let name ← translateIdent String namea
    let (typeParams : List String) ← match argsa with
      | .option _ (.some binds) => do
        let bargs ← checkOpArg binds q`Core.mkBindings 1
        match bargs[0]! with
        | .seq _ .comma args => do
          args.toList.mapM fun argOp => do
            let bindArgs ← checkOpArg argOp q`Core.mkBinding 2
            translateIdent String bindArgs[0]!
        | _ => TransM.error
                s!"typeDecl_statement expects a comma separated list: {repr bargs[0]!}"
      | .option _ .none => pure []
      | _ => TransM.error s!"Invalid type arguments {repr argsa}"
    let md ← getMetaDataWithAnn op annotsArg

    -- Create a TypeConstructor and add it to freeVars (same as program-level types)
    let tc : TypeConstructor := { name := name, params := typeParams }
    let typeDecl : Core.Decl := .type (.con tc) md

    -- Add type parameters (not the type name itself) to boundTypeVars
    -- This matches what the DDM parser does with declareType
    let updatedBindings := { bindings with
      freeVars := bindings.freeVars.push typeDecl,
      boundTypeVars := bindings.boundTypeVars ++ typeParams.toArray }

    return ([.typeDecl tc md], updatedBindings)
  | name, args => TransM.error s!"Unexpected statement {name.fullName} with {args.size} arguments."

partial def translateBlock (p : Program) (bindings : TransBindings) (arg : Arg) :
  TransM ((List Core.Statement) × TransBindings) := do
  let args ← checkOpArg arg q`Core.block 1
  let .seq _ .newline stmts := args[0]!
    | TransM.error s!"Invalid block {repr args[0]!}"
  let (a, bindings) ← stmts.foldlM (init := (#[], bindings)) fun (a, b) s => do
      let (s, b) ← translateStmt p b s
      return (a.append s.toArray, b)
  return (a.toList, bindings)

partial def translateElse (p : Program) (bindings : TransBindings) (arg : Arg) :
  TransM ((List Core.Statement) × TransBindings) := do
  let .op op := arg
    | TransM.error s!"translateElse expected op {repr arg}"
  match op.name with
  | q`Core.else0 =>
    let _ ← checkOpArg arg q`Core.else0 0
    return ([], bindings)
  | q`Core.else1 =>
    let args ← checkOpArg arg q`Core.else1 1
    translateBlock p bindings args[0]!
  | _ => TransM.error s!"translateElse unimplemented for {repr arg}"

end

---------------------------------------------------------------------

inductive BindingKind where
  | input | out | inout | cases
  deriving DecidableEq, Repr

def translateInitMkBinding (bindings : TransBindings) (op : Arg) :
  TransM (Core.CoreIdent × LMonoTy × BindingKind) := do
  let (opName, kind) := match op with
    | .op o =>
      if o.name == q`Core.casesBinding then (q`Core.casesBinding, BindingKind.cases)
      else if o.name == q`Core.outBinding then (q`Core.outBinding, BindingKind.out)
      else if o.name == q`Core.inoutBinding then (q`Core.inoutBinding, BindingKind.inout)
      else (q`Core.mkBinding, BindingKind.input)
    | _ => (q`Core.mkBinding, BindingKind.input)
  let bargs ← checkOpArg op opName 2
  let id ← translateIdent Core.CoreIdent bargs[0]!
  let tp ← translateLMonoTy bindings bargs[1]!
  return (id, tp, kind)

def translateInitMkBindings (bindings : TransBindings) (ops : Array Arg) :
  TransM (Array (Core.CoreIdent × LMonoTy × BindingKind)) := do
  ops.mapM (fun op => translateInitMkBinding bindings op)

def translateBindings (bindings : TransBindings) (op : Arg) :
  TransM (ListMap Core.CoreIdent LMonoTy) := do
  let bargs ← checkOpArg op q`Core.mkBindings 1
  match bargs[0]! with
  | .seq _ .comma args =>
    let arr ← translateInitMkBindings bindings args
    return arr.toList.map fun (id, ty, _) => (id, ty)
  | _ =>
    TransM.error s!"translateBindings expects a comma separated list: {repr op}"

/-- Like `translateBindings` but also returns the index of the `@[cases]` parameter, if any. -/
def translateBindingsWithCases (bindings : TransBindings) (op : Arg) :
  TransM (ListMap Core.CoreIdent LMonoTy × Option Nat) := do
  let bargs ← checkOpArg op q`Core.mkBindings 1
  match bargs[0]! with
  | .seq _ .comma args =>
    let arr ← translateInitMkBindings bindings args
    let sig := arr.toList.map fun (id, ty, _) => (id, ty)
    let casesCount := arr.toList.filter (fun x => x.2.2 == .cases) |>.length
    if casesCount > 1 then
      TransM.error s!"Only one @[cases] parameter is allowed, but {casesCount} were found"
    let casesIdx := arr.toList.findIdx? fun (_, _, c) => c == .cases
    return (sig, casesIdx)
  | _ =>
    TransM.error s!"translateBindingsWithCases expects a comma separated list: {repr op}"

def translateOptionFree (arg : Arg) : TransM Core.Procedure.CheckAttr := do
  let .option _ free := arg
    | TransM.error s!"translateOptionFree unexpected {repr arg}"
  match free with
  | some f =>
    let _ ← checkOpArg f q`Core.free 0
    return .Free
  | none => return .Default

def translateRequires (p : Program) (name : Core.CoreIdent) (count : Nat) (bindings : TransBindings) (arg : Arg) :
  TransM (ListMap Core.CoreLabel Core.Procedure.Check) := do
  let args ← checkOpArg arg q`Core.requires_spec 3
  let l ← translateOptionLabel s!"{name.name}_requires_{count}" args[0]!
  let free? ← translateOptionFree args[1]!
  let e ← translateExpr p bindings args[2]!
  let md ← getArgMetaData arg
  return [(l, { expr := e, attr := free?, md := md })]

def translateEnsures (p : Program) (name : Core.CoreIdent) (count : Nat) (bindings : TransBindings) (arg : Arg) :
  TransM (ListMap Core.CoreLabel Core.Procedure.Check) := do
  let args ← checkOpArg arg q`Core.ensures_spec 3
  let l ← translateOptionLabel s!"{name.name}_ensures_{count}" args[0]!
  let free? ← translateOptionFree args[1]!
  let e ← translateExpr p bindings args[2]!
  let md ← getArgMetaData arg
  return [(l, { expr := e, attr := free?, md := md })]

def translateSpecElem (p : Program) (name : Core.CoreIdent) (count : Nat) (bindings : TransBindings) (arg : Arg) :
  TransM (ListMap Core.CoreLabel Core.Procedure.Check × ListMap Core.CoreLabel Core.Procedure.Check) := do
  let .op op := arg
    | TransM.error s!"translateSpecElem expects an op {repr arg}"
  match op.name with
  | q`Core.requires_spec =>
    let elem ← translateRequires p name count bindings arg
    return (elem, [])
  | q`Core.ensures_spec =>
    let elem ← translateEnsures p name count bindings arg
    return ([], elem)
  | _ =>
    TransM.error s!"translateSpecElem unimplemented for {repr arg}"

partial def translateSpec (p : Program) (name : Core.CoreIdent) (bindings : TransBindings) (arg : Arg) :
  TransM (ListMap Core.CoreLabel Core.Procedure.Check × ListMap Core.CoreLabel Core.Procedure.Check) := do
  let sargs ← checkOpArg arg q`Core.spec_mk 1
  let .seq _ .none args := sargs[0]!
    | TransM.error s!"Invalid specs {repr sargs[0]!}"
  go 0 args.size args
  where go (count max : Nat) (args : Array Arg) := do
  match (max - count) with
  | 0 => return ([], [])
  | _ + 1 =>
    let arg := args[count]!
    let (reqs, ens) ← translateSpecElem p name count bindings arg
    let (restreqs, restens) ← go (count + 1) max args
    return (reqs ++ restreqs, ens ++ restens)

/-- Translate a procedure's parameter bindings (the `mkBindings` arg `bop`) and
    push the body's variable scope.

    Returns the partitioned input/output signatures for the header, together with
    `bindings` extended by the parameter scope. The declaration-order invariant
    lives here: the body's de Bruijn indices are assigned against the *original
    textual order*, not the input/output partition, so the scope binds every
    parameter in declaration order. -/
def translateProcBindings (bindings : TransBindings) (bop : Arg) :
  TransM (ListMap Core.CoreIdent LMonoTy × ListMap Core.CoreIdent LMonoTy × TransBindings) := do
  let bargs ← checkOpArg bop q`Core.mkBindings 1
  let params ← match bargs[0]! with
    | .seq _ .comma args => translateInitMkBindings bindings args
    | _ => TransM.error s!"translateProcBindings expects a comma separated list: {repr bop}"
  -- Header signatures: partition by `out`/`inout` modifiers (`inout` is both an
  -- input and an output).
  let inputs := params.toList.filterMap fun (id, ty, kind) =>
    if kind == .input || kind == .inout || kind == .cases then some (id, ty) else none
  let outputs := params.toList.filterMap fun (id, ty, kind) =>
    if kind == .out || kind == .inout then some (id, ty) else none
  -- Body scope: bind every parameter once in original declaration order — the
  -- body's de Bruijn indices are assigned against that order, not the
  -- input/output partition.
  let param_bindings := params.map (fun (id, ty, _) => LExpr.fvar () id ty)
  return (inputs, outputs, { bindings with boundVars := bindings.boundVars ++ param_bindings })

def translateProcedure (p : Program) (bindings : TransBindings) (op : Operation) :
  TransM (Core.Decl × TransBindings) := do
  let _ ← @checkOp (Core.Decl × TransBindings) op q`Core.command_procedure 6
  let annotsArg := op.args[0]!
  let pname ← translateIdent Core.CoreIdent op.args[1]!
  let typeArgs ← translateTypeArgs op.args[2]!
  let origBindings := bindings
  let (sig, ret, bindings) ← translateProcBindings bindings op.args[3]!
  let .option _ speca := op.args[4]!
    | TransM.error s!"translateProcedure spec. expected here: {repr op.args[4]!}"
  let (requires, ensures) ←
    if speca.isSome then translateSpec p pname bindings speca.get! else pure ([], [])
  let .option _ bodya := op.args[5]!
    | TransM.error s!"translateProcedure body expected here: {repr op.args[5]!}"
  let (body, bindings) ← if bodya.isSome then translateBlock p bindings bodya.get! else pure ([], bindings)
  let origBindings := { origBindings with gen := bindings.gen }
  let md ← getMetaDataWithAnn op annotsArg
  return (.proc { header := { name := pname,
                              typeArgs := typeArgs.toList,
                              inputs := sig,
                              outputs := ret },
                  spec := { preconditions := requires,
                            postconditions := ensures },
                  body := .structured body
                }
                md,
          origBindings)

---------------------------------------------------------------------

/-- Translate a top-level block command as a nameless parameterless procedure -/
def translateBlockCommand (p : Program) (bindings : TransBindings) (op : Operation) :
  TransM (Core.Decl × TransBindings) := do
  let _ ← @checkOp (Core.Decl × TransBindings) op q`Core.command_block 1
  let (body, bindings) ← translateBlock p bindings op.args[0]!
  let md ← getOpMetaData op
  return (.proc { header := { name := "",
                              typeArgs := [],
                              inputs := [],
                              outputs := [] },
                  spec := { preconditions := [],
                            postconditions := [] },
                  body := .structured body
                }
                md,
          bindings)

---------------------------------------------------------------------

/-- Translate a transfer command from the CFG syntax -/

private instance : Inhabited TransBindings := ⟨{}⟩
private instance : Inhabited (Imperative.DetTransferCmd String Core.Expression) := ⟨.finish .empty⟩
private instance : Inhabited (Imperative.BasicBlock (Imperative.DetTransferCmd String Core.Expression) Core.Command) := ⟨⟨[], .finish .empty⟩⟩
private instance : Inhabited (Imperative.CFG String (Imperative.DetBlock String Core.Command Core.Expression)) := ⟨⟨"", []⟩⟩

partial def translateTransfer (p : Program) (bindings : TransBindings) (arg : Arg) :
  TransM (List Core.Command × Imperative.DetTransferCmd String Core.Expression × TransBindings) := do
  let .op op := arg
    | TransM.error s!"translateTransfer expected op {repr arg}"
  let md ← getOpMetaData op
  match op.name with
  | q`Core.transfer_goto =>
    let label ← translateIdent String op.args[0]!
    return ([], .condGoto (Lambda.LExpr.boolConst () Bool.true) label label md, bindings)
  | q`Core.transfer_nondet_goto =>
    let label1 ← translateIdent String op.args[0]!
    let label2 ← translateIdent String op.args[1]!
    -- Nondeterministic choice: use a fresh boolean variable as the branch
    -- condition, declared by the `init` command below (prepended to the block in
    -- `translateCFGBlock`) so the type checker can see it. The symbolic evaluator
    -- leaves the fvar unchanged, so `evalCFGStep` forks into both paths; the
    -- concrete interpreter (runCFG) errors on it, as expected.
    let condName : Core.CoreIdent := ⟨s!"$__nondet_{bindings.gen.var_def}", ()⟩
    let bindings := incrNum .var_def bindings
    let boolMono := Lambda.LMonoTy.bool
    let boolTy : Lambda.LTy := .forAll [] boolMono
    let initCmd : Core.Command := .cmd (.init condName boolTy .nondet md)
    let condExpr := Lambda.LExpr.fvar () condName (some boolMono)
    return ([initCmd], .condGoto condExpr label1 label2 md, bindings)
  | q`Core.transfer_cond_goto =>
    let cond ← translateExpr p bindings op.args[0]!
    let lt ← translateIdent String op.args[1]!
    let lf ← translateIdent String op.args[2]!
    return ([], .condGoto cond lt lf md, bindings)
  | q`Core.transfer_return =>
    return ([], .finish md, bindings)
  | _ => TransM.error s!"translateTransfer: unknown transfer {repr op.name}"

/-- Translate a single CFG block -/
partial def translateCFGBlock (p : Program) (bindings : TransBindings) (arg : Arg) :
  TransM (String × Imperative.BasicBlock (Imperative.DetTransferCmd String Core.Expression) Core.Command × TransBindings) := do
  let .op op := arg
    | TransM.error s!"translateCFGBlock expected op {repr arg}"
  let label ← translateIdent String op.args[0]!
  -- Translate commands - handle both Seq and empty cases
  let stmts : Array Arg := match op.args[1]! with
    | .seq _ _ arr => arr
    | other => #[other]  -- single statement or empty
  let mut cmds : Array Core.Command := #[]
  let mut bindings := bindings
  for s in stmts do
    -- Skip empty/null args
    if let .op _ := s then
      let (translated, bindings') ← translateStmt p bindings s
      bindings := bindings'
      for stmt in translated do
        match stmt with
        | .cmd c => cmds := cmds.push c
        | _ => TransM.error s!"translateCFGBlock: only commands allowed in CFG blocks, got statement"
  let (transferCmds, transfer, bindings') ← translateTransfer p bindings op.args[2]!
  -- Append any commands the transfer needs declared in scope (e.g. the
  -- `$__nondet_N` declaration for a nondeterministic goto).
  return (label, ⟨cmds.toList ++ transferCmds, transfer⟩, bindings')

/-- Translate a list of CFG blocks -/
partial def translateCFGBlocks (p : Program) (bindings : TransBindings) (arg : Arg) :
  TransM (List (String × Imperative.BasicBlock (Imperative.DetTransferCmd String Core.Expression) Core.Command) × TransBindings) := do
  let .op op := arg
    | TransM.error s!"translateCFGBlocks expected op {repr arg}"
  match op.name with
  | q`Core.cfg_blocks_one =>
    let (label, blk, bindings) ← translateCFGBlock p bindings op.args[0]!
    return ([(label, blk)], bindings)
  | q`Core.cfg_blocks_cons =>
    let (label, blk, bindings) ← translateCFGBlock p bindings op.args[0]!
    let (rest, bindings) ← translateCFGBlocks p bindings op.args[1]!
    return ((label, blk) :: rest, bindings)
  | _ => TransM.error s!"translateCFGBlocks: unknown {repr op.name}"

/-- Translate a CFG body -/
partial def translateCFGBody (p : Program) (bindings : TransBindings) (arg : Arg) :
  TransM (Imperative.CFG String (Imperative.DetBlock String Core.Command Core.Expression) × TransBindings) := do
  let .op op := arg
    | TransM.error s!"translateCFGBody expected op {repr arg}"
  let entry ← translateIdent String op.args[0]!
  let (blocks, bindings) ← translateCFGBlocks p bindings op.args[1]!
  return ({ entry := entry, blocks := blocks }, bindings)

/-- Translate a procedure with CFG body -/
def translateCFGProcedure (p : Program) (bindings : TransBindings) (op : Operation) :
  TransM (Core.Decl × TransBindings) := do
  let _ ← @checkOp (Core.Decl × TransBindings) op q`Core.command_cfg_procedure 6
  let annotsArg := op.args[0]!
  let pname ← translateIdent Core.CoreIdent op.args[1]!
  let typeArgs ← translateTypeArgs op.args[2]!
  let origBindings := bindings
  let (sig, ret, bindings) ← translateProcBindings bindings op.args[3]!
  let .option _ speca := op.args[4]!
    | TransM.error s!"translateCFGProcedure spec expected: {repr op.args[4]!}"
  let (requires, ensures) ←
    if speca.isSome then translateSpec p pname bindings speca.get! else pure ([], [])
  let (cfg, bindings) ← translateCFGBody p bindings op.args[5]!
  let origBindings := { origBindings with gen := bindings.gen }
  let md ← getMetaDataWithAnn op annotsArg
  return (.proc { header := { name := pname,
                              typeArgs := typeArgs.toList,
                              inputs := sig,
                              outputs := ret },
                  spec := { preconditions := requires,
                            postconditions := ensures },
                  body := .cfg cfg
                }
                md,
          origBindings)

---------------------------------------------------------------------

def translateOptionInline (arg : Arg) : TransM (Array Strata.DL.Util.FuncAttr) := do
  let .option _ inline := arg
    | TransM.error s!"translateOptionInline unexpected {repr arg}"
  match inline with
  | some f =>
    let _ ← checkOpArg f q`Core.inline 0
    return #[.inline]
  | none => return #[]

/-- Record a constant declaration, making its name available to the declarations
that follow. -/
private def constantDecl (decl : Core.Decl) (bindings : TransBindings) :
  Core.Decl × TransBindings :=
  (decl, { bindings with freeVars := bindings.freeVars.push decl })

/--
Translate `const x : T;`, a constant whose value is left unspecified.

It elaborates to a nullary function without a body, so `x` is constrained only
by whatever axioms mention it.
-/
def translateConstantDecl (bindings : TransBindings) (op : Operation) :
  TransM (Core.Decl × TransBindings) := do
  let _ ← @checkOp (Core.Decl × TransBindings) op q`Core.command_constdecl 3
  let annotsArg := op.args[0]!
  let cname ← translateIdent Core.CoreIdent op.args[1]!
  let ret ← translateLMonoTy bindings op.args[2]!
  let md ← getMetaDataWithAnn op annotsArg
  return constantDecl (.const cname ret (md := md)) bindings

/--
Translate `const x : T := v;`, a constant declared together with its value.

It elaborates to a nullary function whose body is `v`, so the value is available
to the type checker and to symbolic evaluation without an SMT-level axiom
relating `x` to `v`. As for a function definition, the body is substituted at
each use only when the declaration is marked `inline`.

Like `const x : T;`, this form takes no type arguments: a constant is
monomorphic. Write a polymorphic nullary value with `function` syntax instead.
-/
def translateConstantDef (p : Program) (bindings : TransBindings) (op : Operation) :
  TransM (Core.Decl × TransBindings) := do
  let _ ← @checkOp (Core.Decl × TransBindings) op q`Core.command_constdef 5
  let annotsArg := op.args[0]!
  let cname ← translateIdent Core.CoreIdent op.args[1]!
  let ret ← translateLMonoTy bindings op.args[2]!
  let body ← translateExpr p bindings op.args[3]!
  let attr ← translateOptionInline op.args[4]!
  let md ← getMetaDataWithAnn op annotsArg
  return constantDecl (.const cname ret (value := some body) (attr := attr) (md := md)) bindings

---------------------------------------------------------------------

def translateAxiom (p : Program) (bindings : TransBindings) (op : Operation) :
  TransM (Core.Decl × TransBindings) := do
  let _ ← @checkOp (Core.Decl × TransBindings) op q`Core.command_axiom 3
  let annotsArg := op.args[0]!
  let (l, bindings) ← nextLabel "axiom" .axiom_def op.args[1]! bindings
  let e ← translateExpr p bindings op.args[2]!
  let md ← getMetaDataWithAnn op annotsArg
  return (.ax (Core.Axiom.mk l e) md, bindings)

def translateDistinct (p : Program) (bindings : TransBindings) (op : Operation) :
  TransM (Core.Decl × TransBindings) := do
  let _ ← @checkOp (Core.Decl × TransBindings) op q`Core.command_distinct 3
  let annotsArg := op.args[0]!
  let (l, bindings) ← nextLabel "axiom_distinct" .axiom_def op.args[1]! bindings
  let es ← translateCommaSep (translateExpr p bindings) op.args[2]!
  if !(es.all LExpr.isOp) then
    TransM.error s!"arguments to `distinct` must all be constant names: {es}"
  let md ← getMetaDataWithAnn op annotsArg
  return (.distinct l es.toList md, bindings)

---------------------------------------------------------------------

inductive FnInterp where
  | Definition
  | Declaration
  deriving Repr

def translateFunction (status : FnInterp) (p : Program) (bindings : TransBindings) (op : Operation) :
  TransM (Core.Decl × TransBindings) := do
  let _ ←
    match status with
    | .Definition           => @checkOp (Core.Decl × TransBindings) op q`Core.command_fndef     8
    | .Declaration          => @checkOp (Core.Decl × TransBindings) op q`Core.command_fndecl    5
  let annotsArg := op.args[0]!
  let fname ← translateIdent Core.CoreIdent op.args[1]!
  let typeArgs ← translateTypeArgs op.args[2]!
  let sig ← translateBindings bindings op.args[3]!
  let ret ← translateLMonoTy bindings op.args[4]!
  let in_bindings := (sig.map (fun (v, ty) => (LExpr.fvar () v ty))).toArray
  let orig_bbindings := bindings.boundVars
  let bbindings := bindings.boundVars ++ in_bindings
  let bindings := { bindings with boundVars := bbindings }
  let (preconds, body, inline?) ← match status with
    | .Definition =>
      let preconds ← translateFnPreconds p fname bindings op.args[5]!
      let e ← translateExpr p bindings op.args[6]!
      let inline? ← translateOptionInline op.args[7]!
      pure (preconds, some e, inline?)
    | .Declaration => pure ([], none, #[])
  let md ← getMetaDataWithAnn op annotsArg
  let decl := .func { name := fname,
                      typeArgs := typeArgs.toList,
                      isRecursive := false,
                      inputs := sig,
                      output := ret,
                      body := body,
                      attr := inline?,
                      preconditions := preconds } md
  return (decl,
          { bindings with
            boundVars := orig_bbindings,
            freeVars := bindings.freeVars.push decl })

---------------------------------------------------------------------
-- Mutual recursive function translation
-- Follows the same pattern as translateDatatypes:
-- 1. First pass: collect names, allocate placeholder fvars
-- 2. Second pass: translate bodies with all placeholders in scope
-- 3. Build combined recFuncBlock decl
-- 4. Set each function's fvar index to the combined decl

/--
Translate a single function within a mutual recursive block.
`fnOp` is a `recfn_decl` operation.
`preBindings` has placeholder fvars for all functions in the block.
`siblingExprs` contains the opExpr for each preceding sibling (for bvar resolution).
-/
partial def translateRecFnDecl (p : Program) (preBindings : TransBindings)
    (fnOp : Operation) (siblingExprs : Array Core.Expression.Expr) :
    TransM Core.Function := do
  let _ ← @checkOp Core.Function fnOp q`Core.recfn_decl 7
  let fname ← translateIdent Core.CoreIdent fnOp.args[0]!
  let typeArgs ← translateTypeArgs fnOp.args[1]!
  let (sig, casesIdx) ← translateBindingsWithCases preBindings fnOp.args[2]!
  let ret ← translateLMonoTy preBindings fnOp.args[3]!
  let in_bindings := (sig.map (fun (v, ty) => (LExpr.fvar () v ty))).toArray
  -- Build boundVars matching the DDM elaborator's typing context.
  -- @[declareFn] accumulates sibling bvars across NewlineSepBy children.
  -- Self-reference goes through fvar (from @[preRegisterFunctions]), not bvar.
  let tyArgPlaceholders := typeArgs.map fun (ta : TyIdentifier) =>
    LExpr.op () (ta : Core.CoreIdent) .none
  let bbindings := preBindings.boundVars ++ siblingExprs ++ tyArgPlaceholders ++ in_bindings
  let bodyBindings := { preBindings with boundVars := bbindings }
  let casesAttr := match casesIdx with
    | some i => #[Strata.DL.Util.FuncAttr.inlineIfConstr i]
    | none => #[Strata.DL.Util.FuncAttr.inlineIfAllCanonical]
  let preconds ← translateFnPreconds p fname bodyBindings fnOp.args[4]!
  let measure ← translateMeasure p bodyBindings fnOp.args[5]!
  let body ← translateExpr p bodyBindings fnOp.args[6]!
  return { name := fname, typeArgs := typeArgs.toList, isRecursive := true,
           inputs := sig, output := ret, body := some body,
           attr := casesAttr, preconditions := preconds,
           measure := measure }

/--
Translate a `command_recfndefs` block (one or more mutually recursive functions).
-/
partial def translateRecFuncBlock (p : Program) (bindings : TransBindings) (op : Operation) :
    TransM (Core.Decl × TransBindings) := do
  let _ ← @checkOp (Core.Decl × TransBindings) op q`Core.command_recfndefs 2
  let annotsArg := op.args[0]!

  let .seq _ _ declarations := op.args[1]!
    | TransM.error s!"translateRecFuncBlock expected sequence: {repr op.args[1]!}"

  let fnOps := declarations.filterMap fun arg =>
    match arg with
    | .op op => if op.name == q`Core.recfn_decl then some op else none
    | _ => none

  if fnOps.size == 0 then
    TransM.error "Recursive function block must contain at least one function"
  else
    -- First pass: allocate placeholder fvars
    let mut bindingsWithPlaceholders := bindings
    for fnOp in fnOps do
      let fname ← translateIdent Core.CoreIdent fnOp.args[0]!
      let sig ← translateBindings bindingsWithPlaceholders fnOp.args[2]!
      let ret ← translateLMonoTy bindingsWithPlaceholders fnOp.args[3]!
      let placeholder : Core.Function := {
        name := fname, typeArgs := [], inputs := sig, output := ret,
        body := none, isRecursive := true }
      let placeholderDecl := Core.Decl.recFuncBlock [placeholder] .empty
      bindingsWithPlaceholders := { bindingsWithPlaceholders with
        freeVars := bindingsWithPlaceholders.freeVars.push placeholderDecl }

    -- Second pass: translate each function body with all placeholders in scope.
    -- @[declareFn] accumulates bvars across siblings, so the i-th function's
    -- body sees the preceding i siblings as bvars.
    let (funcsRev, _) ← fnOps.foldlM (init := ([], #[])) fun (acc, siblings) fnOp => do
      let func ← translateRecFnDecl p bindingsWithPlaceholders fnOp siblings
      pure (func :: acc, siblings.push func.opExpr)
    let funcs := funcsRev.reverse

    let md ← getMetaDataWithAnn op annotsArg
    let decl := Core.Decl.recFuncBlock funcs md

    -- Replace placeholder freeVars with the real combined decl.
    let mut finalBindings := bindings
    for i in [:fnOps.size] do
      let idx := bindings.freeVars.size + i
      if idx < finalBindings.freeVars.size then
        finalBindings := { finalBindings with
          freeVars := finalBindings.freeVars.set! idx decl }
      else
        finalBindings := { finalBindings with
          freeVars := finalBindings.freeVars.push decl }

    return (decl, finalBindings)

---------------------------------------------------------------------

/--
Information about a single constructor extracted during translation.
This is the Strata Core-specific version of `ConstructorInfo` from AST.lean,
with types translated from `TypeExpr` to `LMonoTy`.
-/
structure TransConstructorInfo where
  /-- Constructor name -/
  name : Core.CoreIdent
  /-- Fields as (fieldName, fieldType) pairs with translated types -/
  fields : Array (Core.CoreIdent × LMonoTy)
  deriving Repr

/--
Translate constructor information from AST.ConstructorInfo to TransConstructorInfo.
-/
private def translateConstructorInfo (bindings : TransBindings) (info : ConstructorInfo) :
    TransM TransConstructorInfo := do
  let fields ← info.fields.mapM fun (fieldName, fieldType) => do
    let translatedType ← translateLMonoTy bindings (.type fieldType)
    return (fieldName, translatedType)
  return { name := info.name, fields := fields }

/--
Extract and translate constructor information from a constructor list argument.

**Parameters:**
- `p`: The DDM Program (provides dialect map for annotation lookup)
- `bindings`: Current translation bindings (for type variable resolution)
- `arg`: The constructor list argument from the parsed datatype command
-/
def translateConstructorList (p : Program) (bindings : TransBindings) (arg : Arg) :
    TransM (Array TransConstructorInfo) := do
  let constructorInfos ← match extractConstructorInfo p.dialects arg with
    | .ok info => pure info
    | .error e => TransM.error s!"Constructor extraction error: {e}"
  constructorInfos.mapM (translateConstructorInfo bindings)

---------------------------------------------------------------------
-- Common helpers for datatype translation

/--
Extract type arguments from a datatype's optional bindings argument.
-/
def translateDatatypeTypeArgs (bindings : TransBindings) (arg : Arg) (errorContext : String) :
    TransM (List TyIdentifier × TransBindings) :=
  translateOption
    (fun maybearg => do
      match maybearg with
      | none => pure ([], bindings)
      | some arg =>
        let bargs ← checkOpArg arg q`Core.mkBindings 1
        match bargs[0]! with
        | .seq _ .comma args =>
          let (arr, bindings) ← translateTypeBindings bindings args
          return (arr.toList, bindings)
        | _ => TransM.error s!"{errorContext} expects a comma separated list: {repr bargs[0]!}")
    arg

/--
Create a placeholder LDatatype for recursive type references.
-/
def mkPlaceholderLDatatype (name : String) (typeArgs : List TyIdentifier) : LDatatype Unit :=
  { name := name
    typeArgs := typeArgs
    constrs := [{ name := name, args := [], testerName := "" }]
    constrs_ne := by simp }

/--
Filter factory function declarations to extract constructor, tester, and field accessor decls
for a single datatype.
-/
def filterDatatypeDecls (ldatatype : LDatatype Unit) (funcDecls : List Core.Decl) :
    List Core.Decl × List Core.Decl × List Core.Decl × List Core.Decl :=
  let constructorNames := ldatatype.constrs.map fun c => c.name.name
  let testerNames := ldatatype.constrs.map fun c => c.testerName
  let fieldAccessorNames := ldatatype.constrs.foldl (fun acc c =>
    acc ++ (c.args.map fun (fieldName, _) => ldatatype.name ++ ".." ++ fieldName.name)) []
  let unsafeFieldAccessorNames := ldatatype.constrs.foldl (fun acc c =>
    acc ++ (c.args.map fun (fieldName, _) => ldatatype.name ++ ".." ++ fieldName.name ++ "!")) []

  let filterByNames (names : List String) := funcDecls.filter fun decl =>
    match decl with | .func f _ => names.contains f.name.name | _ => false

  (filterByNames constructorNames, filterByNames testerNames,
   filterByNames fieldAccessorNames, filterByNames unsafeFieldAccessorNames)

/--
Build LConstr list from TransConstructorInfo array.
-/
def buildLConstrs (datatypeName : String) (constructors : Array TransConstructorInfo) :
    List (LConstr Unit) :=
  let testerPattern : Array NamePatternPart := #[.datatype, .literal "..is", .constructor]
  constructors.toList.map fun constr =>
    let testerName := expandNamePattern testerPattern datatypeName (some constr.name.name)
    { name := constr.name
      args := constr.fields.toList.map fun (fieldName, fieldType) => (fieldName, fieldType)
      testerName := testerName }

/--
Generate factory function declarations from a list of LDatatypes.
-/
def genDatatypeFactory (ldatatypes : List (LDatatype Unit)) :
    TransM (List Core.Decl) := do
  let factory ← match genBlockFactory ldatatypes (T := Core.CoreLParams) with
    | .ok f => pure f
    | .error e => TransM.error s!"Failed to generate datatype factory: {e}"
  -- These decls exist for name resolution only; evaluation re-derives the
  -- factory (with concreteEval) from the `.data` decl via genBlockFactory,
  -- so projecting concreteEval away here loses nothing.
  return factory.toArray.toList.map fun func => Core.Decl.func func.toFunc .empty

---------------------------------------------------------------------

/--
Translate a datatype block (one or more datatype declarations).
The `@[preRegisterTypes]` metadata on `command_datatypes` ensures that
type names are pre-registered in the DDM GlobalContext before processing.
-/
def translateDatatypes (p : Program) (bindings : TransBindings) (op : Operation) :
    TransM (Core.Decl × TransBindings) := do
  let _ ← @checkOp (Core.Decls × TransBindings) op q`Core.command_datatypes 2
  let annotsArg := op.args[0]!

  let .seq _ _ declarations := op.args[1]!
    | TransM.error s!"translateDatatypes expected sequence: {repr op.args[1]!}"

  let datatypeOps := declarations.filterMap fun arg =>
    match arg with
    | .op op => if op.name == q`Core.datatype_decl then some op else none
    | _ => none

  if datatypeOps.size == 0 then
    TransM.error "Datatype block must contain at least one datatype"
  else
    -- First pass: collect all datatype names and type args, allocate placeholders
    let mut datatypeInfos : Array (String × List TyIdentifier × Nat) := #[]
    let mut bindingsWithPlaceholders := bindings

    for dtOp in datatypeOps do
      let datatypeName ← translateIdent String dtOp.args[0]!
      let (typeArgs, _) ← translateDatatypeTypeArgs bindings dtOp.args[1]! "translateDatatypes"

      let existingIdx := bindings.freeVars.findIdx? fun decl =>
        match decl with
        | .type t _ => t.names.contains datatypeName
        | _ => false

      let placeholderDecl := Core.Decl.type (.data [mkPlaceholderLDatatype datatypeName typeArgs]) .empty
      match existingIdx with
      | some i =>
        datatypeInfos := datatypeInfos.push (datatypeName, typeArgs, i)
        bindingsWithPlaceholders := { bindingsWithPlaceholders with
          freeVars := bindingsWithPlaceholders.freeVars.set! i placeholderDecl }
      | none =>
        let idx := bindingsWithPlaceholders.freeVars.size
        datatypeInfos := datatypeInfos.push (datatypeName, typeArgs, idx)
        bindingsWithPlaceholders := { bindingsWithPlaceholders with
          freeVars := bindingsWithPlaceholders.freeVars.push placeholderDecl }

    -- Second pass: translate all constructors with all placeholders in scope
    let ldatatypes ← (datatypeOps.zip datatypeInfos).toList.mapM fun (dtOp, (datatypeName, typeArgs, _idx)) => do
      -- Re-translate type args to populate boundTypeVars for this datatype.
      -- The first pass already translated them but only to collect names/args;
      -- we need per-datatype bindings here so constructors resolve type vars correctly.
      let (_, dtBindings) ← translateDatatypeTypeArgs bindingsWithPlaceholders dtOp.args[1]! "translateDatatypes"
      let constructors ← translateConstructorList p dtBindings dtOp.args[2]!
      if h : constructors.size == 0 then
        TransM.error s!"Datatype {datatypeName} must have at least one constructor"
      else
        let lConstrs := buildLConstrs datatypeName constructors
        have constrs_ne : lConstrs.length != 0 := by
          simp [lConstrs, buildLConstrs]
          intro heq; subst_vars; apply h; rfl
        pure { name := datatypeName, typeArgs := typeArgs, constrs := lConstrs, constrs_ne := constrs_ne }

    let allFuncDecls ← genDatatypeFactory ldatatypes

    let md ← getMetaDataWithAnn op annotsArg
    let typeDecl := Core.Decl.type (.data ldatatypes) md

    let mut finalBindings := bindings

    for (_datatypeName, _typeArgs, idx) in datatypeInfos do
      if idx < finalBindings.freeVars.size then
        finalBindings := { finalBindings with
          freeVars := finalBindings.freeVars.set! idx typeDecl }
      else
        finalBindings := { finalBindings with
          freeVars := finalBindings.freeVars.push typeDecl }

    for ldatatype in ldatatypes do
      let (constructorDecls, testerDecls, fieldAccessorDecls, unsafeFieldAccessorDecls) := filterDatatypeDecls ldatatype allFuncDecls
      for d in constructorDecls ++ testerDecls ++ fieldAccessorDecls ++ unsafeFieldAccessorDecls do
        finalBindings := { finalBindings with freeVars := finalBindings.freeVars.push d }

    return (typeDecl, finalBindings)

---------------------------------------------------------------------

partial def translateCoreDecls (p : Program) (bindings : TransBindings) :
  TransM Core.Decls := do
  let mut acc : Array Core.Decl := #[]
  let mut bindings := bindings
  for i in [:p.commands.size] do
    let op := p.commands[i]!
    let (decl, bindings') ←
      match op.name with
      | q`Core.command_datatypes =>
        translateDatatypes p bindings op
      | q`Core.command_constdecl =>
        translateConstantDecl bindings op
      | q`Core.command_constdef =>
        translateConstantDef p bindings op
      | q`Core.command_typedecl =>
        translateTypeDecl bindings op
      | q`Core.command_typesynonym =>
        translateTypeSynonym bindings op
      | q`Core.command_axiom =>
        translateAxiom p bindings op
      | q`Core.command_distinct =>
        translateDistinct p bindings op
      | q`Core.command_procedure =>
        translateProcedure p bindings op
      | q`Core.command_fndef =>
        translateFunction .Definition p bindings op
      | q`Core.command_fndecl =>
        translateFunction .Declaration p bindings op
      | q`Core.command_recfndefs =>
        translateRecFuncBlock p bindings op
      | q`Core.command_block =>
        translateBlockCommand p bindings op
      | q`Core.command_cfg_procedure =>
        translateCFGProcedure p bindings op
      | _ => TransM.error s!"translateCoreDecls unimplemented for {repr op}"
    acc := acc.push decl
    bindings := bindings'
  return acc.toList

def translateProgram (p : Program) : TransM Core.Program := do
  fun s => ((), { s with globalContext := p.globalContext })
  let decls ← translateCoreDecls p {}
  return { decls := decls }

---------------------------------------------------------------------

end -- public section

end Strata
