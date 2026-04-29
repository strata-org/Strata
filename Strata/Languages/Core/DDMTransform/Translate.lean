/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Env


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

---------------------------------------------------------------------

/- Metadata -/

def SourceRange.toMetaData (ictx : InputContext) (sr : SourceRange) : Imperative.MetaData Core.Expression :=
  let file := ictx.fileName
  let uri: Uri := .file file
  let fileRangeElt := ⟨ MetaData.fileRange, .fileRange ⟨ uri, sr ⟩ ⟩
  #[fileRangeElt]

def getOpMetaData (op : Operation) : TransM (Imperative.MetaData Core.Expression) :=
  return op.ann.toMetaData (← StateT.get).inputCtx

def getArgMetaData (arg : Arg) : TransM (Imperative.MetaData Core.Expression) :=
  return arg.ann.toMetaData (← StateT.get).inputCtx

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

def translateCommaSep [Inhabited α] (f : Strata.Arg → TransM α) (arg : Strata.Arg) :
  TransM (Array α) := do
  let .seq _ .comma args := arg
    | TransM.error s!"Expected commaSepList: {repr arg}"
  args.mapM f

def translateOption [Inhabited α] (f : Option Strata.Arg → TransM α) (arg : Arg) :
  TransM α := do
  let .option _ maybe_arg := arg
    | TransM.error s!"Expected Option: {repr arg}"
  f maybe_arg

---------------------------------------------------------------------

def translateIdent (Identifier : Type) [Coe String Identifier] [Inhabited Identifier]
  (arg : Strata.Arg) : TransM Identifier := do
  let .ident _ name := arg
    | TransM.error s!"Expected ident: {repr arg}"
  pure name

def translateOptionLabel (default : String) (arg : Arg) : TransM String := do
  translateOption (fun maybe_arg => do
                    match maybe_arg with
                    | none => return default
                    | some lop => let args ← checkOpArg lop q`Core.label 1
                                  translateIdent String args[0]!)
                  arg

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

structure TransBindings where
  boundTypeVars : Array TyIdentifier := #[]
  boundVars : Array (LExpr Core.CoreLParams.mono) := #[]
  freeVars  : Array Core.Decl := #[]
  gen : GenNum := (GenNum.mk 0 0 0 0 0)

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
  | .ident _ q`Core.bv1 #[] => pure <| .bitvec 1
  | .ident _ q`Core.bv8 #[] => pure <| .bitvec 8
  | .ident _ q`Core.bv16 #[] => pure <| .bitvec 16
  | .ident _ q`Core.bv32 #[] => pure <| .bitvec 32
  | .ident _ q`Core.bv64 #[] => pure <| .bitvec 64
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

def translateTypeVar (op : Strata.Arg) : TransM TyIdentifier := do
  let args ← checkOpArg op q`Core.type_var 1
  translateIdent TyIdentifier args[0]!

def translateTypeArgs (op : Strata.Arg) : TransM (Array TyIdentifier) := do
  translateOption (fun x => do match x with
                  | none => return Array.empty
                  | some a =>
                    let args ← checkOpArg a q`Core.type_args 1
                    translateCommaSep translateTypeVar args[0]!)
                  op

def translateTypeSynonym (bindings : TransBindings) (op : Operation) :
  TransM (Core.Decl × TransBindings) := do
  let _ ← @checkOp (Core.Decl × TransBindings) op q`Core.command_typesynonym 4
  let name ← translateIdent TyIdentifier op.args[0]!
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
                    op.args[1]!
  let typedef ← translateLMonoTy bindings op.args[3]!
  let md ← getOpMetaData op
  let decl := Core.Decl.type (.syn { name := name, typeArgs := targs, type := typedef }) md
  return (decl, { bindings with freeVars := bindings.freeVars.push decl })


def translateTypeDecl (bindings : TransBindings) (op : Operation) :
  TransM (Core.Decl × TransBindings) := do
  let _ ← @checkOp (Core.Decl × TransBindings) op q`Core.command_typedecl 2
  let name ← translateIdent TyIdentifier op.args[0]!
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
                    op.args[1]!
  let md ← getOpMetaData op
  let decl := Core.Decl.type (.con { name := name, params := params }) md
  return (decl, { bindings with freeVars := bindings.freeVars.push decl })

---------------------------------------------------------------------

def translateLhs (arg : Arg) : TransM Core.CoreIdent := do
  let .op op := arg
    | TransM.error s!"translateLhs expected op {repr arg}"
  match op.name, op.args with
  | q`Core.lhsIdent, #[id] => translateIdent Core.CoreIdent id
  -- (TODO) Implement lhsArray.
  | _, _ => TransM.error s!"translateLhs: unimplemented for {repr arg}"

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
    | .expr te => te
    | .type [] (.some te) => te
    | _ => te
  | _ => te

def dealiasTypeArg (p : Program) (a : Arg) : Arg :=
  match a with
  | .type te => .type (dealiasTypeExpr p te)
  | _ => a

def isArithTy : LMonoTy → Bool
| .int => true
| .real => true
| .bitvec _ => true
| _ => false

def translateFn (ty? : Option LMonoTy) (q : QualifiedIdent) : TransM Core.Expression.Expr :=
  match ty?, q with
  | _, q`Core.equiv    => return Core.boolEquivOp
  | _, q`Core.implies  => return Core.boolImpliesOp
  | _, q`Core.and      => return Core.boolAndOp
  | _, q`Core.or       => return Core.boolOrOp
  | _, q`Core.not      => return Core.boolNotOp

  | .some .int, q`Core.le       => return Core.intLeOp
  | .some .int, q`Core.lt       => return Core.intLtOp
  | .some .int, q`Core.ge       => return Core.intGeOp
  | .some .int, q`Core.gt       => return Core.intGtOp
  | .some .int, q`Core.add_expr => return Core.intAddOp
  | .some .int, q`Core.sub_expr => return Core.intSubOp
  | .some .int, q`Core.mul_expr => return Core.intMulOp
  | .some .int, q`Core.div_expr => return Core.intDivOp
  | .some .int, q`Core.mod_expr => return Core.intModOp
  | .some .int, q`Core.safediv_expr => return Core.intSafeDivOp
  | .some .int, q`Core.safemod_expr => return Core.intSafeModOp
  | .some .int, q`Core.divt_expr => return Core.intDivTOp
  | .some .int, q`Core.modt_expr => return Core.intModTOp
  | .some .int, q`Core.safedivt_expr => return Core.intSafeDivTOp
  | .some .int, q`Core.safemodt_expr => return Core.intSafeModTOp
  | .some .int, q`Core.neg_expr => return Core.intNegOp

  | .some .real, q`Core.le       => return Core.realLeOp
  | .some .real, q`Core.lt       => return Core.realLtOp
  | .some .real, q`Core.ge       => return Core.realGeOp
  | .some .real, q`Core.gt       => return Core.realGtOp
  | .some .real, q`Core.add_expr => return Core.realAddOp
  | .some .real, q`Core.sub_expr => return Core.realSubOp
  | .some .real, q`Core.mul_expr => return Core.realMulOp
  | .some .real, q`Core.div_expr => return Core.realDivOp
  | .some .real, q`Core.neg_expr => return Core.realNegOp

  | .some .bv1, q`Core.le       => return Core.bv1ULeOp
  | .some .bv1, q`Core.lt       => return Core.bv1ULtOp
  | .some .bv1, q`Core.ge       => return Core.bv1UGeOp
  | .some .bv1, q`Core.gt       => return Core.bv1UGtOp
  | .some .bv1, q`Core.bvsle    => return Core.bv1SLeOp
  | .some .bv1, q`Core.bvslt    => return Core.bv1SLtOp
  | .some .bv1, q`Core.bvsge    => return Core.bv1SGeOp
  | .some .bv1, q`Core.bvsgt    => return Core.bv1SGtOp
  | .some .bv1, q`Core.neg_expr => return Core.bv1NegOp
  | .some .bv1, q`Core.add_expr => return Core.bv1AddOp
  | .some .bv1, q`Core.sub_expr => return Core.bv1SubOp
  | .some .bv1, q`Core.mul_expr => return Core.bv1MulOp
  | .some .bv1, q`Core.div_expr => return Core.bv1UDivOp
  | .some .bv1, q`Core.mod_expr => return Core.bv1UModOp
  | .some .bv1, q`Core.bvsdiv   => return Core.bv1SDivOp
  | .some .bv1, q`Core.bvsmod   => return Core.bv1SModOp
  | .some .bv1, q`Core.safeadd_expr  => return Core.bv1SafeAddOp
  | .some .bv1, q`Core.safesub_expr  => return Core.bv1SafeSubOp
  | .some .bv1, q`Core.safemul_expr  => return Core.bv1SafeMulOp
  | .some .bv1, q`Core.safeneg_expr  => return Core.bv1SafeNegOp
  | .some .bv1, q`Core.safesdiv_expr => return Core.bv1SafeSDivOp
  | .some .bv1, q`Core.safesmod_expr => return Core.bv1SafeSModOp
  | .some .bv1, q`Core.bvnot    => return Core.bv1NotOp
  | .some .bv1, q`Core.bvand    => return Core.bv1AndOp
  | .some .bv1, q`Core.bvor     => return Core.bv1OrOp
  | .some .bv1, q`Core.bvxor    => return Core.bv1XorOp
  | .some .bv1, q`Core.bvshl    => return Core.bv1ShlOp
  | .some .bv1, q`Core.bvushr   => return Core.bv1UShrOp
  | .some .bv1, q`Core.bvsshr   => return Core.bv1SShrOp

  | .some .bv8, q`Core.le       => return Core.bv8ULeOp
  | .some .bv8, q`Core.lt       => return Core.bv8ULtOp
  | .some .bv8, q`Core.ge       => return Core.bv8UGeOp
  | .some .bv8, q`Core.gt       => return Core.bv8UGtOp
  | .some .bv8, q`Core.bvsle    => return Core.bv8SLeOp
  | .some .bv8, q`Core.bvslt    => return Core.bv8SLtOp
  | .some .bv8, q`Core.bvsge    => return Core.bv8SGeOp
  | .some .bv8, q`Core.bvsgt    => return Core.bv8SGtOp
  | .some .bv8, q`Core.neg_expr => return Core.bv8NegOp
  | .some .bv8, q`Core.add_expr => return Core.bv8AddOp
  | .some .bv8, q`Core.sub_expr => return Core.bv8SubOp
  | .some .bv8, q`Core.mul_expr => return Core.bv8MulOp
  | .some .bv8, q`Core.div_expr => return Core.bv8UDivOp
  | .some .bv8, q`Core.mod_expr => return Core.bv8UModOp
  | .some .bv8, q`Core.bvsdiv   => return Core.bv8SDivOp
  | .some .bv8, q`Core.bvsmod   => return Core.bv8SModOp
  | .some .bv8, q`Core.safeadd_expr  => return Core.bv8SafeAddOp
  | .some .bv8, q`Core.safesub_expr  => return Core.bv8SafeSubOp
  | .some .bv8, q`Core.safemul_expr  => return Core.bv8SafeMulOp
  | .some .bv8, q`Core.safeneg_expr  => return Core.bv8SafeNegOp
  | .some .bv8, q`Core.safesdiv_expr => return Core.bv8SafeSDivOp
  | .some .bv8, q`Core.safesmod_expr => return Core.bv8SafeSModOp
  | .some .bv8, q`Core.bvnot    => return Core.bv8NotOp
  | .some .bv8, q`Core.bvand    => return Core.bv8AndOp
  | .some .bv8, q`Core.bvor     => return Core.bv8OrOp
  | .some .bv8, q`Core.bvxor    => return Core.bv8XorOp
  | .some .bv8, q`Core.bvshl    => return Core.bv8ShlOp
  | .some .bv8, q`Core.bvushr   => return Core.bv8UShrOp
  | .some .bv8, q`Core.bvsshr   => return Core.bv8SShrOp

  | .some .bv16, q`Core.le       => return Core.bv16ULeOp
  | .some .bv16, q`Core.lt       => return Core.bv16ULtOp
  | .some .bv16, q`Core.ge       => return Core.bv16UGeOp
  | .some .bv16, q`Core.gt       => return Core.bv16UGtOp
  | .some .bv16, q`Core.bvsle    => return Core.bv16SLeOp
  | .some .bv16, q`Core.bvslt    => return Core.bv16SLtOp
  | .some .bv16, q`Core.bvsge    => return Core.bv16SGeOp
  | .some .bv16, q`Core.bvsgt    => return Core.bv16SGtOp
  | .some .bv16, q`Core.neg_expr => return Core.bv16NegOp
  | .some .bv16, q`Core.add_expr => return Core.bv16AddOp
  | .some .bv16, q`Core.sub_expr => return Core.bv16SubOp
  | .some .bv16, q`Core.mul_expr => return Core.bv16MulOp
  | .some .bv16, q`Core.div_expr => return Core.bv16UDivOp
  | .some .bv16, q`Core.mod_expr => return Core.bv16UModOp
  | .some .bv16, q`Core.bvsdiv   => return Core.bv16SDivOp
  | .some .bv16, q`Core.bvsmod   => return Core.bv16SModOp
  | .some .bv16, q`Core.safeadd_expr  => return Core.bv16SafeAddOp
  | .some .bv16, q`Core.safesub_expr  => return Core.bv16SafeSubOp
  | .some .bv16, q`Core.safemul_expr  => return Core.bv16SafeMulOp
  | .some .bv16, q`Core.safeneg_expr  => return Core.bv16SafeNegOp
  | .some .bv16, q`Core.safesdiv_expr => return Core.bv16SafeSDivOp
  | .some .bv16, q`Core.safesmod_expr => return Core.bv16SafeSModOp
  | .some .bv16, q`Core.bvnot    => return Core.bv16NotOp
  | .some .bv16, q`Core.bvand    => return Core.bv16AndOp
  | .some .bv16, q`Core.bvor     => return Core.bv16OrOp
  | .some .bv16, q`Core.bvxor    => return Core.bv16XorOp
  | .some .bv16, q`Core.bvshl    => return Core.bv16ShlOp
  | .some .bv16, q`Core.bvushr   => return Core.bv16UShrOp
  | .some .bv16, q`Core.bvsshr   => return Core.bv16SShrOp

  | .some .bv32, q`Core.le       => return Core.bv32ULeOp
  | .some .bv32, q`Core.lt       => return Core.bv32ULtOp
  | .some .bv32, q`Core.ge       => return Core.bv32UGeOp
  | .some .bv32, q`Core.gt       => return Core.bv32UGtOp
  | .some .bv32, q`Core.bvsle    => return Core.bv32SLeOp
  | .some .bv32, q`Core.bvslt    => return Core.bv32SLtOp
  | .some .bv32, q`Core.bvsge    => return Core.bv32SGeOp
  | .some .bv32, q`Core.bvsgt    => return Core.bv32SGtOp
  | .some .bv32, q`Core.neg_expr => return Core.bv32NegOp
  | .some .bv32, q`Core.add_expr => return Core.bv32AddOp
  | .some .bv32, q`Core.sub_expr => return Core.bv32SubOp
  | .some .bv32, q`Core.mul_expr => return Core.bv32MulOp
  | .some .bv32, q`Core.div_expr => return Core.bv32UDivOp
  | .some .bv32, q`Core.mod_expr => return Core.bv32UModOp
  | .some .bv32, q`Core.bvsdiv   => return Core.bv32SDivOp
  | .some .bv32, q`Core.bvsmod   => return Core.bv32SModOp
  | .some .bv32, q`Core.safeadd_expr  => return Core.bv32SafeAddOp
  | .some .bv32, q`Core.safesub_expr  => return Core.bv32SafeSubOp
  | .some .bv32, q`Core.safemul_expr  => return Core.bv32SafeMulOp
  | .some .bv32, q`Core.safeneg_expr  => return Core.bv32SafeNegOp
  | .some .bv32, q`Core.safesdiv_expr => return Core.bv32SafeSDivOp
  | .some .bv32, q`Core.safesmod_expr => return Core.bv32SafeSModOp
  | .some .bv32, q`Core.bvnot    => return Core.bv32NotOp
  | .some .bv32, q`Core.bvand    => return Core.bv32AndOp
  | .some .bv32, q`Core.bvor     => return Core.bv32OrOp
  | .some .bv32, q`Core.bvxor    => return Core.bv32XorOp
  | .some .bv32, q`Core.bvshl    => return Core.bv32ShlOp
  | .some .bv32, q`Core.bvushr   => return Core.bv32UShrOp
  | .some .bv32, q`Core.bvsshr   => return Core.bv32SShrOp

  | .some .bv64, q`Core.le       => return Core.bv64ULeOp
  | .some .bv64, q`Core.lt       => return Core.bv64ULtOp
  | .some .bv64, q`Core.ge       => return Core.bv64UGeOp
  | .some .bv64, q`Core.gt       => return Core.bv64UGtOp
  | .some .bv64, q`Core.bvsle    => return Core.bv64SLeOp
  | .some .bv64, q`Core.bvslt    => return Core.bv64SLtOp
  | .some .bv64, q`Core.bvsge    => return Core.bv64SGeOp
  | .some .bv64, q`Core.bvsgt    => return Core.bv64SGtOp
  | .some .bv64, q`Core.neg_expr => return Core.bv64NegOp
  | .some .bv64, q`Core.add_expr => return Core.bv64AddOp
  | .some .bv64, q`Core.sub_expr => return Core.bv64SubOp
  | .some .bv64, q`Core.mul_expr => return Core.bv64MulOp
  | .some .bv64, q`Core.div_expr => return Core.bv64UDivOp
  | .some .bv64, q`Core.mod_expr => return Core.bv64UModOp
  | .some .bv64, q`Core.bvsdiv   => return Core.bv64SDivOp
  | .some .bv64, q`Core.bvsmod   => return Core.bv64SModOp
  | .some .bv64, q`Core.safeadd_expr  => return Core.bv64SafeAddOp
  | .some .bv64, q`Core.safesub_expr  => return Core.bv64SafeSubOp
  | .some .bv64, q`Core.safemul_expr  => return Core.bv64SafeMulOp
  | .some .bv64, q`Core.safeneg_expr  => return Core.bv64SafeNegOp
  | .some .bv64, q`Core.safesdiv_expr => return Core.bv64SafeSDivOp
  | .some .bv64, q`Core.safesmod_expr => return Core.bv64SafeSModOp
  | .some .bv64, q`Core.bvnot    => return Core.bv64NotOp
  | .some .bv64, q`Core.bvand    => return Core.bv64AndOp
  | .some .bv64, q`Core.bvor     => return Core.bv64OrOp
  | .some .bv64, q`Core.bvxor    => return Core.bv64XorOp
  | .some .bv64, q`Core.bvshl    => return Core.bv64ShlOp
  | .some .bv64, q`Core.bvushr   => return Core.bv64UShrOp
  | .some .bv64, q`Core.bvsshr   => return Core.bv64SShrOp

  | _, q`Core.bvconcat8 => return Core.bv8ConcatOp
  | _, q`Core.bvconcat16 => return Core.bv16ConcatOp
  | _, q`Core.bvconcat32 => return Core.bv32ConcatOp
  | _, q`Core.bvextract_7_7     => return Core.bv8Extract_7_7_Op
  | _, q`Core.bvextract_15_15   => return Core.bv16Extract_15_15_Op
  | _, q`Core.bvextract_31_31   => return Core.bv32Extract_31_31_Op
  | _, q`Core.bvextract_7_0_16  => return Core.bv16Extract_7_0_Op
  | _, q`Core.bvextract_7_0_32  => return Core.bv32Extract_7_0_Op
  | _, q`Core.bvextract_15_0_32 => return Core.bv32Extract_15_0_Op
  | _, q`Core.bvextract_7_0_64  => return Core.bv64Extract_7_0_Op
  | _, q`Core.bvextract_15_0_64 => return Core.bv64Extract_15_0_Op
  | _, q`Core.bvextract_31_0_64 => return Core.bv64Extract_31_0_Op

  | _, q`Core.str_len      => return Core.strLengthOp
  | _, q`Core.str_concat   => return Core.strConcatOp
  | _, q`Core.str_substr   => return Core.strSubstrOp
  | _, q`Core.str_toregex  => return Core.strToRegexOp
  | _, q`Core.str_inregex  => return Core.strInRegexOp
  | _, q`Core.re_all       => return Core.reAllOp
  | _, q`Core.re_allchar   => return Core.reAllCharOp
  | _, q`Core.re_range     => return Core.reRangeOp
  | _, q`Core.re_concat    => return Core.reConcatOp
  | _, q`Core.re_star      => return Core.reStarOp
  | _, q`Core.re_plus      => return Core.rePlusOp
  | _, q`Core.re_loop      => return Core.reLoopOp
  | _, q`Core.re_union     => return Core.reUnionOp
  | _, q`Core.re_inter     => return Core.reInterOp
  | _, q`Core.re_comp      => return Core.reCompOp
  | _, q`Core.re_none      => return Core.reNoneOp
  | _, _ => TransM.error s!"translateFn: Unknown/unimplemented function {repr q} at type {repr ty?}"

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
  | .fn _ q`Core.strLit, [xa] =>
    let x ← translateStr xa
    return .strConst () x
  | .fn _ q`Core.realLit, [xa] =>
    let x ← translateReal xa
    return .realConst () (Strata.Decimal.toRat x)
  -- Equality
  | .fn _ q`Core.equal, [_tpa, xa, ya] =>
    let x ← translateExpr p bindings xa
    let y ← translateExpr p bindings ya
    return .eq () x y
  | .fn _ q`Core.not_equal, [_tpa, xa, ya] =>
    let x ← translateExpr p bindings xa
    let y ← translateExpr p bindings ya
    return (.app () Core.boolNotOp (.eq () x y))
  | .fn _ q`Core.bvnot, [tpa, xa] =>
    let tp ← translateLMonoTy bindings (dealiasTypeArg p tpa)
    let x ← translateExpr p bindings xa
    let fn : LExpr Core.CoreLParams.mono ←
      translateFn (.some tp) q`Core.bvnot
    return (.app () fn x)
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
  | .fn _ q`Core.neg_expr, [tpa, xa] =>
    let ty ← translateLMonoTy bindings (dealiasTypeArg p tpa)
    let fn ← translateFn ty q`Core.neg_expr
    let x ← translateExpr p bindings xa
    return .mkApp () fn [x]
  | .fn _ q`Core.safeneg_expr, [tpa, xa] =>
    let ty ← translateLMonoTy bindings (dealiasTypeArg p tpa)
    let fn ← translateFn ty q`Core.safeneg_expr
    let x ← translateExpr p bindings xa
    return .mkApp () fn [x]
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
  | .fn _ q`Core.old, [_tp, xa] =>
     let x ← translateExpr p bindings xa
     match x with
     | .fvar m ident ty => return .fvar m (Core.CoreIdent.mkOld ident.name) ty
     | _ => TransM.error s!"old: expected an identifier, got {x}"
  | .fn _ q`Core.map_get, [_ktp, _vtp, ma, ia] =>
     let kty ← translateLMonoTy bindings _ktp
     let vty ← translateLMonoTy bindings _vtp
     -- TODO: use Core.mapSelectOp, but specialized
     let fn : LExpr Core.CoreLParams.mono := (Core.coreOpExpr (.map .Select) (.some (LMonoTy.mkArrow (Core.mapTy kty vty) [kty, vty])))
     let m ← translateExpr p bindings ma
     let i ← translateExpr p bindings ia
     return .mkApp () fn [m, i]
  | .fn _ q`Core.map_set, [_ktp, _vtp, ma, ia, xa] =>
     let kty ← translateLMonoTy bindings _ktp
     let vty ← translateLMonoTy bindings _vtp
     -- TODO: use Core.mapUpdateOp, but specialized
     let fn : LExpr Core.CoreLParams.mono := (Core.coreOpExpr (.map .Update) (.some (LMonoTy.mkArrow (Core.mapTy kty vty) [kty, vty, Core.mapTy kty vty])))
     let m ← translateExpr p bindings ma
     let i ← translateExpr p bindings ia
     let x ← translateExpr p bindings xa
     return .mkApp () fn [m, i, x]
  -- Seq operations
  -- TODO: seq_empty is not yet parseable (see Grammar.lean); handle here when added.
  | .fn _ q`Core.seq_length, [_atp, sa] =>
     let ety ← translateLMonoTy bindings _atp
     let fn : LExpr Core.CoreLParams.mono :=
       Core.coreOpExpr (.seq .Length)
         (.some (LMonoTy.mkArrow (Core.seqTy ety) [.int]))
     let s ← translateExpr p bindings sa
     return .mkApp () fn [s]
  | .fn _ q`Core.seq_select, [_atp, sa, ia] =>
     let ety ← translateLMonoTy bindings _atp
     let fn : LExpr Core.CoreLParams.mono :=
       Core.coreOpExpr (.seq .Select)
         (.some (LMonoTy.mkArrow (Core.seqTy ety) [.int, ety]))
     let s ← translateExpr p bindings sa
     let i ← translateExpr p bindings ia
     return .mkApp () fn [s, i]
  | .fn _ q`Core.seq_append, [_atp, s1a, s2a] =>
     let ety ← translateLMonoTy bindings _atp
     let fn : LExpr Core.CoreLParams.mono :=
       Core.coreOpExpr (.seq .Append)
         (.some (LMonoTy.mkArrow (Core.seqTy ety)
           [Core.seqTy ety, Core.seqTy ety]))
     let s1 ← translateExpr p bindings s1a
     let s2 ← translateExpr p bindings s2a
     return .mkApp () fn [s1, s2]
  | .fn _ q`Core.seq_build, [_atp, sa, va] =>
     let ety ← translateLMonoTy bindings _atp
     let fn : LExpr Core.CoreLParams.mono :=
       Core.coreOpExpr (.seq .Build)
         (.some (LMonoTy.mkArrow (Core.seqTy ety) [ety, Core.seqTy ety]))
     let s ← translateExpr p bindings sa
     let v ← translateExpr p bindings va
     return .mkApp () fn [s, v]
  | .fn _ q`Core.seq_update, [_atp, sa, ia, va] =>
     let ety ← translateLMonoTy bindings _atp
     let fn : LExpr Core.CoreLParams.mono :=
       Core.coreOpExpr (.seq .Update)
         (.some (LMonoTy.mkArrow (Core.seqTy ety)
           [.int, ety, Core.seqTy ety]))
     let s ← translateExpr p bindings sa
     let i ← translateExpr p bindings ia
     let v ← translateExpr p bindings va
     return .mkApp () fn [s, i, v]
  | .fn _ q`Core.seq_contains, [_atp, sa, va] =>
     let ety ← translateLMonoTy bindings _atp
     let fn : LExpr Core.CoreLParams.mono :=
       Core.coreOpExpr (.seq .Contains)
         (.some (LMonoTy.mkArrow (Core.seqTy ety) [ety, .bool]))
     let s ← translateExpr p bindings sa
     let v ← translateExpr p bindings va
     return .mkApp () fn [s, v]
  | .fn _ q`Core.seq_take, [_atp, sa, na] =>
     let ety ← translateLMonoTy bindings _atp
     let fn : LExpr Core.CoreLParams.mono :=
       Core.coreOpExpr (.seq .Take)
         (.some (LMonoTy.mkArrow (Core.seqTy ety)
           [.int, Core.seqTy ety]))
     let s ← translateExpr p bindings sa
     let n ← translateExpr p bindings na
     return .mkApp () fn [s, n]
  | .fn _ q`Core.seq_drop, [_atp, sa, na] =>
     let ety ← translateLMonoTy bindings _atp
     let fn : LExpr Core.CoreLParams.mono :=
       Core.coreOpExpr (.seq .Drop)
         (.some (LMonoTy.mkArrow (Core.seqTy ety)
           [.int, Core.seqTy ety]))
     let s ← translateExpr p bindings sa
     let n ← translateExpr p bindings na
     return .mkApp () fn [s, n]
  -- Lambda abstraction
  | .fn _ q`Core.lambda, [_, xsa, ba] =>
    translateLambda p bindings xsa ba
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
  -- Binary function applications (polymorphic)
  | .fn _ fni, [tpa, xa, ya] =>
    match fni with
    | q`Core.add_expr
    | q`Core.sub_expr
    | q`Core.mul_expr
    | q`Core.div_expr
    | q`Core.safediv_expr
    | q`Core.mod_expr
    | q`Core.safemod_expr
    | q`Core.divt_expr
    | q`Core.modt_expr
    | q`Core.safedivt_expr
    | q`Core.safemodt_expr
    | q`Core.bvand
    | q`Core.bvor
    | q`Core.bvxor
    | q`Core.bvshl
    | q`Core.bvushr
    | q`Core.bvsshr
    | q`Core.bvsdiv
    | q`Core.bvsmod
    | q`Core.safeadd_expr
    | q`Core.safesub_expr
    | q`Core.safemul_expr
    | q`Core.safesdiv_expr
    | q`Core.safesmod_expr
    | q`Core.le
    | q`Core.lt
    | q`Core.gt
    | q`Core.ge
    | q`Core.bvsle
    | q`Core.bvslt
    | q`Core.bvsgt
    | q`Core.bvsge =>
      let ty ← translateLMonoTy bindings (dealiasTypeArg p tpa)
      if ¬ isArithTy ty then
        TransM.error s!"translateExpr unexpected type for {repr fni}: {repr args}"
      else
        let fn ← translateFn (.some ty) fni
        let x ← translateExpr p bindings xa
        let y ← translateExpr p bindings ya
        return .mkApp () fn [x, y]
    | _ => TransM.error s!"translateExpr unimplemented {repr op} {repr args}"
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

def translateInvariant (p : Program) (bindings : TransBindings) (arg : Arg) : TransM (List Core.Expression.Expr) := do
  match arg with
  | .option _ (.some m) => do
    let args ← checkOpArg m q`Core.invariant 1
    let e ← translateExpr p bindings args[0]!
    pure [e]
  | _ => pure []

partial def translateInvariants (p : Strata.Program) (bindings : TransBindings) (arg : Arg) :
  TransM (List Core.Expression.Expr) := do
  let .op op := arg
    | TransM.error s!"translateInvariants expects an op {repr arg}"
  match op.name with
  | q`Core.nilInvariants =>
    pure []
  | q`Core.consInvariants =>
    let args ← checkOpArg arg q`Core.consInvariants 2
    let i ← translateExpr p bindings args[0]!
    let is ← translateInvariants p bindings args[1]!
    pure (i::is)
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

def translateVarStatement (bindings : TransBindings) (decls : Array Arg)
    (md : MetaData Core.Expression):
  TransM ((List Core.Statement) × TransBindings) := do
  if decls.size != 1 then
    TransM.error s!"translateVarStatement unexpected decls length {repr decls}"
  else
    let tpids ← translateDeclList bindings decls[0]!
    let (stmts, bindings) ← initVarStmts tpids bindings md
    let newVars ← tpids.mapM (fun (id, ty) =>
                    if h: ty.isMonoType then
                      return ((LExpr.fvar () id (ty.toMonoType h)): LExpr Core.CoreLParams.mono)
                    else
                      TransM.error s!"translateVarStatement requires {id} to have a monomorphic type, but it has type {ty}")
    let bbindings := bindings.boundVars ++ newVars
    return (stmts, { bindings with boundVars := bbindings })

def translateInitStatement (p : Program) (bindings : TransBindings) (args : Array Arg)
    (md : MetaData Core.Expression):
  TransM ((List Core.Statement) × TransBindings) := do
  if args.size != 3 then
    TransM.error "translateInitStatement unexpected arg length {repr decls}"
  else
    let mty ← translateLMonoTy bindings args[0]!
    let lhs ← translateIdent Core.CoreIdent args[1]!
    let val ← translateExpr p bindings args[2]!
    let ty := (.forAll [] mty)
    let newBinding: LExpr Core.CoreLParams.mono := LExpr.fvar () lhs mty
    let bbindings := bindings.boundVars ++ [newBinding]
    return ([.init lhs ty (.det val) md], { bindings with boundVars := bbindings })

def translateOptionReachCheck (arg : Arg) : TransM Bool := do
  let .option _ rc := arg
    | TransM.error s!"translateOptionReachCheck unexpected {repr arg}"
  match rc with
  | some f =>
    let _ ← checkOpArg f q`Core.reachCheck 0
    return true
  | none => return false

/-- Translate an ExprOrNondet argument to ExprOrNondet. -/
private def translateCondBool (p : Program) (bindings : TransBindings) (a : Arg) :
    TransM (Imperative.ExprOrNondet Core.Expression) := do
  let .op op := a
    | TransM.error s!"translateCondBool expected op {repr a}"
  match op.name, op.args with
  | q`Core.condNondet, #[] => pure .nondet
  | q`Core.condDet, #[ca] => pure (.det (← translateExpr p bindings ca))
  | _, _ => TransM.error s!"translateCondBool: unexpected {repr op.name}"

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

partial def translateStmt (p : Program) (bindings : TransBindings) (arg : Arg) :
  TransM (List Core.Statement × TransBindings) := do
  let .op op := arg
    | TransM.error s!"translateStmt expected op {repr arg}"

  match op.name, op.args with
  | q`Core.varStatement, declsa =>
    translateVarStatement bindings declsa (← getOpMetaData op)
  | q`Core.initStatement, args =>
    translateInitStatement p bindings args (← getOpMetaData op)
  | q`Core.assign, #[_tpa, lhsa, ea] =>
    let lhs ← translateLhs lhsa
    let val ← translateExpr p bindings ea
    let md ← getOpMetaData op
    return ([.set lhs val md], bindings)
  | q`Core.havoc_statement, #[ida] =>
    let id ← translateIdent Core.CoreIdent ida
    let md ← getOpMetaData op
    return ([.havoc id md], bindings)
  | q`Core.assert, #[rca, la, ca] =>
    let c ← translateExpr p bindings ca
    let default_name := s!"assert_{bindings.gen.assert_def}"
    let bindings := incrNum .assert_def bindings
    let l ← translateOptionLabel default_name la
    let hasRC ← translateOptionReachCheck rca
    let md ← getOpMetaData op
    let md := if hasRC then md.pushElem MetaData.reachCheck (.switch true) else md
    return ([.assert l c md], bindings)
  | q`Core.cover, #[rca, la, ca] =>
    let c ← translateExpr p bindings ca
    let default_name := s!"cover_{bindings.gen.assert_def}"
    let bindings := incrNum .cover_def bindings
    let l ← translateOptionLabel default_name la
    let hasRC ← translateOptionReachCheck rca
    let md ← getOpMetaData op
    let md := if hasRC then md.pushElem MetaData.reachCheck (.switch true) else md
    return ([.cover l c md], bindings)
  | q`Core.assume, #[la, ca] =>
    let c ← translateExpr p bindings ca
    let default_name := s!"assume_{bindings.gen.assume_def}"
    let bindings := incrNum .assume_def bindings
    let l ← translateOptionLabel default_name la
    let md ← getOpMetaData op
    return ([.assume l c md], bindings)
  | q`Core.if_statement, #[ca, ta, fa] =>
    let (tss, thenBindings) ← translateBlock p bindings ta
    let (fss, elseBindings) ← translateElse p { bindings with gen := thenBindings.gen } fa
    let md ← getOpMetaData op
    let cond ← translateCondBool p bindings ca
    return ([.ite cond tss fss md], { bindings with gen := elseBindings.gen })
  | q`Core.while_statement, #[ca, ma, ia, ba] =>
    let measure ← translateMeasure p bindings ma
    let invs ← translateInvariants p bindings ia
    let (bodyss, bindings) ← translateBlock p bindings ba
    let md ← getOpMetaData op
    let guard ← translateCondBool p bindings ca
    return ([.loop guard measure invs bodyss md], bindings)
  | q`Core.call_statement, #[fa, callArgsa] =>
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
    let md ← getOpMetaData op
    return ([.call f callArgs md], bindings)
  | q`Core.block_statement, #[la, ba] =>
    let l ← translateIdent String la
    let (ss, innerBindings) ← translateBlock p bindings ba
    let md ← getOpMetaData op
    -- Blocks introduce lexical scope: variables declared inside are not
    -- visible after.  Only propagate counter state (gen), not boundVars.
    return ([.block l ss md], { bindings with gen := innerBindings.gen })
  | q`Core.exit_statement, #[la] =>
    let l ← translateIdent String la
    let md ← getOpMetaData op
    return ([.exit (some l) md], bindings)
  | q`Core.exit_unlabeled_statement, #[] =>
    let md ← getOpMetaData op
    return ([.exit none md], bindings)
  | q`Core.funcDecl_statement, #[namea, _typeArgsa, bindingsa, returna, precondsa, bodya, _inlinea] =>
    let name ← translateIdent Core.CoreIdent namea
    let inputs ← translateMonoDeclList bindings bindingsa
    let outputMono ← translateLMonoTy bindings returna
    let output : Core.Expression.Ty := .forAll [] outputMono
    let inputsConverted : ListMap Core.Expression.Ident Core.Expression.Ty :=
      inputs.map (fun (id, mty) => (id, .forAll [] mty))

    -- The DDM parser's @[scope(b)] on the body adds only the parameters.
    -- The function name is NOT in scope inside the body (declareFn adds it
    -- for subsequent statements only). So body bindings = outer + parameters.
    let funcType := Lambda.LMonoTy.mkArrow outputMono (inputs.values.reverse)
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
    let md ← getOpMetaData op
    -- Add the function to boundVars for subsequent statements.
    let updatedBindings := { bindings with boundVars := bindings.boundVars.push funcBinding }
    return ([.funcDecl decl md], updatedBindings)
  | q`Core.typeDecl_statement, #[namea, argsa] =>
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
    let md ← getOpMetaData op

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

/-- Translate bindings and partition into inputs/outputs based on `out`/`inout` modifiers.
    Returns (inputs, outputs) where `inout` params appear in both lists. -/
def translateBindingsPartitioned (bindings : TransBindings) (op : Arg) :
  TransM (ListMap Core.CoreIdent LMonoTy × ListMap Core.CoreIdent LMonoTy) := do
  let bargs ← checkOpArg op q`Core.mkBindings 1
  match bargs[0]! with
  | .seq _ .comma args =>
    let arr ← translateInitMkBindings bindings args
    let inputs := arr.toList.filterMap fun (id, ty, kind) =>
      if kind == .input || kind == .inout || kind == .cases then some (id, ty) else none
    let outputs := arr.toList.filterMap fun (id, ty, kind) =>
      if kind == .out || kind == .inout then some (id, ty) else none
    return (inputs, outputs)
  | _ =>
    TransM.error s!"translateBindingsPartitioned expects a comma separated list: {repr op}"

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

def translateProcedure (p : Program) (bindings : TransBindings) (op : Operation) :
  TransM (Core.Decl × TransBindings) := do
  let _ ← @checkOp (Core.Decl × TransBindings) op q`Core.command_procedure 5
  let pname ← translateIdent Core.CoreIdent op.args[0]!
  let typeArgs ← translateTypeArgs op.args[1]!
  let (sig, ret) ← translateBindingsPartitioned bindings op.args[2]!
  let in_bindings := (sig.map (fun (v, ty) => (LExpr.fvar () v ty))).toArray
  let out_bindings_only := (ret.filter (fun (v, _) => !sig.any (fun (iv, _) => iv == v))).map
    (fun (v, ty) => (LExpr.fvar () v ty))
  let out_bindings := out_bindings_only.toArray
  let origBindings := bindings
  let bbindings := bindings.boundVars ++ in_bindings ++ out_bindings
  let bindings := { bindings with boundVars := bbindings }
  let .option _ speca := op.args[3]!
    | TransM.error s!"translateProcedure spec. expected here: {repr op.args[3]!}"
  let (requires, ensures) ←
    if speca.isSome then translateSpec p pname bindings speca.get! else pure ([], [])
  let .option _ bodya := op.args[4]!
    | TransM.error s!"translateProcedure body expected here: {repr op.args[4]!}"
  let (body, bindings) ← if bodya.isSome then translateBlock p bindings bodya.get! else pure ([], bindings)
  let origBindings := { origBindings with gen := bindings.gen }
  let md ← getOpMetaData op
  return (.proc { header := { name := pname,
                              typeArgs := typeArgs.toList,
                              inputs := sig,
                              outputs := ret },
                  spec := { preconditions := requires,
                            postconditions := ensures },
                  body := body
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
                  body := body
                }
                md,
          bindings)

---------------------------------------------------------------------

def translateConstant (bindings : TransBindings) (op : Operation) :
  TransM (Core.Decl × TransBindings) := do
  let _ ← @checkOp (Core.Decl × TransBindings) op q`Core.command_constdecl 3
  let cname ← translateIdent Core.CoreIdent op.args[0]!
  let typeArgs ← translateTypeArgs op.args[1]!
  let ret ← translateLMonoTy bindings op.args[2]!
  let md ← getOpMetaData op
  let decl := .func { name := cname,
                      typeArgs := typeArgs.toList,
                      inputs := [],
                      output := ret,
                      body := none }
                    md
  return (decl, { bindings with freeVars := bindings.freeVars.push decl })

---------------------------------------------------------------------

def translateAxiom (p : Program) (bindings : TransBindings) (op : Operation) :
  TransM (Core.Decl × TransBindings) := do
  let _ ← @checkOp (Core.Decl × TransBindings) op q`Core.command_axiom 2
  let default_name := s!"axiom_{bindings.gen.axiom_def}"
  let bindings := incrNum .axiom_def bindings
  let l ← translateOptionLabel default_name op.args[0]!
  let e ← translateExpr p bindings op.args[1]!
  let md ← getOpMetaData op
  return (.ax (Core.Axiom.mk l e) md, bindings)

def translateDistinct (p : Program) (bindings : TransBindings) (op : Operation) :
  TransM (Core.Decl × TransBindings) := do
  let _ ← @checkOp (Core.Decl × TransBindings) op q`Core.command_distinct 2
  let default_name := s!"axiom_distinct_{bindings.gen.axiom_def}"
  let bindings := incrNum .axiom_def bindings
  let l ← translateOptionLabel default_name op.args[0]!
  let es ← translateCommaSep (translateExpr p bindings) op.args[1]!
  if !(es.all LExpr.isOp) then
    TransM.error s!"arguments to `distinct` must all be constant names: {es}"
  let md ← getOpMetaData op
  return (.distinct l es.toList md, bindings)

---------------------------------------------------------------------

inductive FnInterp where
  | Definition
  | Declaration
  deriving Repr

def translateOptionInline (arg : Arg) : TransM (Array Strata.DL.Util.FuncAttr) := do
  let .option _ inline := arg
    | TransM.error s!"translateOptionInline unexpected {repr arg}"
  match inline with
  | some f =>
    let _ ← checkOpArg f q`Core.inline 0
    return #[.inline]
  | none => return #[]

def translateFunction (status : FnInterp) (p : Program) (bindings : TransBindings) (op : Operation) :
  TransM (Core.Decl × TransBindings) := do
  let _ ←
    match status with
    | .Definition           => @checkOp (Core.Decl × TransBindings) op q`Core.command_fndef     7
    | .Declaration          => @checkOp (Core.Decl × TransBindings) op q`Core.command_fndecl    4
  let fname ← translateIdent Core.CoreIdent op.args[0]!
  let typeArgs ← translateTypeArgs op.args[1]!
  let sig ← translateBindings bindings op.args[2]!
  let ret ← translateLMonoTy bindings op.args[3]!
  let in_bindings := (sig.map (fun (v, ty) => (LExpr.fvar () v ty))).toArray
  let orig_bbindings := bindings.boundVars
  let bbindings := bindings.boundVars ++ in_bindings
  let bindings := { bindings with boundVars := bbindings }
  let (preconds, body, inline?) ← match status with
    | .Definition =>
      let preconds ← translateFnPreconds p fname bindings op.args[4]!
      let e ← translateExpr p bindings op.args[5]!
      let inline? ← translateOptionInline op.args[6]!
      pure (preconds, some e, inline?)
    | .Declaration => pure ([], none, #[])
  let md ← getOpMetaData op
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
  let _ ← @checkOp Core.Function fnOp q`Core.recfn_decl 6
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
    | none => #[]
  let preconds ← translateFnPreconds p fname bodyBindings fnOp.args[4]!
  let body ← translateExpr p bodyBindings fnOp.args[5]!
  return { name := fname, typeArgs := typeArgs.toList, isRecursive := true,
           inputs := sig, output := ret, body := some body,
           attr := casesAttr, preconditions := preconds }

/--
Translate a `command_recfndefs` block (one or more mutually recursive functions).
-/
partial def translateRecFuncBlock (p : Program) (bindings : TransBindings) (op : Operation) :
    TransM (Core.Decl × TransBindings) := do
  let _ ← @checkOp (Core.Decl × TransBindings) op q`Core.command_recfndefs 1

  let .seq _ _ declarations := op.args[0]!
    | TransM.error s!"translateRecFuncBlock expected sequence: {repr op.args[0]!}"

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

    let md ← getOpMetaData op
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
  return factory.toArray.toList.map fun func => Core.Decl.func func .empty

---------------------------------------------------------------------

/--
Translate a datatype block (one or more datatype declarations).
The `@[preRegisterTypes]` metadata on `command_datatypes` ensures that
type names are pre-registered in the DDM GlobalContext before processing.
-/
def translateDatatypes (p : Program) (bindings : TransBindings) (op : Operation) :
    TransM (Core.Decl × TransBindings) := do
  let _ ← @checkOp (Core.Decls × TransBindings) op q`Core.command_datatypes 1

  let .seq _ _ declarations := op.args[0]!
    | TransM.error s!"translateDatatypes expected sequence: {repr op.args[0]!}"

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

    let md ← getOpMetaData op
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
  let (decls, _) ← go 0 p.commands.size bindings p.commands
  return decls
  where go (count max : Nat) bindings ops : TransM (Core.Decls × TransBindings) := do
  match (max - count) with
  | 0 => return ([], bindings)
  | _ + 1 =>
    let op := ops[count]!
    let (newDecls, bindings) ← do
        let (decl, bindings) ←
          match op.name with
          | q`Core.command_datatypes =>
            translateDatatypes p bindings op
          | q`Core.command_constdecl =>
            translateConstant bindings op
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
          | _ => TransM.error s!"translateCoreDecls unimplemented for {repr op}"
        pure ([decl], bindings)
    let (decls, bindings) ← go (count + 1) max bindings ops
    return (newDecls ++ decls, bindings)

def translateProgram (p : Program) : TransM Core.Program := do
  fun s => ((), { s with globalContext := p.globalContext })
  let decls ← translateCoreDecls p {}
  return { decls := decls }

---------------------------------------------------------------------

end -- public section

end Strata
