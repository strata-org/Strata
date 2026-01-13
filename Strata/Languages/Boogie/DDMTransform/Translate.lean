/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST
import Strata.Languages.Boogie.DDMTransform.Parse
import Strata.Languages.Boogie.BoogieGen
import Strata.DDM.Util.DecimalRat


---------------------------------------------------------------------
namespace Strata

/- Translating concrete syntax into abstract syntax -/

open Boogie Lambda Imperative Lean.Parser
open Std (ToFormat Format format)

---------------------------------------------------------------------

/- Translation Monad -/

structure TransState where
  inputCtx : InputContext
  errors : Array String

def TransM := StateM TransState
  deriving Monad

def TransM.run (ictx : InputContext) (m : TransM α) : (α × Array String) :=
  let (v, s) := StateT.run m { inputCtx := ictx, errors := #[] }
  (v, s.errors)

instance : ToString (Boogie.Program × Array String) where
  toString p := toString (Std.format p.fst) ++ "\n" ++
                "Errors: " ++ (toString p.snd)

def TransM.error [Inhabited α] (msg : String) : TransM α := do
  fun s => ((), { s with errors := s.errors.push msg })
  return panic msg

---------------------------------------------------------------------

/- Metadata -/

def SourceRange.toMetaData (ictx : InputContext) (sr : SourceRange) : Imperative.MetaData Boogie.Expression :=
  let file := ictx.fileName
  let startPos := ictx.fileMap.toPosition sr.start
  let endPos := ictx.fileMap.toPosition sr.stop
  let uri: Uri := .file file
  let fileRangeElt := ⟨ MetaData.fileRange, .fileRange ⟨ uri, startPos, endPos ⟩ ⟩
  #[fileRangeElt]

def getOpMetaData (op : Operation) : TransM (Imperative.MetaData Boogie.Expression) :=
  return op.ann.toMetaData (← StateT.get).inputCtx

def getArgMetaData (arg : Arg) : TransM (Imperative.MetaData Boogie.Expression) :=
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
  let .commaSepList _ args := arg
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
                    | some lop => let args ← checkOpArg lop q`Boogie.label 1
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
  | var_def | axiom_def | assume_def | assert_def
  deriving DecidableEq

/--
Counters for assigning default names for various definitions.
-/
structure GenNum where
  var_def : Nat
  axiom_def : Nat
  assume_def : Nat
  assert_def : Nat
  deriving Repr

structure TransBindings where
  boundTypeVars : Array TyIdentifier := #[]
  boundVars : Array (LExpr BoogieLParams.mono) := #[]
  freeVars  : Array Boogie.Decl := #[]
  gen : GenNum := (GenNum.mk 0 0 0 0)

def incrNum (gen_kind : GenKind) (b : TransBindings) : TransBindings :=
  let gen := b.gen
  let new_gen :=
    match gen_kind with
    | .var_def => { gen with var_def := gen.var_def + 1 }
    | .axiom_def => { gen with axiom_def := gen.axiom_def + 1 }
    | .assume_def => { gen with assume_def := gen.assume_def + 1 }
    | .assert_def => { gen with assert_def := gen.assert_def + 1 }
  { b with gen := new_gen }

instance : ToFormat TransBindings where
  format b := f!"BoundTypeVars: {b.boundTypeVars}\
                {Format.line}\
                BoundVars: {b.boundVars}\
                {Format.line}\
                FreeVars: {b.freeVars}\
                {Format.line}\
                Gen: {repr b.gen}"

instance : Inhabited (List Boogie.Statement × TransBindings) where
  default := ([], {})

instance : Inhabited Boogie.Decl where
  default := .var "badguy" (.forAll [] (.tcons "bool" [])) (.false ())

instance : Inhabited (Procedure.CheckAttr) where
  default := .Default

instance : Inhabited (Boogie.Decl × TransBindings) where
  default := (.var "badguy" (.forAll [] (.tcons "bool" [])) (.false ()), {})

instance : Inhabited (Boogie.Decls × TransBindings) where
  default := ([], {})

instance : Inhabited (List BoogieIdent × TransBindings) where
  default := ([], {})

instance : Inhabited (List TyIdentifier × TransBindings) where
  default := ([], {})

---------------------------------------------------------------------

def translateTypeBinding (bindings : TransBindings) (op : Arg) :
  TransM (TyIdentifier × TransBindings) := do
  -- (FIXME) Account for metadata.
  let bargs ← checkOpArg op q`Boogie.mkBinding 2
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
  | .ident _ q`Boogie.bv1 #[] => pure <| .bitvec 1
  | .ident _ q`Boogie.bv8 #[] => pure <| .bitvec 8
  | .ident _ q`Boogie.bv16 #[] => pure <| .bitvec 16
  | .ident _ q`Boogie.bv32 #[] => pure <| .bitvec 32
  | .ident _ q`Boogie.bv64 #[] => pure <| .bitvec 64
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
                    -- Boogie is concerned. See `Boogie.TypeConstructor`, where there is no
                    -- facility for providing the type arguments.
                    pure ty.toMonoTypeUnsafe
                  | .type (.syn syn) _md =>
                    let ty := syn.toLHSLMonoTy
                    pure ty
                  | .type (.data ldatatype) =>
                    -- Datatype Declaration
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
  | _ => TransM.error s!"translateLMonoTy not yet implemented {repr tp}"

partial def translateLMonoTys (bindings : TransBindings) (args : Array Arg) :
  TransM (Array LMonoTy) :=
  args.mapM (fun a => translateLMonoTy bindings a)
end

def translateTypeArgs (op : Strata.Arg) : TransM (Array TyIdentifier) := do
  translateOption (fun x => do match x with
                  | none => return Array.empty
                  | some a =>
                    let args ← checkOpArg a q`Boogie.type_args 1
                    translateCommaSep (translateIdent TyIdentifier) args[0]!)
                  op

def translateTypeSynonym (bindings : TransBindings) (op : Operation) :
  TransM (Boogie.Decl × TransBindings) := do
  let _ ← @checkOp (Boogie.Decl × TransBindings) op q`Boogie.command_typesynonym 4
  let name ← translateIdent TyIdentifier op.args[0]!
  let (targs, bindings) ←
    translateOption
      (fun maybearg =>
            do match maybearg with
            | none => pure ([], bindings)
            | some arg =>
              let bargs ← checkOpArg arg q`Boogie.mkBindings 1
              let args ←
                  match bargs[0]! with
                  | .commaSepList _ args =>
                    let (arr, bindings) ← translateTypeBindings bindings args
                    return (arr.toList, bindings)
                  | _ => TransM.error
                          s!"translateTypeSynonym expects a comma separated list: {repr bargs[0]!}")
                    op.args[1]!
  let typedef ← translateLMonoTy bindings op.args[3]!
  let md ← getOpMetaData op
  let decl := Boogie.Decl.type (.syn { name := name, typeArgs := targs, type := typedef }) md
  return (decl, { bindings with freeVars := bindings.freeVars.push decl })


def translateTypeDecl (bindings : TransBindings) (op : Operation) :
  TransM (Boogie.Decl × TransBindings) := do
  let _ ← @checkOp (Boogie.Decl × TransBindings) op q`Boogie.command_typedecl 2
  let name ← translateIdent TyIdentifier op.args[0]!
  let numargs ←
    translateOption
      (fun maybearg =>
            do match maybearg with
            | none => pure 0
            | some arg =>
              let bargs ← checkOpArg arg q`Boogie.mkBindings 1
              let numargs ←
                  match bargs[0]! with
                  | .commaSepList _ args => pure args.size
                  | _ => TransM.error
                          s!"translateTypeDecl expects a comma separated list: {repr bargs[0]!}")
                    op.args[1]!
  let md ← getOpMetaData op
  -- Only the number of type arguments is important; the exact identifiers are
  -- irrelevant.
  let decl := Boogie.Decl.type (.con { name := name, numargs := numargs }) md
  return (decl, { bindings with freeVars := bindings.freeVars.push decl })

---------------------------------------------------------------------

def translateLhs (arg : Arg) : TransM BoogieIdent := do
  let .op op := arg
    | TransM.error s!"translateLhs expected op {repr arg}"
  match op.name, op.args with
  | q`Boogie.lhsIdent, #[id] => translateIdent BoogieIdent id
  -- (TODO) Implement lhsArray.
  | _, _ => TransM.error s!"translateLhs: unimplemented for {repr arg}"

def translateBindMk (bindings : TransBindings) (arg : Arg) :
   TransM (BoogieIdent × List TyIdentifier × LMonoTy) := do
  let .op op := arg
    | TransM.error s!"translateBindMk expected op {repr arg}"
  match op.name, op.args with
  | q`Boogie.bind_mk, #[ida, targsa, tpa] =>
    let id ← translateIdent BoogieIdent ida
    let args ← translateTypeArgs targsa
    let tp ← translateLMonoTy bindings tpa
    return (id, args.toList, tp)
  | _, _ =>
    TransM.error s!"translateBindMk unimplemented for {repr arg}"

def translateMonoBindMk (bindings : TransBindings) (arg : Arg) :
   TransM (BoogieIdent × LMonoTy) := do
  let .op op := arg
    | TransM.error s!"translateMonoBindMk expected op {repr arg}"
  match op.name, op.args with
  | q`Boogie.mono_bind_mk, #[ida, tpa] =>
    let id ← translateIdent BoogieIdent ida
    let tp ← translateLMonoTy bindings tpa
    return (id, tp)
  | _, _ =>
    TransM.error s!"translateMonoBindMk unimplemented for {repr arg}"

partial def translateDeclList (bindings : TransBindings) (arg : Arg) :
  TransM (ListMap Expression.Ident LTy) := do
  let .op op := arg
    | TransM.error s!"translateDeclList expects an op {repr arg}"
  match op.name with
  | q`Boogie.declAtom =>
    let args ← checkOpArg arg q`Boogie.declAtom 1
    let (id, targs, mty) ← translateBindMk bindings args[0]!
    let lty := .forAll targs mty
    pure [(id, lty)]
  | q`Boogie.declPush =>
    let args ← checkOpArg arg q`Boogie.declPush 2
    let fst ← translateDeclList bindings args[0]!
    let (id, targs, mty) ← translateBindMk bindings args[1]!
    let lty : LTy := .forAll targs mty
    pure (fst ++ ListMap.ofList [(id, lty)])
  | _ => TransM.error s!"translateDeclList unimplemented for {repr op}"

partial def translateMonoDeclList (bindings : TransBindings) (arg : Arg) :
  TransM (ListMap Expression.Ident LMonoTy) := do
  let .op op := arg
    | TransM.error s!"translateMonoDeclList expects an op {repr arg}"
  match op.name with
  | q`Boogie.monoDeclAtom =>
    let args ← checkOpArg arg q`Boogie.monoDeclAtom 1
    let (id, mty) ← translateMonoBindMk bindings args[0]!
    pure [(id, mty)]
  | q`Boogie.monoDeclPush =>
    let args ← checkOpArg arg q`Boogie.monoDeclPush 2
    let fst ← translateMonoDeclList bindings args[0]!
    let (id, mty) ← translateMonoBindMk bindings args[1]!
    pure (fst ++ ListMap.ofList [(id, mty)])
  | _ => TransM.error s!"translateMonoDeclList unimplemented for {repr op}"

def translateOptionMonoDeclList (bindings : TransBindings) (arg : Arg) :
  TransM (ListMap Expression.Ident LMonoTy) :=
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

def translateFn (ty? : Option LMonoTy) (q : QualifiedIdent) : TransM Boogie.Expression.Expr :=
  match ty?, q with
  | _, q`Boogie.equiv    => return boolEquivOp
  | _, q`Boogie.implies  => return boolImpliesOp
  | _, q`Boogie.and      => return boolAndOp
  | _, q`Boogie.or       => return boolOrOp
  | _, q`Boogie.not      => return boolNotOp

  | .some .int, q`Boogie.le       => return intLeOp
  | .some .int, q`Boogie.lt       => return intLtOp
  | .some .int, q`Boogie.ge       => return intGeOp
  | .some .int, q`Boogie.gt       => return intGtOp
  | .some .int, q`Boogie.add_expr => return intAddOp
  | .some .int, q`Boogie.sub_expr => return intSubOp
  | .some .int, q`Boogie.mul_expr => return intMulOp
  | .some .int, q`Boogie.div_expr => return intDivOp
  | .some .int, q`Boogie.mod_expr => return intModOp
  | .some .int, q`Boogie.neg_expr => return intNegOp

  | .some .real, q`Boogie.le       => return realLeOp
  | .some .real, q`Boogie.lt       => return realLtOp
  | .some .real, q`Boogie.ge       => return realGeOp
  | .some .real, q`Boogie.gt       => return realGtOp
  | .some .real, q`Boogie.add_expr => return realAddOp
  | .some .real, q`Boogie.sub_expr => return realSubOp
  | .some .real, q`Boogie.mul_expr => return realMulOp
  | .some .real, q`Boogie.div_expr => return realDivOp
  | .some .real, q`Boogie.neg_expr => return realNegOp

  | .some .bv1, q`Boogie.le       => return bv1ULeOp
  | .some .bv1, q`Boogie.lt       => return bv1ULtOp
  | .some .bv1, q`Boogie.ge       => return bv1UGeOp
  | .some .bv1, q`Boogie.gt       => return bv1UGtOp
  | .some .bv1, q`Boogie.bvsle    => return bv1SLeOp
  | .some .bv1, q`Boogie.bvslt    => return bv1SLtOp
  | .some .bv1, q`Boogie.bvsge    => return bv1SGeOp
  | .some .bv1, q`Boogie.bvsgt    => return bv1SGtOp
  | .some .bv1, q`Boogie.neg_expr => return bv1NegOp
  | .some .bv1, q`Boogie.add_expr => return bv1AddOp
  | .some .bv1, q`Boogie.sub_expr => return bv1SubOp
  | .some .bv1, q`Boogie.mul_expr => return bv1MulOp
  | .some .bv1, q`Boogie.div_expr => return bv1UDivOp
  | .some .bv1, q`Boogie.mod_expr => return bv1UModOp
  | .some .bv1, q`Boogie.bvsdiv   => return bv1SDivOp
  | .some .bv1, q`Boogie.bvsmod   => return bv1SModOp
  | .some .bv1, q`Boogie.bvnot    => return bv1NotOp
  | .some .bv1, q`Boogie.bvand    => return bv1AndOp
  | .some .bv1, q`Boogie.bvor     => return bv1OrOp
  | .some .bv1, q`Boogie.bvxor    => return bv1XorOp
  | .some .bv1, q`Boogie.bvshl    => return bv1ShlOp
  | .some .bv1, q`Boogie.bvushr   => return bv1UShrOp
  | .some .bv1, q`Boogie.bvsshr   => return bv1SShrOp

  | .some .bv8, q`Boogie.le       => return bv8ULeOp
  | .some .bv8, q`Boogie.lt       => return bv8ULtOp
  | .some .bv8, q`Boogie.ge       => return bv8UGeOp
  | .some .bv8, q`Boogie.gt       => return bv8UGtOp
  | .some .bv8, q`Boogie.bvsle    => return bv8SLeOp
  | .some .bv8, q`Boogie.bvslt    => return bv8SLtOp
  | .some .bv8, q`Boogie.bvsge    => return bv8SGeOp
  | .some .bv8, q`Boogie.bvsgt    => return bv8SGtOp
  | .some .bv8, q`Boogie.neg_expr => return bv8NegOp
  | .some .bv8, q`Boogie.add_expr => return bv8AddOp
  | .some .bv8, q`Boogie.sub_expr => return bv8SubOp
  | .some .bv8, q`Boogie.mul_expr => return bv8MulOp
  | .some .bv8, q`Boogie.div_expr => return bv8UDivOp
  | .some .bv8, q`Boogie.mod_expr => return bv8UModOp
  | .some .bv8, q`Boogie.bvsdiv   => return bv8SDivOp
  | .some .bv8, q`Boogie.bvsmod   => return bv8SModOp
  | .some .bv8, q`Boogie.bvnot    => return bv8NotOp
  | .some .bv8, q`Boogie.bvand    => return bv8AndOp
  | .some .bv8, q`Boogie.bvor     => return bv8OrOp
  | .some .bv8, q`Boogie.bvxor    => return bv8XorOp
  | .some .bv8, q`Boogie.bvshl    => return bv8ShlOp
  | .some .bv8, q`Boogie.bvushr   => return bv8UShrOp
  | .some .bv8, q`Boogie.bvsshr   => return bv8SShrOp

  | .some .bv16, q`Boogie.le       => return bv16ULeOp
  | .some .bv16, q`Boogie.lt       => return bv16ULtOp
  | .some .bv16, q`Boogie.ge       => return bv16UGeOp
  | .some .bv16, q`Boogie.gt       => return bv16UGtOp
  | .some .bv16, q`Boogie.bvsle    => return bv16SLeOp
  | .some .bv16, q`Boogie.bvslt    => return bv16SLtOp
  | .some .bv16, q`Boogie.bvsge    => return bv16SGeOp
  | .some .bv16, q`Boogie.bvsgt    => return bv16SGtOp
  | .some .bv16, q`Boogie.neg_expr => return bv16NegOp
  | .some .bv16, q`Boogie.add_expr => return bv16AddOp
  | .some .bv16, q`Boogie.sub_expr => return bv16SubOp
  | .some .bv16, q`Boogie.mul_expr => return bv16MulOp
  | .some .bv16, q`Boogie.div_expr => return bv16UDivOp
  | .some .bv16, q`Boogie.mod_expr => return bv16UModOp
  | .some .bv16, q`Boogie.bvsdiv   => return bv16SDivOp
  | .some .bv16, q`Boogie.bvsmod   => return bv16SModOp
  | .some .bv16, q`Boogie.bvnot    => return bv16NotOp
  | .some .bv16, q`Boogie.bvand    => return bv16AndOp
  | .some .bv16, q`Boogie.bvor     => return bv16OrOp
  | .some .bv16, q`Boogie.bvxor    => return bv16XorOp
  | .some .bv16, q`Boogie.bvshl    => return bv16ShlOp
  | .some .bv16, q`Boogie.bvushr   => return bv16UShrOp
  | .some .bv16, q`Boogie.bvsshr   => return bv16SShrOp

  | .some .bv32, q`Boogie.le       => return bv32ULeOp
  | .some .bv32, q`Boogie.lt       => return bv32ULtOp
  | .some .bv32, q`Boogie.ge       => return bv32UGeOp
  | .some .bv32, q`Boogie.gt       => return bv32UGtOp
  | .some .bv32, q`Boogie.bvsle    => return bv32SLeOp
  | .some .bv32, q`Boogie.bvslt    => return bv32SLtOp
  | .some .bv32, q`Boogie.bvsge    => return bv32SGeOp
  | .some .bv32, q`Boogie.bvsgt    => return bv32SGtOp
  | .some .bv32, q`Boogie.neg_expr => return bv32NegOp
  | .some .bv32, q`Boogie.add_expr => return bv32AddOp
  | .some .bv32, q`Boogie.sub_expr => return bv32SubOp
  | .some .bv32, q`Boogie.mul_expr => return bv32MulOp
  | .some .bv32, q`Boogie.div_expr => return bv32UDivOp
  | .some .bv32, q`Boogie.mod_expr => return bv32UModOp
  | .some .bv32, q`Boogie.bvsdiv   => return bv32SDivOp
  | .some .bv32, q`Boogie.bvsmod   => return bv32SModOp
  | .some .bv32, q`Boogie.bvnot    => return bv32NotOp
  | .some .bv32, q`Boogie.bvand    => return bv32AndOp
  | .some .bv32, q`Boogie.bvor     => return bv32OrOp
  | .some .bv32, q`Boogie.bvxor    => return bv32XorOp
  | .some .bv32, q`Boogie.bvshl    => return bv32ShlOp
  | .some .bv32, q`Boogie.bvushr   => return bv32UShrOp
  | .some .bv32, q`Boogie.bvsshr   => return bv32SShrOp

  | .some .bv64, q`Boogie.le       => return bv64ULeOp
  | .some .bv64, q`Boogie.lt       => return bv64ULtOp
  | .some .bv64, q`Boogie.ge       => return bv64UGeOp
  | .some .bv64, q`Boogie.gt       => return bv64UGtOp
  | .some .bv64, q`Boogie.bvsle    => return bv64SLeOp
  | .some .bv64, q`Boogie.bvslt    => return bv64SLtOp
  | .some .bv64, q`Boogie.bvsge    => return bv64SGeOp
  | .some .bv64, q`Boogie.bvsgt    => return bv64SGtOp
  | .some .bv64, q`Boogie.neg_expr => return bv64NegOp
  | .some .bv64, q`Boogie.add_expr => return bv64AddOp
  | .some .bv64, q`Boogie.sub_expr => return bv64SubOp
  | .some .bv64, q`Boogie.mul_expr => return bv64MulOp
  | .some .bv64, q`Boogie.div_expr => return bv64UDivOp
  | .some .bv64, q`Boogie.mod_expr => return bv64UModOp
  | .some .bv64, q`Boogie.bvsdiv   => return bv64SDivOp
  | .some .bv64, q`Boogie.bvsmod   => return bv64SModOp
  | .some .bv64, q`Boogie.bvnot    => return bv64NotOp
  | .some .bv64, q`Boogie.bvand    => return bv64AndOp
  | .some .bv64, q`Boogie.bvor     => return bv64OrOp
  | .some .bv64, q`Boogie.bvxor    => return bv64XorOp
  | .some .bv64, q`Boogie.bvshl    => return bv64ShlOp
  | .some .bv64, q`Boogie.bvushr   => return bv64UShrOp
  | .some .bv64, q`Boogie.bvsshr   => return bv64SShrOp

  | _, q`Boogie.bvconcat8 => return bv8ConcatOp
  | _, q`Boogie.bvconcat16 => return bv16ConcatOp
  | _, q`Boogie.bvconcat32 => return bv32ConcatOp
  | _, q`Boogie.bvextract_7_7     => return bv8Extract_7_7_Op
  | _, q`Boogie.bvextract_15_15   => return bv16Extract_15_15_Op
  | _, q`Boogie.bvextract_31_31   => return bv32Extract_31_31_Op
  | _, q`Boogie.bvextract_7_0_16  => return bv16Extract_7_0_Op
  | _, q`Boogie.bvextract_7_0_32  => return bv32Extract_7_0_Op
  | _, q`Boogie.bvextract_15_0_32 => return bv32Extract_15_0_Op
  | _, q`Boogie.bvextract_7_0_64  => return bv64Extract_7_0_Op
  | _, q`Boogie.bvextract_15_0_64 => return bv64Extract_15_0_Op
  | _, q`Boogie.bvextract_31_0_64 => return bv64Extract_31_0_Op

  | _, q`Boogie.old          => return polyOldOp
  | _, q`Boogie.str_len      => return strLengthOp
  | _, q`Boogie.str_concat   => return strConcatOp
  | _, q`Boogie.str_substr   => return strSubstrOp
  | _, q`Boogie.str_toregex  => return strToRegexOp
  | _, q`Boogie.str_inregex  => return strInRegexOp
  | _, q`Boogie.re_all       => return reAllOp
  | _, q`Boogie.re_allchar   => return reAllCharOp
  | _, q`Boogie.re_range     => return reRangeOp
  | _, q`Boogie.re_concat    => return reConcatOp
  | _, q`Boogie.re_star      => return reStarOp
  | _, q`Boogie.re_plus      => return rePlusOp
  | _, q`Boogie.re_loop      => return reLoopOp
  | _, q`Boogie.re_union     => return reUnionOp
  | _, q`Boogie.re_inter     => return reInterOp
  | _, q`Boogie.re_comp      => return reCompOp
  | _, q`Boogie.re_none      => return reNoneOp
  | _, _ => TransM.error s!"translateFn: Unknown/unimplemented function {repr q} at type {repr ty?}"

mutual

partial
def translateQuantifier
  (qk: QuantifierKind)
  (p : Program)
  (bindings : TransBindings) (xsa : Arg) (triggersa: Option Arg) (bodya: Arg) :
  TransM Boogie.Expression.Expr := do
    let xsArray ← translateDeclList bindings xsa
    -- Note: the indices in the following are placeholders
    let newBoundVars := List.toArray (xsArray.mapIdx (fun i _ => LExpr.bvar () i))
    let boundVars' := bindings.boundVars ++ newBoundVars
    let xbindings := { bindings with boundVars := boundVars' }
    let b ← translateExpr p xbindings bodya

    -- Handle triggers if present
    let triggers ← match triggersa with
      | none => pure (LExpr.noTrigger ())
      | some tsa => translateTriggers p xbindings tsa

    -- Create one quantifier constructor per variable
    -- Trigger attached to only the innermost quantifier
    let buildQuantifier := fun (_, ty) (e, first) =>
      match ty with
      | .forAll [] mty =>
        let triggers := if first then
            triggers
          else
            LExpr.noTrigger ()
        (.quant () qk (.some mty) triggers e, false)
      | _ => panic! s!"Expected monomorphic type in quantifier, got: {ty}"

    return xsArray.foldr buildQuantifier (init := (b, true)) |>.1

partial
def translateTriggerGroup (p: Program) (bindings : TransBindings) (arg : Arg) :
  TransM Boogie.Expression.Expr := do
  let .op op := arg
    | TransM.error s!"translateTriggerGroup expected op, got {repr arg}"
  match op.name, op.args with
  | q`Boogie.trigger, #[tsa] => do
   let ts  ← translateCommaSep (fun t => translateExpr p bindings t) tsa
   return ts.foldl (fun g t => .app () (.app () addTriggerOp t) g) emptyTriggerGroupOp
  | _, _ => panic! s!"Unexpected operator in trigger group"

partial
def translateTriggers (p: Program) (bindings : TransBindings) (arg : Arg) :
  TransM Boogie.Expression.Expr := do
  let .op op := arg
    | TransM.error s!"translateTriggers expected op, got: {repr arg}"
  match op.name, op.args with
  | q`Boogie.triggersAtom, #[group] =>
    let g ← translateTriggerGroup p bindings group
    return .app () (.app () addTriggerGroupOp g) emptyTriggersOp
  | q`Boogie.triggersPush, #[triggers, group] => do
    let ts ← translateTriggers p bindings triggers
    let g ← translateTriggerGroup p bindings group
    return .app () (.app () addTriggerGroupOp g) ts
  | _, _ => panic! s!"Unexpected operator in trigger"

partial def translateExpr (p : Program) (bindings : TransBindings) (arg : Arg) :
  TransM Boogie.Expression.Expr := do
  let .expr expr := arg
    | TransM.error s!"translateExpr expected expr {repr arg}"
  let (op, args) := expr.flatten
  match op, args with
  -- Constants/Literals
  | .fn _ q`Boogie.btrue, [] =>
    return .true ()
  | .fn _ q`Boogie.bfalse, [] =>
    return .false ()
  | .fn _ q`Boogie.natToInt, [xa] =>
    let n ← translateNat xa
    return .intConst () n
  | .fn _ q`Boogie.bv1Lit, [xa] =>
    let n ← translateBitVec 1 xa
    return .bitvecConst () 1 n
  | .fn _ q`Boogie.bv8Lit, [xa] =>
    let n ← translateBitVec 8 xa
    return .bitvecConst () 8 n
  | .fn _ q`Boogie.bv16Lit, [xa] =>
    let n ← translateBitVec 16 xa
    return .bitvecConst () 16 n
  | .fn _ q`Boogie.bv32Lit, [xa] =>
    let n ← translateBitVec 32 xa
    return .bitvecConst () 32 n
  | .fn _ q`Boogie.bv64Lit, [xa] =>
    let n ← translateBitVec 64 xa
    return .bitvecConst () 64 n
  | .fn _ q`Boogie.strLit, [xa] =>
    let x ← translateStr xa
    return .strConst () x
  | .fn _ q`Boogie.realLit, [xa] =>
    let x ← translateReal xa
    return .realConst () (Strata.Decimal.toRat x)
  -- Equality
  | .fn _ q`Boogie.equal, [_tpa, xa, ya] =>
    let x ← translateExpr p bindings xa
    let y ← translateExpr p bindings ya
    return .eq () x y
  | .fn _ q`Boogie.not_equal, [_tpa, xa, ya] =>
    let x ← translateExpr p bindings xa
    let y ← translateExpr p bindings ya
    return (.app () Boogie.boolNotOp (.eq () x y))
  | .fn _ q`Boogie.bvnot, [tpa, xa] =>
    let tp ← translateLMonoTy bindings (dealiasTypeArg p tpa)
    let x ← translateExpr p bindings xa
    let fn : LExpr BoogieLParams.mono ←
      translateFn (.some tp) q`Boogie.bvnot
    return (.app () fn x)
  -- If-then-else expression
  | .fn _ q`Boogie.if, [_tpa, ca, ta, fa] =>
    let c ← translateExpr p bindings ca
    let t ← translateExpr p bindings ta
    let f ← translateExpr p bindings fa
    return .ite () c t f
  -- Re.AllChar
  | .fn _ q`Boogie.re_allchar, [] =>
    let fn ← translateFn .none q`Boogie.re_allchar
    return fn
  -- Re.None
  | .fn _ q`Boogie.re_none, [] =>
    let fn ← translateFn .none q`Boogie.re_none
    return fn
  -- Re.All
  | .fn _ q`Boogie.re_all, [] =>
    let fn ← translateFn .none q`Boogie.re_all
    return fn
  -- Unary function applications
  | .fn _ fni, [xa] =>
    match fni with
    | q`Boogie.not
    | q`Boogie.bvextract_7_7
    | q`Boogie.bvextract_15_15
    | q`Boogie.bvextract_31_31
    | q`Boogie.bvextract_7_0_16
    | q`Boogie.bvextract_7_0_32
    | q`Boogie.bvextract_15_0_32
    | q`Boogie.bvextract_7_0_64
    | q`Boogie.bvextract_15_0_64
    | q`Boogie.bvextract_31_0_64
    | q`Boogie.str_len
    | q`Boogie.str_toregex
    | q`Boogie.re_star
    | q`Boogie.re_plus
    | q`Boogie.re_comp => do
      let fn ← translateFn .none fni
      let x ← translateExpr p bindings xa
      return .mkApp () fn [x]
    | _ => TransM.error s!"translateExpr unimplemented {repr op} {repr args}"
  | .fn _ q`Boogie.neg_expr, [tpa, xa] =>
    let ty ← translateLMonoTy bindings (dealiasTypeArg p tpa)
    let fn ← translateFn ty q`Boogie.neg_expr
    let x ← translateExpr p bindings xa
    return .mkApp () fn [x]
  -- Strings
  | .fn _ q`Boogie.str_concat, [xa, ya] =>
     let x ← translateExpr p bindings xa
     let y ← translateExpr p bindings ya
     return .mkApp () Boogie.strConcatOp [x, y]
  | .fn _ q`Boogie.str_substr, [xa, ia, na] =>
     let x ← translateExpr p bindings xa
     let i ← translateExpr p bindings ia
     let n ← translateExpr p bindings na
     return .mkApp () Boogie.strSubstrOp [x, i, n]
  | .fn _ q`Boogie.old, [_tp, xa] =>
     let x ← translateExpr p bindings xa
     return .mkApp () Boogie.polyOldOp [x]
  | .fn _ q`Boogie.map_get, [_ktp, _vtp, ma, ia] =>
     let kty ← translateLMonoTy bindings _ktp
     let vty ← translateLMonoTy bindings _vtp
     -- TODO: use Boogie.mapSelectOp, but specialized
     let fn : LExpr BoogieLParams.mono := (LExpr.op () "select" (.some (LMonoTy.mkArrow (mapTy kty vty) [kty, vty])))
     let m ← translateExpr p bindings ma
     let i ← translateExpr p bindings ia
     return .mkApp () fn [m, i]
  | .fn _ q`Boogie.map_set, [_ktp, _vtp, ma, ia, xa] =>
     let kty ← translateLMonoTy bindings _ktp
     let vty ← translateLMonoTy bindings _vtp
     -- TODO: use Boogie.mapUpdateOp, but specialized
     let fn : LExpr BoogieLParams.mono := (LExpr.op () "update" (.some (LMonoTy.mkArrow (mapTy kty vty) [kty, vty, mapTy kty vty])))
     let m ← translateExpr p bindings ma
     let i ← translateExpr p bindings ia
     let x ← translateExpr p bindings xa
     return .mkApp () fn [m, i, x]
  -- Quantifiers
  | .fn _ q`Boogie.forall, [xsa, ba] =>
    translateQuantifier .all p bindings xsa .none ba
  | .fn _ q`Boogie.exists, [xsa, ba] =>
    translateQuantifier .exist p bindings xsa .none ba
  | .fn _ q`Boogie.forallT, [xsa, tsa, ba] =>
    translateQuantifier .all p bindings xsa (.some tsa) ba
  | .fn _ q`Boogie.existsT, [xsa, tsa, ba] =>
    translateQuantifier .exist p bindings xsa (.some tsa) ba
  -- Binary function applications (monomorphic)
  | .fn _ fni, [xa, ya] =>
    let fn ← translateFn .none fni
    let x ← translateExpr p bindings xa
    let y ← translateExpr p bindings ya
    return .mkApp () fn [x, y]
  | .fn _ q`Boogie.re_loop, [xa, ya, za] =>
    let fn ← translateFn .none q`Boogie.re_loop
    let x ← translateExpr p bindings xa
    let y ← translateExpr p bindings ya
    let z ← translateExpr p bindings za
    return .mkApp () fn [x, y, z]
  -- Binary function applications (polymorphic)
  | .fn _ fni, [tpa, xa, ya] =>
    match fni with
    | q`Boogie.add_expr
    | q`Boogie.sub_expr
    | q`Boogie.mul_expr
    | q`Boogie.div_expr
    | q`Boogie.mod_expr
    | q`Boogie.bvand
    | q`Boogie.bvor
    | q`Boogie.bvxor
    | q`Boogie.bvshl
    | q`Boogie.bvushr
    | q`Boogie.bvsshr
    | q`Boogie.bvsdiv
    | q`Boogie.bvsmod
    | q`Boogie.le
    | q`Boogie.lt
    | q`Boogie.gt
    | q`Boogie.ge
    | q`Boogie.bvsle
    | q`Boogie.bvslt
    | q`Boogie.bvsgt
    | q`Boogie.bvsge =>
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
  | .bvar _ i, [] => do
    if i < bindings.boundVars.size then
      let expr := bindings.boundVars[bindings.boundVars.size - (i+1)]!
      match expr with
      | .bvar m _ => return .bvar m i
      | _ => return expr
    else
      TransM.error s!"translateExpr out-of-range bound variable: {i}"
  | .fvar _ i, [] =>
    assert! i < bindings.freeVars.size
    let decl := bindings.freeVars[i]!
    let ty? ← match p.globalContext.kindOf! i with
              |.expr te => pure (some (← translateLMonoTy bindings (.type te)))
              | _ => pure none
    match decl with
    | .var name _ty _expr _md =>
      -- Global Variable
      return (.fvar () name ty?)
    | .func func _md =>
      -- 0-ary Function
      return (.op () func.name ty?)
    | _ =>
      TransM.error s!"translateExpr unimplemented fvar decl (no args): {format decl}"
  | .fvar _ i, argsa =>
    -- Call of a function declared/defined in Boogie.
    assert! i < bindings.freeVars.size
    let decl := bindings.freeVars[i]!
    match decl with
    | .func func _md =>
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
  TransM (Array Boogie.Expression.Expr) :=
  args.mapM (fun a => translateExpr p bindings a)
end

---------------------------------------------------------------------

def translateInvariant (p : Program) (bindings : TransBindings) (arg : Arg) : TransM (Option Expression.Expr) := do
  match arg with
  | .option _ (.some m) => do
    let args ← checkOpArg m q`Boogie.invariant 1
    translateExpr p bindings args[0]!
  | _ => pure none

def initVarStmts (tpids : ListMap Expression.Ident LTy) (bindings : TransBindings) :
  TransM ((List Boogie.Statement) × TransBindings) := do
  match tpids with
  | [] => return ([], bindings)
  | (id, tp) :: rest =>
    let s := Boogie.Statement.init id tp (Names.initVarValue (id.name ++ "_" ++ (toString bindings.gen.var_def)))
    let bindings := incrNum .var_def bindings
    let (stmts, bindings) ← initVarStmts rest bindings
    return ((s :: stmts), bindings)

def translateVarStatement (bindings : TransBindings) (decls : Array Arg) :
  TransM ((List Boogie.Statement) × TransBindings) := do
  if decls.size != 1 then
    TransM.error s!"translateVarStatement unexpected decls length {repr decls}"
  else
    let tpids ← translateDeclList bindings decls[0]!
    let (stmts, bindings) ← initVarStmts tpids bindings
    let newVars ← tpids.mapM (fun (id, ty) =>
                    if h: ty.isMonoType then
                      return ((LExpr.fvar () id (ty.toMonoType h)): LExpr BoogieLParams.mono)
                    else
                      TransM.error s!"translateVarStatement requires {id} to have a monomorphic type, but it has type {ty}")
    let bbindings := bindings.boundVars ++ newVars
    return (stmts, { bindings with boundVars := bbindings })

def translateInitStatement (p : Program) (bindings : TransBindings) (args : Array Arg) :
  TransM ((List Boogie.Statement) × TransBindings) := do
  if args.size != 3 then
    TransM.error "translateInitStatement unexpected arg length {repr decls}"
  else
    let mty ← translateLMonoTy bindings args[0]!
    let lhs ← translateIdent BoogieIdent args[1]!
    let val ← translateExpr p bindings args[2]!
    let ty := (.forAll [] mty)
    let newBinding: LExpr BoogieLParams.mono := LExpr.fvar () lhs mty
    let bbindings := bindings.boundVars ++ [newBinding]
    return ([.init lhs ty val], { bindings with boundVars := bbindings })

mutual
partial def translateStmt (p : Program) (bindings : TransBindings) (arg : Arg) :
  TransM (List Boogie.Statement × TransBindings) := do
  let .op op := arg
    | TransM.error s!"translateStmt expected op {repr arg}"

  match op.name, op.args with
  | q`Boogie.varStatement, declsa =>
    translateVarStatement bindings declsa
  | q`Boogie.initStatement, args =>
    translateInitStatement p bindings args
  | q`Boogie.assign, #[_tpa, lhsa, ea] =>
    let lhs ← translateLhs lhsa
    let val ← translateExpr p bindings ea
    let md ← getOpMetaData op
    return ([.set lhs val md], bindings)
  | q`Boogie.havoc_statement, #[ida] =>
    let id ← translateIdent BoogieIdent ida
    let md ← getOpMetaData op
    return ([.havoc id md], bindings)
  | q`Boogie.assert, #[la, ca] =>
    let c ← translateExpr p bindings ca
    let default_name := s!"assert_{bindings.gen.assert_def}"
    let bindings := incrNum .assert_def bindings
    let l ← translateOptionLabel default_name la
    let md ← getOpMetaData op
    return ([.assert l c md], bindings)
  | q`Boogie.assume, #[la, ca] =>
    let c ← translateExpr p bindings ca
    let default_name := s!"assume_{bindings.gen.assume_def}"
    let bindings := incrNum .assume_def bindings
    let l ← translateOptionLabel default_name la
    let md ← getOpMetaData op
    return ([.assume l c md], bindings)
  | q`Boogie.if_statement, #[ca, ta, fa] =>
    let c ← translateExpr p bindings ca
    let (tss, bindings) ← translateBlock p bindings ta
    let (fss, bindings) ← translateElse p bindings fa
    let md ← getOpMetaData op
    return ([.ite c tss fss md], bindings)
  | q`Boogie.while_statement, #[ca, ia, ba] =>
    let c ← translateExpr p bindings ca
    let i ← translateInvariant p bindings ia
    let (bodyss, bindings) ← translateBlock p bindings ba
    let md ← getOpMetaData op
    return ([.loop c .none i bodyss md], bindings)
  | q`Boogie.call_statement, #[lsa, fa, esa] =>
    let ls  ← translateCommaSep (translateIdent BoogieIdent) lsa
    let f   ← translateIdent String fa
    let es  ← translateCommaSep (fun a => translateExpr p bindings a) esa
    let md ← getOpMetaData op
    return ([.call ls.toList f es.toList md], bindings)
  | q`Boogie.call_unit_statement, #[fa, esa] =>
    let f   ← translateIdent String fa
    let es  ← translateCommaSep (fun a => translateExpr p bindings a) esa
    let md ← getOpMetaData op
    return ([.call [] f es.toList md], bindings)
  | q`Boogie.block_statement, #[la, ba] =>
    let l ← translateIdent String la
    let (ss, bindings) ← translateBlock p bindings ba
    let md ← getOpMetaData op
    return ([.block l ss md], bindings)
  | q`Boogie.goto_statement, #[la] =>
    let l ← translateIdent String la
    let md ← getOpMetaData op
    return ([.goto l md], bindings)
  | name, args => TransM.error s!"Unexpected statement {name.fullName} with {args.size} arguments."

partial def translateBlock (p : Program) (bindings : TransBindings) (arg : Arg) :
  TransM ((List Boogie.Statement) × TransBindings) := do
  let args ← checkOpArg arg q`Boogie.block 1
  let .seq _ stmts := args[0]!
    | TransM.error s!"Invalid block {repr args[0]!}"
  let (a, bindings) ← stmts.foldlM (init := (#[], bindings)) fun (a, b) s => do
      let (s, b) ← translateStmt p b s
      return (a.append s.toArray, b)
  return (a.toList, bindings)

partial def translateElse (p : Program) (bindings : TransBindings) (arg : Arg) :
  TransM ((List Boogie.Statement) × TransBindings) := do
  let .op op := arg
    | TransM.error s!"translateElse expected op {repr arg}"
  match op.name with
  | q`Boogie.else0 =>
    let _ ← checkOpArg arg q`Boogie.else0 0
    return ([], bindings)
  | q`Boogie.else1 =>
    let args ← checkOpArg arg q`Boogie.else1 1
    translateBlock p bindings args[0]!
  | _ => TransM.error s!"translateElse unimplemented for {repr arg}"

end

---------------------------------------------------------------------

def translateInitMkBinding (bindings : TransBindings) (op : Arg) :
  TransM (BoogieIdent × LMonoTy) := do
  -- (FIXME) Account for metadata.
  let bargs ← checkOpArg op q`Boogie.mkBinding 2
  let id ← translateIdent BoogieIdent bargs[0]!
  let tp ← translateLMonoTy bindings bargs[1]!
  return (id, tp)

def translateInitMkBindings (bindings : TransBindings) (ops : Array Arg) :
  TransM (Array (BoogieIdent × LMonoTy)) := do
  ops.mapM (fun op => translateInitMkBinding bindings op)

def translateBindings (bindings : TransBindings) (op : Arg) :
  TransM (ListMap BoogieIdent LMonoTy) := do
  let bargs ← checkOpArg op q`Boogie.mkBindings 1
  match bargs[0]! with
  | .commaSepList _ args =>
    let arr ← translateInitMkBindings bindings args
    return arr.toList
  | _ =>
    TransM.error s!"translateBindings expects a comma separated list: {repr op}"

def translateModifies (arg : Arg) : TransM BoogieIdent := do
  let args ← checkOpArg arg q`Boogie.modifies_spec 1
  translateIdent BoogieIdent args[0]!

def translateOptionFree (arg : Arg) : TransM Procedure.CheckAttr := do
  let .option _ free := arg
    | TransM.error s!"translateOptionFree unexpected {repr arg}"
  match free with
  | some f =>
    let _ ← checkOpArg f q`Boogie.free 0
    return .Free
  | none => return .Default

def translateRequires (p : Program) (name : BoogieIdent) (count : Nat) (bindings : TransBindings) (arg : Arg) :
  TransM (ListMap BoogieLabel Procedure.Check) := do
  let args ← checkOpArg arg q`Boogie.requires_spec 3
  let l ← translateOptionLabel s!"{name.name}_requires_{count}" args[0]!
  let free? ← translateOptionFree args[1]!
  let e ← translateExpr p bindings args[2]!
  let md ← getArgMetaData arg
  return [(l, { expr := e, attr := free?, md := md })]

def translateEnsures (p : Program) (name : BoogieIdent) (count : Nat) (bindings : TransBindings) (arg : Arg) :
  TransM (ListMap BoogieLabel Procedure.Check) := do
  let args ← checkOpArg arg q`Boogie.ensures_spec 3
  let l ← translateOptionLabel s!"{name.name}_ensures_{count}" args[0]!
  let free? ← translateOptionFree args[1]!
  let e ← translateExpr p bindings args[2]!
  let md ← getArgMetaData arg
  return [(l, { expr := e, attr := free?, md := md })]

def translateSpecElem (p : Program) (name : BoogieIdent) (count : Nat) (bindings : TransBindings) (arg : Arg) :
  TransM (List BoogieIdent × ListMap BoogieLabel Procedure.Check × ListMap BoogieLabel Procedure.Check) := do
  let .op op := arg
    | TransM.error s!"translateSpecElem expects an op {repr arg}"
  match op.name with
  | q`Boogie.modifies_spec =>
    let elem ← translateModifies arg
    return ([elem], [], [])
  | q`Boogie.requires_spec =>
    let elem ← translateRequires p name count bindings arg
    return ([], elem, [])
  | q`Boogie.ensures_spec =>
    let elem ← translateEnsures p name count bindings arg
    return ([], [], elem)
  | _ =>
    TransM.error s!"translateSpecElem unimplemented for {repr arg}"

partial def translateSpec (p : Program) (name : BoogieIdent) (bindings : TransBindings) (arg : Arg) :
  TransM (List BoogieIdent × ListMap BoogieLabel Procedure.Check × ListMap BoogieLabel Procedure.Check) := do
  let sargs ← checkOpArg arg q`Boogie.spec_mk 1
  let .seq _ args := sargs[0]!
    | TransM.error s!"Invalid specs {repr sargs[0]!}"
  go 0 args.size args
  where go (count max : Nat) (args : Array Arg) := do
  match (max - count) with
  | 0 => return ([], [], [])
  | _ + 1 =>
    let arg := args[count]!
    let (mods, reqs, ens) ← translateSpecElem p name count bindings arg
    let (restmods, restreqs, restens) ← go (count + 1) max args
    return (mods ++ restmods, reqs ++ restreqs, ens ++ restens)

def translateProcedure (p : Program) (bindings : TransBindings) (op : Operation) :
  TransM (Boogie.Decl × TransBindings) := do
  let _ ← @checkOp (Boogie.Decl × TransBindings) op q`Boogie.command_procedure 6
  let pname ← translateIdent BoogieIdent op.args[0]!
  let typeArgs ← translateTypeArgs op.args[1]!
  let sig ← translateBindings bindings op.args[2]!
  let ret ← translateOptionMonoDeclList bindings op.args[3]!
  let in_bindings := (sig.map (fun (v, ty) => (LExpr.fvar () v ty))).toArray
  let out_bindings := (ret.map (fun (v, ty) => (LExpr.fvar () v ty))).toArray
  -- This bindings order -- original, then inputs, and then outputs, is
  -- critical here. Is this right though?
  let origBindings := bindings
  let bbindings := bindings.boundVars ++ in_bindings ++ out_bindings
  let bindings := { bindings with boundVars := bbindings }
  let .option _ speca := op.args[4]!
    | TransM.error s!"translateProcedure spec. expected here: {repr op.args[3]!}"
  let (modifies, requires, ensures) ←
    if speca.isSome then translateSpec p pname bindings speca.get! else pure ([], [], [])
  let .option _ bodya := op.args[5]!
    | TransM.error s!"translateProcedure body expected here: {repr op.args[4]!}"
  let (body, bindings) ← if bodya.isSome then translateBlock p bindings bodya.get! else pure ([], bindings)
  let origBindings := { origBindings with gen := bindings.gen }
  let md ← getOpMetaData op
  return (.proc { header := { name := pname,
                              typeArgs := typeArgs.toList,
                              inputs := sig,
                              outputs := ret },
                  spec := { modifies := modifies,
                            preconditions := requires,
                            postconditions := ensures },
                  body := body
                }
                md,
          origBindings)

---------------------------------------------------------------------

def translateConstant (bindings : TransBindings) (op : Operation) :
  TransM (Boogie.Decl × TransBindings) := do
  let _ ← @checkOp (Boogie.Decl × TransBindings) op q`Boogie.command_constdecl 3
  let cname ← translateIdent BoogieIdent op.args[0]!
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
  TransM (Boogie.Decl × TransBindings) := do
  let _ ← @checkOp (Boogie.Decl × TransBindings) op q`Boogie.command_axiom 2
  let default_name := s!"axiom_{bindings.gen.axiom_def}"
  let bindings := incrNum .axiom_def bindings
  let l ← translateOptionLabel default_name op.args[0]!
  let e ← translateExpr p bindings op.args[1]!
  let md ← getOpMetaData op
  return (.ax (Axiom.mk l e) md, bindings)

def translateDistinct (p : Program) (bindings : TransBindings) (op : Operation) :
  TransM (Boogie.Decl × TransBindings) := do
  let _ ← @checkOp (Boogie.Decl × TransBindings) op q`Boogie.command_distinct 2
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

def translateOptionInline (arg : Arg) : TransM (Array String) := do
  -- (FIXME) The return type should be the same as that of `LFunc.attr`, which is
  -- `Array String` but of course, this is not ideal. We'd like an inductive
  -- type here of the allowed attributes in the future.
  let .option _ inline := arg
    | TransM.error s!"translateOptionInline unexpected {repr arg}"
  match inline with
  | some f =>
    let _ ← checkOpArg f q`Boogie.inline 0
    return #["inline"]
  | none => return #[]

def translateFunction (status : FnInterp) (p : Program) (bindings : TransBindings) (op : Operation) :
  TransM (Boogie.Decl × TransBindings) := do
  let _ ←
    match status with
    | .Definition  => @checkOp (Boogie.Decl × TransBindings) op q`Boogie.command_fndef  6
    | .Declaration => @checkOp (Boogie.Decl × TransBindings) op q`Boogie.command_fndecl 4
  let fname ← translateIdent BoogieIdent op.args[0]!
  let typeArgs ← translateTypeArgs op.args[1]!
  let sig ← translateBindings bindings op.args[2]!
  let ret ← translateLMonoTy bindings op.args[3]!
  let in_bindings := (sig.map (fun (v, ty) => (LExpr.fvar () v ty))).toArray
  -- This bindings order -- original, then inputs, is
  -- critical here. Is this right though?
  let orig_bbindings := bindings.boundVars
  let bbindings := bindings.boundVars ++ in_bindings
  let bindings := { bindings with boundVars := bbindings }
  let body ← match status with
             | .Definition =>
                let e ← translateExpr p bindings op.args[4]!
                pure (some e)
             | .Declaration => pure none
  let inline? ← match status with
                 | .Definition => translateOptionInline op.args[5]!
                 | .Declaration => pure #[]
  let md ← getOpMetaData op
  let decl := .func { name := fname,
                      typeArgs := typeArgs.toList,
                      inputs := sig,
                      output := ret,
                      body := body,
                      attr := inline? } md
  return (decl,
          { bindings with
            boundVars := orig_bbindings,
            freeVars := bindings.freeVars.push decl })

---------------------------------------------------------------------

/--
Information about a single constructor extracted during translation.
This is the Boogie-specific version of `ConstructorInfo` from AST.lean,
with types translated from `TypeExpr` to `LMonoTy`.
-/
structure TransConstructorInfo where
  /-- Constructor name -/
  name : BoogieIdent
  /-- Fields as (fieldName, fieldType) pairs with translated types -/
  fields : Array (BoogieIdent × LMonoTy)
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
  let constructorInfos := GlobalContext.extractConstructorInfo p.dialects arg
  constructorInfos.mapM (translateConstructorInfo bindings)

/--
Translate a datatype declaration to Boogie declarations, updating bindings
appropriately.

**Important:** The returned `Boogie.Decls` only contains the type declaration
itself. Factory functions (constructors, testers, destructors) are generated
automatically by `Env.addDatatypes` during program evaluation to avoid
duplicates.

**Parameters:**
- `p`: The DDM Program (provides dialect map)
- `bindings`: Current translation bindings
- `op`: The `command_datatype` operation to translate
-/
def translateDatatype (p : Program) (bindings : TransBindings) (op : Operation) :
    TransM (Boogie.Decls × TransBindings) := do
  -- Check operation has correct name and argument count
  let _ ← @checkOp (Boogie.Decls × TransBindings) op q`Boogie.command_datatype 3

  let datatypeName ← translateIdent String op.args[0]!

  -- Extract type arguments (optional bindings)
  let (typeArgs, bindings) ←
    translateOption
      (fun maybearg =>
            do match maybearg with
            | none => pure ([], bindings)
            | some arg =>
              let bargs ← checkOpArg arg q`Boogie.mkBindings 1
              let args ←
                  match bargs[0]! with
                  | .commaSepList _ args =>
                    let (arr, bindings) ← translateTypeBindings bindings args
                    return (arr.toList, bindings)
                  | _ => TransM.error
                          s!"translateDatatype expects a comma separated list: {repr bargs[0]!}")
                    op.args[1]!

  /- Note: Add a placeholder for the datatype type BEFORE translating
  constructors, for recursive constructors. Replaced with actual declaration
  later. -/
  let placeholderLDatatype : LDatatype Visibility :=
    { name := datatypeName
      typeArgs := typeArgs
      constrs := [{ name := datatypeName, args := [], testerName := "" }]
      constrs_ne := by simp }
  let placeholderDecl := Boogie.Decl.type (.data placeholderLDatatype)
  let bindingsWithPlaceholder := { bindings with freeVars := bindings.freeVars.push placeholderDecl }

  -- Extract constructor information (possibly recursive)
  let constructors ← translateConstructorList p bindingsWithPlaceholder op.args[2]!

  if h : constructors.size == 0 then
    TransM.error s!"Datatype {datatypeName} must have at least one constructor"
  else
    -- Build LConstr list from TransConstructorInfo
    let testerPattern : Array NamePatternPart := #[.datatype, .literal "..is", .constructor]
    let lConstrs : List (LConstr Visibility) := constructors.toList.map fun constr =>
      let testerName := expandNamePattern testerPattern datatypeName (some constr.name.name)
      { name := constr.name
        args := constr.fields.toList.map fun (fieldName, fieldType) => (fieldName, fieldType)
        testerName := testerName }

    have constrs_ne : lConstrs.length != 0 := by
      simp [lConstrs]
      intro heq; subst_vars; apply h; rfl

    let ldatatype : LDatatype Visibility :=
      { name := datatypeName
        typeArgs := typeArgs
        constrs := lConstrs
        constrs_ne := constrs_ne }

    -- Generate factory from LDatatype and convert to Boogie.Decl
    -- (used only for bindings.freeVars, not for allDecls)
    let factory ← match ldatatype.genFactory (T := BoogieLParams) with
      | .ok f => pure f
      | .error e => TransM.error s!"Failed to generate datatype factory: {e}"
    let funcDecls : List Boogie.Decl := factory.toList.map fun func =>
      Boogie.Decl.func func

    -- Only includes typeDecl, factory functions generated later
    let typeDecl := Boogie.Decl.type (.data ldatatype)
    let allDecls := [typeDecl]

    /-
    We must add to bindings.freeVars in the same order as the DDM's
    `addDatatypeBindings`: type, constructors, template functions. We do NOT
    include eliminators here because the DDM does not (yet) produce them.
    -/

    let constructorNames : List String := lConstrs.map fun c => c.name.name
    let testerNames : List String := lConstrs.map fun c => c.testerName

    -- Extract all field names across all constructors for field projections
    -- Note: DDM validates that field names are unique across constructors
    let fieldNames : List String := lConstrs.foldl (fun acc c =>
      acc ++ (c.args.map fun (fieldName, _) => fieldName.name)) []

    -- Filter factory functions to get constructors, testers, projections
    -- TODO: this could be more efficient via `LDatatype.genFunctionMaps`
    let constructorDecls := funcDecls.filter fun decl =>
      match decl with
      | .func f => constructorNames.contains f.name.name
      | _ => false

    let testerDecls := funcDecls.filter fun decl =>
      match decl with
      | .func f => testerNames.contains f.name.name
      | _ => false

    let fieldAccessorDecls := funcDecls.filter fun decl =>
      match decl with
      | .func f => fieldNames.contains f.name.name
      | _ => false

    let bindingDecls := typeDecl :: constructorDecls ++ testerDecls ++ fieldAccessorDecls
    let bindings := bindingDecls.foldl (fun b d =>
      { b with freeVars := b.freeVars.push d }
    ) bindings

    return (allDecls, bindings)

---------------------------------------------------------------------

def translateGlobalVar (bindings : TransBindings) (op : Operation) :
  TransM (Boogie.Decl × TransBindings) := do
  let _ ← @checkOp (Boogie.Decl × TransBindings) op q`Boogie.command_var 1
  let (id, targs, mty) ← translateBindMk bindings op.args[0]!
  let ty := LTy.forAll targs mty
  let md ← getOpMetaData op
  let decl := (.var id ty (Names.initVarValue (id.name ++ "_" ++ (toString bindings.gen.var_def))) md)
  let bindings := incrNum .var_def bindings
  return (decl, { bindings with freeVars := bindings.freeVars.push decl})

---------------------------------------------------------------------

partial def translateBoogieDecls (p : Program) (bindings : TransBindings) :
  TransM Boogie.Decls := do
  let (decls, _) ← go 0 p.commands.size bindings p.commands
  return decls
  where go (count max : Nat) bindings ops : TransM (Boogie.Decls × TransBindings) := do
  match (max - count) with
  | 0 => return ([], bindings)
  | _ + 1 =>
    let op := ops[count]!
    -- Commands that produce multiple declarations
    let (newDecls, bindings) ←
      match op.name with
      | q`Boogie.command_datatype =>
        translateDatatype p bindings op
      | _ =>
        -- All other commands produce a single declaration
        let (decl, bindings) ←
          match op.name with
          | q`Boogie.command_var =>
            translateGlobalVar bindings op
          | q`Boogie.command_constdecl =>
            translateConstant bindings op
          | q`Boogie.command_typedecl =>
            translateTypeDecl bindings op
          | q`Boogie.command_typesynonym =>
            translateTypeSynonym bindings op
          | q`Boogie.command_axiom =>
            translateAxiom p bindings op
          | q`Boogie.command_distinct =>
            translateDistinct p bindings op
          | q`Boogie.command_procedure =>
            translateProcedure p bindings op
          | q`Boogie.command_fndef =>
            translateFunction .Definition p bindings op
          | q`Boogie.command_fndecl =>
            translateFunction .Declaration p bindings op
          | _ => TransM.error s!"translateBoogieDecls unimplemented for {repr op}"
        pure ([decl], bindings)
    let (decls, bindings) ← go (count + 1) max bindings ops
    return (newDecls ++ decls, bindings)

def translateProgram (p : Program) : TransM Boogie.Program := do
  let decls ← translateBoogieDecls p {}
  return { decls := decls }

---------------------------------------------------------------------

end Strata
