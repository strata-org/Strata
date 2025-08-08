/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.DDMTransform.Parse
import Strata.Languages.Boogie.Names


---------------------------------------------------------------------
namespace Strata

/- Translating concrete syntax into abstract syntax -/

open Boogie Lambda Imperative
open Std (ToFormat Format format)

---------------------------------------------------------------------

/- Translation Monad -/

structure TransState where
  errors : Array String

def TransM := StateM TransState
  deriving Monad

def TransM.run (m : TransM α) : (α × Array String) :=
  let (v, s) := StateT.run m { errors := #[] }
  (v, s.errors)

instance : ToString (Boogie.Program × Array String) where
  toString p := toString (Std.format p.fst) ++ "\n" ++
                "Errors: " ++ (toString p.snd)

def TransM.error [Inhabited α] (msg : String) : TransM α := do
  fun s => ((), { errors := s.errors.push msg })
  return panic msg

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
  let .commaSepList args := arg
    | TransM.error s!"Expected commaSepList: {repr arg}"
  args.mapM f

def translateOption [Inhabited α] (f : Option Strata.Arg → TransM α) (arg : Arg) :
  TransM α := do
  let .option maybe_arg := arg
    | TransM.error s!"Expected Option: {repr arg}"
  f maybe_arg

---------------------------------------------------------------------

def translateIdent (Identifier : Type) [Coe String Identifier] [Inhabited Identifier]
  (arg : Strata.Arg) : TransM Identifier := do
  let .ident name := arg
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
  let .num n := arg
    | TransM.error s!"translateNat expects num lit"
  return n

def translateStr (arg : Arg) : TransM String := do
  let .strlit s := arg
    | TransM.error s!"translateStr expects string lit"
  return s

def translateReal (arg : Arg) : TransM Decimal := do
  let .decimal d := arg
    | TransM.error s!"translateReal expects decimal lit"
  return d

---------------------------------------------------------------------

structure TransBindings where
  boundTypeVars : Array TyIdentifier := #[]
  boundVars : Array (LExpr BoogieIdent) := #[]
  freeVars  : Array Boogie.Decl := #[]
  gen : Nat := 0

def incrGen (b : TransBindings) : TransBindings :=
  { b with gen := b.gen + 1 }

instance : ToFormat TransBindings where
  format b := f!"BoundTypeVars: {b.boundTypeVars}\
                {Format.line}\
                BoundVars: {b.boundVars}\
                {Format.line}\
                FreeVars: {b.freeVars}\
                {Format.line}\
                Gen: {b.gen}"

instance : Inhabited (List Boogie.Statement × TransBindings) where
  default := ([], {})

instance : Inhabited Boogie.Decl where
  default := .var "badguy" (.forAll [] (.tcons "bool" [])) (.const "false" none)

instance : Inhabited (Procedure.CheckAttr) where
  default := .Default

instance : Inhabited (Boogie.Decl × TransBindings) where
  default := (.var "badguy" (.forAll [] (.tcons "bool" [])) (.const "false" none), {})

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
  | .ident q`Boogie.bv1 #[] => pure <| .bitvec 1
  | .ident q`Boogie.bv8 #[] => pure <| .bitvec 8
  | .ident q`Boogie.bv16 #[] => pure <| .bitvec 16
  | .ident q`Boogie.bv32 #[] => pure <| .bitvec 32
  | .ident q`Boogie.bv64 #[] => pure <| .bitvec 64
  | .ident i argst =>
      let argst' ← translateLMonoTys bindings (argst.map Arg.type)
      pure <| (.tcons i.name argst'.toList.reverse)
  | .fvar i argst =>
    assert! i < bindings.freeVars.size
    let decl := bindings.freeVars[i]!
    let ty_core ← match decl with
                  | .type (.con tcons) =>
                    -- Type Declaration
                    let ty := tcons.toType
                    -- While the "unsafe" below looks scary, we should be alright as far as
                    -- Boogie is concerned. See `Boogie.TypeConstructor`, where there is no
                    -- facility for providing the type arguments.
                    pure ty.toMonoTypeUnsafe
                  | .type (.syn syn) =>
                    let ty := syn.toLHSLMonoTy
                    pure ty
                  | _ =>
                    TransM.error
                      s!"translateLMonoTy not yet implemented for this declaration: \
                         {format decl}\n\
                         ty: {repr tp} bindings: {format bindings}"
    match argst with
    | #[] => return ty_core
    | _ =>
      let argst' ← translateLMonoTys bindings (argst.map Arg.type)
      match ty_core with
      -- (TODO) Is ignoring the args of `.tcons` safe here?
      | .tcons name _ => return (.tcons name argst'.toList.reverse)
      | _ => TransM.error s!"translateLMonoTy not yet implemented {repr tp}"
  | .bvar i =>
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
                  | .commaSepList args =>
                    let (arr, bindings) ← translateTypeBindings bindings args
                    return (arr.toList, bindings)
                  | _ => TransM.error
                          s!"translateTypeSynonym expects a comma separated list: {repr bargs[0]!}")
                    op.args[1]!
  -- TODO: get type args from op.args[2]
  -- let qtargs ← translateTypeArgs op.args[2]!
  let typedef ← translateLMonoTy bindings op.args[3]!
  let decl := Boogie.Decl.type (.syn { name := name, typeArgs := targs, type := typedef })
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
                  | .commaSepList args => pure args.size
                  | _ => TransM.error
                          s!"translateTypeDecl expects a comma separated list: {repr bargs[0]!}")
                    op.args[1]!
  -- Only the number of type arguments is important; the exact identifiers are
  -- irrelevant.
  let decl := Boogie.Decl.type (.con { name := name, numargs := numargs })
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
  TransM (Map Expression.Ident LTy) := do
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
    let lty := .forAll targs mty
    pure (fst ++ [(id, lty)])
  | _ => TransM.error s!"translateDeclList unimplemented for {repr op}"

partial def translateMonoDeclList (bindings : TransBindings) (arg : Arg) :
  TransM (Map Expression.Ident LMonoTy) := do
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
    pure (fst ++ [(id, mty)])
  | _ => TransM.error s!"translateMonoDeclList unimplemented for {repr op}"

def translateOptionMonoDeclList (bindings : TransBindings) (arg : Arg) :
  TransM (Map Expression.Ident LMonoTy) :=
  translateOption
    (fun maybedecls => do match maybedecls with
        | none => return []
        | some decls => translateMonoDeclList bindings decls)
    arg
---------------------------------------------------------------------

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

  | .some .bv1, q`Boogie.le       => return bv1LeOp
  | .some .bv1, q`Boogie.lt       => return bv1LtOp
  | .some .bv1, q`Boogie.ge       => return bv1GeOp
  | .some .bv1, q`Boogie.gt       => return bv1GtOp
  | .some .bv1, q`Boogie.add_expr => return bv1AddOp
  | .some .bv1, q`Boogie.sub_expr => return bv1SubOp
  | .some .bv1, q`Boogie.mul_expr => return bv1MulOp
  | .some .bv1, q`Boogie.neg_expr => return bv1NegOp

  | .some .bv8, q`Boogie.le       => return bv8LeOp
  | .some .bv8, q`Boogie.lt       => return bv8LtOp
  | .some .bv8, q`Boogie.ge       => return bv8GeOp
  | .some .bv8, q`Boogie.gt       => return bv8GtOp
  | .some .bv8, q`Boogie.add_expr => return bv8AddOp
  | .some .bv8, q`Boogie.sub_expr => return bv8SubOp
  | .some .bv8, q`Boogie.mul_expr => return bv8MulOp
  | .some .bv8, q`Boogie.neg_expr => return bv8NegOp

  | .some .bv16, q`Boogie.le       => return bv16LeOp
  | .some .bv16, q`Boogie.lt       => return bv16LtOp
  | .some .bv16, q`Boogie.ge       => return bv16GeOp
  | .some .bv16, q`Boogie.gt       => return bv16GtOp
  | .some .bv16, q`Boogie.add_expr => return bv16AddOp
  | .some .bv16, q`Boogie.sub_expr => return bv16SubOp
  | .some .bv16, q`Boogie.mul_expr => return bv16MulOp
  | .some .bv16, q`Boogie.neg_expr => return bv16NegOp

  | .some .bv32, q`Boogie.le       => return bv32LeOp
  | .some .bv32, q`Boogie.lt       => return bv32LtOp
  | .some .bv32, q`Boogie.ge       => return bv32GeOp
  | .some .bv32, q`Boogie.gt       => return bv32GtOp
  | .some .bv32, q`Boogie.add_expr => return bv32AddOp
  | .some .bv32, q`Boogie.sub_expr => return bv32SubOp
  | .some .bv32, q`Boogie.mul_expr => return bv32MulOp
  | .some .bv32, q`Boogie.neg_expr => return bv32NegOp

  | .some .bv64, q`Boogie.le       => return bv64LeOp
  | .some .bv64, q`Boogie.lt       => return bv64LtOp
  | .some .bv64, q`Boogie.ge       => return bv64GeOp
  | .some .bv64, q`Boogie.gt       => return bv64GtOp
  | .some .bv64, q`Boogie.add_expr => return bv64AddOp
  | .some .bv64, q`Boogie.sub_expr => return bv64SubOp
  | .some .bv64, q`Boogie.mul_expr => return bv64MulOp
  | .some .bv64, q`Boogie.neg_expr => return bv64NegOp

  | _, q`Boogie.old      => return polyOldOp
  | _, _              => TransM.error s!"translateFn: Unknown/unimplemented function {repr q} at type {repr ty?}"

mutual

partial
def translateQuantifier
  (qk: QuantifierKind)
  -- TODO: don't ignore triggers
  (bindings : TransBindings) (xsa : Arg) (_triggersa: Option Arg) (bodya: Arg) :
  TransM Boogie.Expression.Expr := do
    let xsArray ← translateDeclList bindings xsa
    -- Note: the indices in the following are placeholders
    let newBoundVars := List.toArray (xsArray.mapIdx (fun i _ => LExpr.bvar i))
    let boundVars' := bindings.boundVars ++ newBoundVars
    let xbindings := { bindings with boundVars := boundVars' }
    let b ← translateExpr xbindings bodya
    -- Create one quantifier constructor per variable
    return xsArray.foldr (fun (_, ty) e =>
      match ty with
      | .forAll [] mty =>
        .quant qk (.some mty) e
      | _ => panic! s!"Expected monomorphic type in quantifier, got: {ty}") b

partial def translateExpr (bindings : TransBindings) (arg : Arg) :
  TransM Boogie.Expression.Expr := do
  let .expr expr := arg
    | TransM.error s!"translateExpr expected expr {repr arg}"
  let (op, args) := expr.flatten
  match op, args with
  -- Constants/Literals
  | .fn q`Boogie.btrue, [] =>
    return .const "true" Lambda.LMonoTy.bool
  | .fn q`Boogie.bfalse, [] =>
    return .const "false" Lambda.LMonoTy.bool
  | .fn q`Boogie.natToInt, [xa] =>
    let n ← translateNat xa
    return .const (toString n) Lambda.LMonoTy.int
  | .fn q`Boogie.bv1Lit, [xa] =>
    let n ← translateNat xa
    return .const (toString n) Lambda.LMonoTy.bv1
  | .fn q`Boogie.bv8Lit, [xa] =>
    let n ← translateNat xa
    return .const (toString n) Lambda.LMonoTy.bv8
  | .fn q`Boogie.bv16Lit, [xa] =>
    let n ← translateNat xa
    return .const (toString n) Lambda.LMonoTy.bv16
  | .fn q`Boogie.bv32Lit, [xa] =>
    let n ← translateNat xa
    return .const (toString n) Lambda.LMonoTy.bv32
  | .fn q`Boogie.bv64Lit, [xa] =>
    let n ← translateNat xa
    return .const (toString n) Lambda.LMonoTy.bv64
  | .fn q`Boogie.strLit, [xa] =>
    let x ← translateStr xa
    return .const x Lambda.LMonoTy.string
  | .fn q`Boogie.realLit, [xa] =>
    let x ← translateReal xa
    return .const (toString x) Lambda.LMonoTy.real
  -- Equality
  | .fn q`Boogie.equal, [_tpa, xa, ya] =>
    let x ← translateExpr bindings xa
    let y ← translateExpr bindings ya
    return .eq x y
  | .fn q`Boogie.not_equal, [_tpa, xa, ya] =>
    let x ← translateExpr bindings xa
    let y ← translateExpr bindings ya
    let fn : LExpr BoogieIdent := (LExpr.op (.unres "Bool.Not") none)
    return (.app fn (.eq x y))
  -- If-then-else expression
  | .fn q`Boogie.if, [_tpa, ca, ta, fa] =>
    let c ← translateExpr bindings ca
    let t ← translateExpr bindings ta
    let f ← translateExpr bindings fa
    return .ite c t f
  -- Unary function applications
  | .fn q`Boogie.not, [xa] =>
    let fn : LExpr BoogieIdent := (LExpr.op (.unres "Bool.Not") none)
    let x ← translateExpr bindings xa
    return .mkApp fn [x]
  | .fn q`Boogie.neg_expr, [_ta, xa] =>
    let fn : LExpr BoogieIdent := (LExpr.op (.unres "Int.Neg") none)
    let x ← translateExpr bindings xa
    return .mkApp fn [x]
  -- Strings
  | .fn q`Boogie.str_len, [xa] =>
     let fn : LExpr BoogieIdent := (LExpr.op "Str.Length" none)
     let x ← translateExpr bindings xa
     return .mkApp fn [x]
  | .fn q`Boogie.str_concat, [xa, ya] =>
     let fn : LExpr BoogieIdent := (LExpr.op "Str.Concat" none)
     let x ← translateExpr bindings xa
     let y ← translateExpr bindings ya
     return .mkApp fn [x, y]
  | .fn q`Boogie.old, [_tp, xa] =>
     let fn : LExpr BoogieIdent := (LExpr.op (.unres "old") none)
     let x ← translateExpr bindings xa
     return .mkApp fn [x]
  | .fn q`Boogie.map_get, [_ktp, _vtp, ma, ia] =>
     let kty ← translateLMonoTy bindings _ktp
     let vty ← translateLMonoTy bindings _vtp
     let fn : LExpr BoogieIdent := (LExpr.op "select" (.some (LMonoTy.mkArrow (mapTy kty vty) [kty, vty])))
     let m ← translateExpr bindings ma
     let i ← translateExpr bindings ia
     return .mkApp fn [m, i]
  | .fn q`Boogie.map_set, [_ktp, _vtp, ma, ia, xa] =>
     let kty ← translateLMonoTy bindings _ktp
     let vty ← translateLMonoTy bindings _vtp
     let fn : LExpr BoogieIdent := (LExpr.op "update" (.some (LMonoTy.mkArrow (mapTy kty vty) [kty, vty, mapTy kty vty])))
     let m ← translateExpr bindings ma
     let i ← translateExpr bindings ia
     let x ← translateExpr bindings xa
     return .mkApp fn [m, i, x]
  -- Quantifiers
  | .fn q`Boogie.forall, [xsa, ba] =>
    translateQuantifier .all bindings xsa .none ba
  | .fn q`Boogie.exists, [xsa, ba] =>
    translateQuantifier .exist bindings xsa .none ba
  | .fn q`Boogie.forallT, [xsa, tsa, ba] =>
    translateQuantifier .all bindings xsa (.some tsa) ba
  | .fn q`Boogie.existsT, [xsa, tsa, ba] =>
    translateQuantifier .exist bindings xsa (.some tsa) ba
  -- Binary function applications
  | .fn fni, [xa, ya] =>
    let fn ← translateFn .none fni
    let x ← translateExpr bindings xa
    let y ← translateExpr bindings ya
    return .mkApp fn [x, y]
  | .fn fni, [tpa, xa, ya] =>
    match fni with
    | q`Boogie.add_expr
    | q`Boogie.sub_expr
    | q`Boogie.mul_expr
    | q`Boogie.div_expr
    | q`Boogie.le
    | q`Boogie.lt
    | q`Boogie.gt
    | q`Boogie.ge =>
      let ty ← translateLMonoTy bindings tpa
      if ¬ isArithTy ty then
        TransM.error s!"translateExpr unexpected type for {repr fni}: {repr args}"
      else
        let fn ← translateFn (.some ty) fni
        let x ← translateExpr bindings xa
        let y ← translateExpr bindings ya
        return .mkApp fn [x, y]
    | _ => TransM.error s!"translateExpr unimplemented {repr op} {repr args}"
  -- NOTE: Bound and free variables are numbered differently. Bound variables
  -- ascending order (so closer to deBrujin levels).
  | .bvar i, [] => do
    if i < bindings.boundVars.size then
      let expr := bindings.boundVars[bindings.boundVars.size - (i+1)]!
      match expr with
      | .bvar _ => return .bvar i
      | _ => return expr
    else
      TransM.error s!"translateExpr out-of-range bound variable: {i}"
  | .fvar i, [] =>
    assert! i < bindings.freeVars.size
    let decl := bindings.freeVars[i]!
    match decl with
    | .var name _ty _expr =>
      -- Global Variable
      return (.fvar name none)
    | .func func =>
      -- 0-ary Function
      return (.op func.name none)
    | _ =>
      TransM.error s!"translateExpr unimplemented fvar decl: {format decl}"
  | .fvar i, argsa =>
    -- Call of a function declared/defined in Boogie.
    assert! i < bindings.freeVars.size
    let decl := bindings.freeVars[i]!
    match decl with
    | .func func =>
      let args ← translateExprs bindings argsa.toArray
      return .mkApp (.op func.name none) args.toList
    | _ =>
     TransM.error s!"translateExpr unimplemented fvar decl: {format decl}"
  | op, args =>
    TransM.error s!"translateExpr unimplemented op:\n\
                     Op: {repr op}\n\
                     Args: {repr args}\n\
                     Bindings: {format bindings}}"

partial def translateExprs (bindings : TransBindings) (args : Array Arg) :
  TransM (Array Boogie.Expression.Expr) :=
  args.mapM (fun a => translateExpr bindings a)
end

---------------------------------------------------------------------

def translateInvariant (bindings : TransBindings) (arg : Arg) : TransM (Option Expression.Expr) := do
  match arg with
  | .option (.some m) => do
    let args ← checkOpArg m q`Boogie.invariant 1
    translateExpr bindings args[0]!
  | _ => pure none

def translateMeasure (bindings : TransBindings) (arg : Arg) : TransM (Option Expression.Expr) := do
  match arg with
  | .option (.some m) => do
    let args ← checkOpArg m q`Boogie.measure 1
    translateExpr bindings args[0]!
  | _ => pure none

def initVarStmts (tpids : Map Expression.Ident LTy) (bindings : TransBindings) :
  TransM ((List Boogie.Statement) × TransBindings) := do
  match tpids with
  | [] => return ([], bindings)
  | (id, tp) :: rest =>
    let s := Boogie.Statement.init id tp (Names.initVarValue id ("_" ++ (toString bindings.gen)))
    let bindings := incrGen bindings
    let (stmts, bindings) ← initVarStmts rest bindings
    return ((s :: stmts), bindings)

def translateVarStatement (bindings : TransBindings) (decls : Array Arg) :
  TransM ((List Boogie.Statement) × TransBindings) := do
  if decls.size != 1 then
    TransM.error "translateVarStatement unexpected decls length {repr decls}"
  else
    let tpids ← translateDeclList bindings decls[0]!
    let (stmts, bindings) ← initVarStmts tpids bindings
    let bbindings := bindings.boundVars ++
                     tpids.map (fun (id, _) => (LExpr.fvar id none))
    return (stmts, { bindings with boundVars := bbindings })

def translateInitStatement (bindings : TransBindings) (args : Array Arg) :
  TransM ((List Boogie.Statement) × TransBindings) := do
  if args.size != 3 then
    TransM.error "translateInitStatement unexpected arg length {repr decls}"
  else
    let mty ← translateLMonoTy bindings args[0]!
    let lhs ← translateIdent BoogieIdent args[1]!
    let val ← translateExpr bindings args[2]!
    let ty := (.forAll [] mty)
    let bbindings := bindings.boundVars ++ [LExpr.fvar lhs none]
    return ([.init lhs ty val], { bindings with boundVars := bbindings })

mutual
partial def translateStmt (bindings : TransBindings) (arg : Arg) :
  TransM (List Boogie.Statement × TransBindings) := do
  let .op op := arg
    | TransM.error s!"translateStmt expected op {repr arg}"

  match op.name, op.args with
  | q`Boogie.varStatement, declsa =>
    translateVarStatement bindings declsa
  | q`Boogie.initStatement, args =>
    translateInitStatement bindings args
  | q`Boogie.assign, #[_tpa, lhsa, ea] =>
    let lhs ← translateLhs lhsa
    let val ← translateExpr bindings ea
    return ([.set lhs val], bindings)
  | q`Boogie.havoc_statement, #[ida] =>
    let id ← translateIdent BoogieIdent ida
    return ([.havoc id], bindings)
  | q`Boogie.assert, #[la, ca] =>
    let c ← translateExpr bindings ca
    let l ← translateOptionLabel s!"assert: {Std.format c}" la
    return ([.assert l c], bindings)
  | q`Boogie.assume, #[la, ca] =>
    let c ← translateExpr bindings ca
    let l ← translateOptionLabel s!"assume: {Std.format c}" la
    return ([.assume l c], bindings)
  | q`Boogie.if_statement, #[ca, ta, fa] =>
    let c ← translateExpr bindings ca
    let (tss, bindings) ← translateBlock bindings ta
    let (fss, bindings) ← translateElse bindings fa
    return ([.ite c { ss := tss } { ss := fss } ], bindings)
  | q`Boogie.while_statement, #[ca, ma, ia, ba] =>
    let c ← translateExpr bindings ca
    let m ← translateMeasure bindings ma
    let i ← translateInvariant bindings ia
    let (bodyss, bindings) ← translateBlock bindings ba
    return ([.loop c m i { ss := bodyss } ], bindings)
  | q`Boogie.call_statement, #[lsa, fa, esa] =>
   let ls  ← translateCommaSep (translateIdent BoogieIdent) lsa
   let f   ← translateIdent String fa
   let es  ← translateCommaSep (fun a => translateExpr bindings a) esa
   return ([.call ls.toList f es.toList], bindings)
  | q`Boogie.call_unit_statement, #[fa, esa] =>
   let f   ← translateIdent String fa
   let es  ← translateCommaSep (fun a => translateExpr bindings a) esa
   return ([.call [] f es.toList], bindings)
  | q`Boogie.block_statement, #[la, ba] =>
    let l ← translateIdent String la
    let (ss, bindings) ← translateBlock bindings ba
    return ([.block l { ss := ss }], bindings)
  | q`Boogie.goto_statement, #[la] =>
    let l ← translateIdent String la
    return ([.goto l], bindings)
  | name, args => TransM.error s!"Unexpected statement {name.fullName} with {args.size} arguments."

partial def translateBlock (bindings : TransBindings) (arg : Arg) :
  TransM ((List Boogie.Statement) × TransBindings) := do
  let args ← checkOpArg arg q`Boogie.block 1
  let .seq stmts := args[0]!
    | TransM.error s!"Invalid block {repr args[0]!}"
  let (a, bindings) ← stmts.foldlM (init := (#[], bindings)) fun (a, b) s => do
      let (s, b) ← translateStmt b s
      return (a.append s.toArray, b)
  return (a.toList, bindings)

partial def translateElse (bindings : TransBindings) (arg : Arg) :
  TransM ((List Boogie.Statement) × TransBindings) := do
  let .op op := arg
    | TransM.error s!"translateElse expected op {repr arg}"
  match op.name with
  | q`Boogie.else0 =>
    let _ ← checkOpArg arg q`Boogie.else0 0
    return ([], bindings)
  | q`Boogie.else1 =>
    let args ← checkOpArg arg q`Boogie.else1 1
    translateBlock bindings args[0]!
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
  TransM (Map BoogieIdent LMonoTy) := do
  let bargs ← checkOpArg op q`Boogie.mkBindings 1
  match bargs[0]! with
  | .commaSepList args =>
    let arr ← translateInitMkBindings bindings args
    return arr.toList
  | _ =>
    TransM.error s!"translateBindings expects a comma separated list: {repr op}"

def translateModifies (arg : Arg) : TransM BoogieIdent := do
  let args ← checkOpArg arg q`Boogie.modifies_spec 1
  translateIdent BoogieIdent args[0]!

def translateOptionFree (arg : Arg) : TransM Procedure.CheckAttr := do
  let .option free := arg
    | TransM.error s!"translateOptionFree unexpected {repr arg}"
  match free with
  | some f =>
    let _ ← checkOpArg f q`Boogie.free 0
    return .Free
  | none => return .Default

def translateRequires (name : BoogieIdent) (count : Nat) (bindings : TransBindings) (arg : Arg) :
  TransM (Map BoogieLabel Procedure.Check) := do
  let args ← checkOpArg arg q`Boogie.requires_spec 3
  let l ← translateOptionLabel s!"{name.2}_requires_{count}" args[0]!
  let free? ← translateOptionFree args[1]!
  let e ← translateExpr bindings args[2]!
  return [(l, { expr := e, attr := free? })]

def translateEnsures (name : BoogieIdent) (count : Nat) (bindings : TransBindings) (arg : Arg) :
  TransM (Map BoogieLabel Procedure.Check) := do
  let args ← checkOpArg arg q`Boogie.ensures_spec 3
  let l ← translateOptionLabel s!"{name.2}_ensures_{count}" args[0]!
  let free? ← translateOptionFree args[1]!
  let e ← translateExpr bindings args[2]!
  return [(l, { expr := e, attr := free? })]

def translateSpecElem (name : BoogieIdent) (count : Nat) (bindings : TransBindings) (arg : Arg) :
  TransM (List BoogieIdent × Map BoogieLabel Procedure.Check × Map BoogieLabel Procedure.Check) := do
  let .op op := arg
    | TransM.error s!"translateSpecElem expects an op {repr arg}"
  match op.name with
  | q`Boogie.modifies_spec =>
    let elem ← translateModifies arg
    return ([elem], [], [])
  | q`Boogie.requires_spec =>
    let elem ← translateRequires name count bindings arg
    return ([], elem, [])
  | q`Boogie.ensures_spec =>
    let elem ← translateEnsures name count bindings arg
    return ([], [], elem)
  | _ =>
    TransM.error s!"translateSpecElem unimplemented for {repr arg}"

partial def translateSpec (name : BoogieIdent) (bindings : TransBindings) (arg : Arg) :
  TransM (List BoogieIdent × Map BoogieLabel Procedure.Check × Map BoogieLabel Procedure.Check) := do
  let sargs ← checkOpArg arg q`Boogie.spec_mk 1
  let .seq args := sargs[0]!
    | TransM.error s!"Invalid specs {repr sargs[0]!}"
  go 0 args.size args
  where go (count max : Nat) (args : Array Arg) := do
  match (max - count) with
  | 0 => return ([], [], [])
  | _ + 1 =>
    let arg := args[count]!
    let (mods, reqs, ens) ← translateSpecElem name count bindings arg
    let (restmods, restreqs, restens) ← go (count + 1) max args
    return (mods ++ restmods, reqs ++ restreqs, ens ++ restens)

def translateProcedure (bindings : TransBindings) (op : Operation) :
  TransM (Boogie.Decl × TransBindings) := do
  let _ ← @checkOp (Boogie.Decl × TransBindings) op q`Boogie.command_procedure 6
  let pname ← translateIdent BoogieIdent op.args[0]!
  let typeArgs ← translateTypeArgs op.args[1]!
  let sig ← translateBindings bindings op.args[2]!
  let ret ← translateOptionMonoDeclList bindings op.args[3]!
  let in_bindings := (sig.keys.map (fun v => (LExpr.fvar v none))).toArray
  let out_bindings := (ret.keys.map (fun v => (LExpr.fvar v none))).toArray
  -- This bindings order -- original, then inputs, and then outputs, is
  -- critical here. Is this right though?
  let origBindings := bindings
  let bbindings := bindings.boundVars ++ in_bindings ++ out_bindings
  let bindings := { bindings with boundVars := bbindings }
  let .option speca := op.args[4]!
    | TransM.error s!"translateProcedure spec. expected here: {repr op.args[3]!}"
  let (modifies, requires, ensures) ←
    if speca.isSome then translateSpec pname bindings speca.get! else pure ([], [], [])
  let .option bodya := op.args[5]!
    | TransM.error s!"translateProcedure body expected here: {repr op.args[4]!}"
  let (body, bindings) ← if bodya.isSome then translateBlock bindings bodya.get! else pure ([], bindings)
  let origBindings := {origBindings with gen := bindings.gen}
  return (.proc { header := { name := pname,
                              typeArgs := typeArgs.toList,
                              inputs := sig,
                              outputs := ret },
                  spec := { modifies := modifies,
                            preconditions := requires,
                            postconditions := ensures },
                  body := body
                },
          origBindings)

---------------------------------------------------------------------

def translateConstant (bindings : TransBindings) (op : Operation) :
  TransM (Boogie.Decl × TransBindings) := do
  let _ ← @checkOp (Boogie.Decl × TransBindings) op q`Boogie.command_constdecl 3
  let cname ← translateIdent BoogieIdent op.args[0]!
  let typeArgs ← translateTypeArgs op.args[1]!
  let ret ← translateLMonoTy bindings op.args[2]!
  let decl := .func { name := cname,
                      typeArgs := typeArgs.toList,
                      inputs := [],
                      output := ret,
                      body := none }
  return (decl, { bindings with freeVars := bindings.freeVars.push decl })

---------------------------------------------------------------------

def translateAxiom (bindings : TransBindings) (op : Operation) :
  TransM (Boogie.Decl × TransBindings) := do
  let _ ← @checkOp (Boogie.Decl × TransBindings) op q`Boogie.command_axiom 2
  let l ← translateOptionLabel s!"TODO" op.args[0]!
  let e ← translateExpr bindings op.args[1]!
  return (.ax (Axiom.mk l e), bindings)

---------------------------------------------------------------------

inductive FnInterp where
  | Definition
  | Declaration
  deriving Repr

def translateOptionInline (arg : Arg) : TransM (Array String) := do
  -- (FIXME) The return type should be the same as that of `LFunc.attr`, which is
  -- `Array String` but of course, this is not ideal. We'd like an inductive
  -- type here of the allowed attributes in the future.
  let .option inline := arg
    | TransM.error s!"translateOptionInline unexpected {repr arg}"
  match inline with
  | some f =>
    let _ ← checkOpArg f q`Boogie.inline 0
    return #["inline"]
  | none => return #[]

def translateFunction (status : FnInterp) (bindings : TransBindings) (op : Operation) :
  TransM (Boogie.Decl × TransBindings) := do
  let _ ←
    match status with
    | .Definition  => @checkOp (Boogie.Decl × TransBindings) op q`Boogie.command_fndef  6
    | .Declaration => @checkOp (Boogie.Decl × TransBindings) op q`Boogie.command_fndecl 4
  let fname ← translateIdent BoogieIdent op.args[0]!
  let typeArgs ← translateTypeArgs op.args[1]!
  let sig ← translateBindings bindings op.args[2]!
  let ret ← translateLMonoTy bindings op.args[3]!
  let in_bindings := (sig.keys.map (fun v => (LExpr.fvar v none))).toArray
  -- This bindings order -- original, then inputs, is
  -- critical here. Is this right though?
  let orig_bbindings := bindings.boundVars
  let bbindings := bindings.boundVars ++ in_bindings
  let bindings := { bindings with boundVars := bbindings }
  let body ← match status with
             | .Definition =>
                let e ← translateExpr bindings op.args[4]!
                pure (some e)
             | .Declaration => pure none
  let inline? ← match status with
                 | .Definition => translateOptionInline op.args[5]!
                 | .Declaration => pure #[]
  let decl := .func { name := fname,
                      typeArgs := typeArgs.toList,
                      inputs := sig,
                      output := ret,
                      body := body,
                      attr := inline? }
  return (decl,
          { bindings with
            boundVars := orig_bbindings,
            freeVars := bindings.freeVars.push decl })

---------------------------------------------------------------------

def translateGlobalVar (bindings : TransBindings) (op : Operation) :
  TransM (Boogie.Decl × TransBindings) := do
  let _ ← @checkOp (Boogie.Decl × TransBindings) op q`Boogie.command_var 1
  let (id, targs, mty) ← translateBindMk bindings op.args[0]!
  let ty := LTy.forAll targs mty
  let decl := (.var id ty (Names.initVarValue id ("_" ++ (toString bindings.gen))))
  let bindings := incrGen bindings
  return (decl, { bindings with freeVars := bindings.freeVars.push decl})

---------------------------------------------------------------------

partial def translateBoogieDecls (n : Nat) (bindings : TransBindings) (ops : Array Operation) :
  TransM Boogie.Decls := do
  let (decls, _) ← go 0 n bindings ops
  return decls
  where go (count max : Nat) bindings ops : TransM (Boogie.Decls × TransBindings) := do
  match (max - count) with
  | 0 => return ([], bindings)
  | _ + 1 =>
    let op := ops[count]!
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
        translateAxiom bindings op
      | q`Boogie.command_procedure =>
        translateProcedure bindings op
      | q`Boogie.command_fndef =>
        translateFunction .Definition bindings op
      | q`Boogie.command_fndecl =>
        translateFunction .Declaration bindings op
      | _ => TransM.error s!"translateBoogieDecls unimplemented for {repr op}"
    let (decls, bindings) ← go (count + 1) max bindings ops
    return ((decl :: decls), bindings)

def translateProgram (ops : Array Operation) : TransM Boogie.Program := do
  let decls ← translateBoogieDecls ops.size {} ops
  return { decls := decls }

---------------------------------------------------------------------

end Strata
