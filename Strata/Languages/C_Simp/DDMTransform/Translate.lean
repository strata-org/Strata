/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.C_Simp.DDMTransform.Parse
import Strata.Languages.C_Simp.C_Simp

---------------------------------------------------------------------
namespace Strata

namespace C_Simp
-- (TODO) A bunch of this is just copied from Boogie (or copied with very minor changes)
-- What can we factor out to shared code (and where should we put it)?


/- Translating concrete syntax into abstract syntax -/

open C_Simp Lambda Imperative
open Std (ToFormat Format format)

---------------------------------------------------------------------

def initVarValue (id : String) : LExpr LMonoTy String :=
  .fvar ("init_" ++ id) none

---------------------------------------------------------------------

/- Translation Monad -/

structure TransState where
  errors : Array String

def TransM := StateM TransState
  deriving Monad

def TransM.run (m : TransM α) : (α × Array String) :=
  let (v, s) := StateT.run m { errors := #[] }
  (v, s.errors)

instance : ToString (C_Simp.Program × Array String) where
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

def translateIdent (arg : Strata.Arg) : TransM String := do
  let .ident name := arg
    | TransM.error s!"Expected ident: {repr arg}"
  pure name

def translateNat (arg : Arg) : TransM Nat := do
  let .num n := arg
    | TransM.error s!"translateNat expects num lit"
  return n

---------------------------------------------------------------------

structure TransBindings where
  boundTypeVars : Array String := #[]
  boundVars : Array (LExpr LMonoTy String) := #[]
  freeVars  : Array String := #["return"] -- There's a global variable "return" for return values

instance : ToFormat TransBindings where
  format b := f!"BoundTypeVars: {b.boundTypeVars}\
                {Format.line}\
                BoundVars: {b.boundVars}\
                {Format.line}\
                FreeVars: {b.freeVars}"

instance : Inhabited (List Statement × TransBindings) where
  default := ([], {})

instance : Inhabited (C_Simp.Function × TransBindings) where
  default := ({name := "badfun", pre := (.const "true" none), post := (.const "true" none), body := [], ret_ty := (.tcons "bad" []), inputs := {} }, {})

instance : Inhabited (List C_Simp.Function × TransBindings) where
  default := ([], {})


-- I'd recommend reading the below code from bottom to top to get a top-down view of the translation.

---------------------------------------------------------------------

def translateTypeBinding (bindings : TransBindings) (op : Arg) :
  TransM (String × TransBindings) := do
  -- (FIXME) Account for metadata.
  let bargs ← checkOpArg op q`C_Simp.mkBinding 2
  let id ← translateIdent bargs[0]!
  -- (TODO) It looks like other elements of `bargs` are irrelevant here?
  -- Perhaps we should not using `Bindings` for type declarations.
  let bindings := { bindings with boundTypeVars := bindings.boundTypeVars ++ [id]}
  return (id, bindings)

mutual
partial def translateLMonoTy (bindings : TransBindings) (arg : Arg) :
  TransM LMonoTy := do
  let .type tp := arg
    | TransM.error s!"translateLMonoTy expected type {repr arg}"
  match tp with
  | .ident i #[] => pure <| (.tcons i.name [])
  | .ident i argst =>
      let argst' ← translateLMonoTys bindings (argst.map Arg.type)
      pure <| (.tcons i.name argst'.toList.reverse)
  | .bvar i =>
    assert! i < bindings.boundTypeVars.size
    let var := bindings.boundTypeVars[bindings.boundTypeVars.size - (i+1)]!
    return (.ftvar var)
  | _ => TransM.error s!"translateLMonoTy not yet implemented {repr tp}"

partial def translateLMonoTys (bindings : TransBindings) (args : Array Arg) :
  TransM (Array LMonoTy) :=
  args.mapM (fun a => translateLMonoTy bindings a)
end

---------------------------------------------------------------------

def translateFn (q : QualifiedIdent) : TransM (LExpr LMonoTy String) :=
  match q with
  | q`C_Simp.and      => return (.op "Bool.And"     none)
  | q`C_Simp.or       => return (.op "Bool.Or"      none)
  | q`C_Simp.not      => return (.op "Bool.Not"     none)
  | q`C_Simp.le       => return (.op "Int.Le"       none)
  | q`C_Simp.lt       => return (.op "Int.Lt"       none)
  | q`C_Simp.ge       => return (.op "Int.Ge"       none)
  | q`C_Simp.gt       => return (.op "Int.Gt"       none)
  | q`C_Simp.add      => return (.op "Int.Add"      none)
  | q`C_Simp.sub      => return (.op "Int.Sub"      none)
  | q`C_Simp.mul      => return (.op "Int.Mul"      none)
  | q`C_Simp.div      => return (.op "Int.Div"      none)
  | q`C_Simp.mod      => return (.op "Int.Mod"      none)
  | q`C_Simp.len      => return (.op "Array.Len"    none)
  | q`C_Simp.get      => return (.op "Array.Get"    none)
  | _                 => TransM.error s!"translateFn: Unknown/unimplemented function {repr q}"

mutual
partial def translateExpr (bindings : TransBindings) (arg : Arg) :
  TransM (LExpr LMonoTy String) := do
  let .expr expr := arg
    | TransM.error s!"translateExpr expected expr {repr arg}"
  let (op, args) := expr.flatten
  match op, args with
  -- Constants/Literals
  | .fn q`C_Simp.btrue, [] =>
    return .const "true" none
  | .fn q`C_Simp.bfalse, [] =>
    return .const "false" none
  | .fn q`C_Simp.to_int, [xa] =>
    let n ← translateNat xa
    return .const (toString n) none
  -- Equality
  | .fn q`C_Simp.eq, [_tpa, xa, ya] =>
    let x ← translateExpr bindings xa
    let y ← translateExpr bindings ya
    return .eq x y
  -- Unary function applications
  | .fn q`C_Simp.not, [xa] =>
    let fn := (LExpr.op "Bool.Not" none)
    let x ← translateExpr bindings xa
    return .mkApp fn [x]
  -- Unary array operations
  | .fn q`C_Simp.len, [xa] =>
    let fn ← translateFn q`C_Simp.len
    let x ← translateExpr bindings xa
    return .mkApp fn [x]
  -- Binary function applications
  | .fn fni, [xa, ya] =>
    let fn ← translateFn fni
    let x ← translateExpr bindings xa
    let y ← translateExpr bindings ya
    return .mkApp fn [x, y]
  -- NOTE: Bound and free variables are numbered differently. Bound variables
  -- ascending order (so closer to deBrujin levels).
  | .bvar i, [] =>
    assert! i < bindings.boundVars.size
    let expr := bindings.boundVars[bindings.boundVars.size - (i+1)]!
    match expr with
    | .bvar _ => return .bvar i
    | _ => return expr
  | .fvar i, [] =>
    assert! i < bindings.freeVars.size
    let name := bindings.freeVars[i]!
    return (.fvar name none)
  | .fvar i, argsa =>
    -- Call of a function declared/defined in C_Simp.
    assert! i < bindings.freeVars.size
    let name := bindings.freeVars[i]!
    let args ← translateExprs bindings argsa.toArray
    return .mkApp (.op name none) args.toList
  | op, args =>
    TransM.error s!"translateExpr unimplemented op:\n\
                     Op: {repr op}\n\
                     Args: {repr args}\n\
                     Bindings: {format bindings}}"

partial def translateExprs (bindings : TransBindings) (args : Array Arg) :
  TransM (Array (LExpr LMonoTy String)) :=
  args.mapM (fun a => translateExpr bindings a)
end

def translateMeasure (bindings : TransBindings) (arg : Arg) : TransM (Option (LExpr LMonoTy String)) := do
  translateOption (fun maybe_arg => do
                    match maybe_arg with
                    | none => return none
                    | some a =>
                      let e ← checkOpArg a q`C_Simp.measure 1
                      assert! e.size == 1
                      return some (← translateExpr bindings e[0]!))
                  arg

def translateInvariant (bindings : TransBindings) (arg : Arg) : TransM (Option (LExpr LMonoTy String)) := do
  translateOption (fun maybe_arg => do
                    match maybe_arg with
                    | none => return none
                    | some a =>
                      let e ← checkOpArg a q`C_Simp.invariant 1
                      assert! e.size == 1
                      return some (← translateExpr bindings e[0]!))
                  arg

---------------------------------------------------------------------

def translateTypeArgs (op : Strata.Arg) : TransM (Array String) := do
  translateOption (fun x => do match x with
                  | none => return Array.empty
                  | some a =>
                    let args ← checkOpArg a q`C_Simp.type_args 1
                    translateCommaSep translateIdent args[0]!)
                  op

def translateBindMk (bindings : TransBindings) (arg : Arg) :
   TransM (String × List String × LMonoTy) := do
  let .op op := arg
    | TransM.error s!"translateBindMk expected op {repr arg}"
  match op.name, op.args with
  | q`C_Simp.bind_mk, #[ida, targsa, tpa] =>
    let id ← translateIdent ida
    let args ← translateTypeArgs targsa
    let tp ← translateLMonoTy bindings tpa
    return (id, args.toList, tp)
  | _, _ =>
    TransM.error s!"translateBindMk unimplemented for {repr arg}"

def translateMonoBindMk (bindings : TransBindings) (arg : Arg) :
   TransM (String × LMonoTy) := do
  let .op op := arg
    | TransM.error s!"translateMonoBindMk expected op {repr arg}"
  match op.name, op.args with
  | q`C_Simp.mono_bind_mk, #[ida, tpa] =>
    let id ← translateIdent ida
    let tp ← translateLMonoTy bindings tpa
    return (id, tp)
  | _, _ =>
    TransM.error s!"translateMonoBindMk unimplemented for {repr arg}"

partial def translateDeclList (bindings : TransBindings) (arg : Arg) :
  TransM (Map Expression.Ident LTy) := do
  let .op op := arg
    | TransM.error s!"translateDeclList expects an op {repr arg}"
  match op.name with
  | q`C_Simp.declAtom =>
    let args ← checkOpArg arg q`C_Simp.declAtom 1
    let (id, targs, mty) ← translateBindMk bindings args[0]!
    let lty := .forAll targs mty
    pure [(id, lty)]
  | q`C_Simp.declPush =>
    let args ← checkOpArg arg q`C_Simp.declPush 2
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
  | q`C_Simp.monoDeclAtom =>
    let args ← checkOpArg arg q`C_Simp.monoDeclAtom 1
    let (id, mty) ← translateMonoBindMk bindings args[0]!
    pure [(id, mty)]
  | q`C_Simp.monoDeclPush =>
    let args ← checkOpArg arg q`C_Simp.monoDeclPush 2
    let fst ← translateMonoDeclList bindings args[0]!
    let (id, mty) ← translateMonoBindMk bindings args[1]!
    pure (fst ++ [(id, mty)])
  | _ => TransM.error s!"translateMonoDeclList unimplemented for {repr op}"

def translateBindings (bindings : TransBindings) (op : Arg) :
  TransM (Map String LMonoTy) := do
  let bargs ← checkOpArg op q`C_Simp.mkBindings 1
  match bargs[0]! with
  | .commaSepList args =>
    let arr ← args.mapM (fun op => do
      let bargs ← checkOpArg op q`C_Simp.mkBinding 2
      let id ← translateIdent bargs[0]!
      let tp ← translateLMonoTy bindings bargs[1]!
      return (id, tp))
    return arr.toList
  | _ =>
    TransM.error s!"translateBindings expects a comma separated list: {repr op}"


mutual
partial def translateStmt (bindings : TransBindings) (arg : Arg) :
  TransM (List Statement × TransBindings) := do
  let .op op := arg
    | TransM.error s!"translateStmt expected op {repr arg}"

  match op.name, op.args with
  | q`C_Simp.init_decl, #[ida, tpa] =>
    let id ← translateIdent ida
    let tp ← translateLMonoTy bindings tpa
    let ty := (.forAll [] tp)
    let newFVar: LExpr LMonoTy String := LExpr.fvar id none
    let bbindings := bindings.boundVars ++ [newFVar]
    let newBindings := { bindings with
                         boundVars := bbindings,
                         freeVars := bindings.freeVars.push id }
    return ([(.cmd (.init id ty (initVarValue id)))], newBindings)
  | q`C_Simp.init_def, #[ida, tpa, ea] =>
    let id ← translateIdent ida
    let tp ← translateLMonoTy bindings tpa
    let val ← translateExpr bindings ea
    let ty := (.forAll [] tp)
    let newFVar: LExpr LMonoTy String := LExpr.fvar id none
    let bbindings := bindings.boundVars ++ [newFVar]
    let newBindings := { bindings with
                         boundVars := bbindings,
                         freeVars := bindings.freeVars.push id }
    return ([(.cmd (.init id ty val))], newBindings)
  | q`C_Simp.assign, #[_tpa, ida, ea] =>
    let id ← translateIdent ida
    let val ← translateExpr bindings ea
    return ([(.cmd (.set id val))], bindings)
  | q`C_Simp.if_command, #[ca, ta, fa] =>
    let c ← translateExpr bindings ca
    let t := { ss := ← translateBlock bindings ta }
    let f := { ss := ← translateElse bindings fa }
    return ([(.ite c t f)], bindings)
  | q`C_Simp.while_command, #[ga, measurea, invarianta, ba] =>
    -- TODO: Handle measure and invariant
    return ([.loop (← translateExpr bindings ga) (← translateMeasure bindings measurea) (← translateInvariant bindings invarianta) { ss := ← translateBlock bindings ba }], bindings)
  | q`C_Simp.return, #[_tpa, ea] =>
    -- Return statements are assignments to the global `return` variable
    -- TODO: I don't think this works if we have functions with different return types
    let val ← translateExpr bindings ea
    return ([(.cmd (.set "return" val))], bindings)
  | q`C_Simp.annotation, #[a] =>
    let .op a_op := a
      | TransM.error s!"Annotation expected op {repr a}"
    match a_op.name, a_op.args with
    | q`C_Simp.assert, #[la, ca] =>
      let l ← translateIdent la
      let c ← translateExpr bindings ca
      return ([(.cmd (.assert l c))], bindings)
    | q`C_Simp.assume, #[la, ca] =>
      let l ← translateIdent la
      let c ← translateExpr bindings ca
      return ([(.cmd (.assume l c))], bindings)
    | _,_ => TransM.error s!"Unexpected annotation."
  | name, args => TransM.error s!"Unexpected statement {name.fullName} with {args.size} arguments."

partial def translateBlock (bindings : TransBindings) (arg : Arg) :
  TransM (List Statement) := do
  let args ← checkOpArg arg q`C_Simp.block 1
  let .seq stmts := args[0]!
    | TransM.error s!"Invalid block {repr args[0]!}"
  let (a, _) ← stmts.foldlM (init := (#[], bindings)) fun (a, b) s => do
      let (s, b) ← translateStmt b s
      return (a.append s.toArray, b)
  return a.toList

partial def translateElse (bindings : TransBindings) (arg : Arg) :
  TransM (List Statement) := do
  let .op op := arg
    | TransM.error s!"translateElse expected op {repr arg}"
  match op.name with
  | q`C_Simp.else0 =>
    let _ ← checkOpArg arg q`C_Simp.else0 0
    return []
  | q`C_Simp.else1 =>
    let args ← checkOpArg arg q`C_Simp.else1 1
    translateBlock bindings args[0]!
  | _ => TransM.error s!"translateElse unimplemented for {repr arg}"

end

---------------------------------------------------------------------

def translateProcedure (bindings : TransBindings) (op : Operation) :
  TransM (C_Simp.Function × TransBindings) := do
  let _ ← @checkOp (C_Simp.Function × TransBindings) op q`C_Simp.procedure 7
  let ret_ty ← translateLMonoTy bindings op.args[0]!
  let _typeArgs := op.args[1]! -- TODO: Handle type arguments
  let sig ← translateBindings bindings op.args[2]!      -- Function signature/parameters
  let pname ← translateIdent op.args[3]!

  -- Add parameters to bindings for pre/post/body translation
  let paramBindings := (sig.keys.map (fun v => (LExpr.fvar v none))).toArray
  let extendedBindings := { bindings with
                            boundVars := bindings.boundVars ++ paramBindings,
                            freeVars := bindings.freeVars ++ sig.keys.toArray }

  let pre ← translateExpr extendedBindings op.args[4]!
  let post ← translateExpr extendedBindings op.args[5]!
  let body ← translateBlock extendedBindings op.args[6]!

  return ({ name := pname,
            pre := pre,
            post := post,
            body := body,
            ret_ty,
            inputs := sig },
          bindings)

---------------------------------------------------------------------

partial def translateCSimpFuncs (n : Nat) (bindings : TransBindings) (ops : Array Operation) :
  TransM (List C_Simp.Function) := do
  let (decls, _) ← go 0 n bindings ops
  return decls
  where go (count max : Nat) bindings ops : TransM ((List C_Simp.Function) × TransBindings) := do
  match (max - count) with
  | 0 => return ([], bindings)
  | _ + 1 =>
    let op := ops[count]!
    let (decl, bindings) ←
      match op.name with
      | q`C_Simp.procedure => translateProcedure bindings op
      | _ => TransM.error s!"translateCSimpFuncs unimplemented for {repr op}"
    let (decls, bindings) ← go (count + 1) max bindings ops
    return ((decl :: decls), bindings)

def translateProgram (ops : Array Operation) : TransM C_Simp.Program := do
  let funcs ← translateCSimpFuncs ops.size {} ops
  return { funcs }

---------------------------------------------------------------------

end C_Simp

end Strata
