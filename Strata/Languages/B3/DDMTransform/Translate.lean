/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST
import Strata.Languages.B3.DDMTransform.Parse
import Strata.Languages.B3.Stmt

---------------------------------------------------------------------
namespace Strata

/- Translating concrete syntax into abstract syntax -/

open B3
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
  let .commaSepList _ args := arg
    | TransM.error s!"Expected commaSepList: {repr arg}"
  args.mapM f

def translateOption [Inhabited α] (f : Option Strata.Arg → TransM α) (arg : Arg) :
  TransM α := do
  let .option _ maybe_arg := arg
    | TransM.error s!"Expected Option: {repr arg}"
  f maybe_arg

---------------------------------------------------------------------

def translateIdent (arg : Strata.Arg) : TransM B3Ident := do
  let .ident _ name := arg
    | TransM.error s!"Expected ident: {repr arg}"
  pure (B3Ident.mk name)

def translateStr (arg : Arg) : TransM String := do
  let .strlit _ s := arg
    | TransM.error s!"translateStr expects string lit"
  return s

def translateNat (arg : Arg) : TransM Nat := do
  let .num _ n := arg
    | TransM.error s!"translateNat expects num lit"
  return n

---------------------------------------------------------------------

structure TransBindings where
  boundVars : Array B3Ident := #[]

instance : Inhabited TransBindings where
  default := {}

instance : Inhabited (B3Stmt × TransBindings) where
  default := (.returnStmt (), {})

instance : Inhabited (List B3Stmt × TransBindings) where
  default := ([], {})

instance : Inhabited (B3Expression × TransBindings) where
  default := (.literal () (Lambda.LConst.boolConst false), {})

instance : Inhabited B3Expression where
  default := .literal () (Lambda.LConst.boolConst false)

---------------------------------------------------------------------

instance : Inhabited BinaryOp where
  default := .add

instance : Inhabited UnaryOp where
  default := .not

instance : Inhabited QuantifierKind where
  default := .forall

instance : Inhabited B3CallArg where
  default := .expr (.literal () (Lambda.LConst.boolConst false))

def translateBinaryOp (name : QualifiedIdent) : TransM BinaryOp :=
  match name with
  | q`B3.iff => return .iff
  | q`B3.implies => return .implies
  | q`B3.impliedBy => return .impliedBy
  | q`B3.and => return .and
  | q`B3.or => return .or
  | q`B3.equal => return .eq
  | q`B3.not_equal => return .neq
  | q`B3.lt => return .lt
  | q`B3.le => return .le
  | q`B3.ge => return .ge
  | q`B3.gt => return .gt
  | q`B3.add_expr => return .add
  | q`B3.sub_expr => return .sub
  | q`B3.mul_expr => return .mul
  | q`B3.div_expr => return .div
  | q`B3.mod_expr => return .mod
  | _ => TransM.error s!"Unknown binary operator: {name}"

def translateUnaryOp (name : QualifiedIdent) : TransM UnaryOp :=
  match name with
  | q`B3.not => return .not
  | q`B3.neg_expr => return .neg
  | _ => TransM.error s!"Unknown unary operator: {name}"

def translateQuantifierKind (name : QualifiedIdent) : TransM QuantifierKind :=
  match name with
  | q`B3.forall => return .forall
  | q`B3.exists => return .exists
  | _ => TransM.error s!"Unknown quantifier: {name}"

---------------------------------------------------------------------

mutual
partial def translateExpr (bindings : TransBindings) (arg : Arg) :
  TransM B3Expression := do
  let .expr expr := arg
    | TransM.error s!"translateExpr expected expr {repr arg}"
  let (op, args) := expr.flatten
  match op, args with
  -- Constants/Literals
  | .fn _ q`B3.btrue, [] =>
    return .literal () (Lambda.LConst.boolConst true)
  | .fn _ q`B3.bfalse, [] =>
    return .literal () (Lambda.LConst.boolConst false)
  | .fn _ q`B3.natToInt, [xa] =>
    let n ← translateNat xa
    return .literal () (Lambda.LConst.intConst n)
  | .fn _ q`B3.strLit, [xa] =>
    let s ← translateStr xa
    return .literal () (Lambda.LConst.strConst s)
  -- Binary operators
  | .fn _ fni, [_tpa, xa, ya] =>
    let op ← translateBinaryOp fni
    let x ← translateExpr bindings xa
    let y ← translateExpr bindings ya
    return .binaryOp () op x y
  -- Unary operators
  | .fn _ fni, [xa] =>
    let op ← translateUnaryOp fni
    let x ← translateExpr bindings xa
    return .unaryOp () op x
  -- Variable reference
  | .bvar _ i, [] =>
    if i < bindings.boundVars.size then
      let id := bindings.boundVars[bindings.boundVars.size - (i+1)]!
      return .id () id
    else
      TransM.error s!"translateExpr out-of-range bound variable: {i}"
  | op, args =>
    TransM.error s!"translateExpr unimplemented op:\n\
                     Op: {repr op}\n\
                     Args: {repr args}"

end

---------------------------------------------------------------------

mutual
partial def translateStmt (bindings : TransBindings) (arg : Arg) :
  TransM (B3Stmt × TransBindings) := do
  let .op op := arg
    | TransM.error s!"translateStmt expected op {repr arg}"

  match op.name, op.args with
  | q`B3.assign, #[_tpa, ida, ea] =>
    let id ← translateIdent ida
    let e ← translateExpr bindings ea
    return (.assign () id e, bindings)
  | q`B3.check, #[ca] =>
    let c ← translateExpr bindings ca
    return (.check () c, bindings)
  | q`B3.assume, #[ca] =>
    let c ← translateExpr bindings ca
    return (.assume () c, bindings)
  | q`B3.reach, #[ca] =>
    let c ← translateExpr bindings ca
    return (.reach () c, bindings)
  | q`B3.assert, #[ca] =>
    let c ← translateExpr bindings ca
    return (.assert () c, bindings)
  | q`B3.if_statement, #[ca, ta, fa] =>
    let c ← translateExpr bindings ca
    let (thenB, _) ← translateBlock bindings ta
    let (elseB, _) ← translateElse bindings fa
    return (.ifStmt () c thenB elseB, bindings)
  | q`B3.loop_statement, #[invsa, bodya] =>
    let .seq _ invs := invsa
      | TransM.error s!"translateStmt loop expected seq for invariants"
    let invariants ← invs.toList.mapM (fun inv => do
      let args ← checkOpArg inv q`B3.invariant 1
      translateExpr bindings args[0]!)
    let (body, _) ← translateBlock bindings bodya
    return (.loop () invariants body, bindings)
  | q`B3.exit_statement, #[labela] =>
    let label ← translateOption (fun x => match x with
      | none => return none
      | some a => do
        let l ← translateIdent a
        return some l.name) labela
    return (.exit () label, bindings)
  | q`B3.return_statement, #[] =>
    return (.returnStmt (), bindings)
  | name, args =>
    TransM.error s!"Unexpected statement {name.fullName} with {args.size} arguments."

partial def translateBlock (bindings : TransBindings) (arg : Arg) :
  TransM (B3Stmt × TransBindings) := do
  let args ← checkOpArg arg q`B3.block 1
  let .seq _ stmts := args[0]!
    | TransM.error s!"Invalid block {repr args[0]!}"
  let (stmtList, bindings) ← stmts.toList.foldlM (init := ([], bindings)) fun (acc, b) s => do
    let (stmt, b) ← translateStmt b s
    return (acc ++ [stmt], b)
  return (.blockStmt () stmtList, bindings)

partial def translateElse (bindings : TransBindings) (arg : Arg) :
  TransM (Option B3Stmt × TransBindings) := do
  let .op op := arg
    | TransM.error s!"translateElse expected op {repr arg}"
  match op.name with
  | q`B3.else0 =>
    let _ ← checkOpArg arg q`B3.else0 0
    return (none, bindings)
  | q`B3.else1 =>
    let args ← checkOpArg arg q`B3.else1 1
    let (block, bindings) ← translateBlock bindings args[0]!
    return (some block, bindings)
  | _ => TransM.error s!"translateElse unimplemented for {repr arg}"

end

---------------------------------------------------------------------

end Strata
