/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LState
import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.LExprTypeEnv
import Strata.DL.Lambda.IntBoolFactory

import Lean.Meta
import Lean.Elab.Term
import Lean.Elab.Command

import Lean.Server.CodeActions
import Lean.Server.Requests

/-!
## Reflect Lambda expressions into Lean's Logic

WIP.
-/

namespace Lambda
open Lean Elab Tactic Expr Meta
open Std (ToFormat Format format)

-------------------------------------------------------------------------------

class IdentifierString (Identifier : Type) where
  idToStr : Identifier → String
  strToId : String → Identifier

instance : IdentifierString String where
  idToStr := fun s => s
  strToId := fun s => s

class ExprIdentifierString (Identifier : Type) where
  idToStr : Expr → MetaM (Option String)
  strToid : Expr → MetaM (Option Identifier)

instance : ExprIdentifierString String where
  idToStr := fun e => return getStringValue? e
  strToid := fun e => return getStringValue? e

-------------------------------------------------------------------------------

def LMonoTy.toExpr (mty : LMonoTy) : MetaM Lean.Expr := do
  match mty with
  | LMonoTy.bool    => return (mkConst ``Bool)
  | LMonoTy.int     => return (mkConst ``Int)
  | LMonoTy.string  => return (mkConst ``String)
  | LMonoTy.bv1     => return (mkApp (mkConst ``BitVec) (mkNatLit 1))
  | LMonoTy.bv8     => return (mkApp (mkConst ``BitVec) (mkNatLit 8))
  | LMonoTy.bv16    => return (mkApp (mkConst ``BitVec) (mkNatLit 16))
  | LMonoTy.bv32    => return (mkApp (mkConst ``BitVec) (mkNatLit 32))
  | LMonoTy.bv64    => return (mkApp (mkConst ``BitVec) (mkNatLit 64))
  | .tcons "arrow" [a, b] =>
    let a ← LMonoTy.toExpr a
    let b ← LMonoTy.toExpr b
    return (.forallE `x a b .default)
  | .tcons "Map" [a, b] =>
    let a ← LMonoTy.toExpr a
    let b ← LMonoTy.toExpr b
    return mkApp2 (mkConst ``Map) a b
  | _ => throwError f!"[LMonoTy.toExpr] Unimplemented: {mty}"

/--
info: Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Map []) (Lean.Expr.const `Int [])) (Lean.Expr.const `Bool [])
-/
#guard_msgs in
open LTy.Syntax in
#eval LMonoTy.toExpr mty[Map int bool]

/--
Convert values of type `Bool` to `Prop` (and leave values of type `Prop`
unchanged); throw an error if non-`Bool` values are encountered.
-/
def toProp (e : Lean.Expr) : MetaM Lean.Expr := do
  let eType ← inferType e
  let eLvl ← getLevel eType
  if eType.isProp then
    return e
  else if eType == mkConst ``Bool then
    let expr := mkAppN (mkConst ``Eq [eLvl]) #[eType, e, mkConst ``Bool.true]
    return expr
  else
    throwError f!"Cannot coerce to a Prop: {e}"

def LExpr.const.toExpr (c : String) (mty : Option LMonoTy) : MetaM Lean.Expr := do
  match mty with
  | none => throwError f!"Cannot reflect an untyped constant: {c}!"
  | some mty => match mty with
    | LMonoTy.bool =>
      match c with
      | "true" => return (mkConst ``Bool.true)
      | "false" => return (mkConst ``Bool.false)
      | _ => throwError f!"Unexpected boolean: {c}"
    | LMonoTy.int =>
      if c.isInt then
        return (mkIntLit c.toInt!)
      else
        throwError f!"Unexpected integer: {c}"
    | LMonoTy.string =>
      return (mkStrLit c)
    | _ => throwError f!"Unexpected constant: {c}"

def LExpr.op.toExpr {Identifier} [IS : IdentifierString Identifier]
    (F : @Factory String) (op : Identifier) (_mty : Option LMonoTy) :
    MetaM Lean.Expr := do
    let op := IS.idToStr op
    match F.find? (fun f => f.name == op) with
    | none => throwError f!"[LExpr.op.toExpr] Operator {op} not found in the factory!"
    | some _lfunc =>
      match op with
      -- | "Int.Add" => return (mkConst ``Int.add)
      | "Int.Add" =>
        mkAppOptM ``HAdd.hAdd #[mkConst ``Int, mkConst ``Int, mkConst ``Int, none]
      -- | "Int.Mul" => return (mkConst ``Int.mul)
      | "Int.Mul" =>
        mkAppOptM ``HMul.hMul #[mkConst ``Int, mkConst ``Int, mkConst ``Int, none]
      -- | "Int.Gt" => return (mkConst ``Int.gt)
      | "Int.Gt" =>
        mkAppOptM ``GT.gt #[mkConst ``Int, none]
      | "Bool.Or" => return (mkConst ``Bool.or)
      | "Bool.Not" => return (mkConst ``Bool.not)
      | "Bool.Implies" => return (mkConst ``Bool.implies)
      | _ => throwError f!"[LExpr.op.toExpr] Unimplemented: {op}"

def LExpr.toExprNoFVars {Identifier} [IS : IdentifierString Identifier]
    (e : LExpr Identifier) : MetaM Lean.Expr := do
  match e with
  | .const c mty =>
    let expr ← LExpr.const.toExpr c mty
    return expr

  | .op name mty =>
    LExpr.op.toExpr IntBoolFactory name mty

  | .bvar i =>
    let lctx ← getLCtx
    let some decl := lctx.getAt? (lctx.decls.size - i - 1) |
        throwError f!"[LExpr .bvar {i}]: No local declaration found in the context!"
    let expr := .fvar decl.fvarId
    return expr

  | .fvar f _ =>
    let f := IS.idToStr f
    let lctx ← getLCtx
    match lctx.findFromUserName? (Lean.Name.mkSimple f) with
    | none => throwError f!"[LExpr.toExprNoFVars] Cannot find free var in the local context: .fvar {f}"
    | some decl => return decl.toExpr

  | .mdata _ e' => LExpr.toExprNoFVars e'

  | .abs mty e' =>
    match mty with
    | none => throwError f!"[LExpr.toExprNoFVars] Cannot reflect untyped abstraction!"
    | some ty => do
      let tyExpr ← LMonoTy.toExpr ty
      let fname ← Lean.Core.mkFreshUserName `x
      withLocalDecl fname .default tyExpr fun x => do
        let bodyExpr ← LExpr.toExprNoFVars e'
        mkLambdaFVars #[x] bodyExpr

  | .quant qk mty e =>
    match mty with
    | none => throwError f!"[LExpr.toExprNoFVars] Cannot reflect untyped quantifier!"
    | some ty =>
      let tyExpr ← LMonoTy.toExpr ty
      let fname ← Lean.Core.mkFreshUserName `x
      withLocalDecl fname .default tyExpr fun x => do
        let bodyExpr ← LExpr.toExprNoFVars e
        let bodyExpr ← toProp bodyExpr
        match qk with
        | .all =>
            let expr ← mkForallFVars #[x] bodyExpr
            return expr
        | .exist => do
          -- let lambdaExpr ← mkLambdaFVars #[x] bodyExpr
          -- dbg_trace f!"lambdaExpr: {lambdaExpr}"
          -- -- mkAppM ``Exists #[lambdaExpr]
          -- mkAppOptM ``Exists #[tyExpr, lambdaExpr]
          let expr ← mkForallFVars #[x] (mkNot bodyExpr)
          let expr := mkNot expr
          return expr

  | .app fn arg =>
    let fnExpr ← LExpr.toExprNoFVars fn
    let argExpr ← LExpr.toExprNoFVars arg
    let ret ← mkAppM' fnExpr #[argExpr]
    let ret_type ← inferType ret
    -- `fn` may be something like `GT.gt`, which returns a `Prop` instead of a
    -- `Bool`. We convert such decidable `Prop`s to `Bool`s below.
    if ret_type.isProp then
      mkAppOptM ``decide #[ret, none]
    else
      return ret

  | .ite c t e =>
    -- Lean's ite:
    -- _root_.ite.{u} {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α
    let cExpr ← LExpr.toExprNoFVars c
    let tExpr ← LExpr.toExprNoFVars t
    let eExpr ← LExpr.toExprNoFVars e
    -- In `cProp` below, `Eq` helps coerce `cExpr`, which is a `Bool`, to
    -- `Prop`.
    let cProp ← mkAppM ``Eq #[cExpr, mkConst ``Bool.true]
    mkAppM ``_root_.ite #[cProp, tExpr, eExpr]

  | .eq e1 e2 =>
    let e1Expr ← LExpr.toExprNoFVars e1
    let e2Expr ← LExpr.toExprNoFVars e2
    let expr ← mkAppM ``BEq.beq #[e1Expr, e2Expr]
    return expr

def LExpr.toExpr {Identifier} [IS: IdentifierString Identifier] [DecidableEq Identifier]
     (e : LExpr Identifier) : MetaM Lean.Expr := do
  let idTs := e.freeVars.deduplicate
  let decls : List (Name × (Array Lean.Expr → MetaM Lean.Expr)) ←
    idTs.mapM fun idT => do
      match idT.snd with
      | none => throwError f!"Untyped fvar encountered: {IS.idToStr idT.fst}"
      | some ty =>
        -- let name ← Lean.Core.mkFreshUserName (Lean.Name.mkSimple idT.fst)
        let name := Lean.Name.mkSimple (IS.idToStr idT.fst)
        return (name, fun _ => LMonoTy.toExpr ty)
  withLocalDeclsD decls.toArray fun fvars => do
    let e ← LExpr.toExprNoFVars e
    let e ← toProp e
    mkForallFVars (usedOnly := true) fvars e

-------------------------------------------------------------------------------

section Tests

open LTy.Syntax LExpr.Syntax

elab "test_elab_lexpr" "[" e:term "]" : term => unsafe do
  let expr ← Term.elabTerm e none
  let lexpr ← Lean.Meta.evalExpr (LExpr String) (mkApp (mkConst ``LExpr) (mkConst ``String)) expr
  let result ← liftM (LExpr.toExpr lexpr)
  return result

/-- error: Cannot reflect an untyped constant: 5! -/
#guard_msgs in
#check test_elab_lexpr [@LExpr.const String "5" Option.none]

/-- error: Cannot coerce to a Prop: OfNat.ofNat.{0} Int 5 (instOfNat 5) -/
#guard_msgs in
#check test_elab_lexpr [@LExpr.const String "5" (Option.some (LMonoTy.int))]

/-- info: true -/
#guard_msgs in
#eval test_elab_lexpr [@LExpr.eq String
                          (@LExpr.const String "5" (Option.some (LMonoTy.int)))
                          (@LExpr.const String "5" (Option.some (LMonoTy.int)))]

/-- info: ∀ (x : Int), (x == 5) = true : Prop -/
#guard_msgs in
#check test_elab_lexpr [@LExpr.eq String
                          (@LExpr.fvar String "x" (Option.some (LMonoTy.int)))
                          (@LExpr.const String "5" (Option.some (LMonoTy.int)))]

/-- info: ∀ (x x_1 : Int), (x == x_1) = true : Prop -/
#guard_msgs in
#check test_elab_lexpr [es[∀ (int): ((x : int) == %0)]]

/-- info: ¬∀ (x : Int), ¬(5 == x) = true : Prop -/
#guard_msgs in
#check test_elab_lexpr [es[∃ (int): ((#5 : int) == %0)]]

end Tests

-------------------------------------------------------------------------------

open Lean Lean.Expr Lean.Meta Lean.Elab Lean.Elab.Command
open LExpr.Syntax LTy.Syntax

partial def shallowExprToLMonoTy (e : Expr) : MetaM LMonoTy := do
  match_expr e with
  | LMonoTy.ftvar name =>
    let some name := Lean.Meta.getStringValue? name | failure
    return (.ftvar name)
  | LMonoTy.tcons name args =>
    let some name := Lean.Meta.getStringValue? name | failure
    let some args ← Lean.Meta.getListLit? args | failure
    let args ← go args.toList
    return (.tcons name args)
  | LMonoTy.bitvec n =>
    let some n ← Lean.Meta.getNatValue? n | failure
    return (.bitvec n)
  | _ => throwError f!"[shallowExprToLMonoTy] Unimplemented: {e}"
  where go (args : List Expr) : MetaM (List LMonoTy) := do
  match args with
  | [] => return []
  | a :: arest =>
    let a ← shallowExprToLMonoTy a
    let arest ← go arest
    return (a :: arest)

def shallowOptionExprToLMonoTy (some_mty : Expr) : MetaM LMonoTy := do
  match_expr some_mty with
  | Option.none _ => failure
  | Option.some _ mty => shallowExprToLMonoTy mty
  | _ => throwError f!"Unexpected optional monotype: {some_mty}"

partial def shallowExprToLExpr {Identifier}
    [IE : ExprIdentifierString Identifier] [IS : IdentifierString Identifier]
    (e : Expr) : MetaM (LExpr Identifier) := do
  match_expr e with
  | Lambda.LExpr.const _identifier c some_mty =>
    -- let_expr String ← identifier | failure
    let some c := Lean.Meta.getStringValue? c |
      throwError f!"[shallowExprToLExpr] Couldn't get the constant {c}!"
    let mty ← shallowOptionExprToLMonoTy some_mty
    return (.const c mty)

  | Lambda.LExpr.op _identifier name _some_mty =>
    -- let_expr String ← identifier | failure
    -- let some name := Lean.Meta.getStringValue? name | failure
    let some name ← IE.idToStr name |
      throwError f!"[shallowExprToLExpr] Couldn't get the op {name}!"
    -- (FIXME)
    -- let mty ← shallowOptionExprToLMonoTy some_mty
    return (.op (IS.strToId name) .none)

  | Lambda.LExpr.bvar _identifier n =>
    -- let_expr String ← identifier | failure
    let some n ← Lean.Meta.getNatValue? n |
      throwError f!"[shallowExprToLExpr] Couldn't get the .bvar {n}!"
    return (.bvar n)

  | Lambda.LExpr.fvar _identifier name some_mty =>
    -- let_expr String ← identifier | failure
    -- let some name := Lean.Meta.getStringValue? name | failure
    let some name ← IE.idToStr name |
      throwError f!"[shallowExprToLExpr] Couldn't get the .fvar {name}!"
    let mty ← shallowOptionExprToLMonoTy some_mty
    return (.fvar (IS.strToId name) mty)

  | Lambda.LExpr.abs _identifier some_mty e =>
    -- let_expr String ← identifier | failure
    let mty ← shallowOptionExprToLMonoTy some_mty
    let e ← shallowExprToLExpr e
    return (.abs mty e)

  | Lambda.LExpr.app _identifier fn e =>
    -- let_expr String ← identifier | failure
    let fn ← shallowExprToLExpr fn
    let e ← shallowExprToLExpr e
    return (.app fn e)

  | Lambda.LExpr.ite _identifier c t e =>
    -- let_expr String ← identifier | failure
    let c ← shallowExprToLExpr c
    let t ← shallowExprToLExpr t
    let e ← shallowExprToLExpr e
    return (.ite c t e)

  | Lambda.LExpr.eq _identifier e1 e2 =>
    -- let_expr String ← identifier | failure
    let e1 ← shallowExprToLExpr e1
    let e2 ← shallowExprToLExpr e2
    return (.eq e1 e2)

  | Lambda.LExpr.quant _identifier kind some_mty e =>
    -- let_expr String ← identifier | failure
    let mty ← shallowOptionExprToLMonoTy some_mty
    let kind := match_expr kind with
                | QuantifierKind.all => .all | _ => .exist
    let e ← shallowExprToLExpr e
    return (.quant kind mty e)

  | _ => throwError f!"Unimplemented: {e}"

/-
elab "#gen_lean_vcs" lexpr:term : command => liftTermElabM do
  let (term : Lean.Expr) ← Elab.Term.elabTerm lexpr (mkApp (mkConst ``LExpr) (mkConst ``String))
  let (term : Lean.Expr) ← whnfD term
  let lexpr ← shallowExprToLExpr term
  let expr ← LExpr.toExpr lexpr
  let pp ← ppExpr expr
  dbg_trace f!"expr: {pp}"
  return

#gen_lean_vcs es[(x : int) == (#5 : int)]

#gen_lean_vcs es[(x : int) == ((λ (int): %0) (#3 : int))]

#eval es[(x : int) == ((~Int.Add %0) (#1 : int))]

#gen_lean_vcs es[(x : int) == ((~Int.Add (#20 : int)) (#30 : int))]

#gen_lean_vcs es[(x : int) == ((λ (int): ((~Int.Add %0) (#1 : int))) (#3 : int))]

#gen_lean_vcs es[∃ (int): %0 == (#5 : int)]

#gen_lean_vcs es[∀ (int): %0 == (#5 : int)]
-/

-------------------------------------------------------------------------------

syntax (name := genLeanVCThms) "#gen_lean_vc_thms"
  ws withoutPosition(ident) ws withoutPosition(ident) ws withoutPosition(term) : command

structure GenLeanVCThmsOutput where
  res : String
deriving TypeName

def genVCTheorem {Identifier} [IE : ExprIdentifierString Identifier]
    [IS : IdentifierString Identifier] [DecidableEq Identifier]
    (ns name : TSyntax `ident) (lexpr : TSyntax `term) : TermElabM String := do
  let full_name := Lean.Name.append ns.getId name.getId
  let curr_ns ← getCurrNamespace
  let label := if curr_ns == ns.getId then name.getId else full_name
  let (term : Lean.Expr) ← Elab.Term.elabTerm lexpr (mkApp (mkConst ``LExpr) (mkConst `Identifier))
  let (term : Lean.Expr) ← whnfD term
  let (lexpr : LExpr Identifier) ← shallowExprToLExpr term
  let type ← LExpr.toExpr lexpr
  let env ← getEnv
  match env.find? full_name with
  | some pre_exist_decl =>
    if pre_exist_decl.type == type then
      let msg := s!"Theorem {label} is already in the environment!"
      let has_sorry := pre_exist_decl.value!.hasSorry
      if has_sorry then
        return (msg ++ s!"\nNote that theorem {label} was proved using `sorry`!")
      else
        return msg
    else
      return s!"Theorem of name {label} is already in the environment, \
                 but its statement differs from the new conjecture! \n\
                 Existing theorem statement:\n\
                 {← ppExpr pre_exist_decl.type}\n\
                 New statement:\n\
                 {← ppExpr type}"
  | none =>
    let value ←  mkSorry (mkSort levelZero) false
    let theoremText := s!"theorem {label} : {← ppExpr type} := {← ppExpr value}"
    return theoremText

-- Everything below assumes, for now, that `Identifier` is simply `String`.

@[command_elab genLeanVCThms] def elabGenLeanVCThms : CommandElab
  | `(command| #gen_lean_vc_thms $ns $name $lexpr) => do
      let msg ← liftTermElabM (@genVCTheorem String _ _ _ ns name lexpr)
      pushInfoLeaf (.ofCustomInfo { stx := ← getRef, value := Dynamic.mk (GenLeanVCThmsOutput.mk msg) })
      logInfo msg
  | _ => throwUnsupportedSyntax

mutual
partial def customNodeFromTree (t : InfoTree) : Option (Syntax × String) := do
  match t with
  | .node (.ofCustomInfo { stx, value }) _ => return (stx, (← value.get? (GenLeanVCThmsOutput)).res)
  | .node _ ts => customNodeFromTrees ts
  | .context _ t => customNodeFromTree t
  | _ => none

partial def customNodeFromTrees (ts : PersistentArray InfoTree) : Option (Syntax × String) := Id.run do
  let mut result := Option.none
  for t in ts do
    match customNodeFromTree t with
    | none => continue
    | some ans => result := ans; break
  return result
end

open Server CodeAction Elab Command RequestM in
@[command_code_action genLeanVCThms]
def genLeanVCThmsCodeAction : CommandCodeAction := fun _ _ _ node => do
  let .node _ ts := node | return #[]
  -- let res := ts.findSome? fun
  --   | .node (.ofCustomInfo { stx, value }) _ =>
  --     return (stx, (← value.get? (GenLeanVCThmsOutput)).res)
  --   | _ => none
  let res := customNodeFromTrees ts
  let some (stx, res) := res | return #[]
  let doc ← readDoc
  let eager := {
    title := "Update #gen_lean_vc_thms with output"
    kind? := "quickfix"
    edit? := .none,
    isPreferred? := true
  }
  pure #[{
    eager
    lazy? := some do
      let some start := stx.getPos? | return eager
      -- let some tail := stx.getTailPos? | return eager
      let newText := s!"/- {res} -/\n"
      pure { eager with
        edit? := some <|.ofTextEdit doc.versionedIdentifier {
          range := doc.meta.text.utf8RangeToLspRange ⟨start, start⟩
          newText
        }
      }
  }]

theorem test_thm : ¬∀ (x : Int), ¬(x == 5) = true := by
  simp_all

/-- info: Theorem test_thm is already in the environment! -/
#guard_msgs in
#gen_lean_vc_thms Lambda test_thm es[∃ (int): %0 == (#5 : int)]

/-- info: theorem eq_4_5 : (4 == 5) = true := sorry -/
#guard_msgs in
#gen_lean_vc_thms Lambda eq_4_5 es[(#4 : int) == (#5 : int)]
