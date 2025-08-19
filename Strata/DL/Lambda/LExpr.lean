/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.Identifiers
import Strata.DL.Lambda.MetaData

/-! ## Lambda Expressions with Quantifiers

Lambda expressions are formalized by the inductive type `LExpr`. Type
formalization is described in `Strata.DL.Lambda.LTy`.
-/

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)

inductive QuantifierKind
  | all
  | exist
  deriving Repr, DecidableEq

/--
Lambda Expressions with Quantifiers.

Like Lean's own expressions, we use the locally nameless
representation for this abstract syntax.
See this [paper](https://chargueraud.org/research/2009/ln/main.pdf)
for details.

We leave placeholders for type annotations only for constants
(`.const`), operations (`.op`), binders (`.abs`, `.quant`), and free
variables (`.fvar`).

LExpr is parameterized by `TypeType`, which represents
user-allowed type annotations (optional), and `Identifier` for allowed
identifiers. For a fully annotated AST, see `LExprT` that is created after the
type inference transform.
-/
inductive LExpr (TypeType : Type) (Identifier : Type) : Type where
  /-- `.const c ty`: constants (in the sense of literals). -/
  | const   (c : String) (ty : Option TypeType)
  /-- `.op c ty`: operation names. -/
  | op      (o : Identifier) (ty : Option TypeType)
  /-- `.bvar deBruijnIndex`: bound variable. -/
  | bvar    (deBruijnIndex : Nat)
  /-- `.fvar name ty`: free variable, with an option (mono)type annotation. -/
  | fvar    (name : Identifier) (ty : Option TypeType)
  | mdata   (info : Info) (e : LExpr TypeType Identifier)
  /-- `.abs ty e`: abstractions; `ty` the is type of bound variable. -/
  | abs     (ty : Option TypeType) (e : LExpr TypeType Identifier)
  /-- `.quant k ty e`: quantified expressions; `ty` the is type of bound variable. -/
  | quant   (k : QuantifierKind) (ty : Option TypeType) (e : LExpr TypeType Identifier)
  /-- `.app fn e`: function application. -/
  | app     (fn e : LExpr TypeType Identifier)
  /-- `.ite c t e`: if-then-else expression. -/
  | ite     (c t e : LExpr TypeType Identifier)
  /-- `.eq e1 e2`: equality expression. -/
  | eq      (e1 e2 : LExpr TypeType Identifier)
  deriving Repr, DecidableEq

def LExpr.all {TypeType: Type} {Identifier : Type} := @LExpr.quant TypeType Identifier .all
def LExpr.exist {TypeType: Type} {Identifier : Type} := @LExpr.quant TypeType Identifier .exist

abbrev LExpr.absUntyped {TypeType: Type} {Identifier : Type} := @LExpr.abs TypeType Identifier .none
abbrev LExpr.allUntyped {TypeType: Type} {Identifier : Type} := @LExpr.quant TypeType Identifier .all .none
abbrev LExpr.existUntyped {TypeType: Type} {Identifier : Type} := @LExpr.quant TypeType Identifier .exist .none
def LExpr.sizeOf {TypeType: Type}  [SizeOf Identifier]
  | LExpr.mdata (TypeType:=TypeType) (Identifier:=Identifier) _ e => 2 + sizeOf e
  | LExpr.abs   _ e => 2 + sizeOf e
  | LExpr.quant _ _ e => 3 + sizeOf e
  | LExpr.app fn e => 3 + sizeOf fn + sizeOf e
  | LExpr.ite c t e => 4 + sizeOf c + sizeOf t + sizeOf e
  | LExpr.eq  e1 e2 => 3 + sizeOf e1 + sizeOf e2
  | _ => 1

instance  : SizeOf (LExpr TypeType Identifier) where
  sizeOf := LExpr.sizeOf
---------------------------------------------------------------------

namespace LExpr

instance : Inhabited (LExpr TypeType Identifier) where
  default := .const "false" none

def LExpr.getVars (e : (LExpr TypeType Identifier)) := match e with
  | .const _ _ => [] | .bvar _ => [] | .op _ _ => []
  | .fvar y _ => [y]
  | .mdata _ e' => LExpr.getVars e'
  | .abs _ e' => LExpr.getVars e'
  | .quant _ _ e' => LExpr.getVars e'
  | .app e1 e2 => LExpr.getVars e1 ++ LExpr.getVars e2
  | .ite c t e => LExpr.getVars c ++ LExpr.getVars t ++ LExpr.getVars e
  | .eq e1 e2 => LExpr.getVars e1 ++ LExpr.getVars e2

def getFVarName? (e : (LExpr TypeType Identifier)) : Option Identifier :=
  match e with
  | .fvar name _ => some name
  | _ => none

def isConst (e : (LExpr TypeType Identifier)) : Bool :=
  match e with
  | .const _ _ => true
  | _ => false

@[match_pattern]
protected def true : (LExpr LMonoTy Identifier) := .const "true"  (some (.tcons "bool" []))

@[match_pattern]
protected def false : (LExpr LMonoTy Identifier) := .const "false"  (some (.tcons "bool" []))

def isTrue (e : (LExpr TypeType Identifier)) : Bool :=
  match e with
  | .const "true" _ => true
  | _ => false

def isFalse (e : (LExpr TypeType Identifier)) : Bool :=
  match e with
  | .const "false" _ => true
  | _ => false

/--
If `e` is an `LExpr` boolean, then denote that into a Lean `Bool`.
Note that we are type-agnostic here.
-/
def denoteBool (e : (LExpr LMonoTy Identifier)) : Option Bool :=
  match e with
  | .const "true"  (some (.tcons "bool" [])) => some true
  | .const "true"  none => some true
  | .const "false" (some (.tcons "bool" [])) => some false
  | .const "false" none => some false
  | _ => none

/--
If `e` is an `LExpr` integer, then denote that into a Lean `Int`.
Note that we are type-agnostic here.
-/
def denoteInt (e : (LExpr LMonoTy Identifier)) : Option Int :=
  match e with
  | .const x (some (.tcons "int" [])) => x.toInt?
  | .const x none => x.toInt?
  | _ => none

/--
If `e` is an `LExpr` real, then denote that into a Lean `String`.
Note that we are type-agnostic here.
-/
def denoteReal (e : (LExpr LMonoTy Identifier)) : Option String :=
  match e with
  | .const x (some (.tcons "real" [])) => .some x
  | .const x none => .some x
  | _ => none

/--
If `e` is an `LExpr` bv<n>, then denote that into a Lean `BitVec n`.
Note that we are type-agnostic here.
-/
def denoteBitVec (n : Nat) (e : (LExpr LMonoTy Identifier)) : Option (BitVec n) :=
  match e with
  | .const x (.some (.bitvec n')) =>
    if n == n' then .map (.ofNat n) x.toNat? else none
  | .const x none => .map (.ofNat n) x.toNat?
  | _ => none

/--
If `e` is an _annotated_ `LExpr` string, then denote that into a Lean `String`.
Note that unannotated strings are not denoted.
-/
def denoteString (e : (LExpr LMonoTy Identifier)) : Option String :=
  match e with
  | .const c  (some (.tcons "string" [])) => some c
  | _ => none

def mkApp (fn : (LExpr TypeType Identifier)) (args : List (LExpr TypeType Identifier)) : (LExpr TypeType Identifier) :=
  match args with
  | [] => fn
  | a :: rest =>
    mkApp (.app fn a) rest

/--
Does `e` have a metadata annotation? We don't check for nested metadata in `e`.
-/
def isMData (e : (LExpr TypeType Identifier)) : Bool :=
  match e with
  | .mdata _ _ => true
  | _ => false

/--
Remove the outermost metadata annotation in `e`, if any.
-/
def removeMData1 (e : (LExpr TypeType Identifier)) : (LExpr TypeType Identifier) :=
  match e with
  | .mdata _ e => e
  | _ => e

/--
Remove all metadata annotations in `e`, included nested ones.
-/
def removeAllMData (e : (LExpr TypeType Identifier)) : (LExpr TypeType Identifier) :=
  match e with
  | .const _ _ | .op _ _ | .fvar _ _ | .bvar _ => e
  | .mdata _ e1 => removeAllMData e1
  | .abs ty e1 => .abs ty (removeAllMData e1)
  | .quant qk ty e1 => .quant qk ty (removeAllMData e1)
  | .app e1 e2 => .app (removeAllMData e1) (removeAllMData e2)
  | .ite c t f => .ite (removeAllMData c) (removeAllMData t) (removeAllMData f)
  | .eq e1 e2 => .eq (removeAllMData e1) (removeAllMData e2)

/--
Compute the size of `e` as a tree.

Not optimized for execution efficiency, but can be used for termination
arguments.
-/
def size (e : (LExpr TypeType Identifier)) : Nat :=
  match e with
  | .const _ _ => 1
  | .op _ _ => 1
  | .bvar _ => 1
  | .fvar _ _ => 1
  | .abs _ e' => 1 + size e'
  | .quant _ _ e' => 1 + size e'
  | .mdata _ e' => 1 + size e'
  | .app e1 e2 => 1 + size e1 + size e2
  | .ite c t f => 1 + size c + size t + size f
  | .eq e1 e2 => 1 + size e1 + size e2

/--
Erase all type annotations from `e`.
-/
def eraseTypes (e : (LExpr TypeType Identifier)) : (LExpr TypeType Identifier) :=
  match e with
  | .const c _ => .const c none
  | .op o _ => .op o none
  | .fvar x _ => .fvar x none
  | .bvar _ => e
  | .abs ty e => .abs ty (e.eraseTypes)
  | .quant qk ty e => .quant qk ty (e.eraseTypes)
  | .app e1 e2 => .app (e1.eraseTypes) (e2.eraseTypes)
  | .ite c t f => .ite (c.eraseTypes) (t.eraseTypes) (f.eraseTypes)
  | .eq e1 e2 => .eq (e1.eraseTypes) (e2.eraseTypes)
  | .mdata m e => .mdata m (e.eraseTypes)

---------------------------------------------------------------------

/- Formatting and Parsing of Lambda Expressions -/

instance (Identifier : Type) [Repr Identifier] [Repr TypeType] : ToString (LExpr TypeType Identifier) where
   toString a := toString (repr a)

private def formatLExpr [ToFormat Identifier] [ToFormat TypeType] (e : (LExpr TypeType Identifier)) :
    Format :=
  match e with
  | .const c ty =>
    match ty with
    | none => f!"#{c}"
    | some ty => f!"(#{c} : {ty})"
  | .op c ty =>
    match ty with
    | none => f!"~{c}"
    | some ty => f!"(~{c} : {ty})"
  | .bvar i => f!"%{i}"
  | .fvar x ty =>
    match ty with
    | none => f!"{x}"
    | some ty => f!"({x} : {ty})"
  | .mdata _info e => formatLExpr e
  | .abs _ e1 => Format.paren (f!"λ {formatLExpr e1}")
  | .quant .all _ e1 => Format.paren (f!"∀ {formatLExpr e1}")
  | .quant .exist _ e1 => Format.paren (f!"∃ {formatLExpr e1}")
  | .app e1 e2 => Format.paren (formatLExpr e1 ++ " " ++ formatLExpr e2)
  | .ite c t e => Format.paren
                      ("if " ++ formatLExpr c ++
                       " then " ++ formatLExpr t ++ " else "
                       ++ formatLExpr e)
  | .eq e1 e2 => Format.paren (formatLExpr e1 ++ " == " ++ formatLExpr e2)

instance [ToFormat Identifier] [ToFormat TypeType] : ToFormat (LExpr TypeType Identifier) where
  format := formatLExpr

/-
Syntax for conveniently building `LExpr` terms with `LMonoTy`, scoped under the namespace
`LExpr.SyntaxMono`.
-/
namespace SyntaxMono
open Lean Elab Meta

class MkIdent (Identifier : Type) where
  elabIdent : Lean.Syntax → MetaM Expr
  toExpr : Expr

declare_syntax_cat lidentmono

declare_syntax_cat lexprmono

-- We expect that `LExpr` will support at least Boolean constants because
-- it includes an if-then-else construct. Here we define a syntactic category
-- for booleans, and also -- for practical reasons -- integers as well.
declare_syntax_cat lconstmono
declare_syntax_cat lnummono
scoped syntax "#" noWs num : lnummono
scoped syntax "#" noWs "-" noWs num : lnummono
scoped syntax lnummono : lconstmono
declare_syntax_cat lboolmono
scoped syntax "#true" : lboolmono
scoped syntax "#false" : lboolmono
scoped syntax lboolmono : lconstmono
scoped syntax "#" noWs ident : lconstmono
scoped syntax "(" lconstmono ":" lmonoty ")" : lconstmono
scoped syntax lconstmono : lexprmono

def elabLConstMono (Identifier : Type) [MkIdent Identifier] : Lean.Syntax → MetaM Expr
  | `(lconstmono| #$n:num)  => do
    let none ← mkNone (mkConst ``LMonoTy)
    let typeTypeExpr := mkConst ``LMonoTy
    return mkAppN (.const ``LExpr.const []) #[typeTypeExpr, MkIdent.toExpr Identifier, mkStrLit (toString n.getNat), none]
  | `(lconstmono| (#$n:num : $ty:lmonoty)) => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    let typeTypeExpr := mkConst ``LMonoTy
    return mkAppN (.const ``LExpr.const []) #[typeTypeExpr, MkIdent.toExpr Identifier, mkStrLit (toString n.getNat), lmonoty]
  | `(lconstmono| #-$n:num) => do
    let none ← mkNone (mkConst ``LMonoTy)
    let typeTypeExpr := mkConst ``LMonoTy
    return mkAppN (.const ``LExpr.const []) #[typeTypeExpr, MkIdent.toExpr Identifier, mkStrLit ("-" ++ (toString n.getNat)), none]
  | `(lconstmono| (#-$n:num : $ty:lmonoty)) => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    let typeTypeExpr := mkConst ``LMonoTy
    return mkAppN (.const ``LExpr.const []) #[typeTypeExpr, MkIdent.toExpr Identifier, mkStrLit ("-" ++ (toString n.getNat)), lmonoty]
  | `(lconstmono| #true)    => do
    let none ← mkNone (mkConst ``LMonoTy)
    let typeTypeExpr := mkConst ``LMonoTy
    return mkAppN (.const ``LExpr.const []) #[typeTypeExpr, MkIdent.toExpr Identifier, mkStrLit "true", none]
  | `(lconstmono| (#true : $ty:lmonoty))    => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    let typeTypeExpr := mkConst ``LMonoTy
    return mkAppN (.const ``LExpr.const []) #[typeTypeExpr, MkIdent.toExpr Identifier, mkStrLit "true", lmonoty]
  | `(lconstmono| #false)   =>  do
    let none ← mkNone (mkConst ``LMonoTy)
    let typeTypeExpr := mkConst ``LMonoTy
    return mkAppN (.const ``LExpr.const []) #[typeTypeExpr, MkIdent.toExpr Identifier, mkStrLit "false", none]
  | `(lconstmono| (#false : $ty:lmonoty))    => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    let typeTypeExpr := mkConst ``LMonoTy
    return mkAppN (.const ``LExpr.const []) #[typeTypeExpr, MkIdent.toExpr Identifier, mkStrLit "false", lmonoty]
  | `(lconstmono| #$s:ident) => do
    let none ← mkNone (mkConst ``LMonoTy)
    let s := toString s.getId
    let typeTypeExpr := mkConst ``LMonoTy
    return mkAppN (.const ``LExpr.const []) #[typeTypeExpr, MkIdent.toExpr Identifier, mkStrLit s, none]
  | `(lconstmono| (#$s:ident : $ty:lmonoty)) => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    let s := toString s.getId
    let typeTypeExpr := mkConst ``LMonoTy
    return mkAppN (.const ``LExpr.const []) #[typeTypeExpr, MkIdent.toExpr Identifier, mkStrLit s, lmonoty]
  | _ => throwUnsupportedSyntax

declare_syntax_cat lopmono
scoped syntax "~" noWs lidentmono : lopmono
scoped syntax "(" lopmono ":" lmonoty ")" : lopmono
scoped syntax lopmono : lexprmono

def elabLOpMono (Identifier : Type) [MkIdent Identifier] : Lean.Syntax → MetaM Expr
  | `(lopmono| ~$s:lidentmono)  => do
    let none ← mkNone (mkConst ``LMonoTy)
    let ident ← MkIdent.elabIdent Identifier s
    let typeTypeExpr := mkConst ``LMonoTy
    return mkAppN (.const ``LExpr.op []) #[typeTypeExpr, MkIdent.toExpr Identifier, ident, none]
  | `(lopmono| (~$s:lidentmono : $ty:lmonoty)) => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    mkAppM ``LExpr.op #[← MkIdent.elabIdent Identifier s, lmonoty]
  | _ => throwUnsupportedSyntax

declare_syntax_cat lbvarmono
scoped syntax "%" noWs num : lbvarmono
def elabLBVarMono (Identifier : Type) [MkIdent Identifier] : Lean.Syntax → MetaM Expr
  | `(lbvarmono| %$n:num) =>
    let typeTypeExpr := mkConst ``LMonoTy
    return mkAppN (.const ``LExpr.bvar []) #[typeTypeExpr, MkIdent.toExpr Identifier, mkNatLit n.getNat]
  | _ => throwUnsupportedSyntax
scoped syntax lbvarmono : lexprmono

declare_syntax_cat lfvarmono
scoped syntax lidentmono : lfvarmono
scoped syntax "(" lidentmono ":" lmonoty ")" : lfvarmono

def elabLFVarMono (Identifier : Type) [MkIdent Identifier] : Lean.Syntax → MetaM Expr
  | `(lfvarmono| $i:lidentmono) => do
    let none ← mkNone (mkConst ``LMonoTy)
    mkAppM ``LExpr.fvar #[← MkIdent.elabIdent Identifier i, none]
  | `(lfvarmono| ($i:lidentmono : $ty:lmonoty)) => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    mkAppM ``LExpr.fvar #[← MkIdent.elabIdent Identifier i, lmonoty]
  | _ => throwUnsupportedSyntax
scoped syntax lfvarmono : lexprmono

declare_syntax_cat mabsmono
declare_syntax_cat mallmono
declare_syntax_cat mexistmono
scoped syntax "λ" lexprmono : mabsmono
scoped syntax "λ" "(" lmonoty ")" ":" lexprmono : mabsmono
scoped syntax "∀" lexprmono : mallmono
scoped syntax "∀" "(" lmonoty ")" ":" lexprmono : mallmono
scoped syntax "∃" lexprmono : mexistmono
scoped syntax "∃" "(" lmonoty ")" ":" lexprmono : mexistmono
scoped syntax mabsmono : lexprmono
scoped syntax mallmono : lexprmono
scoped syntax mexistmono : lexprmono
declare_syntax_cat mappmono
scoped syntax "(" lexprmono lexprmono ")" : mappmono
scoped syntax mappmono : lexprmono
declare_syntax_cat meqmono
scoped syntax "==" : meqmono
scoped syntax lexprmono meqmono lexprmono : lexprmono
declare_syntax_cat mifmono
scoped syntax "if" : mifmono
scoped syntax "then" : mifmono
scoped syntax "else" : mifmono
scoped syntax mifmono lexprmono mifmono lexprmono mifmono lexprmono : lexprmono

scoped syntax "(" lexprmono ")" : lexprmono

open LTy.Syntax in
/-- Elaborator for Lambda expressions.

All type annotations in `LExpr` are for monotypes, not polytypes. It's the
user's responsibility to ensure correct usage of type variables (i.e., they're
unique).
-/
partial def elabLExprMono (Identifier : Type) [MkIdent Identifier] : Lean.Syntax → MetaM Expr
  | `(lexprmono| $c:lconstmono) => elabLConstMono Identifier c
  | `(lexprmono| $o:lopmono) => elabLOpMono Identifier o
  | `(lexprmono| $b:lbvarmono) => elabLBVarMono Identifier b
  | `(lexprmono| $f:lfvarmono) => elabLFVarMono Identifier f
  | `(lexprmono| λ $e:lexprmono) => do
     let e' ← elabLExprMono Identifier e
     let typeTypeExpr := mkConst ``LMonoTy
     return mkAppN (.const ``LExpr.absUntyped []) #[typeTypeExpr, MkIdent.toExpr Identifier, e']
  | `(lexprmono| λ ($mty:lmonoty): $e:lexprmono) => do
     let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy mty
     let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
     let e' ← elabLExprMono Identifier e
     let typeTypeExpr := mkConst ``LMonoTy
     return mkAppN (.const ``LExpr.abs []) #[typeTypeExpr, MkIdent.toExpr Identifier, lmonoty, e']
  | `(lexprmono| ∀ $e:lexprmono) => do
     let e' ← elabLExprMono Identifier e
     let typeTypeExpr := mkConst ``LMonoTy
     return mkAppN (.const ``LExpr.allUntyped []) #[typeTypeExpr, MkIdent.toExpr Identifier, e']
  | `(lexprmono| ∀ ($mty:lmonoty): $e:lexprmono) => do
     let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy mty
     let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
     let e' ← elabLExprMono Identifier e
     let typeTypeExpr := mkConst ``LMonoTy
     return mkAppN (.const ``LExpr.all []) #[typeTypeExpr, MkIdent.toExpr Identifier, lmonoty, e']
  | `(lexprmono| ∃ ($mty:lmonoty): $e:lexprmono) => do
     let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy mty
     let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
     let e' ← elabLExprMono Identifier e
     let typeTypeExpr := mkConst ``LMonoTy
     return mkAppN (.const ``LExpr.exist []) #[typeTypeExpr, MkIdent.toExpr Identifier, lmonoty, e']
  | `(lexprmono| ∃ $e:lexprmono) => do
     let e' ← elabLExprMono Identifier e
     mkAppM ``LExpr.existUntyped #[e']
  | `(lexprmono| ($e1:lexprmono $e2:lexprmono)) => do
     let e1' ← elabLExprMono Identifier e1
     let e2' ← elabLExprMono Identifier e2
     let typeTypeExpr := mkConst ``LMonoTy
     return mkAppN (.const ``LExpr.app []) #[typeTypeExpr, MkIdent.toExpr Identifier, e1', e2']
  | `(lexprmono| $e1:lexprmono == $e2:lexprmono) => do
     let e1' ← elabLExprMono Identifier e1
     let e2' ← elabLExprMono Identifier e2
     let typeTypeExpr := mkConst ``LMonoTy
     return mkAppN (.const ``LExpr.eq []) #[typeTypeExpr, MkIdent.toExpr Identifier, e1', e2']
  | `(lexprmono| if $e1:lexprmono then $e2:lexprmono else $e3:lexprmono) => do
     let e1' ← elabLExprMono Identifier e1
     let e2' ← elabLExprMono Identifier e2
     let e3' ← elabLExprMono Identifier e3
     let typeTypeExpr := mkConst ``LMonoTy
     return mkAppN (.const ``LExpr.ite []) #[typeTypeExpr, MkIdent.toExpr Identifier, e1', e2', e3']
  | `(lexprmono| ($e:lexprmono)) => elabLExprMono Identifier e
  | _ => throwUnsupportedSyntax

scoped syntax ident : lidentmono
/-- Elaborator for String identifiers, construct a String instance -/
def elabStrIdent : Lean.Syntax → MetaM Expr
  | `(lidentmono| $s:ident) => do
    let s := s.getId
    return mkStrLit s.toString
  | _ => throwUnsupportedSyntax

instance : MkIdent String where
  elabIdent := elabStrIdent
  toExpr := .const ``String []

elab "esM[" e:lexprmono "]" : term => elabLExprMono (Identifier:=String) e

open LTy.Syntax

/-- info: (bvar 0).absUntyped.app (const "5" none) : LExpr LMonoTy String -/
#guard_msgs in
#check esM[((λ %0) #5)]

/-- info: (abs (some (LMonoTy.tcons "bool" [])) (bvar 0)).app (const "true" none) : LExpr LMonoTy String -/
#guard_msgs in
#check esM[((λ (bool): %0) #true)]

/-- info: ((bvar 0).eq (const "5" none)).allUntyped : LExpr LMonoTy String -/
#guard_msgs in
#check esM[(∀ %0 == #5)]

/-- info: ((bvar 0).eq (const "5" none)).existUntyped : LExpr LMonoTy String -/
#guard_msgs in
#check esM[(∃ %0 == #5)]

/-- info: exist (some (LMonoTy.tcons "int" [])) ((bvar 0).eq (const "5" none)) : LExpr LMonoTy String -/
#guard_msgs in
#check esM[(∃ (int): %0 == #5)]

/-- info: fvar "x" (some (LMonoTy.tcons "bool" [])) : LExpr LMonoTy String -/
#guard_msgs in
#check esM[(x : bool)]

-- axiom [updateSelect]: forall m: Map k v, kk: k, vv: v :: m[kk := vv][kk] == vv;
/--
info: all (some (LMonoTy.tcons "Map" [LMonoTy.ftvar "k", LMonoTy.ftvar "v"]))
  (all (some (LMonoTy.ftvar "k"))
    (all (some (LMonoTy.ftvar "v"))
      ((((op "select"
                    (some
                      (LMonoTy.tcons "Map"
                        [LMonoTy.ftvar "k",
                          LMonoTy.tcons "arrow"
                            [LMonoTy.ftvar "v", LMonoTy.tcons "arrow" [LMonoTy.ftvar "k", LMonoTy.ftvar "v"]]]))).app
                ((((op "update"
                              (some
                                (LMonoTy.tcons "Map"
                                  [LMonoTy.ftvar "k",
                                    LMonoTy.tcons "arrow"
                                      [LMonoTy.ftvar "v",
                                        LMonoTy.tcons "arrow"
                                          [LMonoTy.ftvar "k",
                                            LMonoTy.tcons "arrow"
                                              [LMonoTy.ftvar "v",
                                                LMonoTy.tcons "Map" [LMonoTy.ftvar "k", LMonoTy.ftvar "v"]]]]]))).app
                          (bvar 2)).app
                      (bvar 1)).app
                  (bvar 0))).app
            (bvar 1)).eq
        (bvar 0)))) : LExpr LMonoTy String
-/
#guard_msgs in
#check
  esM[∀ (Map %k %v):
            (∀ (%k):
               (∀ (%v):
                  (((~select : Map %k %v → %k → %v)
                     ((((~update : Map %k %v → %k → %v → Map %k %v) %2) %1) %0)) %1) == %0))]

end SyntaxMono



/-
Syntax for conveniently building `LExpr` terms with `LTy`, scoped under the namespace
`LExpr.Syntax`.
-/
namespace Syntax
open Lean Elab Meta

class MkIdent (Identifier : Type) where
  elabIdent : Lean.Syntax → MetaM Expr
  toExpr : Expr

declare_syntax_cat lident

declare_syntax_cat lexpr

-- We expect that `LExpr` will support at least Boolean constants because
-- it includes an if-then-else construct. Here we define a syntactic category
-- for booleans, and also -- for practical reasons -- integers as well.
declare_syntax_cat lconst
declare_syntax_cat lnum
scoped syntax "#" noWs num : lnum
scoped syntax "#" noWs "-" noWs num : lnum
scoped syntax lnum : lconst
declare_syntax_cat lbool
scoped syntax "#true" : lbool
scoped syntax "#false" : lbool
scoped syntax lbool : lconst
scoped syntax "#" noWs ident : lconst
scoped syntax "(" lconst ":" lty ")" : lconst
scoped syntax lconst : lexpr

def elabLConst (Identifier : Type) [MkIdent Identifier] : Lean.Syntax → MetaM Expr
  | `(lconst| #$n:num)  => do
    let none ← mkNone (mkConst ``LTy)
    let typeTypeExpr := mkConst ``LTy
    return mkAppN (.const ``LExpr.const []) #[typeTypeExpr, MkIdent.toExpr Identifier, mkStrLit (toString n.getNat), none]
  | `(lconst| (#$n:num : $ty:lty)) => do
    let lty ← Lambda.LTy.Syntax.elabLTy ty
    let lty ← mkSome (mkConst ``LTy) lty
    let typeTypeExpr := mkConst ``LTy
    return mkAppN (.const ``LExpr.const []) #[typeTypeExpr, MkIdent.toExpr Identifier, mkStrLit (toString n.getNat), lty]
  | `(lconst| #-$n:num) => do
    let none ← mkNone (mkConst ``LTy)
    let typeTypeExpr := mkConst ``LTy
    return mkAppN (.const ``LExpr.const []) #[typeTypeExpr, MkIdent.toExpr Identifier, mkStrLit ("-" ++ (toString n.getNat)), none]
  | `(lconst| (#-$n:num : $ty:lty)) => do
    let lty ← Lambda.LTy.Syntax.elabLTy ty
    let lty ← mkSome (mkConst ``LTy) lty
    let typeTypeExpr := mkConst ``LTy
    return mkAppN (.const ``LExpr.const []) #[typeTypeExpr, MkIdent.toExpr Identifier, mkStrLit ("-" ++ (toString n.getNat)), lty]
  | `(lconst| #true)    => do
    let none ← mkNone (mkConst ``LTy)
    let typeTypeExpr := mkConst ``LTy
    return mkAppN (.const ``LExpr.const []) #[typeTypeExpr, MkIdent.toExpr Identifier, mkStrLit "true", none]
  | `(lconst| (#true : $ty:lty))    => do
    let lty ← Lambda.LTy.Syntax.elabLTy ty
    let lty ← mkSome (mkConst ``LTy) lty
    let typeTypeExpr := mkConst ``LTy
    return mkAppN (.const ``LExpr.const []) #[typeTypeExpr, MkIdent.toExpr Identifier, mkStrLit "true", lty]
  | `(lconst| #false)   =>  do
    let none ← mkNone (mkConst ``LTy)
    let typeTypeExpr := mkConst ``LTy
    return mkAppN (.const ``LExpr.const []) #[typeTypeExpr, MkIdent.toExpr Identifier, mkStrLit "false", none]
  | `(lconst| (#false : $ty:lty))    => do
    let lty ← Lambda.LTy.Syntax.elabLTy ty
    let lty ← mkSome (mkConst ``LTy) lty
    let typeTypeExpr := mkConst ``LTy
    return mkAppN (.const ``LExpr.const []) #[typeTypeExpr, MkIdent.toExpr Identifier, mkStrLit "false", lty]
  | `(lconst| #$s:ident) => do
    let none ← mkNone (mkConst ``LTy)
    let s := toString s.getId
    let typeTypeExpr := mkConst ``LTy
    return mkAppN (.const ``LExpr.const []) #[typeTypeExpr, MkIdent.toExpr Identifier, mkStrLit s, none]
  | `(lconst| (#$s:ident : $ty:lty)) => do
    let lty ← Lambda.LTy.Syntax.elabLTy ty
    let lty ← mkSome (mkConst ``LTy) lty
    let s := toString s.getId
    let typeTypeExpr := mkConst ``LTy
    return mkAppN (.const ``LExpr.const []) #[typeTypeExpr, MkIdent.toExpr Identifier, mkStrLit s, lty]
  | _ => throwUnsupportedSyntax

declare_syntax_cat lop
scoped syntax "~" noWs lident : lop
scoped syntax "(" lop ":" lty ")" : lop
scoped syntax lop : lexpr

def elabLOp (Identifier : Type) [MkIdent Identifier] : Lean.Syntax → MetaM Expr
  | `(lop| ~$s:lident)  => do
    let none ← mkNone (mkConst ``LTy)
    let ident ← MkIdent.elabIdent Identifier s
    let typeTypeExpr := mkConst ``LTy
    return mkAppN (.const ``LExpr.op []) #[typeTypeExpr, MkIdent.toExpr Identifier, ident, none]
  | `(lop| (~$s:lident : $ty:lty)) => do
    let lty ← Lambda.LTy.Syntax.elabLTy ty
    let lty ← mkSome (mkConst ``LTy) lty
    mkAppM ``LExpr.op #[← MkIdent.elabIdent Identifier s, lty]
  | _ => throwUnsupportedSyntax

declare_syntax_cat lbvar
scoped syntax "%" noWs num : lbvar
def elabLBVar (Identifier : Type) [MkIdent Identifier] : Lean.Syntax → MetaM Expr
  | `(lbvar| %$n:num) =>
    let typeTypeExpr := mkConst ``LTy
    return mkAppN (.const ``LExpr.bvar []) #[typeTypeExpr, MkIdent.toExpr Identifier, mkNatLit n.getNat]
  | _ => throwUnsupportedSyntax
scoped syntax lbvar : lexpr

declare_syntax_cat lfvar
scoped syntax lident : lfvar
scoped syntax "(" lident ":" lty ")" : lfvar

def elabLFVar (Identifier : Type) [MkIdent Identifier] : Lean.Syntax → MetaM Expr
  | `(lfvar| $i:lident) => do
    let none ← mkNone (mkConst ``LTy)
    mkAppM ``LExpr.fvar #[← MkIdent.elabIdent Identifier i, none]
  | `(lfvar| ($i:lident : $ty:lty)) => do
    let lty ← Lambda.LTy.Syntax.elabLTy ty
    let lty ← mkSome (mkConst ``LTy) lty
    mkAppM ``LExpr.fvar #[← MkIdent.elabIdent Identifier i, lty]
  | _ => throwUnsupportedSyntax
scoped syntax lfvar : lexpr

declare_syntax_cat mabs
declare_syntax_cat mall
declare_syntax_cat mexist
scoped syntax "λ" lexpr : mabs
scoped syntax "λ" "(" lty ")" ":" lexpr : mabs
scoped syntax "∀" lexpr : mall
scoped syntax "∀" "(" lty ")" ":" lexpr : mall
scoped syntax "∃" lexpr : mexist
scoped syntax "∃" "(" lty ")" ":" lexpr : mexist
scoped syntax mabs : lexpr
scoped syntax mall : lexpr
scoped syntax mexist : lexpr
declare_syntax_cat mapp
scoped syntax "(" lexpr lexpr ")" : mapp
scoped syntax mapp : lexpr
declare_syntax_cat meq
scoped syntax "==" : meq
scoped syntax lexpr meq lexpr : lexpr
declare_syntax_cat mif
scoped syntax "if" : mif
scoped syntax "then" : mif
scoped syntax "else" : mif
scoped syntax mif lexpr mif lexpr mif lexpr : lexpr

scoped syntax "(" lexpr ")" : lexpr

open LTy.Syntax in
/-- Elaborator for Lambda expressions.

It's the user's responsibility to ensure correct usage of type variables (i.e., they're
unique).
-/
partial def elabLExpr (Identifier : Type) [MkIdent Identifier] : Lean.Syntax → MetaM Expr
  | `(lexpr| $c:lconst) => elabLConst Identifier c
  | `(lexpr| $o:lop) => elabLOp Identifier o
  | `(lexpr| $b:lbvar) => elabLBVar Identifier b
  | `(lexpr| $f:lfvar) => elabLFVar Identifier f
  | `(lexpr| λ $e:lexpr) => do
     let e' ← elabLExpr Identifier e
     let typeTypeExpr := mkConst ``LTy
     return mkAppN (.const ``LExpr.absUntyped []) #[typeTypeExpr, MkIdent.toExpr Identifier, e']
  | `(lexpr| λ ($mty:lty): $e:lexpr) => do
     let lty ← Lambda.LTy.Syntax.elabLTy mty
     let lty ← mkSome (mkConst ``LTy) lty
     let e' ← elabLExpr Identifier e
     let typeTypeExpr := mkConst ``LTy
     return mkAppN (.const ``LExpr.abs []) #[typeTypeExpr, MkIdent.toExpr Identifier, lty, e']
  | `(lexpr| ∀ $e:lexpr) => do
     let e' ← elabLExpr Identifier e
     let typeTypeExpr := mkConst ``LTy
     return mkAppN (.const ``LExpr.allUntyped []) #[typeTypeExpr, MkIdent.toExpr Identifier, e']
  | `(lexpr| ∀ ($mty:lty): $e:lexpr) => do
     let lty ← Lambda.LTy.Syntax.elabLTy mty
     let lty ← mkSome (mkConst ``LTy) lty
     let e' ← elabLExpr Identifier e
     let typeTypeExpr := mkConst ``LTy
     return mkAppN (.const ``LExpr.all []) #[typeTypeExpr, MkIdent.toExpr Identifier, lty, e']
  | `(lexpr| ∃ ($mty:lty): $e:lexpr) => do
     let lty ← Lambda.LTy.Syntax.elabLTy mty
     let lty ← mkSome (mkConst ``LTy) lty
     let e' ← elabLExpr Identifier e
     let typeTypeExpr := mkConst ``LTy
     return mkAppN (.const ``LExpr.exist []) #[typeTypeExpr, MkIdent.toExpr Identifier, lty, e']
  | `(lexpr| ∃ $e:lexpr) => do
     let e' ← elabLExpr Identifier e
     mkAppM ``LExpr.existUntyped #[e']
  | `(lexpr| ($e1:lexpr $e2:lexpr)) => do
     let e1' ← elabLExpr Identifier e1
     let e2' ← elabLExpr Identifier e2
     let typeTypeExpr := mkConst ``LTy
     return mkAppN (.const ``LExpr.app []) #[typeTypeExpr, MkIdent.toExpr Identifier, e1', e2']
  | `(lexpr| $e1:lexpr == $e2:lexpr) => do
     let e1' ← elabLExpr Identifier e1
     let e2' ← elabLExpr Identifier e2
     let typeTypeExpr := mkConst ``LTy
     return mkAppN (.const ``LExpr.eq []) #[typeTypeExpr, MkIdent.toExpr Identifier, e1', e2']
  | `(lexpr| if $e1:lexpr then $e2:lexpr else $e3:lexpr) => do
     let e1' ← elabLExpr Identifier e1
     let e2' ← elabLExpr Identifier e2
     let e3' ← elabLExpr Identifier e3
     let typeTypeExpr := mkConst ``LTy
     return mkAppN (.const ``LExpr.ite []) #[typeTypeExpr, MkIdent.toExpr Identifier, e1', e2', e3']
  | `(lexpr| ($e:lexpr)) => elabLExpr Identifier e
  | _ => throwUnsupportedSyntax

scoped syntax ident : lident
/-- Elaborator for String identifiers, construct a String instance -/
def elabStrIdent : Lean.Syntax → MetaM Expr
  | `(lident| $s:ident) => do
    let s := s.getId
    return mkStrLit s.toString
  | _ => throwUnsupportedSyntax

instance : MkIdent String where
  elabIdent := elabStrIdent
  toExpr := .const ``String []

elab "es[" e:lexpr "]" : term => elabLExpr (Identifier:=String) e

open LTy.Syntax

/-- info: (bvar 0).absUntyped.app (const "5" none) : LExpr LTy String -/
#guard_msgs in
#check es[((λ %0) #5)]

/-- info: (abs (some (LTy.forAll [] (LMonoTy.tcons "bool" []))) (bvar 0)).app (const "true" none) : LExpr LTy String -/
#guard_msgs in
#check es[((λ (bool): %0) #true)]

/-- info: ((bvar 0).eq (const "5" none)).allUntyped : LExpr LTy String -/
#guard_msgs in
#check es[(∀ %0 == #5)]

/-- info: ((bvar 0).eq (const "5" none)).existUntyped : LExpr LTy String -/
#guard_msgs in
#check es[(∃ %0 == #5)]

/-- info: exist (some (LTy.forAll [] (LMonoTy.tcons "int" []))) ((bvar 0).eq (const "5" none)) : LExpr LTy String -/
#guard_msgs in
#check es[(∃ (int): %0 == #5)]

/-- info: fvar "x" (some (LTy.forAll [] (LMonoTy.tcons "bool" []))) : LExpr LTy String -/
#guard_msgs in
#check es[(x : bool)]

-- axiom [updateSelect]: forall m: Map k v, kk: k, vv: v :: m[kk := vv][kk] == vv;
/--
info: all (some (LTy.forAll [] (LMonoTy.tcons "Map" [LMonoTy.ftvar "k", LMonoTy.ftvar "v"])))
  (all (some (LTy.forAll [] (LMonoTy.ftvar "k")))
    (all (some (LTy.forAll [] (LMonoTy.ftvar "v")))
      ((((op "select"
                    (some
                      (LTy.forAll []
                        (LMonoTy.tcons "Map"
                          [LMonoTy.ftvar "k",
                            LMonoTy.tcons "arrow"
                              [LMonoTy.ftvar "v", LMonoTy.tcons "arrow" [LMonoTy.ftvar "k", LMonoTy.ftvar "v"]]])))).app
                ((((op "update"
                              (some
                                (LTy.forAll []
                                  (LMonoTy.tcons "Map"
                                    [LMonoTy.ftvar "k",
                                      LMonoTy.tcons "arrow"
                                        [LMonoTy.ftvar "v",
                                          LMonoTy.tcons "arrow"
                                            [LMonoTy.ftvar "k",
                                              LMonoTy.tcons "arrow"
                                                [LMonoTy.ftvar "v",
                                                  LMonoTy.tcons "Map" [LMonoTy.ftvar "k", LMonoTy.ftvar "v"]]]]])))).app
                          (bvar 2)).app
                      (bvar 1)).app
                  (bvar 0))).app
            (bvar 1)).eq
        (bvar 0)))) : LExpr LTy String
-/
#guard_msgs in
#check
  es[∀ (Map %k %v):
            (∀ (%k):
               (∀ (%v):
                  (((~select : Map %k %v → %k → %v)
                     ((((~update : Map %k %v → %k → %v → Map %k %v) %2) %1) %0)) %1) == %0))]

end Syntax

---------------------------------------------------------------------

end LExpr
end Lambda
