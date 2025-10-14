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
  /-- `.quant k ty tr e`: quantified expressions; `ty` the is type of bound variable, and `tr` the trigger. -/
  | quant   (k : QuantifierKind) (ty : Option TypeType) (trigger: LExpr TypeType Identifier) (e : LExpr TypeType Identifier)
  /-- `.app fn e`: function application. -/
  | app     (fn e : LExpr TypeType Identifier)
  /-- `.ite c t e`: if-then-else expression. -/
  | ite     (c t e : LExpr TypeType Identifier)
  /-- `.eq e1 e2`: equality expression. -/
  | eq      (e1 e2 : LExpr TypeType Identifier)
  | dontcare -- assume false
  | error    -- assert false
  | choose (t: Option TypeType) -- like fvar, except that it might return a different value every time
  | skip     -- returns the environment or unit
  deriving Repr, DecidableEq

def LExpr.noTrigger {TypeType: Type} {Identifier : Type} : LExpr TypeType Identifier := .bvar 0
def LExpr.allTr {TypeType: Type} {Identifier : Type} (ty : Option TypeType) := @LExpr.quant TypeType Identifier .all ty
def LExpr.all {TypeType: Type} {Identifier : Type} (ty : Option TypeType) := @LExpr.quant TypeType Identifier .all ty LExpr.noTrigger
def LExpr.existTr {TypeType: Type} {Identifier : Type} (ty : Option TypeType) := @LExpr.quant TypeType Identifier .exist ty
def LExpr.exist {TypeType: Type} {Identifier : Type} (ty : Option TypeType) := @LExpr.quant TypeType Identifier .exist ty LExpr.noTrigger

abbrev LExpr.absUntyped {TypeType: Type} {Identifier : Type} := @LExpr.abs TypeType Identifier .none
abbrev LExpr.allUntypedTr {TypeType: Type} {Identifier : Type} := @LExpr.quant TypeType Identifier .all .none
abbrev LExpr.allUntyped {TypeType: Type} {Identifier : Type} := @LExpr.quant TypeType Identifier .all .none LExpr.noTrigger
abbrev LExpr.existUntypedTr {TypeType: Type} {Identifier : Type} := @LExpr.quant TypeType Identifier .exist .none
abbrev LExpr.existUntyped {TypeType: Type} {Identifier : Type} := @LExpr.quant TypeType Identifier .exist .none LExpr.noTrigger


def LExpr.sizeOf {TypeType: Type}  [SizeOf Identifier]
  | LExpr.mdata (TypeType:=TypeType) (Identifier:=Identifier) _ e => 2 + sizeOf e
  | LExpr.abs   _ e => 2 + sizeOf e
  | LExpr.quant _ _ tr e => 3 + sizeOf e + sizeOf tr
  | LExpr.app fn e => 3 + sizeOf fn + sizeOf e
  | LExpr.ite c t e => 4 + sizeOf c + sizeOf t + sizeOf e
  | LExpr.eq  e1 e2 => 3 + sizeOf e1 + sizeOf e2
  | LExpr.choose _ => 1
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
  | .quant _ _ tr' e' => LExpr.getVars tr' ++ LExpr.getVars e'
  | .app e1 e2 => LExpr.getVars e1 ++ LExpr.getVars e2
  | .ite c t e => LExpr.getVars c ++ LExpr.getVars t ++ LExpr.getVars e
  | .eq e1 e2 => LExpr.getVars e1 ++ LExpr.getVars e2
  | .dontcare => []
  | .error => []
  | .choose _ => []
  | .skip => []

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
  | .quant qk ty tr e1 => .quant qk ty (removeAllMData tr) (removeAllMData e1)
  | .app e1 e2 => .app (removeAllMData e1) (removeAllMData e2)
  | .ite c t f => .ite (removeAllMData c) (removeAllMData t) (removeAllMData f)
  | .eq e1 e2 => .eq (removeAllMData e1) (removeAllMData e2)
  | .dontcare => .dontcare
  | .error => .error
  | .choose ty => .choose ty
  | .skip => .skip

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
  | .quant _ _ _ e' => 1 + size e'
  | .mdata _ e' => 1 + size e'
  | .app e1 e2 => 1 + size e1 + size e2
  | .ite c t f => 1 + size c + size t + size f
  | .eq e1 e2 => 1 + size e1 + size e2
  | .dontcare => 1
  | .error => 1
  | .choose _ => 1
  | .skip => 1

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
  | .quant qk ty tr e => .quant qk ty (eraseTypes tr) (e.eraseTypes)
  | .app e1 e2 => .app (e1.eraseTypes) (e2.eraseTypes)
  | .ite c t f => .ite (c.eraseTypes) (t.eraseTypes) (f.eraseTypes)
  | .eq e1 e2 => .eq (e1.eraseTypes) (e2.eraseTypes)
  | .mdata m e => .mdata m (e.eraseTypes)
  | .dontcare => .dontcare
  | .error => .error
  | .choose _ => .choose none
  | .skip => .skip

---------------------------------------------------------------------

/- Formatting and Parsing of Lambda Expressions -/

instance (Identifier : Type) [Repr Identifier] [Repr TypeType] : ToString (LExpr TypeType Identifier) where
   toString a := toString (repr a)

def zeroVarContinuation (e : (LExpr TypeType Identifier)) : Bool :=
  match e with
  | .ite _ _ .error => true --heuristic for formatting
  | .skip => true
  | _ => false

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
  | .quant .all _ _ e1 => Format.paren (f!"∀ {formatLExpr e1}")
  | .quant .exist _ _ e1 => Format.paren (f!"∃ {formatLExpr e1}")
  | .app (.app (.abs _ (.abs _ (.bvar 0))) a) b =>
      f!"pushpop ({Format.line}  {Format.nest 2 (formatLExpr a)}{Format.line}) <|{Format.line}{formatLExpr b}"
  | .app (.abs _ e1) (.choose ty) =>
      match ty with
      | none => f!"let %;{Format.line}{formatLExpr e1}"
      | some ty => f!"let % : {ty};{Format.line}{formatLExpr e1}"
  | .app (.abs ty e1) (.abs ty2 cont) => -- Continuation-passing style
      let absTy :=
        match ty2 with
        | none => f!""
        | some ty => f!" : {ty}"
      f!"({formatLExpr (.abs ty e1)}) <| λ{absTy}{Format.line}{formatLExpr cont}"
  | .app (.abs ty e1) rhs =>
      -- It could also be that rhs is a zero-variable continuation. This ought to be metadata
      if zeroVarContinuation rhs then
        f!"({formatLExpr (.abs ty e1)}) <|{Format.line}{formatLExpr rhs}"
      else
        match ty with
        | none => f!"let % := {formatLExpr rhs};{Format.line}{formatLExpr e1}"
        | some ty => f!"let % : {ty} := {formatLExpr rhs};{Format.line}{formatLExpr e1}"
  | .app e1 e2 => Format.paren (f!"{formatLExpr e1} {formatLExpr e2}")
  | .ite c t e =>
    match e with
    | .dontcare => -- assume statement
        f!"assume {formatLExpr c} <|{Format.line}{formatLExpr t}"
    | .error => -- assert statement
        f!"assert {formatLExpr c} <|{Format.line}{formatLExpr t}"
    | _ =>
    Format.paren f!"if {formatLExpr c} then {Format.nest 2 (formatLExpr t)}{Format.line}else {Format.nest 2 (formatLExpr e)}"
  | .eq e1 e2 => Format.paren (formatLExpr e1 ++ " == " ++ formatLExpr e2)
  | .dontcare => "dontcare"
  | .error => "error"
  | .skip => "skip"
  | .choose ty =>
    match ty with
    | none => Format.paren (f!"*")
    | some ty => Format.paren (f!"(* : {ty})")

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
scoped syntax "∀" "{" lexprmono "}" lexprmono : mallmono
scoped syntax "∀" "(" lmonoty ")" ":" lexprmono : mallmono
scoped syntax "∀" "(" lmonoty ")" ":" "{" lexprmono "}" lexprmono : mallmono
scoped syntax "∃" lexprmono : mexistmono
scoped syntax "∃" "{" lexprmono "}" lexprmono : mexistmono
scoped syntax "∃" "(" lmonoty ")" ":" lexprmono : mexistmono
scoped syntax "∃" "(" lmonoty ")" ":" "{" lexprmono "}" lexprmono : mexistmono
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
  | `(lexprmono| ∀ {$tr}$e:lexprmono) => do
     let e' ← elabLExprMono Identifier e
     let tr' ← elabLExprMono Identifier tr
     let typeTypeExpr := mkConst ``LMonoTy
     return mkAppN (.const ``LExpr.allUntypedTr []) #[typeTypeExpr, MkIdent.toExpr Identifier, tr', e']
  | `(lexprmono| ∀ ($mty:lmonoty): $e:lexprmono) => do
     let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy mty
     let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
     let e' ← elabLExprMono Identifier e
     let typeTypeExpr := mkConst ``LMonoTy
     return mkAppN (.const ``LExpr.all []) #[typeTypeExpr, MkIdent.toExpr Identifier, lmonoty, e']
  | `(lexprmono| ∀ ($mty:lmonoty):{$tr} $e:lexprmono) => do
     let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy mty
     let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
     let e' ← elabLExprMono Identifier e
     let tr' ← elabLExprMono Identifier tr
     let typeTypeExpr := mkConst ``LMonoTy
     return mkAppN (.const ``LExpr.allTr []) #[typeTypeExpr, MkIdent.toExpr Identifier, lmonoty, tr', e']
  | `(lexprmono| ∃ ($mty:lmonoty): $e:lexprmono) => do
     let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy mty
     let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
     let e' ← elabLExprMono Identifier e
     let typeTypeExpr := mkConst ``LMonoTy
     return mkAppN (.const ``LExpr.exist []) #[typeTypeExpr, MkIdent.toExpr Identifier, lmonoty, e']
  | `(lexprmono| ∃ ($mty:lmonoty):{$tr} $e:lexprmono) => do
     let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy mty
     let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
     let e' ← elabLExprMono Identifier e
     let tr' ← elabLExprMono Identifier tr
     let typeTypeExpr := mkConst ``LMonoTy
     return mkAppN (.const ``LExpr.existTr []) #[typeTypeExpr, MkIdent.toExpr Identifier, lmonoty, tr', e']
  | `(lexprmono| ∃ $e:lexprmono) => do
     let e' ← elabLExprMono Identifier e
     mkAppM ``LExpr.existUntyped #[e']
  | `(lexprmono| ∃{$tr} $e:lexprmono) => do
     let e' ← elabLExprMono Identifier e
     let tr' ← elabLExprMono Identifier tr
     mkAppM ``LExpr.existUntypedTr #[tr', e']
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
scoped syntax "∀" "{" lexpr "}" lexpr : mall
scoped syntax "∀" "(" lty ")" ":" lexpr : mall
scoped syntax "∀" "(" lty ")" ":" "{" lexpr "}" lexpr : mall
scoped syntax "∃" lexpr : mexist
scoped syntax "∃" "{" lexpr "}" lexpr : mexist
scoped syntax "∃" "(" lty ")" ":" lexpr : mexist
scoped syntax "∃" "(" lty ")" ":" "{" lexpr "}" lexpr : mexist
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
  | `(lexpr| ∀{$tr}$e:lexpr) => do
     let e' ← elabLExpr Identifier e
     let tr' ← elabLExpr Identifier tr
     let typeTypeExpr := mkConst ``LTy
     return mkAppN (.const ``LExpr.allUntypedTr []) #[typeTypeExpr, MkIdent.toExpr Identifier, tr', e']
  | `(lexpr| ∀ ($mty:lty): $e:lexpr) => do
     let lty ← Lambda.LTy.Syntax.elabLTy mty
     let lty ← mkSome (mkConst ``LTy) lty
     let e' ← elabLExpr Identifier e
     let typeTypeExpr := mkConst ``LTy
     return mkAppN (.const ``LExpr.all []) #[typeTypeExpr, MkIdent.toExpr Identifier, lty, e']
  | `(lexpr| ∀ ($mty:lty): {$tr}$e:lexpr) => do
     let lty ← Lambda.LTy.Syntax.elabLTy mty
     let lty ← mkSome (mkConst ``LTy) lty
     let e' ← elabLExpr Identifier e
     let tr' ← elabLExpr Identifier tr
     let typeTypeExpr := mkConst ``LTy
     return mkAppN (.const ``LExpr.allTr []) #[typeTypeExpr, MkIdent.toExpr Identifier, lty, tr', e']
  | `(lexpr| ∃ ($mty:lty): $e:lexpr) => do
     let lty ← Lambda.LTy.Syntax.elabLTy mty
     let lty ← mkSome (mkConst ``LTy) lty
     let e' ← elabLExpr Identifier e
     let typeTypeExpr := mkConst ``LTy
     return mkAppN (.const ``LExpr.exist []) #[typeTypeExpr, MkIdent.toExpr Identifier, lty, e']
  | `(lexpr| ∃ ($mty:lty): {$tr}$e:lexpr) => do
     let lty ← Lambda.LTy.Syntax.elabLTy mty
     let lty ← mkSome (mkConst ``LTy) lty
     let e' ← elabLExpr Identifier e
     let tr' ← elabLExpr Identifier tr
     let typeTypeExpr := mkConst ``LTy
     return mkAppN (.const ``LExpr.existTr []) #[typeTypeExpr, MkIdent.toExpr Identifier, lty, tr', e']
  | `(lexpr| ∃ $e:lexpr) => do
     let e' ← elabLExpr Identifier e
     mkAppM ``LExpr.existUntyped #[e']
  | `(lexpr| ∃ {$tr} $e:lexpr) => do
     let e' ← elabLExpr Identifier e
     let tr' ← elabLExpr Identifier tr
     mkAppM ``LExpr.existUntypedTr #[tr', e']
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
-- Proof of concept of encoding everything in NLambda calculus

def _Bool : Option LTy := .some <| LTy.forAll [] (LMonoTy.tcons "bool" [])
def _Int : Option LTy := .some <| LTy.forAll [] (LMonoTy.tcons "int" [])
def _String : Option LTy := .some <| LTy.forAll [] (LMonoTy.tcons "string" [])

inductive Context (Identifier : Type) : Type where
  | topLevel : Context Identifier
  | extend
    (tail : Context Identifier)
    (id : Identifier)
    (overrideIndex : Option Nat)
    -- If .some, this variable is supposed to be an override of the variable declared at the given index
    -- which should have a .none
    (indexFromLast : Nat): Context Identifier
deriving Repr

def Context.frame [DecidableEq Identifier] (c: Context Identifier): List Identifier :=
  match c with
  | .topLevel => []
  | .extend tail _ (.some _) _ =>
    -- This seems wrong as there could be shadowings.
    -- Also, we don't want to include procedures.
    tail.frame
  | .extend tail id .none _ =>
    let tailframe := tail.frame
    if id ∈ tailframe then
      tailframe
    else
      id :: tailframe

def Context.size {Identifier : Type} (c : Context Identifier) : Nat :=
  match c with
  | .topLevel => 0
  | .extend _ _ _ s => s + 1

def Context.nameOf (c : Context String) (n: Nat): String :=
  let rec go : Context String → Nat → String
    | .topLevel, _ => "UNDEFINED"
    | .extend _ id' _ _, 0 => id'
    | .extend c' _ _ _, n+1 => go c' n
  go c n

--
def Context.lastIndexOf [DecidableEq Identifier] (c : Context Identifier) (id: Identifier): Nat :=
  let rec go : Context Identifier → Nat
    | .topLevel => 0
    | .extend tail id' _ n => if id == id' then n else go tail
  go c


def Context.add_declare {Identifier : Type} (c : Context Identifier) (id : Identifier) : Context Identifier :=
  Context.extend c id (overrideIndex := .none) (match c with
    | .topLevel => 0
    | .extend _ _ _ s => s + 1)

def Context.add_assign {Identifier : Type} [DecidableEq Identifier] (c : Context Identifier) (id : Identifier) : Context Identifier :=
  let overrideIndex: Nat := c.lastIndexOf id
  Context.extend c id (.some overrideIndex) (match c with
    | .topLevel => 0
    | .extend _ _ _ s => s + 1)

def Context.vOffset [DecidableEq Identifier]: Identifier → Context Identifier → Nat → LExpr TypeType Identifier
  | _, .topLevel, _ => .bvar 0
  | id, .extend c' id' _ _, n =>
    if id == id' then
      LExpr.bvar n
    else
      vOffset id c' (n + 1)

-- Returns a bvar corresponding of the index of the identifier in the context
-- TODO: Add error if identifier not found
def Context.v {Identifier : Type} [DecidableEq Identifier] (c : Context Identifier) (id : Identifier) : LExpr TypeType Identifier :=
  c.vOffset id 0

def Context.vLastAssigned {Identifier : Type}
  [DecidableEq Identifier]
  (c cInit : Context Identifier)
  -- Assuming cInit is a prefix of c, we want to know which identifier in c corresponds to last identifier in cInit
  -- which was last assigned in c
  (id : Identifier) : LExpr TypeType Identifier :=
  let rec go : Context Identifier → Option (LExpr TypeType Identifier) → Nat → LExpr TypeType Identifier
    | .topLevel, _, _ => .bvar 123456789 -- Should not happen!
    | .extend c' id' overrideIndex _, candidate, n =>
      if n + 1 == cInit.size then
        match candidate with
        | .some candidate => candidate
        | .none => -- There were no assignments or they all lead to declarations when walking in reverse, such as
          -- cInit
          -- var i;  -- 3.candidate == .none     because it was a local declaration since cInit
          -- i := 2; -- 2.candidate == .some 0
          --         -- 1.candidate == none
          cInit.vOffset id (c.size - (n + 1)) -- Hence we take the last assignment or declaration in the initial context.
      else
        if id == id' then
          match overrideIndex with
          | .none => go c' .none (n + 1)
          | .some _ => go c' (.some (LExpr.bvar n)) (n + 1)
        else
          go c' candidate (n + 1)
  go c .none 0


def procedure_lambda {Identifier : Type} {TypeType: Type} [DecidableEq Identifier]
  (c : Context Identifier) (id : Identifier) (ty: Option TypeType) (cont: Context Identifier -> LExpr TypeType Identifier): LExpr TypeType Identifier :=
  abs ty <|
    let c': Context Identifier := c.add_declare id
    cont c'

def opcall1 [DecidableEq Identifier] (name: Identifier) (arg: LExpr TypeType Identifier): LExpr TypeType Identifier :=
  .app (.op name .none) arg

def opcall2 [DecidableEq Identifier] (name: Identifier) (arg arg2: LExpr TypeType Identifier): LExpr TypeType Identifier :=
  .app (.app (.op name .none) arg) arg2

def call1 [DecidableEq Identifier] (c: Context Identifier) (name: Identifier) (arg: LExpr TypeType Identifier): LExpr TypeType Identifier :=
  .app (c.v name) arg

def call1_1 [DecidableEq Identifier] (c: Context Identifier) (name: Identifier) (arg: LExpr TypeType Identifier) (out: Identifier) (cont: Context Identifier -> LExpr TypeType Identifier): LExpr TypeType Identifier :=
  .app (.app (c.v name) arg) <| abs .none <|
    let c := c.add_assign out
    cont c

def choose_abs (ty: Option TypeType) (l: LExpr TypeType Identifier) : LExpr TypeType Identifier :=
  .app l (.choose ty)

-- Declare a new variable without RHS
def let_ {Identifier : Type} (c: Context Identifier) (id : Identifier) (ty: Option TypeType) (k : Context Identifier → LExpr TypeType Identifier) : LExpr TypeType Identifier :=
  let c: Context Identifier := .add_declare c id
  choose_abs ty <| LExpr.abs ty <| k c

-- Declare a new variable and assign it a value
def let_assign {Identifier : Type} (c: Context Identifier) (id : Identifier) (ty: Option TypeType) (rhs : LExpr TypeType Identifier) (k : Context Identifier → LExpr TypeType Identifier) : LExpr TypeType Identifier :=
  let c : Context Identifier := .add_declare c id
  .app (.abs ty (k c)) rhs

def assign {Identifier : Type} [DecidableEq Identifier] (c: Context Identifier) (id : Identifier) (ty: Option TypeType) (rhs : LExpr TypeType Identifier) (k : Context Identifier → LExpr TypeType Identifier) : LExpr TypeType Identifier :=
  let c : Context Identifier := .add_assign c id
  .app (.abs ty (k c)) rhs

def procedure  {Identifier : Type} {TypeType: Type} [DecidableEq Identifier]
  (c : Context Identifier)
  (name: Identifier) (args: List (Identifier × Option TypeType)) (body: Context Identifier -> LExpr TypeType Identifier)
  (cont: Context Identifier -> LExpr TypeType Identifier): LExpr TypeType Identifier :=
  let funDef :=
    args.foldr (fun (name, type) body =>
      fun c => procedure_lambda c name type <| body
    ) body
  let_assign c name .none (funDef c) cont

def assume {Identifier : Type} (cond : LExpr TypeType Identifier) (thn : LExpr TypeType Identifier) : LExpr TypeType Identifier :=
  .ite cond thn .dontcare

def assert {Identifier: Type} (cond : LExpr TypeType Identifier) (thn : LExpr TypeType Identifier) : LExpr TypeType Identifier :=
  .ite cond thn .error

def plus (a b: LExpr LTy String) := LExpr.app (.app (.op "+" .none) a) b
def minus (a b: LExpr LTy String) := LExpr.app (.app (.op "-" .none) a) b
def pushpop (a b: LExpr LTy String) :=
  LExpr.app (LExpr.app (.abs .none (.abs .none (.bvar 0))) a) b
def not (a: LExpr LTy String) := LExpr.app (.op "!" .none) a

-- TODO: Prove that this transformation preserves errors
def ifToPushPop (prog: LExpr LTy String): LExpr LTy String :=
  match prog with
  | .assume cond thn =>
    .assume cond (ifToPushPop thn)
  | .assert cond thn =>
    .pushpop (.assume (.not cond) .error) (ifToPushPop thn)
  | .ite cond thn els =>
    -- Interestingly, we discard the thn branch!
    .pushpop (.assume cond (ifToPushPop thn)) (.assume (.not cond) (ifToPushPop els))
  | .choose t =>
    .choose t
  | .app a b =>
    .app (ifToPushPop a) (ifToPushPop b)
  | .abs t b =>
    .abs t (ifToPushPop b)
  | _ => prog

-- We increase the bvars that are currently "free" in the context.
-- Captured bvars remain intact.
def increaseBvars (prog: LExpr LTy String): LExpr LTy String :=
  let rec go: Nat -> LExpr LTy String -> LExpr LTy String
    | aboveLevel, .bvar n =>
      if n >= aboveLevel then
        .bvar (n + 1)
      else
        .bvar n
    | _, .const n t => .const n t
    | aboveLevel, .eq a b => .eq (go aboveLevel a) (go aboveLevel b)
    | aboveLevel, .ite cond thn els =>
      .ite (go aboveLevel cond) (go aboveLevel thn) (go aboveLevel els)
    | _, .dontcare => .dontcare
    | _, .error => .error
    | _, .skip => .skip
    | _, .choose t => .choose t
    | aboveLevel, .app a b => .app (go aboveLevel a) (go aboveLevel b)
    | aboveLevel, .abs t b => .abs t (go (aboveLevel + 1) b)
    | aboveLevel, .mdata m b => .mdata m (go aboveLevel b)
    | aboveLevel, .quant k ty tr e => .quant k ty (go aboveLevel tr) (go (aboveLevel + 1) e)
    | _, .fvar n t => .fvar n t
    | _, .op n t => .op n t
  go 0 prog

-- Same as increasesBvars but in reverse, for cases when we remove a lambda. Every bvar equal or above 0 + current depth is decreased by 1
def decreasesBVar (prog: LExpr LTy String): LExpr LTy String :=
  let rec go: Nat -> LExpr LTy String -> LExpr LTy String
    | aboveLevel, .bvar n =>
      if n >= aboveLevel then
        .bvar (n - 1)
      else
        .bvar n
    | _, .const n t => .const n t
    | aboveLevel, .eq a b => .eq (go aboveLevel a) (go aboveLevel b)
    | aboveLevel, .ite cond thn els =>
      .ite (go aboveLevel cond) (go aboveLevel thn) (go aboveLevel els)
    | _, .dontcare => .dontcare
    | _, .error => .error
    | _, .skip => .skip
    | _, .choose t => .choose t
    | aboveLevel, .app a b => .app (go aboveLevel a) (go aboveLevel b)
    | aboveLevel, .abs t b => .abs t (go (aboveLevel + 1) b)
    | aboveLevel, .mdata m b => .mdata m (go aboveLevel b)
    | aboveLevel, .quant k ty tr e => .quant k ty (go aboveLevel tr) (go (aboveLevel + 1) e)
    | _, .fvar n t => .fvar n t
    | _, .op n t => .op n t
  go 1 prog

def letAssignToLetAssume (prog: LExpr LTy String): LExpr LTy String :=
  match prog with
  | .app (.abs ty body) rhs =>
    let body := letAssignToLetAssume body
    if zeroVarContinuation rhs then
      -- We can simplify
      .app (.abs ty body) rhs
    else
    match rhs with
    | choose _ =>
      .app (.abs ty body) rhs  -- We can't simplify
    | _ => --TODO: Need to check determinism
      -- Interestingly, because the RHS is now in the context of the new variable,
      -- we need to increase all bound variables in the RHS by 1
      choose_abs ty (.abs ty (.assume (.eq (.bvar 0) (.increaseBvars rhs)) body))
  | .assume cond thn =>
    .assume cond (letAssignToLetAssume thn)
  | .assert cond thn =>
    .assert cond (letAssignToLetAssume thn)
  | .ite cond thn els =>
    .ite cond (letAssignToLetAssume thn) (letAssignToLetAssume els)
  | .choose t =>
    .choose t
  | .app a b =>
    .app (letAssignToLetAssume a) (letAssignToLetAssume b)
  | .abs t b =>
    .abs t (letAssignToLetAssume b)
  | _ => prog

partial def ToSMTExpr (c: Context String) (prog: LExpr LTy String): Format :=
  match prog with
  | .bvar n => c.nameOf n
  | .const n _ => f!"{n}"
  | .eq a b =>
    let aSmt := ToSMTExpr c a
    let bSmt := ToSMTExpr c b
    f!"(= {aSmt} {bSmt})"
  | .app (.op name ty) a =>
    let aSmt := ToSMTExpr c a
    let opSmt := ToSMTExpr c (.op name ty)
    f!"({opSmt} {aSmt})"
  | .app (.app (.op name ty) a) b =>
    let aSmt := ToSMTExpr c a
    let bSmt := ToSMTExpr c b
    let opSmt := ToSMTExpr c (.op name ty)
    f!"({opSmt} {aSmt} {bSmt})"
  | .op "+" _ => f!"+"
  | .op "-" _ => f!"-"
  | .op "!" _ => f!"not"
  | .op "&&" _ => f!"and"
  | .op "||" _ => f!"or"
  | .op "<" _ => f!"<"
  | .op "<=" _ => f!"<="
  | .op ">" _ => f!">"
  | .op ">=" _ => f!">="
  | .op "==>" _ => f!"=>"
  | .op "!=" _ => f!"distinct"
  | .op "regexfromstring" _ => "str.to_re"
  | .op "regexallchar" _ => "re.allchar"
  | .op "regexstar" _ => "re.*"
  | .op "regexconcat" _ => "re.++"
  | .op "regexmatch" _ => "str.in_re"
  | _ => panic!("ToSMTExpr: Not supported: " ++ toString (format prog))

-- Assume that the prog is written in an SMT compatible format
-- where expressions are all proved to be deterministic
partial def ToSMT (c: Context String) (prog: LExpr LTy String): Format :=
  match prog with
  | .app (.abs _ body) (.choose lty) =>
    if lty == _Bool then
      let varName :=  ("b" ++ toString c.size) -- TODO: Recover original name in .abs
      let newC := c.add_declare varName
      let bodySmt := ToSMT newC body
      f!"(declare-const {varName} Bool){Format.line}{bodySmt}"
    else if lty == _Int || lty == .none then -- None assumed integer
      let varName :=  ("b" ++ toString c.size) -- TODO: Recover original name in .abs
      let newC := c.add_declare varName
      let bodySmt := ToSMT newC body
      f!"(declare-const {varName} Int){Format.line}{bodySmt}"
    else
      panic!("ToSMT: Unsupported type in choose: " ++ (toString (format lty)))
  | .assume cond remaining =>
    let condSmt := ToSMTExpr c cond
    let remainingSmt := ToSMT c remaining
    f!"(assert {condSmt}){Format.line}{remainingSmt}"
  | .error =>
    f!"(check-sat)"
    -- push / pop
  | .app (.app (.abs _ (.abs _ (.bvar 0))) a) b =>
    let aSmt := ToSMT c a
    let bSmt := ToSMT c b
    f!"(push){Format.line}{aSmt}{Format.line}(pop){if !bSmt.isEmpty then Format.line else f!""}{bSmt}"
  | .skip => f!""
  | _ => panic!("ToSMT not supported:" ++ (toString (format prog)))

-- We wrongly assume determinism. We should detect determinism in the future.
def frameExitCall
  (frame: List String)
  (exitName: String)
  (cAtEntry: Context String)
  (cAtExit: Context String): LExpr LTy String :=
    (frame.map (fun varName =>
        cAtExit.vLastAssigned cAtEntry varName)).foldl
      (fun acc v => .app acc v)
      (cAtExit.v exitName)

def if_
     (c: Context String)
     (frame: List String)
     (cond: Context String -> LExpr LTy String)
     (then_ else_:(Context String -> LExpr LTy String) -> Context String → LExpr LTy String)
     (endif : Context String → LExpr LTy String) : LExpr LTy String :=
  -- First we call thn and els with a '#continue' free variable
  -- Then we detect which variables have been modified since the original context on either branches
  -- We add those variables to the context for next, and then
  -- we replace #continue on each branch with a call to the actual continue variable with the variables modified on either branches as argument.
  let exitName := "#continue" -- TODO: Avoid name clashes in the case of nested ifs. Use metadata?
  let newC := c.add_declare exitName
  let condProg := cond newC
  let thnProg := then_ (frameExitCall frame exitName newC) newC
  let elsProg := else_ (frameExitCall frame exitName newC) newC
  let nextCtx := frame.foldl Context.add_declare c
  let nextProg := frame.foldl (fun acc _ignoredName => .abs .none acc) (endif nextCtx)
  .app (.abs .none <| .ite condProg thnProg elsProg
  ) nextProg

/-
var i := 0;
if b {
  i := 1;
}
assert i == 0; // Error
vs.
var i := 0;
if b {
  var i := 1;
}
assert i == 0;
It seems that both would be encoded using a variable declaration with RHS.
However, the first case would have a "continue i" and the i would be the new argument, whereas the second would have a "continue ()" and the i would be the i before the if.
This means that modifying variables is something that has to be explicit in the input tree.
We don't have to guess.
-/

-- Substitute variable .bvar 0 in the body expression.
-- This variable's index increases every time we go through an abstraction
-- Replacement is assumed to already mention variables at the same scope level
-- so when going past an abstraction, we increase its free bvars.
def subst (replacement body : LExpr LTy String) : LExpr LTy String :=
  -- TODO: replacement MUST be deterministic or there must be EXACTLY one replacement
  let rec go (depth : Nat) (replacement : LExpr LTy String) : LExpr LTy String → LExpr LTy String
    | .bvar n => if n == depth then replacement else .bvar n
    | .abs ty e => .abs ty (go (depth + 1) (increaseBvars replacement) e)
    | .quant k ty tr e => .quant k ty (go depth replacement tr) (go (depth + 1) replacement e)
    | .app e1 e2 => .app (go depth replacement e1) (go depth replacement e2)
    | .ite c t e => .ite (go depth replacement c) (go depth replacement t) (go depth replacement e)
    | .eq e1 e2 => .eq (go depth replacement e1) (go depth replacement e2)
    | .mdata info e => .mdata info (go depth replacement e)
    | e => e
  go 0 replacement body

-- Like simplify but only for continuations.
-- .app (.abs _ x) RHS can be beta expanded if RHS is a function (even non deterministic), a constant or a variable
-- TODO: In other cases, we might prefer to just lift all assertions
partial def inlineContinuations (prog: LExpr LTy String): LExpr LTy String :=
  match prog with
  | .app (.abs _ body) (.abs oty exit) =>
    let newExit := inlineContinuations exit
    let newBody := inlineContinuations body
    decreasesBVar <| subst (increaseBvars (.abs oty newExit)) newBody
  | .app (.abs ty body) cont =>
    if zeroVarContinuation cont then -- TODO: Verify that it returns a unique value (could be unit!)
      decreasesBVar <| subst (increaseBvars <| inlineContinuations cont) (inlineContinuations body)
    else
      .app (.abs ty (inlineContinuations body)) (inlineContinuations cont)
  -- These are inlining values, not continuations. A simplification phase could take care of them.
  /-| .app (.abs _ body) (.const value oty) =>
    decreasesBVar <| subst (.const value oty) (inlineContinuations body)
  | .app (.abs _ body) (.fvar name oty) =>
    decreasesBVar <| subst (.fvar name oty) (inlineContinuations body)
  | .app (.abs _ body) (.bvar depth) =>
    decreasesBVar <| subst (.bvar depth) (inlineContinuations body)-/
  | .ite cond thn els =>
    .ite cond (inlineContinuations thn) (inlineContinuations els)
  | .app a b =>
    .app (inlineContinuations a) (inlineContinuations b)
  | .abs t b =>
    .abs t (inlineContinuations b)
  | _ => prog


-- .app (.abs _ x) RHS can be beta expanded if RHS is a function (even non deterministic), a constant or a variable
-- TODO: In other cases, we might prefer to just lift all assertions
partial def simplify (prog: LExpr LTy String): LExpr LTy String :=
  match prog with
  | .app (.abs _ body) (.const value oty) =>
    decreasesBVar <| subst (.const value oty) (simplify body)
  | .app (.abs _ body) (.fvar name oty) =>
    decreasesBVar <| subst (.fvar name oty) (simplify body)
  | .app (.abs _ body) (.bvar depth) =>
    decreasesBVar <| subst (.bvar depth) (simplify body)
  | .ite cond thn els =>
    .ite cond (simplify thn) (simplify els)
  | .app a b =>
    .app (simplify a) (simplify b)
  | .abs t b =>
    .abs t (simplify b)
  | _ => prog


def implies (a b: LExpr LTy String) := LExpr.app (LExpr.app (LExpr.op "==>" .none) a) b
def and (a b: LExpr LTy String) := LExpr.app (LExpr.app (LExpr.op "&&" .none) a) b
def ge (a b: LExpr LTy String) := LExpr.app (LExpr.app (LExpr.op ">=" .none) a) b
def lt (a b: LExpr LTy String) := LExpr.app (LExpr.app (LExpr.op "<" .none) a) b
def le (a b: LExpr LTy String) := LExpr.app (LExpr.app (LExpr.op "<=" .none) a) b
def gt (a b: LExpr LTy String) := LExpr.app (LExpr.app (LExpr.op ">" .none) a) b
def or (a b: LExpr LTy String) := LExpr.app (LExpr.app (LExpr.op "||" .none) a) b
def neq (a b: LExpr LTy String) := LExpr.app (LExpr.app (LExpr.op "!=" .none) a) b

---- Semantics of non-deterministic LExpr
inductive Value : Type where
  | unit : Value
  | value : String → Value
  | closure : List Value → LExpr LTy String → Value
  | error : Value

structure Environment (Identifier : Type) where
  stack : List Value  -- For bound variables (bvar), indexed by position
  globals : Identifier → Option Value  -- For free variables (fvar), looked up by name
def Environment.empty : Environment String :=
  { stack := [], globals := fun _ => none }
def Environment.pushStack (env : Environment String) (v : Value) : Environment String :=
  { env with stack := v :: env.stack }
def Environment.setGlobal (env : Environment String) (name : String) (v : Value) : Environment String :=
  { env with globals := fun n => if n = name then some v else env.globals n }
def Environment.lookupStack (env : Environment String) (n : Nat) : Option Value :=
  env.stack[n]?
def Environment.lookupGlobal (env : Environment String) (name : String) : Option Value :=
  env.globals name

inductive Eval : Environment String → LExpr LTy String → Value → Prop where
  | const : ∀ env c ty, Eval env (.const c ty) (.value c)
  | op : ∀ env o ty, Eval env (.op o ty) (.closure env.stack (.op o ty))
  | bvar : ∀ env n v, env.lookupStack n = some v → Eval env (.bvar n) v
  | fvar : ∀ env name ty v, env.lookupGlobal name = some v → Eval env (.fvar name ty) v
  | fvar_undef : ∀ env name ty, env.lookupGlobal name = none → Eval env (.fvar name ty) .error
  | abs : ∀ env ty body, Eval env (.abs ty body) (.closure env.stack (.abs ty body))
  | app_closure : ∀ env fn arg fnEnv fnBody argVal result,
      Eval env fn (.closure fnEnv fnBody) →
      Eval env arg argVal →
      Eval (env.pushStack argVal) fnBody result →
      Eval env (.app fn arg) result
  | app_error_fun : ∀ env fn arg,
      Eval env fn .error →
      Eval env (.app fn arg) .error
  | app_error_arg : ∀ env fn arg,
      Eval env arg .error →
      Eval env (.app fn arg) .error
  | ite_true : ∀ env cond thn els result,
      Eval env cond (.value "true") →
      Eval env thn result →
      Eval env (.ite cond thn els) result
  | ite_false : ∀ env cond thn els result,
      Eval env cond (.value "false") →
      Eval env els result →
      Eval env (.ite cond thn els) result
  | ite_error : ∀ env cond thn els,
      Eval env cond .error →
      Eval env (.ite cond thn els) .error
  | eq_true : ∀ env e1 e2 v,
      Eval env e1 v →
      Eval env e2 v →
      Eval env (.eq e1 e2) (.value "true")
  | eq_false : ∀ env e1 e2 v1 v2,
      Eval env e1 v1 →
      Eval env e2 v2 →
      v1 ≠ v2 →
      Eval env (.eq e1 e2) (.value "false")
  --| dontcare : No evaluation rules for .dontcare
  | error : ∀ env, Eval env .error .error
  | choose : ∀ env ty v, Eval env (.choose ty) v -- TODO: Add types
  | skip : ∀ env, Eval env .skip .unit

-- Stated soundness theorem.
def preservesSoundness (t : LExpr LTy String → LExpr LTy String) : Prop :=
  ∀ (prog : LExpr LTy String) (env : Environment String),
    Eval env prog .error →
    Eval env (t prog) .error

theorem letAssignToLetAssumeSound:
  letAssignToLetAssume |> preservesSoundness := by
  rw [preservesSoundness]
  intro prog
  intro env
  intro produceserror
  sorry

end LExpr
end Lambda
