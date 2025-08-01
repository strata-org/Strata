/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.Identifiers
import Strata.DL.Lambda.MetaData

/-
Formalization of Lambda Expressions
-/

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)

/-! ## Lambda Expressions with Quantifiers -/

inductive QuantifierKind
  | all
  | exist
  deriving Repr, DecidableEq

/--
Lambda Expressions with Quantifiers.

Like Lean's own expressions, we use the locally nameless
representation for this abstract syntax.
See https://chargueraud.org/research/2009/ln/main.pdf

We leave placeholders for (mono)type annotations only for constants
(`.const`), operations (`.op`), binders (`.abs`, `.quant`), and free
variables (`.fvar`). For a fully (mono)type annotated AST, see `LExprT`
that is created after the type inference transform.
-/
inductive LExpr (Identifier : Type) : Type where
  /-- `.const c ty`: constants (in the sense of literals). -/
  | const   (c : String) (ty : Option LMonoTy)
  /-- `.op c ty`: operation names. -/
  | op      (o : Identifier) (ty : Option LMonoTy)
  | bvar    (deBruijnIndex : Nat)
  | fvar    (name : Identifier) (ty : Option LMonoTy)
  | mdata   (info : Info) (e : LExpr Identifier)
  /-- `.abs ty e`: abstractions; `ty` the is type of bound variable. -/
  | abs     (ty : Option LMonoTy) (e : LExpr Identifier)
  /-- `.quant k ty e`: quantified expressions; `ty` the is type of bound variable. -/
  | quant   (k : QuantifierKind) (ty : Option LMonoTy) (e : LExpr Identifier)
  | app     (fn e : LExpr Identifier)
  | ite     (c t e : LExpr Identifier)
  | eq      (e1 e2 : LExpr Identifier)
  deriving Repr, DecidableEq

def LExpr.all {Identifier : Type} := @LExpr.quant Identifier .all
def LExpr.exist {Identifier : Type} := @LExpr.quant Identifier .exist

abbrev LExpr.absUntyped {Identifier : Type} := @LExpr.abs Identifier .none
abbrev LExpr.allUntyped {Identifier : Type} := @LExpr.quant Identifier .all .none
abbrev LExpr.existUntyped {Identifier : Type} := @LExpr.quant Identifier .exist .none
def LExpr.sizeOf [SizeOf Identifier]
  | LExpr.mdata (Identifier:=Identifier) _ e => 2 + sizeOf e
  | LExpr.abs   _ e => 2 + sizeOf e
  | LExpr.quant _ _ e => 3 + sizeOf e
  | LExpr.app fn e => 3 + sizeOf fn + sizeOf e
  | LExpr.ite c t e => 4 + sizeOf c + sizeOf t + sizeOf e
  | LExpr.eq  e1 e2 => 3 + sizeOf e1 + sizeOf e2
  | _ => 1

instance : SizeOf (LExpr Identifier) where
  sizeOf := LExpr.sizeOf
---------------------------------------------------------------------

namespace LExpr

instance : Inhabited (LExpr Identifier) where
  default := .const "false" none

def LExpr.getVars (e : (LExpr Identifier)) := match e with
  | .const _ _ => [] | .bvar _ => [] | .op _ _ => []
  | .fvar y _ => [y]
  | .mdata _ e' => LExpr.getVars e'
  | .abs _ e' => LExpr.getVars e'
  | .quant _ _ e' => LExpr.getVars e'
  | .app e1 e2 => LExpr.getVars e1 ++ LExpr.getVars e2
  | .ite c t e => LExpr.getVars c ++ LExpr.getVars t ++ LExpr.getVars e
  | .eq e1 e2 => LExpr.getVars e1 ++ LExpr.getVars e2

def getFVarName? (e : (LExpr Identifier)) : Option Identifier :=
  match e with
  | .fvar name _ => some name
  | _ => none

def isConst (e : (LExpr Identifier)) : Bool :=
  match e with
  | .const _ _ => true
  | _ => false

@[match_pattern]
protected def true : (LExpr Identifier) := .const "true"  (some (.tcons "bool" []))

@[match_pattern]
protected def false : (LExpr Identifier) := .const "false"  (some (.tcons "bool" []))

def isTrue (e : (LExpr Identifier)) : Bool :=
  match e with
  | .const "true" _ => true
  | _ => false

def isFalse (e : (LExpr Identifier)) : Bool :=
  match e with
  | .const "false" _ => true
  | _ => false

/--
If `e` is an `LExpr` boolean, then denote that into a Lean `Bool`.
Note that we are type-agnostic here.
-/
def denoteBool (e : (LExpr Identifier)) : Option Bool :=
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
def denoteInt (e : (LExpr Identifier)) : Option Int :=
  match e with
  | .const x (some (.tcons "int" [])) => x.toInt?
  | .const x none => x.toInt?
  | _ => none

/--
If `e` is an `LExpr` real, then denote that into a Lean `String`.
Note that we are type-agnostic here.
-/
def denoteReal (e : (LExpr Identifier)) : Option String :=
  match e with
  | .const x (some (.tcons "real" [])) => .some x
  | .const x none => .some x
  | _ => none

/--
If `e` is an `LExpr` bv<n>, then denote that into a Lean `BitVec n`.
Note that we are type-agnostic here.
-/
def denoteBitVec (n : Nat) (e : (LExpr Identifier)) : Option (BitVec n) :=
  match e with
  | .const x (.some (.bitvec n')) =>
    if n == n' then .map (.ofNat n) x.toNat? else none
  | .const x none => .map (.ofNat n) x.toNat?
  | _ => none

/--
If `e` is an _annotated_ `LExpr` string, then denote that into a Lean `String`.
Note that unannotated strings are not denoted.
-/
def denoteString (e : (LExpr Identifier)) : Option String :=
  match e with
  | .const c  (some (.tcons "string" [])) => some c
  | _ => none

def mkApp (fn : (LExpr Identifier)) (args : List (LExpr Identifier)) : (LExpr Identifier) :=
  match args with
  | [] => fn
  | a :: rest =>
    mkApp (.app fn a) rest

/--
Does `e` have a metadata annotation? We don't check for nested metadata in `e`.
-/
def isMData (e : (LExpr Identifier)) : Bool :=
  match e with
  | .mdata _ _ => true
  | _ => false

/--
Remove the outermost metadata annotation in `e`, if any.
-/
def removeMData1 (e : (LExpr Identifier)) : (LExpr Identifier) :=
  match e with
  | .mdata _ e => e
  | _ => e

/--
Remove all metadata annotations in `e`, included nested ones.
-/
def removeAllMData (e : (LExpr Identifier)) : (LExpr Identifier) :=
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
def size (e : (LExpr Identifier)) : Nat :=
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
def eraseTypes (e : (LExpr Identifier)) : (LExpr Identifier) :=
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

instance (Identifier : Type) [Repr Identifier] : ToString (LExpr Identifier) where toString a := toString (repr a)

private def formatLExpr [ToFormat Identifier] (e : (LExpr Identifier)) : Format :=
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

instance [ToFormat Identifier] : ToFormat (LExpr Identifier) where
  format := formatLExpr

/-
Syntax for conveniently building `LExpr` terms, scoped under the namespace
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
scoped syntax "(" lconst ":" lmonoty ")" : lconst
scoped syntax lconst : lexpr

def elabLConst (Identifier : Type) [MkIdent Identifier] : Lean.Syntax → MetaM Expr
  | `(lconst| #$n:num)  => do
    let none ← mkNone (mkConst ``LMonoTy)
    return mkAppN (.const ``LExpr.const []) #[MkIdent.toExpr Identifier, mkStrLit (toString n.getNat), none]
  | `(lconst| (#$n:num : $ty:lmonoty)) => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    return mkAppN (.const ``LExpr.const []) #[MkIdent.toExpr Identifier, mkStrLit (toString n.getNat), lmonoty]
  | `(lconst| #-$n:num) => do
    let none ← mkNone (mkConst ``LMonoTy)
    return mkAppN (.const ``LExpr.const []) #[MkIdent.toExpr Identifier, mkStrLit ("-" ++ (toString n.getNat)), none]
  | `(lconst| (#-$n:num : $ty:lmonoty)) => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    return mkAppN (.const ``LExpr.const []) #[MkIdent.toExpr Identifier, mkStrLit ("-" ++ (toString n.getNat)), lmonoty]
  | `(lconst| #true)    => do
    let none ← mkNone (mkConst ``LMonoTy)
    return mkAppN (.const ``LExpr.const []) #[MkIdent.toExpr Identifier, mkStrLit "true", none]
  | `(lconst| (#true : $ty:lmonoty))    => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    return mkAppN (.const ``LExpr.const []) #[MkIdent.toExpr Identifier, mkStrLit "true", lmonoty]
  | `(lconst| #false)   =>  do
    let none ← mkNone (mkConst ``LMonoTy)
    return mkAppN (.const ``LExpr.const []) #[MkIdent.toExpr Identifier, mkStrLit "false", none]
  | `(lconst| (#false : $ty:lmonoty))    => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    return mkAppN (.const ``LExpr.const []) #[MkIdent.toExpr Identifier, mkStrLit "false", lmonoty]
  | `(lconst| #$s:ident) => do
    let none ← mkNone (mkConst ``LMonoTy)
    let s := toString s.getId
    return mkAppN (.const ``LExpr.const []) #[MkIdent.toExpr Identifier, mkStrLit s, none]
  | `(lconst| (#$s:ident : $ty:lmonoty)) => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    let s := toString s.getId
    return mkAppN (.const ``LExpr.const []) #[MkIdent.toExpr Identifier, mkStrLit s, lmonoty]
  | _ => throwUnsupportedSyntax

declare_syntax_cat lop
scoped syntax "~" noWs lident : lop
scoped syntax "(" lop ":" lmonoty ")" : lop
scoped syntax lop : lexpr

def elabLOp (Identifier : Type) [MkIdent Identifier] : Lean.Syntax → MetaM Expr
  | `(lop| ~$s:lident)  => do
    let none ← mkNone (mkConst ``LMonoTy)
    mkAppM ``LExpr.op #[← MkIdent.elabIdent Identifier s, none]
  | `(lop| (~$s:lident : $ty:lmonoty)) => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    mkAppM ``LExpr.op #[← MkIdent.elabIdent Identifier s, lmonoty]
  | _ => throwUnsupportedSyntax

declare_syntax_cat lbvar
scoped syntax "%" noWs num : lbvar
def elabLBVar (Identifier : Type) [MkIdent Identifier] : Lean.Syntax → MetaM Expr
  | `(lbvar| %$n:num) =>
    return mkAppN (.const ``LExpr.bvar []) #[MkIdent.toExpr Identifier, mkNatLit n.getNat]
  | _ => throwUnsupportedSyntax
scoped syntax lbvar : lexpr

declare_syntax_cat lfvar
scoped syntax lident : lfvar
scoped syntax "(" lident ":" lmonoty ")" : lfvar

def elabLFVar (Identifier : Type) [MkIdent Identifier] : Lean.Syntax → MetaM Expr
  | `(lfvar| $i:lident) => do
    let none ← mkNone (mkConst ``LMonoTy)
    mkAppM ``LExpr.fvar #[← MkIdent.elabIdent Identifier i, none]
  | `(lfvar| ($i:lident : $ty:lmonoty)) => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    mkAppM ``LExpr.fvar #[← MkIdent.elabIdent Identifier i, lmonoty]
  | _ => throwUnsupportedSyntax
scoped syntax lfvar : lexpr

declare_syntax_cat mabs
declare_syntax_cat mall
declare_syntax_cat mexist
scoped syntax "λ" lexpr : mabs
scoped syntax "∀" lexpr : mall
scoped syntax "∃" lexpr : mexist
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

partial def elabLExpr (Identifier : Type) [MkIdent Identifier] : Lean.Syntax → MetaM Expr
  | `(lexpr| $c:lconst) => elabLConst Identifier c
  | `(lexpr| $o:lop) => elabLOp Identifier o
  | `(lexpr| $b:lbvar) => elabLBVar Identifier b
  | `(lexpr| $f:lfvar) => elabLFVar Identifier f
  -- Note: there's currently no concrete syntax for binders annotated with types.
  | `(lexpr| λ $e:lexpr) => do
     let e' ← elabLExpr Identifier e
     mkAppM ``LExpr.absUntyped #[e']
  | `(lexpr| ∀ $e:lexpr) => do
     let e' ← elabLExpr Identifier e
     mkAppM ``LExpr.allUntyped #[e']
  | `(lexpr| ∃ $e:lexpr) => do
     let e' ← elabLExpr Identifier e
     mkAppM ``LExpr.existUntyped #[e']
  | `(lexpr| ($e1:lexpr $e2:lexpr)) => do
     let e1' ← elabLExpr Identifier e1
     let e2' ← elabLExpr Identifier e2
     mkAppM ``LExpr.app #[e1', e2']
  | `(lexpr| $e1:lexpr == $e2:lexpr) => do
     let e1' ← elabLExpr Identifier e1
     let e2' ← elabLExpr Identifier e2
     mkAppM ``LExpr.eq #[e1', e2']
  | `(lexpr| if $e1:lexpr then $e2:lexpr else $e3:lexpr) => do
     let e1' ← elabLExpr Identifier e1
     let e2' ← elabLExpr Identifier e2
     let e3' ← elabLExpr Identifier e3
     mkAppM ``LExpr.ite #[e1', e2', e3']
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

/-- info: (bvar 0).absUntyped.app (const "5" none) : LExpr String -/
#guard_msgs in
#check es[((λ %0) #5)]

/-- info: ((bvar 0).eq (const "5" none)).allUntyped : LExpr String -/
#guard_msgs in
#check es[(∀ %0 == #5)]

/-- info: ((bvar 0).eq (const "5" none)).existUntyped : LExpr String -/
#guard_msgs in
#check es[(∃ %0 == #5)]

open LTy.Syntax in
/-- info: fvar "x" (some (LMonoTy.tcons "bool" [])) : LExpr String -/
#guard_msgs in
#check es[(x : bool)]

end Syntax

---------------------------------------------------------------------

end LExpr
end Lambda
