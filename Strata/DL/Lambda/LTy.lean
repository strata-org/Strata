/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Util.Map
import Lean.Elab.Term

/-! ## Formalization of Mono- and Poly- Types in Lambda

We implement a Hindley-Milner type system for expressions in Lambda, which means
that we can infer the types of unannotated `LExpr`s. Note that at this time, we
do not have `let`s in `LExpr`, so we do not tackle let-polymorphism yet.
-/

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)


abbrev TyIdentifier := String

instance : Coe String TyIdentifier where
  coe := id

/--
Types in Lambda: these are mono-types. Note that all free type variables
(`.ftvar`) are implicitly universally quantified.
-/
inductive LMonoTy : Type where
  /-- Type variable. -/
  | ftvar (name : TyIdentifier)
  /-- Type constructor. -/
  | tcons (name : String) (args : List LMonoTy)
  /-- Special support for bitvector types of every size. -/
  | bitvec (size : Nat)
  deriving Inhabited, Repr

abbrev LMonoTys := List LMonoTy

@[match_pattern]
def LMonoTy.bool : LMonoTy :=
  .tcons "bool" []

@[match_pattern]
def LMonoTy.int : LMonoTy :=
  .tcons "int" []

@[match_pattern]
def LMonoTy.real : LMonoTy :=
  .tcons "real" []

@[match_pattern]
def LMonoTy.bv1 : LMonoTy :=
  .bitvec 1

@[match_pattern]
def LMonoTy.bv8 : LMonoTy :=
  .bitvec 8

@[match_pattern]
def LMonoTy.bv16 : LMonoTy :=
  .bitvec 16

@[match_pattern]
def LMonoTy.bv32 : LMonoTy :=
  .bitvec 32

@[match_pattern]
def LMonoTy.bv64 : LMonoTy :=
  .bitvec 64

@[match_pattern]
def LMonoTy.string : LMonoTy :=
  .tcons "string" []

def LMonoTy.arrow (t1 t2 : LMonoTy) : LMonoTy :=
  .tcons "arrow" [t1, t2]

def LMonoTy.mkArrow (mty : LMonoTy) (mtys : LMonoTys) : LMonoTy :=
  match mtys with
  | [] => mty
  | m :: mrest =>
    let mrest' := LMonoTy.mkArrow m mrest
    .arrow mty mrest'

mutual
def LMonoTy.destructArrow (mty : LMonoTy) : LMonoTys :=
  match mty with
  | .tcons "arrow" (t1 :: trest) =>
    t1 :: LMonoTys.destructArrow trest
  | _ => [mty]

def LMonoTys.destructArrow (mtys : LMonoTys) : LMonoTys :=
  match mtys with
  | [] => []
  | mty :: mrest =>
    let mtys := LMonoTy.destructArrow mty
    let mrest_tys := LMonoTys.destructArrow mrest
    mtys ++ mrest_tys
end

theorem LMonoTy.destructArrow_non_empty (mty : LMonoTy) :
  (mty.destructArrow) ≠ [] := by
  unfold destructArrow; split <;> simp_all

/--
Type schemes (poly-types) in Lambda.
-/
inductive LTy : Type where
  | forAll (vars : List TyIdentifier) (ty : LMonoTy)
  deriving Inhabited, Repr

abbrev LTys := List LTy

---------------------------------------------------------------------

/--
Induction rule for `LMonoTy`.

Lean's default `induction` tactic does not support nested or mutual inductive
types. So we define our own induction principle below.
-/
@[induction_eliminator]
theorem LMonoTy.induct {P : LMonoTy → Prop}
  (ftvar : ∀f, P (.ftvar f))
  (bitvec : ∀n, P (.bitvec n))
  (tcons : ∀name args, (∀ ty ∈ args, P ty) → P (.tcons name args)) :
  ∀ ty, P ty := by
  intro n
  apply LMonoTy.rec <;> try assumption
  case nil => simp
  case cons =>
    intro head tail h_head h_tail
    simp_all
  done

mutual
/--
Compute the size of `ty` as a tree.
-/
def LMonoTy.size (ty : LMonoTy) : Nat :=
  match ty with
  | .ftvar _ => 1
  | .tcons _ args => 1 + LMonoTys.size args
  | .bitvec _ => 1

def LMonoTys.size (args : LMonoTys) : Nat :=
    match args with
    | [] => 0
    | t :: rest => LMonoTy.size t + LMonoTys.size rest
end

theorem LMonoTy.size_gt_zero :
  0 < LMonoTy.size ty := by
  induction ty <;>  simp_all [LMonoTy.size]
  unfold LMonoTys.size; split
  simp_all; omega

/--
Boolean equality for `LMonoTy`.
-/
def LMonoTy.BEq (x y : LMonoTy) : Bool :=
  match x, y with
  | .ftvar i, .ftvar j => i == j
  | .bitvec i, .bitvec j => i == j
  | .tcons i1 j1, .tcons i2 j2 =>
    i1 == i2 && j1.length == j2.length && go j1 j2
  | _, _ => false
  where go j1 j2 :=
  match j1, j2 with
  | [], _ => true
  | _, [] => true
  | x :: xrest, y :: yrest =>
    LMonoTy.BEq x y && go xrest yrest

@[simp]
theorem LMonoTy.BEq_refl : LMonoTy.BEq ty ty := by
  induction ty <;> simp_all [LMonoTy.BEq]
  rename_i name args ih
  induction args
  case tcons.nil => simp [LMonoTy.BEq.go]
  case tcons.cons =>
    rename_i head tail ih'
    simp_all [LMonoTy.BEq.go]
  done

instance : DecidableEq LMonoTy :=
  fun x y =>
    if h: LMonoTy.BEq x y then
      isTrue (by
                induction x generalizing y
                case ftvar =>
                  unfold LMonoTy.BEq at h <;> split at h <;> try simp_all
                case bitvec =>
                  unfold LMonoTy.BEq at h <;> split at h <;> try simp_all
                case tcons =>
                  rename_i name args ih
                  cases y <;> try simp_all [LMonoTy.BEq]
                  rename_i name' args'
                  obtain ⟨⟨h1, h2⟩, h3⟩ := h
                  induction args generalizing args'
                  case nil => unfold List.length at h2; split at h2 <;> simp_all
                  case cons head' tail' ih' =>
                    unfold LMonoTy.BEq.go at h3 <;> split at h3 <;> try simp_all
                    rename_i j1 j2 x xrest y yrest heq
                    obtain ⟨h3_1, h3_2⟩ := h3
                    obtain ⟨ih1, ih2⟩ := ih
                    exact ⟨ih1 y h3_1, ih' ih2 yrest h3_2 rfl⟩)
    else
      isFalse (by induction x generalizing y
                  case ftvar =>
                    cases y <;> try simp_all [LMonoTy.BEq]
                  case bitvec n =>
                    cases y <;> try simp_all [LMonoTy.BEq]
                  case tcons name args ih =>
                    cases y <;> try simp_all [LMonoTy.BEq]
                    rename_i name' args'
                    intro hname; simp [hname] at h
                    induction args generalizing args'
                    case tcons.nil =>
                      simp [LMonoTy.BEq.go] at h
                      unfold List.length at h; split at h <;> simp_all
                    case tcons.cons head tail ih' =>
                      cases args' <;> try simp_all
                      rename_i head' tail'; intro _
                      have ih'' := @ih' tail'
                      unfold LMonoTy.BEq.go at h
                      simp_all)

instance : Inhabited LMonoTy where
  default := .tcons "bool" []

instance : ToString LTy where
  toString x := toString (repr x)

mutual
/--
Get the free type variables in monotype `mty`, which are simply the `.ftvar`s in
it.
-/
def LMonoTy.freeVars (mty : LMonoTy) : List TyIdentifier :=
  match mty with
  | .ftvar x => [x]
  | .bitvec _ => []
  | .tcons _ ltys => LMonoTys.freeVars ltys

/--
Get the free type variables in monotypes `mtys`, which are simply the `.ftvar`s
in them.
-/
def LMonoTys.freeVars (mtys : LMonoTys) : List TyIdentifier :=
    match mtys with
    | [] => [] | ty :: rest => LMonoTy.freeVars ty ++ LMonoTys.freeVars rest
end

@[simp]
theorem LMonoTys.freeVars_of_cons :
  LMonoTys.freeVars (x :: xs) = LMonoTy.freeVars x ++ LMonoTys.freeVars xs := by
  simp_all [LMonoTys.freeVars]

/--
Get all type constructors in monotype `mty`.
-/
def LMonoTy.getTyConstructors (mty : LMonoTy) : List LMonoTy :=
  match mty with
  | .ftvar _ => []
  | .bitvec _ => []
  | .tcons name mtys =>
    let typeargs :=  List.replicate mtys.length "_dummy"
    let args := typeargs.mapIdx (fun i elem => LMonoTy.ftvar (elem ++ toString i))
    let mty := .tcons name args
    let ans := mty :: go mtys
    ans.eraseDups
  where go mtys :=
  match mtys with
  | [] => [] | m :: mrest => LMonoTy.getTyConstructors m ++ go mrest

/--
info: [Lambda.LMonoTy.tcons "arrow" [Lambda.LMonoTy.ftvar "_dummy0", Lambda.LMonoTy.ftvar "_dummy1"],
 Lambda.LMonoTy.tcons "bool" [],
 Lambda.LMonoTy.tcons "foo" [Lambda.LMonoTy.ftvar "_dummy0"],
 Lambda.LMonoTy.tcons "a" [Lambda.LMonoTy.ftvar "_dummy0", Lambda.LMonoTy.ftvar "_dummy1"]]
-/
#guard_msgs in
#eval LMonoTy.getTyConstructors
        ((.tcons "arrow" [.tcons "bool" [], .tcons "foo" [.tcons "a" [.ftvar "b", .tcons "bool" []]]]))

---------------------------------------------------------------------

/--
Boolean equality for `LTy`.
-/
def LTy.BEq (x y : LTy) : Bool :=
  match x, y with
  | .forAll xs xlty, .forAll ys ylty =>
    xs == ys && xlty == ylty

instance : DecidableEq LTy :=
  fun x y =>
    if h: LTy.BEq x y then
      isTrue (by
                unfold LTy.BEq at h
                split at h <;> simp_all)
    else
      isFalse (by
                unfold LTy.BEq at h
                split at h <;> simp_all)

/--
Get the free type variables in type scheme `ty`, which are all the unbound
`.ftvar`s in it.
-/
def LTy.freeVars (ty : LTy) : List TyIdentifier :=
  match ty with
  | .forAll xs lty => let lfv := LMonoTy.freeVars lty
                      lfv.removeAll xs

/--
Get the bound type variables in a type scheme.
-/
def LTy.boundVars (sch : LTy) : List TyIdentifier :=
  match sch with
  | .forAll xs _ => xs

/--
A type scheme `ty` is a mono-type if there are no bound variables.
-/
def LTy.isMonoType (ty : LTy) : Bool :=
  ty.boundVars.isEmpty

/--
Obtain a mono-type from a type scheme `ty`.
-/
def LTy.toMonoType (ty : LTy) (h : LTy.isMonoType ty) : LMonoTy :=
  match ty with
  | .forAll _ lty => lty

/--
Unsafe coerce from a type scheme to a mono-type.
-/
def LTy.toMonoTypeUnsafe (ty : LTy) : LMonoTy :=
  match ty with
  | .forAll _ lty => lty

---------------------------------------------------------------------

/- Formatting and Parsing -/

instance : ToString LMonoTy where
  toString x := toString (repr x)

private def formatLMonoTy (lmonoty : LMonoTy) : Format :=
  match lmonoty with
  | .ftvar x => toString x
  | .bitvec n => f!"bv{n}"
  | .tcons name tys =>
    if tys.isEmpty then
      f!"{name}"
    else
      let args := (Std.Format.joinSep (tys.map formatLMonoTy) (" "))
      Std.Format.paren (name ++ " " ++ args)

instance : ToFormat LMonoTy where
  format := formatLMonoTy

instance : ToFormat LTy where
  format ty := match ty with
  | .forAll names lmonoty =>
    if names.isEmpty then f!"{lmonoty}"
    else f!"∀{names}. {lmonoty}"


namespace LTy

/- Syntax for conveniently building `LMonoTy` and `LTy` terms, scoped under the
namespace `LMonoTy.Syntax`. -/
namespace Syntax

/-
NOTE: %<ident> is elaborated to type variables. <ident> is elaborated to a
`tcons` constructor's name.
-/

declare_syntax_cat lmonoty

declare_syntax_cat ftvar
scoped syntax "%" noWs ident : ftvar
scoped syntax ftvar : lmonoty

declare_syntax_cat tcons
declare_syntax_cat tident
scoped syntax ident : tident
scoped syntax tident (lmonoty)* : tcons
scoped syntax tcons : lmonoty
-- Special handling for function types.
scoped syntax:65 lmonoty:66 "→" lmonoty:65 : lmonoty
-- Special handling for bool and int types.
declare_syntax_cat tprim
scoped syntax "int" : tprim
scoped syntax "bool" : tprim
scoped syntax tprim : tcons

scoped syntax "(" lmonoty ")" : lmonoty

open Lean Elab Meta in
partial def elabLMonoTy : Lean.Syntax → MetaM Expr
  | `(lmonoty| %$f:ident) => do
     mkAppM ``LMonoTy.ftvar #[mkStrLit (toString f.getId)]
  | `(lmonoty| $ty1:lmonoty → $ty2:lmonoty) => do
     let ty1' ← elabLMonoTy ty1
     let ty2' ← elabLMonoTy ty2
     let tys ← mkListLit (mkConst ``LMonoTy) [ty1', ty2']
     mkAppM ``LMonoTy.tcons #[(mkStrLit "arrow"), tys]
  | `(lmonoty| int) => do
    let argslist ← mkListLit (mkConst ``LMonoTy) []
    mkAppM ``LMonoTy.tcons #[(mkStrLit "int"), argslist]
  | `(lmonoty| bool) => do
    let argslist ← mkListLit (mkConst ``LMonoTy) []
    mkAppM ``LMonoTy.tcons #[(mkStrLit "bool"), argslist]
  | `(lmonoty| bv1) =>  mkAppM ``LMonoTy.bv1 #[]
  | `(lmonoty| bv8) =>  mkAppM ``LMonoTy.bv8 #[]
  | `(lmonoty| bv16) => mkAppM ``LMonoTy.bv16 #[]
  | `(lmonoty| bv32) => mkAppM ``LMonoTy.bv32 #[]
  | `(lmonoty| bv64) => mkAppM ``LMonoTy.bv64 #[]
  | `(lmonoty| $i:ident $args:lmonoty*) => do
    let args' ← go args
    let argslist ← mkListLit (mkConst ``LMonoTy) args'.toList
    mkAppM ``LMonoTy.tcons #[(mkStrLit (toString i.getId)), argslist]
  | `(lmonoty| ($ty:lmonoty)) => elabLMonoTy ty
  | _ => throwUnsupportedSyntax
  where go (args : TSyntaxArray `lmonoty) : MetaM (Array Expr) := do
    let mut arr := #[]
    for a in args do
      let a' ← elabLMonoTy a
      arr := arr.push a'
    return arr

elab "mty[" ty:lmonoty "]" : term => elabLMonoTy ty

/-- info: LMonoTy.tcons "list" [LMonoTy.tcons "int" []] : LMonoTy -/
#guard_msgs in
#check mty[list int]

/-- info: LMonoTy.tcons "pair" [LMonoTy.tcons "int" [], LMonoTy.tcons "bool" []] : LMonoTy -/
#guard_msgs in
#check mty[pair int bool]

/--
info: LMonoTy.tcons "arrow"
  [LMonoTy.tcons "Map" [LMonoTy.ftvar "k", LMonoTy.ftvar "v"],
    LMonoTy.tcons "arrow" [LMonoTy.ftvar "k", LMonoTy.ftvar "v"]] : LMonoTy
-/
#guard_msgs in
#check mty[(Map %k %v) → %k → %v]

/--
info: LMonoTy.tcons "arrow"
  [LMonoTy.ftvar "a",
    LMonoTy.tcons "arrow" [LMonoTy.ftvar "b", LMonoTy.tcons "arrow" [LMonoTy.ftvar "c", LMonoTy.ftvar "d"]]] : LMonoTy
-/
#guard_msgs in
#check mty[%a → %b → %c → %d]

declare_syntax_cat lty
scoped syntax (lmonoty)* : lty
scoped syntax "∀" (ident)* "." (lmonoty)* : lty
scoped syntax "(" lty ")" : lty

open Lean Elab Meta in
partial def elabLTy : Lean.Syntax → MetaM Expr
  | `(lty| ∀ $vars:ident* . $ty:lmonoty) => do
      let vars' := List.map (fun f => mkStrLit (toString f.getId)) vars.toList
      let varslist ← mkListLit (mkConst ``String) vars'
      let ty' ← elabLMonoTy ty
      mkAppM ``LTy.forAll #[varslist, ty']
  | `(lty| $ty:lmonoty) => do
      let emptylist ← mkListLit (mkConst ``String) []
      let ty' ← elabLMonoTy ty
      mkAppM ``LTy.forAll #[emptylist, ty']
  | `(lty| ($ty:lty)) => elabLTy ty
  | _ => throwUnsupportedSyntax

elab "t[" lsch:lty "]" : term => elabLTy lsch

/-- info: forAll ["α"] (LMonoTy.tcons "myType" [LMonoTy.ftvar "α"]) : LTy -/
#guard_msgs in
#check t[∀α. myType %α]

/--
info: forAll ["α"]
  (LMonoTy.tcons "arrow" [LMonoTy.ftvar "α", LMonoTy.tcons "arrow" [LMonoTy.ftvar "α", LMonoTy.tcons "int" []]]) : LTy
-/
#guard_msgs in
#check t[∀α. %α → %α → int]

end Syntax
end LTy

---------------------------------------------------------------------

open LTy.Syntax

def LMonoTy.inputArity (ty : LMonoTy) : Nat :=
  match ty with
  | .tcons "arrow" (_a :: rest) => 1 + go rest
  | _ => 0
  where go args :=
  match args with
  | [] => 0
  | a :: arest => inputArity a + go arest

def LTy.inputArity (ty : LTy) : Nat :=
  match ty with
  | .forAll _ mty => mty.inputArity

/-- info: 3 -/
#guard_msgs in
#eval LTy.inputArity t[int → (int → (int → int))]
/-- info: 2 -/
#guard_msgs in
#eval LTy.inputArity t[int → (int → int)]
/-- info: 1 -/
#guard_msgs in
#eval LTy.inputArity t[∀a. (%a → int) → int]
/-- info: 0 -/
#guard_msgs in
#eval LTy.inputArity t[∀a. pair %a bool]

def LMonoTy.inputTypes (ty : LMonoTy) : List LMonoTy :=
  match ty with
  | .tcons "arrow" (a :: rest) => a :: go rest
  | _ => []
  where go args :=
  match args with
  | [] => []
  | a :: arest => inputTypes a ++ go arest

/-- info: [int, int, int] -/
#guard_msgs in
#eval format $ LMonoTy.inputTypes mty[int → (int → (int → int))]
/-- info: [int, bool] -/
#guard_msgs in
#eval format $ LMonoTy.inputTypes mty[int → (bool → int)]
/-- info: [int, bool, bit] -/
#guard_msgs in
#eval format $ LMonoTy.inputTypes mty[int → (bool → (bit → nat))]
/-- info: [(arrow int int)] -/
#guard_msgs in
#eval format $ LMonoTy.inputTypes mty[(int → int) → nat]
/-- info: [] -/
#guard_msgs in
#eval LMonoTy.inputTypes mty[pair int bool]

---------------------------------------------------------------------

end Lambda
