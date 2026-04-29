/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Util.Tactics
public import Lean.Elab.Term.TermElabM

/-! ## Formalization of Mono- and Poly- Types in Lambda

We implement a Hindley-Milner type system for expressions in Lambda, which means
that we can infer the types of unannotated `LExpr`s. Note that at this time, we
do not have `let`s in `LExpr`, so we do not tackle let-polymorphism yet.
-/

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)


public section

/-- Type identifiers. For now, these are just strings. -/
@[expose] abbrev TyIdentifier := String

instance : Coe String TyIdentifier where
  coe := id

/-- Monomorphic types in Lambda. Note that all free type variables (`.ftvar`)
are implicitly universally quantified.  -/
inductive LMonoTy : Type where
  /-- A type variable. -/
  | ftvar (name : TyIdentifier)
  /-- A type constructor. -/
  | tcons (name : String) (args : List LMonoTy)
  /-- A bit vector type. This is a special case so that it can be parameterized
  by a size. -/
  | bitvec (size : Nat)
  deriving Inhabited, Repr

@[expose] abbrev LMonoTys := List LMonoTy

@[expose, match_pattern]
def LMonoTy.bool : LMonoTy :=
  .tcons "bool" []

@[expose, match_pattern]
def LMonoTy.int : LMonoTy :=
  .tcons "int" []

@[expose, match_pattern]
def LMonoTy.real : LMonoTy :=
  .tcons "real" []

@[expose, match_pattern]
def LMonoTy.bv1 : LMonoTy :=
  .bitvec 1

@[expose, match_pattern]
def LMonoTy.bv8 : LMonoTy :=
  .bitvec 8

@[expose, match_pattern]
def LMonoTy.bv16 : LMonoTy :=
  .bitvec 16

@[expose, match_pattern]
def LMonoTy.bv32 : LMonoTy :=
  .bitvec 32

@[expose, match_pattern]
def LMonoTy.bv64 : LMonoTy :=
  .bitvec 64

@[expose, match_pattern]
def LMonoTy.string : LMonoTy :=
  .tcons "string" []

@[expose, match_pattern]
def LMonoTy.arrow (t1 t2 : LMonoTy) : LMonoTy :=
  .tcons "arrow" [t1, t2]

def LMonoTy.mkArrow (mty : LMonoTy) (mtys : LMonoTys) : LMonoTy :=
  match mtys with
  | [] => mty
  | m :: mrest =>
    let mrest' := LMonoTy.mkArrow m mrest
    .arrow mty mrest'

/--
Create an iterated arrow type where `mty` is the return type
-/
def LMonoTy.mkArrow' (mty : LMonoTy) (mtys : LMonoTys) : LMonoTy :=
  match mtys with
  | [] => mty
  | m :: mrest => .arrow m (LMonoTy.mkArrow' mty mrest)

@[simp] theorem LMonoTy.mkArrow'_nil (τ : LMonoTy) : LMonoTy.mkArrow' τ [] = τ := by
  simp [LMonoTy.mkArrow']

@[simp] theorem LMonoTy.mkArrow'_cons (τ m : LMonoTy) (ms : LMonoTys) :
    LMonoTy.mkArrow' τ (m :: ms) = .arrow m (LMonoTy.mkArrow' τ ms) := by
  simp [LMonoTy.mkArrow']

theorem LMonoTy.mkArrow'_injective {ret₁ ret₂ : LMonoTy} {ins₁ ins₂ : List LMonoTy}
    (h_len : ins₁.length = ins₂.length)
    (h : LMonoTy.mkArrow' ret₁ ins₁ = LMonoTy.mkArrow' ret₂ ins₂)
    : ret₁ = ret₂ ∧ ins₁ = ins₂ := by
  induction ins₁ generalizing ins₂ with
  | nil =>
    cases ins₂ with
    | nil => simp [mkArrow'] at h; exact ⟨h, rfl⟩
    | cons => simp at h_len
  | cons x xs ih =>
    cases ins₂ with
    | nil => simp at h_len
    | cons y ys =>
      simp [mkArrow', LMonoTy.arrow] at h h_len
      have ⟨h_ret, h_tl⟩ := ih h_len h.2
      exact ⟨h_ret, by rw [h.1, h_tl]⟩

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

def LMonoTy.getArrowArgs (t: LMonoTy) : List LMonoTy :=
  match t with
  | .arrow t1 t2 => t1 :: t2.getArrowArgs
  | _ => []

/-- Return `some (dom, cod)` if the type is an arrow, `none` otherwise. -/
def LMonoTy.isArrow : LMonoTy → Option (LMonoTy × LMonoTy)
  | .tcons "arrow" [dom, cod] => some (dom, cod)
  | _ => none

/-- Checks if the type contains an arrow (function type) at any depth. -/
def LMonoTy.containsArrow : LMonoTy → Bool
  | .tcons "arrow" _ => true
  | .tcons _ args => args.attach.any (fun x => LMonoTy.containsArrow x.1)
  | .ftvar _ | .bitvec _ => false
  termination_by t => SizeOf.sizeOf t
  decreasing_by cases x; term_by_mem

@[simp] theorem LMonoTy.isArrow_arrow (t1 t2 : LMonoTy) :
    (LMonoTy.arrow t1 t2).isArrow = some (t1, t2) := by
  simp [LMonoTy.arrow, isArrow]

theorem LMonoTy.isArrow_some {t t1 t2 : LMonoTy} :
    t.isArrow = some (t1, t2) → t = .arrow t1 t2 := by
  simp [LMonoTy.arrow, isArrow]
  cases t <;> grind

/--
Polymorphic type schemes in Lambda.
-/
inductive LTy : Type where
  /-- A type containing universally quantified type variables. -/
  | forAll (vars : List TyIdentifier) (ty : LMonoTy)
  deriving Inhabited, Repr

@[expose] abbrev LTys := List LTy

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
@[simp]
def LMonoTy.size (ty : LMonoTy) : Nat :=
  match ty with
  | .ftvar _ => 1
  | .tcons _ args => 1 + LMonoTys.size args
  | .bitvec _ => 1

@[simp]
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

theorem LMonoTy.size_lt_of_mem {ty: LMonoTy} {tys: LMonoTys} (h: ty ∈ tys):
  ty.size <= tys.size := by
  induction tys <;> simp only[LMonoTys.size]<;> grind

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


/-- If `v ∈ LMonoTys.freeVars tys` and every element's free vars are in `S`,
then `v ∈ S`. -/
theorem LMonoTys.freeVars_subset
    {tys : List LMonoTy} {S : List TyIdentifier}
    (h : ∀ ty, ty ∈ tys → LMonoTy.freeVars ty ⊆ S)
    {v : TyIdentifier}
    (hv : v ∈ LMonoTys.freeVars tys)
    : v ∈ S := by
  induction tys with
  | nil => simp [LMonoTys.freeVars] at hv
  | cons ty rest ih =>
    simp only [LMonoTys.freeVars_of_cons, List.mem_append] at hv
    cases hv with
    | inl hmem => exact h ty (.head _) hmem
    | inr hmem => exact ih (fun t ht => h t (.tail _ ht)) hmem

/-- Each element's free vars are a subset of the whole list's free vars. -/
theorem LMonoTys.freeVars_mem_subset
    {ty : LMonoTy} {tys : List LMonoTy}
    (ht : ty ∈ tys)
    : LMonoTy.freeVars ty ⊆ LMonoTys.freeVars tys := by
  induction tys with
  | nil => contradiction
  | cons x rest ih =>
    simp only [LMonoTys.freeVars_of_cons]
    grind

/-- If `v ∈ LMonoTys.freeVars tys`, then some element of `tys` contains `v`. -/
theorem LMonoTys.freeVars_exists
    {v : TyIdentifier} {tys : List LMonoTy}
    (hv : v ∈ LMonoTys.freeVars tys)
    : ∃ ty, ty ∈ tys ∧ v ∈ LMonoTy.freeVars ty := by
  induction tys with
  | nil => simp [LMonoTys.freeVars] at hv
  | cons ty rest ih =>
    simp only [LMonoTys.freeVars_of_cons, List.mem_append] at hv
    cases hv with
    | inl h => exact ⟨ty, .head _, h⟩
    | inr h => obtain ⟨t, ht, htv⟩ := ih h; exact ⟨t, .tail _ ht, htv⟩

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
Optionally obtain a mono-type from a type scheme `ty`.
-/
def LTy.toMonoType? (ty : LTy) : Option LMonoTy :=
  match ty with
  | .forAll [] lty => .some lty
  | _ => .none

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
  format := private formatLMonoTy

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
meta partial def elabLMonoTy : Lean.Syntax → MetaM Expr
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

declare_syntax_cat lty
scoped syntax (lmonoty)* : lty
scoped syntax "∀" (ident)* "." (lmonoty)* : lty
scoped syntax "(" lty ")" : lty

open Lean Elab Meta in
meta partial def elabLTy : Lean.Syntax → MetaM Expr
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

def LMonoTy.inputTypes (ty : LMonoTy) : List LMonoTy :=
  match ty with
  | .tcons "arrow" (a :: rest) => a :: go rest
  | _ => []
  where go args :=
  match args with
  | [] => []
  | a :: arest => inputTypes a ++ go arest

---------------------------------------------------------------------

/--
Close `ty` by `x`, i.e., add `x` as a bound type variable.
-/
def LTy.close (x : TyIdentifier) (ty : LTy) : LTy :=
  match ty with
  | .forAll vars lty => .forAll (x :: vars) lty

end -- public section
end Lambda
