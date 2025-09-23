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


class Locatable (T: Type) where
  Uri: T -> String
  LineIndex: T -> Nat
  ColumnIndex: T -> Nat
  PositionIndex: T -> Nat

/-
Traceable class for combining multiple metadata with labeled provenance.

Takes a list of (reason, metadata) pairs and combines them into a single metadata.
Each pair describes why that metadata is being included in the combination.

Usage:
  Traceable.combine [("function", fnMeta), ("argument", argMeta), ("context", ctxMeta)]
-/
class Traceable (Reason: Type) (Metadata : Type) where
  combine : List (Reason × Metadata) → Metadata

/--
Expected interface for pure expressions that can be used to specialize the
Imperative dialect.
-/
structure LExprParams : Type 1 where
  Metadata: Type
  Identifier : Type
  deriving Inhabited

/--
Extended LExprParams that includes TypeType parameter.
-/
structure LExprParamsT : Type 1 where
  base : LExprParams
  TypeType : Type
  deriving Inhabited

/--
Dot notation syntax: T.mono transforms LExprParams into LExprParamsT with LMonoTy.
-/
abbrev LExprParams.mono (T : LExprParams) : LExprParamsT :=
  ⟨T, LMonoTy⟩

structure Typed (T: Type) where
  underlying: T
  type: LMonoTy

-- Metadata annotated with a type
abbrev LExprParams.typed (T: LExprParams): LExprParams :=
  ⟨ Typed T.Metadata, T.Identifier ⟩

abbrev LExprParamsT.typed (T: LExprParamsT): LExprParamsT :=
  ⟨T.base.typed, LMonoTy⟩

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
inductive LExpr (T : LExprParamsT) : Type where
  /-- `.const c ty`: constants (in the sense of literals). -/
  | const   (m: T.base.Metadata) (c : String) (ty : Option T.TypeType)
  /-- `.op c ty`: operation names. -/
  | op      (m: T.base.Metadata) (o : T.base.Identifier) (ty : Option T.TypeType)
  /-- `.bvar deBruijnIndex`: bound variable. -/
  | bvar    (m: T.base.Metadata) (deBruijnIndex : Nat)
  /-- `.fvar name ty`: free variable, with an option (mono)type annotation. -/
  | fvar    (m: T.base.Metadata) (name : T.base.Identifier) (ty : Option T.TypeType)
  /-- `.abs ty e`: abstractions; `ty` the is type of bound variable. -/
  | abs     (m: T.base.Metadata) (ty : Option T.TypeType) (e : LExpr T)
  /-- `.quant k ty tr e`: quantified expressions; `ty` the is type of bound variable, and `tr` the trigger. -/
  | quant   (m: T.base.Metadata) (k : QuantifierKind) (ty : Option T.TypeType) (trigger: LExpr T) (e : LExpr T)
  /-- `.app fn e`: function application. -/
  | app     (m: T.base.Metadata) (fn e : LExpr T)
  /-- `.ite c t e`: if-then-else expression. -/
  | ite     (m: T.base.Metadata) (c t e : LExpr T)
  /-- `.eq e1 e2`: equality expression. -/
  | eq      (m: T.base.Metadata) (e1 e2 : LExpr T)

instance [Repr T.base.Metadata] [Repr T.TypeType] [Repr T.base.Identifier] : Repr (LExpr T) where
  reprPrec e prec :=
    let rec go : LExpr T → Std.Format
      | .const m c ty =>
        match ty with
        | none => f!"LExpr.const {repr m} {repr c} none"
        | some ty => f!"LExpr.const {repr m} {repr c} (some {repr ty})"
      | .op m o ty =>
        match ty with
        | none => f!"LExpr.op {repr m} {repr o} none"
        | some ty => f!"LExpr.op {repr m} {repr o} (some {repr ty})"
      | .bvar m i => f!"LExpr.bvar {repr m} {repr i}"
      | .fvar m name ty =>
        match ty with
        | none => f!"LExpr.fvar {repr m} {repr name} none"
        | some ty => f!"LExpr.fvar {repr m} {repr name} (some {repr ty})"
      | .abs m ty e =>
        match ty with
        | none => f!"LExpr.abs {repr m} none ({go e})"
        | some ty => f!"LExpr.abs {repr m} (some {repr ty}) ({go e})"
      | .quant m k ty tr e =>
        let kindStr := match k with | .all => "QuantifierKind.all" | .exist => "QuantifierKind.exist"
        match ty with
        | none => f!"LExpr.quant {repr m} {kindStr} none ({go tr}) ({go e})"
        | some ty => f!"LExpr.quant {repr m} {kindStr} (some {repr ty}) ({go tr}) ({go e})"
      | .app m fn e => f!"LExpr.app {repr m} ({go fn}) ({go e})"
      | .ite m c t e => f!"LExpr.ite {repr m} ({go c}) ({go t}) ({go e})"
      | .eq m e1 e2 => f!"LExpr.eq {repr m} ({go e1}) ({go e2})"
    if prec > 0 then Std.Format.paren (go e) else go e

-- Boolean equality function for LExpr
def LExpr.beq [BEq T.base.Metadata] [BEq T.TypeType] [BEq T.base.Identifier] : LExpr T → LExpr T → Bool
  | .const m1 c1 ty1, e2 =>
    match e2 with
    | .const m2 c2 ty2 => m1 == m2 && c1 == c2 && ty1 == ty2
    | _ => false
  | .op m1 o1 ty1, e2 =>
    match e2 with
    | .op m2 o2 ty2 => m1 == m2 && o1 == o2 && ty1 == ty2
    | _ => false
  | .bvar m1 i1, e2 =>
    match e2 with
    | .bvar m2 i2 => m1 == m2 && i1 == i2
    | _ => false
  | .fvar m1 n1 ty1, e2 =>
    match e2 with
    | .fvar m2 n2 ty2 => m1 == m2 && n1 == n2 && ty1 == ty2
    | _ => false
  | .abs m1 ty1 e1', e2 =>
    match e2 with
    | .abs m2 ty2 e2' => m1 == m2 && ty1 == ty2 && LExpr.beq e1' e2'
    | _ => false
  | .quant m1 k1 ty1 tr1 e1', e2 =>
    match e2 with
    | .quant m2 k2 ty2 tr2 e2' =>
      m1 == m2 && k1 == k2 && ty1 == ty2 && LExpr.beq tr1 tr2 && LExpr.beq e1' e2'
    | _ => false
  | .app m1 fn1 e1', e2 =>
    match e2 with
    | .app m2 fn2 e2' => m1 == m2 && LExpr.beq fn1 fn2 && LExpr.beq e1' e2'
    | _ => false
  | .ite m1 c1 t1 e1', e2 =>
    match e2 with
    | .ite m2 c2 t2 e2' =>
      m1 == m2 && LExpr.beq c1 c2 && LExpr.beq t1 t2 && LExpr.beq e1' e2'
    | _ => false
  | .eq m1 e1a e1b, e2 =>
    match e2 with
    | .eq m2 e2a e2b => m1 == m2 && LExpr.beq e1a e2a && LExpr.beq e1b e2b
    | _ => false

instance [BEq T.base.Metadata] [BEq T.TypeType] [BEq T.base.Identifier] : BEq (LExpr T) where
  beq := LExpr.beq

-- First, prove that beq is sound and complete
theorem LExpr.beq_eq {T : LExprParamsT} [DecidableEq T.base.Metadata] [DecidableEq T.TypeType] [DecidableEq T.base.Identifier]
  (e1 e2 : LExpr T) : LExpr.beq e1 e2 = true ↔ e1 = e2 := by
  constructor
  · -- Soundness: beq = true → e1 = e2
    intro h
    induction e1 generalizing e2 with
    | const m1 c1 ty1 =>
      cases e2 with
      | const m2 c2 ty2 =>
        unfold beq at h
        simp only [Bool.and_eq_true] at h
        rcases h with ⟨⟨h1, h2⟩, h3⟩
        simp only [beq_iff_eq] at h1 h2 h3
        rw [h1, h2, h3]
      | _ =>
        unfold beq at h
        simp only [] at h
        contradiction
    | op m1 o1 ty1 =>
      cases e2 with
      | op m2 o2 ty2 =>
        unfold beq at h
        simp only [Bool.and_eq_true] at h
        rcases h with ⟨⟨h1, h2⟩, h3⟩
        simp only [beq_iff_eq] at h1 h2 h3
        rw [h1, h2, h3]
      | _ =>
        unfold beq at h
        simp only [] at h
        contradiction

    | bvar m1 i1 =>
      cases e2 with
      | bvar m2 i2 =>
        unfold beq at h
        simp only [Bool.and_eq_true] at h
        rcases h with ⟨h1, h2⟩
        simp only [beq_iff_eq] at h1 h2
        rw [h1, h2]
      | _ =>
        unfold beq at h
        simp only [] at h
        contradiction

    | fvar m1 n1 ty1 =>
      cases e2 with
      | fvar m2 n2 ty2 =>
        unfold beq at h
        simp only [Bool.and_eq_true] at h
        rcases h with ⟨⟨h1, h2⟩, h3⟩
        simp only [beq_iff_eq] at h1 h2 h3
        rw [h1, h2, h3]
      | _ =>
        unfold beq at h
        simp only [] at h
        contradiction

    | abs m1 ty1 e1' ih1 =>
      cases e2 with
      | abs m2 ty2 e2' =>
        unfold beq at h
        simp only [Bool.and_eq_true] at h
        rcases h with ⟨⟨h1, h2⟩, h3⟩
        simp only [beq_iff_eq] at h1 h2
        have h3' := ih1 e2' h3
        rw [h1, h2, h3']
      | _ =>
        unfold beq at h
        simp only [] at h
        contradiction

    | quant m1 k1 ty1 tr1 e1' ih1 ih2 =>
      cases e2 with
      | quant m2 k2 ty2 tr2 e2' =>
        unfold beq at h
        simp only [Bool.and_eq_true] at h
        rcases h with ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
        simp only [beq_iff_eq] at h1 h2 h3
        have h4' := ih1 tr2 h4  -- Pass tr2 as argument
        have h5' := ih2 e2' h5  -- Pass e2' as argument
        rw [h1, h2, h3, h4', h5']
      | _ =>
        unfold beq at h
        simp only [] at h
        contradiction

    | app m1 fn1 e1' ih1 ih2 =>
      cases e2 with
      | app m2 fn2 e2' =>
        unfold beq at h
        simp only [Bool.and_eq_true] at h
        rcases h with ⟨⟨h1, h2⟩, h3⟩
        simp only [beq_iff_eq] at h1
        have h2' := ih1 fn2 h2  -- Pass fn2 as argument
        have h3' := ih2 e2' h3  -- Pass e2' as argument
        rw [h1, h2', h3']
      | _ =>
        unfold beq at h
        simp only [] at h
        contradiction

    | ite m1 c1 t1 e1' ih1 ih2 ih3 =>
      cases e2 with
      | ite m2 c2 t2 e2' =>
        unfold beq at h
        simp only [Bool.and_eq_true] at h
        rcases h with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        simp only [beq_iff_eq] at h1
        have h2' := ih1 c2 h2   -- Pass c2 as argument
        have h3' := ih2 t2 h3   -- Pass t2 as argument
        have h4' := ih3 e2' h4  -- Pass e2' as argument
        rw [h1, h2', h3', h4']
      | _ =>
        unfold beq at h
        simp only [] at h
        contradiction

    | eq m1 e1a e1b ih1 ih2 =>
      cases e2 with
      | eq m2 e2a e2b =>
        unfold beq at h
        simp only [Bool.and_eq_true] at h
        rcases h with ⟨⟨h1, h2⟩, h3⟩
        simp only [beq_iff_eq] at h1
        have h2' := ih1 e2a h2  -- Pass e2a as argument
        have h3' := ih2 e2b h3  -- Pass e2b as argument
        rw [h1, h2', h3']
      | _ =>
        unfold beq at h
        simp only [] at h
        contradiction


  · -- Completeness: e1 = e2 → beq = true
    intro h
    rw [h]
    -- Prove that beq is reflexive
    induction e2 generalizing e1 with
    | const m c ty =>
      simp [LExpr.beq]
    | op m o ty =>
      simp [LExpr.beq]
    | bvar m i =>
      simp [LExpr.beq]
    | fvar m n ty =>
      simp [LExpr.beq]
    | abs m ty e ih =>
      simp [LExpr.beq]
      exact ih e rfl
    | quant m k ty tr e ih_tr ih_e =>
      simp [LExpr.beq]
      exact ⟨ih_tr tr rfl, ih_e e rfl⟩

    | app m fn e ih_fn ih_e =>
      simp [LExpr.beq]
      exact ⟨ih_fn fn rfl, ih_e e rfl⟩

    | ite m c t e ih_c ih_t ih_e =>
      simp [LExpr.beq]
      exact ⟨⟨ih_c c rfl, ih_t t rfl⟩, ih_e e rfl⟩

    | eq m ea eb ih_a ih_b =>
      simp [LExpr.beq]
      exact ⟨ih_a ea rfl, ih_b eb rfl⟩


-- Now use this theorem in DecidableEq
instance {T: LExprParamsT} [DecidableEq T.base.Metadata] [DecidableEq T.TypeType] [DecidableEq T.base.Identifier] : DecidableEq (LExpr T) :=
  fun e1 e2 =>
    if h : LExpr.beq e1 e2 then
      isTrue (LExpr.beq_eq e1 e2 |>.mp h)
    else
      isFalse (fun heq => h (LExpr.beq_eq e1 e2 |>.mpr heq))

instance {T: LExprParamsT} [DecidableEq T.base.Metadata] [DecidableEq T.TypeType] [DecidableEq T.base.Identifier] : DecidableEq (LExpr T) :=
  fun e1 e2 =>
    if h: LExpr.beq e1 e2 then
      isTrue (LExpr.beq_eq e1 e2 |>.mp h)
    else
      isFalse (fun heq => h (LExpr.beq_eq e1 e2 |>.mpr heq))

def LExpr.noTrigger {T : LExprParamsT} (m : T.base.Metadata) : LExpr T := .bvar m 0
def LExpr.allTr {T : LExprParamsT} (m : T.base.Metadata) (ty : Option T.TypeType) := @LExpr.quant T m .all ty
def LExpr.all {T : LExprParamsT} (m : T.base.Metadata) (ty : Option T.TypeType) := @LExpr.quant T m .all ty (LExpr.noTrigger m)
def LExpr.existTr {T : LExprParamsT} (m : T.base.Metadata) (ty : Option T.TypeType) := @LExpr.quant T m .exist ty
def LExpr.exist {T : LExprParamsT} (m : T.base.Metadata) (ty : Option T.TypeType) := @LExpr.quant T m .exist ty (LExpr.noTrigger m)

abbrev LExpr.absUntyped {T : LExprParamsT} (m : T.base.Metadata) := @LExpr.abs T m .none
abbrev LExpr.allUntypedTr {T : LExprParamsT} (m : T.base.Metadata) := @LExpr.quant T m .all .none
abbrev LExpr.allUntyped {T : LExprParamsT} (m : T.base.Metadata) := @LExpr.quant T m .all .none (LExpr.noTrigger m)
abbrev LExpr.existUntypedTr {T : LExprParamsT} (m : T.base.Metadata) := @LExpr.quant T m .exist .none
abbrev LExpr.existUntyped {T : LExprParamsT} (m : T.base.Metadata) := @LExpr.quant T m .exist .none (LExpr.noTrigger m)


def LExpr.sizeOf (T : LExprParamsT) [SizeOf T.base.Identifier] : LExpr T → Nat
  | LExpr.const _ _ _ => 1
  | LExpr.op _ _ _ => 1
  | LExpr.bvar _ _ => 1
  | LExpr.fvar _ _ _ => 1
  | LExpr.abs _ _ e => 2 + LExpr.sizeOf T e
  | LExpr.quant _ _ _ tr e => 3 + LExpr.sizeOf T e + LExpr.sizeOf T tr
  | LExpr.app _ fn e => 3 + LExpr.sizeOf T fn + LExpr.sizeOf T e
  | LExpr.ite _ c t e => 4 + LExpr.sizeOf T c + LExpr.sizeOf T t + LExpr.sizeOf T e
  | LExpr.eq _ e1 e2 => 3 + LExpr.sizeOf T e1 + LExpr.sizeOf T e2

instance (T : LExprParamsT) [SizeOf T.base.Identifier] : SizeOf (LExpr T) where
  sizeOf := LExpr.sizeOf T
---------------------------------------------------------------------

namespace LExpr

instance (T : LExprParamsT) [Inhabited T.base.Metadata] : Inhabited (LExpr T) where
  default := .const default "false" none

def LExpr.getVars (e : LExpr T) : List T.base.Identifier := match e with
  | .const _ _ _ => [] | .bvar _ _ => [] | .op _ _ _ => []
  | .fvar _ y _ => [y]
  | .abs _ _ e' => LExpr.getVars e'
  | .quant _ _ _ tr' e' => LExpr.getVars tr' ++ LExpr.getVars e'
  | .app _ e1 e2 => LExpr.getVars e1 ++ LExpr.getVars e2
  | .ite _ c t e => LExpr.getVars c ++ LExpr.getVars t ++ LExpr.getVars e
  | .eq _ e1 e2 => LExpr.getVars e1 ++ LExpr.getVars e2

def getFVarName? (T : LExprParamsT) (e : LExpr T) : Option T.base.Identifier :=
  match e with
  | .fvar _ name _ => some name
  | _ => none

def isConst (T : LExprParamsT) (e : LExpr T) : Bool :=
  match e with
  | .const _ _ _ => true
  | _ => false

@[match_pattern]
protected def true {T : LExprParams} (m : T.Metadata) : LExpr T.mono := .const m "true"  (some (.tcons "bool" []))

@[match_pattern]
protected def false {T : LExprParams} (m : T.Metadata) : LExpr T.mono := .const m "false"  (some (.tcons "bool" []))

def isTrue (T : LExprParamsT) (e : LExpr T) : Bool :=
  match e with
  | .const _ "true" _ => true
  | _ => false

def isFalse (T : LExprParamsT) (e : LExpr T) : Bool :=
  match e with
  | .const _ "false" _ => true
  | _ => false

/--
If `e` is an `LExpr` boolean, then denote that into a Lean `Bool`.
Note that we are type-agnostic here.
-/
def denoteBool {T : LExprParams} (e : LExpr T.mono) : Option Bool :=
  match e with
  | .const _ "true"  (some (.tcons "bool" [])) => some true
  | .const _ "true"  none => some true
  | .const _ "false" (some (.tcons "bool" [])) => some false
  | .const _ "false" none => some false
  | _ => none

/--
If `e` is an `LExpr` integer, then denote that into a Lean `Int`.
Note that we are type-agnostic here.
-/
def denoteInt {T : LExprParams} (e : LExpr T.mono) : Option Int :=
  match e with
  | .const _ x (some (.tcons "int" [])) => x.toInt?
  | .const _ x none => x.toInt?
  | _ => none

/--
If `e` is an `LExpr` real, then denote that into a Lean `String`.
Note that we are type-agnostic here.
-/
def denoteReal {T : LExprParams} (e : LExpr T.mono) : Option String :=
  match e with
  | .const _ x (some (.tcons "real" [])) => .some x
  | .const _ x none => .some x
  | _ => none

/--
If `e` is an `LExpr` bv<n>, then denote that into a Lean `BitVec n`.
Note that we are type-agnostic here.
-/
def denoteBitVec {T : LExprParams} (n : Nat) (e : LExpr T.mono) : Option (BitVec n) :=
  match e with
  | .const _ x (.some (.bitvec n')) =>
    if n == n' then .map (.ofNat n) x.toNat? else none
  | .const _ x none => .map (.ofNat n) x.toNat?
  | _ => none

/--
If `e` is an _annotated_ `LExpr` string, then denote that into a Lean `String`.
Note that unannotated strings are not denoted.
-/
def denoteString {T : LExprParams} (e : LExpr T.mono) : Option String :=
  match e with
  | .const _ c  (some (.tcons "string" [])) => some c
  | _ => none

def mkApp {T : LExprParamsT} (m : T.base.Metadata) (fn : LExpr T) (args : List (LExpr T)) : LExpr T :=
  match args with
  | [] => fn
  | a :: rest =>
    mkApp m (.app m fn a) rest

/--
Returns the metadata of `e`.
-/
def metadata {T : LExprParamsT} (e : LExpr T) : T.base.Metadata :=
  match e with
  | .const m _ _ => m
  | .op m _ _ => m
  | .bvar m _ => m
  | .fvar m _ _ => m
  | .abs m _ _ => m
  | .quant m _ _ _ _ => m
  | .app m _ _ => m
  | .ite m _ _ _ => m
  | .eq m _ _ => m


def replaceMetadata1 {T : LExprParamsT} (r: T.base.Metadata) (e : LExpr T) : LExpr T :=
  match e with
  | .const _ c ty => .const r c ty
  | .op _ o ty => .op r o ty
  | .bvar _ i => .bvar r i
  | .fvar _ name ty => .fvar r name ty
  | .abs _ ty e' => .abs r ty e'
  | .quant _ qk ty tr e' => .quant r qk ty tr e'
  | .app _ e1 e2 => .app r e1 e2
  | .ite _ c t e' => .ite r c t e'
  | .eq _ e1 e2 => .eq r e1 e2

/--
Compute the size of `e` as a tree.

Not optimized for execution efficiency, but can be used for termination
arguments.
-/
def size (T : LExprParamsT) (e : LExpr T) : Nat :=
  match e with
  | .const _ _ _ => 1
  | .op _ _ _ => 1
  | .bvar _ _ => 1
  | .fvar _ _ _ => 1
  | .abs _ _ e' => 1 + size T e'
  | .quant _ _ _ _ e' => 1 + size T e'
  | .app _ e1 e2 => 1 + size T e1 + size T e2
  | .ite _ c t f => 1 + size T c + size T t + size T f
  | .eq _ e1 e2 => 1 + size T e1 + size T e2

/--
Erase all type annotations from `e`.
-/
def eraseTypes {T : LExprParamsT} (e : LExpr T) : LExpr T :=
  match e with
  | .const m c _ => .const m c none
  | .op m o _ => .op m o none
  | .fvar m x _ => .fvar m x none
  | .bvar _ _ => e
  | .abs m ty e => .abs m ty (eraseTypes e)
  | .quant m qk ty tr e => .quant m qk ty (eraseTypes tr) (eraseTypes e)
  | .app m e1 e2 => .app m (eraseTypes e1) (eraseTypes e2)
  | .ite m c t f => .ite m (eraseTypes c) (eraseTypes t) (eraseTypes f)
  | .eq m e1 e2 => .eq m (eraseTypes e1) (eraseTypes e2)

---------------------------------------------------------------------

/- Formatting and Parsing of Lambda Expressions -/

instance (T : LExprParamsT) [Repr T.base.Identifier] [Repr T.TypeType] [Repr T.base.Metadata] : ToString (LExpr T) where
   toString a := toString (repr a)

private def formatLExpr (T : LExprParamsT) [ToFormat T.base.Identifier] [ToFormat T.TypeType] (e : LExpr T) :
    Format :=
  match e with
  | .const _ c ty =>
    match ty with
    | none => f!"#{c}"
    | some ty => f!"(#{c} : {ty})"
  | .op _ c ty =>
    match ty with
    | none => f!"~{c}"
    | some ty => f!"(~{c} : {ty})"
  | .bvar _ i => f!"%{i}"
  | .fvar _ x ty =>
    match ty with
    | none => f!"{x}"
    | some ty => f!"({x} : {ty})"
  | .abs _ _ e1 => Format.paren (f!"λ {formatLExpr T e1}")
  | .quant _ .all _ _ e1 => Format.paren (f!"∀ {formatLExpr T e1}")
  | .quant _ .exist _ _ e1 => Format.paren (f!"∃ {formatLExpr T e1}")
  | .app _ e1 e2 => Format.paren (formatLExpr T e1 ++ " " ++ formatLExpr T e2)
  | .ite _ c t e => Format.paren
                      ("if " ++ formatLExpr T c ++
                       " then " ++ formatLExpr T t ++ " else "
                       ++ formatLExpr T e)
  | .eq _ e1 e2 => Format.paren (formatLExpr T e1 ++ " == " ++ formatLExpr T e2)

instance (T : LExprParamsT) [ToFormat T.base.Identifier] [ToFormat T.TypeType] : ToFormat (LExpr T) where
  format := formatLExpr T

/-
Syntax for conveniently building `LExpr` terms with `LMonoTy`, scoped under the namespace
`LExpr.SyntaxMono`.
-/
namespace SyntaxMono
open Lean Elab Meta

class MkLExprParams (T : LExprParams) where
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

def elabLConstMono (T: LExprParams) [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lconstmono| #$n:num)  => do
    let none ← mkNone (mkConst ``LMonoTy)
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    return mkAppN (.const ``LExpr.const []) #[tMono, metadata, mkStrLit (toString n.getNat), none]
  | `(lconstmono| (#$n:num : $ty:lmonoty)) => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    return mkAppN (.const ``LExpr.const []) #[tMono, metadata, mkStrLit (toString n.getNat), lmonoty]
  | `(lconstmono| #-$n:num) => do
    let none ← mkNone (mkConst ``LMonoTy)
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    return mkAppN (.const ``LExpr.const []) #[tMono, metadata, mkStrLit ("-" ++ (toString n.getNat)), none]
  | `(lconstmono| (#-$n:num : $ty:lmonoty)) => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    return mkAppN (.const ``LExpr.const []) #[tMono, metadata, mkStrLit ("-" ++ (toString n.getNat)), lmonoty]
  | `(lconstmono| #true)    => do
    let none ← mkNone (mkConst ``LMonoTy)
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    return mkAppN (.const ``LExpr.const []) #[tMono, metadata, mkStrLit "true", none]
  | `(lconstmono| (#true : $ty:lmonoty))    => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    return mkAppN (.const ``LExpr.const []) #[tMono, metadata, mkStrLit "true", lmonoty]
  | `(lconstmono| #false)   =>  do
    let none ← mkNone (mkConst ``LMonoTy)
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    return mkAppN (.const ``LExpr.const []) #[tMono, metadata, mkStrLit "false", none]
  | `(lconstmono| (#false : $ty:lmonoty))    => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    return mkAppN (.const ``LExpr.const []) #[tMono, metadata, mkStrLit "false", lmonoty]
  | `(lconstmono| #$s:ident) => do
    let none ← mkNone (mkConst ``LMonoTy)
    let s := toString s.getId
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    return mkAppN (.const ``LExpr.const []) #[tMono, metadata, mkStrLit s, none]
  | `(lconstmono| (#$s:ident : $ty:lmonoty)) => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    let s := toString s.getId
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    return mkAppN (.const ``LExpr.const []) #[tMono, metadata, mkStrLit s, lmonoty]
  | _ => throwUnsupportedSyntax

declare_syntax_cat lopmono
scoped syntax "~" noWs lidentmono : lopmono
scoped syntax "(" lopmono ":" lmonoty ")" : lopmono
scoped syntax lopmono : lexprmono

def elabLOpMono (T : LExprParams)  [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lopmono| ~$s:lidentmono)  => do
    let none ← mkNone (mkConst ``LMonoTy)
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    return mkAppN (.const ``LExpr.op []) #[tMono, metadata, ← MkLExprParams.elabIdent T s, none]
  | `(lopmono| (~$s:lidentmono : $ty:lmonoty)) => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    return mkAppN (.const ``LExpr.op []) #[tMono, metadata, ← MkLExprParams.elabIdent T s, lmonoty]
  | _ => throwUnsupportedSyntax

declare_syntax_cat lbvarmono
scoped syntax "%" noWs num : lbvarmono
def elabLBVarMono (T : LExprParams)  [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lbvarmono| %$n:num) => do
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    return mkAppN (.const ``LExpr.bvar []) #[tMono, metadata, mkNatLit n.getNat]
  | _ => throwUnsupportedSyntax
scoped syntax lbvarmono : lexprmono

declare_syntax_cat lfvarmono
scoped syntax lidentmono : lfvarmono
scoped syntax "(" lidentmono ":" lmonoty ")" : lfvarmono

def elabLFVarMono (T : LExprParams)  [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lfvarmono| $i:lidentmono) => do
    let none ← mkNone (mkConst ``LMonoTy)
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    return mkAppN (.const ``LExpr.fvar []) #[tMono, metadata, ← MkLExprParams.elabIdent T i, none]
  | `(lfvarmono| ($i:lidentmono : $ty:lmonoty)) => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    return mkAppN (.const ``LExpr.fvar []) #[tMono, metadata, ← MkLExprParams.elabIdent T i, lmonoty]
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
partial def elabLExprMono (T : LExprParams) [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lexprmono| $c:lconstmono) => elabLConstMono T c
  | `(lexprmono| $o:lopmono) => elabLOpMono T o
  | `(lexprmono| $b:lbvarmono) => elabLBVarMono T b
  | `(lexprmono| $f:lfvarmono) => elabLFVarMono T f
  | `(lexprmono| λ $e:lexprmono) => do
     let e' ← elabLExprMono T e
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     return mkAppN (.const ``LExpr.absUntyped []) #[tMono, metadata, e']
  | `(lexprmono| λ ($mty:lmonoty): $e:lexprmono) => do
     let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy mty
     let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
     let e' ← elabLExprMono T e
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     return mkAppN (.const ``LExpr.abs []) #[tMono, metadata, lmonoty, e']
  | `(lexprmono| ∀ $e:lexprmono) => do
     let e' ← elabLExprMono T e
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     return mkAppN (.const ``LExpr.allUntyped []) #[tMono, metadata, e']
  | `(lexprmono| ∀ {$tr}$e:lexprmono) => do
     let e' ← elabLExprMono T e
     let tr' ← elabLExprMono T tr
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     return mkAppN (.const ``LExpr.allUntypedTr []) #[tMono, metadata, tr', e']
  | `(lexprmono| ∀ ($mty:lmonoty): $e:lexprmono) => do
     let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy mty
     let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
     let e' ← elabLExprMono T e
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     return mkAppN (.const ``LExpr.all []) #[tMono, metadata, lmonoty, e']
  | `(lexprmono| ∀ ($mty:lmonoty):{$tr} $e:lexprmono) => do
     let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy mty
     let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
     let e' ← elabLExprMono T e
     let tr' ← elabLExprMono T tr
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     return mkAppN (.const ``LExpr.allTr []) #[tMono, metadata, lmonoty, tr', e']
  | `(lexprmono| ∃ ($mty:lmonoty): $e:lexprmono) => do
     let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy mty
     let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
     let e' ← elabLExprMono T e
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     return mkAppN (.const ``LExpr.exist []) #[tMono, metadata, lmonoty, e']
  | `(lexprmono| ∃ ($mty:lmonoty):{$tr} $e:lexprmono) => do
     let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy mty
     let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
     let e' ← elabLExprMono T e
     let tr' ← elabLExprMono T tr
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     return mkAppN (.const ``LExpr.existTr []) #[tMono, metadata, lmonoty, tr', e']
  | `(lexprmono| ∃ $e:lexprmono) => do
     let e' ← elabLExprMono T e
     let metadata ← mkAppM ``Unit.unit #[]
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     return mkAppN (.const ``LExpr.existUntyped []) #[tMono, metadata, e']
  | `(lexprmono| ∃{$tr} $e:lexprmono) => do
     let e' ← elabLExprMono T e
     let tr' ← elabLExprMono T tr
     let metadata ← mkAppM ``Unit.unit #[]
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     return mkAppN (.const ``LExpr.existUntypedTr []) #[tMono, metadata, tr', e']
  | `(lexprmono| ($e1:lexprmono $e2:lexprmono)) => do
     let e1' ← elabLExprMono T e1
     let e2' ← elabLExprMono T e2
     let metadata ← mkAppM ``Unit.unit #[]
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     return mkAppN (.const ``LExpr.app []) #[tMono, metadata, e1', e2']
  | `(lexprmono| $e1:lexprmono == $e2:lexprmono) => do
     let e1' ← elabLExprMono T e1
     let e2' ← elabLExprMono T e2
     let metadata ← mkAppM ``Unit.unit #[]
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     return mkAppN (.const ``LExpr.eq []) #[tMono, metadata, e1', e2']
  | `(lexprmono| if $e1:lexprmono then $e2:lexprmono else $e3:lexprmono) => do
     let e1' ← elabLExprMono T e1
     let e2' ← elabLExprMono T e2
     let e3' ← elabLExprMono T e3
     let metadata ← mkAppM ``Unit.unit #[]
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     return mkAppN (.const ``LExpr.ite []) #[tMono, metadata, e1', e2', e3']
  | `(lexprmono| ($e:lexprmono)) => elabLExprMono T e
  | _ => throwUnsupportedSyntax

scoped syntax ident : lidentmono
/-- Elaborator for String identifiers, construct a String instance -/
def elabStrIdent : Lean.Syntax → MetaM Expr
  | `(lidentmono| $s:ident) => do
    let s := s.getId
    return mkStrLit s.toString
  | _ => throwUnsupportedSyntax

instance : MkLExprParams ⟨Unit, String⟩ where
  elabIdent := elabStrIdent
  toExpr := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (mkConst ``String)

elab "esM[" e:lexprmono "]" : term => elabLExprMono (T:=⟨Unit, String⟩) e

open LTy.Syntax

/--
info: app () (absUntyped () (bvar () 0)) (const () "5" none) : LExpr { Metadata := Unit, Identifier := String }.mono
-/
#guard_msgs in
#check esM[((λ %0) #5)]

/--
info: app () (abs () (some (LMonoTy.tcons "bool" [])) (bvar () 0))
  (const () "true" none) : LExpr { Metadata := Unit, Identifier := String }.mono
-/
#guard_msgs in
#check esM[((λ (bool): %0) #true)]

/--
info: allUntyped () (eq () (bvar () 0) (const () "5" none)) : LExpr { Metadata := Unit, Identifier := String }.mono
-/
#guard_msgs in
#check esM[(∀ %0 == #5)]

/--
info: existUntyped () (eq () (bvar () 0) (const () "5" none)) : LExpr { Metadata := Unit, Identifier := String }.mono
-/
#guard_msgs in
#check esM[(∃ %0 == #5)]

/--
info: exist () (some (LMonoTy.tcons "int" []))
  (eq () (bvar () 0) (const () "5" none)) : LExpr { Metadata := Unit, Identifier := String }.mono
-/
#guard_msgs in
#check esM[(∃ (int): %0 == #5)]

/--
info: fvar () "x" (some (LMonoTy.tcons "bool" [])) : LExpr { Metadata := Unit, Identifier := String }.mono
-/
#guard_msgs in
#check esM[(x : bool)]

-- axiom [updateSelect]: forall m: Map k v, kk: k, vv: v :: m[kk := vv][kk] == vv;
/--
info: all () (some (LMonoTy.tcons "Map" [LMonoTy.ftvar "k", LMonoTy.ftvar "v"]))
  (all () (some (LMonoTy.ftvar "k"))
    (all () (some (LMonoTy.ftvar "v"))
      (eq ()
        (app ()
          (app ()
            (op () "select"
              (some
                (LMonoTy.tcons "Map"
                  [LMonoTy.ftvar "k",
                    LMonoTy.tcons "arrow"
                      [LMonoTy.ftvar "v", LMonoTy.tcons "arrow" [LMonoTy.ftvar "k", LMonoTy.ftvar "v"]]])))
            (app ()
              (app ()
                (app ()
                  (op () "update"
                    (some
                      (LMonoTy.tcons "Map"
                        [LMonoTy.ftvar "k",
                          LMonoTy.tcons "arrow"
                            [LMonoTy.ftvar "v",
                              LMonoTy.tcons "arrow"
                                [LMonoTy.ftvar "k",
                                  LMonoTy.tcons "arrow"
                                    [LMonoTy.ftvar "v",
                                      LMonoTy.tcons "Map" [LMonoTy.ftvar "k", LMonoTy.ftvar "v"]]]]])))
                  (bvar () 2))
                (bvar () 1))
              (bvar () 0)))
          (bvar () 1))
        (bvar () 0)))) : LExpr { Metadata := Unit, Identifier := String }.mono
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

class MkLExprParams (Identifier : Type) where
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

def elabLConst (Identifier : Type) [MkLExprParams Identifier] : Lean.Syntax → MetaM Expr
  | `(lconst| #$n:num)  => do
    let none ← mkNone (mkConst ``LTy)
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.const []) #[tParams, metadata, mkStrLit (toString n.getNat), none]
  | `(lconst| (#$n:num : $ty:lty)) => do
    let lty ← Lambda.LTy.Syntax.elabLTy ty
    let lty ← mkSome (mkConst ``LTy) lty
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.const []) #[tParams, metadata, mkStrLit (toString n.getNat), lty]
  | `(lconst| #-$n:num) => do
    let none ← mkNone (mkConst ``LTy)
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.const []) #[tParams, metadata, mkStrLit ("-" ++ (toString n.getNat)), none]
  | `(lconst| (#-$n:num : $ty:lty)) => do
    let lty ← Lambda.LTy.Syntax.elabLTy ty
    let lty ← mkSome (mkConst ``LTy) lty
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.const []) #[tParams, metadata, mkStrLit ("-" ++ (toString n.getNat)), lty]
  | `(lconst| #true)    => do
    let none ← mkNone (mkConst ``LTy)
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.const []) #[tParams, metadata, mkStrLit "true", none]
  | `(lconst| (#true : $ty:lty))    => do
    let lty ← Lambda.LTy.Syntax.elabLTy ty
    let lty ← mkSome (mkConst ``LTy) lty
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.const []) #[tParams, metadata, mkStrLit "true", lty]
  | `(lconst| #false)   =>  do
    let none ← mkNone (mkConst ``LTy)
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.const []) #[tParams, metadata, mkStrLit "false", none]
  | `(lconst| (#false : $ty:lty))    => do
    let lty ← Lambda.LTy.Syntax.elabLTy ty
    let lty ← mkSome (mkConst ``LTy) lty
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.const []) #[tParams, metadata, mkStrLit "false", lty]
  | `(lconst| #$s:ident) => do
    let none ← mkNone (mkConst ``LTy)
    let s := toString s.getId
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.const []) #[tParams, metadata, mkStrLit s, none]
  | `(lconst| (#$s:ident : $ty:lty)) => do
    let lty ← Lambda.LTy.Syntax.elabLTy ty
    let lty ← mkSome (mkConst ``LTy) lty
    let s := toString s.getId
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.const []) #[tParams, metadata, mkStrLit s, lty]
  | _ => throwUnsupportedSyntax

declare_syntax_cat lop
scoped syntax "~" noWs lident : lop
scoped syntax "(" lop ":" lty ")" : lop
scoped syntax lop : lexpr

def elabLOp (Identifier : Type) [MkLExprParams Identifier] : Lean.Syntax → MetaM Expr
  | `(lop| ~$s:lident)  => do
    let none ← mkNone (mkConst ``LTy)
    let ident ← MkLExprParams.elabIdent Identifier s
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.op []) #[tParams, metadata, ident, none]
  | `(lop| (~$s:lident : $ty:lty)) => do
    let lty ← Lambda.LTy.Syntax.elabLTy ty
    let lty ← mkSome (mkConst ``LTy) lty
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.op []) #[tParams, metadata, ← MkLExprParams.elabIdent Identifier s, lty]
  | _ => throwUnsupportedSyntax

declare_syntax_cat lbvar
scoped syntax "%" noWs num : lbvar
def elabLBVar (Identifier : Type) [MkLExprParams Identifier] : Lean.Syntax → MetaM Expr
  | `(lbvar| %$n:num) => do
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.bvar []) #[tParams, metadata, mkNatLit n.getNat]
  | _ => throwUnsupportedSyntax
scoped syntax lbvar : lexpr

declare_syntax_cat lfvar
scoped syntax lident : lfvar
scoped syntax "(" lident ":" lty ")" : lfvar

def elabLFVar (Identifier : Type) [MkLExprParams Identifier] : Lean.Syntax → MetaM Expr
  | `(lfvar| $i:lident) => do
    let none ← mkNone (mkConst ``LTy)
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.fvar []) #[tParams, metadata, ← MkLExprParams.elabIdent Identifier i, none]
  | `(lfvar| ($i:lident : $ty:lty)) => do
    let lty ← Lambda.LTy.Syntax.elabLTy ty
    let lty ← mkSome (mkConst ``LTy) lty
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.fvar []) #[tParams, metadata, ← MkLExprParams.elabIdent Identifier i, lty]
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
partial def elabLExpr (Identifier : Type) [MkLExprParams Identifier] : Lean.Syntax → MetaM Expr
  | `(lexpr| $c:lconst) => elabLConst Identifier c
  | `(lexpr| $o:lop) => elabLOp Identifier o
  | `(lexpr| $b:lbvar) => elabLBVar Identifier b
  | `(lexpr| $f:lfvar) => elabLFVar Identifier f
  | `(lexpr| λ $e:lexpr) => do
     let e' ← elabLExpr Identifier e
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.absUntyped []) #[tParams, metadata, e']
  | `(lexpr| λ ($mty:lty): $e:lexpr) => do
     let lty ← Lambda.LTy.Syntax.elabLTy mty
     let lty ← mkSome (mkConst ``LTy) lty
     let e' ← elabLExpr Identifier e
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.abs []) #[tParams, metadata, lty, e']
  | `(lexpr| ∀ $e:lexpr) => do
     let e' ← elabLExpr Identifier e
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.allUntyped []) #[tParams, metadata, e']
  | `(lexpr| ∀{$tr}$e:lexpr) => do
     let e' ← elabLExpr Identifier e
     let tr' ← elabLExpr Identifier tr
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.allUntypedTr []) #[tParams, metadata, tr', e']
  | `(lexpr| ∀ ($mty:lty): $e:lexpr) => do
     let lty ← Lambda.LTy.Syntax.elabLTy mty
     let lty ← mkSome (mkConst ``LTy) lty
     let e' ← elabLExpr Identifier e
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.all []) #[tParams, metadata, lty, e']
  | `(lexpr| ∀ ($mty:lty): {$tr}$e:lexpr) => do
     let lty ← Lambda.LTy.Syntax.elabLTy mty
     let lty ← mkSome (mkConst ``LTy) lty
     let e' ← elabLExpr Identifier e
     let tr' ← elabLExpr Identifier tr
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.allTr []) #[tParams, metadata, lty, tr', e']
  | `(lexpr| ∃ ($mty:lty): $e:lexpr) => do
     let lty ← Lambda.LTy.Syntax.elabLTy mty
     let lty ← mkSome (mkConst ``LTy) lty
     let e' ← elabLExpr Identifier e
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.exist []) #[tParams, metadata, lty, e']
  | `(lexpr| ∃ ($mty:lty): {$tr}$e:lexpr) => do
     let lty ← Lambda.LTy.Syntax.elabLTy mty
     let lty ← mkSome (mkConst ``LTy) lty
     let e' ← elabLExpr Identifier e
     let tr' ← elabLExpr Identifier tr
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.existTr []) #[tParams, metadata, lty, tr', e']
  | `(lexpr| ∃ $e:lexpr) => do
     let e' ← elabLExpr Identifier e
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.existUntyped []) #[tParams, metadata, e']
  | `(lexpr| ∃ {$tr} $e:lexpr) => do
     let e' ← elabLExpr Identifier e
     let tr' ← elabLExpr Identifier tr
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.existUntypedTr []) #[tParams, metadata, tr', e']
  | `(lexpr| ($e1:lexpr $e2:lexpr)) => do
     let e1' ← elabLExpr Identifier e1
     let e2' ← elabLExpr Identifier e2
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.app []) #[tParams, metadata, e1', e2']
  | `(lexpr| $e1:lexpr == $e2:lexpr) => do
     let e1' ← elabLExpr Identifier e1
     let e2' ← elabLExpr Identifier e2
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.eq []) #[tParams, metadata, e1', e2']
  | `(lexpr| if $e1:lexpr then $e2:lexpr else $e3:lexpr) => do
     let e1' ← elabLExpr Identifier e1
     let e2' ← elabLExpr Identifier e2
     let e3' ← elabLExpr Identifier e3
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (MkLExprParams.toExpr Identifier)
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.ite []) #[tParams, metadata, e1', e2', e3']
  | `(lexpr| ($e:lexpr)) => elabLExpr Identifier e
  | _ => throwUnsupportedSyntax

scoped syntax ident : lident
/-- Elaborator for String identifiers, construct a String instance -/
def elabStrIdent : Lean.Syntax → MetaM Expr
  | `(lident| $s:ident) => do
    let s := s.getId
    return mkStrLit s.toString
  | _ => throwUnsupportedSyntax

instance : MkLExprParams String where
  elabIdent := elabStrIdent
  toExpr := .const ``String []

elab "es[" e:lexpr "]" : term => elabLExpr (Identifier:=String) e

open LTy.Syntax

/--
info: app () (absUntyped () (bvar () 0))
  (const () "5" none) : LExpr { base := { Metadata := Unit, Identifier := String }, TypeType := LTy }
-/
#guard_msgs in
#check es[((λ %0) #5)]

/--
info: app () (abs () (some (LTy.forAll [] (LMonoTy.tcons "bool" []))) (bvar () 0))
  (const () "true" none) : LExpr { base := { Metadata := Unit, Identifier := String }, TypeType := LTy }
-/
#guard_msgs in
#check es[((λ (bool): %0) #true)]

/--
info: allUntyped ()
  (eq () (bvar () 0)
    (const () "5" none)) : LExpr { base := { Metadata := Unit, Identifier := String }, TypeType := LTy }
-/
#guard_msgs in
#check es[(∀ %0 == #5)]

/--
info: existUntyped ()
  (eq () (bvar () 0)
    (const () "5" none)) : LExpr { base := { Metadata := Unit, Identifier := String }, TypeType := LTy }
-/
#guard_msgs in
#check es[(∃ %0 == #5)]

/--
info: exist () (some (LTy.forAll [] (LMonoTy.tcons "int" [])))
  (eq () (bvar () 0)
    (const () "5" none)) : LExpr { base := { Metadata := Unit, Identifier := String }, TypeType := LTy }
-/
#guard_msgs in
#check es[(∃ (int): %0 == #5)]

/--
info: fvar () "x"
  (some
    (LTy.forAll []
      (LMonoTy.tcons "bool" []))) : LExpr { base := { Metadata := Unit, Identifier := String }, TypeType := LTy }
-/
#guard_msgs in
#check es[(x : bool)]

-- axiom [updateSelect]: forall m: Map k v, kk: k, vv: v :: m[kk := vv][kk] == vv;
/--
info: all () (some (LTy.forAll [] (LMonoTy.tcons "Map" [LMonoTy.ftvar "k", LMonoTy.ftvar "v"])))
  (all () (some (LTy.forAll [] (LMonoTy.ftvar "k")))
    (all () (some (LTy.forAll [] (LMonoTy.ftvar "v")))
      (eq ()
        (app ()
          (app ()
            (op () "select"
              (some
                (LTy.forAll []
                  (LMonoTy.tcons "Map"
                    [LMonoTy.ftvar "k",
                      LMonoTy.tcons "arrow"
                        [LMonoTy.ftvar "v", LMonoTy.tcons "arrow" [LMonoTy.ftvar "k", LMonoTy.ftvar "v"]]]))))
            (app ()
              (app ()
                (app ()
                  (op () "update"
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
                                        LMonoTy.tcons "Map" [LMonoTy.ftvar "k", LMonoTy.ftvar "v"]]]]]))))
                  (bvar () 2))
                (bvar () 1))
              (bvar () 0)))
          (bvar () 1))
        (bvar () 0)))) : LExpr { base := { Metadata := Unit, Identifier := String }, TypeType := LTy }
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
