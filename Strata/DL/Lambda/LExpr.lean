/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.Identifiers
import Strata.DL.Lambda.MetaData
import Strata.DL.Util.DecidableEq

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
  /-- The type of metadata allowed on expressions. -/
  Metadata: Type
  /-- The type of metadata allowed on identifiers. -/
  IDMeta : Type
  deriving Inhabited

/--
Extended LExprParams that includes TypeType parameter.
-/
structure LExprParamsT : Type 1 where
  /-- The base parameters, with the types for expression and identifier metadata. -/
  base : LExprParams
  /-- The type of types used to annotate expressions. -/
  TypeType : Type
  deriving Inhabited

/--
Dot notation syntax: T.mono transforms LExprParams into LExprParamsT with LMonoTy.
-/
abbrev LExprParams.mono (T : LExprParams) : LExprParamsT :=
  ⟨T, LMonoTy⟩

abbrev LExprParams.Identifier (T : LExprParams) := Lambda.Identifier T.IDMeta

structure Typed (T: Type) where
  underlying: T
  type: LMonoTy

-- Metadata annotated with a type
abbrev LExprParams.typed (T: LExprParams): LExprParams :=
  ⟨ Typed T.Metadata, T.IDMeta ⟩

abbrev LExprParamsT.typed (T: LExprParamsT): LExprParamsT :=
  ⟨T.base.typed, LMonoTy⟩

/--
Lambda constants.

Constants are integers, strings, reals, bitvectors of a fixed length, or
booleans.
-/
inductive LConst : Type where
  /-- An unbounded integer constant. -/
  | intConst (i: Int)

  /-- A string constant, using Lean's `String` type for a sequence of Unicode
  code points encoded with UTF-8. -/
  | strConst (s: String)

  /-- A real constant, represented as a rational number. -/
  | realConst (r: Rat)

  /-- A bit vector constant, represented using Lean's `BitVec` type. -/
  | bitvecConst (n: Nat) (b: BitVec n)

  /-- A Boolean constant. -/
  | boolConst (b: Bool)
deriving Repr, DecidableEq

/--
Lambda expressions with quantifiers.

Like Lean's own expressions, we use the locally nameless
representation for this abstract syntax.
See this [paper](https://chargueraud.org/research/2009/ln/main.pdf)
for details.

We leave placeholders for type annotations only for constants
(`.const`), operations (`.op`), binders (`.abs`, `.quant`), and free
variables (`.fvar`).

LExpr is parameterized by `LExprParamsT`, which includes arbitrary metadata,
user-allowed type annotations (optional), and special metadata to attach to
`Identifier`s. Type inference adds any missing type annotations.
-/
inductive LExpr (T : LExprParamsT) : Type where
  /-- A constant (in the sense of literals). -/
  | const   (m: T.base.Metadata) (c: LConst)
  /-- A built-in operation, referred to by name. -/
  | op      (m: T.base.Metadata) (o : Identifier T.base.IDMeta) (ty : Option T.TypeType)
  /-- A bound variable, in de Bruijn form. -/
  | bvar    (m: T.base.Metadata) (deBruijnIndex : Nat)
  /-- A free variable, with an optional type annotation. -/
  | fvar    (m: T.base.Metadata) (name : Identifier T.base.IDMeta) (ty : Option T.TypeType)
  /-- An abstraction, where `ty` the is (optional) type of bound variable. -/
  | abs     (m: T.base.Metadata) (ty : Option T.TypeType) (e : LExpr T)
  /-- A quantified expression, where `k` indicates whether it is universally or
  existentially quantified, `ty` is the type of bound variable, and `trigger` is
  a trigger pattern (primarily for use with SMT). -/
  | quant   (m: T.base.Metadata) (k : QuantifierKind) (ty : Option T.TypeType) (trigger: LExpr T) (e : LExpr T)
  /-- A function application. -/
  | app     (m: T.base.Metadata) (fn e : LExpr T)
  /-- A conditional expression. This is a constructor rather than a built-in
  operation because it occurs so frequently. -/
  | ite     (m: T.base.Metadata) (c t e : LExpr T)
  /-- An equality expression. This is a constructor rather than a built-in
  operation because it occurs so frequently. -/
  | eq      (m: T.base.Metadata) (e1 e2 : LExpr T)

instance [Repr T.base.Metadata] [Repr T.TypeType] [Repr T.base.IDMeta] : Repr (LExpr T) where
  reprPrec e prec :=
    let rec go : LExpr T → Std.Format
      | .const m c =>
        f!"LExpr.const {repr m} {repr c}"
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
@[grind]
def LExpr.beq [BEq T.base.Metadata] [BEq T.TypeType] [BEq (Identifier T.base.IDMeta)] : LExpr T → LExpr T → Bool
  | .const m1 c1, e2 =>
    match e2 with
    | .const m2 c2 => m1 == m2 && c1 == c2
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

instance [BEq T.base.Metadata] [BEq T.TypeType] [BEq (Identifier T.base.IDMeta)] : BEq (LExpr T) where
  beq := LExpr.beq

-- First, prove that beq is sound and complete
theorem LExpr.beq_eq {T : LExprParamsT} [DecidableEq T.base.Metadata] [DecidableEq T.TypeType] [DecidableEq T.base.IDMeta]
  (e1 e2 : LExpr T) : LExpr.beq e1 e2 = true ↔ e1 = e2 := by
  solve_beq e1 e2

-- Now use this theorem in DecidableEq
instance {T: LExprParamsT} [DecidableEq T.base.Metadata] [DecidableEq T.TypeType] [DecidableEq T.base.IDMeta] : DecidableEq (LExpr T) :=
  fun e1 e2 =>
    if h : LExpr.beq e1 e2 then
      isTrue (LExpr.beq_eq e1 e2 |>.mp h)
    else
      isFalse (fun heq => h (LExpr.beq_eq e1 e2 |>.mpr heq))

def LExpr.noTrigger {T : LExprParamsT} (m : T.base.Metadata) : LExpr T := .bvar m 0
def LExpr.allTr {T : LExprParamsT} (m : T.base.Metadata) (ty : Option T.TypeType) := @LExpr.quant T m .all ty
def LExpr.all {T : LExprParamsT} (m : T.base.Metadata) (ty : Option T.TypeType) := @LExpr.quant T m .all ty (LExpr.noTrigger m)
def LExpr.existTr {T : LExprParamsT} (m : T.base.Metadata) (ty : Option T.TypeType) := @LExpr.quant T m .exist ty
def LExpr.exist {T : LExprParamsT} (m : T.base.Metadata) (ty : Option T.TypeType) := @LExpr.quant T m .exist ty (LExpr.noTrigger m)

@[match_pattern]
def LExpr.intConst (m : T.base.Metadata) (n: Int) : LExpr T := .const m <| LConst.intConst n
@[match_pattern]
def LExpr.strConst (m : T.base.Metadata) (s: String) : LExpr T := .const m <| LConst.strConst s
@[match_pattern]
def LExpr.realConst (m : T.base.Metadata) (r: Rat) : LExpr T := .const m <| LConst.realConst r
@[match_pattern]
def LExpr.bitvecConst (m : T.base.Metadata) (n: Nat) (b: BitVec n) : LExpr T := .const m <| LConst.bitvecConst n b
@[match_pattern]
def LExpr.boolConst (m : T.base.Metadata) (b: Bool) : LExpr T := .const m <| LConst.boolConst b

abbrev LExpr.absUntyped {T : LExprParamsT} (m : T.base.Metadata) := @LExpr.abs T m .none
abbrev LExpr.allUntypedTr {T : LExprParamsT} (m : T.base.Metadata) := @LExpr.quant T m .all .none
abbrev LExpr.allUntyped {T : LExprParamsT} (m : T.base.Metadata) := @LExpr.quant T m .all .none (LExpr.noTrigger m)
abbrev LExpr.existUntypedTr {T : LExprParamsT} (m : T.base.Metadata) := @LExpr.quant T m .exist .none
abbrev LExpr.existUntyped {T : LExprParamsT} (m : T.base.Metadata) := @LExpr.quant T m .exist .none (LExpr.noTrigger m)

@[simp]
def LExpr.sizeOf: LExpr T → Nat
  | LExpr.abs _ _ e => 2 + sizeOf e
  | LExpr.quant _ _ _ tr e => 3 + sizeOf e + sizeOf tr
  | LExpr.app _ fn e => 3 + sizeOf fn + sizeOf e
  | LExpr.ite _ c t e => 4 + sizeOf c + sizeOf t + sizeOf e
  | LExpr.eq _ e1 e2 => 3 + sizeOf e1 + sizeOf e2
  | _ => 1

instance  : SizeOf (LExpr T) where
  sizeOf := LExpr.sizeOf

/--
Get type of a constant `c`
-/
def LConst.ty (c: LConst) : LMonoTy :=
  match c with
  | .intConst _ => .int
  | .strConst _ => .string
  | .bitvecConst n _ => .bitvec n
  | .realConst _ => .real
  | .boolConst _ => .bool

/--
Get type name of a constant `c` (e.g. "int")
-/
def LConst.tyName (c: LConst) : String :=
  match c with
  | .intConst _ => "int"
  | .strConst _ => "string"
  | .bitvecConst _ _ => "bitvec"
  | .realConst _ => "real"
  | .boolConst _ => "bool"

/--
Get type name of a constant `c` as a Format (e.g. "Integers")
-/
def LConst.tyNameFormat (c: LConst) : Format :=
  match c with
  | .intConst _ => f!"Integers"
  | .strConst _ => f!"Strings"
  | .bitvecConst n _ => f!"Bit vectors of size {n}"
  | .realConst _ => f!"Reals"
  | .boolConst _ => f!"Booleans"

---------------------------------------------------------------------

namespace LExpr

instance (T : LExprParamsT) [Inhabited T.base.Metadata] : Inhabited (LExpr T) where
  default := .boolConst default false

def LExpr.getVars (e : LExpr T) : List (Identifier T.base.IDMeta) := match e with
  | .const _ _ => [] | .bvar _ _ => [] | .op _ _ _ => []
  | .fvar _ y _ => [y]
  | .abs _ _ e' => LExpr.getVars e'
  | .quant _ _ _ tr' e' => LExpr.getVars tr' ++ LExpr.getVars e'
  | .app _ e1 e2 => LExpr.getVars e1 ++ LExpr.getVars e2
  | .ite _ c t e => LExpr.getVars c ++ LExpr.getVars t ++ LExpr.getVars e
  | .eq _ e1 e2 => LExpr.getVars e1 ++ LExpr.getVars e2

def getOps (e : LExpr T) := match e with
  | .op _ name _ => [name]
  | .const _ _ => [] | .bvar _ _ => [] | .fvar _ _ _ => []
  | .abs _ _ e' => getOps e'
  | .quant _ _ _ tr e' =>
    -- NOTE: We also get all ops in the triggers here.
    getOps tr ++ getOps e'
  | .app _ e1 e2 => getOps e1 ++ getOps e2
  | .ite _ c t e => getOps c ++ getOps t ++ getOps e
  | .eq _ e1 e2 => getOps e1 ++ getOps e2

def getFVarName? {T : LExprParamsT} (e : LExpr T) : Option (Identifier T.base.IDMeta) :=
  match e with
  | .fvar _ name _ => some name
  | _ => none

def isConst {T : LExprParamsT} (e : LExpr T) : Bool :=
  match e with
  | .const _ _ => true
  | _ => false

def isOp (e : LExpr T) : Bool :=
  match e with
  | .op _ _ _ => true
  | _ => false

@[match_pattern]
protected def true {T : LExprParams} (m : T.Metadata) : LExpr T.mono := .boolConst m true

@[match_pattern]
protected def false {T : LExprParams} (m : T.Metadata) : LExpr T.mono := .boolConst m false

def isTrue (T : LExprParamsT) (e : LExpr T) : Bool :=
  match e with
  | .boolConst _ true => true
  | _ => false

def isFalse (T : LExprParamsT) (e : LExpr T) : Bool :=
  match e with
  | .boolConst _ false => true
  | _ => false

/-- An iterated/multi-argument lambda with arguments of types `tys` and body `body`-/
def absMulti (m: Metadata) (tys: List TypeType) (body: LExpr ⟨⟨Metadata, IDMeta⟩, TypeType⟩)
    : LExpr ⟨⟨Metadata, IDMeta⟩, TypeType⟩ :=
  List.foldr (fun ty e => .abs m (.some ty) e) body tys

/-- An iterated/multi-argument lambda with n inferred arguments and body `body`-/
def absMultiInfer (m: Metadata) (n: Nat) (body: LExpr ⟨⟨Metadata, IDMeta⟩, TypeType⟩)
    : LExpr ⟨⟨Metadata, IDMeta⟩, TypeType⟩ :=
  List.foldr (fun _ e => .abs m .none e) body (List.range n)

/--
If `e` is an `LExpr` boolean, then denote that into a Lean `Bool`.
-/
def denoteBool {T : LExprParams} (e : LExpr ⟨T, TypeType⟩) : Option Bool :=
  match e with
  | .boolConst _ b => some b
  | _ => none

/--
If `e` is an `LExpr` integer, then denote that into a Lean `Int`.
-/
def denoteInt {T : LExprParams} (e : LExpr ⟨T, TypeType⟩) : Option Int :=
  match e with
  | .intConst _ x => x
  | _ => none

/--
If `e` is an `LExpr` real, then denote that into a Lean `Rat`.
-/
def denoteReal {T : LExprParams} (e : LExpr ⟨T, TypeType⟩) : Option Rat :=
  match e with
  | .realConst _ r => some r
  | _ => none

/--
If `e` is an `LExpr` bv<n>, then denote that into a Lean `BitVec n`.
-/
def denoteBitVec {T : LExprParams} (n : Nat) (e : LExpr ⟨T, TypeType⟩) : Option (BitVec n) :=
  match e with
  | .bitvecConst _ n' b => if n == n' then some (BitVec.ofNat n b.toNat) else none
  | _ => none

/--
If `e` is an `LExpr` string, then denote that into a Lean `String`.
-/
def denoteString {T : LExprParams} (e : LExpr T.mono) : Option String :=
  match e with
  | .strConst _ s => some s
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
  | .const m _ => m
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
  | .const _ c => .const r c
  | .op _ o ty => .op r o ty
  | .bvar _ i => .bvar r i
  | .fvar _ name ty => .fvar r name ty
  | .abs _ ty e' => .abs r ty e'
  | .quant _ qk ty tr e' => .quant r qk ty tr e'
  | .app _ e1 e2 => .app r e1 e2
  | .ite _ c t e' => .ite r c t e'
  | .eq _ e1 e2 => .eq r e1 e2


/--
Transform metadata in an expression using a callback function.
-/
def replaceMetadata {T : LExprParamsT} (e : LExpr T) (f : T.base.Metadata → NewMetadata) : LExpr ⟨⟨NewMetadata, T.base.IDMeta⟩, T.TypeType⟩ :=
  match e with
  | .const m c =>
    .const (f m) c
  | .op m o uty =>
    .op (f m) o uty
  | .bvar m b =>
    .bvar (f m) b
  | .fvar m x uty =>
    .fvar (f m) x uty
  | .app m e1 e2 =>
    let e1 := replaceMetadata e1 f
    let e2 := replaceMetadata e2 f
    .app (f m) e1 e2
  | .abs m uty e =>
    let e := replaceMetadata e f
    .abs (f m) uty e
  | .quant m qk argTy tr e =>
    let e := replaceMetadata e f
    let tr := replaceMetadata tr f
    .quant (f m) qk argTy tr e
  | .ite m c t f_expr =>
    let c := replaceMetadata c f
    let t := replaceMetadata t f
    let f_expr := replaceMetadata f_expr f
    .ite (f m) c t f_expr
  | .eq m e1 e2 =>
    let e1 := replaceMetadata e1 f
    let e2 := replaceMetadata e2 f
    .eq (f m) e1 e2

-- Replace all metadata by a unit, suitable for comparison
def eraseMetadata {T : LExprParamsT} (e : LExpr T) : LExpr ⟨⟨Unit, T.base.IDMeta⟩, T.TypeType⟩ := LExpr.replaceMetadata e (λ_ =>())

/--
Compute the size of `e` as a tree.

Not optimized for execution efficiency, but can be used for termination
arguments.
-/
def size (T : LExprParamsT) (e : LExpr T) : Nat :=
  match e with
  | .const .. | .op .. | .bvar .. | .fvar .. => 1
  | .abs _ _ e' => 1 + size T e'
  | .quant _ _ _ _ e' => 1 + size T e'
  | .app _ e1 e2 => 1 + size T e1 + size T e2
  | .ite _ c t f => 1 + size T c + size T t + size T f
  | .eq _ e1 e2 => 1 + size T e1 + size T e2

/--
Erase all type annotations from `e` except the bound variables of abstractions
and quantified expressions.
-/
def eraseTypes {T : LExprParamsT} (e : LExpr T) : LExpr T :=
  match e with
  | .const m c => .const m c
  | .op m o _ => .op m o none
  | .fvar m x _ => .fvar m x none
  | .bvar _ _ => e
  | .abs m ty e => .abs m ty (eraseTypes e)
  | .quant m qk _ tr e => .quant m qk .none (eraseTypes tr) (eraseTypes e)
  | .app m e1 e2 => .app m (eraseTypes e1) (eraseTypes e2)
  | .ite m c t f => .ite m (eraseTypes c) (eraseTypes t) (eraseTypes f)
  | .eq m e1 e2 => .eq m (eraseTypes e1) (eraseTypes e2)

---------------------------------------------------------------------

/- Formatting and Parsing of Lambda Expressions -/
instance : ToString LConst where
  toString c :=
    match c with
    | .intConst i => toString i
    | .strConst s => s
    | .realConst r => toString r
    | .bitvecConst _ b => toString (b.toNat)
    | .boolConst b => toString b

instance (T : LExprParamsT) [Repr T.base.IDMeta] [Repr T.TypeType] [Repr T.base.Metadata] : ToString (LExpr T) where
   toString a := toString (repr a)

private def collectAppSpine {T : LExprParamsT} : LExpr T → List (LExpr T)
  | .app _ fn arg => collectAppSpine fn ++ [arg]
  | other => [other]

/-
Theorem: For any application expression e, every element of collectAppSpine e
is strictly smaller than e.

Proof: By obtaining m, fn, arg from hApp, then by induction on fn.

  Base case (fn is not .app):
    1. collectAppSpine e = [fn, arg]
       by definition (subst e = app m fn arg, fn not .app)
    2. ec = fn or ec = arg
    3. sizeOf e = 3 + sizeOf fn + sizeOf arg > sizeOf ec
       by arithmetic

  Inductive case (fn = app m' fn' arg'):
    Assume: ∀ ec ∈ collectAppSpine (app m' fn' arg'),
            ec.sizeOf < (app m' fn' arg').sizeOf  [IH]
    1. collectAppSpine e = collectAppSpine (app m' fn' arg') ++ [arg]
       by definition
    2. Case ec ∈ collectAppSpine (app m' fn' arg'):
       ec.sizeOf < sizeOf fn < sizeOf e by IH and arithmetic
    3. Case ec = arg:
       ec.sizeOf < sizeOf e by arithmetic
-/
private theorem collectAppSpine_lt {T : LExprParamsT} (e : LExpr T) (ec : LExpr T)
    (hec : ec ∈ collectAppSpine e) (hApp : ∃ m fn arg, e = .app m fn arg) :
    ec.sizeOf < e.sizeOf := by
  obtain ⟨m, fn, arg, rfl⟩ := hApp
  induction fn generalizing arg m ec with
  | app m' fn' arg' ih =>
    simp [collectAppSpine] at hec
    cases hec with
    | inl h =>
      have := ih ec m' arg' (by simp [collectAppSpine]; exact Or.inl h)
      simp [LExpr.sizeOf] at this ⊢; omega
    | inr h =>
      rcases h with rfl | rfl <;> simp [LExpr.sizeOf] <;> omega
  | _ =>
    simp [collectAppSpine] at hec
    rcases hec with rfl | rfl <;> simp [LExpr.sizeOf] <;> omega

private def formatLExpr (T : LExprParamsT) [ToFormat T.base.IDMeta] [ToFormat T.TypeType] (e : LExpr T) :
    Format :=
  match _: e with
  | .const _ c => f!"#{c}"
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
  | .app m fn arg =>
    let fmts := (collectAppSpine e).attach.map (fun ⟨ec, hec⟩ =>
      have : sizeOf ec < sizeOf e := collectAppSpine_lt e ec hec ⟨m, fn, arg, by subst_vars; rfl⟩
      formatLExpr T ec)
    Format.paren (Format.group (Format.joinSep fmts Format.line))
  | .ite _ c t el => Format.paren
                      ("if " ++ formatLExpr T c ++
                       " then " ++ formatLExpr T t ++ " else "
                       ++ formatLExpr T el)
  | .eq _ e1 e2 => Format.paren (formatLExpr T e1 ++ " == " ++ formatLExpr T e2)
  termination_by sizeOf e

instance (T : LExprParamsT) [ToFormat T.base.IDMeta] [ToFormat T.TypeType] : ToFormat (LExpr T) where
  format := formatLExpr T

/-
Syntax for conveniently building `LExpr` terms with `LMonoTy`, scoped under the namespace
`LExpr.SyntaxMono`.
-/
namespace SyntaxMono
open Lean Elab Meta

-- Although T is not used in the class, it makes it possible to create instances
-- so that toExpr is meant to be typed
class MkLExprParams (T: LExprParams) where
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

def mkIntLit (n: NumLit) : Expr := Expr.app (.const ``Int.ofNat []) (mkNatLit n.getNat)
def mkNegLit (n: NumLit) := Expr.app (.const ``Int.neg []) (mkIntLit n)

def elabLConstMono [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lconstmono| #$n:num)  => do
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    let intVal := mkIntLit n
    let lconstVal ← mkAppM ``LConst.intConst #[intVal]
    return mkAppN (.const ``LExpr.const []) #[tMono, metadata, lconstVal]
  | `(lconstmono| #-$n:num)  => do
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    let intVal := mkNegLit n
    let lconstVal ← mkAppM ``LConst.intConst #[intVal]
    return mkAppN (.const ``LExpr.const []) #[tMono, metadata, lconstVal]
  | `(lconstmono| #true)    => do
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    let lconstVal ← mkAppM ``LConst.boolConst #[toExpr true]
    return mkAppN (.const ``LExpr.const []) #[tMono, metadata, lconstVal]
  | `(lconstmono| #false)   =>  do
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    let lconstVal ← mkAppM ``LConst.boolConst #[toExpr false]
    return mkAppN (.const ``LExpr.const []) #[tMono, metadata, lconstVal]
  | `(lconstmono| #$s:ident) => do
    let s := toString s.getId
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    let lconstVal ← mkAppM ``LConst.strConst #[mkStrLit s]
    return mkAppN (.const ``LExpr.const []) #[tMono, metadata, lconstVal]
  | _ => throwUnsupportedSyntax

declare_syntax_cat lopmono
scoped syntax "~" noWs lidentmono : lopmono
scoped syntax "(" lopmono ":" lmonoty ")" : lopmono
scoped syntax lopmono : lexprmono

def elabLOpMono [MkLExprParams T] : Lean.Syntax → MetaM Expr
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
def elabLBVarMono [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lbvarmono| %$n:num) => do
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    return mkAppN (.const ``LExpr.bvar []) #[tMono, metadata, mkNatLit n.getNat]
  | _ => throwUnsupportedSyntax
scoped syntax lbvarmono : lexprmono

declare_syntax_cat lfvarmono
scoped syntax lidentmono : lfvarmono
scoped syntax "(" lidentmono ":" lmonoty ")" : lfvarmono

def elabLFVarMono [MkLExprParams T] : Lean.Syntax → MetaM Expr
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
partial def elabLExprMono [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lexprmono| $c:lconstmono) => elabLConstMono (T:=T) c
  | `(lexprmono| $o:lopmono) => elabLOpMono (T:=T) o
  | `(lexprmono| $b:lbvarmono) => elabLBVarMono (T:=T) b
  | `(lexprmono| $f:lfvarmono) => elabLFVarMono (T:=T) f
  | `(lexprmono| λ $e:lexprmono) => do
     let e' ← elabLExprMono (T:=T) e
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     return mkAppN (.const ``LExpr.absUntyped []) #[tMono, metadata, e']
  | `(lexprmono| λ ($mty:lmonoty): $e:lexprmono) => do
     let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy mty
     let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
     let e' ← elabLExprMono (T:=T) e
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     return mkAppN (.const ``LExpr.abs []) #[tMono, metadata, lmonoty, e']
  | `(lexprmono| ∀ $e:lexprmono) => do
     let e' ← elabLExprMono (T:=T) e
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     return mkAppN (.const ``LExpr.allUntyped []) #[tMono, metadata, e']
  | `(lexprmono| ∀ {$tr}$e:lexprmono) => do
     let e' ← elabLExprMono (T:=T) e
     let tr' ← elabLExprMono (T:=T) tr
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     return mkAppN (.const ``LExpr.allUntypedTr []) #[tMono, metadata, tr', e']
  | `(lexprmono| ∀ ($mty:lmonoty): $e:lexprmono) => do
     let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy mty
     let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
     let e' ← elabLExprMono (T:=T) e
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     return mkAppN (.const ``LExpr.all []) #[tMono, metadata, lmonoty, e']
  | `(lexprmono| ∀ ($mty:lmonoty):{$tr} $e:lexprmono) => do
     let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy mty
     let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
     let e' ← elabLExprMono (T:=T) e
     let tr' ← elabLExprMono (T:=T) tr
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     return mkAppN (.const ``LExpr.allTr []) #[tMono, metadata, lmonoty, tr', e']
  | `(lexprmono| ∃ ($mty:lmonoty): $e:lexprmono) => do
     let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy mty
     let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
     let e' ← elabLExprMono (T:=T) e
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     return mkAppN (.const ``LExpr.exist []) #[tMono, metadata, lmonoty, e']
  | `(lexprmono| ∃ ($mty:lmonoty):{$tr} $e:lexprmono) => do
     let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy mty
     let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
     let e' ← elabLExprMono (T:=T) e
     let tr' ← elabLExprMono (T:=T) tr
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     return mkAppN (.const ``LExpr.existTr []) #[tMono, metadata, lmonoty, tr', e']
  | `(lexprmono| ∃ $e:lexprmono) => do
     let e' ← elabLExprMono (T:=T) e
     let metadata ← mkAppM ``Unit.unit #[]
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     return mkAppN (.const ``LExpr.existUntyped []) #[tMono, metadata, e']
  | `(lexprmono| ∃{$tr} $e:lexprmono) => do
     let e' ← elabLExprMono (T:=T) e
     let tr' ← elabLExprMono (T:=T) tr
     let metadata ← mkAppM ``Unit.unit #[]
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     return mkAppN (.const ``LExpr.existUntypedTr []) #[tMono, metadata, tr', e']
  | `(lexprmono| ($e1:lexprmono $e2:lexprmono)) => do
     let e1' ← elabLExprMono (T:=T) e1
     let e2' ← elabLExprMono (T:=T) e2
     let metadata ← mkAppM ``Unit.unit #[]
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     return mkAppN (.const ``LExpr.app []) #[tMono, metadata, e1', e2']
  | `(lexprmono| $e1:lexprmono == $e2:lexprmono) => do
     let e1' ← elabLExprMono (T:=T) e1
     let e2' ← elabLExprMono (T:=T) e2
     let metadata ← mkAppM ``Unit.unit #[]
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     return mkAppN (.const ``LExpr.eq []) #[tMono, metadata, e1', e2']
  | `(lexprmono| if $e1:lexprmono then $e2:lexprmono else $e3:lexprmono) => do
     let e1' ← elabLExprMono (T:=T) e1
     let e2' ← elabLExprMono (T:=T) e2
     let e3' ← elabLExprMono (T:=T) e3
     let metadata ← mkAppM ``Unit.unit #[]
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     return mkAppN (.const ``LExpr.ite []) #[tMono, metadata, e1', e2', e3']
  | `(lexprmono| ($e:lexprmono)) => elabLExprMono (T:=T) e
  | _ => throwUnsupportedSyntax

scoped syntax ident : lidentmono
/-- Elaborator for String identifiers, construct a String instance -/
def elabStrIdent : Lean.Syntax → MetaM Expr
  | `(lidentmono| $s:ident) => do
    let s := s.getId
    return mkAppN (.const `Lambda.Identifier.mk []) #[.const ``Unit [], mkStrLit s.toString, .const ``Unit.unit []]
  | _ => throwUnsupportedSyntax

-- Unit metadata, Unit IDMeta
instance : MkLExprParams ⟨Unit, Unit⟩ where
  elabIdent := elabStrIdent
  toExpr := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (mkConst ``Unit)

elab "esM[" e:lexprmono "]" : term => elabLExprMono (T:=⟨Unit, Unit⟩) e

-- Syntax tests moved to StrataTest/DL/Lambda/LExprSyntaxTests.lean

end SyntaxMono



/-
Syntax for conveniently building `LExpr` terms with `LTy`, scoped under the namespace
`LExpr.Syntax`.
-/
namespace Syntax
open Lean Elab Meta

-- Although T is not used in the class, it makes it possible to create instances
-- so that toExpr is meant to be typed
class MkLExprParams (T: LExprParams) where
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

def mkIntLit (n: NumLit) : Expr := Expr.app (.const ``Int.ofNat []) (mkNatLit n.getNat)
def mkNegLit (n: NumLit) := Expr.app (.const ``Int.neg []) (mkIntLit n)

def elabLConst [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lconst| #$n:num)  => do
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := MkLExprParams.toExpr T
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    let lconstVal ← mkAppM ``LConst.intConst #[mkIntLit n]
    return mkAppN (.const ``LExpr.const []) #[tParams, metadata, lconstVal]
  | `(lconst| #-$n:num) => do
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := MkLExprParams.toExpr T
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    let lconstVal ← mkAppM ``LConst.intConst #[mkNegLit n]
    return mkAppN (.const ``LExpr.const []) #[tParams, metadata, lconstVal]
  | `(lconst| #true)    => do
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := MkLExprParams.toExpr T
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.boolConst []) #[tParams, metadata, toExpr true]
  | `(lconst| #false)   =>  do
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := MkLExprParams.toExpr T
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.boolConst []) #[tParams, metadata, toExpr false]
  | `(lconst| #$s:ident) => do
    let s := toString s.getId
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := MkLExprParams.toExpr T
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.const []) #[tParams, metadata, mkStrLit s]
  | _ => throwUnsupportedSyntax

declare_syntax_cat lop
scoped syntax "~" noWs lident : lop
scoped syntax "(" lop ":" lty ")" : lop
scoped syntax lop : lexpr

def elabLOp [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lop| ~$s:lident)  => do
    let none ← mkNone (mkConst ``LTy)
    let ident ← MkLExprParams.elabIdent T s
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := MkLExprParams.toExpr T
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.op []) #[tParams, metadata, ident, none]
  | `(lop| (~$s:lident : $ty:lty)) => do
    let lty ← Lambda.LTy.Syntax.elabLTy ty
    let lty ← mkSome (mkConst ``LTy) lty
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := MkLExprParams.toExpr T
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.op []) #[tParams, metadata, ← MkLExprParams.elabIdent T s, lty]
  | _ => throwUnsupportedSyntax

declare_syntax_cat lbvar
scoped syntax "%" noWs num : lbvar

def elabLBVar [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lbvar| %$n:num) => do
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := MkLExprParams.toExpr T
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.bvar []) #[tParams, metadata, mkNatLit n.getNat]
  | _ => throwUnsupportedSyntax
scoped syntax lbvar : lexpr

declare_syntax_cat lfvar
scoped syntax lident : lfvar
scoped syntax "(" lident ":" lty ")" : lfvar

def elabLFVar [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lfvar| $i:lident) => do
    let none ← mkNone (mkConst ``LTy)
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := MkLExprParams.toExpr T
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.fvar []) #[tParams, metadata, ← MkLExprParams.elabIdent T i, none]
  | `(lfvar| ($i:lident : $ty:lty)) => do
    let lty ← Lambda.LTy.Syntax.elabLTy ty
    let lty ← mkSome (mkConst ``LTy) lty
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := MkLExprParams.toExpr T
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.fvar []) #[tParams, metadata, ← MkLExprParams.elabIdent T i, lty]
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
partial def elabLExpr [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lexpr| $c:lconst) => elabLConst (T:=T) c
  | `(lexpr| $o:lop) => elabLOp (T:=T) o
  | `(lexpr| $b:lbvar) => elabLBVar (T:=T) b
  | `(lexpr| $f:lfvar) => elabLFVar (T:=T) f
  | `(lexpr| λ $e:lexpr) => do
     let e' ← elabLExpr (T:=T) e
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.absUntyped []) #[tParams, metadata, e']
  | `(lexpr| λ ($mty:lty): $e:lexpr) => do
     let lty ← Lambda.LTy.Syntax.elabLTy mty
     let lty ← mkSome (mkConst ``LTy) lty
     let e' ← elabLExpr (T:=T) e
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.abs []) #[tParams, metadata, lty, e']
  | `(lexpr| ∀ $e:lexpr) => do
     let e' ← elabLExpr (T:=T) e
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.allUntyped []) #[tParams, metadata, e']
  | `(lexpr| ∀{$tr}$e:lexpr) => do
     let e' ← elabLExpr (T:=T) e
     let tr' ← elabLExpr (T:=T) tr
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.allUntypedTr []) #[tParams, metadata, tr', e']
  | `(lexpr| ∀ ($mty:lty): $e:lexpr) => do
     let lty ← Lambda.LTy.Syntax.elabLTy mty
     let lty ← mkSome (mkConst ``LTy) lty
     let e' ← elabLExpr (T:=T) e
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.all []) #[tParams, metadata, lty, e']
  | `(lexpr| ∀ ($mty:lty): {$tr}$e:lexpr) => do
     let lty ← Lambda.LTy.Syntax.elabLTy mty
     let lty ← mkSome (mkConst ``LTy) lty
     let e' ← elabLExpr (T:=T) e
     let tr' ← elabLExpr (T:=T) tr
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.allTr []) #[tParams, metadata, lty, tr', e']
  | `(lexpr| ∃ ($mty:lty): $e:lexpr) => do
     let lty ← Lambda.LTy.Syntax.elabLTy mty
     let lty ← mkSome (mkConst ``LTy) lty
     let e' ← elabLExpr (T:=T) e
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.exist []) #[tParams, metadata, lty, e']
  | `(lexpr| ∃ ($mty:lty): {$tr}$e:lexpr) => do
     let lty ← Lambda.LTy.Syntax.elabLTy mty
     let lty ← mkSome (mkConst ``LTy) lty
     let e' ← elabLExpr (T:=T) e
     let tr' ← elabLExpr (T:=T) tr
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.existTr []) #[tParams, metadata, lty, tr', e']
  | `(lexpr| ∃ $e:lexpr) => do
     let e' ← elabLExpr (T:=T) e
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.existUntyped []) #[tParams, metadata, e']
  | `(lexpr| ∃ {$tr} $e:lexpr) => do
     let e' ← elabLExpr (T:=T) e
     let tr' ← elabLExpr (T:=T) tr
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.existUntypedTr []) #[tParams, metadata, tr', e']
  | `(lexpr| ($e1:lexpr $e2:lexpr)) => do
     let e1' ← elabLExpr (T:=T) e1
     let e2' ← elabLExpr (T:=T) e2
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.app []) #[tParams, metadata, e1', e2']
  | `(lexpr| $e1:lexpr == $e2:lexpr) => do
     let e1' ← elabLExpr (T:=T) e1
     let e2' ← elabLExpr (T:=T) e2
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.eq []) #[tParams, metadata, e1', e2']
  | `(lexpr| if $e1:lexpr then $e2:lexpr else $e3:lexpr) => do
     let e1' ← elabLExpr (T:=T) e1
     let e2' ← elabLExpr (T:=T) e2
     let e3' ← elabLExpr (T:=T) e3
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.ite []) #[tParams, metadata, e1', e2', e3']
  | `(lexpr| ($e:lexpr)) => elabLExpr (T:=T) e
  | _ => throwUnsupportedSyntax

scoped syntax ident : lident
/-- Elaborator for String identifiers, construct a String instance -/
def elabStrIdent : Lean.Syntax → MetaM Expr
  | `(lident| $s:ident) => do
    let s := s.getId
    return mkAppN (.const `Lambda.Identifier.mk []) #[.const ``Unit [], mkStrLit s.toString, .const ``Unit.unit []]
  | _ => throwUnsupportedSyntax

instance : MkLExprParams ⟨Unit, Unit⟩ where
  elabIdent := elabStrIdent
  toExpr := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (mkConst ``Unit)

elab "es[" e:lexpr "]" : term => elabLExpr (T:=⟨Unit, Unit⟩) e

-- Syntax tests moved to StrataTest/DL/Lambda/LExprSyntaxTests.lean

end Syntax

---------------------------------------------------------------------

end LExpr
end Lambda
