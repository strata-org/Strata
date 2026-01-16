/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LExprTypeSpec
import Strata.DL.Lambda.LExprTypeEnv
import Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LExprT
import Strata.DL.Lambda.LExprEval
import Strata.DL.Lambda.IntBoolFactory
import Plausible.Sampleable
import Plausible.DeriveArbitrary
import Plausible.Attr
import Strata.DL.Lambda.PlausibleHelpers
import Strata.Util.Random

-- -- Add these if depending on Chamelean for instance generation.
-- import Plausible.Chamelean.ArbitrarySizedSuchThat
-- import Plausible.Chamelean.DecOpt
-- import Plausible.Chamelean.DeriveConstrainedProducer
-- import Plausible.Chamelean.DeriveChecker

/-! ## Generators for Well-Typed Lambda expressions -/

-- Most of the instance definitions for `ArbitrarySizedSuchThat α P` could be replaced by a call to
-- `deriving_generator (fun ... => ∃ a : α, P)`, or `deriving_checker ...` if we had a dependency on https://github.com/codyroux/plausible
-- We avoid this for now, and simply inline the instance declaration.
-- We leave the relevant calls as comments, in case they need to be re-generated after a change.

open Plausible

deriving instance Arbitrary for Lambda.Identifier
deriving instance Arbitrary for Lambda.Info
deriving instance Arbitrary for Lambda.QuantifierKind

instance instArbitraryRat : Arbitrary Rat where
  arbitrary := do
  let den ← Gen.chooseNat
  let num : Int ← Arbitrary.arbitrary
  return num / den

deriving instance Arbitrary for Lambda.LConst

-- This doesn't work because of bundled arguments
-- deriving instance Arbitrary for Lambda.LExpr

def instArbitraryLExpr.arbitrary {T}
  [Arbitrary T.base.Metadata] [Arbitrary T.base.IDMeta] [Arbitrary T.TypeType]
  : Nat → Plausible.Gen (@Lambda.LExpr T) :=
  let rec aux_arb (fuel : Nat) : Plausible.Gen (@Lambda.LExpr T) :=
    (match fuel with
    | Nat.zero =>
      Plausible.Gen.oneOfWithDefault
        (do
          let a ← Plausible.Arbitrary.arbitrary
          let a_1 ← Plausible.Arbitrary.arbitrary
          return Lambda.LExpr.const a a_1)
        [(do
            let a ← Plausible.Arbitrary.arbitrary
            let a_1 ← Plausible.Arbitrary.arbitrary
            return Lambda.LExpr.const a a_1),
          (do
            let a_2 ← Plausible.Arbitrary.arbitrary
            let a_3 ← Plausible.Arbitrary.arbitrary
            let a_4 ← Plausible.Arbitrary.arbitrary
            return Lambda.LExpr.op a_2 a_3 a_4),
          (do
            let a_5 ← Plausible.Arbitrary.arbitrary
            let a_6 ← Plausible.Arbitrary.arbitrary
            return Lambda.LExpr.bvar a_5 a_6),
          (do
            let a_7 ← Plausible.Arbitrary.arbitrary
            let a_8 ← Plausible.Arbitrary.arbitrary
            -- let a_9 ← Plausible.Arbitrary.arbitrary
            return Lambda.LExpr.fvar a_7 a_8 none)] -- We don't annotate variables, those types will appear in context.
    | fuel' + 1 =>
      Plausible.Gen.frequency
        (do
          let a ← Plausible.Arbitrary.arbitrary
          let a_1 ← Plausible.Arbitrary.arbitrary
          return Lambda.LExpr.const a a_1)
        [(1,
            (do
              let a ← Plausible.Arbitrary.arbitrary
              let a_1 ← Plausible.Arbitrary.arbitrary
              return Lambda.LExpr.const a a_1)),
          (1,
            (do
              let a_2 ← Plausible.Arbitrary.arbitrary
              let a_3 ← Plausible.Arbitrary.arbitrary
              let a_4 ← Plausible.Arbitrary.arbitrary
              return Lambda.LExpr.op a_2 a_3 a_4)),
          (1,
            (do
              let a_5 ← Plausible.Arbitrary.arbitrary
              let a_6 ← Plausible.Arbitrary.arbitrary
              return Lambda.LExpr.bvar a_5 a_6)),
          (1,
            (do
              let a_7 ← Plausible.Arbitrary.arbitrary
              let a_8 ← Plausible.Arbitrary.arbitrary
              let a_9 ← Plausible.Arbitrary.arbitrary
              return Lambda.LExpr.fvar a_7 a_8 a_9)),
          (fuel' + 1,
            (do
              let a_10 ← Plausible.Arbitrary.arbitrary
              let a_11 ← Plausible.Arbitrary.arbitrary
              let a_12 ← aux_arb fuel'
              return Lambda.LExpr.abs a_10 a_11 a_12)),
          (fuel' + 1,
            (do
              let a_13 ← Plausible.Arbitrary.arbitrary
              let a_14 ← Plausible.Arbitrary.arbitrary
              let a_15 ← Plausible.Arbitrary.arbitrary
              let a_16 ← aux_arb fuel'
              let a_17 ← aux_arb fuel'
              return Lambda.LExpr.quant a_13 a_14 a_15 a_16 a_17)),
          (fuel' + 1,
            (do
              let a_18 ← Plausible.Arbitrary.arbitrary
              let a_19 ← aux_arb fuel'
              let a_20 ← aux_arb fuel'
              return Lambda.LExpr.app a_18 a_19 a_20)),
          (fuel' + 1,
            (do
              let a_21 ← Plausible.Arbitrary.arbitrary
              let a_22 ← aux_arb fuel'
              let a_23 ← aux_arb fuel'
              let a_24 ← aux_arb fuel'
              return Lambda.LExpr.ite a_21 a_22 a_23 a_24)),
          (fuel' + 1,
            (do
              let a_25 ← Plausible.Arbitrary.arbitrary
              let a_26 ← aux_arb fuel'
              let a_27 ← aux_arb fuel'
              return Lambda.LExpr.eq a_25 a_26 a_27))])
  fun fuel => aux_arb fuel

instance {T} [Arbitrary T.base.Metadata] [Arbitrary T.base.IDMeta] [Arbitrary T.TypeType] : Plausible.ArbitraryFueled (@Lambda.LExpr T) := ⟨instArbitraryLExpr.arbitrary⟩

-- -- Prints a few examples of random expressions.
-- #eval Gen.printSamples (Arbitrary.arbitrary : Gen <| Lambda.LExpr ⟨⟨String, String⟩, String⟩)

open Lambda
open LTy

-- Comment this out when depending on Chamelean
open TestGen

-- We make a bunch of functions inductive predicates to play nice with Chamelean.
inductive MapFind : Map α β → α → β → Prop where
| hd : MapFind ((x, y) :: m) x y
| tl : p.fst ≠ x → MapFind m x y → MapFind (p :: m) x y

inductive MapNotFound : Map α β → α → Prop where
| nil : MapNotFound [] x
| cons : z ≠ x → MapNotFound m x → MapNotFound ((z, w) :: m) x

inductive MapsFind : Maps α β → α → β → Prop where
| hd : MapFind m x y → MapsFind (m :: ms) x y
| tl : MapNotFound m x → MapsFind ms x y → MapsFind (m :: ms) x y

-- Sadly, we need these versions as well for the time being, because
-- we can only generate one output at a time for a given inductive constraint.
-- Here we want to produce both the key and the value at once.
inductive MapFind₂ {α β : Type} : Map α β → α × β → Prop where
| hd : MapFind₂ ((x, y) :: m) (x, y)
| tl : MapFind₂ m q → MapFind₂ (p :: m) q

inductive MapsFind₂ : Maps α β → α × β → Prop where
| hd : MapFind₂ m (x, y) → MapsFind₂ (m :: ms) (x, y)
| tl : MapsFind₂ ms (x, y) → MapsFind₂ (m :: ms) (x, y)

inductive MapReplace : Map α β → α → β → Map α β → Prop where
| nil : MapReplace [] x y []
| consFound : MapReplace ((x, z)::m) x y ((x, y)::m)
| consNotFound : x ≠ z → MapReplace m x y m' → MapReplace ((z, w) :: m) x y ((z, w) :: m')

inductive MapsReplace : Maps α β → α → β → Maps α β → Prop where
| nil : MapsReplace [] x y []
-- We do redundant work here but it's ok
| cons : MapReplace m x y m' → MapsReplace ms x y ms' → MapsReplace (m::ms) x y (m'::ms')

inductive MapsNotFound : Maps α β → α → Prop where
| nil : MapsNotFound [] x
| cons : MapNotFound m x → MapsNotFound ms x → MapsNotFound (m::ms) x

-- We tediously do what the functional implementation does but allowing shadowing would probably be ok
inductive MapsInsert : Maps α β → α → β → Maps α β → Prop where
| found : MapsFind ms x z → MapsReplace ms x y ms' → MapsInsert ms x y ms'
| notFound : MapsNotFound (m::ms) x → MapsInsert (m::ms) x y (((x,y)::m)::ms)
| empty : MapsInsert [] x y [[(x, y)]]

-- -- We hand write this to avoid guessing and checking for strings.
instance instStringSuchThatIsInt : ArbitrarySizedSuchThat String (fun s => s.isInt) where
  arbitrarySizedST _ := toString <$> (Arbitrary.arbitrary : Gen Int)

#guard_msgs(drop info) in
#eval
  let P : String → Prop := fun s => s.isInt
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

def ArrayFind (a : Array α) (x : α)  := x ∈ a

instance instArrayFindSuchThat {α} {a} : ArbitrarySizedSuchThat α (fun x => ArrayFind a x) where
  arbitrarySizedST _ := do
  if h:a.size = 0 then throw <| GenError.genError "Gen: cannot generate elements of empty array" else
  let i ← Gen.chooseNatLt 0 a.size (by omega)
  return a[i.val]


inductive IsUnaryArg : LTy → LTy → LTy → Prop where
| mk (ty₁ ty₂ : LMonoTy) : IsUnaryArg (.forAll [] (.tcons "arrow" [ty₁, ty₂])) (.forAll [] ty₁) (.forAll [] ty₂)

inductive IsBinaryArg : LTy → (LTy × LTy) → LTy → Prop where
| mk (ty₁ ty₂ ty₃ : LMonoTy) : IsBinaryArg (.forAll [] (.tcons "arrow" [ty₁, .tcons "arrow" [ty₂, ty₃]])) ((.forAll [] ty₁), (.forAll [] ty₂)) (.forAll [] ty₃)

-- Compare `LExpr.HasType` in `LExprTypeSpec.lean`

-- Parameters for terms without metadata
abbrev TrivialParams : LExprParams := ⟨Unit, Unit⟩

def varClose (k : Nat) (x : IdentT LMonoTy TrivialParams.IDMeta) (e : LExpr TrivialParams.mono) : LExpr TrivialParams.mono :=
  match e with
  | .const m c => .const m c
  | .op m o ty => .op m o ty
  | .bvar m i => .bvar m i
  | .fvar m y yty => if x.fst == y && (yty == x.snd) then
                      (.bvar m k) else (.fvar m y yty)
  | .abs m ty e' => .abs m ty (varClose (k + 1) x e')
  | .quant m qk ty tr' e' => .quant m qk ty (varClose (k + 1) x tr') (varClose (k + 1) x e')
  | .app m e1 e2 => .app m (varClose k x e1) (varClose k x e2)
  | .ite m c t e => .ite m (varClose k x c) (varClose k x t) (varClose k x e)
  | .eq m e1 e2 => .eq m (varClose k x e1) (varClose k x e2)

def LFunc.type! (f : (LFunc T)) : LTy :=
  let input_tys := f.inputs.values
  let output_tys := Lambda.LMonoTy.destructArrow f.output
  match input_tys with
  | [] => .forAll f.typeArgs f.output
  | ity :: irest =>
    .forAll f.typeArgs (Lambda.LMonoTy.mkArrow ity (irest ++ output_tys))

-- We massage the `HasType` definition to be more amenable to generation. The main differences are that
-- polymorphism is not supported, and we tend to move function applications in the "output" position to the conclusion.
-- This avoids an additional costly check in the hypothesis.
inductive HasType {T: LExprParams} [DecidableEq T.IDMeta] (C : LContext T) : (TContext T.IDMeta) → LExpr T.mono → LTy → Prop where
  | tbool_const : ∀ Γ m b,
            C.knownTypes.containsName "bool" →
            HasType C Γ (.boolConst m b) (.forAll [] .bool)
  | tint_const : ∀ Γ m n,
            C.knownTypes.containsName "int" →
            HasType C Γ (.intConst m n) (.forAll [] .int)
  | treal_const : ∀ Γ m r,
            C.knownTypes.containsName "real" →
            HasType C Γ (.realConst m r) (.forAll [] .real)
  | tstr_const : ∀ Γ m s,
            C.knownTypes.containsName "string" →
            HasType C Γ (.strConst m s) (.forAll [] .string)
  | tbitvec_const : ∀ Γ m n b,
            C.knownTypes.containsName "bitvec" →
            HasType C Γ (.bitvecConst m n b) (.forAll [] (.bitvec n))

  | tvar : ∀ Γ m x ty, MapsFind Γ.types x ty → HasType C Γ (.fvar m x none) ty

  | tabs : ∀ Γ Γ' m x x_ty e e_ty,
            MapsInsert Γ.types (id x) (.forAll [] x_ty : LTy) Γ' →
            HasType C { Γ with types := Γ'} e (.forAll [] e_ty) →
            HasType C Γ (.abs m .none <| LExpr.varClose 0 (x, none) e) -- We close in the conclusion rather than opening in the hyps.
                        (.forAll [] (.tcons "arrow" [x_ty, e_ty]))

  | tapp : ∀ Γ m e1 e2 t1 t2,
            HasType C Γ e1 (.forAll [] (.tcons "arrow" [t2, t1])) →
            HasType C Γ e2 (.forAll [] t2) →
            HasType C Γ (.app m e1 e2) (.forAll [] t1)

  | tif : ∀ Γ m c e1 e2 ty,
          HasType C Γ c (.forAll [] .bool) →
          HasType C Γ e1 ty →
          HasType C Γ e2 ty →
          HasType C Γ (.ite m c e1 e2) ty

  | teq : ∀ Γ m e1 e2 ty,
          HasType C Γ e1 ty →
          HasType C Γ e2 ty →
          HasType C Γ (.eq m e1 e2) (.forAll [] .bool)

  | top: ∀ Γ m f ty,
            ty = (LFunc.type! f) →
            ArrayFind C.functions f →
            HasType C Γ (.op m f.name none) ty

  | top₁: ∀ Γ m f ty₁ ty₂,
            ArrayFind C.functions f →
            IsUnaryArg (LFunc.type! f) ty₁ ty₂ →
            HasType C Γ t₁ ty₁ →
            HasType C Γ (.app m (.op m f.name none) t₁) ty₂

  | top₂: ∀ Γ m f ty₁ ty₂ ty₃,
            ArrayFind C.functions f →
            IsBinaryArg (LFunc.type! f) (ty₁, ty₂) ty₃ →
            HasType C Γ t₁ ty₁ →
            HasType C Γ t₂ ty₂ →
            HasType C Γ (.app m (.app m (.op m f.name none) t₁) t₂) ty₃

  -- -- We only generate monomorphic types for now

-- -- We hand write this instance to control the base type names.
instance : Arbitrary LMonoTy where
  arbitrary :=
    let rec aux (n : Nat) : Gen LMonoTy :=
    match n with
    | 0 => Gen.oneOf #[return .tcons "int" [], return .tcons "bool" []]
    | n'+1 => do
    let choice ← Gen.chooseNatLt 0 3 (by simp)
    if ↑choice = 0 then
      Gen.oneOf #[return .tcons "int" [], return .tcons "bool" []]
    else if ↑choice = 1 then
        let ty1 ← aux n'
        let ty2 ← aux n'
        return .tcons "arrow" [ty1, ty2]
    else
      let n ← Gen.oneOf #[return 1, return 8, return 16, return 32, return 64]
      return .bitvec n
  do
    let ⟨size⟩ ← read
    aux size

instance : Arbitrary LTy where
  arbitrary := LTy.forAll [] <$> Arbitrary.arbitrary

-- #eval Gen.printSamples (Arbitrary.arbitrary : Gen LMonoTy)

-- -- This works
-- derive_generator fun α β m y => ∃ x, @MapFind α β m x y

instance {α β m_1 y_1_1} [BEq β] : ArbitrarySizedSuchThat α (fun x_1_1 => @MapFind α β m_1 x_1_1 y_1_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (α_1 : Type) (β_1 : Type) (m_1 : Map α β) (y_1_1 : β) :
      Plausible.Gen α :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match m_1 with
              | List.cons (Prod.mk x y) _m =>
                match DecOpt.decOpt (BEq.beq y y_1_1) initSize with
                | Except.ok Bool.true => return x
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1,
              match m_1 with
              | List.cons (Prod.mk x y) _m =>
                match DecOpt.decOpt (BEq.beq y y_1_1) initSize with
                | Except.ok Bool.true => return x
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (Nat.succ size',
              match m_1 with
              | List.cons _p m => do
                let (x_1_1 : α) ← aux_arb initSize size α_1 β_1 m y_1_1
                return x_1_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)])
    fun size => aux_arb size size α β m_1 y_1_1

/-- info: 2 -/
#guard_msgs(info) in
#eval
  let P : Nat → Prop := fun n : Nat => MapFind [((2 : Nat), "foo")] n "foo"
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

-- -- This works
-- derive_generator fun α β tys y => ∃ x, @MapsFind α β tys x y

instance [DecidableEq β] : ArbitrarySizedSuchThat α (fun x_1 => @MapsFind α β tys_1 x_1 y_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (α : Type) (β : Type) [DecidableEq β] (tys_1 : Maps α β) (y_1 : β) :
      Plausible.Gen α :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match tys_1 with
              | List.cons m _ms => do
                let (x_1 : α) ← ArbitrarySizedSuchThat.arbitrarySizedST (fun (x_1 : α) => @MapFind α β m x_1 y_1) initSize;
                return x_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1,
              match tys_1 with
              | List.cons m _ms => do
                let (x_1 : α) ← ArbitrarySizedSuchThat.arbitrarySizedST (fun (x_1 : α) => MapFind m x_1 y_1) initSize;
                return x_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (Nat.succ size',
              match tys_1 with
              | List.cons _m ms => do
                let (x_1 : α) ← aux_arb initSize size α β ms y_1 -- Chamelean doesn't do the right thing here: it should call itself recursively!
                return x_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)])
    fun size => aux_arb size size α β tys_1 y_1

/-- info: 2 -/
#guard_msgs(info) in
#eval
  let P : Nat → Prop := fun n : Nat => MapsFind [[((2 : Nat), "foo")]] n "foo"
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

-- -- This works
-- derive_generator fun α β m x_1 => ∃ y_1, @MapFind α β m x_1 y_1
instance [DecidableEq α] : ArbitrarySizedSuchThat β (fun y_1_1 => @MapFind α β m_1 x_1_1 y_1_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (α : Type) (β : Type) [DecidableEq α] (m_1 : Map α β) (x_1_1 : α) :
      Plausible.Gen β :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match m_1 with
              | List.cons (Prod.mk x y) _m =>
                match DecOpt.decOpt (BEq.beq x x_1_1) initSize with
                | Except.ok Bool.true => return y
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1,
              match m_1 with
              | List.cons (Prod.mk x y) _m =>
                match DecOpt.decOpt (BEq.beq x x_1_1) initSize with
                | Except.ok Bool.true => return y
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (Nat.succ size',
              match m_1 with
              | List.cons _p m => do
                let (y_1_1 : β) ← aux_arb initSize size' α β m x_1_1
                return y_1_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)])
    fun size => aux_arb size size α β m_1 x_1_1

/-- info: "foo" -/
#guard_msgs(info) in
#eval
  let P : String → Prop := fun s : String => MapFind [((2 : Nat), "foo")] 2 s
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

/-- Creates a fresh identifier from a list -/
def getFreshIdent (pre : String) (l : List TyIdentifier) : TyIdentifier :=
if pre ∉ l then pre else
getFreshIdentSuffix l.length l
where
  getFreshIdentSuffix n l :=
  match n with
  | 0 => pre ++ "0"
  | n'+1 =>
    let ty := pre ++ (toString (l.length - n))
    if ty ∉ l then ty
    else getFreshIdentSuffix n' l

-- -- We hand write this as well. We might be able to derive a reasonable version if we had an inductive relation, by guessing and checking.
instance instArbitrarySizedSuchThatFresh {T : LExprParams} [DecidableEq T.IDMeta] {ctx : TContext T.IDMeta}
  : ArbitrarySizedSuchThat TyIdentifier
  (fun a => TContext.isFresh a ctx) where
  arbitrarySizedST _ := do
    let allTypes := ctx.types.flatten.map Prod.snd
    let allTyVars := allTypes.map LTy.freeVars |>.flatten
    let pre ← Arbitrary.arbitrary
    return getFreshIdent pre allTyVars

#guard_msgs(drop info) in
#eval
  let ty := .forAll [] (LMonoTy.bool)
  let ctx : TContext TrivialParams.IDMeta := ⟨[[(⟨"foo", ()⟩, ty)]], []⟩
  let P : TyIdentifier → Prop := fun s : String => TContext.isFresh s ctx
  Gen.runUntil .none (@ArbitrarySizedSuchThat.arbitrarySizedST _ P (@instArbitrarySizedSuchThatFresh _ _ ctx) 10) 10

-- -- This works
-- derive_checker fun α β m x => @MapNotFound α β m x
instance [DecidableEq α_1] : DecOpt (@MapNotFound α_1 β_1 m_1 x_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (α : Type) (β : Type) [DecidableEq α] (m_1 : Map α β) (x_1 : α) :
      Except Plausible.GenError Bool :=
      (match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun (_ : Unit) =>
            match m_1 with
            | List.nil => Except.ok Bool.true
            | _ => Except.ok Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun (_ : Unit) =>
            match m_1 with
            | List.nil => Except.ok Bool.true
            | _ => Except.ok Bool.false,
            fun (_ : Unit) =>
            match m_1 with
            | List.cons (Prod.mk z _w) m =>
              DecOpt.andOptList [aux_dec initSize size' α β m x_1, DecOpt.decOpt (Ne x_1 z) initSize]
            | _ => Except.ok Bool.false])
    fun size => aux_dec size size α_1 β_1 m_1 x_1

/-- info: false -/
#guard_msgs(info) in
#eval DecOpt.decOpt (MapNotFound [("foo", 4)] "foo") 5
/-- info: true -/
#guard_msgs(info) in
#eval DecOpt.decOpt (MapNotFound [("foo", 4)] "bar") 5

-- -- This works
-- derive_generator fun α β m x_1_1 ty_1_1 => ∃ m', @MapReplace α β m x_1_1 ty_1_1 m'
instance [DecidableEq α] : ArbitrarySizedSuchThat (Map α β) (fun m'_1 => @MapReplace α β m_1 x_1_1_1 ty_1_1_1 m'_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (α : Type) (β : Type) [DecidableEq α] (m_1 : Map α β) (x_1_1_1 : α)
      (ty_1_1_1 : β) : Plausible.Gen (Map α β) :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match m_1 with
              | List.nil => return List.nil
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match m_1 with
              | List.cons (Prod.mk x _z) m =>
                match DecOpt.decOpt (BEq.beq x x_1_1_1) initSize with
                | Except.ok Bool.true => return List.cons (Prod.mk x_1_1_1 ty_1_1_1) m
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1,
              match m_1 with
              | List.nil => return List.nil
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match m_1 with
              | List.cons (Prod.mk x _z) m =>
                match DecOpt.decOpt (BEq.beq x x_1_1_1) initSize with
                | Except.ok Bool.true => return List.cons (Prod.mk x_1_1_1 ty_1_1_1) m
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (Nat.succ size',
              match m_1 with
              | List.cons (Prod.mk z w) m =>
                match DecOpt.decOpt (Ne x_1_1_1 z) initSize with
                | Except.ok Bool.true => do
                  let (m' : Map α β) ← aux_arb initSize size' α β m x_1_1_1 ty_1_1_1
                  return List.cons (Prod.mk z w) m'
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)])
    fun size => aux_arb size size α β m_1 x_1_1_1 ty_1_1_1

/-- info: [(2, "new")] -/
#guard_msgs(info) in
#eval
  let P : Map Nat String → Prop := fun m' => MapReplace [((2 : Nat), "old")] 2 "new" m'
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

-- -- This works
-- derive_checker fun α β m x => @MapsNotFound α β m x

instance [DecidableEq α_1] : DecOpt (@MapsNotFound α_1 β_1 m_1 x_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (α : Type) (β : Type) [DecidableEq α] (m_1 : Maps α β) (x_1 : α) :
      Except Plausible.GenError Bool :=
      (match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun (_ : Unit) =>
            match m_1 with
            | List.nil => Except.ok Bool.true
            | _ => Except.ok Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun (_ : Unit) =>
            match m_1 with
            | List.nil => Except.ok Bool.true
            | _ => Except.ok Bool.false,
            fun (_ : Unit) =>
            match m_1 with
            | List.cons m ms =>
              DecOpt.andOptList [aux_dec initSize size' α β ms x_1, DecOpt.decOpt (MapNotFound m x_1) initSize]
            | _ => Except.ok Bool.false])
    fun size => aux_dec size size α_1 β_1 m_1 x_1

/-- info: false -/
#guard_msgs(info) in
#eval DecOpt.decOpt (MapsNotFound [[("foo", 4)]] "foo") 5
/-- info: true -/
#guard_msgs(info) in
#eval DecOpt.decOpt (MapsNotFound [[("foo", 4)]] "bar") 5

-- -- This works
-- derive_generator fun α β tys_1 x_1 ty_1 => ∃ (Γ_1 : Maps α β), @MapsReplace α β tys_1 x_1 ty_1 Γ_1
instance [DecidableEq α] : ArbitrarySizedSuchThat (Maps α β) (fun Γ_1_1 => @MapsReplace α β tys_1_1 x_1_1 ty_1_1 Γ_1_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (α : Type) (β : Type) [DecidableEq α] (tys_1_1 : Maps α β) (x_1_1 : α)
      (ty_1_1 : β) : Plausible.Gen (Maps α β) :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match tys_1_1 with
              | List.nil => return List.nil
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1,
              match tys_1_1 with
              | List.nil => return List.nil
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (Nat.succ size',
              match tys_1_1 with
              | List.cons m ms => do
                let (m' : Map α β) ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun (m' : Map α β) => @MapReplace α β m x_1_1 ty_1_1 m') initSize;
                do
                  let (ms' : Maps α β) ←
                    aux_arb initSize size α β ms x_1_1 ty_1_1
                  return List.cons m' ms'
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)])
    fun size => aux_arb size size α β tys_1_1 x_1_1 ty_1_1

/-- info: [[(2, "new")]] -/
#guard_msgs(info) in
#eval
  let P : Maps Nat String → Prop := fun m' => MapsReplace [[((2 : Nat), "old")]] 2 "new" m'
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

-- -- This works
-- derive_generator (fun α β tys_1 x_1 => ∃ (z : β), @MapsFind α β tys_1 x_1 z)
instance [DecidableEq α][DecidableEq β] : ArbitrarySizedSuchThat β (fun z_1 => @MapsFind α β tys_1_1 x_1_1 z_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (α : Type) (β : Type) [DecidableEq α] [DecidableEq β] (tys_1_1 : Maps α β) (x_1_1 : α) :
      Plausible.Gen β :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match tys_1_1 with
              | List.cons m _ms => do
                let (z_1 : β) ← ArbitrarySizedSuchThat.arbitrarySizedST (fun (z_1 : β) => MapFind m x_1_1 z_1) initSize;
                return z_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1,
              match tys_1_1 with
              | List.cons m _ms => do
                let (z_1 : β) ← ArbitrarySizedSuchThat.arbitrarySizedST (fun (z_1 : β) => MapFind m x_1_1 z_1) initSize;
                return z_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (Nat.succ size',
              match tys_1_1 with
              | List.cons _m ms => do
                let (z_1 : β) ← aux_arb initSize size' α β ms x_1_1
                return z_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)])
    fun size => aux_arb size size α β tys_1_1 x_1_1

/-- info: "old" -/
#guard_msgs(info) in
#eval
  let P : _ → Prop := fun z => MapsFind [[((2 : Nat), "old")]] 2 z
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

-- -- This works
-- derive_generator (fun α β tys x ty => ∃ Γ, @MapsInsert α β tys x ty Γ)

instance [DecidableEq α] [DecidableEq β] : ArbitrarySizedSuchThat (Maps α β) (fun Γ_1 => @MapsInsert α β tys_1 x_1 ty_1 Γ_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (tys_1 : Maps α β) (x_1 : α)
      (ty_1 : β) : Plausible.Gen (Maps α β) :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1, do
                let (_ : β) ← ArbitrarySizedSuchThat.arbitrarySizedST (fun z_1 => @MapsFind α β tys_1 x_1 z_1) initSize;
                let (Γ_1 : Maps α β) ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun (Γ_1 : Maps α β) => MapsReplace tys_1 x_1 ty_1 Γ_1)
                      initSize;
                return Γ_1),
            (1,
              match tys_1 with
              | List.cons m ms =>
                match DecOpt.decOpt (MapsNotFound (List.cons m ms) x_1) initSize with
                | Except.ok Bool.true => return List.cons (List.cons (Prod.mk x_1 ty_1) m) ms
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ _size' =>
        GeneratorCombinators.backtrack
          [(1, do
                let (_ : β) ← ArbitrarySizedSuchThat.arbitrarySizedST (fun z_1 => @MapsFind α β tys_1 x_1 z_1) initSize;
                let (Γ_1 : Maps α β) ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun (Γ_1 : Maps α β) => MapsReplace tys_1 x_1 ty_1 Γ_1)
                      initSize;
                return Γ_1),
            (1,
              match tys_1 with
              | List.cons m ms =>
                match DecOpt.decOpt (MapsNotFound (List.cons m ms) x_1) initSize with
                | Except.ok Bool.true => return List.cons (List.cons (Prod.mk x_1 ty_1) m) ms
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            ])
    fun size => aux_arb size size tys_1 x_1 ty_1


-- -- This works!
-- derive_generator fun (α β : Type) Γ => ∃ (p : α × β), @MapFind₂ α β Γ p

instance [Plausible.Arbitrary α_1] [DecidableEq α_1] [Plausible.Arbitrary β_1] [DecidableEq β_1] :
    ArbitrarySizedSuchThat (α_1 × β_1) (fun p_1 => @MapFind₂ α_1 β_1 Γ_1 p_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (α_1 : Sort _) (β_1 : Sort _) (Γ_1 : Map α_1 β_1)
      [Plausible.Arbitrary α_1] [DecidableEq α_1] [Plausible.Arbitrary β_1] [DecidableEq β_1] :
      Plausible.Gen (α_1 × β_1) :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match Γ_1 with
              | List.cons (Prod.mk x y) _m => return Prod.mk x y
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
          [(1,
              match Γ_1 with
              | List.cons (Prod.mk x y) _m => return Prod.mk x y
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (Nat.succ size',
              match Γ_1 with
              | List.cons _p m => do
                let (p_1 : Prod α_1 β_1) ← aux_arb initSize size' α_1 β_1 m;
                return p_1
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)])
    fun size => aux_arb size size α_1 β_1 Γ_1


-- --  This does not work for silly reasons, a minor bug in matching on types with a single constructor.
-- derive_generator fun (α β : Type) Γ => ∃ (p : α × β), @MapsFind₂ α β Γ p


instance [Plausible.Arbitrary α_1] [DecidableEq α_1] [Plausible.Arbitrary β_1] [DecidableEq β_1] :
    ArbitrarySizedSuchThat (α_1 × β_1) (fun p_1 => @MapsFind₂ α_1 β_1 Γ_1 p_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (α_1 : Sort _) (β_1 : Sort _) (Γ_1 : Maps α_1 β_1)
      [Plausible.Arbitrary α_1] [DecidableEq α_1] [Plausible.Arbitrary β_1] [DecidableEq β_1] :
      Plausible.Gen (α_1 × β_1) :=
    match size with
    | 0 =>
      match Γ_1 with
      | m :: _ => ArbitrarySizedSuchThat.arbitrarySizedST (fun p => MapFind₂ m p) initSize
      | _ => throw Plausible.Gen.genericFailure
    | size' + 1 => -- Slight hand optimization here, where we can match on Γ_1 directly
      match Γ_1 with
      | m :: ms => GeneratorCombinators.backtrack
        [
          (1, ArbitrarySizedSuchThat.arbitrarySizedST (fun p => MapFind₂ m p) initSize),
          (1, aux_arb initSize size' α_1 β_1 ms)
        ]
      | _ => throw Plausible.Gen.genericFailure
  fun size => aux_arb size size α_1 β_1 Γ_1

/-- info: [[(2, "new")]] -/
#guard_msgs(info) in
#eval
  let P : Maps Nat String → Prop := fun m' => MapsInsert [[((2 : Nat), "old")]] 2 "new" m'
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

/-- info: [[], [(2, "new")]] -/
#guard_msgs(info) in
#eval
  let P : Maps Nat String → Prop := fun m' => MapsInsert [[], [((2 : Nat), "old")]] 2 "new" m'
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

/-- info: [[(2, "new")], [(3, "old")]] -/
#guard_msgs(info) in
#eval
  let P : Maps Nat String → Prop := fun m' => MapsInsert [[], [((3 : Nat), "old")]] 2 "new" m'
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

/-- info: (3, "old") -/
#guard_msgs(info) in
#eval
  let P : _ → Prop := fun m => MapsFind₂ [[], [((3 : Nat), "old")]] m
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10

/-- error: Generation failure:Gen.runUtil: Out of attempts
-/
#guard_msgs(error) in
#eval
  let P : String × Nat → Prop := fun m => MapsFind₂ [[], []] m
  Gen.runUntil (.some 10) (ArbitrarySizedSuchThat.arbitrarySizedST P 10) 10


-- -- This works
-- derive_generator fun ty ty₂ => ∃ ty₁, IsUnaryArg ty ty₁ ty₂

instance : ArbitrarySizedSuchThat LTy (fun ty₁_1 => @IsUnaryArg ty_1 ty₁_1 ty₂_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (ty_1 : LTy) (ty₂_1 : LTy) : Plausible.Gen LTy :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match ty₂_1 with
              | Lambda.LTy.forAll (List.nil) ty₂ =>
                match ty_1 with
                |
                Lambda.LTy.forAll (List.nil)
                    (Lambda.LMonoTy.tcons unk_0 (List.cons ty₁ (List.cons ty₂_1_1 (List.nil)))) =>
                  match @DecOpt.decOpt (@Eq (@Lambda.LMonoTy) ty₂_1_1 ty₂) _ initSize with
                  | Except.ok Bool.true =>
                    match @DecOpt.decOpt (@Eq (@String) unk_0 "arrow") _ initSize with
                    | Except.ok Bool.true => return Lambda.LTy.forAll (List.nil) ty₁
                    | _ => MonadExcept.throw Plausible.Gen.genericFailure
                  | _ => MonadExcept.throw Plausible.Gen.genericFailure
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ _size' =>
        GeneratorCombinators.backtrack
          [(1,
              match ty₂_1 with
              | Lambda.LTy.forAll (List.nil) ty₂ =>
                match ty_1 with
                |
                Lambda.LTy.forAll (List.nil)
                    (Lambda.LMonoTy.tcons unk_0 (List.cons ty₁ (List.cons ty₂_1_1 (List.nil)))) =>
                  match @DecOpt.decOpt (@Eq (@Lambda.LMonoTy) ty₂_1_1 ty₂) _ initSize with
                  | Except.ok Bool.true =>
                    match @DecOpt.decOpt (@Eq (@String) unk_0 "arrow") _ initSize with
                    | Except.ok Bool.true => return Lambda.LTy.forAll (List.nil) ty₁
                    | _ => MonadExcept.throw Plausible.Gen.genericFailure
                  | _ => MonadExcept.throw Plausible.Gen.genericFailure
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            ])
    fun size => aux_arb size size ty_1 ty₂_1


-- -- This works
-- derive_generator fun ty ty₂ => ∃ ty₁, IsUnaryArg ty ty₁ ty₂

instance : ArbitrarySizedSuchThat (LTy × LTy) (fun ty_pair_1 => @IsBinaryArg ty_1 ty_pair_1 ty₃_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (ty_1 : LTy) (ty₃_1 : LTy) : Plausible.Gen (LTy × LTy) :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match ty₃_1 with
              | Lambda.LTy.forAll (List.nil) ty₃ =>
                match ty_1 with
                |
                Lambda.LTy.forAll (List.nil)
                    (Lambda.LMonoTy.tcons unk_0
                      (List.cons ty₁
                        (List.cons (Lambda.LMonoTy.tcons unk_1 (List.cons ty₂ (List.cons ty₃_1_1 (List.nil))))
                          (List.nil)))) =>
                  match @DecOpt.decOpt (@Eq (@Lambda.LMonoTy) ty₃_1_1 ty₃) _ initSize with
                  | Except.ok Bool.true =>
                    match @DecOpt.decOpt (@Eq (@String) unk_1 "arrow") _ initSize with
                    | Except.ok Bool.true =>
                      match @DecOpt.decOpt (@Eq (@String) unk_0 "arrow") _ initSize with
                      | Except.ok Bool.true =>
                        return Prod.mk (Lambda.LTy.forAll (List.nil) ty₁) (Lambda.LTy.forAll (List.nil) ty₂)
                      | _ => MonadExcept.throw Plausible.Gen.genericFailure
                    | _ => MonadExcept.throw Plausible.Gen.genericFailure
                  | _ => MonadExcept.throw Plausible.Gen.genericFailure
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure)]
      | Nat.succ _size' =>
        GeneratorCombinators.backtrack
          [(1,
              match ty₃_1 with
              | Lambda.LTy.forAll (List.nil) ty₃ =>
                match ty_1 with
                |
                Lambda.LTy.forAll (List.nil)
                    (Lambda.LMonoTy.tcons unk_0
                      (List.cons ty₁
                        (List.cons (Lambda.LMonoTy.tcons unk_1 (List.cons ty₂ (List.cons ty₃_1_1 (List.nil))))
                          (List.nil)))) =>
                  match @DecOpt.decOpt (@Eq (@Lambda.LMonoTy) ty₃_1_1 ty₃) _ initSize with
                  | Except.ok Bool.true =>
                    match @DecOpt.decOpt (@Eq (@String) unk_1 "arrow") _ initSize with
                    | Except.ok Bool.true =>
                      match @DecOpt.decOpt (@Eq (@String) unk_0 "arrow") _ initSize with
                      | Except.ok Bool.true =>
                        return Prod.mk (Lambda.LTy.forAll (List.nil) ty₁) (Lambda.LTy.forAll (List.nil) ty₂)
                      | _ => MonadExcept.throw Plausible.Gen.genericFailure
                    | _ => MonadExcept.throw Plausible.Gen.genericFailure
                  | _ => MonadExcept.throw Plausible.Gen.genericFailure
                | _ => MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            ])
    fun size => aux_arb size size ty_1 ty₃_1


-- We don't quite handle this case yet, if `α` is a type variable.
-- Monomorphising `α` and removing the `DecidableEq` constraint gives us an almost perfect generator!

-- derive_generator (fun α eqdec fact ctx ty => ∃ t, @HasType α eqdec fact ctx t ty)

-- For now though, we hand write a specialized version, without certain constants and without polymorphism.
instance {T : LExprParams}
  {C : LContext T}
  {ctx_1 : TContext T.IDMeta}
  [Arbitrary T.mono.base.Metadata]
  [Arbitrary T.IDMeta]
  [DecidableEq T.IDMeta] : ArbitrarySizedSuchThat (LExpr T.mono) (fun t_1 => HasType C ctx_1 t_1 ty_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (ctx_1 : TContext T.IDMeta) (ty_1 : LTy) :
      Plausible.Gen (LExpr T.mono) :=
      (match size with
      | Nat.zero =>
        GeneratorCombinators.backtrack
          [(1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) .bool => do
              if C.knownTypes.containsName "bool" then
                let m ← Arbitrary.arbitrary
                return .boolConst m true
              else MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) .bool => do
              if C.knownTypes.containsName "bool" then
                let m ← Arbitrary.arbitrary
                return .boolConst m false
              else MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) .int => do
              if C.knownTypes.containsName "int" then
                let m ← Arbitrary.arbitrary
                let n ← Arbitrary.arbitrary
                return .intConst m n
              else MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) (.bitvec n) => do
              if C.knownTypes.containsName "bitvec" then
                let m ← Arbitrary.arbitrary
                let bv ← Arbitrary.arbitrary
                return .bitvecConst m n bv
              else MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) .real => do
              if C.knownTypes.containsName "real" then
                let m ← Arbitrary.arbitrary
                let r ← Arbitrary.arbitrary
                return .realConst m r
              else MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) .string => do
              if C.knownTypes.containsName "string" then
                let m ← Arbitrary.arbitrary
                let s ← Arbitrary.arbitrary
                return .strConst m s
              else MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1, do
                let (x : Identifier _ × LTy) ←
                  ArbitrarySizedSuchThat.arbitrarySizedST
                      (fun x => MapsFind₂ (Lambda.TContext.types ctx_1) x) initSize;
                if x.snd = ty_1 then do
                  let m ← Arbitrary.arbitrary
                  return Lambda.LExpr.fvar m x.fst none
                else
                  throw Gen.genericFailure
            )
            ]
      | Nat.succ size' =>
        GeneratorCombinators.backtrack
        [
          (1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) .bool => do
              if C.knownTypes.containsName "bool" then
                let m ← Arbitrary.arbitrary
                return .boolConst m true
              else MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) .bool => do
              if C.knownTypes.containsName "bool" then
                let m ← Arbitrary.arbitrary
                return .boolConst m false
              else MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) .int => do
              if C.knownTypes.containsName "int" then
                let m ← Arbitrary.arbitrary
                let n ← Arbitrary.arbitrary
                return .intConst m n
              else MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) (.bitvec n) => do
              if C.knownTypes.containsName "bitvec" then
                let m ← Arbitrary.arbitrary
                let bv ← Arbitrary.arbitrary
                return .bitvecConst m n bv
              else MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) .real => do
              if C.knownTypes.containsName "real" then
                let m ← Arbitrary.arbitrary
                let r ← Arbitrary.arbitrary
                return .realConst m r
              else MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1,
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) .string => do
              if C.knownTypes.containsName "string" then
                let m ← Arbitrary.arbitrary
                let s ← Arbitrary.arbitrary
                return .strConst m s
              else MonadExcept.throw Plausible.Gen.genericFailure
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),

            (size', do
                let m ← Arbitrary.arbitrary
                let (x : Identifier _ × LTy) ←
                  ArbitrarySizedSuchThat.arbitrarySizedST
                      (fun x_x_ty => MapsFind₂ (Lambda.TContext.types ctx_1) x_x_ty) initSize;
                  if x.snd = ty_1 then
                  return Lambda.LExpr.fvar m x.fst none
                else
                  throw Gen.genericFailure),
            (0, -- FIXME: for now we avoid generating lambdas for the Strata Core translator.
              match ty_1 with
              |
              Lambda.LTy.forAll (List.nil)
                  (Lambda.LMonoTy.tcons "arrow"
                    (List.cons (x_ty)
                      (List.cons (e_ty) (List.nil)))) => do
                let m ← Arbitrary.arbitrary
                let x : Identifier _ ← Arbitrary.arbitrary
                let x_ty' := LTy.forAll [] x_ty
                let e_ty' := LTy.forAll [] e_ty
                let Γ' : Maps (Identifier _) LTy ←
                    ArbitrarySizedSuchThat.arbitrarySizedST
                        (fun (Γ' : Maps (Identifier T.IDMeta) LTy) =>
                          MapsInsert (Lambda.TContext.types ctx_1) x x_ty' Γ') initSize;
                let e ← aux_arb initSize size' {ctx_1 with types := Γ'} e_ty'
                let e := LExpr.varClose 0 (x, none) e
                return .abs m x_ty e
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (Nat.succ size', do
              let (t2 : LMonoTy) ← Plausible.Arbitrary.arbitrary;
              do
                let (e2 : LExpr _) ← aux_arb initSize size' ctx_1 (.forAll [] t2);
                do
                  if h1 : isMonoType ty_1 then
                  let (e1 : LExpr _) ←
                    aux_arb initSize size' ctx_1
                            (Lambda.LTy.forAll (List.nil)
                              (Lambda.LMonoTy.tcons "arrow"
                                (List.cons (t2)
                                  (List.cons (Lambda.LTy.toMonoType ty_1 h1) (List.nil)))));

                      let m ← Arbitrary.arbitrary
                      return Lambda.LExpr.app m e1 e2
                  else MonadExcept.throw Plausible.Gen.genericFailure),
            (Nat.succ size', do
              let (c : LExpr _) ←
                aux_arb initSize size' ctx_1 (Lambda.LTy.forAll (List.nil) (Lambda.LMonoTy.tcons "bool" (List.nil)));
              do
                let (e1 : LExpr _) ← aux_arb initSize size' ctx_1 ty_1;
                do
                  let (e2 : LExpr _) ← aux_arb initSize size' ctx_1 ty_1;
                  let m ← Arbitrary.arbitrary
                  return Lambda.LExpr.ite m c e1 e2),
            (Nat.succ size',
              match ty_1 with
              | Lambda.LTy.forAll (List.nil) (Lambda.LMonoTy.tcons "bool" (List.nil)) => do
                let (ty : LTy) ← Plausible.Arbitrary.arbitrary;
                do
                  let (e1 : LExpr _) ← aux_arb initSize size' ctx_1 ty;
                  do
                    let (e2 : LExpr _) ← aux_arb initSize size' ctx_1 ty;
                    let m ← Arbitrary.arbitrary
                    return Lambda.LExpr.eq m e1 e2
              | _ => MonadExcept.throw Plausible.Gen.genericFailure),
            (1, do
              let (f : LFunc _) ←
                @ArbitrarySizedSuchThat.arbitrarySizedST _
                    (fun (f : LFunc _) =>
                      @ArrayFind (@Lambda.LFunc _) (@Lambda.LContext.functions _ C) f)
                    _ initSize;
              do
                match f.type with
                | .ok f_ty =>
                  if f_ty = ty_1 then do
                    let m ← Arbitrary.arbitrary
                    return Lambda.LExpr.op m f.name (Option.none)
                  else throw Plausible.Gen.genericFailure
                | _ => throw Plausible.Gen.genericFailure
                ),
            (10, do
                  let (f : LFunc T) ←
                    @ArbitrarySizedSuchThat.arbitrarySizedST _
                        (fun (f : LFunc T) =>
                          @ArrayFind (@Lambda.LFunc T) (@Lambda.LContext.functions T C)
                            f)
                        _ initSize;
                  let (ty₁ : LTy) ←  @ArbitrarySizedSuchThat.arbitrarySizedST _ (fun (ty₁ : LTy) => @IsUnaryArg (@LFunc.type! T f) ty₁ ty_1) _ initSize;
                  let (t₁ : LExpr (LExprParams.mono T)) ← aux_arb initSize size' ctx_1 ty₁;
                  let (m : _) ← Plausible.Arbitrary.arbitrary;
                  return Lambda.LExpr.app m (Lambda.LExpr.op m f.name (Option.none)) t₁),
            (10, do
                    let (f : LFunc T) ←
                      @ArbitrarySizedSuchThat.arbitrarySizedST _
                          (fun (f : LFunc T) =>
                            @ArrayFind (@Lambda.LFunc T)
                              (@Lambda.LContext.functions T C) f)
                          _ initSize;
                    do
                      let vty₁_ty₂ ←
                        @ArbitrarySizedSuchThat.arbitrarySizedST _
                            (fun vty₁_ty₂ => @IsBinaryArg (@LFunc.type! T f) vty₁_ty₂ ty_1) _ initSize;
                      match vty₁_ty₂ with
                        | @Prod.mk (@Lambda.LTy) (@Lambda.LTy) ty₁ ty₂ => do
                          let (t₂ : LExpr (LExprParams.mono T)) ← aux_arb initSize size' ctx_1 ty₂;
                          let (t₁ : LExpr (LExprParams.mono T)) ← aux_arb initSize size' ctx_1 ty₁;
                          let (m : _) ← Plausible.Arbitrary.arbitrary;
                          return Lambda.LExpr.app m (Lambda.LExpr.app m (Lambda.LExpr.op m f.name (Option.none)) t₁) t₂)
        ])
    fun size => aux_arb size size ctx_1 ty_1


#guard_msgs(drop info) in
#eval Gen.printSamples (Arbitrary.arbitrary : Gen LMonoTy)

abbrev example_lctx : LContext TrivialParams :=
{ LContext.empty with knownTypes := KnownTypes.default
                      functions := Lambda.IntBoolFactory
}

abbrev example_ctx : TContext Unit := ⟨[[]], []⟩
-- abbrev example_ty : LTy := .forAll [] <| .tcons "bool" []
abbrev example_ty : LTy := .forAll [] <| .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]

/-- info: [[({ name := "y", metadata := () }, Lambda.LTy.forAll [] (Lambda.LMonoTy.tcons "int" []))]] -/
#guard_msgs(info) in
#eval
  let P : Maps (Identifier Unit) LTy → Prop := fun Γ => MapsInsert (example_ctx.types) "y" (.forAll [] (.tcons "int" [])) Γ
  Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 5) 5


#guard_msgs(drop info) in
#time #eval
    let P : LExpr TrivialParams.mono → Prop := fun t => HasType example_lctx example_ctx t example_ty
    Gen.runUntil .none (ArbitrarySizedSuchThat.arbitrarySizedST P 4) 4

def example_lstate :=
  { LState.init (T := TrivialParams) with config :=
    { LState.init.config (T := TrivialParams) with
      factory := Lambda.IntBoolFactory (T := TrivialParams)}
  }

/-- `Monad` instance for List.
    Note that:
    - The Lean standard library does not have a Monad instance for List (see https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Option.20do.20notation.20regression.3F.html#231433226)
    - MathLib4 does have a Monad instance for List, but we wish to avoid having Chamelean rely on Mathlib
    as a dependency, so we reproduce instance here instead. -/
private instance : Monad List where
  pure x := [x]
  bind xs f := xs.flatMap f

instance [Inhabited T.base.IDMeta] : Shrinkable (LExpr T) where
  shrink t :=
  let rec aux (t : LExpr T) : List (LExpr T) :=
  match t with
    | .fvar _ _ _
    | .bvar _ _
    | .op _ _ _
    | .const _ _ -- We're being a bit lazy here for the time being
              => []
    | .app m t u =>
      t :: u :: (.app m <$> aux t <*> aux u)
    | .abs m ty t => (LExpr.varOpen 0 ⟨⟨"x", default⟩, ty⟩ t) :: (.abs m ty <$> aux t) -- IDK about the `"x"`
    | .eq m t u => t :: u :: (.eq m <$> aux t <*> aux u)
    | .ite m cond t u => cond :: t :: u :: (.ite m <$> aux cond <*> aux t <*> aux u)
    | .quant m k ty tr t => (LExpr.varOpen 0 ⟨⟨"x", default⟩, ty⟩ t) :: (.quant m k ty tr <$> aux t)
  aux t

-- Shrinks an element of `α` recursively.
partial def shrinkFunAux [Shrinkable α] (f : α → Bool) (x : α) : Option α := do
  let candidates := Shrinkable.shrink x
  let y ← candidates.find? f
  let z := shrinkFunAux f y
  z <|> some y

def shrinkFun [Shrinkable α] (f : α → Bool) (x : α) : α :=
let shrinked := shrinkFunAux f x
match shrinked with
| .some y => y
| .none => x

/-- info: [LExpr.fvar () { name := "x", metadata := () } none, LExpr.fvar () { name := "y", metadata := () } none] -/
#guard_msgs(info) in
#eval Shrinkable.shrink (LExpr.eq (T := TrivialParams.mono) () (.fvar () "x" .none) (.fvar () "y" .none))

/-- info: 2 -/
#guard_msgs(info) in
#eval shrinkFun (fun n : Nat => n % 3 == 2) 42

def annotate (t : LExpr TrivialParams.mono) :=
  let state : TState := {}
  let env : TEnv Unit := { genEnv := ⟨example_ctx, state⟩ }
  LExpr.annotate example_lctx env t

def canAnnotate (t : LExpr TrivialParams.mono) : Bool :=
  (annotate t).isOk


#guard_msgs(drop info) in
#eval Strata.Util.withStdGenSeed 0 do
    let P : LExpr TrivialParams.mono → Prop := fun t => HasType example_lctx example_ctx t example_ty
    let t ← Gen.runUntil (.some 10) (ArbitrarySizedSuchThat.arbitrarySizedST P 5) 5
    IO.println s!"Generated {t}"

/-- info: Generating terms of type
Lambda.LTy.forAll [] (Lambda.LMonoTy.tcons "arrow" [Lambda.LMonoTy.tcons "bool" [], Lambda.LMonoTy.tcons "bool" []])
in context
{ types := [[]], aliases := [] }
in factory
#[Int.Add, Int.Sub, Int.Mul, Int.Div, Int.Mod, Int.Neg, Int.Lt, Int.Le, Int.Gt, Int.Ge, Bool.And, Bool.Or, Bool.Implies, Bool.Equiv, Bool.Not]
-/
#guard_msgs in
#eval Strata.Util.withStdGenSeed 0 do
  IO.println s!"Generating terms of type\n{example_ty}\nin context\n{repr example_ctx}\nin \
                factory\n{example_lctx.functions.map (fun f : LFunc TrivialParams => f.name)}\n"
  for i in List.range 100 do
    let P : LExpr TrivialParams.mono → Prop := fun t => HasType example_lctx example_ctx t example_ty
    let t ← Gen.runUntil (.some 1000) (ArbitrarySizedSuchThat.arbitrarySizedST P 5) 5
    -- IO.println s!"Generated {t}"
    if !(canAnnotate t) then
      let .error e := annotate t | throw <| IO.Error.userError "Unreachable"
      IO.println s!"FAILED({i}): {e}\n{t}\n\nSHRUNK TO:\n{shrinkFun (not ∘ canAnnotate) t}\n\n"

def isIntConst (t : LExpr TrivialParams.mono) : Bool :=
match t with
| .const _ (.intConst _) => true
| _ => false

def reduces (t : LExpr TrivialParams.mono) : Bool :=
  let t' := t.eval 1000 example_lstate
  isIntConst t'

/-- info: Generating terms of type
Lambda.LTy.forAll [] (Lambda.LMonoTy.tcons "arrow" [Lambda.LMonoTy.tcons "bool" [], Lambda.LMonoTy.tcons "bool" []])
in context
{ types := [[]], aliases := [] }
in factory
#[Int.Add, Int.Sub, Int.Mul, Int.Div, Int.Mod, Int.Neg, Int.Lt, Int.Le, Int.Gt, Int.Ge, Bool.And, Bool.Or, Bool.Implies, Bool.Equiv, Bool.Not]
-/
#guard_msgs(info, drop error) in
#eval Strata.Util.withStdGenSeed 0 do
  IO.println s!"Generating terms of type\n{example_ty}\nin context\n{repr example_ctx}\nin \
                factory\n{example_lctx.functions.map (fun f : LFunc _ => f.name)}\n"
  for _i in List.range 100 do
    let P : LExpr TrivialParams.mono → Prop := fun t => HasType example_lctx example_ctx t (.forAll [] (.tcons "int" []))
    let t ← Gen.runUntil (.some 1000) (ArbitrarySizedSuchThat.arbitrarySizedST P 5) 5
    -- Unfortunately this *can* fail, if we compare two terms at arrow types, or try to take mod 0 etc.
    if !(reduces t) then
      -- IO.println s!"NOT A VALUE({i}): {t}\nREDUCES TO\n{t.eval 10000 example_lstate}\n\n"
      continue
