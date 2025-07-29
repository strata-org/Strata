/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

import Strata.DL.SMT.TermType
import Strata.DL.SMT.Basic
import Strata.DL.SMT.Op

/-!
Based on Cedar's Term language.
(https://github.com/cedar-policy/cedar-spec/blob/main/cedar-lean/Cedar/SymCC/Term.lean)
This file defines the Term language, a strongly and simply typed IR. The Term language
has a straightforward translation to SMTLib. It is designed to reduce the
semantic gap between Strata and SMTLib, and to faciliate proofs of soundness and
completeness of the symbolic evaluator. Additionally, it allows us to generate
different SMT encodings for different solvers (e.g., CVC5's theory of finite sets
vs Z3's theory of Arrays).

Terms should _not_ be created directly using `Term` constructors. Instead, they
should be created using the factory functions defined in `Factory.lean`.
The factory functions check the types of their arguments, perform optimizations,
and ensure that applying them to well-formed terms results in well-formed terms.

See `TermType.lean` and `Op.lean` for definition of Term types and
operators.
-/

namespace Strata.SMT

inductive TermPrim : Type where
  | bool   : Bool → TermPrim
  | int    : Int → TermPrim
  | real   : String → TermPrim
  | bitvec : ∀ {n}, BitVec n → TermPrim
  | string : String → TermPrim
deriving instance Repr, Inhabited, DecidableEq for TermPrim

def TermPrim.mkName : TermPrim → String
  | .bool _   => "bool"
  | .int _    => "int"
  | .real _   => "real"
  | .bitvec _ => "bitvec"
  | .string _ => "string"

def TermPrim.lt : TermPrim → TermPrim → Bool
  | .bool b₁, .bool b₂         => b₁ < b₂
  | .int  i₁, .int i₂          => i₁ < i₂
  | .real r₁, .real r₂         => r₁ < r₂ -- TODO
  | @TermPrim.bitvec n₁ bv₁,
    @TermPrim.bitvec n₂ bv₂    => n₁ < n₂ || (n₁ = n₂ && bv₁.toNat < bv₂.toNat)
  | .string s₁, .string s₂     => s₁ < s₂
  | p₁, p₂                     => p₁.mkName < p₂.mkName

instance : LT TermPrim where
  lt := fun x y => TermPrim.lt x y

instance TermPrim.decLt (x y : TermPrim) : Decidable (x < y) :=
  if h : TermPrim.lt x y then isTrue h else isFalse h

inductive QuantifierKind
  | all
  | exist
deriving Repr, DecidableEq

inductive Term : Type where
  | prim    : TermPrim → Term
  | var     : TermVar → Term
  | none    : TermType → Term
  | some    : Term → Term
  | app     : Op → (args: List Term) → (retTy: TermType) → Term
  | quant   : QuantifierKind → String → TermType → Term → Term
deriving instance Repr, Inhabited for Term

def Term.isVar (t : Term) : Bool :=
  match t with
  | .var _ => true
  | _ => false

def Term.isFreeVar (t : Term) : Bool :=
  match t with
  | .var v => !v.isBound
  | _ => false

mutual
def Term.hasDecEq (t t' : Term) : Decidable (t = t') := by
  cases t <;> cases t' <;>
  try { apply isFalse ; intro h ; injection h }
  case prim.prim v₁ v₂ | none.none v₁ v₂ | var.var v₁ v₂ =>
    exact match decEq v₁ v₂ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case some.some t t' =>
    exact match Term.hasDecEq t t' with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case app.app op ts ty op' ts' ty' =>
    exact match decEq op op', Term.hasListDec ts ts', decEq ty ty' with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse h₁, _, _ | _, isFalse h₁, _ | _, _, isFalse h₁ =>
      isFalse (by intro h₂; simp [h₁] at h₂)
  case quant.quant qk x ty t qk' x' ty' t' =>
    exact match decEq qk qk', decEq x x', decEq ty ty', Term.hasDecEq t t' with
    | isTrue h₁, isTrue h₂, isTrue h₃, isTrue h₄ => isTrue (by rw [h₁, h₂, h₃, h₄])
    | isFalse h₁, _, _, _ | _, isFalse h₁, _, _ | _, _, isFalse h₁, _ | _, _, _, isFalse h₁ =>
      isFalse (by intro h₂; simp [h₁] at h₂)

def Term.hasListDec (ts₁ ts₂ : List Term) : Decidable (ts₁ = ts₂) :=
  match ts₁, ts₂ with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | t₁ :: tl₁, t₂ :: tl₂ =>
    match Term.hasDecEq t₁ t₂ with
    | isTrue h₁ =>
        match Term.hasListDec tl₁ tl₂ with
        | isTrue h₂ => isTrue (by subst h₁ h₂; rfl)
        | isFalse _ => isFalse (by simp; intros; assumption)
    | isFalse _ => isFalse (by simp; intros; contradiction)
end

instance : DecidableEq Term := Term.hasDecEq

instance : Hashable Term where
  hash := λ a => hash s!"{repr a}"

def Term.mkName : Term → String
  | .prim _     => "prim"
  | .var _      => "var"
  | .none _     => "none"
  | .some _     => "some"
  | .app _ _ _  => "app"
  | .quant .all _ _ _ => "all"
  | .quant .exist _ _ _ => "exists"

mutual
def Term.lt : Term → Term → Bool
  | .prim p₁, .prim p₂                     => p₁ < p₂
  | .var v₁, .var v₂                       => v₁ < v₂
  | .none ty₁, .none ty₂                   => ty₁ < ty₂
  | .some t₁, .some t₂                     => Term.lt t₁ t₂
  | .app o ts ty, .app o' ts' ty'          =>
    o < o' ||
    (o = o' && Term.ltList ts ts') ||
    (o = o' && ts = ts' && ty < ty')
  | t₁, t₂                                 => t₁.mkName < t₂.mkName
termination_by t _ => sizeOf t

def Term.ltList : List Term → List Term → Bool
  | [], []    => false
  | [], _::_  => true
  | _::_, []  => false
  | t₁ :: ts₁, t₂ :: ts₂ => Term.lt t₁ t₂ || (t₁ = t₂ && Term.ltList ts₁ ts₂)
termination_by ts _ => sizeOf ts
end

instance : LT Term where
  lt := fun x y => Term.lt x y

instance Term.decLt (x y : Term) : Decidable (x < y) :=
  if h : Term.lt x y then isTrue h else isFalse h

abbrev Term.bool (b : Bool) : Term := .prim (.bool b)
abbrev Term.int  (i : Int) : Term := .prim (.int i)
abbrev Term.real  (r : String) : Term := .prim (.real r)
abbrev Term.bitvec {n : Nat} (bv : BitVec n) : Term := .prim (.bitvec bv)
abbrev Term.string (s : String) : Term := .prim (.string s)

def TermPrim.typeOf : TermPrim → TermType
  | .bool _           => .bool
  | .int _            => .int
  | .real _           => .real
  | .bitvec b         => .bitvec b.width
  | .string _         => .string

def Term.typeOf : Term → TermType
  | .prim l       => l.typeOf
  | .var v        => v.ty
  | .none ty      => .option ty
  | .some t       => .option t.typeOf
  | .app _ _ ty   => ty
  | .quant _ _ _ _ => .bool


def Term.isLiteral : Term → Bool
  | .prim _
  | .none _               => true
  | .some t               => t.isLiteral
  | _                     => false

instance : Coe Bool Term where
  coe b := .prim (.bool b)

instance : Coe Int Term where
  coe i := .prim (.int i)

instance : Coe Int64 Term where
  coe i := .prim (.bitvec i.toBitVec)

instance : CoeOut (BitVec n) Term where
  coe b := .prim (.bitvec b)

instance : Coe String Term where
  coe s := .prim (.string s)

instance : Coe TermVar Term where
  coe v := .var v

end Strata.SMT
