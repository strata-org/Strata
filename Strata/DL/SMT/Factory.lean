/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.Basic
import Strata.DL.SMT.Function
import Strata.DL.SMT.Op
import Strata.DL.SMT.Term
import Strata.DL.SMT.TermType


/-!
Based on Cedar's Term language.
(https://github.com/cedar-policy/cedar-spec/blob/main/cedar-lean/Cedar/SymCC/Factory.lean)
This file defines an API for construcing well-formed Terms. In this basic
implementation, the factory functions perform only basic partial
evaluation---constant folding along with a few other rewrites.  In an optimized
implementation, the factory functions would include more rewrite rules, and
share a cache of partially cannonicalized terms that have been constructed so
far.

The factory functions are total. If given well-formed and type-correct
arguments, a factory function will return a well-formed and type-correct output.
Otherwise, the output is an arbitrary term.

This design lets us minimize the number of error paths in the overall
specification of symbolic evaluation, which makes for nicer code and proofs, and
it more closely tracks the specification of the concrete evaluator.

See `Evaluator.lean` to see how the symbolic evaluator uses this API.
-/

namespace Strata.SMT

namespace Factory

---------- Term constructors ----------

def noneOf (ty : TermType) : Term := .none ty

def someOf (t : Term) : Term := .some t

---------- SMTLib core theory of equality with uninterpreted functions (`UF`) ----------

def not : Term → Term
  | .prim (.bool b)  => ! b
  | .app .not [t'] _ => t'
  | t                => .app .not [t] .bool

def opposites : Term → Term → Bool
  | t₁, .app .not [t₂] _
  | .app .not [t₁] _, t₂ => t₁ = t₂
  | _, _                 => false

def and (t₁ t₂ : Term) : Term :=
  if t₁ = t₂ || t₂ = true
  then t₁
  else if t₁ = true
  then t₂
  else if t₁ = false || t₂ = false || opposites t₁ t₂
  then false
  else .app .and [t₁, t₂] .bool

def or (t₁ t₂ : Term) : Term :=
  if t₁ = t₂ || t₂ = false
  then t₁
  else if t₁ = false
  then t₂
  else if t₁ = true || t₂ = true || opposites t₁ t₂
  then true
  else .app .or [t₁, t₂] .bool

def implies (t₁ t₂ : Term) : Term :=
  or (not t₁) t₂

def eq (t₁ t₂ : Term) : Term :=
  if t₁ = t₂
  then true
  else if t₁.isLiteral && t₂.isLiteral
  then false
  else match t₁, t₂ with
  | .some t₁', .some t₂' => .app .eq [t₁', t₂'] .bool
  | .some _, .none _     => false
  | .none _, .some _     => false
  | _, _                 => .app .eq [t₁, t₂] .bool

def ite (t₁ t₂ t₃ : Term) : Term :=
  if t₁ = true || t₂ = t₃
  then t₂
  else if t₁ = false
  then t₃
  else match t₂, t₃ with
  | .some t₂', .some t₃' => -- Pull `some` wrappers to the top
    .some (.app .ite [t₁, t₂', t₃'] t₂'.typeOf)
  | _, _ =>
    .app .ite [t₁, t₂, t₃] t₂.typeOf

/-
Returns the result of applying function to a list of terms.

(TODO) Arity check?
-/
def app : Function → List Term → Term
  | .uf f, ts => .app (.uf f) ts f.out

-- Note: we could coalesce nested quantifiers here, since SMT-Lib allows multiple variables to be bound at once.
def quant (qk : QuantifierKind) (x : String) (ty : TermType) (e : Term) : Term :=
  .quant qk x ty e

---------- SMTLib theory of integer numbers (`Ints`) ----------

def intNeg : Term → Term
  | .prim (.int i) => i.neg
  | t              => .app .neg [t] t.typeOf

def intAbs : Term → Term
  | .prim (.int i) => Int.ofNat i.natAbs
  | t              => .app .abs [t] t.typeOf

def intapp (op : Op) (fn : Int → Int → Int) (t₁ t₂ : Term) : Term :=
  match t₁, t₂ with
  | .prim (.int i₁), .prim (.int i₂) => fn i₁ i₂
  | _, _ => .app op [t₁, t₂] t₁.typeOf

def intSub := intapp .sub Int.sub
def intAdd := intapp .add Int.add
def intMul := intapp .mul Int.mul
def intDiv := intapp .div Int.ediv
def intMod := intapp .mod Int.emod

def intcmp (op : Op) (fn : Int → Int → Bool) (t₁ t₂ : Term) : Term :=
  match t₁, t₂ with
  | .prim (.int i₁), .prim (.int i₂) => fn i₁ i₂
  | _, _ => .app op [t₁, t₂] .bool

def intLe  := intcmp .le (λ i₁ i₂ => i₁ <= i₂)
def intLt  := intcmp .lt (λ i₁ i₂ => i₁ < i₂)
def intGe  := intcmp .ge (λ i₁ i₂ => i₁ >= i₂)
def intGt  := intcmp .gt (λ i₁ i₂ => i₁ > i₂)

---------- SMTLib theory of finite bitvectors (`BV`) ----------

-- We are doing very weak partial evaluation for bitvectors: just constant
-- propagation. If more rewrites are needed, we can add them later.  This simple
-- approach is sufficient for the strong PE property we care about:  if given a
-- fully concrete input, the symbolic evaluator returns a fully concrete output.

def bvneg : Term → Term
  | .prim (.bitvec b)  => b.neg
  | t                  => .app .bvneg [t] t.typeOf

def bvapp (op : Op) (fn : ∀ {n}, BitVec n → BitVec n → BitVec n) (t₁ t₂ : Term) : Term :=
  match t₁, t₂ with
  | .prim (@TermPrim.bitvec n b₁), .prim (.bitvec b₂) =>
    fn b₁ (BitVec.ofNat n b₂.toNat)
  | _, _ =>
    .app op [t₁, t₂] t₁.typeOf

def bvadd := bvapp .bvadd BitVec.add
def bvsub := bvapp .bvsub BitVec.sub
def bvmul := bvapp .bvmul BitVec.mul

def bvshl  := bvapp .bvshl (λ b₁ b₂ => b₁ <<< b₂)
def bvlshr := bvapp .bvlshr (λ b₁ b₂ => b₁ >>> b₂)

def bvcmp (op : Op) (fn : ∀ {n}, BitVec n → BitVec n → Bool) (t₁ t₂ : Term) : Term :=
  match t₁, t₂ with
  | .prim (@TermPrim.bitvec n b₁), .prim (.bitvec b₂) =>
    fn b₁ (BitVec.ofNat n b₂.toNat)
  | _, _ =>
    .app op [t₁, t₂] .bool

def bvslt := bvcmp .bvslt BitVec.slt
def bvsle := bvcmp .bvsle BitVec.sle
def bvult := bvcmp .bvult BitVec.ult
def bvule := bvcmp .bvule BitVec.ule

def bvnego : Term → Term
  | .prim (@TermPrim.bitvec n b₁) => BitVec.overflows n (-b₁.toInt)
  | t                             => .app .bvnego [t] .bool

def bvso (op : Op) (fn : Int → Int → Int) (t₁ t₂ : Term) : Term :=
  match t₁, t₂ with
  | .prim (@TermPrim.bitvec n b₁), .prim (.bitvec b₂) =>
    BitVec.overflows n (fn b₁.toInt b₂.toInt)
  | _, _ => .app op [t₁, t₂] .bool

def bvsaddo := bvso .bvsaddo (· + ·)
def bvssubo := bvso .bvssubo (· - ·)
def bvsmulo := bvso .bvsmulo (· * ·)

/-
Note that BitVec defines zero_extend differently from SMTLib,
so we compensate for the difference in partial evaluation.
-/
def zero_extend (n : Nat) : Term → Term
  | .prim (@TermPrim.bitvec m b) =>
    BitVec.zeroExtend (n + m) b
  | t =>
    match t.typeOf with
    | .bitvec m => .app (.zero_extend n) [t] (.bitvec (n + m))
    | _         => t -- should be ruled out by callers


---------- Core ADT operators with a trusted mapping to SMT ----------

def option.get : Term → Term
  | .some t  => t
  | t        =>
    match t.typeOf with
    | .option ty => .app .option.get [t] ty
    | _          => t

end Factory

end Strata.SMT
