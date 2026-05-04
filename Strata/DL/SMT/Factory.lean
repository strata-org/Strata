/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Util.BitVec
public import Strata.DL.SMT.Function
public import Strata.DL.SMT.Op
public import Strata.DL.SMT.Term
public import Strata.DL.SMT.TermType


@[expose] public section
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

-- Correctness: `Factory.noneOf_correct`
def noneOf (ty : TermType) : Term := .none ty

-- Correctness: `Factory.someOf_correct`
def someOf (t : Term) : Term := .some t

---------- SMTLib core theory of equality with uninterpreted functions (`UF`) ----------

-- Correctness: `Factory.not_correct`
def not : Term → Term
  | .prim (.bool b)  => ! b
  | .app .not [t'] _ => t'
  | t                => .app .not [t] .bool

def opposites : Term → Term → Bool
  | t₁, .app .not [t₂] _
  | .app .not [t₁] _, t₂ => t₁ = t₂
  | _, _                 => false

-- Correctness: `Factory.and_correct`
def and (t₁ t₂ : Term) : Term :=
  if t₁ = t₂ || t₂ = true
  then t₁
  else if t₁ = true
  then t₂
  else if t₁ = false || t₂ = false || opposites t₁ t₂
  then false
  else .app .and [t₁, t₂] .bool

-- Correctness: `Factory.or_correct`
def or (t₁ t₂ : Term) : Term :=
  if t₁ = t₂ || t₂ = false
  then t₁
  else if t₁ = false
  then t₂
  else if t₁ = true || t₂ = true || opposites t₁ t₂
  then true
  else .app .or [t₁, t₂] .bool

-- Correctness: `Factory.implies_correct`
def implies (t₁ t₂ : Term) : Term :=
  or (not t₁) t₂

-- Correctness: `Factory.eq_correct_bool`, `Factory.eq_correct_int`,
-- `Factory.eq_correct_bv`, `Factory.eq_correct_string`
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

-- Correctness: `Factory.ite_correct_bool`, `Factory.ite_correct_int`,
-- `Factory.ite_correct_bv`, `Factory.ite_correct_string`
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

def addTrigger : Term → Term → Term
| t, .app .triggers ts .trigger =>  .app .triggers (t :: ts) .trigger
| t, _ => t

def addTriggerList (args : List Term) (ty : TermType) : Term  :=
  match args with
  | [t, ts] => addTrigger t ts
  | _ => .app .triggers args ty

/-
Returns the result of applying function to a list of terms.

(TODO) Arity check?
-/
-- Correctness: `Factory.app_uf_correct`
def app : Function → List Term → Term
  | .uf f, ts => .app (.uf f) ts f.out

def isSimpleTrigger : Term → Bool
| .var _ => true
| .app .triggers [] .trigger => true
| .app .triggers [t] .trigger => isSimpleTrigger t
| _ => false

def mkSimpleTrigger (x : String) (ty : TermType) : Term :=
  .app .triggers [.var (TermVar.mk x ty)] .trigger -- TODO: empty list instead?

theorem mkSimpleTriggerIsSimple: isSimpleTrigger (mkSimpleTrigger x ty) := by
  simp [isSimpleTrigger, mkSimpleTrigger]

-- Note: we could coalesce nested quantifiers here, since SMT-Lib allows multiple variables to be bound at once.
-- TODO: Its correctness could not be proven due to its complexity. Contribution is welcome
def quant (qk : QuantifierKind) (x : String) (ty : TermType) (tr : Term) (e : Term) : Term :=
  -- Check if we can coalesce with a nested quantifier
  match e with
  | .quant qk2 args2 tr2 e2 =>
    -- Coalesce if:
    -- 1. Same quantifier kind
    -- 2. Outer trigger is just a bound variable (indicating no meaningful trigger)
    if qk = qk2 && isSimpleTrigger tr then
      -- If both triggers are simple, use the first variable as trigger
      -- Otherwise use the inner trigger (which is more meaningful)
      let coalescedTrigger := if isSimpleTrigger tr2 then (mkSimpleTrigger x ty) else tr2
      .quant qk ([⟨x, ty⟩] ++ args2) coalescedTrigger e2
    else
      .quant qk [⟨x, ty⟩] tr e
  | _ =>
    .quant qk [⟨x, ty⟩] tr e

---------- SMTLib theory of integer numbers (`Ints`) ----------

-- Correctness: `Factory.intNeg_correct`
def intNeg : Term → Term
  | .prim (.int i) => i.neg
  | t              => .app .neg [t] t.typeOf

-- Correctness: `Factory.intAbs_correct`
def intAbs : Term → Term
  | .prim (.int i) => Int.ofNat i.natAbs
  | t              => .app .abs [t] t.typeOf

def intapp (op : Op) (fn : Int → Int → Int) (t₁ t₂ : Term) : Term :=
  match t₁, t₂ with
  | .prim (.int i₁), .prim (.int i₂) => fn i₁ i₂
  | _, _ => .app op [t₁, t₂] t₁.typeOf

-- Correctness: `Factory.intSub_correct`
def intSub := intapp .sub Int.sub
-- Correctness: `Factory.intAdd_correct`
def intAdd := intapp .add Int.add
-- Correctness: `Factory.intMul_correct`
def intMul := intapp .mul Int.mul
-- Correctness: `Factory.intDiv_correct`
def intDiv := intapp .div Int.ediv
-- Correctness: `Factory.intMod_correct`
def intMod := intapp .mod Int.emod

def intcmp (op : Op) (fn : Int → Int → Bool) (t₁ t₂ : Term) : Term :=
  match t₁, t₂ with
  | .prim (.int i₁), .prim (.int i₂) => fn i₁ i₂
  | _, _ => .app op [t₁, t₂] .bool

-- Correctness: `Factory.intLe_correct`
def intLe  := intcmp .le (λ i₁ i₂ => i₁ <= i₂)
-- Correctness: `Factory.intLt_correct`
def intLt  := intcmp .lt (λ i₁ i₂ => i₁ < i₂)
-- Correctness: `Factory.intGe_correct`
def intGe  := intcmp .ge (λ i₁ i₂ => i₁ >= i₂)
-- Correctness: `Factory.intGt_correct`
def intGt  := intcmp .gt (λ i₁ i₂ => i₁ > i₂)

---------- SMTLib theory of finite bitvectors (`BV`) ----------

-- We are doing very weak partial evaluation for bitvectors: just constant
-- propagation. If more rewrites are needed, we can add them later.  This simple
-- approach is sufficient for the strong PE property we care about:  if given a
-- fully concrete input, the symbolic evaluator returns a fully concrete output.

-- Correctness: `Factory.bvneg_correct`
def bvneg : Term → Term
  | .prim (.bitvec b)  => b.neg
  | t                  => .app .bvneg [t] t.typeOf

def bvapp (op : Op) (fn : ∀ {n}, BitVec n → BitVec n → BitVec n) (t₁ t₂ : Term) : Term :=
  match t₁, t₂ with
  | .prim (@TermPrim.bitvec n b₁), .prim (.bitvec b₂) =>
    fn b₁ (BitVec.ofNat n b₂.toNat)
  | _, _ =>
    .app op [t₁, t₂] t₁.typeOf

-- Correctness: `Factory.bvadd_correct`
def bvadd := bvapp .bvadd BitVec.add
-- Correctness: `Factory.bvsub_correct`
def bvsub := bvapp .bvsub BitVec.sub
-- Correctness: `Factory.bvmul_correct`
def bvmul := bvapp .bvmul BitVec.mul

-- Correctness: `Factory.bvshl_correct`
def bvshl  := bvapp .bvshl (λ b₁ b₂ => b₁ <<< b₂)
-- Correctness: `Factory.bvlshr_correct`
def bvlshr := bvapp .bvlshr (λ b₁ b₂ => b₁ >>> b₂)

def bvcmp (op : Op) (fn : ∀ {n}, BitVec n → BitVec n → Bool) (t₁ t₂ : Term) : Term :=
  match t₁, t₂ with
  | .prim (@TermPrim.bitvec n b₁), .prim (.bitvec b₂) =>
    fn b₁ (BitVec.ofNat n b₂.toNat)
  | _, _ =>
    .app op [t₁, t₂] .bool

-- Correctness: `Factory.bvslt_correct`
def bvslt := bvcmp .bvslt BitVec.slt
-- Correctness: `Factory.bvsle_correct`
def bvsle := bvcmp .bvsle BitVec.sle
-- Correctness: `Factory.bvult_correct`
def bvult := bvcmp .bvult BitVec.ult
-- Correctness: `Factory.bvule_correct`
def bvule := bvcmp .bvule BitVec.ule

-- Correctness: `Factory.bvnego_correct`
def bvnego : Term → Term
  | .prim (@TermPrim.bitvec n b₁) => BitVec.overflows n (-b₁.toInt)
  | t                             => .app .bvnego [t] .bool

def bvso (op : Op) (fn : Int → Int → Int) (t₁ t₂ : Term) : Term :=
  match t₁, t₂ with
  | .prim (@TermPrim.bitvec n b₁), .prim (.bitvec b₂) =>
    BitVec.overflows n (fn b₁.toInt b₂.toInt)
  | _, _ => .app op [t₁, t₂] .bool

-- Correctness: `Factory.bvsaddo_correct`
def bvsaddo := bvso .bvsaddo (· + ·)
-- Correctness: `Factory.bvssubo_correct`
def bvssubo := bvso .bvssubo (· - ·)
-- Correctness: `Factory.bvsmulo_correct`
def bvsmulo := bvso .bvsmulo (· * ·)

/-
Note that BitVec defines zero_extend differently from SMTLib,
so we compensate for the difference in partial evaluation.
-/
-- Correctness: `Factory.zero_extend_correct`
def zero_extend (n : Nat) : Term → Term
  | .prim (@TermPrim.bitvec m b) =>
    BitVec.zeroExtend (n + m) b
  | t =>
    match t.typeOf with
    | .bitvec m => .app (.zero_extend n) [t] (.bitvec (n + m))
    | _         => t -- should be ruled out by callers


---------- Core ADT operators with a trusted mapping to SMT ----------

-- Correctness: `Factory.option_get_some_correct`
def option.get : Term → Term
  | .some t  => t
  | t        =>
    match t.typeOf with
    | .option ty => .app .option_get [t] ty
    | _          => t

end Factory

end Strata.SMT
end
