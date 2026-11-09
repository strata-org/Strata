/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Init
public import Std.Data.HashSet.Basic

public section
/-!
Based on Cedar's Term language.
(https://github.com/cedar-policy/cedar-spec/blob/main/cedar-lean/Cedar/SymCC/TermType.lean)
This file defines the types of Terms.  See `Term.lean` for the
definition of the Term language.
-/

namespace Strata.SMT

inductive TermPrimType where
  | bool
  | int
  | real
  | bitvec (n : Nat)
  | string
  /-- `regex`: regular expressions in the theory of unicode strings -/
  | regex
deriving instance Repr, Inhabited, Hashable for TermPrimType

-- Exposed so that importers' kernels can evaluate equality of primitive types
-- (used through `TermType.beq` by the proof-producing `gen_smt_vcs`).
@[expose] section
deriving instance DecidableEq for TermPrimType
end

def TermPrimType.mkName : TermPrimType → String
  | .bool     => "bool"
  | .int      => "int"
  | .real     => "real"
  | .bitvec _ => "bitvec"
  | .string   => "string"
  | .regex   =>  "regex"

def TermPrimType.lt : TermPrimType → TermPrimType → Bool
  | .bitvec n₁, .bitvec n₂     => n₁ < n₂
  | ty₁, ty₂                   => ty₁.mkName < ty₂.mkName

instance : LT TermPrimType where
  lt := fun x y => TermPrimType.lt x y

instance TermPrimType.decLt (x y : TermPrimType) : Decidable (x < y) :=
  if h : TermPrimType.lt x y then isTrue h else isFalse h

inductive TermType where
  | prim (pty : TermPrimType)
  -- (TODO) It looks like `option` is a special instance of `constr`.
  | option (ty : TermType)
  | constr (id : String) (args : List TermType)
deriving instance Repr, Inhabited, Hashable for TermType

/--
Induction rule for `TermType`: the default induction tactic doesn't yet support
nested or mutual induction types.
-/
@[induction_eliminator]
theorem TermType.induct {P : TermType → Prop}
  (prim : ∀pty, P (.prim pty))
  (option : ∀ty, P ty → P (.option ty))
  (constr : ∀id args, (∀ ty ∈ args, P ty) → P (.constr id args)) :
  ∀ ty, P ty := by
  intro n
  apply TermType.rec <;> try assumption
  case nil => simp
  case cons => simp_all


def TermType.mkName : TermType → String
  | .prim _   => "prim"
  | .option _ => "option"
  | .constr id _ => id

def TermType.lt : TermType → TermType → Bool
  | .prim pty₁, .prim pty₂ => pty₁ < pty₂
  | .option ty₁, .option ty₂ => TermType.lt ty₁ ty₂
  | .constr id₁ args₁, .constr id₂ args₂ => id₁ < id₂ && go args₁ args₂
  | ty₁, ty₂ => ty₁.mkName < ty₂.mkName
  where go : List TermType → List TermType → Bool
  | [], [] => true
  | [], _ | _, [] => false
  | a1 :: rst1, a2 :: rst2 => TermType.lt a1 a2 && go rst1 rst2

instance : LT TermType where
  lt := fun x y => TermType.lt x y

instance TermType.decLt (x y : TermType) : Decidable (x < y) :=
  if h : TermType.lt x y then isTrue h else isFalse h


/-- Boolean equality of types. Exposed so that importers' kernels can evaluate it. -/
@[expose] def TermType.beq : TermType → TermType → Bool
  | .prim pty₁, .prim pty₂ => pty₁ == pty₂
  | .option ty₁, .option ty₂ => TermType.beq ty₁ ty₂
  | .constr id₁ args₁, .constr id₂ args₂ => id₁ == id₂ && go args₁ args₂
  | _, _ => false
  where go : List TermType → List TermType → Bool
  | [], [] => true
  | [], _ | _, [] => false
  | a1 :: rst1, a2 :: rst2 => TermType.beq a1 a2 && go rst1 rst2

@[simp]
theorem TermType.beq_refl : TermType.beq ty ty := by
  induction ty with
  | prim p => simp only [TermType.beq, BEq.rfl]
  | option t ih => simp only [TermType.beq, ih]
  | constr id args ih =>
    simp only [TermType.beq, BEq.rfl, Bool.true_and]
    induction args with
    | nil => simp only [TermType.beq.go]
    | cons head tail ih' =>
      simp only [List.mem_cons, forall_eq_or_imp] at ih
      simp only [TermType.beq.go, Bool.and_eq_true]
      exact ⟨ih.1, ih' ih.2⟩

/-- Soundness of the boolean equality test: if `TermType.beq x y` returns `true`,
then the term types `x` and `y` are equal. -/
theorem TermType.beq_eq (x y : TermType) (h : TermType.beq x y = true) : x = y := by
  induction x generalizing y with
  | prim p =>
    cases y <;> simp only [TermType.beq, Bool.false_eq_true, beq_iff_eq] at h
    rw [h]
  | option t ih =>
    cases y <;> simp only [TermType.beq, Bool.false_eq_true] at h
    rename_i t'
    rw [ih t' h]
  | constr id args ih =>
    cases y <;> simp only [TermType.beq, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rename_i id' args'
    obtain ⟨h1, h2⟩ := h
    rw [h1]
    suffices args = args' by rw [this]
    induction args generalizing args' with
    | nil =>
      cases args' with
      | nil => rfl
      | cons _ _ => simp only [TermType.beq.go, Bool.false_eq_true] at h2
    | cons x xrest ihl =>
      cases args' with
      | nil => simp only [TermType.beq.go, Bool.false_eq_true] at h2
      | cons y yrest =>
        simp only [TermType.beq.go, Bool.and_eq_true] at h2
        simp only [List.mem_cons, forall_eq_or_imp] at ih
        rw [ih.1 y h2.1, ihl ih.2 yrest h2.2]
instance : DecidableEq TermType :=
  fun x y =>
    if h : TermType.beq x y then isTrue (TermType.beq_eq x y h)
    else isFalse (fun e => h (e ▸ TermType.beq_refl))

abbrev TermType.bool : TermType := .prim .bool
abbrev TermType.int  : TermType := .prim .int
abbrev TermType.real : TermType := .prim .real
abbrev TermType.bitvec (n : Nat) : TermType := .prim (.bitvec n)
abbrev TermType.string : TermType := .prim .string
abbrev TermType.regex : TermType := .prim .regex

def TermType.isPrimType : TermType → Bool
  | .prim _ => true
  | _       => false

def TermType.isBitVecType : TermType → Bool
  | .prim (.bitvec _) => true
  | _                 => false

def TermType.isOptionType : TermType → Bool
  | .option _ => true
  | _         => false

def TermType.isConstrType : TermType → Bool
  | .constr _ _ => true
  | _         => false

mutual
/-- Add the names of the constructed sorts in a type, including its
    arguments. -/
def TermType.addSortNames (acc : Std.HashSet String) :
    TermType → Std.HashSet String
  | .prim _ => acc
  | .option ty => TermType.addSortNames acc ty
  | .constr id args => TermType.addSortNamesList (acc.insert id) args

private def TermType.addSortNamesList (acc : Std.HashSet String) :
    List TermType → Std.HashSet String
  | [] => acc
  | ty :: tys => TermType.addSortNamesList (TermType.addSortNames acc ty) tys
end

end Strata.SMT
end

public section
-- In `Strata.DL.SMT` rather than `Strata.SMT` to avoid collision with
-- `StrataDDM.Dialect.Sort` field projection on the `Strata.SMT` dialect instance.
structure Strata.DL.SMT.Sort where
  name : String
  arity : Nat
deriving Repr, DecidableEq, Inhabited, Hashable
end
