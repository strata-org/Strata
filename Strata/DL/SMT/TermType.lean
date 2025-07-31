/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

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
deriving instance Repr, Inhabited, DecidableEq for TermPrimType

def TermPrimType.mkName : TermPrimType → String
  | .bool     => "bool"
  | .int      => "int"
  | .real     => "real"
  | .bitvec _ => "bitvec"
  | .string   => "string"

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
deriving instance Repr, Inhabited for TermType

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

instance : Hashable TermType where
  hash := λ a => hash s!"{repr a}"

def TermType.beq : TermType → TermType → Bool
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
  induction ty <;> simp_all [TermType.beq]
  rename_i name args ih
  induction args
  case constr.nil => simp [TermType.beq.go]
  case constr.cons =>
    rename_i head tail ih'
    simp_all [TermType.beq.go]
  done

-- (FIXME) Golf.
instance : DecidableEq TermType :=
  fun x y =>
    if h: TermType.beq x y then
      isTrue (by
                induction x generalizing y
                case prim =>
                  unfold TermType.beq at h <;> split at h <;> simp_all
                case option =>
                  unfold TermType.beq at h <;> split at h <;> simp_all
                  rename_i _ _ _ _ ty2 h1 _
                  exact h1 ty2 h
                case constr =>
                  rename_i id args ih
                  cases y <;> try simp_all [TermType.beq]
                  rename_i id' args'
                  obtain ⟨h1, h2⟩ := h
                  induction args generalizing args' <;> simp_all
                  case constr.intro.nil =>
                    unfold TermType.beq.go at h2
                    split at h2 <;> simp_all
                  case constr.intro.cons head tail tail_ih =>
                    unfold TermType.beq.go at h2; split at h2 <;> simp_all
                    obtain ⟨h2_1, h2_2⟩ := h2
                    obtain ⟨ih1, ih2⟩ := ih
                    rename_i _ _ _ _ a2 rst2 _
                    exact ⟨ih1 a2 h2_1, tail_ih ih2 rst2 h2_2⟩)
    else
      isFalse (by
                induction x generalizing y
                case prim =>
                  unfold TermType.beq at h; split at h <;> simp_all
                  rename_i pty _ _ _ h
                  exact fun a => h pty pty rfl (id (Eq.symm a))
                case option =>
                  unfold TermType.beq at h <;> split at h <;> simp_all
                  rename_i ty _ _ _ _ h2
                  exact fun a => h2 ty ty rfl (id (Eq.symm a))
                case constr =>
                  rename_i id args ih
                  cases y <;> try simp_all [TermType.beq]
                  rename_i id' args'
                  induction args generalizing args' <;> simp_all
                  case constr.nil =>
                    unfold TermType.beq.go at h
                    split at h <;> simp_all
                  case constr.cons head tail tail_ih =>
                    intro h1; subst id'; simp_all
                    obtain ⟨ih1, ih2⟩ := ih
                    cases args' <;> simp_all
                    rename_i head1 tail1; intro h_head; subst head1
                    have tail_ih' := @tail_ih tail1
                    unfold TermType.beq.go at h
                    simp at h; exact tail_ih tail1 h)

abbrev TermType.bool : TermType := .prim .bool
abbrev TermType.int  : TermType := .prim .int
abbrev TermType.real : TermType := .prim .real
abbrev TermType.bitvec (n : Nat) : TermType := .prim (.bitvec n)
abbrev TermType.string : TermType := .prim .string

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

end Strata.SMT
