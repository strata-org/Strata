/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.SMT.Denote

public section

/-! ## Inductive denotation predicate for ground terms

`DenotePred t v` holds when the ground (closed, quantifier-free) SMT term `t`
evaluates to the primitive value `v`. Unlike the functional denotation
`denoteTerm`, which threads contexts and environments through a
dependently-typed interpreter, `DenotePred` is a plain inductive family
`Term → TermPrim → Prop` that admits straightforward structural induction.

### Coverage

The predicate currently covers binary applications of all operators handled by
`denoteTerm`.  N-ary (left- and right-associative, chainable) applications can
be reduced to binary form; additional constructors for n-ary patterns may be
added as needed.

### Equivalence

`DenotePred.sound_bool` and `DenotePred.sound_int` relate the predicate to the
functional denotation (`denoteBoolTermAux`, `denoteIntTermAux`).
-/

open Strata.SMT

/-- Inductive predicate relating a ground SMT `Term` to the `TermPrim` it
    denotes.  Each constructor corresponds to one evaluation rule from
    `denoteTerm` restricted to the ground, quantifier-free, binary fragment. -/
inductive DenotePred : Term → TermPrim → Prop where
  -- ═══ Literals ═══
  -- Split by type (excluding `.real` which `denoteTerm` does not support).
  /-- A boolean literal. -/
  | prim_bool (b : Bool) : DenotePred (.prim (.bool b)) (.bool b)
  /-- An integer literal. -/
  | prim_int (n : Int) : DenotePred (.prim (.int n)) (.int n)
  /-- A bitvector literal. -/
  | prim_bitvec {n : Nat} (x : BitVec n) : DenotePred (.prim (.bitvec x)) (.bitvec x)
  /-- A string literal. -/
  | prim_string (s : String) : DenotePred (.prim (.string s)) (.string s)
  -- ═══ Core boolean operations ═══
  /-- Boolean negation. -/
  | not {a : Term} {b : Bool} {ty : TermType} :
      DenotePred a (.bool b) →
      DenotePred (.app .not [a] ty) (.bool (!b))
  /-- Binary conjunction. -/
  | and {a b : Term} {ba bb : Bool} {ty : TermType} :
      DenotePred a (.bool ba) → DenotePred b (.bool bb) →
      DenotePred (.app .and [a, b] ty) (.bool (ba && bb))
  /-- Binary disjunction. -/
  | or {a b : Term} {ba bb : Bool} {ty : TermType} :
      DenotePred a (.bool ba) → DenotePred b (.bool bb) →
      DenotePred (.app .or [a, b] ty) (.bool (ba || bb))
  /-- Binary implication (`=>` in SMT-LIB). -/
  | implies {a b : Term} {ba bb : Bool} {ty : TermType} :
      DenotePred a (.bool ba) → DenotePred b (.bool bb) →
      DenotePred (.app .implies [a, b] ty) (.bool ((!ba) || bb))
  /-- Equality of two same-type values (uses decidable equality on `TermPrim`). -/
  | eq {a b : Term} {va vb : TermPrim} {ty : TermType} :
      DenotePred a va → DenotePred b vb →
      va.typeOf = vb.typeOf →
      DenotePred (.app .eq [a, b] ty) (.bool (decide (va = vb)))
  /-- If-then-else, true branch (both branches must be denotable with matching types). -/
  | ite_true {c a b : Term} {ty : TermType} {v vb : TermPrim} :
      DenotePred c (.bool true) → DenotePred a v → DenotePred b vb →
      v.typeOf = vb.typeOf →
      DenotePred (.app .ite [c, a, b] ty) v
  /-- If-then-else, false branch (both branches must be denotable with matching types). -/
  | ite_false {c a b : Term} {ty : TermType} {va v : TermPrim} :
      DenotePred c (.bool false) → DenotePred a va → DenotePred b v →
      va.typeOf = v.typeOf →
      DenotePred (.app .ite [c, a, b] ty) v
  -- ═══ Integer arithmetic ═══
  /-- Integer negation. -/
  | neg_int {a : Term} {n : Int} {ty : TermType} :
      DenotePred a (.int n) →
      DenotePred (.app .neg [a] ty) (.int (-n))
  /-- Binary integer addition. -/
  | add_int {a b : Term} {na nb : Int} {ty : TermType} :
      DenotePred a (.int na) → DenotePred b (.int nb) →
      DenotePred (.app .add [a, b] ty) (.int (na + nb))
  /-- Binary integer subtraction. -/
  | sub_int {a b : Term} {na nb : Int} {ty : TermType} :
      DenotePred a (.int na) → DenotePred b (.int nb) →
      DenotePred (.app .sub [a, b] ty) (.int (na - nb))
  /-- Binary integer multiplication. -/
  | mul_int {a b : Term} {na nb : Int} {ty : TermType} :
      DenotePred a (.int na) → DenotePred b (.int nb) →
      DenotePred (.app .mul [a, b] ty) (.int (na * nb))
  /-- Binary integer division (Lean semantics: `x / 0 = 0`). -/
  | div_int {a b : Term} {na nb : Int} {ty : TermType} :
      DenotePred a (.int na) → DenotePred b (.int nb) →
      DenotePred (.app .div [a, b] ty) (.int (na / nb))
  /-- Integer modulus (Lean semantics: `x % 0 = x`). -/
  | mod_int {a b : Term} {na nb : Int} {ty : TermType} :
      DenotePred a (.int na) → DenotePred b (.int nb) →
      DenotePred (.app .mod [a, b] ty) (.int (na % nb))
  /-- Integer absolute value. -/
  | abs_int {a : Term} {n : Int} {ty : TermType} :
      DenotePred a (.int n) →
      DenotePred (.app .abs [a] ty) (.int (if n < 0 then -n else n))
  -- ═══ Integer comparisons ═══
  /-- Integer `≤`. -/
  | le_int {a b : Term} {na nb : Int} {ty : TermType} :
      DenotePred a (.int na) → DenotePred b (.int nb) →
      DenotePred (.app .le [a, b] ty) (.bool (decide (na ≤ nb)))
  /-- Integer `<`. -/
  | lt_int {a b : Term} {na nb : Int} {ty : TermType} :
      DenotePred a (.int na) → DenotePred b (.int nb) →
      DenotePred (.app .lt [a, b] ty) (.bool (decide (na < nb)))
  /-- Integer `≥`. -/
  | ge_int {a b : Term} {na nb : Int} {ty : TermType} :
      DenotePred a (.int na) → DenotePred b (.int nb) →
      DenotePred (.app .ge [a, b] ty) (.bool (decide (na ≥ nb)))
  /-- Integer `>`. -/
  | gt_int {a b : Term} {na nb : Int} {ty : TermType} :
      DenotePred a (.int na) → DenotePred b (.int nb) →
      DenotePred (.app .gt [a, b] ty) (.bool (decide (na > nb)))
  -- ═══ Bitvector arithmetic ═══
  /-- Bitvector negation. -/
  | bvneg {a : Term} {n : Nat} {x : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) →
      DenotePred (.app .bvneg [a] ty) (.bitvec (-x))
  /-- Binary bitvector addition. -/
  | bvadd {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvadd [a, b] ty) (.bitvec (x + y))
  /-- Binary bitvector subtraction. -/
  | bvsub {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvsub [a, b] ty) (.bitvec (x - y))
  /-- Binary bitvector multiplication. -/
  | bvmul {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvmul [a, b] ty) (.bitvec (x * y))
  /-- Bitvector bitwise NOT. -/
  | bvnot {a : Term} {n : Nat} {x : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) →
      DenotePred (.app .bvnot [a] ty) (.bitvec (~~~x))
  /-- Binary bitvector AND. -/
  | bvand {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvand [a, b] ty) (.bitvec (x &&& y))
  /-- Binary bitvector OR. -/
  | bvor {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvor [a, b] ty) (.bitvec (x ||| y))
  /-- Binary bitvector XOR. -/
  | bvxor {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvxor [a, b] ty) (.bitvec (x ^^^ y))
  /-- Bitvector shift left (operands may have different widths). -/
  | bvshl {a b : Term} {n m : Nat} {x : BitVec n} {y : BitVec m} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvshl [a, b] ty) (.bitvec (x <<< y))
  /-- Bitvector logical shift right (operands may have different widths). -/
  | bvlshr {a b : Term} {n m : Nat} {x : BitVec n} {y : BitVec m} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvlshr [a, b] ty) (.bitvec (x >>> y))
  /-- Bitvector arithmetic shift right (operands may have different widths). -/
  | bvashr {a b : Term} {n m : Nat} {x : BitVec n} {y : BitVec m} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvashr [a, b] ty) (.bitvec (BitVec.sshiftRight' x y))
  -- ═══ Bitvector comparisons (same width) ═══
  /-- Bitvector signed `<`. -/
  | bvslt {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvslt [a, b] ty) (.bool (BitVec.slt x y))
  /-- Bitvector signed `≤`. -/
  | bvsle {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvsle [a, b] ty) (.bool (BitVec.sle x y))
  /-- Bitvector unsigned `<`. -/
  | bvult {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvult [a, b] ty) (.bool (decide (x < y)))
  /-- Bitvector unsigned `≤`. -/
  | bvule {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvule [a, b] ty) (.bool (decide (x ≤ y)))
  /-- Bitvector signed `>`. -/
  | bvsgt {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvsgt [a, b] ty) (.bool (BitVec.slt y x))
  /-- Bitvector signed `≥`. -/
  | bvsge {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvsge [a, b] ty) (.bool (BitVec.sle y x))
  /-- Bitvector unsigned `>`. -/
  | bvugt {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvugt [a, b] ty) (.bool (decide (x > y)))
  /-- Bitvector unsigned `≥`. -/
  | bvuge {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvuge [a, b] ty) (.bool (decide (x ≥ y)))
  -- ═══ Bitvector division / remainder ═══
  /-- Bitvector unsigned division (same width, SMT-LIB semantics). -/
  | bvudiv {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvudiv [a, b] ty) (.bitvec (BitVec.smtUDiv x y))
  /-- Bitvector unsigned remainder (same width). -/
  | bvurem {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvurem [a, b] ty) (.bitvec (x % y))
  /-- Bitvector signed division (same width, SMT-LIB semantics). -/
  | bvsdiv {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvsdiv [a, b] ty) (.bitvec (BitVec.smtSDiv x y))
  /-- Bitvector signed remainder (same width). -/
  | bvsrem {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvsrem [a, b] ty) (.bitvec (BitVec.srem x y))
  -- ═══ Bitvector overflow predicates ═══
  /-- Bitvector negation overflow. -/
  | bvnego {a : Term} {n : Nat} {x : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) →
      DenotePred (.app .bvnego [a] ty) (.bool (BitVec.negOverflow x))
  /-- Bitvector signed addition overflow (same width). -/
  | bvsaddo {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvsaddo [a, b] ty) (.bool (BitVec.saddOverflow x y))
  /-- Bitvector signed subtraction overflow (same width). -/
  | bvssubo {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvssubo [a, b] ty) (.bool (BitVec.ssubOverflow x y))
  /-- Bitvector signed multiplication overflow (same width). -/
  | bvsmulo {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvsmulo [a, b] ty) (.bool (BitVec.smulOverflow x y))
  -- ═══ Bitvector concatenation and extension ═══
  /-- Bitvector concatenation. -/
  | bvconcat {a b : Term} {n m : Nat} {x : BitVec n} {y : BitVec m} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvconcat [a, b] ty) (.bitvec (x ++ y))
  /-- Bitvector zero extension by `i` bits. -/
  | zero_extend {a : Term} {n : Nat} {x : BitVec n} {ty : TermType} (i : Nat) :
      DenotePred a (.bitvec x) →
      DenotePred (.app (.zero_extend i) [a] ty) (.bitvec (BitVec.zeroExtend (n + i) x))
  -- ═══ String operations ═══
  /-- String length (result is a non-negative integer). -/
  | str_length {s : Term} {sv : String} {ty : TermType} :
      DenotePred s (.string sv) →
      DenotePred (.app .str_length [s] ty) (.int (Int.ofNat sv.length))
  /-- Binary string concatenation. -/
  | str_concat {a b : Term} {sa sb : String} {ty : TermType} :
      DenotePred a (.string sa) → DenotePred b (.string sb) →
      DenotePred (.app .str_concat [a, b] ty) (.string (sa ++ sb))

/-! ### DenotePred determinism -/

/-- `DenotePred` is deterministic: a term has at most one denotation. -/
theorem DenotePred.deterministic {t : Term} {v₁ v₂ : TermPrim}
    (h₁ : DenotePred t v₁) (h₂ : DenotePred t v₂) : v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  -- Literals
  | prim_bool | prim_int | prim_bitvec | prim_string => cases h₂; rfl
  -- ITE requires ruling out the opposite branch
  | ite_true _ _ _ _ ihc iha _ =>
    cases h₂ with
    | ite_true _ ha' _ _ => exact iha ha'
    | ite_false hc' _ _ _ => exact absurd (ihc hc') (by simp)
  | ite_false _ _ _ _ ihc _ ihb =>
    cases h₂ with
    | ite_true hc' _ _ _ => exact absurd (ihc hc') (by simp)
    | ite_false _ _ hb' _ => exact ihb hb'
  -- Unary bitvector ops (need `cases` for heterogeneous width equality)
  | bvneg _ ih | bvnot _ ih | bvnego _ ih =>
    cases h₂; have h := ih ‹_›; cases h; rfl
  -- Binary bitvector ops
  | bvadd _ _ iha ihb | bvsub _ _ iha ihb | bvmul _ _ iha ihb
  | bvand _ _ iha ihb | bvor _ _ iha ihb | bvxor _ _ iha ihb
  | bvshl _ _ iha ihb | bvlshr _ _ iha ihb | bvashr _ _ iha ihb
  | bvslt _ _ iha ihb | bvsle _ _ iha ihb | bvult _ _ iha ihb | bvule _ _ iha ihb
  | bvsgt _ _ iha ihb | bvsge _ _ iha ihb | bvugt _ _ iha ihb | bvuge _ _ iha ihb
  | bvudiv _ _ iha ihb | bvurem _ _ iha ihb | bvsdiv _ _ iha ihb | bvsrem _ _ iha ihb
  | bvsaddo _ _ iha ihb | bvssubo _ _ iha ihb | bvsmulo _ _ iha ihb
  | bvconcat _ _ iha ihb =>
    cases h₂; have h1 := iha ‹_›; have h2 := ihb ‹_›; cases h1; cases h2; rfl
  -- zero_extend: unary with extra Nat parameter
  | zero_extend _ _ iha => cases h₂; have := iha ‹_›; cases this; rfl
  -- All remaining (boolean/int/string ops): apply IHs then close with simp_all
  | not _ ih | neg_int _ ih | abs_int _ ih | str_length _ ih =>
    cases h₂; have := ih ‹_›; simp_all
  | _ =>
    rename_i iha ihb; cases h₂; have := iha ‹_›; have := ihb ‹_›; simp_all
/-! ### Soundness proof infrastructure -/

/-- The unique `TermDenoteInput` for the empty context. -/
private noncomputable abbrev tdi₀ : TermDenoteInput ({} : Context) :=
  ⟨[], ⟨rfl, fun _ hi => nomatch hi⟩, ⟨[], []⟩,
   ⟨⟨rfl, fun _ hi => nomatch hi⟩, ⟨rfl, fun _ hi => nomatch hi⟩⟩⟩

/-- Soundness goal for each `TermPrim` variant.  Tracks the `denoteTerm`
    result so that the induction hypothesis is usable across type boundaries
    (e.g. integer sub-terms inside boolean comparisons). -/
private noncomputable def DenotePred.SoundGoal (t : Term) : TermPrim → Prop
  | .bool b         => ∃ f : TermDenoteInput ({} : Context) → Prop,
                          denoteTerm ({} : Context) t = some ⟨.prim .bool, rfl, f⟩ ∧ (f tdi₀ ↔ b = true)
  | .int n          => ∃ f : TermDenoteInput ({} : Context) → Int,
                          denoteTerm ({} : Context) t = some ⟨.prim .int, rfl, f⟩ ∧ f tdi₀ = n
  | @TermPrim.bitvec k x => ∃ f : TermDenoteInput ({} : Context) → BitVec k,
                          denoteTerm ({} : Context) t = some ⟨.prim (.bitvec k), rfl, f⟩ ∧ f tdi₀ = x
  | .string s       => ∃ f : TermDenoteInput ({} : Context) → String,
                          denoteTerm ({} : Context) t = some ⟨.prim .string, rfl, f⟩ ∧ f tdi₀ = s
  | .real _         => True

/-- No `DenotePred` derivation produces a `.real` value (reals are unsupported by `denoteTerm`). -/
private theorem DenotePred.not_real {t : Term} {v : TermPrim} (h : DenotePred t v) :
    ∀ d : Strata.Decimal, v = .real d → False := by
  induction h <;> intro d heq <;> simp_all [TermPrim.typeOf]

/-! ### Core soundness lemma -/

private theorem DenotePred.sound_aux {t : Term} {v : TermPrim} (h : DenotePred t v) :
    DenotePred.SoundGoal t v := by
  induction h with
  -- ═══ Literals ═══
  | prim_bool b =>
    unfold SoundGoal; cases b
    all_goals exact ⟨_, by unfold denoteTerm; rfl, by simp⟩
  | prim_int n => exact ⟨_, by unfold denoteTerm; rfl, rfl⟩
  | prim_bitvec x => exact ⟨_, by unfold denoteTerm; rfl, rfl⟩
  | prim_string s => exact ⟨_, by unfold denoteTerm; rfl, rfl⟩
  -- ═══ Core boolean operations ═══
  | @not _ b _ _ ih =>
    obtain ⟨f, hdt, hiff⟩ := ih
    refine ⟨fun Γ => ¬f Γ, by unfold denoteTerm; rw [hdt]; first | rfl | simp, ?_⟩
    cases b <;> simp_all
  | @and _ _ ba bb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hiffa⟩ := iha; obtain ⟨fb, hdtb, hiffb⟩ := ihb
    refine ⟨fun Γ => fa Γ ∧ fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp, ?_⟩
    constructor
    · rintro ⟨ha, hb⟩; rw [Bool.and_eq_true]; exact ⟨hiffa.mp ha, hiffb.mp hb⟩
    · intro h; rw [Bool.and_eq_true] at h; exact ⟨hiffa.mpr h.1, hiffb.mpr h.2⟩
  | @or _ _ ba bb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hiffa⟩ := iha; obtain ⟨fb, hdtb, hiffb⟩ := ihb
    refine ⟨fun Γ => fa Γ ∨ fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp, ?_⟩
    constructor
    · rintro (ha | hb)
      · rw [Bool.or_eq_true]; exact Or.inl (hiffa.mp ha)
      · rw [Bool.or_eq_true]; exact Or.inr (hiffb.mp hb)
    · intro h; rw [Bool.or_eq_true] at h; exact h.elim (Or.inl ∘ hiffa.mpr) (Or.inr ∘ hiffb.mpr)
  | @implies _ _ ba bb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hiffa⟩ := iha; obtain ⟨fb, hdtb, hiffb⟩ := ihb
    refine ⟨fun Γ => fa Γ → fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms rightAssoc rightAssoc.go; rw [hdta, hdtb]; first | rfl | simp, ?_⟩
    cases ba <;> cases bb <;> simp_all
  | @eq _ _ va vb _ ha _ htyeq iha ihb =>
    cases va with
    | real d => exact absurd rfl (DenotePred.not_real ha d)
    | bool ba =>
      cases vb with
      | real _ => simp [TermPrim.typeOf] at htyeq
      | bool bb =>
        obtain ⟨fa, hdta, hiffa⟩ := iha; obtain ⟨fb, hdtb, hiffb⟩ := ihb
        refine ⟨fun Γ => fa Γ ↔ fb Γ,
          by unfold denoteTerm denoteTerms denoteTerms denoteTerms chainable chainable.go
             simp only [hdta, hdtb, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                        dite_true]
             congr; funext x; apply propext; exact eq_iff_iff, ?_⟩
        simp only [decide_eq_true_eq]
        cases ba <;> cases bb <;> simp_all
      | int _ => simp [TermPrim.typeOf] at htyeq
      | bitvec _ => simp [TermPrim.typeOf] at htyeq
      | string _ => simp [TermPrim.typeOf] at htyeq
    | int na =>
      cases vb with
      | real _ => simp [TermPrim.typeOf] at htyeq
      | int nb =>
        obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
        refine ⟨fun Γ => fa Γ = fb Γ, ?_, ?_⟩
        · unfold denoteTerm denoteTerms denoteTerms denoteTerms chainable chainable.go
          simp only [hdta, hdtb, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                     dite_true]
          congr; funext
        · simp [hvala, hvalb, decide_eq_true_eq]
      | bool _ => simp [TermPrim.typeOf] at htyeq
      | bitvec _ => simp [TermPrim.typeOf] at htyeq
      | string _ => simp [TermPrim.typeOf] at htyeq
    | @bitvec ka xa =>
      cases vb with
      | real _ => simp [TermPrim.typeOf] at htyeq
      | @bitvec kb xb =>
        have hkk : ka = kb := by
          simp only [TermPrim.typeOf, TermType.bitvec] at htyeq
          injection htyeq with h; injection h
        subst hkk
        obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
        refine ⟨fun Γ => fa Γ = fb Γ, ?_, ?_⟩
        · unfold denoteTerm denoteTerms denoteTerms denoteTerms chainable chainable.go
          simp only [hdta, hdtb, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                     dite_true]
          congr; funext
        · simp [hvala, hvalb, decide_eq_true_eq]
      | bool _ => simp [TermPrim.typeOf] at htyeq
      | int _ => simp [TermPrim.typeOf] at htyeq
      | string _ => simp [TermPrim.typeOf] at htyeq
    | string sa =>
      cases vb with
      | string sb =>
        obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
        refine ⟨fun Γ => fa Γ = fb Γ, ?_, ?_⟩
        · unfold denoteTerm denoteTerms denoteTerms denoteTerms chainable chainable.go
          simp only [hdta, hdtb, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                     dite_true]
          congr; funext
        · simp [hvala, hvalb, decide_eq_true_eq]
      | real _ => simp [TermPrim.typeOf] at htyeq
      | bool _ => simp [TermPrim.typeOf] at htyeq
      | int _ => simp [TermPrim.typeOf] at htyeq
      | bitvec _ => simp [TermPrim.typeOf] at htyeq
  | @ite_true _ _ _ _ v vb _ _ _ htyeq ihc iha ihb =>
    obtain ⟨fc, hdtc, hiffc⟩ := ihc
    have hcpos : fc tdi₀ := hiffc.mpr rfl
    cases v with
    | real _ => trivial
    | @bitvec k x =>
      cases vb with
      | @bitvec k' _ =>
        have hk : k = k' := by simp [TermPrim.typeOf] at htyeq; exact htyeq
        subst hk
        obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, _⟩ := ihb
        refine ⟨fun Γ => @ite _ (fc Γ) (Classical.propDecidable (fc Γ)) (fa Γ) (fb Γ), ?_, ?_⟩
        · unfold denoteTerm
          simp only [hdtc, hdta, hdtb, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                     dite_true]
          congr; funext
        · simp [if_pos hcpos]; exact hvala
      | _ => simp [TermPrim.typeOf] at htyeq
    | bool _ | int _ | string _ =>
      cases vb <;> try (simp [TermPrim.typeOf] at htyeq)
      obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, _⟩ := ihb
      refine ⟨fun Γ => @ite _ (fc Γ) (Classical.propDecidable (fc Γ)) (fa Γ) (fb Γ), ?_, ?_⟩
      · unfold denoteTerm
        simp only [hdtc, hdta, hdtb, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                   dite_true]
        congr; funext
      · simp only [if_pos hcpos]; exact hvala
  | @ite_false _ _ _ _ va v _ _ _ htyeq ihc iha ihb =>
    obtain ⟨fc, hdtc, hiffc⟩ := ihc
    have hcneg : ¬fc tdi₀ := fun h => by simp at hiffc; exact hiffc h
    cases v with
    | real _ => trivial
    | @bitvec k x =>
      cases va with
      | @bitvec k' _ =>
        have hk : k' = k := by simp [TermPrim.typeOf] at htyeq; exact htyeq
        subst hk
        obtain ⟨fa, hdta, _⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
        refine ⟨fun Γ => @ite _ (fc Γ) (Classical.propDecidable (fc Γ)) (fa Γ) (fb Γ), ?_, ?_⟩
        · unfold denoteTerm
          simp only [hdtc, hdta, hdtb, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                     dite_true]
          congr; funext
        · simp [if_neg hcneg]; exact hvalb
      | _ => simp [TermPrim.typeOf] at htyeq
    | bool _ | int _ | string _ =>
      cases va <;> try (simp [TermPrim.typeOf] at htyeq)
      obtain ⟨fa, hdta, _⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
      refine ⟨fun Γ => @ite _ (fc Γ) (Classical.propDecidable (fc Γ)) (fa Γ) (fb Γ), ?_, ?_⟩
      · unfold denoteTerm
        simp only [hdtc, hdta, hdtb, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                   dite_true]
        congr; funext
      · simp only [if_neg hcneg]; exact hvalb
  -- ═══ Integer arithmetic ═══
  | @neg_int _ n _ _ ih =>
    obtain ⟨f, hdt, hval⟩ := ih
    exact ⟨fun Γ => -f Γ, by unfold denoteTerm; rw [hdt]; first | rfl | simp, by simp [hval]⟩
  | @add_int _ _ na nb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ + fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @sub_int _ _ na nb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ - fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @mul_int _ _ na nb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ * fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @div_int _ _ na nb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ / fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @mod_int _ _ na nb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ % fb Γ, by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp, by simp [hvala, hvalb]⟩
  | @abs_int _ n _ _ ih =>
    obtain ⟨f, hdt, hval⟩ := ih
    exact ⟨fun Γ => if f Γ < 0 then -f Γ else f Γ, by unfold denoteTerm; rw [hdt]; first | rfl | simp, by simp [hval]⟩
  -- ═══ Integer comparisons ═══
  | @le_int _ _ na nb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ ≤ fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms chainable chainable.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb, decide_eq_true_eq]⟩
  | @lt_int _ _ na nb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ < fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms chainable chainable.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb, decide_eq_true_eq]⟩
  | @ge_int _ _ na nb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ ≥ fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms chainable chainable.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb, decide_eq_true_eq]⟩
  | @gt_int _ _ na nb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ > fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms chainable chainable.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb, decide_eq_true_eq]⟩
  -- ═══ Bitvector arithmetic ═══
  | @bvneg _ n x _ _ ih =>
    obtain ⟨f, hdt, hval⟩ := ih
    exact ⟨fun Γ => -f Γ, by unfold denoteTerm; rw [hdt]; first | rfl | simp, by simp [hval]⟩
  | @bvadd _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ + fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; simp,
      by simp [hvala, hvalb]⟩
  | @bvsub _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ - fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvmul _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ * fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvnot _ n x _ _ ih =>
    obtain ⟨f, hdt, hval⟩ := ih
    exact ⟨fun Γ => ~~~f Γ, by unfold denoteTerm; rw [hdt]; first | rfl | simp, by simp [hval]⟩
  | @bvand _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ &&& fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvor _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ ||| fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvxor _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ ^^^ fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvshl _ _ n m x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ <<< fb Γ, by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp, by simp [hvala, hvalb]⟩
  | @bvlshr _ _ n m x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ >>> fb Γ, by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp, by simp [hvala, hvalb]⟩
  | @bvashr _ _ n m x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => BitVec.sshiftRight' (fa Γ) (fb Γ), by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  -- ═══ Bitvector comparisons ═══
  | @bvslt _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => BitVec.slt (fa Γ) (fb Γ) = true,
      by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvsle _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => BitVec.sle (fa Γ) (fb Γ) = true,
      by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvult _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ < fb Γ,
      by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb, decide_eq_true_eq]⟩
  | @bvule _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ ≤ fb Γ,
      by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb, decide_eq_true_eq]⟩
  | @bvsgt _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => BitVec.slt (fb Γ) (fa Γ) = true,
      by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvsge _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => BitVec.sle (fb Γ) (fa Γ) = true,
      by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvugt _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ > fb Γ,
      by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb, decide_eq_true_eq]⟩
  | @bvuge _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ ≥ fb Γ,
      by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb, decide_eq_true_eq]⟩
  -- ═══ Bitvector division / remainder ═══
  | @bvudiv _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => BitVec.smtUDiv (fa Γ) (fb Γ), by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvurem _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ % fb Γ, by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp, by simp [hvala, hvalb]⟩
  | @bvsdiv _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => BitVec.smtSDiv (fa Γ) (fb Γ), by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvsrem _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => BitVec.srem (fa Γ) (fb Γ), by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  -- ═══ Bitvector overflow predicates ═══
  | @bvnego _ n x _ _ ih =>
    obtain ⟨f, hdt, hval⟩ := ih
    exact ⟨fun Γ => BitVec.negOverflow (f Γ) = true, by unfold denoteTerm; rw [hdt]; first | rfl | simp,
      by simp [hval]⟩
  | @bvsaddo _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => BitVec.saddOverflow (fa Γ) (fb Γ) = true, by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvssubo _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => BitVec.ssubOverflow (fa Γ) (fb Γ) = true, by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvsmulo _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => BitVec.smulOverflow (fa Γ) (fb Γ) = true, by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  -- ═══ Bitvector concatenation and extension ═══
  | @bvconcat _ _ n m x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ ++ fb Γ, by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp, by simp [hvala, hvalb]⟩
  | @zero_extend _ n x _ i _ ih =>
    obtain ⟨f, hdt, hval⟩ := ih
    exact ⟨fun Γ => BitVec.zeroExtend (n + i) (f Γ), by unfold denoteTerm; rw [hdt]; first | rfl | simp, by simp [hval]⟩
  -- ═══ String operations ═══
  | @str_length _ sv _ _ ih =>
    obtain ⟨f, hdt, hval⟩ := ih
    exact ⟨fun Γ => Int.ofNat (f Γ).length, by unfold denoteTerm; rw [hdt]; first | rfl | simp, by simp [hval]⟩
  | @str_concat _ _ sa sb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ ++ fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩

/-! ### Soundness theorems

These theorems state that `DenotePred t v` implies that the functional
denotation (`denoteBoolTermAux`, `denoteIntTermAux`, `denoteBVTermAux`,
`denoteStringTermAux`) succeeds with a consistent result.  The boolean case
bridges the `Bool`/`Prop` gap: `denoteTerm` maps booleans to `Prop`
(`True`/`False`), while `DenotePred` stays in `Bool`.
-/

/-- Soundness for boolean results: if `DenotePred t (.bool b)` holds, then
    `denoteBoolTermAux` succeeds with a proposition logically equivalent
    to `b = true`. -/
theorem DenotePred.sound_bool {t : Term} {b : Bool}
    (h : DenotePred t (.bool b)) :
    ∃ p, denoteBoolTermAux t = some p ∧ (p ↔ b = true) := by
  obtain ⟨f, hdt, hiff⟩ := DenotePred.sound_aux h
  exact ⟨f tdi₀, by simp [denoteBoolTermAux, hdt], hiff⟩

/-- Soundness for integer results: if `DenotePred t (.int n)` holds, then
    `denoteIntTermAux` succeeds with value `n`. -/
theorem DenotePred.sound_int {t : Term} {n : Int}
    (h : DenotePred t (.int n)) :
    denoteIntTermAux t = some n := by
  obtain ⟨f, hdt, hval⟩ := DenotePred.sound_aux h
  simp [denoteIntTermAux, hdt, hval]

/-- Soundness for bitvector results: if `DenotePred t (.bitvec x)` holds, then
    `denoteBVTermAux` succeeds with value `x`. -/
theorem DenotePred.sound_bitvec {t : Term} {n : Nat} {x : BitVec n}
    (h : DenotePred t (.bitvec x)) :
    denoteBVTermAux n t = some x := by
  obtain ⟨f, hdt, hval⟩ := DenotePred.sound_aux h
  simp [denoteBVTermAux, hdt, hval]

/-- Soundness for string results: if `DenotePred t (.string s)` holds, then
    `denoteStringTermAux` succeeds with value `s`. -/
theorem DenotePred.sound_string {t : Term} {s : String}
    (h : DenotePred t (.string s)) :
    denoteStringTermAux t = some s := by
  obtain ⟨f, hdt, hval⟩ := DenotePred.sound_aux h
  simp [denoteStringTermAux, hdt, hval]

