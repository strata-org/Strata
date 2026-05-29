/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Analysis.Productivity
public import Std.Data.HashSet.Lemmas

/-!
# Productivity spec

`Productive` is the inductive spec; `runFixpoint` computes it.  Kernel
theorems are parametric in the seed; `runFixpoint_strict_correct`
specialises to the strict mode where the seed is
`frameworkAtomicCategories`.
-/

public section

namespace Strata.DDM.Productivity

/-! ## Spec -/

/--
Inductive specification of productivity over a flat operator pool.

`OpInfo` is the productivity-relevant skeleton of an operator
declaration: its result category and the categories of its arguments,
flattened by `opInfoOfDecl`.  `extractOps` produces these from a
`Dialect` and `extractOpsClosure` from a target dialect plus its
import closure.

`Productive ops base C` says category `C` admits a finite derivation
tree using operators from `ops`, with leaves drawn from `base`
(typically `frameworkAtomicCategories` — the categories the parser
constructs directly).
-/
inductive Productive (ops : Array OpInfo) (base : QualifiedIdent → Prop)
    : QualifiedIdent → Prop where
  | byBase : ∀ {C}, base C → Productive ops base C
  | byOp : ∀ (op : OpInfo),
      op ∈ ops →
      (∀ a ∈ op.args, Productive ops base a) →
      Productive ops base op.result

/-! ## Soundness -/

theorem step_preserves_productive
    {ops : Array OpInfo} {base : QualifiedIdent → Prop}
    {productive : Std.HashSet QualifiedIdent}
    (h : ∀ c, c ∈ productive → Productive ops base c) :
    ∀ c, c ∈ step ops productive → Productive ops base c := by
  intro c hc
  rw [step_eq] at hc
  refine Array.foldl_induction
    (motive := fun _ acc => ∀ c, c ∈ acc → Productive ops base c)
    h ?_ c hc
  intro i acc accInv c hc
  by_cases hall : (ops[i].args.all acc.contains) = true
  · simp only [hall, if_true] at hc
    rw [Std.HashSet.mem_insert] at hc
    rcases hc with heq | hold
    · have : ops[i].result = c := by simpa using heq
      subst this
      have argsProd : ∀ a ∈ ops[i].args, Productive ops base a := fun a haIn =>
        accInv a (Std.HashSet.mem_iff_contains.mpr ((Array.all_eq_true'.mp hall) a haIn))
      exact Productive.byOp ops[i] (Array.getElem_mem i.isLt) argsProd
    · exact accInv c hold
  · simp only [hall] at hc
    exact accInv c hc

theorem iterate_preserves_productive
    (ops : Array OpInfo) (base : QualifiedIdent → Prop) :
    ∀ (n : Nat) (s : Std.HashSet QualifiedIdent),
      (∀ c, c ∈ s → Productive ops base c) →
      ∀ c, c ∈ iterate ops s n → Productive ops base c
  | 0, _, hs => fun c hc => by rw [iterate_zero] at hc; exact hs c hc
  | n + 1, s, hs => by
    intro c hc
    rw [iterate_succ] at hc
    by_cases hsame : ((step ops s).size == s.size) = true
    · simp only [hsame, if_true] at hc; exact hs c hc
    · simp only [hsame] at hc
      exact iterate_preserves_productive ops base n (step ops s)
        (step_preserves_productive hs) c hc

theorem runFixpoint_sound
    (ops : Array OpInfo) (trusted : Std.HashSet QualifiedIdent)
    (baseSpec : QualifiedIdent → Prop)
    (h0 : ∀ c, c ∈ trusted → baseSpec c) :
    ∀ c, c ∈ runFixpoint trusted ops → Productive ops baseSpec c :=
  iterate_preserves_productive ops baseSpec (ops.size + 1) trusted
    (fun c hMem => Productive.byBase (h0 c hMem))

/-! ## Monotonicity -/

theorem step_mono
    (ops : Array OpInfo) (s : Std.HashSet QualifiedIdent) :
    ∀ c, c ∈ s → c ∈ step ops s := by
  intro c hc
  rw [step_eq]
  refine Array.foldl_induction
    (motive := fun _ acc => c ∈ acc) hc ?_
  intro i acc accMem
  by_cases hall : (ops[i].args.all acc.contains) = true
  · simp only [hall, if_true]; exact Std.HashSet.mem_insert.mpr (Or.inr accMem)
  · simp only [hall]; exact accMem

theorem iterate_mono (ops : Array OpInfo) :
    ∀ (n : Nat) (s : Std.HashSet QualifiedIdent) (c : QualifiedIdent),
      c ∈ s → c ∈ iterate ops s n
  | 0, _, _, hc => by rw [iterate_zero]; exact hc
  | n + 1, s, c, hc => by
    rw [iterate_succ]
    by_cases hsame : ((step ops s).size == s.size) = true
    · simp only [hsame, if_true]; exact hc
    · simp only [hsame]
      exact iterate_mono ops n (step ops s) c (step_mono ops s c hc)

/-- Args of `op` in `s` ⇒ `op.result ∈ step ops s`. -/
theorem step_grows
    (ops : Array OpInfo) (s : Std.HashSet QualifiedIdent)
    (op : OpInfo) (hOp : op ∈ ops)
    (hArgs : ∀ a ∈ op.args, a ∈ s) :
    op.result ∈ step ops s := by
  rw [step_eq]
  obtain ⟨i, hi_lt, hi⟩ := Array.getElem_of_mem hOp
  have key := Array.foldl_induction
    (as := ops) (init := s)
    (f := fun acc op' =>
      if op'.args.all acc.contains then acc.insert op'.result else acc)
    (motive := fun j acc =>
      (∀ a ∈ op.args, a ∈ acc) ∧ (j > i → op.result ∈ acc))
    ⟨hArgs, fun h => absurd h (Nat.not_lt_zero _)⟩
    (by
      intro j acc ⟨accArgs, accAfter⟩
      refine ⟨?_, ?_⟩
      · intro a haIn
        by_cases hall : (ops[j].args.all acc.contains) = true
        · simp only [hall, if_true]
          exact Std.HashSet.mem_insert.mpr (Or.inr (accArgs a haIn))
        · simp only [hall]; exact accArgs a haIn
      · intro hgt
        by_cases hjeq : j.val = i
        · have hopEq : ops[j] = op := by
            have : ops[j.val]'j.isLt = ops[i]'hi_lt := by simp [hjeq]
            rw [show ops[j] = ops[j.val]'j.isLt from rfl, this, hi]
          have hallArgs : ops[j].args.all acc.contains = true := by
            rw [hopEq]
            exact Array.all_eq_true'.mpr fun a haIn =>
              Std.HashSet.mem_iff_contains.mp (accArgs a haIn)
          simp only [hallArgs, if_true]
          have hresEq : ops[j].result = op.result := by rw [hopEq]
          rw [hresEq]
          exact Std.HashSet.mem_insert_self
        · have hjgt : j.val > i := by have : j.val + 1 > i := hgt; omega
          have prev : op.result ∈ acc := accAfter hjgt
          by_cases hall : (ops[j].args.all acc.contains) = true
          · simp only [hall, if_true]
            exact Std.HashSet.mem_insert.mpr (Or.inr prev)
          · simp only [hall]; exact prev)
  exact key.2 hi_lt

/-! ## Size bookkeeping -/

theorem step_size_mono (ops : Array OpInfo) (s : Std.HashSet QualifiedIdent) :
    s.size ≤ (step ops s).size := by
  rw [step_eq]
  refine Array.foldl_induction
    (motive := fun _ acc => s.size ≤ Std.HashSet.size acc) (Nat.le_refl _) ?_
  intro i acc accLe
  by_cases hall : (ops[i].args.all acc.contains) = true
  · simp only [hall, if_true]
    exact Nat.le_trans accLe Std.HashSet.size_le_size_insert
  · simp only [hall]; exact accLe

/-- `step` preserves size ⇒ preserves membership. -/
theorem step_size_eq_implies_mem_eq
    (ops : Array OpInfo) (s : Std.HashSet QualifiedIdent)
    (heq : (step ops s).size = s.size) :
    ∀ c, c ∈ step ops s → c ∈ s := by
  have key :
      (Std.HashSet.size (step ops s) = s.size
        ∧ ∀ c, c ∈ step ops s → c ∈ s)
      ∨ Std.HashSet.size (step ops s) > s.size := by
    rw [step_eq]
    refine Array.foldl_induction
      (motive := fun _ acc =>
        (Std.HashSet.size acc = s.size ∧ ∀ c, c ∈ acc → c ∈ s)
        ∨ Std.HashSet.size acc > s.size)
      (Or.inl ⟨rfl, fun _ h => h⟩) ?_
    intro i acc accInv
    by_cases hall : (ops[i].args.all acc.contains) = true
    · simp only [hall, if_true]
      by_cases hin : ops[i].result ∈ acc
      · rcases accInv with ⟨hsz, hmem⟩ | hgt
        · refine Or.inl ⟨?_, ?_⟩
          · rw [Std.HashSet.size_insert, if_pos hin]; exact hsz
          · intro c hc
            rw [Std.HashSet.mem_insert] at hc
            rcases hc with heq2 | hold
            · have : ops[i].result = c := by simpa using heq2
              subst this; exact hmem _ hin
            · exact hmem _ hold
        · right; rw [Std.HashSet.size_insert, if_pos hin]; exact hgt
      · right
        rw [Std.HashSet.size_insert, if_neg hin]
        rcases accInv with ⟨hsz, _⟩ | hgt
        · rw [hsz]; exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt hgt
    · simp only [hall]; exact accInv
  rcases key with ⟨_, hmem⟩ | hgt
  · exact hmem
  · exfalso; exact Nat.lt_irrefl _ (heq ▸ hgt)

/-! ## Bounding the iterated set -/

theorem step_mem_origin (ops : Array OpInfo) (s : Std.HashSet QualifiedIdent) :
    ∀ c, c ∈ step ops s → c ∈ s ∨ ∃ op ∈ ops, op.result = c := by
  rw [step_eq]
  intro c
  refine Array.foldl_induction
    (motive := fun _ acc =>
      c ∈ acc → c ∈ s ∨ ∃ op ∈ ops, op.result = c)
    (fun h => Or.inl h) ?_
  intro i acc accInv hMem
  by_cases hall : (ops[i].args.all acc.contains) = true
  · simp only [hall, if_true] at hMem
    rw [Std.HashSet.mem_insert] at hMem
    rcases hMem with heq | hold
    · right
      have : ops[i].result = c := by simpa using heq
      exact ⟨ops[i], Array.getElem_mem i.isLt, this⟩
    · exact accInv hold
  · simp only [hall] at hMem; exact accInv hMem

theorem iterate_mem_origin (ops : Array OpInfo) :
    ∀ (n : Nat) (s : Std.HashSet QualifiedIdent) (c : QualifiedIdent),
      c ∈ iterate ops s n → c ∈ s ∨ ∃ op ∈ ops, op.result = c
  | 0, s, c, hMem => by rw [iterate_zero] at hMem; exact Or.inl hMem
  | n + 1, s, c, hMem => by
    rw [iterate_succ] at hMem
    by_cases hsame : ((step ops s).size == s.size) = true
    · simp only [hsame, if_true] at hMem; exact Or.inl hMem
    · simp only [hsame] at hMem
      rcases iterate_mem_origin ops n (step ops s) c hMem with hStep | hOp
      · exact step_mem_origin ops s c hStep
      · exact Or.inr hOp

/-- `s ∪ { op.result | op ∈ ops }`. -/
def boundingSet (ops : Array OpInfo) (s : Std.HashSet QualifiedIdent)
    : Std.HashSet QualifiedIdent :=
  ops.foldl (init := s) fun acc op => acc.insert op.result

theorem mem_boundingSet_of_mem_iterate
    (ops : Array OpInfo) (s : Std.HashSet QualifiedIdent) (n : Nat) :
    ∀ c, c ∈ iterate ops s n → c ∈ boundingSet ops s := by
  intro c hMem
  rcases iterate_mem_origin ops n s c hMem with hS | ⟨op, hOp, hRes⟩
  · show c ∈ ops.foldl (init := s) (fun acc op => acc.insert op.result)
    refine Array.foldl_induction
      (motive := fun _ acc => c ∈ acc) hS ?_
    intro i acc accMem
    exact Std.HashSet.mem_insert.mpr (Or.inr accMem)
  · obtain ⟨i, hi_lt, hi⟩ := Array.getElem_of_mem hOp
    show c ∈ ops.foldl (init := s) (fun acc op => acc.insert op.result)
    have key := Array.foldl_induction
      (as := ops) (init := s)
      (f := fun acc op => acc.insert op.result)
      (motive := fun j acc => j > i → c ∈ acc)
      (fun h => absurd h (Nat.not_lt_zero _))
      (by
        intro j acc accAfter hgt
        by_cases hjeq : j.val = i
        · have hopEq : ops[j.val] = ops[i] := by simp [hjeq]
          have hRes' : ops[j].result = c := by
            show ops[j.val].result = c
            rw [hopEq, hi]; exact hRes
          show c ∈ acc.insert ops[j].result
          rw [hRes']
          exact Std.HashSet.mem_insert_self
        · have hjgt : j.val > i := by have : j.val + 1 > i := hgt; omega
          exact Std.HashSet.mem_insert.mpr (Or.inr (accAfter hjgt)))
    exact key hi_lt

theorem boundingSet_size_le (ops : Array OpInfo) (s : Std.HashSet QualifiedIdent) :
    (boundingSet ops s).size ≤ s.size + ops.size := by
  show Std.HashSet.size
        (ops.foldl (init := s) (fun acc op => acc.insert op.result))
      ≤ s.size + ops.size
  refine Array.foldl_induction
    (motive := fun i acc => Std.HashSet.size acc ≤ s.size + i)
    (Nat.le_refl _) ?_
  intro i acc accLe
  calc (acc.insert ops[i].result).size
      ≤ acc.size + 1 := Std.HashSet.size_insert_le
    _ ≤ s.size + i.val + 1 := Nat.add_le_add_right accLe 1
    _ = s.size + (i.val + 1) := by omega

theorem hashset_size_le_of_subset
    (r t : Std.HashSet QualifiedIdent)
    (hSub : ∀ c, c ∈ r → c ∈ t) :
    r.size ≤ t.size := by
  have : (r ∩ t).size = r.size :=
    Std.HashSet.size_inter_eq_size_left hSub
  calc r.size = (r ∩ t).size := this.symm
    _ ≤ t.size := Std.HashSet.size_inter_le_size_right

theorem iterate_size_bound (ops : Array OpInfo) (s : Std.HashSet QualifiedIdent)
    (n : Nat) :
    (iterate ops s n).size ≤ s.size + ops.size := by
  calc (iterate ops s n).size
      ≤ (boundingSet ops s).size :=
        hashset_size_le_of_subset _ _ (mem_boundingSet_of_mem_iterate ops s n)
    _ ≤ s.size + ops.size := boundingSet_size_le ops s

/-! ## Closure under `step` (fuel suffices) -/

/-- After `n` rounds, `iterate` is either at a fixedpoint or has grown by `n`. -/
theorem iterate_fixedpoint_or_grew
    (ops : Array OpInfo) :
    ∀ (n : Nat) (s : Std.HashSet QualifiedIdent),
      (∀ c, c ∈ step ops (iterate ops s n) → c ∈ iterate ops s n)
      ∨ (iterate ops s n).size ≥ s.size + n
  | 0, s => by rw [iterate_zero]; exact Or.inr (Nat.le_refl _)
  | n + 1, s => by
    rw [iterate_succ]
    by_cases hsame : ((step ops s).size == s.size) = true
    · simp only [hsame, if_true]
      left
      exact step_size_eq_implies_mem_eq ops s
        ((Nat.beq_eq_true_eq _ _).mp hsame)
    · have hsame' : ((step ops s).size == s.size) = false := by
        rcases h : ((step ops s).size == s.size) with _ | _
        · rfl
        · exact absurd h hsame
      rw [show (if ((step ops s).size == s.size) = true
                then s
                else iterate ops (step ops s) n)
              = iterate ops (step ops s) n from by simp [hsame']]
      rcases iterate_fixedpoint_or_grew ops n (step ops s) with hFix | hGrew
      · exact Or.inl hFix
      · right
        have hStrict : (step ops s).size ≥ s.size + 1 := by
          have hMono := step_size_mono ops s
          have hNeq : (step ops s).size ≠ s.size := fun hEq =>
            hsame ((Nat.beq_eq_true_eq _ _).mpr hEq)
          omega
        omega

theorem runFixpoint_isFixed
    (ops : Array OpInfo) (trusted : Std.HashSet QualifiedIdent)
    (c : QualifiedIdent) :
    c ∈ step ops (runFixpoint trusted ops) → c ∈ runFixpoint trusted ops := by
  intro hMem
  rw [runFixpoint_eq] at *
  rcases iterate_fixedpoint_or_grew ops (ops.size + 1) trusted with hFix | hGrew
  · exact hFix c hMem
  · have hLe : (iterate ops trusted (ops.size + 1)).size ≤ trusted.size + ops.size :=
      iterate_size_bound ops trusted (ops.size + 1)
    omega

/-! ## Completeness and parametric correctness -/

theorem runFixpoint_complete
    (ops : Array OpInfo) (trusted : Std.HashSet QualifiedIdent)
    (baseSpec : QualifiedIdent → Prop)
    (h0 : ∀ c, baseSpec c → c ∈ trusted) :
    ∀ c, Productive ops baseSpec c → c ∈ runFixpoint trusted ops := by
  intro c hC
  induction hC with
  | @byBase C hT =>
    rw [runFixpoint_eq]
    exact iterate_mono ops (ops.size + 1) trusted C (h0 _ hT)
  | byOp op hOp _ argIH =>
    exact runFixpoint_isFixed ops trusted op.result
      (step_grows ops _ op hOp argIH)

/-- Parametric kernel correctness. -/
theorem runFixpoint_correct
    (ops : Array OpInfo) (trusted : Std.HashSet QualifiedIdent)
    (baseSpec : QualifiedIdent → Prop)
    (hAgree : ∀ c, c ∈ trusted ↔ baseSpec c) :
    ∀ c, c ∈ runFixpoint trusted ops ↔ Productive ops baseSpec c := fun c =>
  ⟨runFixpoint_sound ops trusted baseSpec (fun c h => (hAgree c).mp h) c,
   runFixpoint_complete ops trusted baseSpec (fun c h => (hAgree c).mpr h) c⟩

/-! ## Strict-mode bridge and top-level theorem -/

/-- `trustedCategories` and `frameworkAtomicCategories` agree on membership. -/
theorem mem_trustedCategories_iff_mem_frameworkAtomicCategories
    (c : QualifiedIdent) :
    c ∈ trustedCategories ↔ c ∈ frameworkAtomicCategories := by
  show c ∈ frameworkAtomicCategories.foldl
            (init := (∅ : Std.HashSet QualifiedIdent))
            (fun acc x => acc.insert x)
        ↔ c ∈ frameworkAtomicCategories
  have key := Array.foldl_induction
    (as := frameworkAtomicCategories)
    (init := (∅ : Std.HashSet QualifiedIdent))
    (f := fun acc x => acc.insert x)
    (motive := fun j acc =>
      c ∈ acc ↔
        ∃ k : Nat, ∃ h : k < frameworkAtomicCategories.size,
          k < j ∧ frameworkAtomicCategories[k]'h = c)
    (by
      refine ⟨fun h => ?_, fun ⟨_, _, hk, _⟩ => ?_⟩
      · exact absurd h Std.HashSet.not_mem_empty
      · exact absurd hk (Nat.not_lt_zero _))
    (by
      intro j acc accInv
      refine ⟨fun h => ?_, fun ⟨k, hk_lt, hk_j, hk_eq⟩ => ?_⟩
      · rw [Std.HashSet.mem_insert] at h
        rcases h with hEq | hOld
        · refine ⟨j.val, j.isLt, Nat.lt_succ_self _, ?_⟩
          have : frameworkAtomicCategories[j.val] = c := by simpa using hEq
          exact this
        · rcases (accInv.mp hOld) with ⟨k, hk_lt, hk_j, hk_eq⟩
          exact ⟨k, hk_lt, Nat.lt_succ_of_lt hk_j, hk_eq⟩
      · rw [Std.HashSet.mem_insert]
        by_cases hk_eq_j : k = j.val
        · left
          have hEq : frameworkAtomicCategories[j] = c := by
            show frameworkAtomicCategories[j.val]'j.isLt = c
            have : frameworkAtomicCategories[j.val]'j.isLt
                    = frameworkAtomicCategories[k]'hk_lt := by simp [hk_eq_j]
            rw [this, hk_eq]
          simp [hEq]
        · right
          have hk_lt_j : k < j.val := by
            have : k < j.val + 1 := hk_j
            omega
          exact accInv.mpr ⟨k, hk_lt, hk_lt_j, hk_eq⟩)
  refine key.trans ?_
  refine ⟨fun ⟨k, hk_lt, _, hk_eq⟩ => ?_, fun hMem => ?_⟩
  · rw [← hk_eq]
    exact Array.getElem_mem hk_lt
  · obtain ⟨k, hk_lt, hk_eq⟩ := Array.getElem_of_mem hMem
    exact ⟨k, hk_lt, hk_lt, hk_eq⟩

/-! ## Strict-mode kernel correctness -/

/-- Soundness: every algorithmic ✓ has a derivation tree rooted in
`frameworkAtomicCategories`. -/
theorem runFixpoint_strict_sound (ops : Array OpInfo) :
    ∀ c, c ∈ runFixpoint trustedCategories ops
          → Productive ops (· ∈ frameworkAtomicCategories) c :=
  runFixpoint_sound ops trustedCategories (· ∈ frameworkAtomicCategories)
    (fun c h => (mem_trustedCategories_iff_mem_frameworkAtomicCategories c).mp h)

/-- Completeness: every spec-productive category is in the algorithmic
output. -/
theorem runFixpoint_strict_complete (ops : Array OpInfo) :
    ∀ c, Productive ops (· ∈ frameworkAtomicCategories) c
          → c ∈ runFixpoint trustedCategories ops :=
  runFixpoint_complete ops trustedCategories (· ∈ frameworkAtomicCategories)
    (fun c h => (mem_trustedCategories_iff_mem_frameworkAtomicCategories c).mpr h)

/-- Strict-mode kernel correctness: sound and complete. -/
theorem runFixpoint_strict_correct (ops : Array OpInfo) :
    ∀ c, c ∈ runFixpoint trustedCategories ops
          ↔ Productive ops (· ∈ frameworkAtomicCategories) c := fun c =>
  ⟨runFixpoint_strict_sound ops c, runFixpoint_strict_complete ops c⟩

/-! ## Wrapper correctness -/

/-- Ops of every dialect reachable from `target`. -/
def OpInPool (D : DialectMap) (target : DialectName) (op : OpInfo) : Prop :=
  ∃ d : Dialect, d ∈ D.toList ∧
    ReachableViaImports D target d.name ∧ op ∈ extractOps d

/-- Soundness: every reported productive category is declared in `target`
and has a derivation tree over `extractOpsClosure D target`. -/
theorem check_sound
    (D : DialectMap) (target : DialectName) (h : target ∈ D) (c : QualifiedIdent) :
    c ∈ (check D target).productive →
      c ∈ declaredCategories (D[target]'h)
      ∧ Productive (extractOpsClosure D target)
          (· ∈ frameworkAtomicCategories) c := by
  intro hc
  rw [check_productive_eq D target h, Array.mem_filter] at hc
  exact ⟨hc.1, runFixpoint_strict_sound _ c
    (Std.HashSet.mem_iff_contains.mpr hc.2)⟩

/-- Completeness: every declared category with a derivation tree over
`extractOpsClosure D target` is reported. -/
theorem check_complete
    (D : DialectMap) (target : DialectName) (h : target ∈ D) (c : QualifiedIdent) :
    c ∈ declaredCategories (D[target]'h)
    → Productive (extractOpsClosure D target)
        (· ∈ frameworkAtomicCategories) c
    → c ∈ (check D target).productive := by
  intro hDecl hProd
  rw [check_productive_eq D target h, Array.mem_filter]
  exact ⟨hDecl, Std.HashSet.mem_iff_contains.mp
    (runFixpoint_strict_complete _ c hProd)⟩

/-- Wrapper correctness (sound and complete) modulo `extractOpsClosure`.
Pair with `transitiveImports.fuel_suffices` for full-closure correctness. -/
theorem check_correct
    (D : DialectMap) (target : DialectName) (h : target ∈ D) (c : QualifiedIdent) :
    c ∈ (check D target).productive ↔
      c ∈ declaredCategories (D[target]'h)
      ∧ Productive (extractOpsClosure D target)
          (· ∈ frameworkAtomicCategories) c :=
  ⟨check_sound D target h c,
   fun ⟨hDecl, hProd⟩ => check_complete D target h c hDecl hProd⟩

end Strata.DDM.Productivity

end
