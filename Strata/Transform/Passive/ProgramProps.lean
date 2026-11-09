/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.Program
import Std.Data.String.ToNat
import Strata.Util.ExceptProps

/-! # Properties of the vocabulary of the WP and SSA phases: fresh names and the names invariant

Introduced names are injective in their counter (`freshName_counter_inj`), and `freshIn` picks
one outside the avoided names with a counter at least the current one (`freshIn_spec`); the base
of a name is a prefix of it (`baseOf_prefix`); the names invariant `NamesOK` (every defined name
of the form of a name still to be introduced is avoided) survives defining fresh names.

Key theorems: `freshName_counter_inj`, `freshIn_spec`, `baseOf_prefix`, `NamesOK.add_fresh`.

Key definitions: `NamesOK`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iB : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iHB : HasBool P] [iHF : HasFvar P] [iHS : HasSubstFvar P] [iH : HasIdent P]
  [iLI : LawfulHasIdent P] [iHa : Hashable P.Ident] [iHV : HasFvars P]
omit iDE iB iLB iHB iHF iHS iH iLI iHa iHV

/-! ### Fresh names

Introduced names are injective in their counter, and `freshIn` picks one outside the avoided
names with a counter at least the current one. -/

include iH iLI in
/-- Two introduced names that are equal have the same counter. -/
theorem freshName_counter_inj {b b' : String} {n n' : Nat}
    (h : freshName (P := P) b n = freshName b' n') : n = n' := by
  have hs := congrArg (fun s : String => (s.toList.reverse.takeWhile Char.isDigit).reverse)
    (LawfulHasIdent.ident_inj h)
  have hd (k : Nat) : ∀ c ∈ (Nat.toDigits 10 k).reverse, c.isDigit :=
    fun _ hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) (List.mem_reverse.1 hc)
  refine Nat.repr_injective (String.toList_inj.1 ?_)
  simpa [Nat.toList_repr, List.takeWhile_append_of_pos (hd _)] using hs

include iDE iB iLB iHB iHF iHS iH iLI iHa iHV in
/-- `freshIn avoid b n` is `(freshName b k, k + 1)` for a counter `k ≥ n` whose name is not
    avoided. -/
theorem freshIn_spec (avoid : AvoidSet P) (b : String) (n : Nat) :
    ∃ k, freshIn avoid b n = (freshName b k, k + 1) ∧ n ≤ k ∧
      avoid.contains (freshName b k) = false := by
  have hc (x : P.Ident) (hx : avoid.contains x) : x ∈ avoid.toList := by
    simp only [AvoidSet.contains, Bool.or_eq_true] at hx
    simp only [AvoidSet.toList, List.mem_append, Std.HashSet.mem_toList]
    exact hx.imp Std.HashSet.mem_iff_contains.2 Std.HashSet.mem_iff_contains.2
  have hfc (fuel n : Nat) : n ≤ freeCounterIn avoid b fuel n ∧
      (avoid.contains (freshName b (freeCounterIn avoid b fuel n)) →
        ∀ i ≤ fuel, freshName b (n + i) ∈ avoid.toList) := by
    fun_induction freeCounterIn avoid b fuel n with
    | case2 k n h ih => exact ⟨by omega, fun hm i hi => by cases i <;> grind [ih.2 hm]⟩
    | _ => grind
  obtain ⟨hge, hmem⟩ := hfc (avoid.glob.size + avoid.loc.size + 1) n
  refine ⟨_, rfl, hge, Bool.eq_false_iff.2 fun h => ?_⟩
  have hnd : ((List.range (avoid.glob.size + avoid.loc.size + 1)).map
      (freshName (P := P) b <| n + ·)).Nodup :=
    List.nodup_range.map _ fun i j hne he => hne (by simpa using freshName_counter_inj he)
  exact absurd (List.subset_nodup_length (s2 := avoid.toList) hnd fun y hy => by grind)
    (by simp [AvoidSet.toList])

/-! ### Bases of names -/

/-- The base of a name is a prefix of it. -/
theorem baseOf_prefix [WPOps P] (x : P.Ident) : (baseOf x).toList <+: (WPOps.name x).toList := by
  unfold baseOf
  dsimp only
  generalize (List.takeWhile Char.isDigit (WPOps.name x).toList.reverse).length = k
  split
  · rename_i pre h
    split
    · exact List.prefix_refl _
    · rw [String.toList_ofList, ← List.reverse_reverse (WPOps.name x).toList]
      generalize (WPOps.name x).toList.reverse = cs at h ⊢
      rw [← List.take_append_drop k cs, h, List.reverse_append, List.reverse_cons,
        List.append_assoc]
      exact List.prefix_append _ _
  · exact List.prefix_refl _

/-! ### The names invariant -/

include iH in
/-- The names invariant: every defined name in `D` of the form of a name the
    pass may still introduce (`freshName b j`, `n ≤ j`) is one of the avoided names `A`. -/
@[expose] def NamesOK (A D : List P.Ident) (n : Nat) : Prop :=
  ∀ y ∈ D, ∀ b j, n ≤ j → y = freshName b j → y ∈ A

include iH in
/-- Under `NamesOK`, a name the pass introduces with a counter at least the current one and
    outside the avoided names is not defined. -/
theorem NamesOK.fresh_not_mem {A D : List P.Ident} {n : Nat} (h : NamesOK A D n) {b : String}
    {j : Nat} (hj : n ≤ j) (hA : freshName (P := P) b j ∉ A) : freshName b j ∉ D :=
  fun hm => hA (h _ hm b j hj rfl)

include iH iLI in
/-- `NamesOK` survives defining an introduced name with a counter `j` at least the current
    one and advancing the counter past `j`. -/
theorem NamesOK.add_fresh {A D : List P.Ident} {n : Nat} (h : NamesOK A D n) (b : String)
    {j : Nat} (hj : n ≤ j) : NamesOK A (freshName b j :: D) (j + 1) :=
  fun y hy b' j' hj' he => (List.mem_cons.1 hy).elim
    (fun e => absurd (freshName_counter_inj (e ▸ he)) (by omega)) (h y · b' j' (by omega) he)

end -- public section

end WP
end Imperative
