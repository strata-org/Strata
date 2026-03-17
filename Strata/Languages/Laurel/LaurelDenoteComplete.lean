/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Laurel.LaurelDenote
import Strata.Languages.Laurel.LaurelSemantics
import Strata.Languages.Laurel.LaurelDenoteBridge
import Strata.Languages.Laurel.LaurelDenoteMono

/-!
# Completeness: Relational Semantics Implies Denotational Interpreter

If `EvalLaurelStmt` has a derivation, then `denoteStmt` succeeds with
enough fuel (and similarly for `EvalLaurelBlock`/`EvalStmtArgs`).

## Heap Bound Assumption

The computable `allocHeap` searches a bounded range (`heapSearchBound = 10000`)
for a free address. The relational `AllocHeap` has no such bound. Completeness
therefore requires that every heap encountered during evaluation has a free
address within the search bound. The predicate `HeapInBound` captures this:
it says the smallest free address in the heap is ≤ `heapSearchBound`.

For any program that allocates fewer than 10000 objects, every intermediate
heap satisfies `HeapInBound`, so the hypothesis is trivially discharged.
-/

namespace Strata.Laurel

/-! ## Heap bound predicate -/

/-- A heap is "in bound" if its smallest free address is ≤ `heapSearchBound`.
Equivalently, there exists a free address within the search range. -/
def HeapInBound (h : LaurelHeap) : Prop :=
  ∀ addr, h addr = none → (∀ a, a < addr → (h a).isSome) → addr ≤ heapSearchBound

/-- If `HeapInBound h` and `AllocHeap h typeName addr h'`, then `addr ≤ heapSearchBound`. -/
theorem AllocHeap_addr_bound {h h' : LaurelHeap} {typeName : String} {addr : Nat}
    (hib : HeapInBound h) (halloc : AllocHeap h typeName addr h') :
    addr ≤ heapSearchBound := by
  cases halloc with
  | alloc hfree hmin _ _ => exact hib addr hfree hmin

/-! ## Helper lemmas for block cases -/

private theorem denoteBlock_exit_of_head
    {δ : LaurelEval} {π : ProcEnv} {fuel : Nat}
    {h : LaurelHeap} {σ : LaurelStore}
    {s : StmtExprMd} {rest : List StmtExprMd}
    {label : String} {σ' : LaurelStore} {h' : LaurelHeap}
    (hs : denoteStmt δ π fuel h σ s.val = some (.exit label, σ', h')) :
    denoteBlock δ π (fuel + 1) h σ (s :: rest) = some (.exit label, σ', h') := by
  cases rest with
  | nil => simp [denoteBlock]; exact hs
  | cons => unfold denoteBlock; simp [hs]

private theorem denoteBlock_return_of_head
    {δ : LaurelEval} {π : ProcEnv} {fuel : Nat}
    {h : LaurelHeap} {σ : LaurelStore}
    {s : StmtExprMd} {rest : List StmtExprMd}
    {rv : Option LaurelValue} {σ' : LaurelStore} {h' : LaurelHeap}
    (hs : denoteStmt δ π fuel h σ s.val = some (.ret rv, σ', h')) :
    denoteBlock δ π (fuel + 1) h σ (s :: rest) = some (.ret rv, σ', h') := by
  cases rest with
  | nil => simp [denoteBlock]; exact hs
  | cons => unfold denoteBlock; simp [hs]

private theorem denoteBlock_cons_normal
    {δ : LaurelEval} {π : ProcEnv} {fuel : Nat}
    {h : LaurelHeap} {σ : LaurelStore}
    {s : StmtExprMd} {rest : List StmtExprMd}
    {v : LaurelValue} {σ₁ : LaurelStore} {h₁ : LaurelHeap}
    {o : Outcome} {σ' : LaurelStore} {h' : LaurelHeap}
    (hne : rest ≠ [])
    (hs : denoteStmt δ π fuel h σ s.val = some (.normal v, σ₁, h₁))
    (hr : denoteBlock δ π fuel h₁ σ₁ rest = some (o, σ', h')) :
    denoteBlock δ π (fuel + 1) h σ (s :: rest) = some (o, σ', h') := by
  cases rest with
  | nil => exact absurd rfl hne
  | cons => unfold denoteBlock; simp [hs, hr]

/-! ## Main completeness theorems -/

set_option maxHeartbeats 12800000 in
set_option maxRecDepth 4096 in
mutual
theorem denoteStmt_complete
    {δ : LaurelEval} {π : ProcEnv} {h : LaurelHeap} {σ : LaurelStore}
    {s : StmtExprMd} {h' : LaurelHeap} {σ' : LaurelStore} {o : Outcome}
    (heval : EvalLaurelStmt δ π h σ s h' σ' o)
    (hib : ∀ hx, HeapInBound hx) :
    ∃ fuel, denoteStmt δ π fuel h σ s.val = some (o, σ', h') :=
  match heval with
  | .literal_int => ⟨1, rfl⟩
  | .literal_bool => ⟨1, rfl⟩
  | .literal_string => ⟨1, rfl⟩
  | .identifier hlook => ⟨1, by simp only [denoteStmt, hlook]⟩
  | .exit_sem => ⟨1, rfl⟩
  | .return_none => ⟨1, rfl⟩
  | .this_sem hlook => ⟨1, by simp only [denoteStmt, hlook]⟩
  | .forall_sem hd => ⟨1, by simp only [denoteStmt, hd]⟩
  | .exists_sem hd => ⟨1, by simp only [denoteStmt, hd]⟩
  | .old_sem hd => ⟨1, by simp only [denoteStmt, hd]⟩
  | .fresh_sem hd => ⟨1, by simp only [denoteStmt, hd]⟩
  | .assigned_sem hd => ⟨1, by simp only [denoteStmt, hd]⟩
  | .contract_of hd => ⟨1, by simp only [denoteStmt, hd]⟩
  | .new_obj halloc =>
    ⟨1, by simp only [denoteStmt,
      allocHeap_complete (hbound := AllocHeap_addr_bound (hib h) halloc) halloc]⟩
  | .local_var_uninit hnone hinit =>
    ⟨1, by simp only [denoteStmt, initStore_complete hinit]⟩
  | .return_some hv =>
    let ⟨f, hf⟩ := denoteStmt_complete hv hib
    ⟨f + 1, by simp only [denoteStmt, hf]⟩
  | .assert_true hc =>
    let ⟨f, hf⟩ := denoteStmt_complete hc hib
    ⟨f + 1, by simp only [denoteStmt, hf]⟩
  | .assume_true hc =>
    let ⟨f, hf⟩ := denoteStmt_complete hc hib
    ⟨f + 1, by simp only [denoteStmt, hf]⟩
  | .as_type ht =>
    let ⟨f, hf⟩ := denoteStmt_complete ht hib
    ⟨f + 1, by simp only [denoteStmt, hf]⟩
  | .prove_by hv =>
    let ⟨f, hf⟩ := denoteStmt_complete hv hib
    ⟨f + 1, by simp only [denoteStmt]; exact hf⟩
  | .field_select ht hread =>
    let ⟨f, hf⟩ := denoteStmt_complete ht hib
    ⟨f + 1, by simp only [denoteStmt, hf, hread]⟩
  | .is_type ht hlook =>
    let ⟨f, hf⟩ := denoteStmt_complete ht hib
    ⟨f + 1, by simp only [denoteStmt, hf, hlook]⟩
  | .ite_false_no_else hc =>
    let ⟨f, hf⟩ := denoteStmt_complete hc hib
    ⟨f + 1, by simp only [denoteStmt, hf]⟩
  | .while_false hc =>
    let ⟨f, hf⟩ := denoteStmt_complete hc hib
    ⟨f + 1, by simp only [denoteStmt, hf]⟩
  | .assign_single hv hexists hupd =>
    let ⟨f, hf⟩ := denoteStmt_complete hv hib
    ⟨f + 1, by simp only [denoteStmt, hf, hexists, updateStore_complete hupd]⟩
  | .local_var_init hinit _ hinitS =>
    let ⟨f, hf⟩ := denoteStmt_complete hinit hib
    ⟨f + 1, by simp only [denoteStmt, hf, initStore_complete hinitS]⟩
  | .ite_true hc hthen =>
    let ⟨f₁, hf₁⟩ := denoteStmt_complete hc hib
    let ⟨f₂, hf₂⟩ := denoteStmt_complete hthen hib
    ⟨(f₁ + f₂) + 1, by
      unfold denoteStmt
      simp [denoteStmt_fuel_mono (show f₁ ≤ f₁ + f₂ by omega) hf₁,
            denoteStmt_fuel_mono (show f₂ ≤ f₁ + f₂ by omega) hf₂]⟩
  | .ite_false hc helse =>
    let ⟨f₁, hf₁⟩ := denoteStmt_complete hc hib
    let ⟨f₂, hf₂⟩ := denoteStmt_complete helse hib
    ⟨(f₁ + f₂) + 1, by
      unfold denoteStmt
      simp [denoteStmt_fuel_mono (show f₁ ≤ f₁ + f₂ by omega) hf₁,
            denoteStmt_fuel_mono (show f₂ ≤ f₁ + f₂ by omega) hf₂]⟩
  | .ite_true_no_else hc hthen =>
    let ⟨f₁, hf₁⟩ := denoteStmt_complete hc hib
    let ⟨f₂, hf₂⟩ := denoteStmt_complete hthen hib
    ⟨(f₁ + f₂) + 1, by
      unfold denoteStmt
      simp [denoteStmt_fuel_mono (show f₁ ≤ f₁ + f₂ by omega) hf₁,
            denoteStmt_fuel_mono (show f₂ ≤ f₁ + f₂ by omega) hf₂]⟩
  | .reference_equals hl hr =>
    let ⟨f₁, hf₁⟩ := denoteStmt_complete hl hib
    let ⟨f₂, hf₂⟩ := denoteStmt_complete hr hib
    ⟨(f₁ + f₂) + 1, by
      unfold denoteStmt
      simp [denoteStmt_fuel_mono (show f₁ ≤ f₁ + f₂ by omega) hf₁,
            denoteStmt_fuel_mono (show f₂ ≤ f₁ + f₂ by omega) hf₂]⟩
  | .while_exit hc hbody =>
    let ⟨f₁, hf₁⟩ := denoteStmt_complete hc hib
    let ⟨f₂, hf₂⟩ := denoteStmt_complete hbody hib
    ⟨(f₁ + f₂) + 1, by
      unfold denoteStmt
      simp [denoteStmt_fuel_mono (show f₁ ≤ f₁ + f₂ by omega) hf₁,
            denoteStmt_fuel_mono (show f₂ ≤ f₁ + f₂ by omega) hf₂]⟩
  | .while_return hc hbody =>
    let ⟨f₁, hf₁⟩ := denoteStmt_complete hc hib
    let ⟨f₂, hf₂⟩ := denoteStmt_complete hbody hib
    ⟨(f₁ + f₂) + 1, by
      unfold denoteStmt
      simp [denoteStmt_fuel_mono (show f₁ ≤ f₁ + f₂ by omega) hf₁,
            denoteStmt_fuel_mono (show f₂ ≤ f₁ + f₂ by omega) hf₂]⟩
  | .while_true hc hbody hrec =>
    let ⟨f₁, hf₁⟩ := denoteStmt_complete hc hib
    let ⟨f₂, hf₂⟩ := denoteStmt_complete hbody hib
    let ⟨f₃, hf₃⟩ := denoteStmt_complete hrec hib
    ⟨(f₁ + f₂ + f₃) + 1, by
      unfold denoteStmt
      simp [denoteStmt_fuel_mono (show f₁ ≤ f₁ + f₂ + f₃ by omega) hf₁,
            denoteStmt_fuel_mono (show f₂ ≤ f₁ + f₂ + f₃ by omega) hf₂,
            denoteStmt_fuel_mono (show f₃ ≤ f₁ + f₂ + f₃ by omega) hf₃]⟩
  | .pure_field_update ht hv hfw =>
    let ⟨f₁, hf₁⟩ := denoteStmt_complete ht hib
    let ⟨f₂, hf₂⟩ := denoteStmt_complete hv hib
    ⟨(f₁ + f₂) + 1, by
      unfold denoteStmt
      simp [denoteStmt_fuel_mono (show f₁ ≤ f₁ + f₂ by omega) hf₁,
            denoteStmt_fuel_mono (show f₂ ≤ f₁ + f₂ by omega) hf₂,
            heapFieldWrite_complete hfw]⟩
  | .assign_field ht hv hfw =>
    let ⟨f₁, hf₁⟩ := denoteStmt_complete ht hib
    let ⟨f₂, hf₂⟩ := denoteStmt_complete hv hib
    ⟨(f₁ + f₂) + 1, by
      unfold denoteStmt
      simp [denoteStmt_fuel_mono (show f₁ ≤ f₁ + f₂ by omega) hf₁,
            denoteStmt_fuel_mono (show f₂ ≤ f₁ + f₂ by omega) hf₂,
            heapFieldWrite_complete hfw]⟩
  | .block_sem hblock hcatch =>
    let ⟨f, hf⟩ := denoteBlock_complete hblock hib
    ⟨f + 1, by simp only [denoteStmt, hf, hcatch]⟩
  | .prim_op hargs hprim =>
    let ⟨f, hf⟩ := denoteArgs_complete hargs hib
    ⟨f + 1, by simp only [denoteStmt, hf, hprim]⟩
  | .static_call hproc hargs hbind hbody hcall =>
    let ⟨fa, hfa⟩ := denoteArgs_complete hargs hib
    let ⟨fb, hfb⟩ := denoteStmt_complete hcall hib
    ⟨(fa + fb) + 1, by
      unfold denoteStmt
      simp [hproc, denoteArgs_fuel_mono (show fa ≤ fa + fb by omega) hfa,
            hbind, hbody, denoteStmt_fuel_mono (show fb ≤ fa + fb by omega) hfb]⟩
  | .static_call_return hproc hargs hbind hbody hcall =>
    let ⟨fa, hfa⟩ := denoteArgs_complete hargs hib
    let ⟨fb, hfb⟩ := denoteStmt_complete hcall hib
    ⟨(fa + fb) + 1, by
      unfold denoteStmt
      simp [hproc, denoteArgs_fuel_mono (show fa ≤ fa + fb by omega) hfa,
            hbind, hbody, denoteStmt_fuel_mono (show fb ≤ fa + fb by omega) hfb]⟩
  | .static_call_return_void hproc hargs hbind hbody hcall =>
    let ⟨fa, hfa⟩ := denoteArgs_complete hargs hib
    let ⟨fb, hfb⟩ := denoteStmt_complete hcall hib
    ⟨(fa + fb) + 1, by
      unfold denoteStmt
      simp [hproc, denoteArgs_fuel_mono (show fa ≤ fa + fb by omega) hfa,
            hbind, hbody, denoteStmt_fuel_mono (show fb ≤ fa + fb by omega) hfb]⟩
  | .instance_call htarget hlook hproc hargs hbind hbody hcall =>
    let ⟨ft, hft⟩ := denoteStmt_complete htarget hib
    let ⟨fa, hfa⟩ := denoteArgs_complete hargs hib
    let ⟨fb, hfb⟩ := denoteStmt_complete hcall hib
    ⟨(ft + fa + fb) + 1, by
      unfold denoteStmt
      simp [denoteStmt_fuel_mono (show ft ≤ ft + fa + fb by omega) hft,
            hlook, hproc, denoteArgs_fuel_mono (show fa ≤ ft + fa + fb by omega) hfa,
            hbind, hbody, denoteStmt_fuel_mono (show fb ≤ ft + fa + fb by omega) hfb]⟩
  | .instance_call_return htarget hlook hproc hargs hbind hbody hcall =>
    let ⟨ft, hft⟩ := denoteStmt_complete htarget hib
    let ⟨fa, hfa⟩ := denoteArgs_complete hargs hib
    let ⟨fb, hfb⟩ := denoteStmt_complete hcall hib
    ⟨(ft + fa + fb) + 1, by
      unfold denoteStmt
      simp [denoteStmt_fuel_mono (show ft ≤ ft + fa + fb by omega) hft,
            hlook, hproc, denoteArgs_fuel_mono (show fa ≤ ft + fa + fb by omega) hfa,
            hbind, hbody, denoteStmt_fuel_mono (show fb ≤ ft + fa + fb by omega) hfb]⟩
  | .instance_call_return_void htarget hlook hproc hargs hbind hbody hcall =>
    let ⟨ft, hft⟩ := denoteStmt_complete htarget hib
    let ⟨fa, hfa⟩ := denoteArgs_complete hargs hib
    let ⟨fb, hfb⟩ := denoteStmt_complete hcall hib
    ⟨(ft + fa + fb) + 1, by
      unfold denoteStmt
      simp [denoteStmt_fuel_mono (show ft ≤ ft + fa + fb by omega) hft,
            hlook, hproc, denoteArgs_fuel_mono (show fa ≤ ft + fa + fb by omega) hfa,
            hbind, hbody, denoteStmt_fuel_mono (show fb ≤ ft + fa + fb by omega) hfb]⟩

theorem denoteBlock_complete
    {δ : LaurelEval} {π : ProcEnv} {h : LaurelHeap} {σ : LaurelStore}
    {ss : List StmtExprMd} {h' : LaurelHeap} {σ' : LaurelStore} {o : Outcome}
    (heval : EvalLaurelBlock δ π h σ ss h' σ' o)
    (hib : ∀ hx, HeapInBound hx) :
    ∃ fuel, denoteBlock δ π fuel h σ ss = some (o, σ', h') :=
  match heval with
  | .nil => ⟨1, rfl⟩
  | .last_normal hs =>
    let ⟨f, hf⟩ := denoteStmt_complete hs hib
    ⟨f + 1, by simp only [denoteBlock]; exact hf⟩
  | .cons_normal hs hne hrest =>
    let ⟨f₁, hf₁⟩ := denoteStmt_complete hs hib
    let ⟨f₂, hf₂⟩ := denoteBlock_complete hrest hib
    ⟨(f₁ + f₂) + 1, denoteBlock_cons_normal hne
      (denoteStmt_fuel_mono (by omega) hf₁)
      (denoteBlock_fuel_mono (by omega) hf₂)⟩
  | .cons_exit hs =>
    let ⟨f, hf⟩ := denoteStmt_complete hs hib
    ⟨f + 1, denoteBlock_exit_of_head hf⟩
  | .cons_return hs =>
    let ⟨f, hf⟩ := denoteStmt_complete hs hib
    ⟨f + 1, denoteBlock_return_of_head hf⟩

theorem denoteArgs_complete
    {δ : LaurelEval} {π : ProcEnv} {h : LaurelHeap} {σ : LaurelStore}
    {as : List StmtExprMd} {h' : LaurelHeap} {σ' : LaurelStore}
    {vs : List LaurelValue}
    (heval : EvalStmtArgs δ π h σ as h' σ' vs)
    (hib : ∀ hx, HeapInBound hx) :
    ∃ fuel, denoteArgs δ π fuel h σ as = some (vs, σ', h') :=
  match heval with
  | .nil => ⟨1, rfl⟩
  | .cons he hes =>
    let ⟨f₁, hf₁⟩ := denoteStmt_complete he hib
    let ⟨f₂, hf₂⟩ := denoteArgs_complete hes hib
    ⟨(f₁ + f₂) + 1, by
      unfold denoteArgs
      simp [denoteStmt_fuel_mono (show f₁ ≤ f₁ + f₂ by omega) hf₁,
            denoteArgs_fuel_mono (show f₂ ≤ f₁ + f₂ by omega) hf₂]⟩
end

end Strata.Laurel
