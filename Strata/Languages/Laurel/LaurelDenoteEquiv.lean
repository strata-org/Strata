/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Laurel.LaurelDenoteSound
import Strata.Languages.Laurel.LaurelDenoteComplete
import Strata.Languages.Laurel.LaurelSemanticsProps

/-!
# Equivalence Corollaries for Denotational Semantics

Combines soundness (`LaurelDenoteSound`) and completeness
(`LaurelDenoteComplete`) into bidirectional `_iff` lemmas, and derives
determinism of the denotational interpreter from relational determinism.

Downstream proofs should import this file to get the full public API.

**Note on `HeapInBound` precondition:** The `_iff` lemmas require
`∀ hx, HeapInBound hx` (universally quantified over all heaps), inherited from
`denoteStmt_complete`. The completeness proof needs this invariant to hold for
intermediate heaps produced during evaluation. The `_deterministic` corollaries
do *not* require this assumption since they only use soundness.
-/

namespace Strata.Laurel

/-- The denotational interpreter and relational semantics are
equivalent: a result is reachable by the interpreter (for some fuel)
iff the relational semantics has a derivation. -/
theorem denoteStmt_iff
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore} {s : StmtExprMd}
    {h' : LaurelHeap} {σ' : LaurelStore} {o : Outcome}
    (hib : ∀ hx, HeapInBound hx) :
    (∃ fuel, denoteStmt δ π fuel h σ s.val = some (o, σ', h')) ↔
    EvalLaurelStmt δ π h σ s h' σ' o :=
  ⟨fun ⟨f, hf⟩ => denoteStmt_sound f s.md hf, fun hrel => denoteStmt_complete hrel hib⟩

theorem denoteBlock_iff
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore} {ss : List StmtExprMd}
    {h' : LaurelHeap} {σ' : LaurelStore} {o : Outcome}
    (hib : ∀ hx, HeapInBound hx) :
    (∃ fuel, denoteBlock δ π fuel h σ ss = some (o, σ', h')) ↔
    EvalLaurelBlock δ π h σ ss h' σ' o :=
  ⟨fun ⟨f, hf⟩ => denoteBlock_sound f hf, fun hrel => denoteBlock_complete hrel hib⟩

theorem denoteArgs_iff
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore} {as : List StmtExprMd}
    {h' : LaurelHeap} {σ' : LaurelStore} {vs : List LaurelValue}
    (hib : ∀ hx, HeapInBound hx) :
    (∃ fuel, denoteArgs δ π fuel h σ as = some (vs, σ', h')) ↔
    EvalStmtArgs δ π h σ as h' σ' vs :=
  ⟨fun ⟨f, hf⟩ => denoteArgs_sound f hf, fun hrel => denoteArgs_complete hrel hib⟩

/-- The denotational interpreter is deterministic (up to fuel):
if it returns a result at any two fuel levels, the results agree.
This follows from soundness + relational determinism. -/
theorem denoteStmt_deterministic
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore} {s : StmtExprMd}
    {fuel₁ fuel₂ : Nat}
    {r₁ r₂ : Outcome × LaurelStore × LaurelHeap}
    (h₁ : denoteStmt δ π fuel₁ h σ s.val = some r₁)
    (h₂ : denoteStmt δ π fuel₂ h σ s.val = some r₂) :
    r₁ = r₂ := by
  obtain ⟨o₁, σ₁, hp₁⟩ := r₁
  obtain ⟨o₂, σ₂, hp₂⟩ := r₂
  have hs₁ := denoteStmt_sound fuel₁ s.md h₁
  have hs₂ := denoteStmt_sound fuel₂ s.md h₂
  have ⟨heq_h, heq_σ, heq_o⟩ := EvalLaurelStmt_deterministic hs₁ hs₂
  subst heq_h; subst heq_σ; subst heq_o; rfl

theorem denoteBlock_deterministic
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore} {ss : List StmtExprMd}
    {fuel₁ fuel₂ : Nat}
    {r₁ r₂ : Outcome × LaurelStore × LaurelHeap}
    (h₁ : denoteBlock δ π fuel₁ h σ ss = some r₁)
    (h₂ : denoteBlock δ π fuel₂ h σ ss = some r₂) :
    r₁ = r₂ := by
  obtain ⟨o₁, σ₁, hp₁⟩ := r₁
  obtain ⟨o₂, σ₂, hp₂⟩ := r₂
  have hs₁ := denoteBlock_sound fuel₁ h₁
  have hs₂ := denoteBlock_sound fuel₂ h₂
  have ⟨heq_h, heq_σ, heq_o⟩ := EvalLaurelBlock_deterministic hs₁ hs₂
  subst heq_h; subst heq_σ; subst heq_o; rfl

theorem denoteArgs_deterministic
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore} {as : List StmtExprMd}
    {fuel₁ fuel₂ : Nat}
    {r₁ r₂ : List LaurelValue × LaurelStore × LaurelHeap}
    (h₁ : denoteArgs δ π fuel₁ h σ as = some r₁)
    (h₂ : denoteArgs δ π fuel₂ h σ as = some r₂) :
    r₁ = r₂ := by
  obtain ⟨vs₁, σ₁, hp₁⟩ := r₁
  obtain ⟨vs₂, σ₂, hp₂⟩ := r₂
  have hs₁ := denoteArgs_sound fuel₁ h₁
  have hs₂ := denoteArgs_sound fuel₂ h₂
  have ⟨heq_h, heq_σ, heq_vs⟩ := EvalStmtArgs_deterministic hs₁ hs₂
  subst heq_h; subst heq_σ; subst heq_vs; rfl

end Strata.Laurel
