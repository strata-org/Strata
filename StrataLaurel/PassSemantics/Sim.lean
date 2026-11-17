/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.PassSemantics.RealMono

/-!
# Forward simulation between two interpreter runs

This file defines when one interpreter action simulates another, and proves that this is
preserved by the combinators and primitives the interpreter is written with. Pass proofs
relate a source run and a target run through these lemmas.

* `SimRel`: a simulation relation. It relates states (`st`) and events (`ev`), says which
  control signals may escape (`ok`), which label a `return` becomes (`ret`), and how a
  valued `return` relates to the target state (`win`).
* `TrRel`: two traces have the same number of failed checks (`nFail`), the same oracle,
  initial values and initial heap, and the oracle ignores types (`Blind`).
* `FSH S T U A x y`: if the states are related by `S`, the traces by `TrRel`, and `x` does
  not run out of fuel, then `x` gets stuck (`Stuck`) or the results are related by `RR`:
  values by `A`, states after a normal exit by `T`, signals and their states by `U`
  (`SigR`). `FS S A` is `FSH S S S A`.
* `fs_pure`, `fs_bind`, `fs_tryCatch`, `fs_ite`, `fs_forM`, `fs_mapM`, `fs_forIn`: `FSH`
  is preserved by each combinator.
* `fs_get`, `fs_modify`, `fs_emit`, `fs_liftM`, `fs_choose`: `FSH` holds for the
  interpreter's primitives.
* `L2 R l l'`: two lists of equal length, related pointwise by `R`.
-/

namespace Strata.Laurel.PassSemantics

open Strata.Laurel
open Strata.Laurel.Interpreter

inductive L2 (R : α → β → Prop) : List α → List β → Prop where
  | nil : L2 R [] []
  | cons {a b as bs} : R a b → L2 R as bs → L2 R (a :: as) (b :: bs)

theorem L2.refl (l : List α) : L2 Eq l l := by
  induction l with
  | nil => exact .nil
  | cons x xs ih => exact .cons rfl ih

theorem L2.reflP {P : α → Prop} (l : List α) (h : ∀ x ∈ l, P x) : L2 (fun a b => a = b ∧ P a) l l := by
  induction l with
  | nil => exact .nil
  | cons x xs ih =>
    exact .cons ⟨rfl, h x (List.mem_cons_self ..)⟩ (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem L2.concat {R : α → β → Prop} {l : List α} {l' : List β} {a : α} {b : β}
    (h : L2 R l l') (hab : R a b) : L2 R (l ++ [a]) (l' ++ [b]) := by
  induction h with
  | nil => exact .cons hab .nil
  | cons h1 _ ih => exact .cons h1 ih

theorem L2.imp {R R' : α → β → Prop} {l : List α} {l' : List β} (h : L2 R l l') (hR : ∀ a b, R a b → R' a b) :
    L2 R' l l' := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hR _ _ hab) ih

theorem L2.and {R S : α → β → Prop} {l : List α} {l' : List β} (h : L2 R l l') (h' : L2 S l l') :
    L2 (fun a b => R a b ∧ S a b) l l' := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih =>
    cases h' with
    | cons hs hl => exact .cons ⟨hab, hs⟩ (ih hl)

theorem L2.head {R : α → β → Prop} {a : α} {b : β} {l : List α} {l' : List β} (h : L2 R (a :: l) (b :: l')) :
    R a b := by
  cases h; assumption

theorem L2.withMem {R : α → β → Prop} {l : List α} {l' : List β} (h : L2 R l l') :
    L2 (fun a b => R a b ∧ a ∈ l) l l' := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih =>
    exact .cons ⟨hab, List.mem_cons_self ..⟩ (ih.imp (fun a b h => ⟨h.1, List.mem_cons_of_mem _ h.2⟩))

structure SimRel where
  st : EvalState → EvalState → Prop
  ev : Event → Event → Prop
  ok : Control → Prop
  ret : Option String
  win : Value → EvalState → EvalState → Prop := fun _ _ _ => False

def Blind (o : Nat → Option HighType → Value → Value) : Prop :=
  ∀ i t t' d, o i t d = o i t' d

def failOf : Event → Nat
  | .check _ _ _ false _ => 1
  | _ => 0

def nFail (l : List Event) : Nat := (l.map failOf).sum

def TrRel (_S : SimRel) (τ τ' : Trace) : Prop :=
  nFail τ.events.toList = nFail τ'.events.toList ∧ (τ.oracle, τ.init, τ.heap0) = (τ'.oracle, τ'.init, τ'.heap0) ∧
    Blind τ.oracle ∧ τ.next = τ'.next

theorem nFail_concat (l : List Event) (e : Event) : nFail (l ++ [e]) = nFail l + failOf e := by
  simp [nFail]

@[simp] theorem returnedValues_nil (P : Procedure) (r : EvalM PM Unit) :
    returnedValues P r [] = pure none := rfl

theorem returnedValues_toList (P : Procedure) (r : EvalM PM Unit) (o : Option Value) :
    returnedValues P r o.toList = pure o := by
  cases o <;> rfl

@[simp] theorem returnedValues_single (P : Procedure) (r : EvalM PM Unit) (v : Value) :
    returnedValues P r [v] = pure (some v) := rfl

def CtlR (ret : Option String) (c c' : Control) : Prop :=
  c = c' ∨ (∃ L, ret = some L ∧ c = .return_ [] ∧ c' = .exit_ L) ∨ ∃ r r', c = .refused r ∧ c' = .refused r'

theorem CtlR.eq {c c' : Control} (h : CtlR none c c') : c = c' ∨ ∃ r r', c = .refused r ∧ c' = .refused r' :=
  h.elim .inl (fun h => h.elim (fun ⟨_, hL, _⟩ => by cases hL) .inr)

def eraseO : Outcome → Outcome
  | .refused _ => .refused ""
  | o => o

def SigR (U : SimRel) (c c' : Control) (σ σ' : EvalState) : Prop :=
  (CtlR U.ret c c' ∧ U.ok c ∧ U.st σ σ') ∨
    (∃ v, c = .return_ [v] ∧ c' = .return_ [] ∧ U.win v σ σ')

def ExRel (U : SimRel) (A : α → β → Prop) :
    Except Control α → Except Control β → EvalState → EvalState → Prop
  | .ok a, .ok b, _, _ => A a b
  | .error c, .error c', σ, σ' => SigR U c c' σ σ'
  | _, _, _, _ => False

inductive Stuck : HErr → Prop where
  | mk (m : String) : Stuck (.stuck m)

def RR (T U : SimRel) (A : α → β → Prop) : R α → R β → Prop
  | .error e, .error e' => Stuck e' → Stuck e
  | .error e, .ok _ => Stuck e
  | .ok ((a, σ), τ), .ok ((b, σ'), τ') => ExRel U A a b σ σ' ∧
      match a with
      | .ok _ => T.st σ σ' ∧ TrRel T τ τ'
      | .error _ => TrRel U τ τ'
  | _, _ => False

structure FSH (S T U : SimRel) (A : α → β → Prop) (x : EvalM PM α) (y : EvalM PM β) : Prop where
  sim : ∀ σ σ' τ τ', S.st σ σ' → TrRel S τ τ' → ¬ OOF (run x σ τ) →
    RR T U A (run x σ τ) (run y σ' τ')

abbrev FS (S : SimRel) (A : α → β → Prop) (x : EvalM PM α) (y : EvalM PM β) : Prop := FSH S S S A x y

variable {S T U V : SimRel}

theorem SigR.not_oof {c c' : Control} {σ σ' : EvalState} (h : SigR U c c' σ σ') (hc : c ≠ .outOfFuel) :
    c' ≠ .outOfFuel := by
  rcases h with ⟨hc', -, -⟩ | ⟨v, rfl, rfl, -⟩
  · rcases hc' with rfl | ⟨L, -, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
    · exact hc
    · exact fun h => by cases h
    · exact fun h => by cases h
  · exact fun h => by cases h

theorem SigR.same {c c' : Control} {σ σ' : EvalState} (h : SigR U c c' σ σ') (hw : ∀ v, ¬ U.win v σ σ') :
    CtlR U.ret c c' ∧ U.ok c ∧ U.st σ σ' :=
  h.elim id (fun ⟨v, _, _, h⟩ => absurd h (hw v))

theorem SigR.mono {c c' : Control} {σ σ' : EvalState} (h : SigR U c c' σ σ') (hr : U.ret = V.ret)
    (hok : ∀ c, U.ok c → V.ok c) (hst : ∀ σ σ', U.st σ σ' → V.st σ σ')
    (hw : ∀ v σ σ', U.win v σ σ' → V.win v σ σ') : SigR V c c' σ σ' := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨v, h1, h2, h3⟩
  · exact .inl ⟨hr ▸ h1, hok _ h2, hst _ _ h3⟩
  · exact .inr ⟨v, h1, h2, hw _ _ _ h3⟩

theorem RR.ofStuck {A : α → β → Prop} {e : HErr} (h : Stuck e) (r' : R β) :
    RR T U A (.error e : R α) r' := by
  rcases r' with _ | _
  · exact fun _ => h
  · exact h

theorem stuck_fail {m : String} : ¬ Stuck (.fail m) := fun h => nomatch h

macro "stuck_close" : tactic => `(tactic|
  all_goals try (first
    | exact RR.ofStuck ‹Stuck _› _
    | exact RV.ofStuck ‹Stuck _› _
    | exact ‹Stuck _›
    | exact ‹Stuck _ → Stuck _›
    | exact id
    | exact fun h => absurd h stuck_fail
    | (split <;> first | trivial | exact ‹Stuck _› | exact ‹Stuck _ → Stuck _› | exact id | done)))

theorem RR.not_oof {A : α → β → Prop} {r : R α} {r' : R β} (h : RR T U A r r') (hn : ¬ OOF r)
    (he : ∀ e, r ≠ .error e) : ¬ OOF r' := by
  rcases r with e | ⟨⟨c | a, σ⟩, τ⟩
  · exact absurd rfl (he e)
  all_goals rcases r' with e' | ⟨⟨c' | b, σ'⟩, τ'⟩ <;> simp only [RR, ExRel, false_and] at h
  · rw [OOF_err] at hn ⊢
    exact h.1.not_oof hn
  · exact not_OOF_ok

theorem not_oof_bind {x : EvalM PM α} {f : α → EvalM PM β} {σ : EvalState} {τ : Trace}
    (h : ¬ OOF (run (x >>= f) σ τ)) : ¬ OOF (run x σ τ) := by
  rw [run_bind] at h
  rcases r : run x σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;> rw [r] at h
  · exact not_OOF_error
  · dsimp only at h
    rw [OOF_err] at h ⊢
    exact h
  · exact not_OOF_ok

theorem not_oof_tryCatch {x : EvalM PM α} {h : Control → EvalM PM α} {σ : EvalState} {τ : Trace}
    (hk : KeepsOOF h) (hn : ¬ OOF (run (tryCatch x h) σ τ)) : ¬ OOF (run x σ τ) := by
  rw [run_tryCatch] at hn
  rcases r : run x σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;> rw [r] at hn
  · exact not_OOF_error
  · rw [OOF_err]
    rintro rfl
    exact hn (hk σ1 τ1)
  · exact not_OOF_ok

theorem FSH.mono {A : α → β → Prop} {x : EvalM PM α} {y y' : EvalM PM β} (h : FSH S T U A x y)
    (hl : Le y y') : FSH S T U A x y' := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have r := h.sim σ σ' τ τ' hs ht hn
  rcases hx : run x σ τ with e | v
  · rw [hx] at r
    rcases hy : run y σ' τ' with e' | v'
    · rw [hl.eq σ' τ' (by rw [hy]; exact not_OOF_error), hy]; rw [hy] at r; exact r
    · rw [hy] at r
      exact RR.ofStuck r _
  rw [hx] at r hn
  rw [hl.eq σ' τ' (r.not_oof hn (fun _ h => by cases h))]
  exact r

theorem FSH.weaken {A A' : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β} (h : FSH S T U A x y)
    (hA : ∀ a b, A a b → A' a b) : FSH S T U A' x y := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have r := h.sim σ σ' τ τ' hs ht hn
  revert r
  rcases run x σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;> rcases run y σ' τ' with e' | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;>
    simp only [RR, ExRel, imp_self, false_and]
  exact fun ⟨h1, h2, h3⟩ => ⟨hA _ _ h1, h2, h3⟩

theorem FS.mono {A : α → β → Prop} {x : EvalM PM α} {y y' : EvalM PM β} (h : FS S A x y)
    (hl : Le y y') : FS S A x y' := FSH.mono h hl

theorem FS.weaken {A A' : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β} (h : FS S A x y)
    (hA : ∀ a b, A a b → A' a b) : FS S A' x y := FSH.weaken h hA

def VRel {α : Type} (p : Prop) (a b : α) : Prop := p → a = b

theorem FS.vr {p : Prop} {x y : EvalM PM α} (h : FSH S T U Eq x y) : FSH S T U (VRel p) x y :=
  FSH.weaken h (fun _ _ h _ => h)

/-- `pure a` is simulated by `pure b` whenever the values are related by `A`: the states stay related
by `S.st` and the traces by `TrRel`. -/
theorem fs_pure {A : α → β → Prop} {a : α} {b : β} (h : A a b) : FSH S S U A (pure a) (pure b) := by
  refine ⟨fun σ σ' τ τ' hs ht _ => ?_⟩
  simp only [run_pure, RR, ExRel]
  exact ⟨h, hs, ht⟩

/-- `throw c` is simulated by `throw c` whenever `S` allows the control signal `c` to escape
(`S.ok c`). -/
theorem fs_throw {A : α → β → Prop} (c : Control) (hc : S.ok c := by trivial) :
    FS S A (throw c) (throw c) := by
  refine ⟨fun σ σ' τ τ' hs ht _ => ?_⟩
  simp only [run_throw, RR, ExRel]
  exact ⟨.inl ⟨.inl rfl, hc, hs⟩, ht⟩

theorem fs_throwR {A : α → β → Prop} {c c' : Control} (hc : S.ok c) (hr : CtlR S.ret c c') :
    FS S A (throw c) (throw c') := by
  refine ⟨fun σ σ' τ τ' hs ht _ => ?_⟩
  simp only [run_throw, RR, ExRel]
  exact ⟨.inl ⟨hr, hc, hs⟩, ht⟩

theorem fs_throwM {A : α → β → Prop} {L : String} (hL : S.ret = some L) (hc : S.ok (.return_ [])) :
    FS S A (throw (.return_ [])) (throw (.exit_ L)) :=
  fs_throwR hc (.inr (.inl ⟨L, hL, rfl, rfl⟩))

/-- `FSH` is preserved by `bind`. If `x` is simulated by `y` with values related by `A` and end states
related by `T`, and for all `A`-related values `a` and `b` the continuation `f a` is simulated by
`g b` starting from `T`-related states, then `x >>= f` is simulated by `y >>= g`. Escaping signals
are related by `U` in both parts. -/
theorem fs_bind {A : α → β → Prop} {B : γ → δ → Prop} {x : EvalM PM α} {y : EvalM PM β}
    {f : α → EvalM PM γ} {g : β → EvalM PM δ} (hx : FSH S T U A x y)
    (hf : ∀ a b, A a b → FSH T V U B (f a) (g b)) : FSH S V U B (x >>= f) (y >>= g) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have h0 := hx.sim σ σ' τ τ' hs ht (not_oof_bind hn)
  simp only [run_bind] at hn ⊢
  rcases r : run x σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;>
    rcases r' : run y σ' τ' with e' | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;> rw [r, r'] at h0 <;> rw [r] at hn <;>
    simp only [RR, ExRel, false_and] at h0 ⊢
  all_goals first
    | exact h0
    | exact RR.ofStuck h0 _
    | exact (hf _ _ h0.1).sim _ _ _ _ h0.2.1 h0.2.2 hn

def SimRel.atWin (U : SimRel) (v : Value) : SimRel := { U with st := U.win v }

theorem fs_noPre {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β} (h : ∀ σ σ', ¬ S.st σ σ') :
    FSH S T U A x y :=
  ⟨fun σ σ' _ _ hs => absurd hs (h σ σ')⟩

theorem TrRel.ev_eq {S S' : SimRel} (_h : S.ev = S'.ev) {τ τ' : Trace} (ht : TrRel S τ τ') : TrRel S' τ τ' := ht

theorem FSH.reg {S S' T T' U U' : SimRel} {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β}
    (h : FSH S' T' U' A x y) (hs : ∀ σ σ', S.st σ σ' → S'.st σ σ') (hse : S.ev = S'.ev)
    (ht : ∀ σ σ', T'.st σ σ' → T.st σ σ') (hte : T'.ev = T.ev)
    (hu : ∀ c c' σ σ', SigR U' c c' σ σ' → SigR U c c' σ σ') (hue : U'.ev = U.ev) : FSH S T U A x y := by
  refine ⟨fun σ σ' τ τ' hs0 ht0 hn => ?_⟩
  have r := h.sim σ σ' τ τ' (hs _ _ hs0) (ht0.ev_eq hse) hn
  revert r
  rcases run x σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;> rcases run y σ' τ' with e' | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;>
    simp only [RR, ExRel, imp_self, false_and]
  · exact fun ⟨h1, h2⟩ => ⟨hu _ _ _ _ h1, h2.ev_eq hue⟩
  · exact fun ⟨h1, h2, h3⟩ => ⟨h1, ht _ _ h2, h3.ev_eq hte⟩

theorem fs_throwW {A : α → β → Prop} (v : Value) :
    FSH (U.atWin v) T U A (throw (.return_ [v])) (throw (.return_ [])) := by
  refine ⟨fun σ σ' τ τ' hs ht _ => ?_⟩
  simp only [run_throw, RR, ExRel]
  exact ⟨.inr ⟨v, rfl, rfl, hs⟩, ht⟩

def reRef (q' : String) : R β → R β
  | .ok ((.error (.refused _), σ), τ) => .ok ((.error (.refused q'), σ), τ)
  | r => r

def RefFree (h : Control → EvalM PM β) : Prop :=
  ∀ q q' σ τ, run (h (.refused q')) σ τ = reRef q' (run (h (.refused q)) σ τ)

theorem RR.reRef {A : α → β → Prop} {a : R α} {b : R β} (q' : String) (h : RR T U A a b) :
    RR T U A a (reRef q' b) := by
  rcases b with e' | ⟨⟨c' | b, σ'⟩, τ'⟩
  · exact h
  · cases c' with
    | refused r' =>
      rw [show PassSemantics.reRef q' (.ok ((.error (.refused r'), σ'), τ') : R β) = .ok ((.error (.refused q'), σ'), τ') from rfl]
      rcases a with e | ⟨⟨c | a, σ⟩, τ⟩
      · exact h
      · simp only [RR, ExRel] at h ⊢
        obtain ⟨hs, ht⟩ := h
        refine ⟨?_, ht⟩
        rcases hs with ⟨hc, hok, hst⟩ | ⟨v, _, h2, _⟩
        · refine .inl ⟨?_, hok, hst⟩
          rcases hc with rfl | ⟨L, _, _, h2⟩ | ⟨r, _, rfl, _⟩
          · exact .inr (.inr ⟨_, _, rfl, rfl⟩)
          · cases h2
          · exact .inr (.inr ⟨_, _, rfl, rfl⟩)
        · cases h2
      · simp only [RR, ExRel] at h
        exact h.1.elim
    | _ => exact h
  · exact h

/-- `FSH` is preserved by `tryCatch`. If `x` is simulated by `y`, the handlers `h c` and `h' c` simulate
for every signal `c` that `U` lets escape, and `h` rethrows `outOfFuel` (`KeepsOOF h`), then
`tryCatch x h` is simulated by `tryCatch y h'`. `hm` covers a source `return` that the target turned
into `exit L` for the return label `L`; `hw` covers a source valued `return v` that the target turned
into a bare `return`; `hrf` says `h'` treats every refusal message alike. The defaults discharge
these when there is no return label, no valued return, and the handler is a plain rethrow or
`escapeSig`. -/
theorem fs_tryCatch {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β}
    {h : Control → EvalM PM α} {h' : Control → EvalM PM β} (hx : FSH S T U A x y)
    (hh : ∀ c, U.ok c → FSH U T V A (h c) (h' c)) (hk : KeepsOOF h)
    (hm : ∀ L, U.ret = some L → U.ok (.return_ []) → FSH U T V A (h (.return_ [])) (h' (.exit_ L)) := by
      intro L hL; cases hL)
    (hw : ∀ v, FSH (U.atWin v) T V A (h (.return_ [v])) (h' (.return_ [])) := by
      intro v; exact fs_noPre (fun _ _ h => False.elim h))
    (hrf : RefFree h' := by
      intro _ _ _ _; first
        | (simp [reRef, run_bind, run_modify, run_throw, run_get, run_pure]; done)
        | (rw [run_escapeSig_other (fun _ h => by cases h), run_escapeSig_other (fun _ h => by cases h)]; rfl)) :
    FSH S T V A (tryCatch x h) (tryCatch y h') := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have h0 := hx.sim σ σ' τ τ' hs ht (not_oof_tryCatch hk hn)
  simp only [run_tryCatch] at hn ⊢
  rcases r : run x σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;>
    rcases r' : run y σ' τ' with e' | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;> rw [r, r'] at h0 <;> rw [r] at hn <;>
    simp only [RR, ExRel, false_and] at h0 ⊢
  stuck_close
  · obtain ⟨hsg, ht1⟩ := h0
    rcases hsg with ⟨hcr, hok, hs1⟩ | ⟨v, rfl, rfl, hw1⟩
    · rcases hcr with rfl | ⟨L, hL, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
      · exact (hh c hok).sim σ1 σ1' τ1 τ1' hs1 ht1 hn
      · exact (hm L hL hok).sim σ1 σ1' τ1 τ1' hs1 ht1 hn
      · rw [hrf _ _ σ1' τ1']
        exact RR.reRef _ ((hh _ hok).sim σ1 σ1' τ1 τ1' hs1 ht1 hn)
    · exact (hw v).sim σ1 σ1' τ1 τ1' hw1 ht1 hn
  · exact h0

theorem run_wow_nil {s : StmtExprMd} {x : EvalM PM α} {σ : EvalState} (h : σ.operands = []) (τ : Trace) :
    run (withOperandWindow s x) σ τ = run x σ τ := by
  unfold withOperandWindow
  rw [run_bind, run_get]
  simp only [h]

theorem run_wow_site {s : StmtExprMd} {x : EvalM PM α} {σ : EvalState} (h : σ.operands = []) (ss : FileRange)
    (τ : Trace) : run (withOperandWindow s x) { σ with stmtSite := ss } τ = run x { σ with stmtSite := ss } τ :=
  run_wow_nil (σ := { σ with stmtSite := ss }) h τ

theorem FSH.wowL {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β} {s : StmtExprMd}
    (hS : ∀ σ σ', S.st σ σ' → σ.operands = []) (h : FSH S T U A x y) :
    FSH S T U A (withOperandWindow s x) y :=
  ⟨fun σ σ' τ τ' hs ht hn => by
    rw [run_wow_nil (hS σ σ' hs)] at hn ⊢
    exact h.sim σ σ' τ τ' hs ht hn⟩

theorem FSH.wowR {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β} {t : StmtExprMd}
    (hS : ∀ σ σ', S.st σ σ' → σ'.operands = []) (h : FSH S T U A x y) :
    FSH S T U A x (withOperandWindow t y) :=
  ⟨fun σ σ' τ τ' hs ht hn => by
    rw [run_wow_nil (hS σ σ' hs)]
    exact h.sim σ σ' τ τ' hs ht hn⟩

theorem FSH.wowRb {A : α → γ → Prop} {x : EvalM PM α} {y : EvalM PM β} {k : β → EvalM PM γ}
    {t : StmtExprMd} (hS : ∀ σ σ', S.st σ σ' → σ'.operands = []) (h : FSH S T U A x (y >>= k)) :
    FSH S T U A x (withOperandWindow t y >>= k) :=
  ⟨fun σ σ' τ τ' hs ht hn => by
    rw [run_bind, run_wow_nil (hS σ σ' hs), ← run_bind]
    exact h.sim σ σ' τ τ' hs ht hn⟩

theorem FSH.wow {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β} {s t : StmtExprMd}
    (hS : ∀ σ σ', S.st σ σ' → σ.operands = [] ∧ σ'.operands = []) (h : FSH S T U A x y) :
    FSH S T U A (withOperandWindow s x) (withOperandWindow t y) :=
  ⟨fun σ σ' τ τ' hs ht hn => by
    obtain ⟨h1, h2⟩ := hS σ σ' hs
    rw [run_wow_nil h1] at hn ⊢
    rw [run_wow_nil h2]
    exact h.sim σ σ' τ τ' hs ht hn⟩

/-- `get` is simulated by `get`: the two returned states are the current states, so they are related
by `S.st`. -/
theorem fs_get : FSH S S U S.st get get := by
  refine ⟨fun σ σ' τ τ' hs ht _ => ?_⟩
  simp only [run_get, RR, ExRel]
  exact ⟨hs, hs, ht⟩

/-- `modify f` is simulated by `modify g` whenever `f` and `g` map states related by `S.st` to states
related by `S.st`. -/
theorem fs_modify {f g : EvalState → EvalState} (h : ∀ σ σ', S.st σ σ' → S.st (f σ) (g σ')) :
    FSH S S U (fun _ _ => True) (modify f : EvalM PM PUnit) (modify g) := by
  refine ⟨fun σ σ' τ τ' hs ht _ => ?_⟩
  simp only [run_modify, RR, ExRel]
  exact ⟨trivial, h σ σ' hs, ht⟩

theorem fs_modifyTo {f g : EvalState → EvalState} (h : ∀ σ σ', S.st σ σ' → T.st (f σ) (g σ'))
    (he : S.ev = T.ev) : FSH S T U (fun _ _ => True) (modify f : EvalM PM PUnit) (modify g) := by
  refine ⟨fun σ σ' τ τ' hs ht _ => ?_⟩
  simp only [run_modify, RR, ExRel]
  exact ⟨trivial, h σ σ' hs, ht.ev_eq he⟩

theorem fs_fail {A : α → β → Prop} (msg msg' : String) :
    FSH S T U A (hostFail msg : EvalM PM α) (hostFail msg') := by
  refine ⟨fun σ σ' τ τ' _ _ _ => ?_⟩
  show RR T U A (.error (.fail msg)) (.error (.fail msg'))
  exact fun h => absurd h stuck_fail

theorem fs_stuck {A : α → β → Prop} (msg msg' : String) :
    FSH S T U A (stuckError msg : EvalM PM α) (stuckError msg') := by
  refine ⟨fun σ σ' τ τ' _ _ _ => ?_⟩
  show RR T U A (.error (.stuck msg)) (.error (.stuck msg'))
  exact fun _ => .mk msg

def PConst (X : PM α) : Prop := (∃ a, ∀ τ, X τ = .ok (a, τ)) ∨ (∃ e, ∀ τ, X τ = .error e)

theorem pconst_pure (a : α) : PConst (pure a : PM α) := .inl ⟨a, fun _ => rfl⟩

theorem pconst_fail (m : String) : PConst (InterpHost.fail m : PM α) := .inr ⟨.fail m, fun _ => rfl⟩

theorem pconst_stuck (m : String) : PConst (InterpHost.stuck m : PM α) := .inr ⟨.stuck m, fun _ => rfl⟩

theorem pconst_opIllTyped (args : List Value) (m : String) : PConst (opIllTyped args m : PM Value) := by
  unfold opIllTyped
  exact pconst_stuck _

theorem run_lift (x : PM α) (σ : EvalState) (τ : Trace) :
    run (liftM x : EvalM PM α) σ τ = match x τ with
      | .error e => .error e
      | .ok (a, τ') => .ok ((.ok a, σ), τ') := by
  rcases hx : x τ with e | ⟨a, τ'⟩ <;>
    simp [run, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, StateT.lift,
      Functor.map, StateT.map, StateT.bind, bind, Except.bind, hx, StateT.run, ExceptT.run, pure,
      StateT.pure, Except.pure]

/-- Lifting a host action `X` into the interpreter monad is simulated by lifting the same action,
with equal results, provided `X` gives the same result for every trace and leaves it unchanged
(`PConst X`). -/
theorem fs_liftM {X : PM α} (hX : PConst X) : FSH S S U Eq (liftM X : EvalM PM α) (liftM X) := by
  refine ⟨fun σ σ' τ τ' hs ht _ => ?_⟩
  rcases hX with ⟨a, ha⟩ | ⟨e, he⟩
  · simp only [run_lift, ha, RR, ExRel]
    exact ⟨trivial, hs, ht⟩
  · simp only [run_lift, he, RR]
    exact id

/-- `emitEvent e` is simulated by `emitEvent e'` whenever `e` and `e'` are related by `S.ev` and every
pair of events related by `S.ev` counts as a failed check on both sides or on neither (`failOf`),
so the traces keep the same number of failed checks. -/
theorem fs_emit {e e' : Event} (hS : ∀ e e', S.ev e e' → failOf e = failOf e') (h : S.ev e e') :
    FSH S S U (fun _ _ => True) (emitEvent e : EvalM PM Unit) (emitEvent e') := by
  refine ⟨fun σ σ' τ τ' hs ht _ => ?_⟩
  show RR S U _ (.ok ((.ok (), σ), { τ with events := τ.events.push e }))
    (.ok ((.ok (), σ'), { τ' with events := τ'.events.push e' }))
  refine ⟨trivial, hs, ?_, ht.2⟩
  simp only [Array.toList_push, nFail_concat]
  rw [ht.1, hS e e' h]

theorem fs_emitE {e e' : Event} (hS : ∀ e e', S.ev e e' → failOf e = failOf e') (h : S.ev e e') :
    FSH S S U Eq (emitEvent e : EvalM PM Unit) (emitEvent e') :=
  (fs_emit hS h).weaken (fun _ _ _ => rfl)

theorem fs_emitR {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β} {e' : Event} (hf : failOf e' = 0)
    (h : FSH S T U A x y) : FSH S T U A x (emitEvent e' >>= fun _ => y) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have ht' : TrRel S τ { τ' with events := τ'.events.push e' } := by
    refine ⟨?_, ht.2⟩
    simp only [Array.toList_push, nFail_concat, hf, Nat.add_zero]
    exact ht.1
  have hr : run (emitEvent e' >>= fun _ => y) σ' τ' = run y σ' { τ' with events := τ'.events.push e' } := by
    rw [run_bind]; rfl
  rw [hr]
  exact h.sim σ σ' τ _ hs ht' hn

/-- `FS` with equal values is preserved by `Functor.map`: if `x` is simulated by `x'` with equal
values, then so is `f <$> x` by `f <$> x'`. -/
theorem fs_map {x x' : EvalM PM α} (f : α → β) (h : FS S Eq x x') :
    FS S Eq (f <$> x) (f <$> x') := by
  simp only [map_eq_pure_bind]
  exact fs_bind h (fun a b hab => by subst hab; exact fs_pure rfl)

/-- `chooseValue ty d` is simulated by `chooseValue ty' d` with equal values, even when the type hints
`ty` and `ty'` differ: related traces have the same oracle at the same position, and the oracle
ignores type hints (`Blind`). -/
theorem fs_choose (ty ty' : Option HighType) (d : Value) :
    FSH S S U Eq (chooseValue ty d : EvalM PM Value) (chooseValue ty' d) := by
  refine ⟨fun σ σ' τ τ' hs ht _ => ?_⟩
  show RR S U Eq (.ok ((.ok (τ.oracle τ.next ty d), σ), { τ with next := τ.next + 1 }))
    (.ok ((.ok (τ'.oracle τ'.next ty' d), σ'), { τ' with next := τ'.next + 1 }))
  obtain ⟨he, ho, hb, hnx⟩ := ht
  refine ⟨?_, hs, he, ho, hb, by simp only [hnx]⟩
  show τ.oracle τ.next ty d = τ'.oracle τ'.next ty' d
  rw [← (Prod.mk.inj ho).1, ← hnx]
  exact hb _ _ _ _

theorem fs_chooseInit (k : String) (ty ty' : Option HighType) (d : Value) :
    FSH S S U Eq (liftM (InterpHost.chooseInit k ty d : PM Value) : EvalM PM Value)
      (liftM (InterpHost.chooseInit k ty' d : PM Value)) := by
  refine ⟨fun σ σ' τ τ' hs ht _ => ?_⟩
  show RR S U Eq (.ok ((.ok ((τ.init k).getD d), σ), τ)) (.ok ((.ok ((τ'.init k).getD d), σ'), τ'))
  have hi : τ.init = τ'.init := (Prod.mk.inj (Prod.mk.inj ht.2.1).2).1
  exact ⟨by show (τ.init k).getD d = (τ'.init k).getD d; rw [hi], hs, ht⟩

theorem fs_chooseHeap (h : Array HeapObject) :
    FSH S S U Eq (liftM (InterpHost.chooseHeap h : PM (Array HeapObject)) : EvalM PM (Array HeapObject))
      (liftM (InterpHost.chooseHeap h : PM (Array HeapObject))) := by
  refine ⟨fun σ σ' τ τ' hs ht _ => ?_⟩
  show RR S U Eq (.ok ((.ok (τ.heap0.getD h), σ), τ)) (.ok ((.ok (τ'.heap0.getD h), σ'), τ'))
  have hi : τ.heap0 = τ'.heap0 := (Prod.mk.inj (Prod.mk.inj ht.2.1).2).2
  exact ⟨by show τ.heap0.getD h = τ'.heap0.getD h; rw [hi], hs, ht⟩

theorem run_escapeSig_throw {P : Procedure} (h : P.throwsType.isNone = true) (v : Value) (σ : EvalState) (τ : Trace) :
    run (escapeSig P (.throw_ v) : EvalM PM α) σ τ =
      .ok ((.error .infeasible, { σ with assertFailures := σ.assertFailures.push (escapeMsg P v) }),
        { τ with events := τ.events.push (.check .assert none (escapeMsg P v) false
          { σ with stack := {}, cursor := [], seek := none, coroSelf := none, entryState := none }) }) := by
  simp only [escapeSig, h, ite_true]
  rfl

theorem run_checkExcType (ty : HighType) (v : Value) (σ : EvalState) (τ : Trace) :
    run (checkExcType ty v : EvalM PM Unit) σ τ =
      if excTypeOK σ v ty then .ok ((.ok (), σ), τ)
      else .error (.stuck s!"exception {v.display} is not a '{toString (formatHighTypeVal ty)}'") := by
  unfold checkExcType
  simp only [run_bind, run_get]
  split <;> rfl

theorem run_escapeSig_other {P : Procedure} {c : Control} (h : ∀ v, c = .throw_ v → False)
    (σ : EvalState) (τ : Trace) : run (escapeSig P c : EvalM PM α) σ τ = .ok ((.error c, σ), τ) := by
  cases c with
  | throw_ v => exact (h v rfl).elim
  | _ => rfl

theorem run_escapeSig_some {P : Procedure} {t : HighTypeMd} (h : P.throwsType = some t) (v : Value)
    (σ : EvalState) (τ : Trace) :
    run (escapeSig P (.throw_ v) : EvalM PM α) σ τ =
      if excTypeOK σ v t.val then .ok ((.error (.throw_ v), σ), τ)
      else .error (.stuck s!"exception {v.display} is not a '{toString (formatHighTypeVal t.val)}'") := by
  simp only [escapeSig, h, Option.isNone_some, Bool.false_eq_true, ite_false]
  rw [run_bind, run_checkExcType]
  by_cases hk : excTypeOK σ v t.val = true <;> simp only [hk, ite_true, ite_false, Bool.false_eq_true] <;> rfl

theorem run_escapeSig_ok_or_stuck (P : Procedure) (c : Control) (σ : EvalState) (τ : Trace) :
    (∃ q, run (escapeSig P c : EvalM PM α) σ τ = .ok q) ∨ ∃ m, run (escapeSig P c : EvalM PM α) σ τ = .error (.stuck m) := by
  cases c with
  | throw_ v =>
    cases ht : P.throwsType with
    | none => exact .inl ⟨_, run_escapeSig_throw (by simp [ht]) v σ τ⟩
    | some t =>
      rw [run_escapeSig_some ht]
      split
      · exact .inl ⟨_, rfl⟩
      · exact .inr ⟨_, rfl⟩
  | _ => exact .inl ⟨_, run_escapeSig_other (fun _ h => by cases h) σ τ⟩

def ExcOK (S : SimRel) (P P' : Procedure) : Prop :=
  ∀ σ σ' v t, S.st σ σ' → P.throwsType = some t → ∃ t', P'.throwsType = some t' ∧ excTypeOK σ' v t'.val = excTypeOK σ v t.val

/-- Wrapping a procedure body in its escape handler preserves `FSH`. If `x` is simulated by `y`, then
`tryCatch x (escapeSig P)` is simulated by `tryCatch y (escapeSig P')`. The hypotheses say that `P`
and `P'` both declare an exception type or both do not, that when `P` declares one so does `P'` and
the two give the same type test in related states (`ExcOK`), that `U` lets `infeasible` escape, and
that `U.st` survives recording one more assertion failure on each side. -/
theorem fs_escape {P P' : Procedure} (ht : P'.throwsType.isNone = P.throwsType.isNone) (hx : ExcOK U P P')
    {A : α → β → Prop}
    {x : EvalM PM α} {y : EvalM PM β} (h : FSH S T U A x y) (hok : U.ok .infeasible)
    (hU : ∀ σ σ' f f', U.st σ σ' → U.st { σ with assertFailures := σ.assertFailures.push f }
      { σ' with assertFailures := σ'.assertFailures.push f' }) :
    FSH S T U A (tryCatch x (escapeSig P)) (tryCatch y (escapeSig P')) := by
  refine ⟨fun σ σ' τ τ' hs ht0 hn => ?_⟩
  rw [run_tryCatch] at hn ⊢
  rw [run_tryCatch]
  have hn0 : ¬ OOF (run x σ τ) := by
    intro ho
    apply hn
    rcases r : run x σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;> rw [r] at ho
    · exact absurd ho not_OOF_error
    · rw [OOF_err] at ho; subst ho
      dsimp only
      rw [run_escapeSig_other (fun v h => by cases h)]
      exact OOF_err.mpr rfl
    · exact absurd ho not_OOF_ok
  have h0 := h.sim σ σ' τ τ' hs ht0 hn0
  rcases r : run x σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;>
    rcases r' : run y σ' τ' with e' | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;> rw [r, r'] at h0 <;> dsimp only
  · exact h0
  · exact RR.ofStuck h0 _
  · exact h0
  · exact h0.elim
  · simp only [RR, ExRel] at h0
    obtain ⟨hsg, htr⟩ := h0
    rcases hsg with ⟨hcr, hokc, hst⟩ | ⟨v, rfl, rfl, hw⟩
    · rcases hcr with rfl | ⟨L, hL, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
      · cases c with
        | throw_ v =>
          cases hb : P.throwsType.isNone
          · obtain ⟨t, htt⟩ := Option.isSome_iff_exists.mp (by simpa using hb)
            obtain ⟨t', htt', hxe⟩ := hx σ1 σ1' v t hst htt
            rw [run_escapeSig_some htt, run_escapeSig_some htt', hxe]
            split
            · exact ⟨.inl ⟨.inl rfl, hokc, hst⟩, htr⟩
            · exact fun _ => ⟨_⟩
          · rw [run_escapeSig_throw hb, run_escapeSig_throw (by rw [ht, hb])]
            refine ⟨.inl ⟨.inl rfl, hok, hU _ _ _ _ hst⟩, ?_⟩
            refine ⟨?_, htr.2⟩
            simp only [Array.toList_push, nFail_concat]
            rw [htr.1]
            rfl
        | _ =>
          rw [run_escapeSig_other (fun _ h => by cases h), run_escapeSig_other (fun _ h => by cases h)]
          exact ⟨.inl ⟨.inl rfl, hokc, hst⟩, htr⟩
      · rw [run_escapeSig_other (fun _ h => by cases h), run_escapeSig_other (fun _ h => by cases h)]
        exact ⟨.inl ⟨.inr (.inl ⟨L, hL, rfl, rfl⟩), hokc, hst⟩, htr⟩
      · rw [run_escapeSig_other (fun _ h => by cases h), run_escapeSig_other (fun _ h => by cases h)]
        exact ⟨.inl ⟨.inr (.inr ⟨_, _, rfl, rfl⟩), hokc, hst⟩, htr⟩
    · rw [run_escapeSig_other (fun _ h => by cases h), run_escapeSig_other (fun _ h => by cases h)]
      exact ⟨.inr ⟨v, rfl, rfl, hw⟩, htr⟩
  · simp only [RR, ExRel, false_and] at h0
  · exact h0.elim
  · simp only [RR, ExRel, false_and] at h0
  · exact h0

/-- `FS` is preserved by `List.forM`: if the lists `l` and `l'` are related pointwise by `R` (`L2`) and
`f a` is simulated by `g b` for all `R`-related elements, then `l.forM f` is simulated by
`l'.forM g`. -/
theorem fs_forM {R : β → γ → Prop} {l : List β} {l' : List γ} (hl : L2 R l l')
    {f : β → EvalM PM PUnit} {g : γ → EvalM PM PUnit}
    (h : ∀ a b, R a b → FS S (fun _ _ => True) (f a) (g b)) :
    FS S (fun _ _ => True) (l.forM f) (l'.forM g) := by
  induction hl with
  | nil => exact fs_pure (A := fun _ _ => True) trivial
  | cons hab _ ih => exact fs_bind (h _ _ hab) (fun _ _ _ => ih)

/-- `FS` with equal values is preserved by `List.mapM`: if `l` and `l'` are related pointwise by `R`
and `f a` is simulated by `g b` with equal values for all `R`-related elements, then `l.mapM f` is
simulated by `l'.mapM g` with equal result lists. -/
theorem fs_mapM {R : β → γ → Prop} {l : List β} {l' : List γ} (hl : L2 R l l')
    {f : β → EvalM PM δ} {g : γ → EvalM PM δ} (h : ∀ a b, R a b → FS S Eq (f a) (g b)) :
    FS S Eq (l.mapM f) (l'.mapM g) := by
  induction hl with
  | nil => exact fs_pure rfl
  | cons hab _ ih =>
    simp only [List.mapM_cons]
    refine fs_bind (h _ _ hab) (fun a b hab' => fs_bind ih (fun as bs has => fs_pure ?_))
    rw [hab', has]

/-- `FS` is preserved by `List.mapM` with pointwise related results: if `l` and `l'` are related
pointwise by `R` and `f a` is simulated by `g b` with values related by `Q` for all `R`-related
elements, then `l.mapM f` is simulated by `l'.mapM g` with result lists related pointwise by `Q`. -/
theorem fs_mapM_L2 {R : β → γ → Prop} {Q : δ → ε → Prop} {l : List β} {l' : List γ} (hl : L2 R l l')
    {f : β → EvalM PM δ} {g : γ → EvalM PM ε} (h : ∀ a b, R a b → FS S Q (f a) (g b)) :
    FS S (L2 Q) (l.mapM f) (l'.mapM g) := by
  induction hl with
  | nil => exact fs_pure .nil
  | cons hab _ ih =>
    simp only [List.mapM_cons]
    exact fs_bind (h _ _ hab) (fun a b hab' => fs_bind ih (fun as bs has => fs_pure (.cons hab' has)))

/-- `FS` with equal values is preserved by `forIn` over lists: if `l` and `l'` are related pointwise by
`R` and `f a c` is simulated by `g a' c` with equal results for all `R`-related elements and every
accumulator `c`, then `forIn l b f` is simulated by `forIn l' b g` with equal results. -/
theorem fs_forIn {R : β → γ → Prop} {l : List β} {l' : List γ} (hl : L2 R l l')
    {b : δ} {f : β → δ → EvalM PM (ForInStep δ)} {g : γ → δ → EvalM PM (ForInStep δ)}
    (h : ∀ a a', R a a' → ∀ c, FS S Eq (f a c) (g a' c)) :
    FS S Eq (forIn l b f) (forIn l' b g) := by
  induction hl generalizing b with
  | nil => exact fs_pure rfl
  | cons hab _ ih =>
    simp only [List.forIn_cons]
    refine fs_bind (h _ _ hab b) (fun r r' hr => ?_)
    subst hr
    cases r with
    | done c => exact fs_pure rfl
    | yield c => exact ih

/-- `FSH` is preserved by `if`: if `x` is simulated by `y` when `c` holds and `x'` by `y'` when it does
not, then `if c then x else x'` is simulated by `if c then y else y'`. -/
theorem fs_ite {A : α → β → Prop} {c : Prop} [Decidable c] {x x' : EvalM PM α} {y y' : EvalM PM β}
    (hx : c → FSH S T U A x y) (hy : ¬ c → FSH S T U A x' y') :
    FSH S T U A (if c then x else x') (if c then y else y') := by
  split
  · exact hx ‹_›
  · exact hy ‹_›

def MuteSt (σ a : EvalState) : EvalState := { a with assertFailures := σ.assertFailures, muted := σ.muted }

theorem fsh_muteE {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β} (h : FSH S T U A x y)
    (hS : ∀ σ σ', S.st σ σ' → S.st { σ with muted := true } { σ' with muted := true })
    (hT : ∀ σ σ' a a', S.st σ σ' → T.st a a' → T.st (MuteSt σ a) (MuteSt σ' a'))
    (hU : ∀ σ σ' c c' a a', S.st σ σ' → SigR U c c' a a' → SigR U c c' (MuteSt σ a) (MuteSt σ' a')) :
    FSH S T U A (muteE x) (muteE y) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  rw [run_muteE, OOF_muteR] at hn
  rw [run_muteE, run_muteE]
  have h0 := h.sim _ _ τ τ' (hS _ _ hs) ht hn
  rcases r : run x { σ with muted := true } τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;>
    rcases r' : run y { σ' with muted := true } τ' with e' | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;> rw [r, r'] at h0 <;>
    simp only [RR, ExRel, muteR, false_and] at h0 ⊢
  stuck_close
  · exact ⟨hU _ _ _ _ _ _ hs h0.1, ⟨ht.1, h0.2.2.1, h0.2.2.2.1, h0.2.2.2.2⟩⟩
  · exact ⟨h0.1, hT _ _ _ _ hs h0.2.1, ⟨ht.1, h0.2.2.2.1, h0.2.2.2.2.1, h0.2.2.2.2.2⟩⟩

theorem unalias_userDefined {ix : ProgramIndex} {n : Identifier} (h : ix.aliasMap[n.text]? = none) :
    ix.unalias (.UserDefined n) = .UserDefined n := by
  unfold ProgramIndex.unalias unaliasWith
  rw [resolveAliasType.eq_def]
  simp [Std.HashMap.get?_eq_getElem?, h]

theorem highTypeName_unalias {ix : ProgramIndex} {t : HighType} {n : String} (h : highTypeName? t = some n)
    (ha : ix.aliasMap[n]? = none) : highTypeName? (ix.unalias t) = some n := by
  cases t with
  | UserDefined x =>
    simp only [highTypeName?, Option.some.injEq] at h
    subst h
    rw [unalias_userDefined ha]
    rfl
  | Applied b args =>
    unfold ProgramIndex.unalias unaliasWith
    rw [resolveAliasType.eq_def]
    simp only [highTypeName?] at h
    split at h
    · rename_i x hx
      simp only [Option.some.injEq] at h
      subst h
      simp only [hx, Std.HashSet.contains_empty, Bool.false_eq_true, ite_false, Std.HashMap.get?_eq_getElem?, ha,
        highTypeName?]
    · cases h
  | _ => simp [highTypeName?] at h

end Strata.Laurel.PassSemantics
