/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Counterexample.BackLink
public import Strata.DL.Imperative.Counterexample.RunProps
import all Strata.DL.Imperative.Counterexample.Run
import all Strata.DL.Imperative.Counterexample.BackLink

/-! # Properties of back-links and their composition

Key theorems:
- `composeBackLinks_cons_eq`: prepending a link composes it as the outermost `composeStep`.
- `composeTargeted_id`: with identity target maps, target-threading composition is
  `composeBackLinks`.
- `exactBackLink_preserves`: the replay-free back-link of an exact phase maps valid outcomes
  to valid outcomes.
-/

namespace Imperative

public section

/-- Prepending a link (in forward order) to a back-link chain composes it as the
    outermost `composeStep`, applied after the rest of the chain. -/
theorem composeBackLinks_cons_eq [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    (link : BackLink P CmdT CmdT) (links : List (BackLink P CmdT CmdT))
    (st : List (Stmt P CmdT)) (sts : List (List (Stmt P CmdT)))
    (initial : BackLinkOutcome P CmdT) :
    composeBackLinks (link :: links) (st :: sts) initial
      = composeStep st (composeBackLinks links sts initial) link := by
  simp only [composeBackLinks, List.zip_cons_cons, List.reverse_cons, List.foldl_append]
  rfl

/-- With identity target maps, `targetIn` returns the output target. -/
private theorem cel_targetIn_id [HasBool P] [DecidableEq P.Expr] [InterpLang P] {Tgt : Type}
    (l : List (Tgt → BackLink P CmdT CmdT)) (t : Tgt) :
    targetIn (l.map fun b => ({ build := b, upstream := id } : TargetedBackLink P CmdT Tgt)) t
      = t := by
  induction l <;> simp_all!

/-- With identity target maps, target-threading composition is `composeBackLinks`. -/
theorem composeTargeted_id [HasBool P] [DecidableEq P.Expr] [InterpLang P] {Tgt : Type}
    (build : List (Tgt → BackLink P CmdT CmdT)) (sts : List (List (Stmt P CmdT)))
    (t : Tgt) (initial : BackLinkOutcome P CmdT) (hlen : build.length = sts.length) :
    composeTargeted (build.map fun b => { build := b, upstream := id }) sts t initial
      = composeBackLinks (build.map fun b => b t) sts initial := by
  induction build generalizing sts <;> cases sts <;>
    simp_all! only [composeBackLinks_cons_eq, cel_targetIn_id, Nat.add_eq_zero_iff,
      Nat.succ_ne_self, and_false, Nat.right_eq_add, Nat.add_right_cancel_iff, id_eq]
  rfl

/-! ## Replay-free back-links of exact phases -/

namespace ExactCert

variable {P : PureExpr} [InterpLang P] {CmdT : Type} {WF : IConfig P CmdT → Prop}
  {T : List (Stmt P CmdT) → Option (List (Stmt P CmdT))} {Tgt : Type}
  {V' V : CexValidity P CmdT Tgt}

/-- A translated slice has a translated configuration and oracle. -/
private theorem backCex_eq_some {cert : ExactCert WF T V' V} {st : List (Stmt P CmdT)}
    {head : Bool} {c' c : CexA P CmdT} (h : cert.backCex st head c' = some c) :
    ∃ cfg, cert.backCfg st head c'.cfg = some cfg ∧
      c = ⟨cfg, cert.backOracle st c'.cfg c'.oracle⟩ := by grind [backCex, Option.map_eq_some_iff]

/-- Every element of a translated outcome's chain is the translation of an element of
    the incoming chain. -/
private theorem liftOutcome_chain (cert : ExactCert WF T V' V) (st : List (Stmt P CmdT))
    (o : BackLinkOutcome P CmdT) :
    ∀ x ∈ (cert.liftOutcome st o).chain,
      ∃ x' ∈ o.chain, ∃ head, cert.backCex st head x' = some x := by
  intro x hx
  rcases o with ⟨_ | _, _ | _⟩ <;>
    simp only [liftOutcome, Option.bind_some] at hx <;> (repeat' split at hx) <;>
    simp_all only [BackLinkOutcome.chain, BackLinkOutcome.empty, Option.toList_some,
      Option.mem_toList, Option.map_eq_some_iff, List.not_mem_nil, List.mem_append,
      List.mem_map] <;> grind

end ExactCert

/-- **Once-and-for-all validity of the replay-free back-link.**  A valid downstream
    outcome for target `t` translates to a valid upstream outcome for
    `cert.backTarget t`. -/
theorem exactBackLink_preserves {P : PureExpr} [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    {CmdT : Type} {WF : IConfig P CmdT → Prop}
    {T : List (Stmt P CmdT) → Option (List (Stmt P CmdT))}
    {Tgt : Type} {V' V : CexValidity P CmdT Tgt} (name : String) (cert : ExactCert WF T V' V) :
    ∀ st st', T st = some st' → ∀ (t : Tgt) (o : BackLinkOutcome P CmdT),
      ValidOutcomeWF WF V' t st' o →
      ValidOutcomeWF WF V (cert.backTarget t) st ((exactBackLink name cert).lift st o) := by
  intro st st' hT t ⟨sl, cl⟩ ⟨hhead, hclaim, hwf⟩
  have hwf' : ∀ x ∈ ((exactBackLink name cert).lift st ⟨sl, cl⟩).chain, WF x.cfg := fun x hx => by
    obtain ⟨x', hx', head, hback⟩ := cert.liftOutcome_chain st _ x hx
    obtain ⟨cfg, hcfg, rfl⟩ := ExactCert.backCex_eq_some hback
    exact cert.wf_back st st' hT head _ _ (hwf x' hx') hcfg
  revert hwf'
  rcases sl with _ | ⟨s, rest⟩
  · rcases cl with _ | ⟨c', f⟩
    · exact fun _ => validOutcome_empty_of
    simp only [exactBackLink, ExactCert.liftOutcome]
    split
    · exact fun _ => validOutcome_empty_of
    rename_i hb
    obtain ⟨cfg, hcfg, rfl⟩ := ExactCert.backCex_eq_some hb
    refine fun hw => ⟨fun _ hh => ?_, fun _ _ hc => ?_, hw⟩
    · cases hh
      exact cert.top_back st st' hT c' _ (hhead c' rfl) hcfg _
    · cases hc
      have hv := cert.claim_back st st' hT t f true c' _ (hwf c' (.head _)) (hclaim c' f rfl).1 hcfg
      exact ⟨hv, nofun⟩
  simp only [exactBackLink, ExactCert.liftOutcome]
  split
  · exact fun _ => validOutcome_empty_of
  rename_i hb
  obtain ⟨cfg, hcfg, rfl⟩ := ExactCert.backCex_eq_some hb
  refine fun hw => ⟨fun _ hh => ?_, fun c f hc => ?_, hw⟩
  · cases hh
    exact cert.top_back st st' hT s _ (hhead s rfl) hcfg _
  obtain ⟨⟨c', f'⟩, rfl, hc⟩ := Option.bind_eq_some_iff.1 hc
  obtain ⟨c0, hb', hc⟩ := Option.map_eq_some_iff.1 hc
  cases hc
  obtain ⟨cfg', hcfg', rfl⟩ := ExactCert.backCex_eq_some hb'
  obtain ⟨hv, hnt⟩ := hclaim c' f' rfl
  have hw' := hwf c' (List.mem_append_right _ (.head _))
  exact ⟨cert.claim_back st st' hT t f' false c' _ hw' hv hcfg',
    fun _ => cert.nontop_back st st' hT c' _ (hnt nofun) hcfg' _⟩
where
  /-- The empty outcome is valid. -/
  validOutcome_empty_of {W : CexValidity P CmdT Tgt} {u : Tgt} {s : List (Stmt P CmdT)} :
      ValidOutcomeWF WF W u s (BackLinkOutcome.empty : BackLinkOutcome P CmdT) :=
    ⟨fun _ => nofun, fun _ _ => nofun, fun _ => nofun⟩


end -- public section

end Imperative
