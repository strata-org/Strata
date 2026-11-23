/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.LangDef
public import Strata.Transform.Specification
import all Strata.Languages.Cortex.Module
import Strata.DL.Imperative.CFGSemanticsProps

/-! # Properties of the Cortex event-trace language

## Key theorems

- `cortex_traceStar_iff_cfg`: the bridge to Imperative's CFG relation. On an entry frame
  whose body has no handlers and only base commands, and no postconditions, a Cortex run to
  `terminal` is exactly a run of `StepCFGE` with `EvalCmdE` on the erased CFG, its events
  wrapped by `CEvent.std`.
- `EventLang.eraseEvents_traceStar`, `EventLang.liftStd_traceStar`: the runs of the
  adapted languages are the runs of the original ones, with their traces erased or lifted.
- `OverapproximatesTraces2UptoWhen.eraseEvents`: an overapproximation between Cortex
  languages up to lifted trace relations is one between their erased languages, so the
  framework's validity transfer lemmas apply to Cortex.
-/

namespace Cortex.Sem

open Imperative Lambda Strata.Logic Imperative.Specification.Transform

public section

/-! ## Event adapters -/

/-- A run of a relation whose steps emit `F e` for the events `e` of a step of `r` is a
run of `r` whose trace maps to its trace, when `F` maps concatenation to concatenation. -/
private theorem reflTransTrace_mapEvents {A E E' : Type _} {r : A → List E → A → Prop}
    {F : List E → List E'} (hnil : F [] = []) (happ : ∀ a b, F (a ++ b) = F a ++ F b)
    {c τ c'} :
    ReflTransTrace (fun c e c' => ∃ e₀, r c e₀ c' ∧ e = F e₀) c τ c' ↔
      ∃ τ₀, ReflTransTrace r c τ₀ c' ∧ τ = F τ₀ := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], .refl _, hnil.symm⟩
    | step _ _ _ _ _ hs _ ih =>
      obtain ⟨e₀, hs, rfl⟩ := hs
      obtain ⟨τ₀, h, rfl⟩ := ih
      exact ⟨e₀ ++ τ₀, .step _ _ _ _ _ hs h, (happ _ _).symm⟩
  · rintro ⟨τ₀, h, rfl⟩
    induction h with
    | refl => exact hnil ▸ .refl _
    | step _ _ _ _ _ hs _ ih => exact happ _ _ ▸ .step _ _ _ _ _ ⟨_, hs, rfl⟩ ih

/-- The runs of a Cortex language with its traces erased are its runs, with their traces
erased by `CEvent.erase`. -/
theorem EventLang.eraseEvents_traceStar {L : EventLang Core.Expression CEvent}
    {c c' : L.CfgT} {τ : Trace Core.Expression} :
    (EventLang.eraseEvents L).traceStar c τ c' ↔
      ∃ τ', L.traceStar c τ' c' ∧ τ = τ'.flatMap CEvent.erase :=
  reflTransTrace_mapEvents rfl (fun _ _ => List.flatMap_append)

/-- The runs of a Core language with its events lifted are its runs, with their events
wrapped by `CEvent.std`. -/
theorem EventLang.liftStd_traceStar {L : EventLang Core.Expression (Event Core.Expression)}
    {c c' : L.CfgT} {τ : List CEvent} :
    (EventLang.liftStd L).traceStar c τ c' ↔ ∃ τ₀, L.traceStar c τ₀ c' ∧ τ = τ₀.map .std :=
  reflTransTrace_mapEvents rfl (fun _ _ => List.map_append)

/-- Erasing a lifted Core trace gives the trace back. -/
private theorem CEvent.flatMap_erase_map_std (τ : Trace Core.Expression) :
    (τ.map CEvent.std).flatMap CEvent.erase = τ := by
  induction τ with
  | nil => rfl
  | cons e τ ih => exact congrArg (e :: ·) ih

/-- On lifted Core traces, a lifted relation is the relation itself. -/
theorem CEvent.liftRel_map_std {R : Relation (Trace Core.Expression)}
    {τ τ' : Trace Core.Expression} :
    CEvent.liftRel R (τ.map .std) (τ'.map .std) ↔ R τ τ' := by
  simp only [CEvent.liftRel, CEvent.flatMap_erase_map_std]

/-- An overapproximation between Cortex languages up to the lifts of two Core trace
relations is an overapproximation between their erased languages up to those
relations. -/
theorem OverapproximatesTraces2UptoWhen.eraseEvents
    {R R' : Relation (Trace Core.Expression)} {Rin Rout : Relation (Imperative.Env Core.Expression)}
    {L₁ L₂ : EventLang Core.Expression CEvent} {T : L₁.StmtT → Option L₂.StmtT}
    {pre : L₁.StmtT → Prop} {params₁ : L₁.InitEnvWFParamsTy} {params₂ : L₂.InitEnvWFParamsTy}
    (h : OverapproximatesTraces2UptoWhen (CEvent.liftRel R) (CEvent.liftRel R') Rin Rout
      L₁ L₂ T pre params₁ params₂) :
    OverapproximatesTraces2UptoWhen R R' Rin Rout (EventLang.eraseEvents L₁)
      (EventLang.eraseEvents L₂) T pre params₁ params₂ := by
  intro st st' hT hpre ρ₀ ρ₀' hin hwf
  obtain ⟨hpfx, hterm, hexit, hwf'⟩ := h st st' hT hpre ρ₀ ρ₀' hin hwf
  refine ⟨fun cfg tr htr => ?_, fun ρ' tr htr => ?_, fun lbl ρ' tr htr => ?_, hwf'⟩
  · obtain ⟨τ, hτ, rfl⟩ := EventLang.eraseEvents_traceStar.1 htr
    obtain ⟨cfg', τ', h', hR⟩ := hpfx cfg τ hτ
    exact ⟨cfg', _, EventLang.eraseEvents_traceStar.2 ⟨τ', h', rfl⟩, hR⟩
  · obtain ⟨τ, hτ, rfl⟩ := EventLang.eraseEvents_traceStar.1 htr
    obtain ⟨ρ'', τ', h', hout, hR⟩ := hterm ρ' τ hτ
    exact ⟨ρ'', _, EventLang.eraseEvents_traceStar.2 ⟨τ', h', rfl⟩, hout, hR⟩
  · obtain ⟨τ, hτ, rfl⟩ := EventLang.eraseEvents_traceStar.1 htr
    obtain ⟨ρ'', τ', h', hout, hR⟩ := hexit lbl ρ' τ hτ
    exact ⟨ρ'', _, EventLang.eraseEvents_traceStar.2 ⟨τ', h', rfl⟩, hout, hR⟩

/-! ## Bridge to Imperative's CFG relation -/

/-- Looking up a label in blocks mapped blockwise finds the mapped block. -/
private theorem lookup_map_snd {β γ : Type} (F : β → γ) (t : String) (bs : List (String × β)) :
    List.lookup t (bs.map fun (l, b) => (l, F b)) = (List.lookup t bs).map F := by
  induction bs with
  | nil => rfl
  | cons p bs ih =>
    obtain ⟨l, b⟩ := p
    simp only [List.map_cons, List.lookup_cons]
    split <;> simp [ih]

/-- With no checks of a normal return, the commands the relation runs for a block of base
commands are its commands with their constraint checks. -/
private theorem blockCmds_liftBlock {Γ : UnorderedProgram} {fr : Fr} (hx : fr.exits = [])
    (b : DetBlock Label (Cmd Core.Expression) Core.Expression) :
    fr.blockCmds Γ (liftBlock b) = (b.cmds.flatMap (checkedBaseCmd Γ fr.vars)).map .cmd := by
  simp only [Fr.blockCmds, liftBlock, hx, List.map_nil, List.flatMap_map, List.map_flatMap,
    checkedCmd]
  cases b.transfer <;> simp

/-- A base command's step whose writes are safe references in the heap `h`: the step of
`EvalCmdE`, where every value the command binds differently is `Null` or allocated in `h`
(`SafeRef`). This is the base-command step the relation takes in a state whose heap is `h`. -/
@[expose] def SafeEvalCmdE (h : SemValue) : EvalCmdParamE Core.Expression (Cmd Core.Expression)
    (Event Core.Expression) :=
  fun f σ c σ' evs => EvalCmdE Core.Expression f σ c σ' evs ∧
    ∀ x v, σ' x = some v → σ x ≠ some v → SafeRef f h v

/-- The configurations of a Cortex run of the frame `fr` over `liftCFG g`, with the heap
`h`, and of the CFG run over `eraseCFG Γ g` that correspond: the same label, commands and
environment, a normal return corresponding to the CFG's end. -/
private inductive BridgeRel (Γ : UnorderedProgram)
    (g : DetCFG Core.Expression (Cmd Core.Expression))
    (fr : Fr) (h : SemValue) :
    CConfig → CFGConfig String (Cmd Core.Expression) Core.Expression → Prop where
  | atBlock (t : Label) (ρ : Imperative.Env Core.Expression) :
      BridgeRel Γ g fr h (.atBlock fr t ⟨ρ, h⟩) (.atBlock (eraseCFG Γ g) t ρ)
  | inBlock (t : Label) (cs : List (Cmd Core.Expression))
      (tr : DetTransferCmd Label Core.Expression) (ρ : Imperative.Env Core.Expression) :
      BridgeRel Γ g fr h (.inBlock fr t (cs.map .cmd) tr ⟨ρ, h⟩)
        (.inBlock (eraseCFG Γ g) t (cs.map (eraseCmd Γ)) (mapTransfer (eraseExpr Γ) tr) ρ)
  | returned (ρ : Imperative.Env Core.Expression) :
      BridgeRel Γ g fr h (.returned ⟨ρ, h⟩) (.terminal ρ)
  | terminal (ρ : Imperative.Env Core.Expression) : BridgeRel Γ g fr h (.terminal ρ) (.terminal ρ)

/-- A Cortex run to `terminal` over `liftCFG g`, with no postconditions, has a
corresponding CFG run whose trace its own trace wraps. -/
private theorem bridge_fwd {Γ g fr h} (hb : fr.body.cfg = liftCFG g) (he : fr.ensures = [])
    (hv : fr.vars = constrainedVars Γ [] (some ⟨liftCFG g, []⟩)) (hx : fr.exits = [])
    {c ε c'} (hrun : ReflTransTrace (StepCortex Γ (EvalIRCmd Γ)) c ε c') :
    ∀ {d ρ'}, c' = .terminal ρ' → BridgeRel Γ g fr h c d →
      ∃ τ, ε = τ.map .std ∧ StepCFGStarE Core.Expression (SafeEvalCmdE h) d τ
        (.terminal ρ') := by
  induction hrun with
  | refl =>
    rintro d ρ' rfl hr
    cases hr
    exact ⟨[], rfl, .refl _⟩
  | step _ _ _ _ _ hs _ ih =>
    intro d ρ' hc hr
    cases hr with
    | atBlock t ρ =>
      cases hs with
      | fetch hl =>
        rw [hb] at hl
        obtain ⟨b, hb', rfl⟩ :=
          Option.map_eq_some_iff.1 ((lookup_map_snd liftBlock t _).symm.trans hl)
        rw [blockCmds_liftBlock hx, hv] at ih
        obtain ⟨τ, rfl, hτ⟩ := ih hc (.inBlock t _ b.transfer ρ)
        have hl' := (lookup_map_snd (eraseBlock Γ (constrainedVars Γ [] (some ⟨liftCFG g, []⟩)))
          t g.blocks).trans (congrArg _ hb')
        exact ⟨[] ++ τ, rfl, .step _ _ _ _ _ (.fetch hl') hτ⟩
    | inBlock t cs tr ρ =>
      cases cs with
      | cons c cs =>
        cases hs with
        | cmd_normal hev =>
          cases hev with
          | base hev hsafe =>
            obtain ⟨τ, rfl, hτ⟩ := ih hc (.inBlock t cs tr _)
            exact ⟨_ ++ τ, List.map_append.symm, .step _ _ _ _ _ (.step_cmd ⟨hev, hsafe⟩) hτ⟩
        | cmd_caught hev | cmd_uncaught_throws hev | cmd_uncaught_nothrows hev => cases hev
      | nil =>
        cases tr with
        | condGoto e lt lf md =>
          cases hs with
          | goto_true hv =>
            obtain ⟨τ, rfl, hτ⟩ := ih hc (.atBlock lt ρ)
            exact ⟨[] ++ τ, rfl, .step _ _ _ _ _ (.goto_true hv) hτ⟩
          | goto_false hv =>
            obtain ⟨τ, rfl, hτ⟩ := ih hc (.atBlock lf ρ)
            exact ⟨[] ++ τ, rfl, .step _ _ _ _ _ (.goto_false hv) hτ⟩
        | finish md =>
          cases hs
          obtain ⟨τ, rfl, hτ⟩ := ih hc (.returned ρ)
          refine ⟨[] ++ τ, ?_, .step _ _ _ _ _ .finish hτ⟩
          simp [ensuresEvents, he]
    | returned ρ =>
      cases hs
      exact ih hc (.terminal ρ)
    | terminal => cases hs

/-- A CFG run to `.terminal` over `eraseCFG Γ g` has a corresponding Cortex run over
`liftCFG g`, with no postconditions, whose trace wraps the CFG trace. -/
private theorem bridge_bwd {Γ g fr h} (hb : fr.body.cfg = liftCFG g) (he : fr.ensures = [])
    (hv : fr.vars = constrainedVars Γ [] (some ⟨liftCFG g, []⟩)) (hx : fr.exits = [])
    {d τ d'} (hrun : StepCFGStarE Core.Expression (SafeEvalCmdE h) d τ d') :
    ∀ {c ρ'}, d' = .terminal ρ' → BridgeRel Γ g fr h c d →
      ReflTransTrace (StepCortex Γ (EvalIRCmd Γ)) c (τ.map .std) (.terminal ρ') := by
  induction hrun with
  | refl =>
    rintro c ρ' rfl hr
    cases hr with
    | returned ρ => exact .step _ [] _ [] _ .close (.refl _)
    | terminal => exact .refl _
  | step _ _ _ _ _ hs _ ih =>
    intro c ρ' hc hr
    cases hr with
    | atBlock t ρ =>
      cases hs with
      | fetch hl =>
        obtain ⟨b, hb', rfl⟩ :=
          Option.map_eq_some_iff.1 ((lookup_map_snd (eraseBlock Γ _) t _).symm.trans hl)
        have hl' : List.lookup t fr.body.cfg.blocks = some (liftBlock b) :=
          hb ▸ (lookup_map_snd liftBlock t g.blocks).trans (congrArg _ hb')
        have hstep := StepCortex.fetch (Γ := Γ) (EvalCmd := EvalIRCmd Γ) (s := ⟨ρ, h⟩) hl'
        rw [blockCmds_liftBlock hx, hv] at hstep
        exact .step _ _ _ _ _ hstep (ih hc (.inBlock t _ b.transfer ρ))
    | inBlock t cs tr ρ =>
      cases cs with
      | cons c cs =>
        cases hs with
        | step_cmd hev =>
          exact List.map_append ▸
            .step _ _ _ _ _ (.cmd_normal (.base hev.1 hev.2)) (ih hc (.inBlock t cs tr _))
      | nil =>
        cases tr with
        | condGoto e lt lf md =>
          cases hs with
          | goto_true hv => exact .step _ _ _ _ _ (.goto_true hv) (ih hc (.atBlock lt ρ))
          | goto_false hv => exact .step _ _ _ _ _ (.goto_false hv) (ih hc (.atBlock lf ρ))
        | finish md =>
          cases hs
          have hens : ensuresEvents Γ fr ⟨ρ, h⟩ = [] := by simp [ensuresEvents, he]
          exact .step _ _ _ _ _ (hens ▸ StepCortex.finish (EvalCmd := EvalIRCmd Γ))
            (ih hc (.returned ρ))
    | returned => cases hs
    | terminal => cases hs

/-- The bridge to Imperative's CFG relation: for an entry frame whose body is a CFG `g` of
base commands with no handlers, and which has no postconditions, a Cortex run from the
entry to `terminal ρ'` emitting `τ` wrapped by `CEvent.std` is exactly a run of `StepCFGE`
from the entry of the erased CFG to `.terminal ρ'` emitting `τ` whose command steps are
`SafeEvalCmdE` steps in the heap the run starts from: every reference a command writes is
`Null` or allocated there. Base commands leave the heap unchanged, so that heap is the one
of the whole run. -/
theorem cortex_traceStar_iff_cfg {prog : Program} {g : DetCFG Core.Expression (Cmd Core.Expression)}
    {st : Frame} {ρ ρ' : Imperative.Env Core.Expression} {τ : Trace Core.Expression}
    (hb : st.body = ⟨liftCFG g, []⟩) (he : st.ensures = []) :
    (EventLang.cortex prog).traceStar ((EventLang.cortex prog).stmtCfg st ρ) (τ.map .std)
        (.terminal ρ') ↔
      StepCFGStarE Core.Expression (SafeEvalCmdE (entryHeap ρ.factory ρ.store))
        (.atBlock (eraseCFG prog.ctx g) g.entry ρ) τ (.terminal ρ') := by
  have hcfg : st.body.cfg = liftCFG g := by rw [hb]
  have hentry : st.body.cfg.entry = g.entry := by rw [hcfg]; rfl
  have hv : (st.toFr prog.ctx (entryOld prog.ctx st.inputs st.outputs ρ.store)).vars =
      constrainedVars prog.ctx [] (some ⟨liftCFG g, []⟩) := by
    simp only [Frame.toFr, hb]
  simp only [EventLang.cortex, hentry]
  constructor
  · intro h
    obtain ⟨τ', hτ, hrun⟩ := bridge_fwd (fr := st.toFr _ _) hcfg he hv rfl h rfl (.atBlock _ ρ)
    exact (List.map_inj_right (fun _ _ h => CEvent.std.inj h)).1 hτ ▸ hrun
  · exact fun h => bridge_bwd (fr := st.toFr _ _) hcfg he hv rfl h rfl (.atBlock _ ρ)

/-- The direction of the bridge a verification argument uses: a Cortex run from the entry
of a frame whose body is a CFG `g` of base commands with no handlers, and which has no
postconditions, is a run of `StepCFGE` with `EvalCmdE` over the erased CFG with the same
trace. -/
theorem cortex_traceStar_cfg {prog : Program} {g : DetCFG Core.Expression (Cmd Core.Expression)}
    {st : Frame} {ρ ρ' : Imperative.Env Core.Expression} {τ : Trace Core.Expression}
    (hb : st.body = ⟨liftCFG g, []⟩) (he : st.ensures = [])
    (h : (EventLang.cortex prog).traceStar ((EventLang.cortex prog).stmtCfg st ρ) (τ.map .std)
      (.terminal ρ')) :
    StepCFGStarE Core.Expression (EvalCmdE Core.Expression)
      (.atBlock (eraseCFG prog.ctx g) g.entry ρ) τ (.terminal ρ') :=
  ReflTransTrace.imp (fun _ _ _ => StepCFGE.imp fun _ _ _ _ _ h => h.1)
    ((cortex_traceStar_iff_cfg hb he).1 h)

end -- public section

end Cortex.Sem
