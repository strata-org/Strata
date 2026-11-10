/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterConfig
import all Strata.DL.Imperative.InterpreterConfig
import all Strata.DL.Imperative.StmtSemantics
import all Strata.Util.ListMap
public import Strata.Util.ListMapProps

/-! # Properties of `IConfig`

* `InterpLang.absStore_update`, `InterpLang.absStore_project`, `storeDenotes_iff`: the semantic
  image of runtime stores commutes with the store operations, and `StoreDenotes` is denotation
  plus equality with the image;
* `IConfig.getEnv_abs`, `IConfig.lvl_abs`, `IConfig.levelCmd?_abs`, `IConfig.abs_eq_terminal`,
  `IConfig.abs_eq_exiting`: the accessors and the stopping shapes commute with `abs`;
* `ScopeFrame.exit_eq`: an exact frame's exit store is the semantic projection;
* `StepStmtE.lvl_defines`: a reference step grows the level store only by the names of the
  command it runs at that level;
* `ScopeFrame.record_exact`: the frame recorded for such a step stays exact. -/

namespace Imperative

public section

variable {P : PureExpr} [InterpLang P] {CmdT : Type}

/-! ## The abstraction and the embedding -/

/-- The interpreter store of a store stands for that store. -/
@[simp] theorem IStore.get_ofStore [DecidableEq P.Ident] (σ : RStore P) :
    (IStore.ofStore σ).get = σ := by
  funext x
  simp [IStore.get, IStore.ofStore, InterpLang.writesFind?_empty]


/-- Binding `x` to `v` in an interpreter store stands for the point update. -/
@[simp] theorem IStore.get_update [DecidableEq P.Ident] (s : IStore P) (x : P.Ident)
    (v : P.Expr) : (s.update x v).get = RStore.update s.get x v := by
  funext y
  by_cases h : y = x
  · subst h
    simp [IStore.get, IStore.update, RStore.update, InterpLang.writesFind?_insert_self]
  · simp [IStore.get, IStore.update, RStore.update,
      InterpLang.writesFind?_insert_ne _ _ _ _ h, h]

/-- Dropping the names `D` from an interpreter store stands for `dropVars D`. -/
@[simp] theorem IStore.get_drop [DecidableEq P.Ident] (D : List P.Ident) (s : IStore P) :
    (s.drop D).get = RStore.dropVars D s.get := by
  induction D generalizing s with
  | nil => funext y; simp [IStore.drop, RStore.dropVars]
  | cons x D ih =>
    funext y
    obtain ⟨b, w⟩ := s
    have h := congrFun (ih ⟨b, if (b x).isSome then InterpLang.writesInsert w x none
      else InterpLang.writesErase w x⟩) y
    simp only [IStore.drop, List.foldl_cons] at h ⊢
    rw [h]
    by_cases hy : y = x
    · subst hy
      cases hb : b y <;>
        simp [RStore.dropVars, IStore.get, hb, InterpLang.writesFind?_insert_self,
          InterpLang.writesFind?_erase_self]
    · split <;> simp [RStore.dropVars, IStore.get, InterpLang.writesFind?_insert_ne _ _ _ _ hy,
        InterpLang.writesFind?_erase_ne _ _ _ hy, hy]

/-- After dropping `D`, a name of `D` has an undefined entry when the base store defines it and
    no entry otherwise; every other name keeps its entry. -/
theorem IStore.writesFind?_drop [DecidableEq P.Ident] (D : List P.Ident) (s : IStore P)
    (x : P.Ident) : InterpLang.writesFind? (s.drop D).writes x =
      if x ∈ D then (if (s.base x).isSome then some none else none)
      else InterpLang.writesFind? s.writes x := by
  obtain ⟨b, w⟩ := s
  induction D generalizing w with
  | nil => simp [IStore.drop]
  | cons y D ih =>
    have h := ih (if (b y).isSome then InterpLang.writesInsert w y none
      else InterpLang.writesErase w y)
    simp only [IStore.drop, List.foldl_cons] at h ⊢
    rw [h]
    by_cases hD : x ∈ D
    · simp [hD]
    · by_cases hy : x = y
      · subst hy
        by_cases hb : (b x).isSome <;>
          simp [hb, hD, InterpLang.writesFind?_insert_self, InterpLang.writesFind?_erase_self]
      · by_cases hb : (b y).isSome <;>
          simp [hb, hD, hy, InterpLang.writesFind?_insert_ne _ _ _ _ hy,
            InterpLang.writesFind?_erase_ne _ _ _ hy]

/-! ## Boolean literals up to metadata -/

/-- A runtime value read as a Boolean literal (`InterpLang.boolLit?`) denotes the corresponding
    Boolean value: `ttVal` for `true`, `ffVal` for `false`. -/
theorem InterpLang.denote_of_boolLit? [HasBool P] [InterpLangBool P] {F : P.Factory}
    {r : P.Expr} {v : P.Val} {b : Bool} (h : InterpLang.boolLit? r = some b)
    (hd : InterpLang.Denotes F r v) : v = if b then HasBool.ttVal F else HasBool.ffVal F := by
  unfold InterpLang.boolLit? at h
  split at h
  · cases h
    exact InterpLangBool.denote_of_eqModuloMeta_tt F r v ‹_› hd
  · split at h <;> cases h
    exact InterpLangBool.denote_of_eqModuloMeta_ff F r v ‹_› hd

/-! ## The semantic image of runtime stores -/

/-- Binding `x` to a runtime value `r` that denotes `v` stands for binding `x` to `v`. -/
theorem InterpLang.absStore_update [DecidableEq P.Ident] {F : P.Factory} (σ : RStore P)
    (x : P.Ident) {r : P.Expr} {v : P.Val} (h : InterpLang.Denotes F r v) :
    InterpLang.absStore F (RStore.update σ x r) = SemanticStore.update (InterpLang.absStore F σ) x v := by
  funext y
  by_cases hy : y = x <;>
    simp_all only [Denotes, absStore, RStore.update, ↓reduceIte, Option.bind_some,
        SemanticStore.update]

/-- On a denoting store, a name is defined in the semantic image exactly when it is defined. -/
theorem InterpLang.absStore_isSome {F : P.Factory} {σ : RStore P} (h : RStore.Denoting F σ)
    (x : P.Ident) : (InterpLang.absStore F σ x).isSome = (σ x).isSome := by
  cases hx : σ x with
  | none => simp [InterpLang.absStore, hx]
  | some r =>
    obtain ⟨v, hv⟩ := h x r hx
    simp_all only [Denotes, absStore, Option.bind_some, Option.isSome_some]

/-- The projection of runtime stores through a denoting parent stands for the projection of
    their images. -/
theorem InterpLang.absStore_project {F : P.Factory} {σp : RStore P} (σ : RStore P)
    (h : RStore.Denoting F σp) :
    InterpLang.absStore F (RStore.project σp σ) =
      projectStore (InterpLang.absStore F σp) (InterpLang.absStore F σ) := by
  funext x
  have hx := InterpLang.absStore_isSome h x
  simp only [projectStore, hx]
  by_cases hp : (σp x).isSome <;> simp [hp, InterpLang.absStore, RStore.project]

/-- Dropping names of a runtime store stands for dropping them from its image. -/
theorem InterpLang.absStore_dropVars [DecidableEq P.Ident] {F : P.Factory} (D : List P.Ident)
    (σ : RStore P) :
    InterpLang.absStore F (RStore.dropVars D σ) = dropVars D (InterpLang.absStore F σ) := by
  funext x
  by_cases hx : x ∈ D <;> simp [InterpLang.absStore, RStore.dropVars, dropVars, hx]

/-- `StoreDenotes` is: every runtime value denotes, and the semantic store is the image. -/
theorem storeDenotes_iff {F : P.Factory} {σr : RStore P} {σ : SemanticStore P} :
    StoreDenotes F σr σ ↔ RStore.Denoting F σr ∧ InterpLang.absStore F σr = σ := by
  constructor
  · rintro ⟨hn, hv⟩
    refine ⟨fun x r hr => ?_, funext fun x => ?_⟩
    · cases hσ : σ x with
      | none => exact absurd ((hn x).1 hσ) (by simp [hr])
      | some v => exact ⟨v, hv x r v hr hσ⟩
    · cases hr : σr x with
      | none => simp [InterpLang.absStore, hr, (hn x).2 hr]
      | some r =>
        cases hσ : σ x with
        | none => exact absurd ((hn x).1 hσ) (by simp [hr])
        | some v =>
          simpa [InterpLang.absStore, hr, hσ, InterpLang.Denotes] using hv x r v hr hσ
  · rintro ⟨hd, rfl⟩
    refine ⟨fun x => ?_, fun x r v hr hσ => ?_⟩
    · cases hr : σr x with
      | none => simp [InterpLang.absStore, hr]
      | some r =>
        obtain ⟨v, hv⟩ := hd x r hr
        simp_all only [InterpLang.Denotes, InterpLang.absStore, Option.bind_some, reduceCtorEq]
    · simpa [InterpLang.absStore, hr, InterpLang.Denotes] using hσ

/-- A runtime store denotes its image when every value denotes. -/
theorem storeDenotes_absStore {F : P.Factory} {σr : RStore P} (h : RStore.Denoting F σr) :
    StoreDenotes F σr (InterpLang.absStore F σr) := storeDenotes_iff.2 ⟨h, rfl⟩

/-- Binding a denoting runtime value keeps a store denoting. -/
theorem RStore.Denoting.update [DecidableEq P.Ident] {F : P.Factory} {σ : RStore P}
    (h : RStore.Denoting F σ) (x : P.Ident) {r : P.Expr} {v : P.Val}
    (hr : InterpLang.Denotes F r v) : RStore.Denoting F (RStore.update σ x r) := by
  intro y w hw
  by_cases hy : y = x
  · subst hy
    simp only [RStore.update, ite_true, Option.some.injEq] at hw
    exact hw ▸ ⟨v, hr⟩
  · exact h y w (by simpa [RStore.update, hy] using hw)

/-- Projecting keeps a denoting inner store denoting. -/
theorem RStore.Denoting.project {F : P.Factory} {σ : RStore P} (σp : RStore P)
    (h : RStore.Denoting F σ) : RStore.Denoting F (RStore.project σp σ) := by
  intro y w hw
  simp only [RStore.project] at hw
  split at hw
  · exact h y w hw
  · cases hw

/-- Dropping names keeps a denoting store denoting. -/
theorem RStore.Denoting.dropVars [DecidableEq P.Ident] {F : P.Factory} {σ : RStore P}
    (D : List P.Ident) (h : RStore.Denoting F σ) : RStore.Denoting F (RStore.dropVars D σ) := by
  intro y w hw
  simp only [RStore.dropVars] at hw
  split at hw
  · cases hw
  · exact h y w hw

omit [InterpLang P] in
/-- A sequence tower has the leaf environment of its innermost configuration. -/
@[simp] theorem Config.getEnv_wrapSeqs (c : Config P CmdT) (k : Nat) :
    (c.wrapSeqs k).getEnv = c.getEnv := by
  induction k <;> simp_all only [wrapSeqs, getEnv]

omit [InterpLang P] in
/-- A sequence tower has the level store of its innermost configuration. -/
@[simp] theorem Config.lvl_wrapSeqs (c : Config P CmdT) (k : Nat) :
    (c.wrapSeqs k).lvl = c.lvl := by
  induction k <;> simp_all only [wrapSeqs, lvl]

omit [InterpLang P] in
/-- A sequence tower has the level command of its innermost configuration. -/
@[simp] theorem Config.levelCmd?_wrapSeqs (c : Config P CmdT) (k : Nat) :
    (c.wrapSeqs k).levelCmd? = c.levelCmd? := by
  induction k <;> simp_all only [wrapSeqs, levelCmd?]

/-- Joining a sequence tower stands for one more sequence context with no remaining statements. -/
@[simp] theorem IConfig.abs_seqNil [DecidableEq P.Ident] (F : P.Factory) (c : IConfig P CmdT) :
    c.seqNil.abs F = .seq (c.abs F) [] := by
  cases c <;> rfl

/-- Joining a sequence tower keeps the configuration's frames. -/
@[simp] theorem IConfig.tracked_seqNil [DecidableEq P.Ident] (c : IConfig P CmdT) :
    c.seqNil.Tracked = c.Tracked := by
  cases c <;> rfl

/-- Joining a sequence tower keeps the leaf environment. -/
@[simp] theorem IConfig.getEnv_seqNil (c : IConfig P CmdT) : c.seqNil.getEnv = c.getEnv := by
  cases c <;> rfl
/-- Joining a sequence tower keeps the configuration's stores. -/
@[simp] theorem IConfig.denoting_seqNil [DecidableEq P.Ident] (F : P.Factory)
    (c : IConfig P CmdT) : c.seqNil.Denoting F = c.Denoting F := by
  cases c <;> rfl

/-- The leaf environment of the configuration an interpreter configuration stands for is the
    environment its leaf environment stands for. -/
@[simp] theorem IConfig.getEnv_abs [DecidableEq P.Ident] (F : P.Factory) (c : IConfig P CmdT) :
    (c.abs F).getEnv = c.getEnv.abs F := by
  induction c <;> simp_all only [abs, Config.getEnv, getEnv, Config.getEnv_wrapSeqs]

/-- A configuration's leaf store is that of the configuration it stands for. -/
@[simp] theorem IConfig.getStore_abs [DecidableEq P.Ident] (F : P.Factory) (c : IConfig P CmdT) :
    (c.abs F).getStore = InterpLang.absStore F c.getStore := by
  simp only [Config.getStore, IConfig.getStore, IConfig.getEnv_abs, IEnv.abs]

/-- A configuration's level store is that of the configuration it stands for. -/
@[simp] theorem IConfig.lvl_abs [DecidableEq P.Ident] (F : P.Factory) (c : IConfig P CmdT) :
    (c.abs F).lvl = InterpLang.absStore F c.lvl := by
  induction c <;> simp_all only [abs, IEnv.abs, Config.lvl, lvl, Config.lvl_wrapSeqs]

/-- A configuration's level command is that of the configuration it stands for. -/
@[simp] theorem IConfig.levelCmd?_abs [DecidableEq P.Ident] (F : P.Factory) (c : IConfig P CmdT) :
    (c.abs F).levelCmd? = c.levelCmd? := by
  induction c with
  | stmt s _ => cases s <;> rfl
  | seq _ _ ih => exact ih
  | seqs _ _ ih => simpa [IConfig.abs, IConfig.levelCmd?] using ih
  | _ => rfl

/-- A configuration stands for a terminal configuration exactly when it is that terminal
    configuration. -/
@[simp] theorem IConfig.abs_eq_terminal [DecidableEq P.Ident] (F : P.Factory) (c : IConfig P CmdT)
    (e : Env P) :
    c.abs F = .terminal e ↔ ∃ ie, c = .terminal ie ∧ ie.abs F = e := by
  cases c <;> simp [IConfig.abs, Config.wrapSeqs]

/-- A configuration stands for an exiting configuration exactly when it is that exiting
    configuration. -/
@[simp] theorem IConfig.abs_eq_exiting [DecidableEq P.Ident] (F : P.Factory) (c : IConfig P CmdT)
    (l : String) (e : Env P) :
    c.abs F = .exiting l e ↔ ∃ ie, c = .exiting l ie ∧ ie.abs F = e := by
  cases c <;> simp [IConfig.abs, Config.wrapSeqs, and_assoc]

/-- A configuration stands for a statement configuration exactly when it is that configuration. -/
@[simp] theorem IConfig.abs_eq_stmt [DecidableEq P.Ident] (F : P.Factory) (c : IConfig P CmdT)
    (s : Stmt P CmdT) (e : Env P) :
    c.abs F = .stmt s e ↔ ∃ ie, c = .stmt s ie ∧ ie.abs F = e := by
  cases c <;> simp [IConfig.abs, Config.wrapSeqs, and_assoc]

/-- A configuration stands for a statement-list configuration exactly when it is that
    configuration. -/
@[simp] theorem IConfig.abs_eq_stmts [DecidableEq P.Ident] (F : P.Factory) (c : IConfig P CmdT)
    (ss : List (Stmt P CmdT)) (e : Env P) :
    c.abs F = .stmts ss e ↔ ∃ ie, c = .stmts ss ie ∧ ie.abs F = e := by
  cases c <;> simp [IConfig.abs, Config.wrapSeqs, and_assoc]

/-- A configuration stands for a sequence context exactly when it is a sequence context whose
    inner configuration stands for the inner one. -/
theorem IConfig.abs_eq_seq [DecidableEq P.Ident] (F : P.Factory) (c : IConfig P CmdT)
    (i : Config P CmdT) (ss : List (Stmt P CmdT)) :
    c.abs F = .seq i ss ↔ (∃ ci, c = .seq ci ss ∧ ci.abs F = i) ∨
      (ss = [] ∧ ∃ ci k, c = .seqs ci k ∧ (ci.abs F).wrapSeqs k = i) := by
  cases c <;> simp [IConfig.abs, Config.wrapSeqs, and_assoc, and_comm, eq_comm]

/-- A configuration stands for a block context exactly when it is a block context with the same
    label whose frame has that parent store and whose inner configuration stands for the inner
    one. -/
theorem IConfig.abs_eq_block [DecidableEq P.Ident] (F : P.Factory) (c : IConfig P CmdT)
    (l : Option String) (σ : SemanticStore P) (i : Config P CmdT) :
    c.abs F = .block l σ i ↔
      ∃ fr ci, c = .block l fr ci ∧ InterpLang.absStore F fr.parent.get = σ ∧ ci.abs F = i := by
  cases c <;> simp [IConfig.abs, Config.wrapSeqs, and_assoc]

/-- A configuration whose abstraction is neither terminal nor exiting is neither terminal nor
    exiting. -/
theorem IConfig.not_done_of_abs [DecidableEq P.Ident] {F : P.Factory} {c : IConfig P CmdT}
    (h : (∀ e, c.abs F ≠ .terminal e) ∧ (∀ l e, c.abs F ≠ .exiting l e)) :
    (∀ e, c ≠ .terminal e) ∧ (∀ l e, c ≠ .exiting l e) := by
  simpa using h


/-- The level store of a configuration whose stores denote denotes. -/
theorem IConfig.Denoting.lvl [DecidableEq P.Ident] {F : P.Factory} {c : IConfig P CmdT}
    (h : c.Denoting F) : RStore.Denoting F c.lvl := by
  induction c with
  | seq _ _ ih => exact ih h
  | seqs _ _ ih => exact ih h
  | block _ _ _ _ => exact h.1
  | _ => exact h.1

/-- The leaf store of a configuration whose stores denote denotes, and its leaf environment
    carries the runtime factory of `F`. -/
theorem IConfig.Denoting.getEnv [DecidableEq P.Ident] {F : P.Factory} {c : IConfig P CmdT}
    (h : c.Denoting F) :
    RStore.Denoting F c.getEnv.store.get ∧ c.getEnv.factory = InterpLang.rfactory F := by
  induction c with
  | seq _ _ ih => exact ih h
  | seqs _ _ ih => exact ih h
  | block _ _ _ ih => exact ih h.2
  | _ => exact h

/-! ## Exact frames -/

/-- The exit store of a frame that is exact for the inner store `σ` is the projection of `σ`
    through the parent store. -/
theorem ScopeFrame.exit_eq [DecidableEq P.Ident] {fr : ScopeFrame P} {σ : IStore P}
    (h : fr.Exact σ.get) : (fr.exit σ).get = RStore.project fr.parent.get σ.get := by
  rcases fr with ⟨σp, _ | D⟩
  · exact IStore.get_ofStore _
  · funext x
    have hx := h D rfl x
    cases hp : σp.get x <;> cases hs : σ.get x <;>
      simp_all only [implies_true, Option.isNone_none, Option.isSome_none, Bool.false_eq_true,
          false_implies, and_self, exit, IStore.get_drop, RStore.dropVars, ite_self,
          RStore.project, ↓reduceIte, Option.isSome_some, forall_const, true_and, reduceCtorEq,
          imp_false, Option.isNone_some, and_true]

/-- A frame opened at store `σ` is exact for `σ`. -/
@[simp] theorem ScopeFrame.opened_exact [DecidableEq P.Ident] (σ : IStore P) :
    (ScopeFrame.opened σ).Exact σ.get := by
  simp [ScopeFrame.opened, ScopeFrame.Exact]

/-- Recording a step keeps the frame's parent store. -/
@[simp] theorem ScopeFrame.record_parent [DecidableEq P.Ident] [CmdDefs P CmdT] (fr : ScopeFrame P)
    (c? : Option CmdT) : (fr.record c?).parent = fr.parent := by
  unfold ScopeFrame.record
  split <;> rfl

omit [InterpLang P] in
/-- A reference step from a command statement reaches a terminal configuration. -/
theorem StepStmtE.cmd_terminal [HasBool P] [HasBoolOps P] {EventT : Type _}
    {EvalCmd : EvalCmdParamE P CmdT EventT} {c : CmdT} {ρ : Env P} {evs : List EventT}
    {c' : Config P CmdT} (h : StepStmtE P EvalCmd (.stmt (.cmd c) ρ) evs c') :
    ∃ ρ', c' = .terminal ρ' := by
  cases h
  exact ⟨_, rfl⟩

omit [InterpLang P] in
/-- A reference step from `c` to `c'` defines at `c`'s level only names of the command it runs
    at that level: every name `c'`'s level store defines is defined in `c`'s, or listed by
    `CmdDefs.defs` of `c`'s level command. -/
theorem StepStmtE.lvl_defines [CmdDefs P CmdT] [HasBool P] [HasBoolOps P] {EventT : Type _}
    {EvalCmd : EvalCmdParamE P CmdT EventT} (hdefs : CmdDefsSound EvalCmd)
    {c c' : Config P CmdT} {evs : List EventT} (h : StepStmtE P EvalCmd c evs c') :
    ∀ x, (c'.lvl x).isSome →
      (c.lvl x).isSome ∨ ∃ cmd, c.levelCmd? = some cmd ∧ x ∈ CmdDefs.defs (P := P) cmd := by
  induction h with
  | step_cmd hc => exact fun x hx => (hdefs _ _ _ _ _ hc x hx).imp_right fun h => ⟨_, rfl, h⟩
  | step_seq_inner _ ih => exact ih
  | step_block_body _ _ => exact fun _ hx => .inl hx
  | _ => exact fun x hx => .inl (by simp_all only [Config.lvl, Option.isSome_iff_ne_none, ne_eq,
      not_false_eq_true, projectStore, ite_not, ite_eq_left_iff, not_imp])

/-- The frame recorded for a step from the level store `σ` with level command `c?` to the level
    store `σ'` stays exact when the step defines only names of that command (`hgrow`). -/
theorem ScopeFrame.record_exact [DecidableEq P.Ident] [CmdDefs P CmdT] {fr : ScopeFrame P}
    {c? : Option CmdT}
    {σ σ' : RStore P} (hex : fr.Exact σ)
    (hgrow : ∀ x, (σ' x).isSome →
      (σ x).isSome ∨ ∃ cmd, c? = some cmd ∧ x ∈ CmdDefs.defs (P := P) cmd) :
    (fr.record c?).Exact σ' := by
  rcases fr with ⟨σp, _ | D⟩
  · simp [ScopeFrame.record, ScopeFrame.Exact]
  · simp only [ScopeFrame.record, ScopeFrame.Exact] at hex ⊢
    grind [Option.isNone_iff_eq_none]

end -- public section

end Imperative
