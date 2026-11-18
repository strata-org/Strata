/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.PassSemantics.Jumps
import StrataLaurel.Implementation.LaurelNodeKindProps

/-!
# Relations for Laurel pass proofs

This file defines the relations that pass proofs use to relate a source run to a target
run, and proves `FSH` lemmas for the interpreter's state operations under them. The main
theorem built on them, `fund`, is in `FundProof.lean`.

* `Reserved`: a class that fixes the names, procedures and labels a pass reserves for its
  own use, plus hooks a pass can use to relate stack frames. `Reserved.none` (in
  `Trav.lean`) reserves no name and no procedure, and the labels it is given.
* `SR G gs s s'`: the target stack agrees with the source stack on every name that is not
  reserved. `StRel G IR σ σ'` extends this to whole interpreter states, with the program
  indices related by `IR`, and with the same open labelled blocks (`openLabels`) except for
  the labels the pass reserves (`Reserved.resLabel`).
* `Shape E s t`: `s` and `t` have the same constructor and their children are related by
  `E`.
* `ImplRel`, `BodyRel`, `ProcRel E P P'`, `IxRel E ix ix'`: procedure bodies, procedures and
  program indices that agree up to `E`.
* `EvRel E`: events related by `E` and `StRel`. `CtlOK Gl G`: the control signals that may
  escape; `Gl` holds of the exit labels that may escape.
* `Sm E Gl G`: the `SimRel` built from `StRel`, `EvRel` and `CtlOK`. Every pass theorem is
  stated with it. `SmO E Gl G ol` is `Sm` for target states whose open labels are exactly `ol`.
* `Corr E l ss ss' j j'`: the statement at index `j` of `ss` and the one at `j'` of `ss'` hold
  the label `l` and are related, and the statements before and after them are related as well.
  `LX.find` says that the first statement of two related lists holding a label that is not
  reserved are at such indices.
* `fs_withLabels`, `fs_withOpenLabel`, `fs_openR`: `FS` for running with other open labels,
  and for a target block that the pass adds around code.
* `CfgB cfg`: every action of the external backend gives the same result for every trace
  (`PConst`).
* `fs_wbs`, `fs_readField`, `fs_writeField`, `fs_assignLocal`, `fs_resolveMethod`: `FS`
  lemmas for scopes, heap access, local assignment and method lookup.
-/

namespace Strata.Laurel.PassSemantics

open Strata.Laurel
open Strata.Laurel.Interpreter

def ORel (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False



structure CfgB (cfg : ExternalBackendM PM) : Prop where
  truthy : ∀ e, PConst (cfg.externalTruthy e)
  int : ∀ e, PConst (cfg.valueInt e)
  bool : ∀ e, PConst (cfg.valueBool e)
  string : ∀ e, PConst (cfg.valueString e)
  call : ∀ n a, PConst (cfg.callExternal n a)
  enumerate : ∀ t, PConst (cfg.enumerate t)
  strict : cfg.strict = none

structure CfgOK (cfg : ExternalBackendM PM) : Prop extends CfgB cfg where
  modular : cfg.modular = false

instance {cfg : ExternalBackendM PM} : CoeOut (CfgOK cfg) (CfgB cfg) := ⟨CfgOK.toCfgB⟩

theorem CfgOK.default : CfgOK ({} : ExternalBackendM PM) :=
  ⟨⟨fun _ => pconst_stuck _, fun _ => pconst_fail _, fun _ => pconst_fail _, fun _ => pconst_fail _,
    fun _ _ => pconst_fail _, fun _ => pconst_fail _, rfl⟩, rfl⟩

theorem pconst_bind {x : PM α} {f : α → PM β} (hx : PConst x) (hf : ∀ a, PConst (f a)) :
    PConst (x >>= f) := by
  rcases hx with ⟨a, ha⟩ | ⟨e, he⟩
  · rcases hf a with ⟨b, hb⟩ | ⟨e, he⟩
    · exact .inl ⟨b, fun τ => by simp only [bind, StateT.bind, ha, Except.bind, hb]⟩
    · exact .inr ⟨e, fun τ => by simp only [bind, StateT.bind, ha, Except.bind, he]⟩
  · exact .inr ⟨e, fun τ => by simp only [bind, StateT.bind, he, Except.bind]⟩

theorem pconst_ite {c : Prop} [Decidable c] {x y : PM α} (hx : PConst x) (hy : PConst y) :
    PConst (if c then x else y) := by
  split
  · exact hx
  · exact hy

def OPConst (o : Option (PM α)) : Prop := ∀ act, o = some act → PConst act

macro "pconst_tac" : tactic => `(tactic|
  repeat' (first
    | exact pconst_pure _
    | exact pconst_fail _
    | (apply pconst_bind <;> intros)
    | apply pconst_ite
    | assumption
    | split))

section
variable {cfg : ExternalBackendM PM} (hc : CfgB cfg)
include hc

/-- For a backend that satisfies `CfgB`, deciding whether a value is true (`Interpreter.isTrue`) gives
the same result for every trace and leaves the trace unchanged (`PConst`). -/
theorem isTrue_pconst (v : Value) : PConst (Interpreter.isTrue cfg v) := by
  unfold Interpreter.isTrue
  split
  · exact pconst_pure _
  · exact hc.truthy _
  · exact pconst_stuck _

theorem primEq_pconst (a b : Value) : PConst (primEq cfg a b) := by
  unfold primEq
  split <;> first
    | exact pconst_pure _
    | exact pconst_fail _
    | exact pconst_bind (hc.int _) (fun _ => pconst_pure _)
    | exact pconst_bind (hc.bool _) (fun _ => pconst_pure _)
    | exact pconst_bind (hc.string _) (fun _ => pconst_pure _)

/-- For a backend that satisfies `CfgB`, evaluating a primitive operation `op` on argument values
(`evalOp`) gives the same result for every trace and leaves the trace unchanged (`PConst`). -/
theorem evalOp_pconst (op : Operation) (args : List Value) : PConst (evalOp cfg op args) := by
  unfold evalOp
  split <;> first
    | exact pconst_pure _
    | exact pconst_fail _
    | exact pconst_stuck _
    | exact pconst_opIllTyped _ _
    | exact pconst_ite (pconst_pure _) (pconst_pure _)
    | exact pconst_bind (primEq_pconst hc _ _) (fun _ => pconst_pure _)

end

theorem hostOfExcept_pconst (r : Except String α) : PConst (hostOfExcept (m := PM) r) := by
  cases r
  · exact pconst_fail _
  · exact pconst_pure _

theorem bvBuiltin_pconst (name : String) (args : List Value) :
    OPConst (bvBuiltin? (m := PM) name args) := by
  intro act h
  simp only [bvBuiltin?, Option.map_eq_some_iff] at h
  obtain ⟨r, -, rfl⟩ := h
  cases r
  · exact pconst_stuck _
  · exact pconst_pure _

theorem callBuiltin_pconst (name : String) (args : List Value) (absent : Value) :
    OPConst (callBuiltin (m := PM) name args absent) := by
  intro act h
  simp only [callBuiltin, Option.map_eq_some_iff] at h
  obtain ⟨r, -, rfl⟩ := h
  exact hostOfExcept_pconst r


inductive Hered (P : StmtExprMd → Prop) : StmtExprMd → Prop where
  | node (e : StmtExprMd) : P e → (∀ c ∈ stmtExprChildren e.val, Hered P c) → Hered P e

theorem Hered.here {P : StmtExprMd → Prop} {e : StmtExprMd} (h : Hered P e) : P e := by
  cases h; assumption

theorem Hered.kid {P : StmtExprMd → Prop} {e : StmtExprMd} (h : Hered P e) {c : StmtExprMd}
    (hc : c ∈ stmtExprChildren e.val) : Hered P c := by
  cases h with
  | node _ _ kids => exact kids c hc

theorem Hered.mono {P Q : StmtExprMd → Prop} {e : StmtExprMd} (h : Hered P e) (hPQ : ∀ x, P x → Q x) :
    Hered Q e := by
  induction h with
  | node e hp _ ih => exact .node e (hPQ e hp) ih

theorem hered_all {P : StmtExprMd → Prop} (h : ∀ e, P e) (s : StmtExprMd) : Hered P s :=
  .node s (h s) (fun c _ => hered_all h c)
termination_by sizeOf s
decreasing_by exact stmtExprChildren_sizeOf_lt s c ‹_›

def freeKey (o : String) : String := o ++ "$free"

def noRetKey (o : String) : String := o ++ "$noret"

def IxSame (ix jx : ProgramIndex) : Prop :=
  jx.methodsById = ix.methodsById ∧ jx.methodOwner = ix.methodOwner ∧ jx.methodLists = ix.methodLists ∧
    jx.ancestors = ix.ancestors ∧ jx.aliasMap = ix.aliasMap

class Reserved where
  res : String → Prop
  shadow : ∀ n, ¬ res n → ¬ res (shadowKey n)
  shadow_res : ∀ n, res n → res (shadowKey n)
  resProc : String → Prop
  ixX : (StmtExprMd → StmtExprMd → Prop) → ProgramIndex → ProgramIndex → Prop := fun _ _ _ => True
  ixX_congr : ∀ E ix ix' jx jx', jx.procsById = ix.procsById → jx.procs = ix.procs →
    jx.overloaded = ix.overloaded → jx'.procsById = ix'.procsById → jx'.procs = ix'.procs →
    jx'.overloaded = ix'.overloaded → jx.ctors = ix.ctors → jx.testers = ix.testers →
    jx.destructors = ix.destructors → jx.constants = ix.constants → jx.procsNamed = ix.procsNamed →
    IxSame ix jx → IxSame ix' jx' →
    ixX E ix ix' → ixX E jx jx' := by intros; trivial
  resMethods : Prop := False
  resCall : Identifier → Prop := fun c => resProc c.text
  resCall_text : ∀ c, resProc c.text → resCall c := by intro _ h; exact h
  retLabel : Option String
  resLabel : String → Prop := fun _ => False
  noGlobals : Prop
  ren : Identifier → Identifier → Prop
  vret : Option String
  vret_ok : ∀ o, vret = some o → ¬ res o ∧ ¬ res (freeKey o) ∧ ∀ n, shadowKey n ≠ o
  vret_noret : ∀ o, vret = some o → ¬ res (noRetKey o)
  ex : (StmtExprMd → StmtExprMd → Prop) → StmtExprMd → List StmtExprMd → Prop
  vok : (StmtExprMd → StmtExprMd → Prop) → StmtExprMd → StmtExprMd → Prop := fun _ _ _ => True
  vokX : (StmtExprMd → StmtExprMd → Prop) → StmtExprMd → List StmtExprMd → Prop := fun _ _ _ => True
  aliasOf : StackFrame → String → Prop := fun _ _ => False
  aliasOf_res : ∀ G k, aliasOf G k → res k := by intro _ _ h; exact h.elim
  frozenOf : StackFrame → String → Option Value := fun _ _ => none
  frozenOf_res : ∀ G k v, frozenOf G k = some v → res k := by intro _ _ _ h; cases h
  loose : StackFrame → String → Prop := fun _ _ => False
  loose_res : ∀ G k, loose G k → res k := by intro _ _ h; exact h.elim
  loose_shadow : ∀ G k, loose G k → loose G (shadowKey k) := by intro _ _ h; exact h.elim
  loose_alias : ∀ G k, loose G k → ¬ aliasOf G k := by intro _ _ h; exact h.elim
  loose_bind : ∀ G n v k, res n → (loose (bindCatch G n v) k ↔ loose G k) := by intros; exact Iff.rfl
  loose_vret : ∀ o, vret = some o → ∀ G G' k, (loose G k ↔ loose G' k) := by intros; exact Iff.rfl
  pinOf : StackFrame → String → Option (Value × Nat × Bool) := fun _ _ => none
  pin_loose : ∀ G k p, pinOf G k = some p → loose G k := by intro _ _ _ h; cases h
  pin_bind : ∀ G n v k, res n → pinOf (bindCatch G n v) k = pinOf G k := by intros; rfl
  pin_vret : ∀ o, vret = some o → ∀ G k, pinOf G k = none := by intros; rfl
  pin_empty : ∀ k, pinOf {} k = none := by intros; rfl
  pin_noShadow : ∀ G k p, pinOf G k = some p → ∀ n, k ≠ shadowKey n := by intro _ _ _ h; cases h
  nodeOK : StackFrame → StmtExprMd → Prop := fun _ _ => True
  nodeOK_bind : ∀ G n v e, res n → (nodeOK (bindCatch G n v) e ↔ nodeOK G e) := by intros; exact Iff.rfl
  nodeOK_vret : ∀ o, vret = some o → ∀ G G' e, nodeOK G e → nodeOK G' e := by intros; trivial
  nodeOK_src : ∀ G v s s', nodeOK G ⟨v, s⟩ → nodeOK G ⟨v, s'⟩ := by intros; trivial
  freeze : StackFrame → Std.HashMap String Value → StackFrame → StackFrame := fun _ _ b => b
  freeze_get : ∀ G gs b k, (res k ∨ ∃ o, vret = some o ∧ (k = o ∨ k = freeKey o ∨ k = noRetKey o)) →
    (freeze G gs b)[k]? = b[k]? := by intros; rfl
  freeze_alias : ∀ G gs b k, aliasOf (freeze G gs b) k ↔ aliasOf b k := by intros; exact Iff.rfl
  freeze_frozen : ∀ G gs b k v, frozenOf (freeze G gs b) k = some v → frozenOf b k = some v ∨ gs[k]? = some v :=
    by intro _ _ _ _ _ h; exact .inl h
  freeze_keep : ∀ G gs b k v, aliasOf G k → gs[k]? = some v → frozenOf (freeze G gs b) k = some v :=
    by intro _ _ _ _ _ h; exact h.elim
  freeze_keepF : ∀ G gs b k v, frozenOf G k = some v → gs[k]? = some v → frozenOf (freeze G gs b) k = some v :=
    by intro _ _ _ _ _ h; cases h
  nodeOK_freeze : ∀ G gs b e, (∀ k, ¬ aliasOf b k) → nodeOK b e → nodeOK (freeze G gs b) e := by intros; trivial
  postOf : StackFrame → StackFrame → StackFrame := fun _ b => b
  postOf_get : ∀ G b k, (res k ∨ ∃ o, vret = some o ∧ (k = o ∨ k = freeKey o ∨ k = noRetKey o)) →
    (postOf G b)[k]? = b[k]? := by intros; rfl
  postOf_alias : ∀ G b k, aliasOf (postOf G b) k ↔ aliasOf b k := by intros; exact Iff.rfl
  postOf_frozen : ∀ G b k v, frozenOf (postOf G b) k = some v → frozenOf b k = some v ∨ frozenOf G k = some v :=
    by intro _ _ _ _ h; exact .inl h
  postOf_keepF : ∀ G b k v, frozenOf G k = some v → frozenOf (postOf G b) k = some v :=
    by intro _ _ _ _ h; cases h
  nodeOK_postOf : ∀ G b e, (∀ k, ¬ aliasOf b k) → nodeOK b e → nodeOK (postOf G b) e := by intros; trivial
  loose_freeze : ∀ G gs b k, loose (freeze G gs b) k ↔ loose b k := by intros; exact Iff.rfl
  loose_postOf : ∀ G b k, loose (postOf G b) k ↔ loose b k := by intros; exact Iff.rfl
  pin_freeze : ∀ G gs b k, pinOf (freeze G gs b) k = pinOf b k := by intros; rfl
  pin_postOf : ∀ G b k, pinOf (postOf G b) k = pinOf b k := by intros; rfl
  relax : StackFrame → List String → StackFrame := fun G _ => G
  relax_get : ∀ G ds k, (res k ∨ ∃ o, vret = some o ∧ (k = o ∨ k = freeKey o ∨ k = noRetKey o)) →
    (relax G ds)[k]? = G[k]? := by intros; rfl
  relax_alias : ∀ G ds k, aliasOf (relax G ds) k ↔ aliasOf G k := by intros; exact Iff.rfl
  relax_frozen : ∀ G ds k, frozenOf (relax G ds) k = frozenOf G k := by intros; rfl
  relax_loose : ∀ G ds k, loose (relax G ds) k ↔ loose G k := by intros; exact Iff.rfl
  relax_pin : ∀ G ds k, pinOf (relax G ds) k =
    if k ∈ ds then (pinOf G k).map (fun p => (p.1, p.2.1, false)) else pinOf G k := by intros; split <;> rfl
  nodeOK_relax : ∀ G ds e, nodeOK (relax G ds) e ↔ nodeOK G e := by intros; exact Iff.rfl
  postMode : StackFrame → Prop := fun _ => False
  alias_bind : ∀ G n v k, res n → (aliasOf (bindCatch G n v) k ↔ aliasOf G k) := by intros; exact Iff.rfl
  frozen_bind : ∀ G n v k, res n → frozenOf (bindCatch G n v) k = frozenOf G k := by intros; rfl
  postMode_bind : ∀ G n v, res n → (postMode (bindCatch G n v) ↔ postMode G) := by intros; exact Iff.rfl
  alias_empty : ∀ k, ¬ aliasOf {} k := by intro _ h; exact h
  frozen_empty : ∀ k, frozenOf {} k = none := by intros; rfl
  alias_vret : ∀ o, vret = some o → ∀ G k, ¬ aliasOf G k := by intro _ _ _ _ h; exact h
  frozen_vret : ∀ o, vret = some o → ∀ G k, frozenOf G k = none := by intros; rfl
  entOK : StackFrame → Prop := fun _ => True
  entOK_postOf : ∀ G b, (∀ k, ¬ aliasOf b k) → entOK (postOf G b) := by intros; trivial
  entOK_relax : ∀ G ds, entOK G → entOK (relax G ds) := by intros; trivial
  entOK_unrelax : ∀ G ds, entOK (relax G ds) → entOK G := by intros; trivial
  entOK_vret : ∀ o, vret = some o → ∀ G G', entOK G → entOK G' := by intros; trivial
  tyR : HighType → HighType → Prop := fun a b => a = b
  inoutOK : String → Prop := fun _ => True

section
variable [Reserved]

def shadowAt (s : StackFrame) (k : String) (i : Nat) : Option Value :=
  match s[shadowKey k]? with
  | some (.seq q) => q[i]?
  | _ => none

def PinOK (s : StackFrame) (k : String) (v : Value) (δ : Nat) (x : Bool) : Prop :=
  if x then Interpreter.shadowDepth s k = δ ∧ s[k]? = some v
  else δ ≤ Interpreter.shadowDepth s k ∧ (Interpreter.shadowDepth s k = δ → s[k]? = some v) ∧
    (δ < Interpreter.shadowDepth s k → shadowAt s k δ = some (Interpreter.savedPrior (some v)))

omit [Reserved] in
theorem PinOK.congr {s s2 : StackFrame} {k : String} {v : Value} {δ : Nat} {x : Bool} (h : PinOK s k v δ x)
    (h1 : s2[k]? = s[k]?) (h2 : s2[shadowKey k]? = s[shadowKey k]?) : PinOK s2 k v δ x := by
  have e1 : Interpreter.shadowDepth s2 k = Interpreter.shadowDepth s k := by
    unfold Interpreter.shadowDepth; rw [h2]
  have e2 : ∀ i, shadowAt s2 k i = shadowAt s k i := fun i => by unfold shadowAt; rw [h2]
  unfold PinOK at h ⊢
  rw [e1, h1, e2]
  exact h

omit [Reserved] in
theorem PinOK.weaken {s : StackFrame} {k : String} {v : Value} {δ : Nat} {x : Bool} (h : PinOK s k v δ x) :
    PinOK s k v δ false := by
  unfold PinOK at h ⊢
  cases x with
  | false => exact h
  | true =>
    simp only [ite_true] at h
    obtain ⟨h1, h2⟩ := h
    exact ⟨Nat.le_of_eq h1.symm, fun _ => h2, fun hlt => absurd h1 (Nat.ne_of_gt hlt)⟩

def NotV (n : String) : Prop := ∀ o, Reserved.vret = some o → n ≠ o

def ParamR (p p' : Parameter) : Prop := p.name = p'.name ∧ Reserved.tyR p.type.val p'.type.val

def TyEq : Prop := ∀ t t', Reserved.tyR t t' ↔ t = t'

class TyEqC : Prop where
  ok : TyEq

theorem TyEq.refl (h : TyEq) (t : HighType) : Reserved.tyR t t := (h t t).mpr rfl

theorem ParamR.refl (h : TyEq) (p : Parameter) : ParamR p p := ⟨rfl, h.refl _⟩

theorem ORel.tyRefl (h : TyEq) (o : Option HighTypeMd) : ORel (fun a b => Reserved.tyR a.val b.val) o o := by
  cases o
  · trivial
  · exact h.refl _

theorem L2.tyRefl (h : TyEq) (l : List HighTypeMd) : L2 (fun a b => Reserved.tyR a.val b.val) l l := by
  induction l with
  | nil => exact .nil
  | cons x xs ih => exact .cons (h.refl _) ih

theorem ParamR.list (h : TyEq) (l : List Parameter) : L2 ParamR l l := by
  induction l with
  | nil => exact .nil
  | cons x xs ih => exact .cons (ParamR.refl h x) ih

def NG (k : String) : Prop := Reserved.noGlobals ∨ ∃ o, Reserved.vret = some o ∧ k = o

theorem not_NG (h1 : ¬ Reserved.noGlobals) (h2 : Reserved.vret = none) (k : String) : ¬ NG k := by
  rintro (h | ⟨o, ho, -⟩)
  · exact h1 h
  · rw [h2] at ho; cases ho

theorem gk_insert {g : Std.HashMap String Value} (hg : ∀ k, NG k → g.contains k = false) {n : String}
    (hn : g.contains n = true) (v : Value) : ∀ k, NG k → (g.insert n v).contains k = false := by
  intro k hk
  rw [Std.HashMap.contains_insert, hg k hk, Bool.or_false, beq_eq_false_iff_ne]
  rintro rfl
  rw [hg _ hk] at hn
  cases hn

theorem gk_ins {g : Std.HashMap String Value} (hg : ∀ k, NG k → g.contains k = false) (hng : ¬ Reserved.noGlobals)
    {n : String} (hn : ∀ o, Reserved.vret = some o → n ≠ o) (v : Value) :
    ∀ k, NG k → (g.insert n v).contains k = false := by
  rintro k (h | ⟨o, ho, hk⟩)
  · exact absurd h hng
  · subst hk
    rw [Std.HashMap.contains_insert, hg _ (.inr ⟨_, ho, rfl⟩), Bool.or_false, beq_eq_false_iff_ne]
    exact hn _ ho

def Strict (G : StackFrame) : Prop := ∀ o, Reserved.vret = some o → ¬ G.contains (freeKey o) ∧ G[o]? = none

def Free (G : StackFrame) : Prop := ∃ o, Reserved.vret = some o ∧ G.contains (freeKey o)

def NoRet (G : StackFrame) : Prop := ∃ o, Reserved.vret = some o ∧ G.contains (noRetKey o)

structure SR (G : StackFrame) (gs : Std.HashMap String Value) (s s' : StackFrame) : Prop where
  src : ∀ k, ¬ Reserved.res k → (NotV k ∨ Strict G) → s'[k]? = s[k]?
  ghost : ∀ k, Reserved.res k → ¬ Reserved.aliasOf G k → ¬ Reserved.loose G k → s'[k]? = G[k]?
  out : ∀ o w, Reserved.vret = some o → ¬ G.contains (freeKey o) → G[o]? = some w → s'[o]? = some w
  alias : ∀ k, Reserved.aliasOf G k → ∃ v, gs[k]? = some v ∧ s'[k]? = some v
  frozen : ∀ k v, Reserved.frozenOf G k = some v → gs[k]? = some v
  clean : ∀ k, Reserved.res k → s[k]? = none
  pin : ∀ k v δ x, Reserved.pinOf G k = some (v, δ, x) → PinOK s' k v δ x

variable {G : StackFrame} {gs : Std.HashMap String Value}

theorem pin_res {G : StackFrame} {k : String} {p : Value × Nat × Bool} (h : Reserved.pinOf G k = some p) :
    Reserved.res k :=
  Reserved.loose_res G k (Reserved.pin_loose G k p h)

theorem SR.pin_res_eq {s s' s2 : StackFrame} (h : SR G gs s s') (he : ∀ k, Reserved.res k → s2[k]? = s'[k]?) :
    ∀ k v δ x, Reserved.pinOf G k = some (v, δ, x) → PinOK s2 k v δ x :=
  fun k v δ x hp => (h.pin k v δ x hp).congr (he k (pin_res hp)) (he _ (Reserved.shadow_res k (pin_res hp)))

theorem insert_res_eq {s : StackFrame} {k0 : String} (hk : ¬ Reserved.res k0) (w : Value) :
    ∀ k, Reserved.res k → (s.insert k0 w)[k]? = s[k]? := fun k hr => by
  rw [Std.HashMap.getElem?_insert, ite_eq_right (by simp only [beq_iff_eq]; rintro rfl; exact hk hr)]

theorem erase_res_eq {s : StackFrame} {k0 : String} (hk : ¬ Reserved.res k0) :
    ∀ k, Reserved.res k → (s.erase k0)[k]? = s[k]? := fun k hr => by
  rw [Std.HashMap.getElem?_erase, ite_eq_right (by simp only [beq_iff_eq]; rintro rfl; exact hk hr)]

theorem notV_shadow (n : String) : NotV (shadowKey n) := fun o h => (Reserved.vret_ok o h).2.2 n

theorem notV_none (h : Reserved.vret = none) (n : String) : NotV n := fun o ho => by rw [h] at ho; cases ho

theorem strict_none (h : Reserved.vret = none) (G : StackFrame) : Strict G := fun o ho => by rw [h] at ho; cases ho

theorem Strict.empty : Strict ({} : StackFrame) := fun _ _ => ⟨by simp, by simp⟩

theorem clean_insert {s : StackFrame} (hc : ∀ j, Reserved.res j → s[j]? = none) {k : String}
    (hk : ¬ Reserved.res k) (v : Value) : ∀ j, Reserved.res j → (s.insert k v)[j]? = none := by
  intro j hj
  rw [Std.HashMap.getElem?_insert, ite_eq_right (by simp only [beq_iff_eq]; rintro rfl; exact hk hj)]
  exact hc j hj

theorem clean_erase {s : StackFrame} (hc : ∀ j, Reserved.res j → s[j]? = none) (k : String) :
    ∀ j, Reserved.res j → (s.erase k)[j]? = none := by
  intro j hj
  rw [Std.HashMap.getElem?_erase]
  split
  · rfl
  · exact hc j hj

theorem SR.fresh {s : StackFrame} (hs : ∀ k, Reserved.res k → s[k]? = none) : SR {} gs s s :=
  ⟨fun _ _ _ => rfl, fun k hk _ _ => by rw [hs k hk]; simp, fun _ _ _ _ h => by simp at h,
    fun k h => absurd h (Reserved.alias_empty k), fun k v h => (by rw [Reserved.frozen_empty] at h; cases h), hs,
    fun k v δ x h => (by rw [Reserved.pin_empty] at h; cases h)⟩

theorem SR.get {s s' : StackFrame} (h : SR G gs s s') {k : String} (hk : ¬ Reserved.res k)
    (hv : NotV k ∨ Strict G) : s'[k]? = s[k]? :=
  h.src k hk hv

theorem SR.insert {s s' : StackFrame} (h : SR G gs s s') {k : String} (hk : ¬ Reserved.res k) (hv : NotV k)
    (v : Value) : SR G gs (s.insert k v) (s'.insert k v) := by
  refine ⟨fun j hj hjv => ?_, fun j hj hja hjl => ?_, fun o w ho hf hw => ?_, fun j ha => ?_, h.frozen, clean_insert h.clean hk _,
    h.pin_res_eq (insert_res_eq hk _)⟩
  · simp only [Std.HashMap.getElem?_insert]
    split
    · rfl
    · exact h.src j hj hjv
  · simp only [Std.HashMap.getElem?_insert]
    split
    · rename_i he; simp only [beq_iff_eq] at he; subst he; exact absurd hj hk
    · exact h.ghost j hj hja hjl
  · simp only [Std.HashMap.getElem?_insert]
    rw [ite_eq_right (by simpa using hv o ho)]
    exact h.out o w ho hf hw
  · have hjr := Reserved.aliasOf_res _ _ ha
    simp only [Std.HashMap.getElem?_insert]
    rw [ite_eq_right (by simp only [beq_iff_eq]; rintro rfl; exact hk hjr)]
    exact h.alias j ha

def Plain (G : StackFrame) : Prop := (∀ k, ¬ Reserved.aliasOf G k) ∧ ∀ k, Reserved.frozenOf G k = none

theorem not_resProc_of_call {c : Identifier} (h : ¬ Reserved.resCall c) : ¬ Reserved.resProc c.text :=
  fun h' => h (Reserved.resCall_text c h')


theorem SR.regs {s s' : StackFrame} (h : SR G gs s s') (hp : Plain G) (gs' : Std.HashMap String Value) :
    SR G gs' s s' :=
  ⟨h.src, h.ghost, h.out, fun k ha => absurd ha (hp.1 k), fun k v hf => (by rw [hp.2 k] at hf; cases hf), h.clean,
    h.pin⟩

theorem SR.gs_insert {s s' : StackFrame} (h : SR G gs s s') {k : String} (hk : ¬ Reserved.res k) (v : Value) :
    SR G (gs.insert k v) s s' := by
  refine ⟨h.src, h.ghost, h.out, fun j ha => ?_, fun j w hf => ?_, h.clean, h.pin⟩
  · have hjr := Reserved.aliasOf_res _ _ ha
    rw [Std.HashMap.getElem?_insert, ite_eq_right (by intro he; simp only [beq_iff_eq] at he; subst he; exact hk hjr)]
    exact h.alias j ha
  · have hjr := Reserved.frozenOf_res _ _ _ hf
    rw [Std.HashMap.getElem?_insert, ite_eq_right (by intro he; simp only [beq_iff_eq] at he; subst he; exact hk hjr)]
    exact h.frozen j w hf

theorem SR.erase {s s' : StackFrame} (h : SR G gs s s') {k : String} (hk : ¬ Reserved.res k) (hv : NotV k) :
    SR G gs (s.erase k) (s'.erase k) := by
  refine ⟨fun j hj hjv => ?_, fun j hj hja hjl => ?_, fun o w ho hf hw => ?_, fun j ha => ?_, h.frozen, clean_erase h.clean k,
    h.pin_res_eq (erase_res_eq hk)⟩
  · simp only [Std.HashMap.getElem?_erase]
    split
    · rfl
    · exact h.src j hj hjv
  · simp only [Std.HashMap.getElem?_erase]
    split
    · rename_i he; simp only [beq_iff_eq] at he; subst he; exact absurd hj hk
    · exact h.ghost j hj hja hjl
  · simp only [Std.HashMap.getElem?_erase]
    rw [ite_eq_right (by simpa using hv o ho)]
    exact h.out o w ho hf hw
  · have hjr := Reserved.aliasOf_res _ _ ha
    simp only [Std.HashMap.getElem?_erase]
    rw [ite_eq_right (by simp only [beq_iff_eq]; rintro rfl; exact hk hjr)]
    exact h.alias j ha

theorem SR.contains {s s' : StackFrame} (h : SR G gs s s') {k : String} (hk : ¬ Reserved.res k)
    (hv : NotV k ∨ Strict G) : s'.contains k = s.contains k := by
  rw [← Std.HashMap.isSome_getElem?_eq_contains, ← Std.HashMap.isSome_getElem?_eq_contains, h.get hk hv]

theorem SR.bindCatch {s s' : StackFrame} (h : SR G gs s s') {n : String} (hn : ¬ Reserved.res n) (hv : NotV n)
    (v : Value) : SR G gs (bindCatch s n v) (bindCatch s' n v) := by
  unfold Interpreter.bindCatch
  rw [h.get (Reserved.shadow n hn) (.inl (notV_shadow n)), h.get hn (.inl hv)]
  exact (h.insert (Reserved.shadow n hn) (notV_shadow n) _).insert hn hv _

theorem SR.declareLocal {s s' : StackFrame} (h : SR G gs s s') {n : String} (hn : ¬ Reserved.res n) (hv : NotV n)
    (v : Value) : SR G gs (declareLocal s n v) (declareLocal s' n v) :=
  h.bindCatch hn hv v

theorem SR.unbindCatch {s s' : StackFrame} (h : SR G gs s s') {n : String} (hn : ¬ Reserved.res n) (hv : NotV n) :
    SR G gs (unbindCatch s n) (unbindCatch s' n) := by
  have hs := Reserved.shadow n hn
  have hsv := notV_shadow n
  unfold Interpreter.unbindCatch
  rw [h.get hs (.inl hsv)]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> first
    | exact h
    | exact (h.erase hs hsv).insert hn hv _
    | exact (h.erase hs hsv).erase hn hv
    | exact (h.insert hs hsv _).insert hn hv _
    | exact (h.insert hs hsv _).erase hn hv

theorem SR.shadowDepth {s s' : StackFrame} (h : SR G gs s s') {n : String} (hn : ¬ Reserved.res n) :
    shadowDepth s' n = shadowDepth s n := by
  unfold Interpreter.shadowDepth
  rw [h.get (Reserved.shadow n hn) (.inl (notV_shadow n))]

theorem SR.popShadowsTo_go {n : String} (hn : ¬ Reserved.res n) (hv : NotV n) (d : Nat) :
    ∀ k {s s' : StackFrame}, SR G gs s s' → SR G gs (popShadowsGo n d k s) (popShadowsGo n d k s')
  | 0, _, _, h => h
  | k + 1, _, _, h => by
    simp only [popShadowsGo, h.shadowDepth hn]
    split
    · exact SR.popShadowsTo_go hn hv d k (h.unbindCatch hn hv)
    · exact h

theorem SR.popShadowsTo {s s' : StackFrame} (h : SR G gs s s') {n : String} (hn : ¬ Reserved.res n) (hv : NotV n)
    (d : Nat) : SR G gs (popShadowsTo s n d) (popShadowsTo s' n d) := by
  unfold Interpreter.popShadowsTo
  rw [h.shadowDepth hn]
  exact SR.popShadowsTo_go hn hv d _ h

theorem SR.fold {s s' : StackFrame} (h : SR G gs s s') (m : StackFrame)
    (hm : ∀ kv ∈ m.toList, ¬ Reserved.res kv.1 ∧ NotV kv.1) :
    SR G gs (m.fold (fun acc k v => acc.insert k v) s) (m.fold (fun acc k v => acc.insert k v) s') := by
  rw [Std.HashMap.fold_eq_foldl_toList, Std.HashMap.fold_eq_foldl_toList]
  generalize m.toList = l at hm
  induction l generalizing s s' with
  | nil => exact h
  | cons kv l ih =>
    exact ih (h.insert (hm kv (List.mem_cons_self ..)).1 (hm kv (List.mem_cons_self ..)).2 _)
      (fun x hx => hm x (List.mem_cons_of_mem _ hx))

theorem SR.insertS {s s' : StackFrame} (h : SR G gs s s') {k : String} (hk : ¬ Reserved.res k) (hS : Strict G)
    (v : Value) : SR G gs (s.insert k v) (s'.insert k v) := by
  refine ⟨fun j hj hjv => ?_, fun j hj hja hjl => ?_, fun o w ho _ hw => ?_, fun j ha => ?_, h.frozen, clean_insert h.clean hk _,
    h.pin_res_eq (insert_res_eq hk _)⟩
  · simp only [Std.HashMap.getElem?_insert]
    split
    · rfl
    · exact h.src j hj hjv
  · simp only [Std.HashMap.getElem?_insert]
    split
    · rename_i he; simp only [beq_iff_eq] at he; subst he; exact absurd hj hk
    · exact h.ghost j hj hja hjl
  · rw [(hS o ho).2] at hw; cases hw
  · have hjr := Reserved.aliasOf_res _ _ ha
    simp only [Std.HashMap.getElem?_insert]
    rw [ite_eq_right (by simp only [beq_iff_eq]; rintro rfl; exact hk hjr)]
    exact h.alias j ha

omit [Reserved] in
theorem foldl_ins_none {β : Type} (l : List (String × β)) (s : Std.HashMap String β) (k : String)
    (h : ∀ kv ∈ l, kv.1 ≠ k) : (l.foldl (fun acc kv => acc.insert kv.1 kv.2) s)[k]? = s[k]? := by
  induction l generalizing s with
  | nil => rfl
  | cons kv l ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun x hx => h x (List.mem_cons_of_mem _ hx)), Std.HashMap.getElem?_insert,
      ite_eq_right (by simp only [beq_iff_eq]; exact h kv (List.mem_cons_self ..))]

omit [Reserved] in
theorem foldl_ins_some {β : Type} (l : List (String × β)) (s : Std.HashMap String β) (k : String) (v : β)
    (hd : l.Pairwise (fun a b => (a.1 == b.1) = false)) (hm : (k, v) ∈ l) :
    (l.foldl (fun acc kv => acc.insert kv.1 kv.2) s)[k]? = some v := by
  induction l generalizing s with
  | nil => cases hm
  | cons kv l ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hm with he | hm
    · subst he
      rw [foldl_ins_none _ _ _ (fun x hx => by
        have := List.rel_of_pairwise_cons hd hx
        intro hx1; simp [hx1] at this)]
      simp
    · exact ih _ hd.of_cons hm

omit [Reserved] in
theorem fold_ins_get {β : Type} (m s : Std.HashMap String β) (k : String) :
    (m.fold (fun acc k v => acc.insert k v) s)[k]? = (m[k]?).or s[k]? := by
  rw [Std.HashMap.fold_eq_foldl_toList]
  cases hk : m[k]? with
  | some v =>
    exact foldl_ins_some _ _ _ _ Std.HashMap.distinct_keys_toList
      (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hk)
  | none =>
    refine foldl_ins_none _ _ _ (fun x hx he => ?_)
    have := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp (show (x.1, x.2) ∈ m.toList from hx)
    rw [he, hk] at this; cases this

def GlR (g g' : Std.HashMap String Value) : Prop := ∀ k, ¬ Reserved.res k → g'[k]? = g[k]?

structure EntOK (G : StackFrame) (g : Std.HashMap String Value) (i i' : StackFrame) : Prop where
  src : ∀ k, ¬ Reserved.res k → i'[k]? = i[k]?
  ghost : ∀ k, Reserved.res k → ¬ Reserved.aliasOf G k → i'[k]? = none
  alias : ∀ k, Reserved.aliasOf G k → (∃ v, g[k]? = some v ∧ i'[k]? = some v) ∨
    (i'[k]? = none ∧ ∃ v, Reserved.frozenOf G k = some v ∧ g[k]? = some v)
  frozen : ∀ k v, Reserved.frozenOf G k = some v → g[k]? = some v
  hook : Reserved.entOK G
  keys : ∀ k v, i[k]? = some v → Reserved.inoutOK k := by intros; trivial

def EntR (G : StackFrame) :
    Option (Array HeapObject × Std.HashMap String Value × StackFrame) →
      Option (Array HeapObject × Std.HashMap String Value × StackFrame) → Prop
  | none, none => True
  | some (h, g, i), some (h', g', i') =>
    h' = h ∧ GlR g g' ∧ (∀ k, NG k → g'.contains k = false) ∧ EntOK G g i i'
  | _, _ => False

theorem GlR.contains {g g' : Std.HashMap String Value} (h : GlR g g') {k : String} (hk : ¬ Reserved.res k) :
    g'.contains k = g.contains k := by
  rw [Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.contains_eq_isSome_getElem?, h k hk]

theorem GlR.insert {g g' : Std.HashMap String Value} (h : GlR g g') (k : String) (v : Value) :
    GlR (g.insert k v) (g'.insert k v) := by
  intro j hj
  simp only [Std.HashMap.getElem?_insert]
  split
  · rfl
  · exact h j hj

theorem GlR.refl (g : Std.HashMap String Value) : GlR g g := fun _ _ => rfl

theorem EntOK.same {G : StackFrame} {g : Std.HashMap String Value} {i : StackFrame} (hc : ∀ k, Reserved.res k → i[k]? = none)
    (ha : ∀ k, ¬ Reserved.aliasOf G k) (hf : ∀ k, Reserved.frozenOf G k = none) (hh : Reserved.entOK G)
    (hio : ∀ k v, i[k]? = some v → Reserved.inoutOK k := by intros; trivial) : EntOK G g i i :=
  ⟨fun _ _ => rfl, fun k hk _ => hc k hk, fun k h => absurd h (ha k), fun k v h => (by rw [hf k] at h; cases h), hh, hio⟩

theorem EntR.congr {G G' : StackFrame} {e e'} (h : EntR G e e') (ha : ∀ k, Reserved.aliasOf G' k ↔ Reserved.aliasOf G k)
    (hf : ∀ k, Reserved.frozenOf G' k = Reserved.frozenOf G k) (hh : Reserved.entOK G → Reserved.entOK G') :
    EntR G' e e' := by
  match e, e', h with
  | none, none, _ => trivial
  | some (_, _, _), some (_, _, _), ⟨h1, h2, h4, h3⟩ =>
    exact ⟨h1, h2, h4, ⟨h3.src, fun k hk hna => h3.ghost k hk (fun h => hna ((ha k).mpr h)),
      fun k h => (h3.alias k ((ha k).mp h)).imp id (fun ⟨h1, v, h2, h3⟩ => ⟨h1, v, by rw [hf k]; exact h2, h3⟩),
      fun k v h => h3.frozen k v (by rw [← hf k]; exact h), hh h3.hook, h3.keys⟩⟩

theorem SR.foldEnt {s s' : StackFrame} (h : SR G gs s s') (hS : Strict G) {g : Std.HashMap String Value}
    {i i' : StackFrame} (hc : ∀ k, Reserved.res k → i[k]? = none) (he : EntOK G g i i') :
    SR G g (i.fold (fun acc k v => acc.insert k v) s) (i'.fold (fun acc k v => acc.insert k v) s') := by
  refine ⟨fun k hk hkv => ?_, fun k hk hka hkl => ?_, fun o w ho _ hw => ?_, fun k ha => ?_, he.frozen, ?_,
    fun k w δ x hp => ?_⟩
  · rw [fold_ins_get, fold_ins_get, he.src k hk, h.src k hk hkv]
  · rw [fold_ins_get, he.ghost k hk hka]
    exact h.ghost k hk hka hkl
  · rw [(hS o ho).2] at hw; cases hw
  · rcases he.alias k ha with ⟨v, hg, hi⟩ | ⟨hi, v, hf, hg⟩
    · exact ⟨v, hg, by rw [fold_ins_get, hi]; rfl⟩
    · refine ⟨v, hg, ?_⟩
      rw [fold_ins_get, hi]
      obtain ⟨w, hw, hs'⟩ := h.alias k ha
      rw [h.frozen k v hf] at hw
      cases hw
      exact hs'
  · intro k hk
    rw [fold_ins_get, hc k hk, h.clean k hk]; rfl
  · have hl := Reserved.pin_loose G k _ hp
    refine (h.pin k w δ x hp).congr ?_ ?_
    · rw [fold_ins_get, he.ghost k (pin_res hp) (Reserved.loose_alias G k hl)]; rfl
    · rw [fold_ins_get, he.ghost _ (Reserved.shadow_res k (pin_res hp))
        (Reserved.loose_alias G _ (Reserved.loose_shadow G k hl))]; rfl

theorem SR.foldS {s s' : StackFrame} (h : SR G gs s s') (m : StackFrame)
    (hm : ∀ kv ∈ m.toList, ¬ Reserved.res kv.1) (hS : Strict G) :
    SR G gs (m.fold (fun acc k v => acc.insert k v) s) (m.fold (fun acc k v => acc.insert k v) s') := by
  rw [Std.HashMap.fold_eq_foldl_toList, Std.HashMap.fold_eq_foldl_toList]
  generalize m.toList = l at hm
  induction l generalizing s s' with
  | nil => exact h
  | cons kv l ih =>
    exact ih (h.insertS (hm kv (List.mem_cons_self ..)) hS _) (fun x hx => hm x (List.mem_cons_of_mem _ hx))

theorem Strict.not_free (h : Strict G) : ¬ Free G := fun ⟨o, ho, hc⟩ => (h o ho).1 hc

def Clean (f : StackFrame) : Prop := ∀ k, Reserved.res k → f[k]? = none

theorem Clean.empty : Clean ({} : StackFrame) := fun _ _ => by simp

theorem Clean.insert {f : StackFrame} (h : Clean f) {k : String} (hk : ¬ Reserved.res k) (v : Value) :
    Clean (f.insert k v) := by
  intro j hj
  simp only [Std.HashMap.getElem?_insert]
  split
  · rename_i he; simp only [beq_iff_eq] at he; subst he; exact absurd hj hk
  · exact h j hj

theorem Clean.foldl {f : StackFrame} (h : Clean f) {l : List γ} (key : γ → String) (val : γ → Value)
    (hl : ∀ x ∈ l, ¬ Reserved.res (key x)) :
    Clean (l.foldl (fun acc x => acc.insert (key x) (val x)) f) := by
  induction l generalizing f with
  | nil => exact h
  | cons x xs ih =>
    exact ih (h.insert (hl x (List.mem_cons_self ..)) _) (fun y hy => hl y (List.mem_cons_of_mem _ hy))

theorem Clean.foldl_gen {f : StackFrame} (h : Clean f) {l : List γ} {F : StackFrame → γ → StackFrame}
    (hF : ∀ acc, Clean acc → ∀ x ∈ l, Clean (F acc x)) : Clean (l.foldl F f) := by
  induction l generalizing f with
  | nil => exact h
  | cons x xs ih =>
    exact ih (hF _ h x (List.mem_cons_self ..)) (fun acc ha y hy => hF acc ha y (List.mem_cons_of_mem _ hy))

theorem Clean.fold {m f : StackFrame} (hm : Clean m) (hf : Clean f) :
    Clean (m.fold (fun acc k v => acc.insert k v) f) := by
  rw [Std.HashMap.fold_eq_foldl_toList]
  refine hf.foldl_gen (fun acc ha kv hkv => ha.insert (fun hr => ?_) _)
  have hnone := hm kv.1 hr
  rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] at hkv
  rw [hkv] at hnone
  cases hnone

def IsAbsent (w : Value) : Prop := ∃ a, w = .data "$absent" a

def WFG (G : StackFrame) : Prop :=
  ∀ k, Reserved.res k → (G[shadowKey k]? = none ∨ ∃ q, q ≠ #[] ∧ G[shadowKey k]? = some (.seq q)) ∧
    ∀ w, G[k]? = some w → ¬ IsAbsent w

theorem WFG.empty : WFG ({} : StackFrame) := fun _ _ => ⟨.inl (by simp), fun _ h => by simp at h⟩

omit [Reserved] in
theorem shadowKey_ne (n : String) : shadowKey n ≠ n := by
  intro h
  have := congrArg String.length h
  simp [shadowKey] at this

def Tracked (G : StackFrame) (k : String) : Prop := ¬ Reserved.aliasOf G k ∧ ¬ Reserved.loose G k

theorem tracked_default (h : ∀ G k, ¬ Reserved.aliasOf G k) (hl : ∀ G k, ¬ Reserved.loose G k) (G : StackFrame)
    (k : String) : Tracked G k := ⟨h G k, hl G k⟩

theorem Tracked.bind {n k : String} (hn : Reserved.res n) (v : Value) (h : Tracked G k) :
    Tracked (Interpreter.bindCatch G n v) k :=
  ⟨fun ha => h.1 ((Reserved.alias_bind G n v k hn).mp ha), fun hl => h.2 ((Reserved.loose_bind G n v k hn).mp hl)⟩

theorem SR.shadowDepth_r {s s' : StackFrame} (h : SR G gs s s') {n : String} (hn : Reserved.res n)
    (ht : Tracked G (shadowKey n)) :
    Interpreter.shadowDepth s' n = Interpreter.shadowDepth G n := by
  unfold Interpreter.shadowDepth
  rw [h.ghost _ (Reserved.shadow_res n hn) ht.1 ht.2]

theorem bindCatch_unres {n k : String} (hn : Reserved.res n) (hk : ¬ Reserved.res k) (f : StackFrame) (v : Value) :
    (Interpreter.bindCatch f n v)[k]? = f[k]? := by
  have hs := Reserved.shadow_res n hn
  unfold Interpreter.bindCatch
  simp only [Std.HashMap.getElem?_insert]
  rw [ite_eq_right (by simp only [beq_iff_eq]; rintro rfl; exact hk hn),
    ite_eq_right (by simp only [beq_iff_eq]; rintro rfl; exact hk hs)]

theorem bindCatch_contains_unres {n k : String} (hn : Reserved.res n) (hk : ¬ Reserved.res k) (f : StackFrame)
    (v : Value) : (Interpreter.bindCatch f n v).contains k = f.contains k := by
  rw [← Std.HashMap.isSome_getElem?_eq_contains, ← Std.HashMap.isSome_getElem?_eq_contains,
    bindCatch_unres hn hk]

theorem strict_bind_iff {n : String} (hn : Reserved.res n) (v : Value) :
    Strict (Interpreter.bindCatch G n v) ↔ Strict G := by
  unfold Strict
  refine forall_congr' (fun o => imp_congr_right (fun ho => ?_))
  have ⟨h1, h2, _⟩ := Reserved.vret_ok o ho
  rw [bindCatch_unres hn h1, bindCatch_contains_unres hn h2]

omit [Reserved] in
theorem bindCatch_ne {f : StackFrame} {n k : String} (h1 : n ≠ k) (h2 : shadowKey n ≠ k) (v : Value) :
    (Interpreter.bindCatch f n v)[k]? = f[k]? := by
  unfold Interpreter.bindCatch
  simp only [Std.HashMap.getElem?_insert]
  rw [ite_eq_right (by simpa using h1), ite_eq_right (by simpa using h2)]

theorem SR.bind_r {s s' : StackFrame} (h : SR G gs s s') {n : String} (hn : Reserved.res n) (v : Value)
    (ht : Tracked G n) (hts : Tracked G (shadowKey n)) :
    SR (Interpreter.bindCatch G n v) gs s (Interpreter.bindCatch s' n v) := by
  have hs := Reserved.shadow_res n hn
  refine ⟨fun k hk hkv => ?_, fun k hk hka hkl => ?_, fun o w ho hf hw => ?_, fun k ha => ?_, fun k w hw => ?_, h.clean,
    fun k w δ x hp => ?_⟩
  · rw [bindCatch_unres hn hk]
    exact h.src k hk (hkv.imp id (strict_bind_iff hn v).mp)
  · unfold Interpreter.bindCatch
    rw [h.ghost _ hs hts.1 hts.2, h.ghost _ hn ht.1 ht.2]
    simp only [Std.HashMap.getElem?_insert]
    split
    · rfl
    · split
      · rfl
      · exact h.ghost k hk (fun ha => hka ((Reserved.alias_bind G n v k hn).mpr ha))
          (fun hl => hkl ((Reserved.loose_bind G n v k hn).mpr hl))
  · have ⟨h1, h2, _⟩ := Reserved.vret_ok o ho
    rw [bindCatch_unres hn h1]
    rw [bindCatch_contains_unres hn h2] at hf
    rw [bindCatch_unres hn h1] at hw
    exact h.out o w ho hf hw
  · have ha' := (Reserved.alias_bind G n v k hn).mp ha
    rw [bindCatch_ne (fun e => ht.1 (by rw [e]; exact ha')) (fun e => hts.1 (by rw [e]; exact ha'))]
    exact h.alias k ha'
  · rw [Reserved.frozen_bind G n v k hn] at hw
    exact h.frozen k w hw
  · rw [Reserved.pin_bind G n v k hn] at hp
    have hl := Reserved.pin_loose G k _ hp
    have hls := Reserved.loose_shadow G k hl
    refine (h.pin k w δ x hp).congr ?_ ?_
    · exact bindCatch_ne (fun e => ht.2 (by rw [e]; exact hl)) (fun e => hts.2 (by rw [e]; exact hl)) v
    · exact bindCatch_ne (fun e => ht.2 (by rw [e]; exact hls))
        (fun e => ht.2 (by rw [(String.append_right_inj _).mp e]; exact hl)) v

omit [Reserved] in
theorem shadowKey_inj {a b : String} (h : shadowKey a = shadowKey b) : a = b :=
  (String.append_right_inj _).mp h

theorem WFG.bind {n : String} (h : WFG G) (hnk : ∀ k, shadowKey k ≠ n) {v : Value} (hv : ¬ IsAbsent v) :
    WFG (bindCatch G n v) := by
  intro k hk
  unfold Interpreter.bindCatch
  have hne := shadowKey_ne n
  refine ⟨?_, fun w hw => ?_⟩
  · simp only [Std.HashMap.getElem?_insert]
    by_cases e : k = n
    · subst e
      rw [ite_eq_right (by simpa using fun h => hne h.symm), ite_eq_left (by simp)]
      exact .inr ⟨_, by simp, rfl⟩
    · rw [ite_eq_right (by simpa using fun h => hnk k h.symm),
        ite_eq_right (by simpa using fun h => e (shadowKey_inj h).symm)]
      exact (h k hk).1
  · simp only [Std.HashMap.getElem?_insert] at hw
    split at hw
    · cases hw; exact hv
    · split at hw
      · cases hw; rintro ⟨a, ha⟩; cases ha
      · exact (h k hk).2 w hw

omit [Reserved] in
theorem popShadowsGo_stop {f : StackFrame} {n : String} {d : Nat} (h : ¬ Interpreter.shadowDepth f n > d) (k : Nat) :
    popShadowsGo n d k f = f := by
  cases k <;> simp [popShadowsGo, h]

set_option hygiene false in
macro "stop_tac" : tactic => `(tactic| (
  simp only [Interpreter.shadowDepth]
  first
  | rw [Std.HashMap.getElem?_insert, ite_eq_right (by simpa using hne'), Std.HashMap.getElem?_insert_self]; simp
  | rw [Std.HashMap.getElem?_erase, ite_eq_right (by simpa using hne'), Std.HashMap.getElem?_insert_self]; simp))

set_option linter.unusedSimpArgs false in
theorem SR.unwind_r {s s' : StackFrame} {n : String} {v : Value} (h : SR (Interpreter.bindCatch G n v) gs s s')
    (hn : Reserved.res n) (hwf : WFG G) (ht : Tracked G n) (hts : Tracked G (shadowKey n)) :
    SR G gs s (Interpreter.popShadowsTo s' n (Interpreter.shadowDepth G n)) := by
  have hs := Reserved.shadow_res n hn
  have hne := shadowKey_ne n
  have e1 : s'[shadowKey n]? = (Interpreter.bindCatch G n v)[shadowKey n]? :=
    h.ghost _ hs (hts.bind hn v).1 (hts.bind hn v).2
  have e2 : s'[n]? = (Interpreter.bindCatch G n v)[n]? := h.ghost _ hn (ht.bind hn v).1 (ht.bind hn v).2
  simp only [Interpreter.bindCatch, Std.HashMap.getElem?_insert] at e1 e2
  rw [ite_eq_right (by simpa using fun h => hne h.symm), ite_eq_left (by simp)] at e1
  rw [ite_eq_left (by simp)] at e2
  obtain ⟨hsk, hab⟩ := hwf n hn
  have key : ∀ k, (Interpreter.popShadowsTo s' n (Interpreter.shadowDepth G n))[k]? =
      if n = k then G[n]? else if shadowKey n = k then G[shadowKey n]? else s'[k]? := by
    intro k
    have hne' : n ≠ shadowKey n := fun h => hne h.symm
    rcases hsk with hsk | ⟨q, hq, hsk⟩ <;> rcases hG : G[n]? with _ | w <;> simp only [hsk, hG] at e1 e2
    · simp [Interpreter.popShadowsTo, Interpreter.popShadowsGo, Interpreter.shadowDepth,
        Interpreter.unbindCatch, Interpreter.savedPrior, e1, hsk, Std.HashMap.getElem?_insert,
        Std.HashMap.getElem?_erase]
    · simp [Interpreter.popShadowsTo, Interpreter.popShadowsGo, Interpreter.shadowDepth,
        Interpreter.unbindCatch, Interpreter.savedPrior, e1, hsk, hG, Std.HashMap.getElem?_insert,
        Std.HashMap.getElem?_erase]
    · simp only [Interpreter.popShadowsTo, Interpreter.shadowDepth, hsk, e1, savedPrior, Array.size_push, popShadowsGo, gt_iff_lt, Nat.lt_add_one, ↓reduceIte, Interpreter.unbindCatch, Array.back?_push, List.size_toArray, List.length_nil, Nat.lt_irrefl, not_false_eq_true, getElem?_neg, Nat.reduceBeqDiff, beq_iff_eq, Array.size_eq_zero_iff, hq, Array.pop_push]
      rw [popShadowsGo_stop (by stop_tac)]
      simp [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase]
    · simp only [Interpreter.popShadowsTo, Interpreter.shadowDepth, hsk, e1, savedPrior, Array.size_push, popShadowsGo, gt_iff_lt, Nat.lt_add_one, ↓reduceIte, Interpreter.unbindCatch, Array.back?_push, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, getElem?_pos, List.getElem_toArray, List.getElem_cons_zero, Nat.reduceBeqDiff, beq_iff_eq, Array.size_eq_zero_iff, hq, Array.pop_push]
      rw [popShadowsGo_stop (by stop_tac)]
      simp [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase]
  refine ⟨fun k hk hkv => ?_, fun k hk hka hkl => ?_, fun o w ho hf hw => ?_, fun k ha => ?_, fun k w hw => ?_, h.clean,
    fun k w δ x hp => ?_⟩
  · rw [key, ite_eq_right (fun e => hk (by subst e; exact hn)), ite_eq_right (fun e => hk (by rw [← e]; exact hs))]
    exact h.src k hk (hkv.imp id (strict_bind_iff hn v).mpr)
  · rw [key]
    split
    · rename_i e; subst e; rfl
    · split
      · rename_i e; subst e; rfl
      · rename_i e1' e2'
        rw [h.ghost k hk (fun ha => hka ((Reserved.alias_bind G n v k hn).mp ha))
          (fun hl => hkl ((Reserved.loose_bind G n v k hn).mp hl))]
        simp only [Interpreter.bindCatch, Std.HashMap.getElem?_insert]
        rw [ite_eq_right (by simpa using e1'), ite_eq_right (by simpa using e2')]
  · have ⟨h1, h2, _⟩ := Reserved.vret_ok o ho
    rw [key, ite_eq_right (fun e => h1 (by subst e; exact hn)), ite_eq_right (fun e => h1 (by rw [← e]; exact hs))]
    refine h.out o w ho ?_ ?_
    · rw [bindCatch_contains_unres hn h2]; exact hf
    · rw [bindCatch_unres hn h1]; exact hw
  · rw [key, ite_eq_right (fun e => ht.1 (by rw [e]; exact ha)), ite_eq_right (fun e => hts.1 (by rw [e]; exact ha))]
    exact h.alias k ((Reserved.alias_bind G n v k hn).mpr ha)
  · exact h.frozen k w (by rw [Reserved.frozen_bind G n v k hn]; exact hw)
  · have hl := Reserved.pin_loose G k _ hp
    have hls := Reserved.loose_shadow G k hl
    refine (h.pin k w δ x (by rw [Reserved.pin_bind G n v k hn]; exact hp)).congr ?_ ?_
    · rw [key, ite_eq_right (fun e => ht.2 (by rw [e]; exact hl)), ite_eq_right (fun e => hts.2 (by rw [e]; exact hl))]
    · rw [key, ite_eq_right (fun e => ht.2 (by rw [e]; exact hls)),
        ite_eq_right (fun e => ht.2 (by rw [(String.append_right_inj _).mp e]; exact hl))]

theorem Clean.keys {m : StackFrame} (h : Clean m) : ∀ kv ∈ m.toList, ¬ Reserved.res kv.1 := by
  intro kv hkv hr
  have hnone := h kv.1 hr
  rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] at hkv
  rw [hkv] at hnone
  cases hnone

theorem Clean.params (ps : List Parameter) (vs : List Value) (h : ∀ x ∈ ps, ¬ Reserved.res x.name.text) :
    Clean ((ps.zip vs).foldl (fun acc (param, v) => acc.insert param.name.text v) {}) := by
  suffices ∀ (f : StackFrame), Clean f → Clean ((ps.zip vs).foldl (fun acc (param, v) => acc.insert param.name.text v) f) from
    this _ Clean.empty
  induction ps generalizing vs with
  | nil => intro f hf; exact hf
  | cons p ps ih =>
    intro f hf
    cases vs with
    | nil => exact hf
    | cons v vs =>
      exact ih vs (fun x hx => h x (List.mem_cons_of_mem _ hx)) _ (hf.insert (h p (List.mem_cons_self ..)) _)

theorem SR.outs {s s' : StackFrame} (h : SR G gs s s') {os : List Parameter}
    (hn : ∀ x ∈ os, ¬ Reserved.res x.name.text) (hv : ∀ x ∈ os, NotV x.name.text ∨ Strict G) :
    os.toArray.map (fun o => s'[o.name.text]?.getD .unset) = os.toArray.map (fun o => s[o.name.text]?.getD .unset) := by
  simp only [List.map_toArray]
  congr 1
  exact List.map_congr_left (fun x hx => by rw [h.get (hn x hx) (hv x hx)])

theorem SR.outsFold {s s' : StackFrame} (h : SR G gs s s') {os : List Parameter}
    (hn : ∀ x ∈ os, ¬ Reserved.res x.name.text) (hv : ∀ x ∈ os, NotV x.name.text ∨ Strict G) (init : StackFrame) :
    os.foldl (fun acc o => acc.insert o.name.text (s'[o.name.text]?.getD .unset)) init =
      os.foldl (fun acc o => acc.insert o.name.text (s[o.name.text]?.getD .unset)) init := by
  induction os generalizing init with
  | nil => rfl
  | cons o os ih =>
    simp only [List.foldl_cons]
    rw [h.get (hn o (List.mem_cons_self ..)) (hv o (List.mem_cons_self ..))]
    exact ih (fun x hx => hn x (List.mem_cons_of_mem _ hx)) (fun x hx => hv x (List.mem_cons_of_mem _ hx)) _

end

structure StRel [Reserved] (G : StackFrame) (IR : ProgramIndex → ProgramIndex → Prop) (σ σ' : EvalState) : Prop where
  stack : SR G σ.globals σ.stack σ'.stack
  wf : WFG G
  entryClean : ∀ h g i, σ.entryState = some (h, g, i) → Clean i
  heap : σ'.heap = σ.heap
  steps : σ.steps = none
  steps' : σ'.steps = none
  quiet : σ'.quiet = σ.quiet
  muted : σ'.muted = σ.muted
  globals : GlR σ.globals σ'.globals
  coros : σ'.coros = σ.coros
  coroSelf : σ.coroSelf = none
  coroSelf' : σ'.coroSelf = none
  seek : σ.seek = none
  seek' : σ'.seek = none
  entR : EntR G σ.entryState σ'.entryState
  inOld : σ'.inOld = σ.inOld
  ops : σ.operands = []
  ops' : σ'.operands = []
  index : IR σ.index σ'.index
  gk : ∀ k, NG k → σ.globals.contains k = false
  gk' : ∀ k, NG k → σ'.globals.contains k = false
  egk : ∀ h g i, σ.entryState = some (h, g, i) → ∀ k, NG k → g.contains k = false
  openLabels : ∀ l, ¬ Reserved.resLabel l → (l ∈ σ.openLabels ↔ l ∈ σ'.openLabels)

/-- Opening a reserved label in the target keeps the states related. -/
theorem StRel.pushOL [Reserved] {G : StackFrame} {IR : ProgramIndex → ProgramIndex → Prop} {σ σ' : EvalState} {L : String}
    (h : StRel G IR σ σ') (hL : Reserved.resLabel L) : StRel G IR σ { σ' with openLabels := L :: σ'.openLabels } := by
  have hk : ∀ k, ¬ Reserved.resLabel k → (k ∈ σ.openLabels ↔ k ∈ L :: σ'.openLabels) := fun k hk => by
    rw [h.openLabels k hk, List.mem_cons]
    exact (or_iff_right (fun (e : k = L) => hk (e ▸ hL))).symm
  exact { h with openLabels := hk }

/-- Closing a reserved label in the target keeps the states related. -/
theorem StRel.restoreOL [Reserved] {G : StackFrame} {IR : ProgramIndex → ProgramIndex → Prop} {σ σ' : EvalState}
    {L : String} {ol : List String} (h : StRel G IR σ σ') (hk : σ'.openLabels = L :: ol) (hL : Reserved.resLabel L) :
    StRel G IR σ { σ' with openLabels := ol } := by
  have hk' : ∀ k, ¬ Reserved.resLabel k → (k ∈ σ.openLabels ↔ k ∈ ol) := fun k hk' => by
    rw [h.openLabels k hk', hk, List.mem_cons]
    exact or_iff_right (fun (e : k = L) => hk' (e ▸ hL))
  exact { h with openLabels := hk' }


section
variable [Reserved] (E : StmtExprMd → StmtExprMd → Prop)

def VarRel : Variable → Variable → Prop
  | .Local n, .Local n' => n.text = n'.text ∧ ¬ Reserved.res n.text
  | .Field t f, .Field t' f' => E t t' ∧ f.text = f'.text
  | .Declare p, .Declare p' => p.name.text = p'.name.text ∧ ORel (fun a b => Reserved.tyR a.val b.val) p.type p'.type ∧
      ¬ Reserved.res p.name.text ∧ NotV p.name.text
  | _, _ => False

def WOK : Variable → Prop
  | .Local n => NotV n.text
  | _ => True

def FinP (e : StmtExprMd) : Prop :=
  (match e.val with
  | .Var (.Local n) => NotV n.text
  | .Return _ => Reserved.vret = none
  | .Old .. => Reserved.vret = none
  | .IncrDecr _ _ t => ∀ G a, t.val = .Local a → Reserved.nodeOK G ⟨.Var (.Local a), .unknown⟩
  | .CompoundAssign _ t _ => ∀ G a, t.val = .Local a → Reserved.nodeOK G ⟨.Var (.Local a), .unknown⟩
  | .While _ is _ _ _ => ∀ G, ∀ i ∈ is, Reserved.nodeOK G ⟨.Assert i none, i.source⟩
  | _ => True) ∧ ∀ G, Reserved.nodeOK G e

def FinOK (f : Option StmtExprMd) : Prop := ∀ x, f = some x → Hered FinP x

def CondRel (c c' : Condition) : Prop :=
  c.mode = c'.mode ∧ E c.condition c'.condition ∧ Reserved.vok E c.condition c'.condition

def CatchRel (c c' : CatchClause) : Prop :=
  c.binding.text = c'.binding.text ∧ ORel E c.predicate c'.predicate ∧ E c.body c'.body ∧
    ¬ Reserved.res c.binding.text ∧ NotV c.binding.text ∧ Reserved.tyR c.bindingType.val c'.bindingType.val

inductive LX (X : StmtExprMd → List StmtExprMd → Prop) : List StmtExprMd → List StmtExprMd → Prop where
  | nil : LX X [] []
  | cons {a b as bs} : E a b → LX X as bs → LX X (a :: as) (b :: bs)
  | expand {a ts as bs} : X a ts → LX X as bs → LX X (a :: as) (ts ++ bs)

inductive LXv (X : StmtExprMd → List StmtExprMd → Prop) : List StmtExprMd → List StmtExprMd → Prop where
  | nil : LXv X [] []
  | snoc_e {i i' : List StmtExprMd} {x y : StmtExprMd} : LX E X i i' → E x y → Reserved.vok E x y →
      LXv X (i ++ [x]) (i' ++ [y])
  | snoc_x {i i' ts : List StmtExprMd} {x : StmtExprMd} : LX E X i i' → X x ts → Reserved.vokX E x ts →
      LXv X (i ++ [x]) (i' ++ ts)

def Corr (l : String) (ss ss' : List StmtExprMd) (j j' : Nat) : Prop :=
  ∃ pre a post pre' b post', ss = pre ++ a :: post ∧ ss' = pre' ++ b :: post' ∧ j = pre.length ∧
    j' = pre'.length ∧ LX E (Reserved.ex E) pre pre' ∧ E a b ∧ LX E (Reserved.ex E) post post' ∧
    l ∈ statementLabels a

def CallRel (f f' : Identifier) : Prop := (f = f' ∧ ¬ Reserved.resCall f) ∨ Reserved.ren f f'

def RenProc (P P' : Procedure) : Prop :=
  P.name.uniqueId = P'.name.uniqueId ∧ Reserved.resProc P.name.text ∧ Reserved.resProc P'.name.text ∧
    P.body ≠ .External

def LabOK (l : Option String) : Prop := ∀ L, Reserved.retLabel = some L → l ≠ some L

def NotYield (v : StmtExprMd) : Prop := match v.val with | .Yield => False | _ => True

def Unsup : StmtExpr → Prop
  | .PureFieldUpdate .. | .This | .Assigned .. | .OldGuarantee .. | .OldRelies ..
  | .Fresh .. | .ProveBy .. | .Abstract | .All | .Snapshot .. => True
  | .ContractOf ty _ => ty ≠ .Precondition
  | _ => False

inductive Shape : StmtExprMd → StmtExprMd → Prop where
  | ite {c th c' th' : StmtExprMd} {el el' : Option StmtExprMd} {s s' : FileRange} :
      E c c' → E th th' → ORel E el el' → Shape ⟨.IfThenElse c th el, s⟩ ⟨.IfThenElse c' th' el', s'⟩
  | block {ss ss' : List StmtExprMd} {l : Option String} {s s' : FileRange} :
      LX E (Reserved.ex E) ss ss' → LabOK l → Shape ⟨.Block ss l [] none, s⟩ ⟨.Block ss' l [] none, s'⟩
  | while_ {c c' b b' : StmtExprMd} {is is' : List StmtExprMd} {d d' : Option StmtExprMd} {p : Bool}
      {s s' : FileRange} :
      E c c' → L2 E is is' → E b b' → Shape ⟨.While c is d b p, s⟩ ⟨.While c' is' d' b' p, s'⟩
  | jump {l : String} {d : GotoDestination} {s s' : FileRange} : Shape ⟨.Goto l d, s⟩ ⟨.Goto l d, s'⟩
  | ret {v v' : List StmtExprMd} {s s' : FileRange} :
      v.length ≤ 1 → L2 E v v' → Shape ⟨.Return v, s⟩ ⟨.Return v', s'⟩
  | litInt {n : Int} {s s' : FileRange} : Shape ⟨.LiteralInt n, s⟩ ⟨.LiteralInt n, s'⟩
  | litBool {b : Bool} {s s' : FileRange} : Shape ⟨.LiteralBool b, s⟩ ⟨.LiteralBool b, s'⟩
  | litString {x : String} {s s' : FileRange} : Shape ⟨.LiteralString x, s⟩ ⟨.LiteralString x, s'⟩
  | litDecimal {d : StrataDDM.Decimal} {s s' : FileRange} :
      Shape ⟨.LiteralDecimal d, s⟩ ⟨.LiteralDecimal d, s'⟩
  | litBv {v w : Nat} {s s' : FileRange} : Shape ⟨.LiteralBv v w, s⟩ ⟨.LiteralBv v w, s'⟩
  | var {v v' : Variable} {s s' : FileRange} : VarRel E v v' → Shape ⟨.Var v, s⟩ ⟨.Var v', s'⟩
  | assign {ts ts' : List VariableMd} {v v' : StmtExprMd} {s s' : FileRange} :
      L2 (fun a b => VarRel E a.val b.val ∧ WOK a.val) ts ts' → E v v' → NotYield v → NotYield v' →
      Shape ⟨.Assign ts v, s⟩ ⟨.Assign ts' v', s'⟩
  | call {f f' : Identifier} {as as' : List StmtExprMd} {ta ta' : List HighTypeMd} {s s' : FileRange} :
      L2 E as as' → L2 (fun a b => Reserved.tyR a.val b.val) ta ta' → CallRel f f' →
      Shape ⟨.Call none f as ta, s⟩ ⟨.Call none f' as' ta', s'⟩
  | icall {t t' : StmtExprMd} {f f' : Identifier} {as as' : List StmtExprMd} {ta ta' : List HighTypeMd}
      {s s' : FileRange} :
      E t t' → f.text = f'.text → L2 E as as' → ¬ Reserved.resProc f.text → ¬ Reserved.resMethods →
      f.uniqueId = f'.uniqueId → Shape ⟨.Call (some t) f as ta, s⟩ ⟨.Call (some t') f' as' ta', s'⟩
  | new_ {r r' : Identifier} {o o' : List HighTypeMd} {s s' : FileRange} :
      (∀ (E' : StmtExprMd → StmtExprMd → Prop) (ix ix' : ProgramIndex), Reserved.ixX E' ix ix' →
        (∀ t t', Reserved.tyR t t' → ix'.unalias t' = ix.unalias t) →
        (ix.allocName r o).text = (ix'.allocName r' o').text) → Shape ⟨.New r o, s⟩ ⟨.New r' o', s'⟩
  | isType {t t' : StmtExprMd} {ty ty' : HighTypeMd} {s s' : FileRange} :
      E t t' → Reserved.tyR ty.val ty'.val → Shape ⟨.IsType t ty, s⟩ ⟨.IsType t' ty', s'⟩
  | asType {t t' : StmtExprMd} {ty ty' : HighTypeMd} {s s' : FileRange} :
      E t t' → Reserved.tyR ty.val ty'.val → Shape ⟨.AsType t ty, s⟩ ⟨.AsType t' ty', s'⟩
  | refEq {a a' b b' : StmtExprMd} {s s' : FileRange} :
      E a a' → E b b' → Shape ⟨.ReferenceEquals a b, s⟩ ⟨.ReferenceEquals a' b', s'⟩
  | throw_ {v v' : StmtExprMd} {s s' : FileRange} : E v v' → Shape ⟨.Throw v, s⟩ ⟨.Throw v', s'⟩
  | try_ {b b' : StmtExprMd} {cs cs' : List CatchClause} {f f' : Option StmtExprMd} {s s' : FileRange} :
      E b b' → L2 (CatchRel E) cs cs' → ORel E f f' → FinOK f → Shape ⟨.Try b cs f, s⟩ ⟨.Try b' cs' f', s'⟩
  | assert {c c' : StmtExprMd} {m m' : Option String} {s s' : FileRange} :
      E c c' → Shape ⟨.Assert c m, s⟩ ⟨.Assert c' m', s'⟩
  | assume {c c' : StmtExprMd} {s s' : FileRange} : E c c' → Shape ⟨.Assume c, s⟩ ⟨.Assume c', s'⟩
  | old {v v' : StmtExprMd} {l : Option Identifier} {s s' : FileRange} :
      E v v' → Shape ⟨.Old v l, s⟩ ⟨.Old v' l, s'⟩
  | incr {m : IncrDecrMode} {o : IncrDecrOp} {t t' : VariableMd} {s s' : FileRange} :
      VarRel E t.val t'.val → WOK t.val → Shape ⟨.IncrDecr m o t, s⟩ ⟨.IncrDecr m o t', s'⟩
  | compound {o : Operation} {t t' : VariableMd} {r r' : StmtExprMd} {s s' : FileRange} :
      VarRel E t.val t'.val → WOK t.val → E r r' → ¬ Reserved.resProc o.procName →
      Shape ⟨.CompoundAssign o t r, s⟩ ⟨.CompoundAssign o t' r', s'⟩
  | hole {d d' : Bool} {ty ty' : HighTypeMd} {s s' : FileRange} :
      Reserved.tyR ty.val ty'.val → Shape ⟨.Hole d (some ty), s⟩ ⟨.Hole d' (some ty'), s'⟩
  | holeNone {d d' : Bool} {s s' : FileRange} : Shape ⟨.Hole d none, s⟩ ⟨.Hole d' none, s'⟩
  | quant {m : QuantifierMode} {p p' : Parameter} {tr tr' : Option StmtExprMd} {b b' : StmtExprMd}
      {s s' : FileRange} :
      p.name.text = p'.name.text → Reserved.tyR p.type.val p'.type.val → ¬ Reserved.res p.name.text →
      NotV p.name.text → E b b' → Shape ⟨.Quantifier m p tr b, s⟩ ⟨.Quantifier m p' tr' b', s'⟩
  | unsup {v v' : StmtExpr} {s s' : FileRange} : Unsup v → Unsup v' → Shape ⟨v, s⟩ ⟨v', s'⟩

omit [Reserved] in
theorem LX.append {X : StmtExprMd → List StmtExprMd → Prop} {l₁ l₂ l₁' l₂' : List StmtExprMd}
    (h₁ : LX E X l₁ l₁') (h₂ : LX E X l₂ l₂') : LX E X (l₁ ++ l₂) (l₁' ++ l₂') := by
  induction h₁ with
  | nil => exact h₂
  | cons hab _ ih => exact .cons hab ih
  | expand hab _ ih => rw [List.append_assoc]; exact .expand hab ih

def LabAgree (l : String) : Prop := ∀ a b, E a b → (l ∈ statementLabels a ↔ l ∈ statementLabels b)

def ExLabFree (l : String) : Prop :=
  ∀ a ts, Reserved.ex E a ts → l ∉ statementLabels a ∧ ∀ t ∈ ts, l ∉ statementLabels t

theorem LX.flatLabels {l : String} (hX : ExLabFree E l) {ss ss' : List StmtExprMd}
    (h : LX E (Reserved.ex E) ss ss') (hE : ∀ a b, E a b → a ∈ ss → (l ∈ statementLabels a ↔ l ∈ statementLabels b)) :
    (l ∈ (ss.map statementLabels).flatten ↔ l ∈ (ss'.map statementLabels).flatten) := by
  induction h with
  | nil => exact Iff.rfl
  | cons hab _ ih =>
    simp only [List.map_cons, List.flatten_cons, List.mem_append]
    exact or_congr (hE _ _ hab (List.mem_cons_self ..)) (ih (fun a b h hm => hE a b h (List.mem_cons_of_mem _ hm)))
  | @expand a ts as bs hab _ ih =>
    have ih := ih (fun a b h hm => hE a b h (List.mem_cons_of_mem _ hm))
    obtain ⟨h1, h2⟩ := hX a ts hab
    simp only [List.map_cons, List.flatten_cons, List.map_append, List.flatten_append, List.mem_append] at ih ⊢
    have : l ∉ (ts.map statementLabels).flatten := by
      simp only [List.mem_flatten, List.mem_map, not_exists, not_and]
      rintro _ ⟨t, ht, rfl⟩
      exact h2 t ht
    exact ⟨fun h => h.elim (fun h => absurd h h1) (fun h => Or.inr (ih.mp h)),
      fun h => h.elim (fun h => absurd h this) (fun h => Or.inr (ih.mpr h))⟩

theorem LX.find {l : String} (hE : LabAgree E l) (hX : ExLabFree E l) {ss ss' : List StmtExprMd}
    (h : LX E (Reserved.ex E) ss ss') :
    ORel (Corr E l ss ss') (ss.findIdx? (fun t => (statementLabels t).contains l))
      (ss'.findIdx? (fun t => (statementLabels t).contains l)) := by
  induction h with
  | nil => trivial
  | @cons a b as bs hab hr ih =>
    have hp : (statementLabels a).contains l = (statementLabels b).contains l :=
      Bool.eq_iff_iff.mpr (by rw [List.contains_iff_mem, List.contains_iff_mem]; exact hE _ _ hab)
    simp only [List.findIdx?_cons, ← hp]
    rcases hcv : (statementLabels a).contains l with _ | _
    · simp only [Bool.false_eq_true, ite_false]
      revert ih
      cases as.findIdx? (fun t => (statementLabels t).contains l) <;>
        cases bs.findIdx? (fun t => (statementLabels t).contains l) <;> simp only [Option.map_some, Option.map_none, ORel]
      all_goals first
        | exact id
        | (rintro ⟨pre, a', post, pre', b', post', e1, e2, e3, e4, e5, e6, e7, e8⟩
           exact ⟨a :: pre, a', post, b :: pre', b', post', by simp [e1], by simp [e2], by simp [e3], by simp [e4],
             .cons hab e5, e6, e7, e8⟩)
    · simp only [ite_true]
      exact ⟨[], a, as, [], b, bs, rfl, rfl, rfl, rfl, .nil, hab, hr, List.contains_iff_mem.mp hcv⟩
  | @expand a ts as bs hab hr ih =>
    obtain ⟨h1, h2⟩ := hX a ts hab
    have hpa : (statementLabels a).contains l = false := by
      cases hc : (statementLabels a).contains l
      · rfl
      · exact absurd (List.contains_iff_mem.mp hc) h1
    have hts : ts.findIdx? (fun t => (statementLabels t).contains l) = none := by
      rw [List.findIdx?_eq_none_iff]
      intro t ht
      cases hc : (statementLabels t).contains l
      · rfl
      · exact absurd (List.contains_iff_mem.mp hc) (h2 t ht)
    simp only [List.findIdx?_cons, hpa, Bool.false_eq_true, ite_false, List.findIdx?_append, hts, Option.none_or]
    revert ih
    cases as.findIdx? (fun t => (statementLabels t).contains l) <;>
      cases bs.findIdx? (fun t => (statementLabels t).contains l) <;> simp only [Option.map_some, Option.map_none, ORel]
    all_goals first
      | exact id
      | (rintro ⟨pre, a', post, pre', b', post', e1, e2, e3, e4, e5, e6, e7, e8⟩
         exact ⟨a :: pre, a', post, ts ++ pre', b', post', by simp [e1], by simp [e2], by simp [e3], by simp [e4]; omega,
           .expand hab e5, e6, e7, e8⟩)

theorem Shape.labels {l : String} (hX : ExLabFree E l) {s t : StmtExprMd} (h : Shape E s t)
    (hE : ∀ a b, E a b → a ∈ stmtExprChildren s.val → (l ∈ statementLabels a ↔ l ∈ statementLabels b)) :
    (l ∈ statementLabels s ↔ l ∈ statementLabels t) := by
  cases h with
  | @ite c th c' th' el el' _ _ h1 h2 h3 =>
    rw [statementLabels_ite, statementLabels_ite]
    simp only [List.mem_append]
    refine or_congr (hE _ _ h2 (by simp [stmtExprChildren])) ?_
    cases el with
    | none =>
      cases el' with
      | none => simp only [Option.map_none, Option.getD_none]
      | some e' => exact (h3 : False).elim
    | some e =>
      cases el' with
      | none => exact (h3 : False).elim
      | some e' =>
        simp only [Option.map_some, Option.getD_some]
        exact hE _ _ h3 (by simp [stmtExprChildren])
  | block hss _ =>
    rw [statementLabels_block, statementLabels_block]
    simp only [List.mem_append]
    exact or_congr Iff.rfl (LX.flatLabels E hX hss (fun a b h hm => hE a b h (by simp [stmtExprChildren, hm])))
  | unsup hu hu' =>
    rename_i v v'
    rename_i w w'
    rw [statementLabels_other w v (by intros; rintro rfl; exact hu) (by intros; rintro rfl; exact hu),
      statementLabels_other w' v' (by intros; rintro rfl; exact hu') (by intros; rintro rfl; exact hu')]
  | _ =>
    rw [statementLabels_other _ _ (by intros; nofun) (by intros; nofun),
      statementLabels_other _ _ (by intros; nofun) (by intros; nofun)]

theorem Shape.ann (hren : ∀ f f', Reserved.ren f f' → f.text ≠ stackShapeName ∧ f'.text ≠ stackShapeName)
    {s t : StmtExprMd} (h : Shape E s t) : (stackAnnotation? s).isNone = (stackAnnotation? t).isNone := by
  cases h with
  | @call f f' as as' ta ta' _ _ has _ hcr =>
    cases has with
    | nil =>
      simp only [stackAnnotation?]
      rcases hcr with ⟨rfl, -⟩ | hr
      · cases f.text == stackShapeName <;> simp
      · simp [(hren _ _ hr).1, (hren _ _ hr).2]
    | cons _ _ => simp [stackAnnotation?]
  | unsup hu hu' =>
    have h1 : ∀ v : StmtExpr, Unsup v → ∀ src, stackAnnotation? ⟨v, src⟩ = none := by
      intro v hv src
      cases v <;> simp_all [Unsup, stackAnnotation?]
    simp only [h1 _ hu, h1 _ hu', Option.isNone_none]
  | _ => simp [stackAnnotation?]

theorem allocName_refl (hte : TyEq) {ix ix' : ProgramIndex}
    (hu : ∀ t t', Reserved.tyR t t' → ix'.unalias t' = ix.unalias t) (r : Identifier) (o : List HighTypeMd) :
    ix'.allocName r o = ix.allocName r o := by
  unfold ProgramIndex.allocName
  rw [hu _ _ (hte.refl _)]

theorem Shape.newRefl (hte : TyEq) {r : Identifier} {o : List HighTypeMd} {s s' : FileRange} :
    Shape E ⟨.New r o, s⟩ ⟨.New r o, s'⟩ :=
  .new_ (fun _ _ _ _ hu => by rw [allocName_refl hte hu])

def LV (E : StmtExprMd → StmtExprMd → Prop) (l l' : List StmtExprMd) : Prop := L2 (Reserved.vok E) l l'

def OV (E : StmtExprMd → StmtExprMd → Prop) (o o' : Option StmtExprMd) : Prop := ∀ a b, o = some a → o' = some b → Reserved.vok E a b

def VV (E : StmtExprMd → StmtExprMd → Prop) (v v' : Variable) : Prop := ∀ t t' f f', v = .Field t f → v' = .Field t' f' → Reserved.vok E t t'

def ValKids (E : StmtExprMd → StmtExprMd → Prop) (s t : StmtExprMd) : Prop :=
  match s.val, t.val with
  | .IfThenElse c th el, .IfThenElse c' th' el' =>
      Reserved.vok E c c' ∧ (Reserved.vok E s t → Reserved.vok E th th' ∧ OV E el el')
  | .Block ss _ _ _, .Block ss' _ _ _ => Reserved.vok E s t → LXv E (Reserved.ex E) ss ss'
  | .While c is _ _ _, .While c' is' _ _ _ => Reserved.vok E c c' ∧ LV E is is'
  | .Return v, .Return v' => LV E v v'
  | .Var v, .Var v' => VV E v v'
  | .Assign ts v, .Assign ts' v' =>
      L2 (fun (a b : VariableMd) => VV E a.val b.val) ts ts' ∧ Reserved.vok E v v'
  | .Call none _ as _, .Call none _ as' _ => LV E as as'
  | .Call (some t) _ as _, .Call (some t') _ as' _ => Reserved.vok E t t' ∧ LV E as as'
  | .IsType t _, .IsType t' _ => Reserved.vok E t t'
  | .AsType t _, .AsType t' _ => Reserved.vok E t t'
  | .ReferenceEquals a b, .ReferenceEquals a' b' => Reserved.vok E a a' ∧ Reserved.vok E b b'
  | .Throw v, .Throw v' => Reserved.vok E v v'
  | .Assert v _, .Assert v' _ => Reserved.vok E v v'
  | .Assume v, .Assume v' => Reserved.vok E v v'
  | .Old v _, .Old v' _ => Reserved.vok E v v'
  | .Try _ cs _, .Try _ cs' _ =>
      L2 (fun c c' => OV E c.predicate c'.predicate) cs cs'
  | .IncrDecr _ _ t, .IncrDecr _ _ t' => VV E t.val t'.val
  | .CompoundAssign _ t r, .CompoundAssign _ t' r' => VV E t.val t'.val ∧ Reserved.vok E r r'
  | .Quantifier _ _ _ b, .Quantifier _ _ _ b' => Reserved.vok E b b'
  | _, _ => True

def NodeOK (G : StackFrame) (e : StmtExprMd) : Prop :=
  (match e.val with
  | .Var (.Local n) => NotV n.text ∨ Strict G
  | .Return [] => Strict G ∧ ¬ NoRet G
  | .Return [_] => (Reserved.vret = none ∨ Free G) ∧ ¬ NoRet G
  | .Old .. => Strict G
  | .IncrDecr _ _ t => ∀ a, t.val = .Local a → Reserved.nodeOK G ⟨.Var (.Local a), .unknown⟩
  | .CompoundAssign _ t _ => ∀ a, t.val = .Local a → Reserved.nodeOK G ⟨.Var (.Local a), .unknown⟩
  | .While _ is _ _ _ => ∀ i ∈ is, Reserved.nodeOK G ⟨.Assert i none, i.source⟩
  | _ => True) ∧ Reserved.nodeOK G e

def OvOK (G : StackFrame) (e : StmtExprMd) : Prop := Hered (NodeOK G) e

def declNames (s : StmtExprMd) : List String :=
  blockDeclarations [s]

inductive ImplRel (outs : List Parameter) : StmtExprMd → StmtExprMd → Prop where
  | plain {b b' : StmtExprMd} : Reserved.retLabel = none → E b b' → ImplRel outs b b'
  | wrapBlock {ss ss' : List StmtExprMd} {s s' : FileRange} {L : String} :
      Reserved.retLabel = some L → L2 E ss ss' →
      ImplRel outs ⟨.Block ss none [] none, s⟩ ⟨.Block ss' (some L) [] none, s'⟩
  | wrapOther {b b' : StmtExprMd} {s' : FileRange} {L : String} :
      Reserved.retLabel = some L → E b b' → blockDeclarations [b] = [] →
      (∀ l, ¬ Reserved.resLabel l → l ∉ statementLabels b) → (stackAnnotation? b).isNone = true →
      ImplRel outs b ⟨.Block [b'] (some L) [] none, s'⟩
  | valued {e e' : StmtExprMd} {o : Parameter} {s s' s1 s2 s3 : FileRange} {L : String} :
      Reserved.retLabel = some L → outs = [o] → E e e' → NotYield e' →
      ImplRel outs ⟨.Return [e], s⟩
        ⟨.Block [⟨.Assign [⟨.Local o.name, s1⟩] e', s2⟩, ⟨.Goto L .blockEnd, s3⟩] (some L) [] none, s'⟩
  | valuedB {e e' : StmtExprMd} {o : Parameter} {s s' s0 s1 s2 s3 s4 : FileRange} {L : String} :
      Reserved.retLabel = some L → outs = [o] → E e e' → NotYield e' →
      ImplRel outs ⟨.Block [⟨.Return [e], s0⟩] none [] none, s⟩
        ⟨.Block [⟨.Block [⟨.Assign [⟨.Local o.name, s1⟩] e', s2⟩, ⟨.Goto L .blockEnd, s3⟩] none [] none, s4⟩] (some L) [] none, s'⟩

inductive BodyRel (outs : List Parameter) : Body → Body → Prop where
  | transparent {b b' : StmtExprMd} : ImplRel E outs b b' → BodyRel outs (.Transparent b) (.Transparent b')
  | opq {ps ps' : List Condition} {i i' : Option StmtExprMd} {ms ms' : List ModifiesGroup} :
      L2 (CondRel E) ps ps' → ORel (ImplRel E outs) i i' →
      ms.any (!·.targets.isEmpty) = ms'.any (!·.targets.isEmpty) →
      BodyRel outs (.Opaque ps i ms) (.Opaque ps' i' ms')
  | abs {ps ps' : List Condition} : L2 (CondRel E) ps ps' → BodyRel outs (.Abstract ps) (.Abstract ps')
  | external : BodyRel outs .External .External

def valued (P : Procedure) : Bool :=
  match Reserved.vret with
  | some o => P.outputs.map (·.name.text) == [o]
  | none => false

def freeG : StackFrame :=
  match Reserved.vret with
  | some o => ({} : StackFrame).insert (freeKey o) .unset
  | none => {}

def condG : StackFrame :=
  match Reserved.vret with
  | some o => ({} : StackFrame).insert (noRetKey o) .unset
  | none => {}

def procG (P : Procedure) : StackFrame := if valued P then freeG else {}

def NC (b : StmtExprMd) : Prop :=
  ∀ (cfg : ExternalBackendM PM) n σ τ σ' τ', run (evalStmt cfg n b) σ τ ≠ .ok ((.ok (), σ'), τ')

def TargRel (t t' : StmtExprMd) : Prop :=
  (∃ o f s o' f' s', t = ⟨.Var (.Field o f), s⟩ ∧ t' = ⟨.Var (.Field o' f'), s'⟩ ∧ f.text = f'.text ∧ E o o' ∧
    Reserved.vok E o o' ∧ OvOK condG o) ∨
  ((∀ o f, t.val ≠ .Var (.Field o f)) ∧ (∀ o f, t'.val ≠ .Var (.Field o f)) ∧ E t t' ∧ Reserved.vok E t t' ∧
    OvOK condG t)

def GroupRel (g g' : ModifiesGroup) : Prop :=
  ORel E g.guard g'.guard ∧ OV E g.guard g'.guard ∧ (∀ e, g.guard = some e → OvOK condG e) ∧
    L2 (TargRel E) g.targets g'.targets

structure ProcRel (P P' : Procedure) : Prop where
  name : P.name = P'.name ∨ RenProc P P'
  inputs : L2 ParamR P.inputs P'.inputs
  outputs : L2 ParamR P.outputs P'.outputs
  pre : L2 (CondRel E) P.preconditions P'.preconditions
  coro : P.is_coroutine = false
  coro' : P'.is_coroutine = false
  body : BodyRel E P.outputs P.body P'.body
  writes : P.writesGlobals = P'.writesGlobals
  throws : P.throwsType = P'.throwsType
  outNames : ∀ x ∈ P.outputs, ¬ Reserved.res x.name.text
  inNames : ∀ x ∈ P.inputs, ¬ Reserved.res x.name.text
  inV : ∀ x ∈ P.inputs, NotV x.name.text
  outV : ∀ x ∈ P.outputs, NotV x.name.text ∨ valued P = true
  preOK : ∀ c ∈ P.preconditions, OvOK condG c.condition
  postOK : ∀ c ∈ P.body.postconditions, OvOK condG c.condition
  bodyOK : ∀ b, P.body.implementation = some b → OvOK (procG P) b
  nc : valued P = true → ∀ b, P.body.implementation = some b → NC b
  frames : L2 (GroupRel E) (procFrames P) (procFrames P')
  inouts : ∀ o ∈ P.outputs, P.inputs.any (·.name.text == o.name.text) = true → Reserved.inoutOK o.name.text := by
    intros; trivial
  throwsTy : ∀ t, P.throwsType = some t → Reserved.tyR t.val t.val := by intros; rfl

structure ProcRelB (P P' : Procedure) : Prop where
  ext : P.body = .External → P'.name.text = P.name.text
  inputs : L2 ParamR P.inputs P'.inputs
  outputs : L2 ParamR P.outputs P'.outputs
  pre : L2 (CondRel E) P.preconditions P'.preconditions
  coro : P.is_coroutine = false
  coro' : P'.is_coroutine = false
  body : BodyRel E P.outputs P.body P'.body
  writes : P.writesGlobals = P'.writesGlobals
  throws : P.throwsType = P'.throwsType
  outNames : ∀ x ∈ P.outputs, ¬ Reserved.res x.name.text
  inNames : ∀ x ∈ P.inputs, ¬ Reserved.res x.name.text
  inV : ∀ x ∈ P.inputs, NotV x.name.text
  outV : ∀ x ∈ P.outputs, NotV x.name.text ∨ valued P = true
  preOK : ∀ c ∈ P.preconditions, OvOK condG c.condition
  postOK : ∀ c ∈ P.body.postconditions, OvOK condG c.condition
  bodyOK : ∀ b, P.body.implementation = some b → OvOK (procG P) b
  nc : valued P = true → ∀ b, P.body.implementation = some b → NC b
  frames : L2 (GroupRel E) (procFrames P) (procFrames P')
  inouts : ∀ o ∈ P.outputs, P.inputs.any (·.name.text == o.name.text) = true → Reserved.inoutOK o.name.text := by
    intros; trivial
  throwsTy : ∀ t, P.throwsType = some t → Reserved.tyR t.val t.val := by intros; rfl

theorem ProcRel.toB {P P' : Procedure} (h : ProcRel E P P') : ProcRelB E P P' where
  ext hb := by
    rcases h.name with h' | ⟨-, -, -, hne⟩
    · rw [h']
    · exact absurd hb hne
  inputs := h.inputs
  outputs := h.outputs
  pre := h.pre
  coro := h.coro
  coro' := h.coro'
  body := h.body
  writes := h.writes
  throws := h.throws
  throwsTy := h.throwsTy
  outNames := h.outNames
  inNames := h.inNames
  inV := h.inV
  outV := h.outV
  preOK := h.preOK
  postOK := h.postOK
  bodyOK := h.bodyOK
  nc := h.nc
  frames := h.frames
  inouts := h.inouts

def FieldRel (f f' : String × HighType × Option StmtExprMd) : Prop :=
  f.1 = f'.1 ∧ Reserved.tyR f.2.1 f'.2.1 ∧ ORel E f.2.2 f'.2.2 ∧ FinOK f.2.2 ∧ OV E f.2.2 f'.2.2

def ConstRel (c c' : Constant) : Prop :=
  ORel E c.initializer c'.initializer ∧ (∀ e, c.initializer = some e → OvOK condG e) ∧
    OV E c.initializer c'.initializer

structure IxRel0 (ix ix' : ProgramIndex) : Prop where
  callee : ∀ c, ¬ Reserved.resCall c → ORel (ProcRel E) (lookupCallee ix c) (lookupCallee ix' c)
  overloaded : ∀ n, ¬ Reserved.resProc n → ix'.overloaded.contains n = ix.overloaded.contains n
  renCallee : ∀ f f', Reserved.ren f f' →
    ∃ P P', f.uniqueId.bind ix.procsById.get? = some P ∧ f'.uniqueId.bind ix'.procsById.get? = some P' ∧
      ProcRel E P P'
  methods : ¬ Reserved.resMethods → ∀ (t n : String), ¬ Reserved.resProc n →
    ORel (ProcRel E) (ix.methods[t]? >>= fun (m : Std.HashMap String Procedure) => m[n]?)
    (ix'.methods[t]? >>= fun (m : Std.HashMap String Procedure) => m[n]?)
  methodsById : ¬ Reserved.resMethods → ∀ (id : Nat),
    ORel (fun P P' => ProcRel E P P' ∧ P.name.text = P'.name.text ∧ P.inputs = P'.inputs)
      (ix.methodsById[id]?) (ix'.methodsById[id]?)
  methodOwner : ¬ Reserved.resMethods → ix'.methodOwner = ix.methodOwner
  methodLists : ¬ Reserved.resMethods → ∀ (t : String),
    L2 (fun P P' => ProcRel E P P' ∧ P.name.text = P'.name.text ∧ P.inputs = P'.inputs)
      (ix.methodLists[t]?.getD []) (ix'.methodLists[t]?.getD [])
  ancestors : ix'.ancestors = ix.ancestors
  fields : ∀ (n : String), L2 (FieldRel E) (ix.compositeFields[n]?.getD []) (ix'.compositeFields[n]?.getD [])
  procsNamed : ∀ (n : String), ¬ Reserved.resProc n →
    L2 (ProcRel E) (ix.procsNamed[n]?.getD []) (ix'.procsNamed[n]?.getD [])
  ctors : ix'.ctors = ix.ctors
  testers : ix'.testers = ix.testers
  destructors : ix'.destructors = ix.destructors
  witnesses : ix'.witnesses = ix.witnesses
  noWitness : ix'.noWitness = ix.noWitness
  exceptionBases : ix'.exceptionBases = ix.exceptionBases
  unalias : ∀ t t', Reserved.tyR t t' → ix'.unalias t' = ix.unalias t
  consts : ∀ (n : String), ¬ Reserved.resProc n → ORel (ConstRel E) (ix.constants[n]?) (ix'.constants[n]?)
  heapFields : ix'.heapFields = ix.heapFields
  heapTy : ∀ (n loc : String) (t : HighType), ix.heapFields[n]? = some (loc, t) → Reserved.tyR t t

structure IxRel (ix ix' : ProgramIndex) : Prop extends IxRel0 E ix ix' where
  extra : Reserved.ixX E ix ix'

def EvRel : Event → Event → Prop
  | .check k c _ h st, .check k' c' _ h' st' =>
    k = k' ∧ ORel E c c' ∧ h = h' ∧ ∃ G, StRel G (IxRel E) st st'
  | .assume c _ st, .assume c' _ st' => E c c' ∧ ∃ G, StRel G (IxRel E) st st'
  | _, _ => False

theorem evRel_fail : ∀ e e', EvRel E e e' → failOf e = failOf e' := by
  intro e e' h
  cases e with
  | check k c m hd st =>
    cases e' with
    | check k' c' m' hd' st' =>
      obtain ⟨-, -, he, -⟩ := h
      subst he
      cases hd <;> rfl
    | assume => exact h.elim
  | assume c s st =>
    cases e' with
    | check => exact h.elim
    | assume => rfl

def CtlOK (Gl : String → Prop) (G : StackFrame) : Control → Prop
  | .exit_ l => Gl l
  | .goto_ l => Gl l
  | .jump_ l _ => Gl l
  | .suspended => False
  | .return_ [] => Strict G ∧ ¬ NoRet G
  | .return_ [_] => ¬ NoRet G
  | .return_ _ => False
  | _ => True

def OutIs (v : Value) (σ' : EvalState) : Prop := ∀ o, Reserved.vret = some o → σ'.stack[o]? = some v

def Sm (Gl : String → Prop) (G : StackFrame) : SimRel :=
  ⟨StRel G (IxRel E), EvRel E, CtlOK Gl G, Reserved.retLabel,
    fun v σ σ' => Free G ∧ StRel G (IxRel E) σ σ' ∧ OutIs v σ'⟩

def exactG (G : StackFrame) (o : String) (v : Value) : StackFrame := (G.erase (freeKey o)).insert o v

theorem exactG_res {G : StackFrame} {o : String} (ho : Reserved.vret = some o) (v : Value) {k : String}
    (hk : Reserved.res k) : (exactG G o v)[k]? = G[k]? := by
  have ⟨h1, h2, _⟩ := Reserved.vret_ok o ho
  unfold exactG
  rw [Std.HashMap.getElem?_insert, ite_eq_right (by simp only [beq_iff_eq]; rintro rfl; exact h1 hk),
    Std.HashMap.getElem?_erase, ite_eq_right (by simp only [beq_iff_eq]; rintro rfl; exact h2 hk)]

theorem not_strict_exact {G : StackFrame} {o : String} (ho : Reserved.vret = some o) (v : Value) :
    ¬ Strict (exactG G o v) := fun h => by
  have := (h o ho).2
  simp [exactG] at this

theorem not_free_exact {G : StackFrame} {o : String} (ho : Reserved.vret = some o) (v : Value) :
    ¬ Free (exactG G o v) := fun ⟨o', ho', hc⟩ => by
  rw [ho] at ho'
  cases ho'
  have hne : (o == freeKey o) = false := by
    simp only [beq_eq_false_iff_ne, freeKey]
    intro h
    have := congrArg String.length h
    simp at this
  simp [exactG, Std.HashMap.contains_insert, hne] at hc

theorem SR.toExact {G s s' : StackFrame} {o : String} (ho : Reserved.vret = some o) (h : SR G gs s s') {v : Value}
    (hv : s'[o]? = some v) : SR (exactG G o v) gs s s' := by
  refine ⟨fun k hk hkv => ?_, fun k hk _ hkl => ?_, fun o' w ho' _ hw => ?_,
    fun k ha => absurd ha (Reserved.alias_vret o ho _ k),
    fun k w hw => (by rw [Reserved.frozen_vret o ho] at hw; cases hw), h.clean,
    fun k w δ x hp => (by rw [Reserved.pin_vret o ho] at hp; cases hp)⟩
  · rcases hkv with hkv | hkv
    · exact h.src k hk (.inl hkv)
    · exact absurd hkv (not_strict_exact ho v)
  · rw [exactG_res ho v hk]
    exact h.ghost k hk (Reserved.alias_vret o ho G k) (fun hl => hkl ((Reserved.loose_vret o ho _ _ k).mp hl))
  · rw [ho] at ho'
    cases ho'
    simp only [exactG, Std.HashMap.getElem?_insert_self, Option.some.injEq] at hw
    rw [← hw]; exact hv

theorem SR.ofExact {G s s' : StackFrame} {o : String} (ho : Reserved.vret = some o) (hf : Free G) {v : Value}
    (h : SR (exactG G o v) gs s s') : SR G gs s s' ∧ s'[o]? = some v := by
  refine ⟨⟨fun k hk hkv => ?_, fun k hk _ hkl => ?_, fun o' w ho' hc _ => ?_,
    fun k ha => absurd ha (Reserved.alias_vret o ho _ k),
    fun k w hw => (by rw [Reserved.frozen_vret o ho] at hw; cases hw), h.clean,
    fun k w δ x hp => (by rw [Reserved.pin_vret o ho] at hp; cases hp)⟩, ?_⟩
  · rcases hkv with hkv | hkv
    · exact h.src k hk (.inl hkv)
    · obtain ⟨o', ho', hc⟩ := hf
      exact absurd hc (hkv o' ho').1
  · exact (h.ghost k hk (Reserved.alias_vret o ho _ k) (fun hl => hkl ((Reserved.loose_vret o ho _ _ k).mp hl))).trans
      (exactG_res ho v hk)
  · obtain ⟨o'', ho'', hc'⟩ := hf
    rw [ho] at ho' ho''
    cases ho'; cases ho''
    exact absurd hc' hc
  · refine h.out o v ho ?_ (by simp [exactG])
    have hne : (o == freeKey o) = false := by
      simp only [beq_eq_false_iff_ne, freeKey]
      intro h
      have := congrArg String.length h
      simp at this
    simp [exactG, Std.HashMap.contains_insert, hne]

theorem WFG.exact {G : StackFrame} {o : String} (ho : Reserved.vret = some o) (h : WFG G) (v : Value) :
    WFG (exactG G o v) := by
  intro k hk
  rw [exactG_res ho v hk, exactG_res ho v (Reserved.shadow_res k hk)]
  exact h k hk

theorem not_noRet_none (h : Reserved.vret = none) (G : StackFrame) : ¬ NoRet G := fun ⟨o, ho, _⟩ => by
  rw [h] at ho; cases ho

theorem ovOK_none (h : Reserved.vret = none) (G : StackFrame) (e : StmtExprMd)
    (hk : ∀ G e, Reserved.nodeOK G e := by intros; trivial) : OvOK G e :=
  hered_all (fun e => by
    refine ⟨?_, hk G e⟩
    split
    · exact .inl (notV_none h _)
    · exact ⟨strict_none h G, not_noRet_none h G⟩
    · exact ⟨.inl h, not_noRet_none h G⟩
    · exact strict_none h G
    · exact fun _ _ => hk _ _
    · exact fun _ _ => hk _ _
    · exact fun _ _ => hk _ _
    · trivial) e

theorem finP_none (h : Reserved.vret = none) (e : StmtExprMd)
    (hk : ∀ G e, Reserved.nodeOK G e := by intros; trivial) : Hered FinP e :=
  hered_all (fun e => by
    refine ⟨?_, fun G => hk G e⟩
    split
    · exact notV_none h _
    · exact h
    · exact h
    · exact fun _ _ _ => hk _ _
    · exact fun _ _ _ => hk _ _
    · exact fun _ _ _ => hk _ _
    · trivial) e

theorem OvOK.resrc {G : StackFrame} {v : StmtExpr} {src : FileRange} (h : OvOK G ⟨v, src⟩) (src' : FileRange) :
    OvOK G ⟨v, src'⟩ := by
  cases h with
  | node _ hp hk => exact .node _ ⟨hp.1, Reserved.nodeOK_src _ _ _ _ hp.2⟩ hk

theorem finP_nodeOK {G : StackFrame} {e : StmtExprMd} (h : FinP e) : NodeOK G e := by
  obtain ⟨h, hk⟩ := h
  refine ⟨?_, hk G⟩
  split
  · rename_i n hn; rw [hn] at h; exact .inl h
  · rename_i hn; rw [hn] at h; exact ⟨strict_none h G, not_noRet_none h G⟩
  · rename_i v hn; rw [hn] at h; exact ⟨.inl h, not_noRet_none h G⟩
  · rename_i v l hn; rw [hn] at h; exact strict_none h G
  · rename_i hn; rw [hn] at h; exact h G
  · rename_i hn; rw [hn] at h; exact h G
  · rename_i hn; rw [hn] at h; exact h G
  · trivial

theorem FinOK.ov {G : StackFrame} {f : Option StmtExprMd} (h : FinOK f) : ∀ x, f = some x → OvOK G x :=
  fun x hx => (h x hx).mono (fun _ => finP_nodeOK)

theorem EntR.vret {G G' : StackFrame} {o : String} (ho : Reserved.vret = some o) {e e'} (h : EntR G e e') :
    EntR G' e e' :=
  h.congr (fun k => iff_of_false (Reserved.alias_vret o ho _ k) (Reserved.alias_vret o ho _ k))
    (fun k => by rw [Reserved.frozen_vret o ho, Reserved.frozen_vret o ho]) (Reserved.entOK_vret o ho G G')

theorem StRel.toExact {IR : ProgramIndex → ProgramIndex → Prop} {G : StackFrame} {σ σ' : EvalState} {o : String}
    (ho : Reserved.vret = some o) (h : StRel G IR σ σ') {v : Value} (hv : σ'.stack[o]? = some v) :
    StRel (exactG G o v) IR σ σ' :=
  { h with stack := h.stack.toExact ho hv, wf := h.wf.exact ho v, entR := h.entR.vret ho }

theorem StRel.ofExact {IR : ProgramIndex → ProgramIndex → Prop} {G : StackFrame} {σ σ' : EvalState} {o : String}
    (ho : Reserved.vret = some o) (hf : Free G) {v : Value} (h : StRel (exactG G o v) IR σ σ') :
    StRel G IR σ σ' ∧ σ'.stack[o]? = some v := by
  obtain ⟨hs, hv⟩ := h.stack.ofExact ho hf
  refine ⟨{ h with stack := hs, entR := h.entR.vret ho, wf := fun k hk => ?_ }, hv⟩
  have := h.wf k hk
  rwa [exactG_res ho v hk, exactG_res ho v (Reserved.shadow_res k hk)] at this

theorem noRet_exact {G : StackFrame} {o : String} (ho : Reserved.vret = some o) (v : Value) :
    NoRet (exactG G o v) ↔ NoRet G := by
  have h1 : (o == noRetKey o) = false := by
    simp only [beq_eq_false_iff_ne, noRetKey]
    intro h
    have := congrArg String.length h
    simp at this
  have h2 : (freeKey o == noRetKey o) = false := by
    simp only [beq_eq_false_iff_ne, noRetKey, freeKey]
    intro h
    have := (String.append_right_inj o).mp h
    simp at this
  unfold NoRet
  constructor
  · rintro ⟨o', ho', hc⟩
    rw [ho] at ho'; cases ho'
    simp only [exactG, Std.HashMap.contains_insert, h1, Std.HashMap.contains_erase, h2, Bool.false_or,
      Bool.not_false, Bool.true_and] at hc
    exact ⟨o, ho, hc⟩
  · rintro ⟨o', ho', hc⟩
    rw [ho] at ho'; cases ho'
    refine ⟨o, ho, ?_⟩
    simp only [exactG, Std.HashMap.contains_insert, h1, Std.HashMap.contains_erase, h2, Bool.false_or,
      Bool.not_false, Bool.true_and]
    exact hc

theorem CtlOK.ofExact {Gl : String → Prop} {G : StackFrame} {o : String} (ho : Reserved.vret = some o) {v : Value}
    {c : Control} (h : CtlOK Gl (exactG G o v) c) : CtlOK Gl G c := by
  cases c with
  | return_ w =>
    rcases w with _ | ⟨_, _ | ⟨_, _⟩⟩
    · exact absurd h.1 (not_strict_exact ho v)
    · exact fun hn => h ((noRet_exact ho v).mpr hn)
    · first | exact (h : False).elim | exact (hc : False).elim
  | _ => exact h

theorem CtlOK.none {Gl : String → Prop} {G G' : StackFrame} (h : Reserved.vret = none) {c : Control}
    (hc : CtlOK Gl G c) : CtlOK Gl G' c := by
  cases c with
  | return_ w =>
    rcases w with _ | ⟨_, _ | ⟨_, _⟩⟩
    · exact ⟨strict_none h G', fun ⟨o, ho, _⟩ => by rw [h] at ho; cases ho⟩
    · exact fun ⟨o, ho, _⟩ => by rw [h] at ho; cases ho
    · first | exact (h : False).elim | exact (hc : False).elim
  | _ => exact hc

theorem not_free_none (h : Reserved.vret = none) (G : StackFrame) : ¬ Free G := fun ⟨o, ho, _⟩ => by
  rw [h] at ho; cases ho

theorem Sm.noWin {Gl : String → Prop} {G : StackFrame} (hf : ¬ Free G) (v : Value) {σ σ' : EvalState} :
    ¬ (Sm E Gl G).win v σ σ' := fun h => hf h.1

omit [Reserved] in
theorem LX.ofL2 {X : StmtExprMd → List StmtExprMd → Prop} {l l' : List StmtExprMd} (h : L2 E l l') :
    LX E X l l' := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons hab ih

omit [Reserved] in
theorem LX.toL2 {X : StmtExprMd → List StmtExprMd → Prop} {l l' : List StmtExprMd} (h : LX E X l l')
    (hx : ∀ a ts, X a ts → False) : L2 E l l' := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons hab ih
  | expand hab _ _ => exact (hx _ _ hab).elim

omit [Reserved] in
theorem LX.mono {E' : StmtExprMd → StmtExprMd → Prop} {X X' : StmtExprMd → List StmtExprMd → Prop}
    {l l' : List StmtExprMd} (h : LX E X l l') (hE : ∀ a b, E a b → E' a b) (hX : ∀ a ts, X a ts → X' a ts) :
    LX E' X' l l' := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hE _ _ hab) ih
  | expand hab _ ih => exact .expand (hX _ _ hab) ih

theorem not_free_empty : ¬ Free ({} : StackFrame) := fun ⟨_, _, h⟩ => by simp at h

omit [Reserved] in
theorem noRetKey_ne (o : String) : noRetKey o ≠ o := by
  intro h
  have := congrArg String.length h
  simp [noRetKey] at this

omit [Reserved] in
theorem noRetKey_ne_free (o : String) : noRetKey o ≠ freeKey o := by
  intro h
  have := (String.append_right_inj o).mp h
  simp at this

theorem condG_strict : Strict condG := by
  intro o ho
  simp only [condG, ho]
  refine ⟨?_, ?_⟩
  · simp only [Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false, beq_iff_eq]
    exact noRetKey_ne_free o
  · rw [Std.HashMap.getElem?_insert, ite_eq_right (by simpa using noRetKey_ne o)]
    simp

theorem not_free_condG : ¬ Free condG := by
  rintro ⟨o, ho, hc⟩
  simp only [condG, ho, Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false, beq_iff_eq] at hc
  exact noRetKey_ne_free o hc

theorem CtlOK.ofCond {Gl : String → Prop} {G : StackFrame} {c : Control} (h : CtlOK Gl condG c) : CtlOK Gl G c := by
  cases hv : Reserved.vret with
  | none =>
    cases c with
    | return_ w =>
      rcases w with _ | ⟨_, _ | ⟨_, _⟩⟩
      · exact ⟨strict_none hv G, not_noRet_none hv G⟩
      · exact not_noRet_none hv G
      · first | exact (h : False).elim | exact (hc : False).elim
    | _ => exact h
  | some o =>
    have hnr : NoRet condG := ⟨o, hv, by simp [condG, hv]⟩
    cases c with
    | return_ w =>
      rcases w with _ | ⟨_, _ | ⟨_, _⟩⟩
      · exact absurd hnr h.2
      · exact absurd hnr h
      · first | exact (h : False).elim | exact (hc : False).elim
    | _ => exact h

theorem condG_res {k : String} (hk : Reserved.res k) : condG[k]? = none := by
  cases hv : Reserved.vret with
  | none => simp [condG, hv]
  | some o =>
    simp only [condG, hv]
    rw [Std.HashMap.getElem?_insert, ite_eq_right (by
      simp only [beq_iff_eq]; rintro rfl; exact Reserved.vret_noret o hv hk)]
    simp

theorem alias_condG (k : String) : ¬ Reserved.aliasOf condG k := by
  cases hv : Reserved.vret with
  | none => have : condG = {} := by simp [condG, hv]
            rw [this]; exact Reserved.alias_empty k
  | some o => exact Reserved.alias_vret o hv _ k

theorem frozen_condG (k : String) : Reserved.frozenOf condG k = none := by
  cases hv : Reserved.vret with
  | none => have : condG = {} := by simp [condG, hv]
            rw [this]; exact Reserved.frozen_empty k
  | some o => exact Reserved.frozen_vret o hv _ k

theorem pin_condG (k : String) : Reserved.pinOf condG k = none := by
  cases hv : Reserved.vret with
  | none => have : condG = {} := by simp [condG, hv]
            rw [this]; exact Reserved.pin_empty k
  | some o => exact Reserved.pin_vret o hv _ k

theorem pin_freeG (k : String) : Reserved.pinOf freeG k = none := by
  cases hv : Reserved.vret with
  | none => have : freeG = {} := by simp [freeG, hv]
            rw [this]; exact Reserved.pin_empty k
  | some o => exact Reserved.pin_vret o hv _ k

theorem SR.freshC {s : StackFrame} (hs : ∀ k, Reserved.res k → s[k]? = none) : SR condG gs s s :=
  ⟨fun _ _ _ => rfl, fun k hk _ _ => (by rw [hs k hk, condG_res hk]),
    fun o w ho _ hw => (by rw [(condG_strict o ho).2] at hw; cases hw),
    fun k h => absurd h (alias_condG k), fun k v h => (by rw [frozen_condG] at h; cases h), hs,
    fun k v δ x h => (by rw [pin_condG] at h; cases h)⟩

theorem WFG.condG : WFG condG := fun k hk => by
  rw [condG_res hk, condG_res (Reserved.shadow_res k hk)]
  exact ⟨.inl rfl, fun _ h => by cases h⟩

theorem fs_noWin {Gl : String → Prop} {G : StackFrame} {T U : SimRel} {A : α → β → Prop} {x : EvalM PM α}
    {y : EvalM PM β} (hf : ¬ Free G) (v : Value) : FSH ((Sm E Gl G).atWin v) T U A x y :=
  fs_noPre (fun _ _ h => hf h.1)

theorem valued_outputs {P : Procedure} (hv : valued P = true) :
    ∃ o x, Reserved.vret = some o ∧ P.outputs = [x] ∧ x.name.text = o := by
  unfold valued at hv
  split at hv
  · rename_i o ho
    simp only [beq_iff_eq] at hv
    match h : P.outputs, hv with
    | [x], hv => exact ⟨o, x, ho, rfl, by simpa using hv⟩
  · cases hv

theorem valued_none (h : Reserved.vret = none) (P : Procedure) : valued P = false := by
  simp [valued, h]

theorem procG_valued {P : Procedure} (hv : valued P = true) : procG P = freeG := by simp [procG, hv]

theorem freeG_free {o : String} (ho : Reserved.vret = some o) : Free freeG :=
  ⟨o, ho, by simp [freeG, ho]⟩

theorem freeG_res {k : String} (hk : Reserved.res k) : freeG[k]? = none := by
  cases hv : Reserved.vret with
  | none => simp [freeG, hv]
  | some o =>
    simp only [freeG, hv]
    rw [Std.HashMap.getElem?_insert, ite_eq_right (by
      simp only [beq_iff_eq]; rintro rfl; exact (Reserved.vret_ok o hv).2.1 hk)]
    simp

theorem freeG_out {o : String} (ho : Reserved.vret = some o) : freeG[o]? = none := by
  simp only [freeG, ho]
  rw [Std.HashMap.getElem?_insert, ite_eq_right (by
    simp only [beq_iff_eq, freeKey]
    intro h
    have := congrArg String.length h
    simp at this)]
  simp

theorem not_noRet_freeG : ¬ NoRet freeG := by
  rintro ⟨o, ho, hc⟩
  simp only [freeG, ho, Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false, beq_iff_eq] at hc
  exact noRetKey_ne_free o hc.symm

theorem alias_freeG (k : String) : ¬ Reserved.aliasOf freeG k := by
  cases hv : Reserved.vret with
  | none => have : freeG = {} := by simp [freeG, hv]
            rw [this]; exact Reserved.alias_empty k
  | some o => exact Reserved.alias_vret o hv _ k

theorem frozen_freeG (k : String) : Reserved.frozenOf freeG k = none := by
  cases hv : Reserved.vret with
  | none => have : freeG = {} := by simp [freeG, hv]
            rw [this]; exact Reserved.frozen_empty k
  | some o => exact Reserved.frozen_vret o hv _ k

theorem SR.freshF {s : StackFrame} (hs : ∀ k, Reserved.res k → s[k]? = none) : SR freeG gs s s :=
  ⟨fun _ _ _ => rfl, fun k hk _ _ => (by rw [hs k hk, freeG_res hk]),
    fun o w ho _ hw => (by rw [freeG_out ho] at hw; cases hw),
    fun k h => absurd h (alias_freeG k), fun k v h => (by rw [frozen_freeG] at h; cases h), hs,
    fun k v δ x h => (by rw [pin_freeG] at h; cases h)⟩

theorem loose_condG (k : String) : Reserved.loose condG k ↔ Reserved.loose ({} : StackFrame) k := by
  cases hv : Reserved.vret with
  | none => have : condG = {} := by simp [condG, hv]
            rw [this]
  | some o => exact Reserved.loose_vret o hv _ _ k

theorem loose_freeG (k : String) : Reserved.loose freeG k ↔ Reserved.loose ({} : StackFrame) k := by
  cases hv : Reserved.vret with
  | none => have : freeG = {} := by simp [freeG, hv]
            rw [this]
  | some o => exact Reserved.loose_vret o hv _ _ k

theorem plain_condG : Plain condG := ⟨alias_condG, frozen_condG⟩
theorem plain_freeG : Plain freeG := ⟨alias_freeG, frozen_freeG⟩
theorem plain_empty : Plain ({} : StackFrame) := ⟨Reserved.alias_empty, Reserved.frozen_empty⟩

theorem EntR.plain {G G' : StackFrame} {e e'} (h : EntR G e e') (hG : Plain G) (hG' : Plain G')
    (hh : Reserved.entOK G → Reserved.entOK G') : EntR G' e e' :=
  h.congr (fun k => iff_of_false (hG'.1 k) (hG.1 k)) (fun k => by rw [hG.2 k, hG'.2 k]) hh

theorem WFG.freeG : WFG freeG := fun k hk => by
  rw [freeG_res hk, freeG_res (Reserved.shadow_res k hk)]
  exact ⟨.inl rfl, fun _ h => by cases h⟩

def SameRegime (G G' : StackFrame) : Prop :=
  ∀ k, (Reserved.res k ∨ ∃ o, Reserved.vret = some o ∧ (k = o ∨ k = freeKey o ∨ k = noRetKey o)) → G'[k]? = G[k]?

theorem SameRegime.contains {G G' : StackFrame} (h : SameRegime G G') {k : String}
    (hk : Reserved.res k ∨ ∃ o, Reserved.vret = some o ∧ (k = o ∨ k = freeKey o ∨ k = noRetKey o)) :
    G'.contains k = G.contains k := by
  rw [Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.contains_eq_isSome_getElem?, h k hk]

theorem SameRegime.strict {G G' : StackFrame} (h : SameRegime G G') : Strict G' ↔ Strict G := by
  unfold Strict
  refine forall_congr' (fun o => imp_congr_right (fun ho => ?_))
  rw [h.contains (.inr ⟨o, ho, .inr (.inl rfl)⟩), h o (.inr ⟨o, ho, .inl rfl⟩)]

theorem SameRegime.free {G G' : StackFrame} (h : SameRegime G G') : Free G' ↔ Free G := by
  unfold Free
  refine exists_congr (fun o => ⟨fun ⟨ho, hc⟩ => ⟨ho, ?_⟩, fun ⟨ho, hc⟩ => ⟨ho, ?_⟩⟩)
  · rwa [h.contains (.inr ⟨o, ho, .inr (.inl rfl)⟩)] at hc
  · rwa [h.contains (.inr ⟨o, ho, .inr (.inl rfl)⟩)]

theorem SameRegime.noRet {G G' : StackFrame} (h : SameRegime G G') : NoRet G' ↔ NoRet G := by
  unfold NoRet
  refine exists_congr (fun o => ⟨fun ⟨ho, hc⟩ => ⟨ho, ?_⟩, fun ⟨ho, hc⟩ => ⟨ho, ?_⟩⟩)
  · rwa [h.contains (.inr ⟨o, ho, .inr (.inr rfl)⟩)] at hc
  · rwa [h.contains (.inr ⟨o, ho, .inr (.inr rfl)⟩)]

theorem SameRegime.wfg {G G' : StackFrame} (h : SameRegime G G') (hw : WFG G) : WFG G' := by
  intro k hk
  rw [h k (.inl hk), h _ (.inl (Reserved.shadow_res k hk))]
  exact hw k hk

theorem SameRegime.nodeOK {G G' : StackFrame} (h : SameRegime G G') (hn : ∀ e, Reserved.nodeOK G e → Reserved.nodeOK G' e)
    {e : StmtExprMd} (he : NodeOK G e) : NodeOK G' e := by
  obtain ⟨h1, h2⟩ := he
  refine ⟨?_, hn e h2⟩
  revert h1
  split <;> intro h1
  · exact h1.imp id h.strict.mpr
  · exact ⟨h.strict.mpr h1.1, fun hn' => h1.2 (h.noRet.mp hn')⟩
  · exact ⟨h1.1.imp id h.free.mpr, fun hn' => h1.2 (h.noRet.mp hn')⟩
  · exact h.strict.mpr h1
  · exact fun a ha => hn _ (h1 a ha)
  · exact fun a ha => hn _ (h1 a ha)
  · exact fun i hi => hn _ (h1 i hi)
  · trivial

theorem OvOK.regime {G G' : StackFrame} {e : StmtExprMd} (h : OvOK G e) (hs : SameRegime G G')
    (hn : ∀ e, Reserved.nodeOK G e → Reserved.nodeOK G' e) : OvOK G' e :=
  h.mono (fun _ hx => hs.nodeOK hn hx)

theorem sameRegime_freeze (G : StackFrame) (gs : Std.HashMap String Value) (b : StackFrame) :
    SameRegime b (Reserved.freeze G gs b) := fun k hk => Reserved.freeze_get G gs b k hk

theorem sameRegime_postOf (G b : StackFrame) : SameRegime b (Reserved.postOf G b) :=
  fun k hk => Reserved.postOf_get G b k hk

theorem SR.ofRegime {b G' s : StackFrame} (h : SR b gs s s) (hsr : SameRegime b G')
    (ha : ∀ k, Reserved.aliasOf G' k ↔ Reserved.aliasOf b k)
    (hf : ∀ k v, Reserved.frozenOf G' k = some v → gs[k]? = some v)
    (hl : ∀ k, Reserved.loose G' k ↔ Reserved.loose b k) (hp : ∀ k, Reserved.pinOf G' k = Reserved.pinOf b k) :
    SR G' gs s s := by
  refine ⟨fun k hk hkv => h.src k hk (hkv.imp id hsr.strict.mp), fun k hk hka hkl => ?_,
    fun o w ho hc hw => ?_, fun k hk => h.alias k ((ha k).mp hk), hf, h.clean,
    fun k v δ x h' => h.pin k v δ x (by rw [← hp k]; exact h')⟩
  · rw [hsr k (.inl hk)]; exact h.ghost k hk (fun x => hka ((ha k).mpr x)) (fun x => hkl ((hl k).mpr x))
  · rw [hsr.contains (.inr ⟨o, ho, .inr (.inl rfl)⟩)] at hc
    rw [hsr o (.inr ⟨o, ho, .inl rfl⟩)] at hw
    exact h.out o w ho hc hw

theorem SR.restoreF {G f f' : StackFrame} {gs0 gs1 : Std.HashMap String Value} (h : SR G gs0 f f')
    (hk : ∀ k v, Reserved.aliasOf G k → gs0[k]? = some v → gs1[k]? = some v)
    (hkf : ∀ k v, Reserved.frozenOf G k = some v → gs1[k]? = some v) : SR G gs1 f f' := by
  refine ⟨h.src, h.ghost, h.out, fun k ha => ?_, hkf, h.clean, h.pin⟩
  obtain ⟨v, hg, hs⟩ := h.alias k ha
  exact ⟨v, hk k v ha hg, hs⟩

theorem EntR.noAlias {G G' : StackFrame} {e e'} (h : EntR G e e') (hG : ∀ k, ¬ Reserved.aliasOf G k)
    (hG' : ∀ k, ¬ Reserved.aliasOf G' k) (hf : ∀ k v, Reserved.frozenOf G' k = some v → Reserved.frozenOf G k = some v)
    (hh : Reserved.entOK G') : EntR G' e e' := by
  match e, e', h with
  | none, none, _ => trivial
  | some (_, _, _), some (_, _, _), ⟨h1, h2, h4, h3⟩ =>
    exact ⟨h1, h2, h4, ⟨h3.src, fun k hk _ => h3.ghost k hk (hG k),
      fun k h => absurd h (hG' k), fun k v h => h3.frozen k v (hf k v h), hh, h3.keys⟩⟩

theorem SameRegime.symm {G G' : StackFrame} (h : SameRegime G G') : SameRegime G' G := fun k hk => (h k hk).symm

theorem CtlOK.regime {Gl : String → Prop} {G G' : StackFrame} {c : Control} (h : CtlOK Gl G c)
    (hs : SameRegime G G') : CtlOK Gl G' c := by
  cases c with
  | return_ w =>
    rcases w with _ | ⟨_, _ | ⟨_, _⟩⟩
    · exact ⟨hs.strict.mpr h.1, fun hn => h.2 (hs.noRet.mp hn)⟩
    · exact fun hn => h (hs.noRet.mp hn)
    · first | exact (h : False).elim | exact (hc : False).elim
  | _ => exact h

theorem SR.restoreFz {G b f f' x x' : StackFrame} {gs0 gs1 : Std.HashMap String Value} (h : SR G gs0 f f')
    (ha : SR (Reserved.freeze G gs0 b) gs1 x x') : SR G gs1 f f' :=
  h.restoreF (fun k v hk hv => ha.frozen k v (Reserved.freeze_keep G gs0 b k v hk hv))
    (fun k v hk => ha.frozen k v (Reserved.freeze_keepF G gs0 b k v hk (h.frozen k v hk)))

theorem SR.restorePost {G b b' f f' x x' : StackFrame} {gs0 gs1 : Std.HashMap String Value} (h : SR G gs0 f f')
    (ha : SR (Reserved.postOf (Reserved.freeze G gs0 b) b') gs1 x x') : SR G gs1 f f' :=
  h.restoreF (fun k v hk hv => ha.frozen k v (Reserved.postOf_keepF _ b' k v (Reserved.freeze_keep G gs0 b k v hk hv)))
    (fun k v hk => ha.frozen k v (Reserved.postOf_keepF _ b' k v (Reserved.freeze_keepF G gs0 b k v hk (h.frozen k v hk))))

theorem noAlias_freeze (G : StackFrame) (gs : Std.HashMap String Value) {b : StackFrame}
    (hb : ∀ k, ¬ Reserved.aliasOf b k) : ∀ k, ¬ Reserved.aliasOf (Reserved.freeze G gs b) k :=
  fun k h => hb k ((Reserved.freeze_alias G gs b k).mp h)

theorem noAlias_postOf (G : StackFrame) {b : StackFrame} (hb : ∀ k, ¬ Reserved.aliasOf b k) :
    ∀ k, ¬ Reserved.aliasOf (Reserved.postOf G b) k :=
  fun k h => hb k ((Reserved.postOf_alias G b k).mp h)

theorem SigR.ofExact {Gl : String → Prop} {G : StackFrame} {o : String} (ho : Reserved.vret = some o) (hf : Free G)
    {v : Value} {c c' : Control} {σ σ' : EvalState} (h : SigR (Sm E Gl (exactG G o v)) c c' σ σ') :
    SigR (Sm E Gl G) c c' σ σ' := by
  rcases h with ⟨hcr, hok, hst⟩ | ⟨w, _, _, hw⟩
  · exact .inl ⟨hcr, CtlOK.ofExact ho hok, (StRel.ofExact ho hf hst).1⟩
  · exact absurd hw.1 (not_free_exact ho v)

end

end Strata.Laurel.PassSemantics

namespace Strata.Laurel.PassSemantics

open Strata.Laurel
open Strata.Laurel.Interpreter

section Helpers

macro "strel" h:term : tactic => `(tactic|
  (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try dsimp only) <;>
    first
    | exact StRel.openLabels $h
    | exact fun _ _ => Iff.rfl
    | exact StRel.gk $h
    | exact StRel.gk' $h
    | exact StRel.egk $h
    | exact StRel.ops $h
    | exact StRel.ops' $h
    | (intro hg; exact absurd hg (by assumption))
    | (intro _ _ _ _ he; cases he; done)
    | (intro _ _ _ he; cases he; done)
    | (intro _ _ _ he; cases he; solve_by_elim)
    | exact StRel.index $h
    | exact StRel.stack $h
    | exact (StRel.stack $h).gs_insert (by assumption) _
    | exact (StRel.stack $h).regs (by assumption) _
    | exact StRel.globals $h
    | exact (StRel.globals $h).insert _ _
    | exact StRel.entR $h
    | exact True.intro
    | exact StRel.entryClean $h
    | exact StRel.wf $h
    | exact WFG.empty
    | exact WFG.condG
    | exact (StRel.stack $h).insert (by assumption) (by assumption) _
    | exact (StRel.stack $h).insertS (by assumption) (by assumption) _
    | assumption
    | (intro _ _ _ he; cases he; assumption)
    | (simp only [StRel.heap $h, StRel.coros $h,
        StRel.inOld $h, StRel.quiet $h, StRel.muted $h, StRel.steps $h, StRel.steps' $h,
        StRel.coroSelf $h, StRel.coroSelf' $h, StRel.seek $h, StRel.seek' $h, StRel.ops $h, StRel.ops' $h]; done)
    | rfl
    | exact gk_ins (StRel.gk $h) (by assumption) (by assumption) _
    | exact gk_ins (StRel.gk' $h) (by assumption) (by assumption) _))

macro "strelw" h:ident " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try dsimp only) <;>
    first
    | exact StRel.openLabels $h
    | exact fun _ _ => Iff.rfl
    | exact StRel.gk $h
    | exact StRel.gk' $h
    | exact StRel.egk $h
    | exact StRel.ops $h
    | exact StRel.ops' $h
    | (intro hg; exact absurd hg (by assumption))
    | (intro _ _ _ _ he; cases he; done)
    | (intro _ _ _ he; cases he; done)
    | (intro _ _ _ he; cases he; solve_by_elim)
    | exact StRel.index $h
    | exact StRel.stack $h
    | exact (StRel.stack $h).gs_insert (by assumption) _
    | exact (StRel.stack $h).regs (by assumption) _
    | exact StRel.globals $h
    | exact (StRel.globals $h).insert _ _
    | exact StRel.entR $h
    | exact True.intro
    | exact StRel.entryClean $h
    | exact StRel.wf $h
    | exact WFG.empty
    | exact WFG.condG
    | exact (StRel.stack $h).insert (by assumption) (by assumption) _
    | exact (StRel.stack $h).insertS (by assumption) (by assumption) _
    | assumption
    | (intro _ _ _ he; cases he; assumption)
    | ((try simp only [$ls,*]) <;> first
        | exact StRel.stack $h
        | exact (StRel.stack $h).gs_insert (by assumption) _
        | exact StRel.globals $h
        | exact (StRel.globals $h).insert _ _
        | exact StRel.entR $h
        | exact StRel.entryClean $h
        | exact StRel.wf $h
        | exact WFG.empty
        | exact WFG.condG
        | exact (StRel.stack $h).insert (by assumption) (by assumption) _
        | exact (StRel.stack $h).insertS (by assumption) (by assumption) _
        | assumption)
    | (simp only [StRel.heap $h, StRel.coros $h,
        StRel.inOld $h, StRel.quiet $h, StRel.muted $h, StRel.steps $h, StRel.steps' $h,
        StRel.coroSelf $h, StRel.coroSelf' $h, StRel.seek $h, StRel.seek' $h, StRel.ops $h, StRel.ops' $h, $ls,*]; done)
    | rfl
    | exact gk_ins (StRel.gk $h) (by assumption) (by assumption) _
    | exact gk_ins (StRel.gk' $h) (by assumption) (by assumption) _))

variable {E : StmtExprMd → StmtExprMd → Prop} {Gl : String → Prop} {G : StackFrame} {U : SimRel}

theorem StRel.site [Reserved] {G : StackFrame} {IR : ProgramIndex → ProgramIndex → Prop} {σ σ' : EvalState}
    (h : StRel G IR σ σ') (s : FileRange) : StRel G IR σ { σ' with stmtSite := s } := by
  strel h

theorem fuel_split {K n M' : Nat} (hK : 1 ≤ K) (h : K * (n + 1) ≤ M') :
    ∃ M, M' = M + 1 ∧ K * n ≤ M := by
  refine ⟨M' - 1, by rw [Nat.mul_succ] at h; omega, ?_⟩
  rw [Nat.mul_succ] at h
  omega

theorem L2.length_eq {R : α → β → Prop} {l : List α} {l' : List β} (h : L2 R l l') :
    l.length = l'.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem L2.append {R : α → β → Prop} {l₁ l₂ : List α} {l₁' l₂' : List β} (h₁ : L2 R l₁ l₁')
    (h₂ : L2 R l₂ l₂') : L2 R (l₁ ++ l₂) (l₁' ++ l₂') := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h ih

theorem L2.reverse {R : α → β → Prop} {l : List α} {l' : List β} (h : L2 R l l') :
    L2 R l.reverse l'.reverse := by
  induction h with
  | nil => exact .nil
  | cons h _ ih =>
    simp only [List.reverse_cons]
    exact ih.append (.cons h .nil)

theorem L2.filter {R : α → β → Prop} {l : List α} {l' : List β} (h : L2 R l l') {p : α → Bool}
    {p' : β → Bool} (hp : ∀ a b, R a b → p a = p' b) : L2 R (l.filter p) (l'.filter p') := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih =>
    simp only [List.filter_cons, hp _ _ hab]
    split
    · exact .cons hab ih
    · exact ih

theorem L2.zip {R : α → β → Prop} {l : List α} {l' : List β} (h : L2 R l l') (xs : List γ) :
    L2 (fun a b => R a.1 b.1 ∧ a.2 = b.2) (l.zip xs) (l'.zip xs) := by
  induction h generalizing xs with
  | nil => exact .nil
  | cons hab _ ih =>
    cases xs with
    | nil => exact .nil
    | cons x xs => exact .cons ⟨hab, rfl⟩ (ih xs)

theorem L2.find? {R : α → β → Prop} {l : List α} {l' : List β} (h : L2 R l l') {p : α → Bool}
    {p' : β → Bool} (hp : ∀ a b, R a b → p a = p' b) : ORel R (l.find? p) (l'.find? p') := by
  induction h with
  | nil => trivial
  | cons hab _ ih =>
    simp only [List.find?_cons, hp _ _ hab]
    split
    · exact hab
    · exact ih

theorem L2.map_eq {R : α → β → Prop} {l : List α} {l' : List β} (h : L2 R l l') {f : α → γ}
    {g : β → γ} (hf : ∀ a b, R a b → f a = g b) : l.map f = l'.map g := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp [hf _ _ hab, ih]

theorem defaultValueU_congr {ix ix' : ProgramIndex} (hw : ix'.witnesses = ix.witnesses) (t : HighType) (d : Nat) :
    defaultValueU ix' t d = defaultValueU ix t d := by
  induction d generalizing t with
  | zero => cases t <;> simp [defaultValueU]
  | succ d ih =>
    cases t <;> simp only [defaultValueU, hw, ih]

variable [Reserved]

theorem IxRel.defaultR {ix ix' : ProgramIndex} (h : IxRel E ix ix') {t t' : HighType} (ht : Reserved.tyR t t')
    (d : Nat := 16) : defaultValue ix' t' d = defaultValue ix t d := by
  unfold defaultValue
  rw [h.unalias t t' ht]
  exact defaultValueU_congr h.witnesses _ d

theorem IxRel.default {ix ix' : ProgramIndex} (h : IxRel E ix ix') (hte : TyEq) (t : HighType) (d : Nat := 16) :
    defaultValue ix' t d = defaultValue ix t d :=
  h.defaultR (hte.refl t) d

omit [Reserved] in
theorem run_chargeStep {σ : EvalState} (h : σ.steps = none) (τ : Trace) :
    run (chargeStep : EvalM PM Unit) σ τ = .ok ((.ok (), σ), τ) := by
  unfold chargeStep
  rw [run_bind]
  simp only [run_get, h]
  rfl

theorem fs_unit {x : EvalM PM Unit} {y : EvalM PM Unit}
    (hx : ∀ σ τ, σ.steps = none → run x σ τ = .ok ((.ok (), σ), τ))
    (hy : ∀ σ τ, σ.steps = none → run y σ τ = .ok ((.ok (), σ), τ)) :
    FS (Sm E Gl G) Eq x y := by
  refine ⟨fun σ σ' τ τ' hs ht _ => ?_⟩
  have hs' : StRel G (IxRel E) σ σ' := hs
  rw [hx σ τ hs'.steps, hy σ' τ' hs'.steps']
  exact ⟨rfl, hs, ht⟩

theorem fs_chargeStep : FS (Sm E Gl G) Eq (chargeStep : EvalM PM Unit) chargeStep :=
  fs_unit (fun _ τ h => run_chargeStep h τ) (fun _ τ h => run_chargeStep h τ)

omit [Reserved] in
theorem run_chargeIteration (b : StmtExprMd) {σ : EvalState} (h : σ.steps = none) (τ : Trace) :
    run (chargeIteration b : EvalM PM Unit) σ τ = .ok ((.ok (), σ), τ) := by
  unfold chargeIteration
  split
  · rfl
  · exact run_chargeStep h τ

theorem fs_chargeIteration (b b' : StmtExprMd) :
    FS (Sm E Gl G) Eq (chargeIteration b : EvalM PM Unit) (chargeIteration b') :=
  fs_unit (fun _ τ h => run_chargeIteration b h τ) (fun _ τ h => run_chargeIteration b' h τ)

theorem fs_switch {f g : EvalState → EvalState} {G' : StackFrame} {T U : SimRel} {B : γ → δ → Prop}
    {k : PUnit → EvalM PM γ} {k' : PUnit → EvalM PM δ}
    (h : ∀ σ σ', StRel G (IxRel E) σ σ' → StRel G' (IxRel E) (f σ) (g σ'))
    (hk : FSH (Sm E Gl G') T U B (k ()) (k' ())) :
    FSH (Sm E Gl G) T U B (modify f >>= k) (modify g >>= k') := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  rw [run_bind, run_modify] at hn ⊢
  exact hk.sim (f σ) (g σ') τ τ' (h σ σ' hs) ht hn

theorem StRel.muteIn {σ σ' : EvalState} (h : StRel G (IxRel E) σ σ') :
    StRel G (IxRel E) { σ with muted := true } { σ' with muted := true } := { h with muted := rfl }

theorem StRel.muteOut {σ σ' a a' : EvalState} (hs : StRel G (IxRel E) σ σ') (h : StRel G0 (IxRel E) a a') :
    StRel G0 (IxRel E) (MuteSt σ a) (MuteSt σ' a') := { h with muted := hs.muted }

theorem fs_muteE {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β} (h : FS (Sm E Gl G) A x y) :
    FS (Sm E Gl G) A (muteE x) (muteE y) := by
  refine fsh_muteE h (fun _ _ hs => StRel.muteIn hs) (fun _ _ _ _ hs ha => StRel.muteOut (E := E) hs ha)
    (fun _ _ c c' a a' hs hc => ?_)
  rcases hc with ⟨h1, h2, h3⟩ | ⟨v, h1, h2, h3⟩
  · exact .inl ⟨h1, h2, StRel.muteOut (E := E) hs h3⟩
  · exact .inr ⟨v, h1, h2, h3.1, StRel.muteOut (E := E) hs h3.2.1, h3.2.2⟩

theorem fs_muteSel {c : Prop} [Decidable c] {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β}
    (h : FS (Sm E Gl G) A x y) :
    FS (Sm E Gl G) A ((if c then muteE else id) x) ((if c then muteE else id) y) := by
  rw [muteSel_apply, muteSel_apply]
  split
  · exact fs_muteE h
  · exact h

def SimRel.at (S : SimRel) (σ0 σ0' : EvalState) : SimRel :=
  { S with st := fun σ σ' => σ = σ0 ∧ σ' = σ0' ∧ S.st σ σ' }

omit [Reserved] in
theorem fs_getAt {S T U : SimRel} {A : α → β → Prop} {k : EvalState → EvalM PM α} {k' : EvalState → EvalM PM β}
    (h : ∀ c c', S.st c c' → FSH (S.at c c') T U A (k c) (k' c')) :
    FSH S T U A (get >>= k) (get >>= k') := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  rw [run_bind, run_get] at hn ⊢
  exact (h σ σ' hs).sim σ σ' τ τ' ⟨rfl, rfl, hs⟩ ht hn

theorem fs_switchAt {σ0 σ0' : EvalState} {f g : EvalState → EvalState} {G' : StackFrame} {T U : SimRel}
    {B : γ → δ → Prop} {k : PUnit → EvalM PM γ} {k' : PUnit → EvalM PM δ}
    (h : StRel G (IxRel E) σ0 σ0' → StRel G' (IxRel E) (f σ0) (g σ0'))
    (hk : FSH (Sm E Gl G') T U B (k ()) (k' ())) :
    FSH ((Sm E Gl G).at σ0 σ0') T U B (modify f >>= k) (modify g >>= k') := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  obtain ⟨rfl, rfl, hs⟩ := hs
  rw [run_bind, run_modify] at hn ⊢
  exact hk.sim (f σ) (g σ') τ τ' (h hs) ht hn

theorem fs_switch1 {f g : EvalState → EvalState} {G' : StackFrame} {U : SimRel}
    (h : ∀ σ σ', StRel G (IxRel E) σ σ' → StRel G' (IxRel E) (f σ) (g σ')) :
    FSH (Sm E Gl G) (Sm E Gl G') U Eq (modify f : EvalM PM PUnit) (modify g) := by
  refine ⟨fun σ σ' τ τ' hs ht _ => ?_⟩
  simp only [run_modify, RR, ExRel]
  exact ⟨trivial, h σ σ' hs, ht⟩

omit [Reserved] in
theorem fs_throwT {A : α → β → Prop} {S T : SimRel} (c : Control) (hc : S.ok c := by trivial) :
    FSH S T S A (throw c) (throw c) := by
  refine ⟨fun σ σ' τ τ' hs ht _ => ?_⟩
  simp only [run_throw, RR, ExRel]
  exact ⟨.inl ⟨.inl rfl, hc, hs⟩, ht⟩

omit [Reserved] in
theorem fs_throwTR {A : α → β → Prop} {S T : SimRel} {c c' : Control} (hc : S.ok c) (hr : CtlR S.ret c c') :
    FSH S T S A (throw c) (throw c') := by
  refine ⟨fun σ σ' τ τ' hs ht _ => ?_⟩
  simp only [run_throw, RR, ExRel]
  exact ⟨.inl ⟨hr, hc, hs⟩, ht⟩

omit [Reserved] in
theorem fs_throwTM {A : α → β → Prop} {S T : SimRel} {L : String} (hL : S.ret = some L)
    (hc : S.ok (.return_ [])) : FSH S T S A (throw (.return_ [])) (throw (.exit_ L)) :=
  fs_throwTR hc (.inr (.inl ⟨L, hL, rfl, rfl⟩))

theorem fs_evalError {A : α → β → Prop} (m m' : String) :
    FS (Sm E Gl G) A (evalError m : EvalM PM α) (evalError m') := by
  unfold evalError
  exact fs_bind fs_get (fun _ _ _ => fs_fail _ _)

theorem fs_refuse {A : α → β → Prop} (m m' : String) :
    FS (Sm E Gl G) A (refuse m : EvalM PM α) (refuse m') := by
  unfold refuse
  exact fs_bind fs_get (fun _ _ _ => fs_throwTR trivial (.inr (.inr ⟨_, _, rfl, rfl⟩)))

theorem fs_refuse_bind {A : α → β → Prop} (m m' : String) (k : PUnit → EvalM PM α) (k' : PUnit → EvalM PM β) :
    FS (Sm E Gl G) A ((refuse m : EvalM PM PUnit) >>= k) ((refuse m' : EvalM PM PUnit) >>= k') := by
  unfold refuse
  simp only [bind_assoc]
  refine fs_bind fs_get (fun _ _ _ => ⟨fun σ σ' τ τ' hs ht _ => ?_⟩)
  have hb : ∀ {γ : Type} (c : Control) (k : PUnit → EvalM PM γ) (σ : EvalState) (τ : Trace),
      run ((throw c : EvalM PM PUnit) >>= k) σ τ = .ok ((.error c, σ), τ) := fun _ _ _ _ => rfl
  simp only [hb, RR, ExRel]
  exact ⟨.inl ⟨.inr (.inr ⟨_, _, rfl, rfl⟩), trivial, hs⟩, ht⟩

theorem fs_stuckError {A : α → β → Prop} (m m' : String) :
    FS (Sm E Gl G) A (stuckError m : EvalM PM α) (stuckError m') := by
  refine ⟨fun σ σ' τ τ' _ _ _ => ?_⟩
  show RR _ _ A (.error (.stuck m)) (.error (.stuck m'))
  exact fun _ => .mk m

theorem fs_modifyRel {f g : EvalState → EvalState}
    (h : ∀ σ σ', StRel G (IxRel E) σ σ' → StRel G (IxRel E) (f σ) (g σ')) :
    FSH (Sm E Gl G) (Sm E Gl G) U Eq (modify f : EvalM PM PUnit) (modify g) :=
  (fs_modify (S := Sm E Gl G) h).weaken (fun _ _ _ => rfl)

theorem fs_get' : FS (Sm E Gl G) (StRel G (IxRel E)) (get : EvalM PM EvalState) get := fs_get

theorem fs_wow {T U : SimRel} {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β} {s t : StmtExprMd}
    (h : FSH (Sm E Gl G) T U A x y) : FSH (Sm E Gl G) T U A (withOperandWindow s x) (withOperandWindow t y) :=
  FSH.wow (fun _ _ (h : StRel G (IxRel E) _ _) => ⟨h.ops, h.ops'⟩) h

theorem fs_wowL {T U : SimRel} {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β} {s : StmtExprMd}
    (h : FSH (Sm E Gl G) T U A x y) : FSH (Sm E Gl G) T U A (withOperandWindow s x) y :=
  FSH.wowL (fun _ _ (h : StRel G (IxRel E) _ _) => h.ops) h

theorem fs_wowRb {T U : SimRel} {A : α → γ → Prop} {x : EvalM PM α} {y : EvalM PM β} {k : β → EvalM PM γ}
    {t : StmtExprMd} (h : FSH (Sm E Gl G) T U A x (y >>= k)) :
    FSH (Sm E Gl G) T U A x (withOperandWindow t y >>= k) :=
  FSH.wowRb (fun _ _ (h : StRel G (IxRel E) _ _) => h.ops') h

theorem fs_wowR {T U : SimRel} {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β} {t : StmtExprMd}
    (h : FSH (Sm E Gl G) T U A x y) : FSH (Sm E Gl G) T U A x (withOperandWindow t y) :=
  FSH.wowR (fun _ _ (h : StRel G (IxRel E) _ _) => h.ops') h

omit [Reserved] in
theorem keepsOOF_restore_throw (f : EvalState → EvalState) :
    KeepsOOF (fun (sig : Control) => (do
      match sig with
      | .suspended => pure ()
      | _ => (modify f : EvalM PM PUnit)
      throw sig : EvalM PM α)) := by
  intro σ τ
  simp [run_bind, run_throw, run_modify, OOF]

theorem StRel.with_stack {IR : ProgramIndex → ProgramIndex → Prop} {a a' : EvalState} (ha : StRel G IR a a')
    {f g : StackFrame} (hs : SR G a.globals f g) : StRel G IR { a with stack := f } { a' with stack := g } :=
  { ha with stack := hs }

theorem SR.unwind (ns : List String) (hr : ∀ n ∈ ns, ¬ Reserved.res n) (hv : ∀ n ∈ ns, NotV n)
    {G' d d' : StackFrame} {gs' : Std.HashMap String Value} (hd : SR G' gs' d d') :
    ∀ {s s' : StackFrame}, SR G gs s s' →
      SR G gs ((ns.map fun n => (n, Interpreter.shadowDepth d n)).foldl
          (fun acc nd => Interpreter.popShadowsTo acc nd.1 nd.2) s)
        ((ns.map fun n => (n, Interpreter.shadowDepth d' n)).foldl
          (fun acc nd => Interpreter.popShadowsTo acc nd.1 nd.2) s') := by
  induction ns with
  | nil => exact fun h => h
  | cons n ns ih =>
    intro s s' h
    simp only [List.map_cons, List.foldl_cons]
    rw [hd.shadowDepth (hr n (List.mem_cons_self ..))]
    exact ih (fun m hm => hr m (List.mem_cons_of_mem _ hm)) (fun m hm => hv m (List.mem_cons_of_mem _ hm))
      (h.popShadowsTo (hr n (List.mem_cons_self ..)) (hv n (List.mem_cons_self ..)) _)

omit [Reserved] in
theorem unbindCatch_ne {f : StackFrame} {n k : String} (h1 : n ≠ k) (h2 : shadowKey n ≠ k) :
    (Interpreter.unbindCatch f n)[k]? = f[k]? := by
  unfold Interpreter.unbindCatch
  split
  · split
    · rfl
    · split <;> split <;> (try split) <;>
        simp [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, h1, h2]
  · rfl

omit [Reserved] in
theorem popShadowsGo_ne {n k : String} (h1 : n ≠ k) (h2 : shadowKey n ≠ k) (d : Nat) :
    ∀ m (f : StackFrame), (Interpreter.popShadowsGo n d m f)[k]? = f[k]?
  | 0, _ => rfl
  | m + 1, f => by
    simp only [Interpreter.popShadowsGo]
    split
    · rw [popShadowsGo_ne h1 h2 d m, unbindCatch_ne h1 h2]
    · rfl

omit [Reserved] in
theorem unwind_ne (ns : List (String × Nat)) {k : String} (h : ∀ nd ∈ ns, nd.1 ≠ k ∧ shadowKey nd.1 ≠ k)
    (s : StackFrame) : (ns.foldl (fun acc nd => Interpreter.popShadowsTo acc nd.1 nd.2) s)[k]? = s[k]? := by
  induction ns generalizing s with
  | nil => rfl
  | cons nd ns ih =>
    simp only [List.foldl_cons]
    rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    unfold Interpreter.popShadowsTo
    exact popShadowsGo_ne (h nd (List.mem_cons_self ..)).1 (h nd (List.mem_cons_self ..)).2 _ _ _

inductive LooseExt (G : StackFrame) : List String → List String → Prop
  | nil : LooseExt G [] []
  | same {d : String} {ds ds' : List String} : LooseExt G ds ds' → LooseExt G (d :: ds) (d :: ds')
  | extra {d : String} {ds ds' : List String} : Reserved.loose G d → (∀ k, d ≠ shadowKey k) → LooseExt G ds ds' →
      LooseExt G ds (d :: ds')

theorem LooseExt.refl : ∀ (l : List String), LooseExt G l l
  | [] => .nil
  | _ :: l => .same (LooseExt.refl l)

theorem LooseExt.append {a a' b b' : List String} (ha : LooseExt G a a') (hb : LooseExt G b b') :
    LooseExt G (a ++ b) (a' ++ b') := by
  induction ha with
  | nil => exact hb
  | same _ ih => exact .same ih
  | extra hl hns _ ih => exact .extra hl hns ih

theorem LooseExt.mem {a a' : List String} (h : LooseExt G a a') : ∀ x ∈ a', x ∈ a ∨ Reserved.loose G x := by
  induction h with
  | nil => intro x hx; cases hx
  | @same d _ _ _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .inl (List.mem_cons_self ..)
    · exact (ih x hx).imp (List.mem_cons_of_mem _) id
  | @extra d _ _ hl _ _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .inr hl
    · exact ih x hx

theorem LooseExt.ofEq {a b : List String} (h : a = b) : LooseExt G a b := h ▸ LooseExt.refl a

theorem LooseExt.nil_right {a : List String} (h : LooseExt G a []) : a = [] := by
  cases h; rfl

omit [Reserved] in
theorem popShadowsTo_ne {n k : String} (h1 : n ≠ k) (h2 : shadowKey n ≠ k) (d : Nat) (f : StackFrame) :
    (Interpreter.popShadowsTo f n d)[k]? = f[k]? :=
  popShadowsGo_ne h1 h2 d _ f

theorem SR.popLoose {s s' : StackFrame} (h : SR G gs s s') {n : String} (hl : Reserved.loose G n)
    (hnp : Reserved.pinOf G n = none) (hns : ∀ k, n ≠ shadowKey k) (d : Nat) :
    SR G gs s (Interpreter.popShadowsTo s' n d) := by
  have key : ∀ k, ¬ Reserved.loose G k → (Interpreter.popShadowsTo s' n d)[k]? = s'[k]? := fun k hk =>
    popShadowsTo_ne (fun e => hk (by rw [← e]; exact hl)) (fun e => hk (by rw [← e]; exact Reserved.loose_shadow G n hl)) d s'
  have nl : ∀ k, ¬ Reserved.res k → ¬ Reserved.loose G k := fun k hk hl => hk (Reserved.loose_res G k hl)
  refine ⟨fun k hk hkv => ?_, fun k hk hka hkl => ?_, fun o w ho hf hw => ?_, fun k ha => ?_, h.frozen, h.clean,
    fun k w δ x hp => ?_⟩
  · rw [key k (nl k hk)]; exact h.src k hk hkv
  · rw [key k hkl]; exact h.ghost k hk hka hkl
  · rw [key o (nl o (Reserved.vret_ok o ho).1)]; exact h.out o w ho hf hw
  · rw [key k (fun hl => Reserved.loose_alias G k hl ha)]; exact h.alias k ha
  · have hkn : n ≠ k := fun e => by rw [e, hp] at hnp; cases hnp
    refine (h.pin k w δ x hp).congr (popShadowsTo_ne hkn (fun e => Reserved.pin_noShadow G k _ hp n e.symm) d s')
      (popShadowsTo_ne (hns k) (fun e => hkn ((String.append_right_inj _).mp e)) d s')

def priorVal (p : Value) : Option Value :=
  match p with
  | .seq a => a[0]?
  | _ => some p

omit [Reserved] in
theorem unbind_eqs {f : StackFrame} {k : String} {q : Array Value} (hq : f[shadowKey k]? = some (.seq q))
    (hn : 0 < q.size) :
    (Interpreter.unbindCatch f k)[shadowKey k]? = (if q.size = 1 then none else some (.seq q.pop)) ∧
      (Interpreter.unbindCatch f k)[k]? = priorVal q[q.size - 1] := by
  have hne' : k ≠ shadowKey k := fun e => shadowKey_ne k e.symm
  have hback : q.back? = some q[q.size - 1] := by
    rw [Array.back?_eq_getElem?]; exact Array.getElem?_eq_getElem (by omega)
  unfold Interpreter.unbindCatch
  simp only [hq, hback]
  generalize q[q.size - 1] = p
  have e1 : ∀ (g : StackFrame) (w : Value), (g.insert k w)[shadowKey k]? = g[shadowKey k]? := fun g w => by
    rw [Std.HashMap.getElem?_insert, ite_eq_right (by simpa using hne')]
  have e2 : ∀ (g : StackFrame), (g.erase k)[shadowKey k]? = g[shadowKey k]? := fun g => by
    rw [Std.HashMap.getElem?_erase, ite_eq_right (by simpa using hne')]
  have e3 : (if (q.size == 1) = true then f.erase (shadowKey k) else f.insert (shadowKey k) (.seq q.pop))[shadowKey k]? =
      (if q.size = 1 then none else some (.seq q.pop)) := by
    by_cases h1 : q.size = 1 <;> simp [h1]
  have e4 : ∀ (g : StackFrame) (w : Value), (g.insert k w)[k]? = some w := fun g w => by simp
  have e5 : ∀ (g : StackFrame), (g.erase k)[k]? = none := fun g => by simp
  cases p with
  | seq a =>
    simp only [priorVal]
    cases ha : a[0]? with
    | some w => exact ⟨by rw [e1, e3], by rw [e4]⟩
    | none => exact ⟨by rw [e2, e3], by rw [e5]⟩
  | _ => exact ⟨by rw [e1, e3], by rw [e4]; rfl⟩

omit [Reserved] in
theorem PinOK.unbind {f : StackFrame} {k : String} {v : Value} {δ : Nat} (h : PinOK f k v δ false)
    (hd : δ < Interpreter.shadowDepth f k) :
    PinOK (Interpreter.unbindCatch f k) k v δ false ∧
      Interpreter.shadowDepth (Interpreter.unbindCatch f k) k + 1 = Interpreter.shadowDepth f k := by
  unfold PinOK at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨-, -, h3⟩ := h
  have h3 := h3 hd
  unfold shadowAt at h3
  have hd' := hd
  unfold Interpreter.shadowDepth at hd'
  split at hd'
  · rename_i q hq
    rw [hq] at h3
    simp only at h3
    have hfd : Interpreter.shadowDepth f k = q.size := by unfold Interpreter.shadowDepth; rw [hq]
    obtain ⟨u1, u2⟩ := unbind_eqs hq (by omega)
    have hdep : Interpreter.shadowDepth (Interpreter.unbindCatch f k) k = q.size - 1 := by
      unfold Interpreter.shadowDepth; rw [u1]
      by_cases h1 : q.size = 1
      · simp [h1]
      · simp [h1]
    have hat : ∀ i, shadowAt (Interpreter.unbindCatch f k) k i = if q.size = 1 then none else q.pop[i]? := by
      intro i; unfold shadowAt; rw [u1]
      by_cases h1 : q.size = 1 <;> simp [h1]
    unfold PinOK
    simp only [Bool.false_eq_true, ite_false]
    rw [hdep, hfd]
    refine ⟨⟨by omega, fun he => ?_, fun hlt => ?_⟩, by omega⟩
    · rw [u2]
      have : q.size - 1 = δ := he
      rw [show q[q.size - 1] = q[δ] from by simp [this]]
      rw [Array.getElem?_eq_getElem (by omega)] at h3
      rw [Option.some.inj h3]
      rfl
    · rw [hat, ite_eq_right (by omega), Array.getElem?_pop, ite_eq_left hlt]
      exact h3
  · omega

omit [Reserved] in
theorem PinOK.popGo {m : String} {v : Value} {δ e : Nat} (he : δ ≤ e) :
    ∀ j (f : StackFrame), PinOK f m v δ false →
      PinOK (Interpreter.popShadowsGo m e j f) m v δ false ∧
      (Interpreter.shadowDepth f m ≤ j + e →
        Interpreter.shadowDepth (Interpreter.popShadowsGo m e j f) m = min (Interpreter.shadowDepth f m) e)
  | 0, f, h => ⟨h, fun hd => by simp only [Interpreter.popShadowsGo]; omega⟩
  | j + 1, f, h => by
    simp only [Interpreter.popShadowsGo]
    split
    · rename_i hgt
      obtain ⟨h1, h2⟩ := h.unbind (by omega)
      obtain ⟨r1, r2⟩ := PinOK.popGo he j _ h1
      exact ⟨r1, fun hd => by rw [r2 (by omega)]; omega⟩
    · rename_i hle
      exact ⟨h, fun _ => by omega⟩

omit [Reserved] in
theorem PinOK.pop {f : StackFrame} {m : String} {v : Value} {δ e : Nat} (h : PinOK f m v δ false) (he : δ ≤ e) :
    PinOK (Interpreter.popShadowsTo f m e) m v δ false ∧
      Interpreter.shadowDepth (Interpreter.popShadowsTo f m e) m = min (Interpreter.shadowDepth f m) e := by
  unfold Interpreter.popShadowsTo
  obtain ⟨r1, r2⟩ := PinOK.popGo he _ f h
  exact ⟨r1, r2 (by omega)⟩

omit [Reserved] in
theorem PinOK.depth_ge {f : StackFrame} {m : String} {v : Value} {δ : Nat} {x : Bool} (h : PinOK f m v δ x) :
    δ ≤ Interpreter.shadowDepth f m := by
  unfold PinOK at h
  cases x with
  | false => exact h.1
  | true => simp only [ite_true] at h; omega

omit [Reserved] in
theorem PinOK.exactOf {f : StackFrame} {m : String} {v : Value} {δ : Nat} (h : PinOK f m v δ false)
    (hd : Interpreter.shadowDepth f m = δ) : PinOK f m v δ true := by
  unfold PinOK at h ⊢
  simp only [Bool.false_eq_true, ite_false, ite_true] at h ⊢
  exact ⟨hd, h.2.1 hd⟩

theorem sameRegime_relax (G : StackFrame) (ds : List String) : SameRegime G (Reserved.relax G ds) :=
  fun k hk => Reserved.relax_get G ds k hk

theorem SR.remap {G1 G2 s s' : StackFrame} (h : SR G1 gs s s') (hsr : SameRegime G1 G2)
    (ha : ∀ k, Reserved.aliasOf G2 k ↔ Reserved.aliasOf G1 k)
    (hf : ∀ k, Reserved.frozenOf G2 k = Reserved.frozenOf G1 k)
    (hl : ∀ k, Reserved.loose G2 k ↔ Reserved.loose G1 k)
    (hp : ∀ k v δ x, Reserved.pinOf G2 k = some (v, δ, x) → PinOK s' k v δ x) : SR G2 gs s s' := by
  refine ⟨fun k hk hkv => h.src k hk (hkv.imp id hsr.strict.mp), fun k hk hka hkl => ?_, fun o w ho hc hw => ?_,
    fun k hk => h.alias k ((ha k).mp hk), fun k v hv => h.frozen k v (by rw [← hf k]; exact hv), h.clean, hp⟩
  · rw [hsr k (.inl hk)]; exact h.ghost k hk (fun x => hka ((ha k).mpr x)) (fun x => hkl ((hl k).mpr x))
  · rw [hsr.contains (.inr ⟨o, ho, .inr (.inl rfl)⟩)] at hc
    rw [hsr o (.inr ⟨o, ho, .inl rfl⟩)] at hw
    exact h.out o w ho hc hw

theorem SR.relax {s s' : StackFrame} (h : SR G gs s s') (ds : List String) : SR (Reserved.relax G ds) gs s s' := by
  refine h.remap (sameRegime_relax G ds) (Reserved.relax_alias G ds) (Reserved.relax_frozen G ds)
    (Reserved.relax_loose G ds) (fun k v δ x hp => ?_)
  rw [Reserved.relax_pin] at hp
  split at hp
  · cases hq : Reserved.pinOf G k with
    | none => rw [hq] at hp; cases hp
    | some p =>
      rw [hq] at hp
      obtain ⟨v0, δ0, x0⟩ := p
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      exact (h.pin k _ _ _ hq).weaken
  · exact h.pin k v δ x hp

theorem relax_relax_same (G : StackFrame) (l1 l2 : List String) : SameRegime (Reserved.relax G l1) (Reserved.relax G l2) :=
  fun k hk => (Reserved.relax_get G l2 k hk).trans (Reserved.relax_get G l1 k hk).symm

theorem SR.relaxDrop {s s' : StackFrame} {n : String} {l : List String} (h : SR (Reserved.relax G (n :: l)) gs s s')
    (hn : Reserved.pinOf G n = none) : SR (Reserved.relax G l) gs s s' := by
  refine h.remap (relax_relax_same G _ _) (fun k => (Reserved.relax_alias G l k).trans (Reserved.relax_alias G _ k).symm)
    (fun k => (Reserved.relax_frozen G l k).trans (Reserved.relax_frozen G _ k).symm)
    (fun k => (Reserved.relax_loose G l k).trans (Reserved.relax_loose G _ k).symm) (fun k v δ x hp => ?_)
  refine h.pin k v δ x ?_
  rw [Reserved.relax_pin] at hp ⊢
  by_cases hk : k = n
  · subst hk; rw [hn] at hp; simp at hp
  · have e : (k ∈ n :: l) ↔ k ∈ l := by simp [hk]
    by_cases hkl : k ∈ l
    · rw [ite_eq_left hkl] at hp; rw [ite_eq_left (e.mpr hkl)]; exact hp
    · rw [ite_eq_right hkl] at hp; rw [ite_eq_right (fun h => hkl (e.mp h))]; exact hp

theorem SR.relaxNil {s s' : StackFrame} (h : SR (Reserved.relax G []) gs s s') : SR G gs s s' := by
  refine h.remap (sameRegime_relax G []).symm (fun k => (Reserved.relax_alias G [] k).symm)
    (fun k => (Reserved.relax_frozen G [] k).symm) (fun k => (Reserved.relax_loose G [] k).symm)
    (fun k v δ x hp => h.pin k v δ x ?_)
  rw [Reserved.relax_pin, ite_eq_right (by simp)]; exact hp

theorem SR.popExtra {s s' d' : StackFrame} {m : String} {l : List String}
    (h : SR (Reserved.relax G (m :: l)) gs s s') (hl : Reserved.loose G m) (hns : ∀ k, m ≠ shadowKey k)
    (hent : ∀ v δ x, Reserved.pinOf G m = some (v, δ, x) → PinOK d' m v δ x) :
    SR (Reserved.relax G l) gs s (Interpreter.popShadowsTo s' m (Interpreter.shadowDepth d' m)) := by
  have hlr : Reserved.loose (Reserved.relax G (m :: l)) m := (Reserved.relax_loose G _ m).mpr hl
  have key : ∀ k, k ≠ m → shadowKey m ≠ k → (Interpreter.popShadowsTo s' m (Interpreter.shadowDepth d' m))[k]? = s'[k]? :=
    fun k h1 h2 => popShadowsTo_ne (fun e => h1 e.symm) h2 _ s'
  have nl : ∀ k, Reserved.loose (Reserved.relax G (m :: l)) k ∨ ¬ Reserved.res k → (k ≠ m ∧ shadowKey m ≠ k) ∨ Reserved.loose (Reserved.relax G (m :: l)) k := by
    intro k hk; rcases hk with hk | hk
    · exact .inr hk
    · exact .inl ⟨fun e => hk (by rw [e]; exact Reserved.loose_res _ _ hlr),
        fun e => hk (by rw [← e]; exact Reserved.loose_res _ _ (Reserved.loose_shadow _ m hlr))⟩
  have keyU : ∀ k, ¬ Reserved.res k → (Interpreter.popShadowsTo s' m (Interpreter.shadowDepth d' m))[k]? = s'[k]? :=
    fun k hk => key k (fun e => hk (by rw [e]; exact Reserved.loose_res _ _ hlr))
      (fun e => hk (by rw [← e]; exact Reserved.loose_res _ _ (Reserved.loose_shadow _ m hlr)))
  have keyL : ∀ k, ¬ Reserved.loose (Reserved.relax G (m :: l)) k →
      (Interpreter.popShadowsTo s' m (Interpreter.shadowDepth d' m))[k]? = s'[k]? :=
    fun k hk => key k (fun e => hk (by rw [e]; exact hlr)) (fun e => hk (by rw [← e]; exact Reserved.loose_shadow _ m hlr))
  have hsr := relax_relax_same G (m :: l) l
  refine ⟨fun k hk hkv => ?_, fun k hk hka hkl => ?_, fun o w ho hf hw => ?_, fun k ha => ?_,
    fun k w hw => h.frozen k w (by rw [Reserved.relax_frozen, ← Reserved.relax_frozen G l]; exact hw), h.clean,
    fun k w δ x hp => ?_⟩
  · rw [keyU k hk]; exact h.src k hk (hkv.imp id hsr.strict.mp)
  · have hkl' : ¬ Reserved.loose (Reserved.relax G (m :: l)) k := fun x =>
      hkl ((Reserved.relax_loose G l k).mpr ((Reserved.relax_loose G _ k).mp x))
    rw [keyL k hkl', hsr k (.inl hk)]
    exact h.ghost k hk (fun x => hka ((Reserved.relax_alias G l k).mpr ((Reserved.relax_alias G _ k).mp x))) hkl'
  · rw [keyU o (Reserved.vret_ok o ho).1]
    rw [hsr.contains (.inr ⟨o, ho, .inr (.inl rfl)⟩)] at hf
    rw [hsr o (.inr ⟨o, ho, .inl rfl⟩)] at hw
    exact h.out o w ho hf hw
  · have ha' : Reserved.aliasOf (Reserved.relax G (m :: l)) k :=
      (Reserved.relax_alias G _ k).mpr ((Reserved.relax_alias G l k).mp ha)
    rw [keyL k (fun x => Reserved.loose_alias _ k x ha')]
    exact h.alias k ha'
  · rw [Reserved.relax_pin] at hp
    by_cases hk : k = m
    · subst hk
      cases hq : Reserved.pinOf G k with
      | none => rw [hq] at hp; split at hp <;> simp at hp
      | some p =>
        obtain ⟨v0, δ0, x0⟩ := p
        have hd0 := hent v0 δ0 x0 hq
        have hrel := h.pin k v0 δ0 false (by rw [Reserved.relax_pin, ite_eq_left (by simp), hq]; rfl)
        obtain ⟨r1, r2⟩ := hrel.pop hd0.depth_ge
        rw [hq] at hp
        split at hp
        · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl, rfl⟩ := hp
          exact r1
        · simp only [Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl, rfl⟩ := hp
          cases x0 with
          | false => exact r1
          | true =>
            refine r1.exactOf ?_
            have hdd : Interpreter.shadowDepth d' k = δ0 := by
              unfold PinOK at hd0; simp only [ite_true] at hd0; exact hd0.1
            rw [r2, hdd]
            exact Nat.min_eq_right hrel.depth_ge
    · have hnp : Reserved.pinOf (Reserved.relax G (m :: l)) k = some (w, δ, x) := by
        rw [Reserved.relax_pin]
        have e : (k ∈ m :: l) ↔ k ∈ l := by simp [hk]
        by_cases hkl : k ∈ l
        · rw [ite_eq_left hkl] at hp; rw [ite_eq_left (e.mpr hkl)]; exact hp
        · rw [ite_eq_right hkl] at hp; rw [ite_eq_right (fun h => hkl (e.mp h))]; exact hp
      refine (h.pin k w δ x hnp).congr (key k hk ?_) (key _ (fun e => hns k e.symm)
        (fun e => hk ((String.append_right_inj _).mp e).symm))
      exact fun e => Reserved.pin_noShadow _ k _ hnp m e.symm

theorem SR.unwindX {ns ns' : List String} (hx : LooseExt G ns ns') (hr : ∀ n ∈ ns, ¬ Reserved.res n)
    (hv : ∀ n ∈ ns, NotV n) {d d' : StackFrame} {gs' : Std.HashMap String Value} (hd : SR G gs' d d') :
    ∀ {s s' : StackFrame}, SR (Reserved.relax G ns') gs s s' →
      SR G gs ((ns.map fun n => (n, Interpreter.shadowDepth d n)).foldl
          (fun acc nd => Interpreter.popShadowsTo acc nd.1 nd.2) s)
        ((ns'.map fun n => (n, Interpreter.shadowDepth d' n)).foldl
          (fun acc nd => Interpreter.popShadowsTo acc nd.1 nd.2) s') := by
  induction hx with
  | nil => exact fun h => h.relaxNil
  | @same n ns ns' _ ih =>
    intro s s' h
    simp only [List.map_cons, List.foldl_cons]
    rw [hd.shadowDepth (hr n (List.mem_cons_self ..))]
    have hn := hr n (List.mem_cons_self ..)
    exact ih (fun m hm => hr m (List.mem_cons_of_mem _ hm)) (fun m hm => hv m (List.mem_cons_of_mem _ hm))
      ((h.popShadowsTo hn (hv n (List.mem_cons_self ..)) _).relaxDrop
        (by cases hq : Reserved.pinOf G n with
            | none => rfl
            | some p => exact absurd (pin_res hq) hn))
  | @extra m ns ns' hl hns _ ih =>
    intro s s' h
    simp only [List.map_cons, List.foldl_cons]
    exact ih hr hv (h.popExtra hl hns (fun v δ x hp => hd.pin m v δ x hp))

def wbsU (names : List String) (act : EvalM PM α) : EvalM PM α := do
  let st ← get
  let inCoro := st.coroSelf.isSome
  let depthKey (n : String) := s!"$scopeDepth${st.cursor}${n}"
  let depths : List (String × Nat) := names.map fun n =>
    match (if inCoro then st.stack[depthKey n]? else none) with
    | some (.int ⟨d⟩) => (n, d.toNat)
    | _ => (n, shadowDepth st.stack n)
  let record (frame : StackFrame) : StackFrame :=
    depths.foldl (init := frame) fun acc nd => acc.insert (depthKey nd.1) (.int ⟨Int.ofNat nd.2⟩)
  let unwind (frame : StackFrame) : StackFrame :=
    depths.foldl (init := frame) fun acc nd =>
      let acc := popShadowsTo acc nd.1 nd.2
      if inCoro then acc.erase (depthKey nd.1) else acc
  if inCoro then
    modify fun s => { s with stack := record s.stack }
  let restore : EvalM PM Unit := modify fun s => { s with stack := unwind s.stack }
  let r ← tryCatch act fun sig => do
    match sig with
    | .suspended => pure ()
    | _ => restore
    throw sig
  restore
  pure r

omit [Reserved] in
theorem withBlockScope_eq (l : List StmtExprMd) (act : EvalM PM α) :
    withBlockScope l act = if (blockDeclarations l).isEmpty then act else wbsU (blockDeclarations l) act := rfl

omit [Reserved] in
theorem run_wbsU_nil (act : EvalM PM α) (σ : EvalState) (τ : Trace) : run (wbsU [] act) σ τ = run act σ τ := by
  unfold wbsU
  simp only [List.map_nil, List.foldl_nil]
  rw [run_bind, run_get]
  dsimp only
  split
  · rw [run_bind, run_modify]
    dsimp only
    rw [run_bind, run_tryCatch]
    rcases run act σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩
    · rfl
    · dsimp only
      cases c <;> simp [run_bind, run_modify, run_throw]
    · dsimp only
      rw [run_bind, run_modify]
      rfl
  · rw [run_bind, run_tryCatch]
    rcases run act σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩
    · rfl
    · dsimp only
      cases c <;> simp [run_bind, run_modify, run_throw]
    · dsimp only
      rw [run_bind, run_modify]
      rfl

/-- Running related actions inside a block scope preserves `FS`: if `x` is simulated by `y`, then
`withBlockScope l x` is simulated by `withBlockScope l' y`. The two statement lists must declare the
same names, and none of those names may be reserved or be the pass's valued-return output (`NotV`). -/
theorem fs_wbs {l l' : List StmtExprMd} (hn : blockDeclarations l = blockDeclarations l')
    (hr : ∀ n ∈ blockDeclarations l, ¬ Reserved.res n) (hv : ∀ n ∈ blockDeclarations l, NotV n)
    {A : α → α → Prop} {x y : EvalM PM α} (h : FS (Sm E Gl G) A x y) :
    FS (Sm E Gl G) A (withBlockScope l x) (withBlockScope l' y) := by
  unfold withBlockScope
  rw [← hn]
  dsimp only
  split
  · exact h
  · refine fs_bind fs_get (fun σ σ' hσ => ?_)
    have hσ : StRel G (IxRel E) σ σ' := hσ
    simp only [hσ.coroSelf, hσ.coroSelf', Option.isSome_none, Bool.false_eq_true, ite_false]
    refine fs_bind (fs_tryCatch h (fun c hc => ?_) (keepsOOF_restore_throw _) (fun L hL hok => ?_)
      (fun w => ?_)) (fun r r' hr' => ?_)
    · cases c <;> dsimp only <;> first
        | exact fs_throw _ hc
        | exact fs_bind (fs_pure rfl) (fun _ _ _ => fs_throw _ hc)
        | exact fs_bind (fs_modifyRel (fun a a' ha => ha.with_stack (SR.unwind _ hr hv hσ.stack ha.stack)))
            (fun _ _ _ => fs_throw _ hc)
    · exact fs_bind (fs_modifyRel (fun a a' ha => ha.with_stack (SR.unwind _ hr hv hσ.stack ha.stack)))
        (fun _ _ _ => fs_throwM hL hok)
    · refine fs_bind (fs_modify (S := (Sm E Gl G).atWin w) (fun a a' ⟨hf, ha, ho⟩ =>
        ⟨hf, ha.with_stack (SR.unwind _ hr hv hσ.stack ha.stack), fun o hvo => ?_⟩)) (fun _ _ _ => fs_throwW w)
      dsimp only
      rw [unwind_ne _ (fun nd hnd => ?_)]
      · exact ho o hvo
      · simp only [List.mem_map] at hnd
        obtain ⟨m, hm, rfl⟩ := hnd
        exact ⟨hv m hm o hvo, (Reserved.vret_ok o hvo).2.2 m⟩
    · exact fs_bind (fs_modifyRel (fun a a' ha => ha.with_stack (SR.unwind _ hr hv hσ.stack ha.stack)))
        (fun _ _ _ => fs_pure hr')

omit [Reserved] in
theorem keepsOOF_restore_labels (saved : List String) :
    KeepsOOF (fun (sig : Control) => (do
      modify fun (s : EvalState) => { s with openLabels := saved }
      throw sig : EvalM PM α)) := by
  intro σ τ
  simp [run_bind, run_throw, run_modify, OOF]

/-- Running related actions with the open labels replaced preserves `FS`: if `x` is simulated by `y`, and `f`
and `g` take lists of open labels that agree on every label that is not reserved to lists that do, then
`withLabels f x` is simulated by `withLabels g y`. Each side restores its own list on the way out, so the
two lists keep agreeing on every label that is not reserved. -/
theorem fs_withLabels (f g : List String → List String)
    (hfg : ∀ A B : List String, (∀ l, ¬ Reserved.resLabel l → (l ∈ A ↔ l ∈ B)) →
      ∀ l, ¬ Reserved.resLabel l → (l ∈ f A ↔ l ∈ g B))
    {A : α → α → Prop} {x y : EvalM PM α} (h : FS (Sm E Gl G) A x y) :
    FS (Sm E Gl G) A (withLabels f x) (withLabels g y) := by
  unfold withLabels
  refine fs_bind fs_get (fun σ σ' hσ => ?_)
  have hσ : StRel G (IxRel E) σ σ' := hσ
  refine fs_bind (fs_modifyRel (fun a a' ha => ?_)) (fun _ _ _ => ?_)
  · exact { ha with openLabels := hfg _ _ hσ.openLabels }
  refine fs_bind (fs_tryCatch h (fun c hc => ?_) (keepsOOF_restore_labels _) (fun L hL hok => ?_)
    (fun w => ?_)) (fun r r' hr' => ?_)
  · exact fs_bind (fs_modifyRel (fun a a' ha => { ha with openLabels := hσ.openLabels })) (fun _ _ _ => fs_throw _ hc)
  · exact fs_bind (fs_modifyRel (fun a a' ha => { ha with openLabels := hσ.openLabels })) (fun _ _ _ => fs_throwM hL hok)
  · exact fs_bind (fs_modify (S := (Sm E Gl G).atWin w) (fun a a' ⟨hf, ha, ho⟩ =>
      ⟨hf, { ha with openLabels := hσ.openLabels }, ho⟩)) (fun _ _ _ => fs_throwW w)
  · exact fs_bind (fs_modifyRel (fun a a' ha => { ha with openLabels := hσ.openLabels })) (fun _ _ _ => fs_pure hr')

/-- Running related actions with a labelled block open preserves `FS`: if `x` is simulated by `y`, then
`withOpenLabel l x` is simulated by `withOpenLabel l y`. -/
theorem fs_withOpenLabel (l : String) {A : α → α → Prop} {x y : EvalM PM α} (h : FS (Sm E Gl G) A x y) :
    FS (Sm E Gl G) A (withOpenLabel l x) (withOpenLabel l y) :=
  fs_withLabels (l :: ·) (l :: ·) (fun _ _ hAB k hk => by simp only [List.mem_cons]; exact or_congr Iff.rfl (hAB k hk)) h

/-- The simulation relation `Sm` for states whose target has exactly the labels `ol` open. -/
def SmO (E : StmtExprMd → StmtExprMd → Prop) (Gl : String → Prop) (G : StackFrame) (ol : List String) : SimRel :=
  { Sm E Gl G with
    st := fun σ σ' => StRel G (IxRel E) σ σ' ∧ σ'.openLabels = ol
    win := fun v σ σ' => (Sm E Gl G).win v σ σ' ∧ σ'.openLabels = ol }

theorem SmO.noWin {ol : List String} (hf : ¬ Free G) (v : Value) {σ σ' : EvalState} :
    ¬ (SmO E Gl G ol).win v σ σ' := fun h => hf h.1.1

/-- A simulation by `Sm` of a target action that keeps the open labels is a simulation by `SmO ol` for every
list `ol` of open labels of the target. -/
theorem FSH.toO {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β} (hy : KeepsOL y) (ol : List String)
    (h : FS (Sm E Gl G) A x y) : FS (SmO E Gl G ol) A x y := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have r0 := h.sim σ σ' τ τ' hs.1 ht hn
  rcases hr : run y σ' τ' with e | ⟨⟨c | b, σ1'⟩, τ1'⟩ <;> rw [hr] at r0 <;>
    rcases hx : run x σ τ with e0 | ⟨⟨c0 | a0, σ1⟩, τ1⟩ <;> rw [hx] at r0 <;> simp only [RR, ExRel] at r0 ⊢
  all_goals try exact r0
  all_goals try exact r0.1.elim
  · have hk := (hy ol).keep _ _ _ _ _ hs.2 hr
    obtain ⟨hsg, ht1⟩ := r0
    refine ⟨?_, ht1⟩
    rcases hsg with ⟨h1, h2, h3⟩ | ⟨v, h1, h2, h3⟩
    · exact .inl ⟨h1, h2, h3, hk⟩
    · exact .inr ⟨v, h1, h2, h3, hk⟩
  · have hk := (hy ol).keep _ _ _ _ _ hs.2 hr
    obtain ⟨h1, h2, h3⟩ := r0
    exact ⟨h1, ⟨h2, hk⟩, h3⟩

/-- A simulation by `SmO ol`, for every list `ol` containing the reserved label `L`, is a simulation by `Sm` of the
same target action run with `L` open. -/
theorem fs_openR (L : String) (hL : Reserved.resLabel L) {A : α → α → Prop} {x y : EvalM PM α}
    (h : ∀ ol, L ∈ ol → FS (SmO E Gl G ol) A x y) :
    FS (Sm E Gl G) A x (withOpenLabel L y) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have hs' : StRel G (IxRel E) σ σ' := hs
  have hst : (SmO E Gl G (L :: σ'.openLabels)).st σ { σ' with openLabels := L :: σ'.openLabels } :=
    ⟨hs'.pushOL hL, rfl⟩
  have r0 := (h (L :: σ'.openLabels) (List.mem_cons_self ..)).sim σ _ τ τ' hst ht hn
  rw [run_withOpenLabel]
  have hrestore : ∀ (a a' : EvalState), StRel G (IxRel E) a a' → a'.openLabels = L :: σ'.openLabels →
      StRel G (IxRel E) a { a' with openLabels := σ'.openLabels } := fun a a' ha he => ha.restoreOL he hL
  rcases hr : run y { σ' with openLabels := L :: σ'.openLabels } τ' with e | ⟨⟨c | b, σ1'⟩, τ1'⟩ <;> rw [hr] at r0 <;>
    rcases hx : run x σ τ with e0 | ⟨⟨c0 | a0, σ1⟩, τ1⟩ <;> rw [hx] at r0 <;> simp only [RR, ExRel] at r0 ⊢
  all_goals try exact r0
  all_goals try exact r0.1.elim
  · obtain ⟨hsg, ht1⟩ := r0
    refine ⟨?_, ht1⟩
    rcases hsg with ⟨h1, h2, h3, h4⟩ | ⟨v, h1, h2, ⟨hf, h3, ho⟩, h4⟩
    · exact .inl ⟨h1, h2, hrestore _ _ h3 h4⟩
    · exact .inr ⟨v, h1, h2, hf, hrestore _ _ h3 h4, ho⟩
  · obtain ⟨h1, ⟨h2, h4⟩, h3⟩ := r0
    exact ⟨h1, hrestore _ _ h2 h4, h3⟩

omit [Reserved] in
theorem FSH.congrL {S T U : SimRel} {A : α → β → Prop} {x x' : EvalM PM α} {y : EvalM PM β} (h : FSH S T U A x' y)
    (e : ∀ σ τ, run x σ τ = run x' σ τ) : FSH S T U A x y :=
  ⟨fun σ σ' τ τ' hs ht hn => by rw [e]; exact h.sim σ σ' τ τ' hs ht (by rw [← e]; exact hn)⟩

theorem StRel.relaxR {IR : ProgramIndex → ProgramIndex → Prop} {a a' : EvalState} (ha : StRel G IR a a')
    (ds : List String) : StRel (Reserved.relax G ds) IR a a' :=
  { ha with stack := ha.stack.relax ds, wf := (sameRegime_relax G ds).wfg ha.wf, entR := ha.entR.congr (Reserved.relax_alias G ds) (Reserved.relax_frozen G ds) (Reserved.entOK_relax G ds) }

theorem StRel.unrelax {IR : ProgramIndex → ProgramIndex → Prop} {a a' : EvalState} {ds : List String}
    (ha : StRel (Reserved.relax G ds) IR a a') (hw : WFG G) {f g : StackFrame} (hs : SR G a.globals f g) :
    StRel G IR { a with stack := f } { a' with stack := g } :=
  { ha with stack := hs, wf := hw, entR := ha.entR.congr (fun k => (Reserved.relax_alias G ds k).symm) (fun k => (Reserved.relax_frozen G ds k).symm) (Reserved.entOK_unrelax G ds) }

theorem StRel.ofRelaxNil {IR : ProgramIndex → ProgramIndex → Prop} {a a' : EvalState}
    (ha : StRel (Reserved.relax G []) IR a a') : StRel G IR a a' :=
  { ha with stack := ha.stack.relaxNil, wf := (sameRegime_relax G []).symm.wfg ha.wf, entR := ha.entR.congr (fun k => (Reserved.relax_alias G [] k).symm) (fun k => (Reserved.relax_frozen G [] k).symm) (Reserved.entOK_unrelax G []) }

theorem fs_regime {G1 G2 : StackFrame} {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β}
    (h : FS (Sm E Gl G1) A x y) (h21 : ∀ a a', StRel G2 (IxRel E) a a' → StRel G1 (IxRel E) a a')
    (h12 : ∀ a a', StRel G1 (IxRel E) a a' → StRel G2 (IxRel E) a a') (hsr : SameRegime G1 G2) :
    FS (Sm E Gl G2) A x y := by
  refine h.reg h21 rfl h12 rfl (fun c c' σ σ' hs => ?_) rfl
  rcases hs with ⟨hcr, hok, hst⟩ | ⟨v, h1, h2, hf, hst, ho⟩
  · exact .inl ⟨hcr, CtlOK.regime hok hsr, h12 _ _ hst⟩
  · exact .inr ⟨v, h1, h2, hsr.free.mpr hf, h12 _ _ hst, ho⟩

theorem fs_wbsU {ns ns' : List String} (hx : LooseExt G ns ns') (hr : ∀ n ∈ ns, ¬ Reserved.res n)
    (hv : ∀ n ∈ ns, NotV n) {β : Type} {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β}
    (h : FS (Sm E Gl (Reserved.relax G ns')) A x y) :
    FS (Sm E Gl G) A (wbsU ns x) (wbsU ns' y) := by
  have hsr := sameRegime_relax G ns'
  unfold wbsU
  refine fs_bind fs_get (fun σ σ' hσ => ?_)
  have hσ : StRel G (IxRel E) σ σ' := hσ
  simp only [hσ.coroSelf, hσ.coroSelf', Option.isSome_none, Bool.false_eq_true, ite_false]
  refine fs_bind (fs_tryCatch (h.reg (S := Sm E Gl G) (fun a a' ha => StRel.relaxR ha ns') rfl (fun _ _ h => h) rfl
      (fun _ _ _ _ h => h) rfl) (fun c hc => ?_) (keepsOOF_restore_throw _) (fun L hL hok => ?_)
    (fun w => ?_)) (fun r r' hr' => ?_)
  · have hc' : (Sm E Gl G).ok c := CtlOK.regime (Gl := Gl) (c := c) hc hsr.symm
    cases c with
    | suspended => exact hc.elim
    | _ =>
      exact fs_bind (fs_modifyTo (T := Sm E Gl G) (fun a a' ha =>
          StRel.unrelax ha hσ.wf (SR.unwindX hx hr hv hσ.stack ha.stack)) rfl)
        (fun _ _ _ => fs_throwT _ hc')
  · have hok' : (Sm E Gl G).ok (.return_ []) := CtlOK.regime (Gl := Gl) (c := .return_ []) hok hsr.symm
    exact fs_bind (fs_modifyTo (T := Sm E Gl G) (fun a a' ha =>
        StRel.unrelax ha hσ.wf (SR.unwindX hx hr hv hσ.stack ha.stack)) rfl)
      (fun _ _ _ => fs_throwTM hL hok')
  · refine fs_bind (fs_modifyTo (S := (Sm E Gl (Reserved.relax G ns')).atWin w) (T := (Sm E Gl G).atWin w)
      (fun a a' ⟨hf, ha, ho⟩ => ⟨hsr.free.mp hf, StRel.unrelax ha hσ.wf (SR.unwindX hx hr hv hσ.stack ha.stack),
        fun o hvo => ?_⟩) rfl) (fun _ _ _ => fs_throwW w)
    dsimp only
    rw [unwind_ne _ (fun nd hnd => ?_)]
    · exact ho o hvo
    · simp only [List.mem_map] at hnd
      obtain ⟨m, hm, rfl⟩ := hnd
      refine ⟨?_, (Reserved.vret_ok o hvo).2.2 m⟩
      rcases hx.mem m hm with hm | hl
      · exact hv m hm o hvo
      · rintro rfl; exact (Reserved.vret_ok _ hvo).1 (Reserved.loose_res _ _ hl)
  · exact fs_bind (fs_modifyTo (T := Sm E Gl G) (fun a a' ha =>
        StRel.unrelax ha hσ.wf (SR.unwindX hx hr hv hσ.stack ha.stack)) rfl) (fun _ _ _ => fs_pure hr')

theorem fs_wbsX {l l' : List StmtExprMd} (hn : LooseExt G (blockDeclarations l) (blockDeclarations l'))
    (hr : ∀ n ∈ blockDeclarations l, ¬ Reserved.res n) (hv : ∀ n ∈ blockDeclarations l, NotV n)
    {β : Type} {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β}
    (h : FS (Sm E Gl (Reserved.relax G (blockDeclarations l'))) A x y) :
    FS (Sm E Gl G) A (withBlockScope l x) (withBlockScope l' y) := by
  rw [withBlockScope_eq, withBlockScope_eq]
  cases hl' : (blockDeclarations l').isEmpty
  · cases hl : (blockDeclarations l).isEmpty
    · simp only [Bool.false_eq_true, ite_false]
      exact fs_wbsU hn hr hv h
    · simp only [Bool.false_eq_true, ite_false, ite_true]
      have e : blockDeclarations l = [] := List.isEmpty_iff.mp hl
      rw [e] at hn
      exact (fs_wbsU hn (fun _ h => by cases h) (fun _ h => by cases h) h).congrL (fun σ τ => (run_wbsU_nil x σ τ).symm)
  · have e' : blockDeclarations l' = [] := List.isEmpty_iff.mp hl'
    rw [e'] at hn h
    rw [hn.nil_right]
    exact fs_regime h (fun a a' ha => ha.relaxR []) (fun a a' ha => ha.ofRelaxNil) (sameRegime_relax G []).symm

omit [Reserved] in
theorem blockDeclarations_cons (s : StmtExprMd) (ss : List StmtExprMd) :
    blockDeclarations (s :: ss) = blockDeclarations [s] ++ blockDeclarations ss := by
  simp [blockDeclarations]

omit [Reserved] in
theorem L2.blockDeclarations {R : StmtExprMd → StmtExprMd → Prop} {l l' : List StmtExprMd} (h : L2 R l l')
    (hd : ∀ s t, R s t → blockDeclarations [s] = blockDeclarations [t]) :
    blockDeclarations l = blockDeclarations l' := by
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    have h1 := hd _ _ hab
    simp only [Interpreter.blockDeclarations, List.flatMap_cons, List.flatMap_nil, List.append_nil] at h1 ih ⊢
    rw [h1, ih]

/-- Reading the field `f` of a value `v` is simulated by reading the same field (`f = f'`), with equal
results. -/
theorem fs_readField (v : Value) (f f' : String) (hf : f = f') :
    FS (Sm E Gl G) Eq (readField v f : EvalM PM Value) (readField v f') := by
  subst hf
  unfold readField
  split
  · refine fs_bind fs_get (fun σ σ' hσ => ?_)
    have hσ : StRel G (IxRel E) σ σ' := hσ
    simp only [hσ.heap, hσ.inOld]
    split
    · split
      · exact fs_pure rfl
      · exact fs_evalError _ _
    · split
      · exact fs_evalError _ _
      · exact fs_fail _ _
  · refine fs_bind fs_get (fun σ σ' hσ => ?_)
    have hσ : StRel G (IxRel E) σ σ' := hσ
    simp only [hσ.heap, hσ.inOld, hσ.index.heapFields]
    split
    · split
      · split
        · exact fs_pure rfl
        · rw [hσ.index.defaultR (hσ.index.heapTy _ _ _ ‹_›)]
          exact fs_pure rfl
      · split
        · exact fs_pure rfl
        · exact fs_evalError _ _
    · split
      · exact fs_evalError _ _
      · exact fs_fail _ _
  · exact fs_evalError _ _

theorem fs_allocateObject : FS (Sm E Gl G) Eq (allocateObject : EvalM PM Value) allocateObject := by
  unfold allocateObject
  refine fs_bind fs_get (fun σ σ' hσ => ?_)
  have hσ : StRel G (IxRel E) σ σ' := hσ
  rw [hσ.heap]
  exact fs_bind (fs_modifyRel (fun a a' ha => by strel ha)) (fun _ _ _ => fs_pure rfl)

/-- Writing the value `x` to the field `f` of `v` is simulated by writing it to the same field
(`f = f'`); the states stay related. -/
theorem fs_writeField (v : Value) (f f' : String) (hf : f = f') (x : Value) :
    FS (Sm E Gl G) Eq (writeField v f x : EvalM PM Unit) (writeField v f' x) := by
  subst hf
  unfold writeField
  split
  · refine fs_bind fs_get (fun σ σ' hσ => ?_)
    have hσ : StRel G (IxRel E) σ σ' := hσ
    simp only [hσ.heap]
    split
    · exact fs_modifyRel (fun a a' ha => by strel ha)
    · exact fs_fail _ _
  · refine fs_bind fs_get (fun σ σ' hσ => ?_)
    have hσ : StRel G (IxRel E) σ σ' := hσ
    simp only [hσ.heap, hσ.index.heapFields]
    split
    · exact fs_modifyRel (fun a a' ha => by strel ha)
    · exact fs_fail _ _
  · exact fs_fail _ _

/-- Assigning `v` to the local `n` is simulated by assigning it to a local `n'` with the same name text,
provided the name is not reserved and is not the pass's valued-return output (`NotV`). -/
theorem fs_assignLocal (n n' : Identifier) (hn : n.text = n'.text) (hr : ¬ Reserved.res n.text) (hv : NotV n.text)
    (v : Value) : FS (Sm E Gl G) Eq (assignLocal n v : EvalM PM Unit) (assignLocal n' v) := by
  unfold assignLocal
  refine fs_modifyRel (fun a a' ha => ?_)
  rw [← hn, ha.stack.contains hr (.inl hv), ha.globals.contains hr]
  split
  · strel ha
  · split
    · rename_i hc
      have hk1 := gk_insert ha.gk hc v
      have hk2 := gk_insert ha.gk' (by rw [ha.globals.contains hr]; exact hc) v
      have hs := ha.stack.gs_insert hr v
      strel ha
    · strel ha

theorem fs_missingPrelude (name : String) (args : List Value) :
    FS (Sm E Gl G) Eq (missingPrelude name args : EvalM PM Unit) (missingPrelude name args) := by
  unfold missingPrelude
  split
  · exact fs_evalError _ _
  · exact fs_pure rfl

theorem procsNamed_isEmpty_congr {ix ix' : ProgramIndex} (h : IxRel E ix ix') (op : Operation)
    (hop : ¬ Reserved.resProc op.procName) :
    (ix'.procsNamed[op.procName]?.getD []).isEmpty = (ix.procsNamed[op.procName]?.getD []).isEmpty := by
  have hl := (h.procsNamed _ hop).length_eq
  revert hl
  cases ix.procsNamed[op.procName]?.getD [] <;> cases ix'.procsNamed[op.procName]?.getD [] <;> simp

theorem fs_noFitPrelude {ix ix' : ProgramIndex} (h : IxRel E ix ix') (op : Operation)
    (hop : ¬ Reserved.resProc op.procName) (args : List Value) :
    FS (Sm E Gl G) Eq (noFitPrelude ix op args : EvalM PM Unit) (noFitPrelude ix' op args) := by
  unfold noFitPrelude
  rw [procsNamed_isEmpty_congr h op hop]
  exact fs_ite (fun _ => fs_missingPrelude _ _) (fun _ => fs_stuckError _ _)

omit [Reserved] in
theorem lookupCallee_of_byId {ix : ProgramIndex} {c : Identifier} {P : Procedure}
    (h : c.uniqueId.bind ix.procsById.get? = some P) : lookupCallee ix c = some P := by
  simp only [lookupCallee, h]
  rfl

theorem IxRel.method {ix ix' : ProgramIndex} (h : IxRel E ix ix') (hrm : ¬ Reserved.resMethods) (tn name : String)
    (hn : ¬ Reserved.resProc name) :
    ORel (ProcRel E) (Interpreter.methodOf ix tn name) (Interpreter.methodOf ix' tn name) := by
  unfold Interpreter.methodOf
  have hm := fun t => h.methods hrm t name hn
  have key : ∀ (t : String), (ix.methods[t]? >>= fun (m : Std.HashMap String Procedure) => m[name]?).isSome =
      (ix'.methods[t]? >>= fun (m : Std.HashMap String Procedure) => m[name]?).isSome := by
    intro t
    have := hm t
    revert this
    cases (ix.methods[t]? >>= fun (m : Std.HashMap String Procedure) => m[name]?) <;>
      cases (ix'.methods[t]? >>= fun (m : Std.HashMap String Procedure) => m[name]?) <;>
      simp [ORel]
  simp only [h.ancestors, key]
  generalize List.find? _ _ = md
  cases md with
  | none => trivial
  | some t => exact hm t

theorem fs_methodOf_match {ix ix' : ProgramIndex} (h : IxRel E ix ix') (hrm : ¬ Reserved.resMethods) (tn name : String)
    (hn : ¬ Reserved.resProc name) (msg msg' : String) :
    FS (Sm E Gl G) (ProcRel E)
      (match Interpreter.methodOf ix tn name with
        | some p => pure p
        | none => (stuckError msg : EvalM PM Procedure))
      (match Interpreter.methodOf ix' tn name with
        | some p => pure p
        | none => stuckError msg') := by
  have := h.method hrm tn name hn
  revert this
  cases Interpreter.methodOf ix tn name <;> cases Interpreter.methodOf ix' tn name <;>
    simp only [ORel, false_implies, true_implies]
  · exact fs_stuckError _ _
  · exact fun h => fs_pure h

/-- Looking up the method `name` on a value `v` is simulated by looking up the same name, and the two
procedures found are related by `ProcRel E`. The name must not be a reserved procedure name and the
pass must not reserve methods (`Reserved.resMethods`). -/
theorem fs_resolveMethod (v : Value) (name name' : String) (hn : name = name') (hr : ¬ Reserved.resProc name)
    (hrm : ¬ Reserved.resMethods) :
    FS (Sm E Gl G) (ProcRel E) (resolveMethod v name : EvalM PM Procedure) (resolveMethod v name') := by
  subst hn
  unfold resolveMethod
  split
  · refine fs_bind fs_get (fun σ σ' hσ => ?_)
    have hσ : StRel G (IxRel E) σ σ' := hσ
    exact fs_methodOf_match hσ.index hrm _ _ hr _ _
  · exact fs_stuckError _ _

omit [Reserved] in
theorem isOverrideOf_congr {s s' a a' : Procedure} (hs : s.name.text = s'.name.text) (hsi : s.inputs = s'.inputs)
    (ha : a.name.text = a'.name.text) (hai : a.inputs = a'.inputs) : isOverrideOf s a = isOverrideOf s' a' := by
  simp only [isOverrideOf, sameNonSelfSignature, hs, hsi, ha, hai]

theorem IxRel.overrideOf {ix ix' : ProgramIndex} (h : IxRel E ix ix') (hrm : ¬ Reserved.resMethods) (tn : String)
    {s s' : Procedure} (hs : s.name.text = s'.name.text) (hsi : s.inputs = s'.inputs) :
    ORel (ProcRel E) (Interpreter.overrideOf ix tn s) (Interpreter.overrideOf ix' tn s') := by
  unfold Interpreter.overrideOf
  have hd : ∀ (t : String), ORel (fun P P' => ProcRel E P P' ∧ P.name.text = P'.name.text ∧ P.inputs = P'.inputs)
      ((ix.methodLists[t]?.getD []).find? (isOverrideOf s ·)) ((ix'.methodLists[t]?.getD []).find? (isOverrideOf s' ·)) :=
    fun t => (h.methodLists hrm t).find? (fun a b hab => isOverrideOf_congr hs hsi hab.2.1 hab.2.2)
  have key : ∀ (t : String), ((ix.methodLists[t]?.getD []).find? (isOverrideOf s ·)).isSome =
      ((ix'.methodLists[t]?.getD []).find? (isOverrideOf s' ·)).isSome := by
    intro t
    have := hd t
    revert this
    cases ((ix.methodLists[t]?.getD []).find? (isOverrideOf s ·)) <;>
      cases ((ix'.methodLists[t]?.getD []).find? (isOverrideOf s' ·)) <;> simp [ORel]
  simp only [h.ancestors, key]
  generalize List.find? _ _ = md
  cases md with
  | none => trivial
  | some t =>
    have := hd t
    dsimp only [bind, Option.bind]
    revert this
    cases ((ix.methodLists[t]?.getD []).find? (isOverrideOf s ·)) <;>
      cases ((ix'.methodLists[t]?.getD []).find? (isOverrideOf s' ·)) <;> simp only [ORel]
    all_goals first | exact fun _ => trivial | exact id | exact fun h => h.1

theorem fs_resolveOverride (v : Value) (id : Nat) {s s' : Procedure} (hs : s.name.text = s'.name.text)
    (hsi : s.inputs = s'.inputs) (hrm : ¬ Reserved.resMethods) :
    FS (Sm E Gl G) (ProcRel E) (resolveOverride v id s : EvalM PM Procedure) (resolveOverride v id s') := by
  unfold resolveOverride
  split
  · refine fs_bind fs_get (fun σ σ' hσ => ?_)
    have hσ : StRel G (IxRel E) σ σ' := hσ
    simp only [hσ.index.methodOwner hrm, hσ.index.ancestors]
    have tail : ∀ (tn : String), FS (Sm E Gl G) (ProcRel E)
        (match Interpreter.overrideOf σ.index tn s with
          | some proc => pure proc
          | none => (stuckError s!"no override of '{s.name.text}' on {tn}" : EvalM PM Procedure))
        (match Interpreter.overrideOf σ'.index tn s' with
          | some proc => pure proc
          | none => stuckError s!"no override of '{s'.name.text}' on {tn}") := by
      intro tn
      have := hσ.index.overrideOf hrm tn hs hsi
      revert this
      cases Interpreter.overrideOf σ.index tn s <;> cases Interpreter.overrideOf σ'.index tn s' <;>
        simp only [ORel, false_implies, true_implies]
      · exact fs_stuckError _ _
      · exact fun h => fs_pure h
    split
    · refine fs_ite (fun _ => tail _)
        (fun _ => fs_bind (fs_stuckError (A := fun _ _ => True) _ _) (fun _ _ _ => tail _))
    · exact fs_stuckError _ _
  · exact fs_stuckError _ _

theorem fs_coroInstance (v : Value) (w w' : String) :
    FS (Sm E Gl G) Eq (coroInstance v w : EvalM PM (Nat × CoroState)) (coroInstance v w') := by
  unfold coroInstance
  split
  · refine fs_bind fs_get (fun σ σ' hσ => ?_)
    have hσ : StRel G (IxRel E) σ σ' := hσ
    rw [hσ.coros]
    split
    · exact fs_pure rfl
    · exact fs_evalError _ _
  · exact fs_evalError _ _

theorem ProcRel.ofV (hvn : Reserved.vret = none) {P P' : Procedure} (name : P.name = P'.name ∨ RenProc P P')
    (inputs : L2 ParamR P.inputs P'.inputs) (outputs : L2 ParamR P.outputs P'.outputs)
    (pre : L2 (CondRel E) P.preconditions P'.preconditions) (coro : P.is_coroutine = false)
    (coro' : P'.is_coroutine = false) (body : BodyRel E P.outputs P.body P'.body)
    (writes : P.writesGlobals = P'.writesGlobals) (throws : P.throwsType = P'.throwsType)
    (outNames : ∀ x ∈ P.outputs, ¬ Reserved.res x.name.text)
    (inNames : ∀ x ∈ P.inputs, ¬ Reserved.res x.name.text)
    (frames : L2 (GroupRel E) (procFrames P) (procFrames P'))
    (hk : ∀ G e, Reserved.nodeOK G e := by intros; trivial)
    (inouts : ∀ o ∈ P.outputs, P.inputs.any (·.name.text == o.name.text) = true → Reserved.inoutOK o.name.text := by
      intros; trivial)
    (throwsTy : ∀ t, P.throwsType = some t → Reserved.tyR t.val t.val := by intros; rfl) : ProcRel E P P' :=
  { name, inputs, outputs, pre, coro, coro', body, writes, throws, throwsTy, outNames, inNames, frames, inouts
    inV := fun _ _ => notV_none hvn _
    outV := fun _ _ => .inl (notV_none hvn _)
    preOK := fun _ _ => ovOK_none hvn _ _ hk
    postOK := fun _ _ => ovOK_none hvn _ _ hk
    bodyOK := fun _ _ => ovOK_none hvn _ _ hk
    nc := fun h => by rw [valued_none hvn] at h; cases h }

end Helpers

end Strata.Laurel.PassSemantics
