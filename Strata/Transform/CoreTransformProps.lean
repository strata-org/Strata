/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemanticsProps
public import Strata.Transform.CoreTransform
import all Strata.Transform.CoreTransform
import all Strata.Languages.Core.CoreGen
public import Strata.Languages.Core.CoreGenProps

public section

/-! # Transformation-generic store helpers

Small, transformation-agnostic store lemmas shared across the
structured-to-unstructured passes (`projectStore_undef_at`).  They depend only on
the base statement semantics, so they sit below every pass-specific correctness
proof. -/


namespace Imperative

variable {P : PureExpr}

/-! ## Store helpers -/

/-- `projectStore` reverts to `none` on parent-undefined keys. -/
theorem projectStore_undef_at {P : PureExpr}
    {σ_parent σ_inner : SemanticStore P} {x : P.Ident}
    (h : σ_parent x = none) :
    projectStore σ_parent σ_inner x = none := by
  unfold projectStore
  simp [h]

end Imperative

/-! # Core Transform — Theorems

Properties of the per-call-site opaque types of `freshenTypeArgsSubst` in
`Strata.Transform.CoreTransform`, and of the successful runs of the generic runners
(`Post m Q`: every successful run of `m` returns a value satisfying `Q`; `PostGen P m Q`: every
successful run of `m` from a generator state satisfying `P` ends with a value and a generator
state satisfying `Q`). Key results:

- `runProgram_post` — `runProgram f p` replaces each structured procedure body by the result
  of a run of `runStmtsRec f` on it when that run reports a change, keeps a CFG body when its
  rewrite reports no change (`DeclStep`, `runCFGCmds_keep`), and reports a
  change exactly when one of these runs does.
- `runProgramUntil_post` — `runProgramUntil f p (some n)` keeps any invariant that each pass
  keeps, and returns a program of measure zero when the measure of `p` is below `n` and each
  pass lowers the measure when it reports a change and returns measure zero otherwise.
- `runProgram_postGen`, `runProgramUntil_postGen` — the same, following the generator state,
  so that a transformation can show that the names it draws in different passes differ; the
  two results above are their instances.

- `freshenTypeArgsSubst_fresh` — every type in the substitution's range is a
  nullary type constant with a fresh `<prefix>_<n>` name, present in the output
  generator state and absent from the input's.
- `freshenTypeArgsSubst_disjoint` — two successive call sites draw disjoint
  ranges, so facts about one call's types say nothing about another's.
- `freshenTypeArgsSubst_empty` — monomorphic callees (`typeArgs = []`) yield
  `Subst.empty` without touching the generator.

The theorems are generic in the prefix string; call elimination and procedure
inlining instantiate it with `Core.CallElim.callElimTyPrefix` and
`Core.ProcedureInlining.inlineTyPrefix`.
The counter does not ingest existing program identifiers, so both passes give the
generator the program's type names that start with the prefix, and a drawn name
among them is drawn again.
-/


namespace Core
namespace Transform

/-! ## Monad plumbing for `CoreTransformM`

`CoreTransformM = ExceptT Err (StateM CoreTransformState)`, so a computation
applied to a state `σ` returns an `(Except Err _) × CoreTransformState` pair.
The lemmas here expose the facts about `pure`, `throw`, `>>=`, and `Except.ok`
pair equalities that transform-correctness proofs need — letting them treat the
effectful sub-computations (`genLiftVar`, `mapM`, `capturedVars`, …) as opaque. -/

/-- Running `pure v` from state `σ` yields `.ok v` with `σ` unchanged. -/
theorem pure_apply {α : Type} (v : α) (σ : CoreTransformState) :
    (pure v : CoreTransformM α) σ = (Except.ok v, σ) := rfl

/-- Running `throw e` from state `σ` yields `.error e` with `σ` unchanged. -/
theorem throw_apply {α : Type} (e : Err) (σ : CoreTransformState) :
    (throw e : CoreTransformM α) σ = (Except.error e, σ) := rfl

/-- Inversion for a successful `>>=` run: if `(x >>= k) σ` returns `.ok b`, then
`x` first ran to some `.ok a` at an intermediate state `σ2`, and `k a` ran from
`σ2` to `.ok b`. -/
theorem bind_ok_inv {α β : Type} (x : CoreTransformM α) (k : α → CoreTransformM β)
    {σ σ' : CoreTransformState} {b : β}
    (h : (x >>= k) σ = (Except.ok b, σ')) :
    ∃ a σ2, x σ = (Except.ok a, σ2) ∧ k a σ2 = (Except.ok b, σ') := by
  rcases hx : x σ with ⟨r, σ2⟩
  cases r with
  | ok a =>
    refine ⟨a, σ2, rfl, ?_⟩
    have hred : (x >>= k) σ = k a σ2 := by
      simp only [bind, ExceptT.bind, ExceptT.mk, StateT.bind, ExceptT.bindCont, hx]
    rw [hred] at h; exact h
  | error e =>
    exfalso
    have hred : (x >>= k) σ = (Except.error e, σ2) := by
      simp only [bind, ExceptT.bind, ExceptT.mk, StateT.bind, ExceptT.bindCont, hx, pure, StateT.pure]
    rw [hred] at h
    injection h with he _
    nomatch he

/-- Injectivity of `(Except.ok _, _)` pairs: from
`(Except.ok a, s) = (Except.ok b, t)` recover `a = b ∧ s = t`. -/
theorem ok_pair_inj {ε α σT : Type} {a b : α} {s t : σT}
    (h : ((@Except.ok ε α a), s) = (Except.ok b, t)) : a = b ∧ s = t := by
  simp only [Prod.mk.injEq, Except.ok.injEq] at h
  exact h

/-! ## Successful runs

`Post m Q` says that every successful run of `m`, from any state, returns a value satisfying
`Q`.  It ignores the state, so a property of the values a statement-level transformation
returns carries through `runStmtsRec`, `runProgram` and `runProgramUntil` (`runProgram_post`,
`runProgramUntil_post`). -/

/-- Every successful run of `m`, from any state, returns a value satisfying `Q`. -/
@[expose] def Post {α : Type} (m : CoreTransformM α) (Q : α → Prop) : Prop :=
  ∀ σ a σ', m σ = (Except.ok a, σ') → Q a

/-- A run of `pure a` returns `a`. -/
theorem Post.pure {α : Type} {a : α} {Q : α → Prop} (h : Q a) :
    Post (Pure.pure a : CoreTransformM α) Q :=
  fun _ _ _ hr => (ok_pair_inj hr).1 ▸ h

/-- A failing computation has no successful run. -/
theorem Post.throw {α : Type} {e : Err} {Q : α → Prop} :
    Post (MonadExcept.throw e : CoreTransformM α) Q :=
  fun σ _ _ hr => by rw [throw_apply] at hr; cases hr

/-- Every successful run returns a value satisfying `True`. -/
theorem Post.true {α : Type} (m : CoreTransformM α) : Post m fun _ => True :=
  fun _ _ _ _ => trivial

/-- A run of `x >>= f` returns a value with `Q` when `x` returns values with `Q₁` and `f` maps
    each such value to a computation returning values with `Q`. -/
theorem Post.bind {α β : Type} {x : CoreTransformM α} {f : α → CoreTransformM β}
    {Q₁ : α → Prop} {Q : β → Prop} (hx : Post x Q₁) (hf : ∀ a, Q₁ a → Post (f a) Q) :
    Post (x >>= f) Q := fun _ _ _ h =>
  have ⟨a, _, ha, hk⟩ := bind_ok_inv x f h
  hf a (hx _ _ _ ha) _ _ _ hk

/-- A computation returning values with `Q` returns values with any weaker property. -/
theorem Post.mono {α : Type} {m : CoreTransformM α} {Q Q' : α → Prop} (h : Post m Q)
    (himp : ∀ a, Q a → Q' a) : Post m Q' :=
  fun _ _ _ hr => himp _ (h _ _ _ hr)

/-- A `for` loop over `l` returns a value with `Q` when its state satisfies `I rest` before the
    elements `rest` remain, each step from such a state yields one satisfying `I` on the
    remaining elements or stops with one satisfying `Q`, and `I []` implies `Q`. -/
theorem Post.forIn {α β : Type} {I : List α → β → Prop} {Q : β → Prop}
    {f : α → β → CoreTransformM (ForInStep β)} (hend : ∀ b, I [] b → Q b)
    (hstep : ∀ x rest b, I (x :: rest) b → Post (f x b) fun
      | .yield b' => I rest b'
      | .done b' => Q b') :
    ∀ (l : List α) (b : β), I l b → Post (forIn l b f) Q
  | [], _, hb => (List.forIn_nil (m := CoreTransformM)).symm ▸ Post.pure (hend _ hb)
  | x :: l, b, hb => (List.forIn_cons f x l b).symm ▸ Post.bind (hstep x l b hb) fun
    | .done _, hc => Post.pure hc
    | .yield c, hc => Post.forIn hend hstep l c hc

/-! ## Successful runs and the generator state

`PostGen P m Q` says that every successful run of `m` from a state whose generator state
satisfies `P` returns a value `a` in a state whose generator state `γ'` satisfies `Q a γ'`.
`Post m Q` is its instance ignoring the generator (`Post.of_postGen`).  Tracking the generator
lets a transformation show that the names it draws in different runs differ. -/

/-- Every successful run of `m` from a state whose generator state satisfies `P` returns a value
    `a` in a state whose generator state `γ'` satisfies `Q a γ'`. -/
@[expose] def PostGen {α : Type} (P : CoreGenState → Prop) (m : CoreTransformM α)
    (Q : α → CoreGenState → Prop) : Prop :=
  ∀ σ a σ', P σ.genState → m σ = (Except.ok a, σ') → Q a σ'.genState

/-- A run of `pure a` returns `a` in the generator state it starts in. -/
theorem PostGen.pure {α : Type} {a : α} {P : CoreGenState → Prop} {Q : α → CoreGenState → Prop}
    (h : ∀ γ, P γ → Q a γ) : PostGen P (Pure.pure a : CoreTransformM α) Q :=
  fun _ _ _ hP hr => by obtain ⟨rfl, rfl⟩ := ok_pair_inj hr; exact h _ hP

/-- A failing computation has no successful run. -/
theorem PostGen.throw {α : Type} {e : Err} {P : CoreGenState → Prop}
    {Q : α → CoreGenState → Prop} : PostGen P (MonadExcept.throw e : CoreTransformM α) Q :=
  fun σ _ _ _ hr => by rw [throw_apply] at hr; cases hr

/-- A run of `x >>= f` ends with `Q` when `x` ends with `Q₁ a` and `f a` runs from there to
    `Q`. -/
theorem PostGen.bind {α β : Type} {x : CoreTransformM α} {f : α → CoreTransformM β}
    {P : CoreGenState → Prop} {Q₁ : α → CoreGenState → Prop} {Q : β → CoreGenState → Prop}
    (hx : PostGen P x Q₁) (hf : ∀ a, PostGen (Q₁ a) (f a) Q) : PostGen P (x >>= f) Q :=
  fun _ _ _ hP h =>
    have ⟨a, _, ha, hk⟩ := bind_ok_inv x f h
    hf a _ _ _ (hx _ _ _ hP ha) hk

/-- Strengthening the precondition and weakening the postcondition. -/
theorem PostGen.mono {α : Type} {m : CoreTransformM α} {P P' : CoreGenState → Prop}
    {Q Q' : α → CoreGenState → Prop} (h : PostGen P m Q) (hP : ∀ γ, P' γ → P γ)
    (hQ : ∀ a γ, Q a γ → Q' a γ) : PostGen P' m Q' :=
  fun _ _ _ hP' hr => hQ _ _ (h _ _ _ (hP _ hP') hr)

/-- A computation runs from every generator state satisfying `P` to `Q` when it does from each
    such state `γ`, fixed. -/
theorem PostGen.of_forall {α : Type} {m : CoreTransformM α} {P : CoreGenState → Prop}
    {Q : α → CoreGenState → Prop} (h : ∀ γ, P γ → PostGen (· = γ) m Q) : PostGen P m Q :=
  fun _ _ _ hP hr => h _ hP _ _ _ rfl hr

/-- A change of the state that keeps the generator state keeps it. -/
theorem PostGen.modify {g : CoreTransformState → CoreTransformState}
    (hg : ∀ σ, (g σ).genState = σ.genState) {P : CoreGenState → Prop}
    {Q : Unit → CoreGenState → Prop} (h : ∀ γ, P γ → Q () γ) :
    PostGen P (modify g : CoreTransformM Unit) Q :=
  fun σ _ _ hP hr => by
    obtain ⟨rfl, rfl⟩ := ok_pair_inj (show (Except.ok (), g σ) = _ from hr)
    rw [hg]
    exact h _ hP

/-- A `for` loop over `l` ends with `Q` when it starts from a generator state satisfying
    `I l b`, each step from a state satisfying `I` on the elements left either continues to one
    satisfying `I` on the remaining elements or stops with `Q`, and `I []` implies `Q`. -/
theorem PostGen.forIn {α β : Type} {I : List α → β → CoreGenState → Prop}
    {Q : β → CoreGenState → Prop} {f : α → β → CoreTransformM (ForInStep β)}
    (hend : ∀ b γ, I [] b γ → Q b γ)
    (hstep : ∀ x rest b, PostGen (I (x :: rest) b) (f x b) fun r γ => match r with
      | .yield b' => I rest b' γ
      | .done b' => Q b' γ) :
    ∀ (l : List α) (b : β), PostGen (I l b) (forIn l b f) Q
  | [], _ => (List.forIn_nil (m := CoreTransformM)).symm ▸ PostGen.pure (hend _)
  | x :: l, b => (List.forIn_cons f x l b).symm ▸ PostGen.bind (hstep x l b) fun
    | .done _ => PostGen.pure fun _ h => h
    | .yield c => PostGen.forIn hend hstep l c

/-- A computation's successful runs from every state satisfy `Q` when they do from every
    generator state. -/
theorem Post.of_postGen {α : Type} {m : CoreTransformM α} {Q : α → Prop}
    (h : PostGen (fun _ => True) m fun a _ => Q a) : Post m Q :=
  fun σ a σ' hr => h σ a σ' trivial hr

/-- A computation whose successful runs satisfy `Q` runs from every generator state to `Q`. -/
theorem Post.postGen {α : Type} {m : CoreTransformM α} {Q : α → Prop} (h : Post m Q)
    (P : CoreGenState → Prop) : PostGen P m fun a _ => Q a :=
  fun σ a σ' _ hr => h σ a σ' hr

/-- A run of `runStmtsRecTyped` whose step ignores the variable types does not depend on the
    variable types it starts from. -/
private theorem runStmtsRecTyped_const (f : Statement → CoreTransformM (Option (List Statement)))
    (vt vt' : TypeSpec.TypeScopes) (ss : List Statement) :
    runStmtsRecTyped (fun _ => f) vt ss = runStmtsRecTyped (fun _ => f) vt' ss := by
  induction vt, ss using runStmtsRecTyped.induct generalizing vt' with
  | case1 vt => simp only [runStmtsRecTyped]
  | case2 vt s ss' hsub htail =>
    have htail' : ∀ sres, runStmtsRecTyped (fun _ => f) (vt.addInits sres) ss' =
        runStmtsRecTyped (fun _ => f) (vt'.addInits sres) ss' := fun sres => htail sres _
    cases s with
    | cmd c => simp only [runStmtsRecTyped, htail']
    | block lbl b md =>
      have hb : ∀ v, runStmtsRecTyped (fun _ => f) (vt.push .empty) b =
          runStmtsRecTyped (fun _ => f) v b := hsub
      simp only [runStmtsRecTyped, htail', hb (vt'.push .empty)]
    | ite c thenb elseb md =>
      have ht : ∀ v, runStmtsRecTyped (fun _ => f) (vt.push .empty) thenb =
          runStmtsRecTyped (fun _ => f) v thenb := hsub.1
      have he : ∀ v, runStmtsRecTyped (fun _ => f) (vt.push .empty) elseb =
          runStmtsRecTyped (fun _ => f) v elseb := hsub.2
      simp only [runStmtsRecTyped, htail', ht (vt'.push .empty), he (vt'.push .empty)]
    | loop guard measure invariant body md =>
      have hb : ∀ v, runStmtsRecTyped (fun _ => f) (vt.push .empty) body =
          runStmtsRecTyped (fun _ => f) v body := hsub
      simp only [runStmtsRecTyped, htail', hb (vt'.push .empty)]
    | typeDecl tc md => simp only [runStmtsRecTyped, htail']
    | exit label md => simp only [runStmtsRecTyped, htail']

/-- A run of `runStmtsRecTyped` whose step ignores the variable types is `runStmtsRec`. -/
private theorem runStmtsRecTyped_eq_runStmtsRec
    (f : Statement → CoreTransformM (Option (List Statement))) (vt : TypeSpec.TypeScopes)
    (ss : List Statement) : runStmtsRecTyped (fun _ => f) vt ss = runStmtsRec f ss :=
  runStmtsRecTyped_const f vt [] ss

/-- `runStmtsRec f` unfolds as a recursion over the statement list: it runs `f` on each
    statement and, where `f` declines, on the statement's bodies. -/
theorem runStmtsRec_eq (f : Statement → CoreTransformM (Option (List Statement)))
    (ss : List Statement) :
    runStmtsRec f ss = (do
      match ss with
      | [] => return (false, [])
      | s :: ss' =>
        let (changed, sres) ← (do
          match ← f s with
          | .some s' => return (true, s')
          | .none =>
            match s with
            | .cmd _ => return (false, [s])
            | .block lbl b md => do
              let (changed, b') ← runStmtsRec f b
              return (changed, [.block lbl b' md])
            | .ite c thenb elseb md => do
              let (changed, thenb') ← runStmtsRec f thenb
              let (changed', elseb') ← runStmtsRec f elseb
              return (changed || changed', [.ite c thenb' elseb' md])
            | .loop guard measure invariant body md => do
              let (changed, body') ← runStmtsRec f body
              return (changed, [.loop guard measure invariant body' md])
            | .typeDecl _ _ => return (false, [s])
            | .exit _ _ => return (false, [s]))
        let (changed0, ss'') ← runStmtsRec f ss'
        return ⟨changed || changed0, sres ++ ss''⟩ : CoreTransformM (Bool × List Statement)) := by
  show runStmtsRecTyped (fun _ => f) [] ss = _
  rw [runStmtsRecTyped.eq_def]
  cases ss with
  | nil => rfl
  | cons s ss' =>
    simp only [runStmtsRecTyped_eq_runStmtsRec]
    rfl

/-- `runCFGCmdsTyped` with a step that ignores the variable types does not depend on them. -/
theorem runCFGCmdsTyped_const (f : Command → CoreTransformM (Option (List Command)))
    (vt : TypeSpec.TypeScopes) (g : DetCFG) :
    runCFGCmdsTyped (fun _ => f) vt g = runCFGCmds f g := by
  simp only [runCFGCmds, runCFGCmdsTyped]

/-- `runCFGCmds` with a rewrite that changes no command reports no change and keeps the
    generator state. -/
theorem runCFGCmds_keep (g : DetCFG) (γ : CoreGenState) :
    PostGen (· = γ) (runCFGCmds (fun _ => pure none) g) fun r γ' => r.1 = false ∧ γ' = γ := by
  -- A fold whose step keeps the first component keeps it.
  have hfold : ∀ {α δ : Type} (F : Bool × δ → α → Bool × δ), (∀ b a, (F b a).1 = b.1) →
      ∀ (l : List α) (b : Bool × δ), (l.foldl F b).1 = b.1 := by
    intro α δ F hF l
    induction l with
    | nil => intro; rfl
    | cons x _ ih => intro b; rw [List.foldl_cons, ih, hF]
  intro σ a σ' hP hr
  unfold runCFGCmds runCFGCmdsTyped at hr
  simp only [pure_bind, bind_pure_comp, map_pure, List.forIn_pure_yield_eq_foldl] at hr
  obtain ⟨rfl, rfl⟩ := ok_pair_inj hr
  refine ⟨?_, hP⟩
  dsimp only
  rw [hfold]
  intro b _
  dsimp only
  rw [hfold]
  intros; rfl

/-- `r` is what `runProgram` makes of the declaration `d`, with its change flag, when every
    successful run of `runStmtsRec` on a list `ss` returning `(c, ss')` satisfies
    `Q ss (c, ss')` and the rewrite of CFG bodies reports no change: a procedure with a
    structured body `ss` gets the body `ss'` when `c` is set and is kept otherwise; a procedure
    with a CFG body and any other declaration are kept, with no change. -/
@[expose] def DeclStep (Q : Statements → Bool × Statements → Prop) (d : Decl)
    (r : Bool × Decl) : Prop :=
  match d with
  | .proc proc md => (∃ ss ss', proc.body = .structured ss ∧ Q ss (r.1, ss') ∧
      r.2 = if r.1 then .proc { proc with body := .structured ss' } md else .proc proc md) ∨
    (∃ g, proc.body = .cfg g ∧ r = (false, d))
  | _ => r = (false, d)

/-- **What `runProgram` does to each declaration, tracking the generator state.**  Let `le` be
    a preorder on generator states, and let every successful run of `runStmtsRec f` on a list
    `ss` from a generator state `γ` end in a generator state `γ'` with `le γ γ'` and return a
    value `r` with `Q ss γ r γ'`, a property kept by any wider pair of generator states.  Let
    the rewrites of CFG bodies, `cfgCmd` (per command) and `cfgBody` (whole graph), when there
    are any, report no change and keep the generator state.  A successful run of
    `runProgram f p` from `γ₀` ends in some `γ₁` with `le γ₀ γ₁`, and returns the program of the
    declarations `rs` makes of those of `p` (`DeclStep (Q · γ₀ · γ₁)`), reporting a change
    exactly when one of them does. -/
theorem runProgram_postGen {f : Statement → CoreTransformM (Option (List Statement))}
    {le : CoreGenState → CoreGenState → Prop} (hrefl : ∀ γ, le γ γ)
    (htrans : ∀ {γ₁ γ₂ γ₃}, le γ₁ γ₂ → le γ₂ γ₃ → le γ₁ γ₃)
    {Q : Statements → CoreGenState → Bool × Statements → CoreGenState → Prop}
    (hQ : ∀ {ss γ₀ γ r γ' γ₁}, le γ₀ γ → le γ' γ₁ → Q ss γ r γ' → Q ss γ₀ r γ₁)
    (hf : ∀ ss γ, PostGen (· = γ) (runStmtsRec f ss) fun r γ' => le γ γ' ∧ Q ss γ r γ')
    {cfgCmd : Option (Command → CoreTransformM (Option (List Command)))}
    (hcfg : ∀ h, cfgCmd = some h → ∀ g γ,
      PostGen (· = γ) (runCFGCmds h g) fun r γ' => r.1 = false ∧ γ' = γ)
    {cfgBody : Option (Procedure → DetCFG → CoreTransformM (Bool × DetCFG))}
    (hwhole : ∀ k, cfgBody = some k → ∀ proc g γ,
      PostGen (· = γ) (k proc g) fun r γ' => r.1 = false ∧ γ' = γ)
    (p : Program) (γ₀ : CoreGenState) :
    PostGen (· = γ₀) (runProgram f p (cfgCmd := cfgCmd) (cfgBody := cfgBody)) fun r γ₁ =>
      le γ₀ γ₁ ∧
      ∃ rs : List (Bool × Decl),
      List.Rel₂ (DeclStep fun ss r => Q ss γ₀ r γ₁) p.decls rs ∧ r.2.decls = rs.map (·.2) ∧
      r.1 = rs.any (·.1) := by
  -- The declarations made so far keep their property in a wider generator state.
  have hwiden : ∀ {γ γ'}, le γ γ' → ∀ {ds : List Decl} {rs : List (Bool × Decl)},
      List.Rel₂ (DeclStep fun ss r => Q ss γ₀ r γ) ds rs →
      List.Rel₂ (DeclStep fun ss r => Q ss γ₀ r γ') ds rs := fun hle _ _ h =>
    h.imp fun {d r} hd => by
      cases d
      case proc proc md =>
        rcases hd with ⟨ss, ss', hb, hq, hr⟩ | hd
        · exact .inl ⟨ss, ss', hb, hQ (hrefl _) hle hq, hr⟩
        · exact .inr hd
      all_goals exact hd
  unfold runProgram runProgramTyped
  refine PostGen.bind (PostGen.modify (Q := fun _ γ => γ = γ₀) (by intro; rfl) fun _ h => h)
    fun _ => ?_
  refine PostGen.bind (Q₁ := fun (s : Bool × List Decl) γ => le γ₀ γ ∧
      ∃ rs : List (Bool × Decl),
      List.Rel₂ (DeclStep fun ss r => Q ss γ₀ r γ) p.decls rs ∧ s.2 = rs.map (·.2) ∧
      s.1 = rs.any (·.1))
    ?_ fun s => ?_
  rotate_left
  · refine PostGen.bind (PostGen.modify (Q := fun _ γ => le γ₀ γ ∧ ∃ rs : List (Bool × Decl),
      List.Rel₂ (DeclStep fun ss r => Q ss γ₀ r γ) p.decls rs ∧ s.2 = rs.map (·.2) ∧
      s.1 = rs.any (·.1)) (by intro; rfl) fun _ h => h) fun _ => ?_
    exact PostGen.pure fun _ h => h
  refine PostGen.mono
    (PostGen.forIn (I := fun rest s γ => le γ₀ γ ∧ ∃ k rs, rest = p.decls.zipIdx.drop k ∧
      rs.length = k ∧ List.Rel₂ (DeclStep fun ss r => Q ss γ₀ r γ) (p.decls.take k) rs ∧
      s.2 = rs.map (·.2) ++ p.decls.drop k ∧ s.1 = rs.any (·.1)) ?_ ?_ _ _)
    (fun γ h => by subst h; exact ⟨hrefl _, 0, [], by simp, rfl, .nil, by simp, rfl⟩)
    (fun _ _ h => h)
  · rintro s γ ⟨hle, k, rs, hrest, -, hrel, h2, h1⟩
    have hk : p.decls.length ≤ k := by
      have := congrArg List.length hrest
      simp only [List.length_nil, List.length_drop, List.length_zipIdx] at this
      omega
    exact ⟨hle, rs, by rwa [List.take_of_length_le hk] at hrel,
      by rw [h2, List.drop_of_length_le hk, List.append_nil], h1⟩
  · intro x rest s
    refine PostGen.of_forall fun γ ⟨hle, k, rs, hrest, hlen, hrel, h2, h1⟩ => ?_
    have hk : k < p.decls.length := by
      have := congrArg List.length hrest
      simp only [List.length_cons, List.length_drop, List.length_zipIdx] at this
      omega
    rw [List.drop_eq_getElem_cons (by simpa using hk)] at hrest
    obtain ⟨rfl, rfl⟩ := List.cons.inj hrest
    simp only [List.getElem_zipIdx, Nat.zero_add]
    -- The declarations after this step.
    have hdrop : p.decls.drop k = p.decls[k] :: p.decls.drop (k + 1) :=
      List.drop_eq_getElem_cons hk
    have htake : p.decls.take (k + 1) = p.decls.take k ++ [p.decls[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
    have hnext : ∀ γ' (r : Bool × Decl), le γ γ' →
        DeclStep (fun ss r => Q ss γ₀ r γ') p.decls[k] r →
        ∃ k' rs', p.decls.zipIdx.drop (k + 1) = p.decls.zipIdx.drop k' ∧ rs'.length = k' ∧
          List.Rel₂ (DeclStep fun ss r => Q ss γ₀ r γ') (p.decls.take k') rs' ∧
          rs.map (·.2) ++ r.2 :: p.decls.drop (k + 1) = rs'.map (·.2) ++ p.decls.drop k' ∧
          (s.1 || r.1) = rs'.any (·.1) := fun γ' r hle' hr =>
      ⟨k + 1, rs ++ [r], rfl, by simp [hlen], htake ▸ (hwiden hle' hrel).append (.cons hr .nil),
        by simp, by simp [h1]⟩
    generalize hd : p.decls[k] = d at hnext hdrop
    cases d
    case proc proc md =>
      simp only [↓reduceIte]
      refine PostGen.bind (PostGen.modify (Q := fun _ γ' => γ' = γ) (by intro; rfl)
        fun _ h => h) fun _ => ?_
      split
      · rename_i ss hbody
        rw [runStmtsRecTyped_eq_runStmtsRec]
        refine PostGen.bind (hf ss γ) fun r => ?_
        obtain ⟨c, ss'⟩ := r
        refine PostGen.bind (PostGen.pure (Q := fun a γ' => a = (c, .structured ss') ∧
          le γ γ' ∧ Q ss γ (c, ss') γ') fun _ h => ⟨rfl, h⟩) fun a => ?_
        refine PostGen.of_forall fun γ' ⟨ha, hle', hq⟩ => ?_
        subst ha
        cases c
        · refine PostGen.pure fun γ₂ hγ => ?_
          subst hγ
          obtain ⟨k', rs', h₁, h₂, h₃, h₄, h₅⟩ := hnext γ₂ (false, .proc proc md) hle'
            (.inl ⟨ss, ss', hbody, hQ hle (hrefl _) hq, by simp⟩)
          exact ⟨htrans hle hle', k', rs', h₁, h₂, h₃, by rw [h2, hdrop]; exact h₄,
            by simpa using h₅⟩
        · refine PostGen.bind (PostGen.modify (Q := fun _ γ'' => γ'' = γ') (by intro; rfl)
            fun _ h => h) fun _ => PostGen.pure fun γ₂ hγ => ?_
          subst hγ
          have hset : s.2.set k (.proc { proc with body := .structured ss' } md) =
              rs.map (·.2) ++ .proc { proc with body := .structured ss' } md ::
                p.decls.drop (k + 1) := by
            rw [h2, hdrop, List.set_append_right _ _ (by simp [hlen])]
            simp [hlen]
          obtain ⟨k', rs', h₁, h₂, h₃, h₄, h₅⟩ :=
            hnext γ₂ (true, .proc { proc with body := .structured ss' } md) hle'
              (.inl ⟨ss, ss', hbody, hQ hle (hrefl _) hq, by simp⟩)
          exact ⟨htrans hle hle', k', rs', h₁, h₂, h₃, hset.trans h₄, by simpa using h₅⟩
      · -- A CFG body rewritten whole: the rewrite reports no change, so the declaration is
        -- kept.
        rename_i g k hbody'
        refine PostGen.bind (hwhole k rfl proc g γ) fun r => ?_
        obtain ⟨c, g'⟩ := r
        refine PostGen.bind (PostGen.pure (Q := fun a γ' => a = (c, .cfg g') ∧
          c = false ∧ γ' = γ) fun _ h => ⟨rfl, h⟩) fun a => ?_
        refine PostGen.of_forall fun γ' ⟨ha, hc, hγ'⟩ => ?_
        subst ha hc hγ'
        refine PostGen.pure fun γ₂ hγ => ?_
        subst hγ
        obtain ⟨k', rs', h₁, h₂, h₃, h₄, h₅⟩ :=
          hnext _ (false, .proc proc md) (hrefl _) (.inr ⟨g, hbody', rfl⟩)
        exact ⟨hle, k', rs', h₁, h₂, h₃, by rw [h2, hdrop]; exact h₄, by simpa using h₅⟩
      · exact PostGen.bind (Q₁ := fun _ _ => False) PostGen.throw fun _ _ _ _ h _ => h.elim
      · -- A CFG body: the rewrite reports no change, so the declaration is kept.
        rename_i g gf hbody hmap
        obtain ⟨h0, hc, rfl⟩ := Option.map_eq_some_iff.mp hmap
        rw [runCFGCmdsTyped_const]
        refine PostGen.bind (hcfg h0 hc g γ) fun r => ?_
        obtain ⟨c, g'⟩ := r
        refine PostGen.bind (PostGen.pure (Q := fun a γ' => a = (c, .cfg g') ∧
          c = false ∧ γ' = γ) fun _ h => ⟨rfl, h⟩) fun a => ?_
        refine PostGen.of_forall fun γ' ⟨ha, hc, hγ'⟩ => ?_
        subst ha hc hγ'
        refine PostGen.pure fun γ₂ hγ => ?_
        subst hγ
        obtain ⟨k', rs', h₁, h₂, h₃, h₄, h₅⟩ :=
          hnext _ (false, .proc proc md) (hrefl _) (.inr ⟨g, hbody, rfl⟩)
        exact ⟨hle, k', rs', h₁, h₂, h₃, by rw [h2, hdrop]; exact h₄, by simpa using h₅⟩
    all_goals
      refine PostGen.pure fun _ h => ?_
      rw [h]
      obtain ⟨k', rs', h₁, h₂, h₃, h₄, h₅⟩ := hnext γ (false, _) (hrefl _) rfl
      exact ⟨hle, k', rs', h₁, h₂, h₃, by rw [h2, hdrop]; exact h₄, by simpa using h₅⟩

/-- **What `runProgram` does to each declaration.**  When every successful run of
    `runStmtsRec f` on a list `ss` returns a value satisfying `Q ss`, and the rewrites of CFG
    bodies (`cfgCmd`, `cfgBody`), when there are any, report no change and keep the generator
    state, a successful run of `runProgram f p` (over every procedure) returns the program of the
    declarations `rs` makes of those of `p` (`DeclStep Q`), and reports a change exactly when one
    of them does. -/
theorem runProgram_post {f : Statement → CoreTransformM (Option (List Statement))}
    {Q : Statements → Bool × Statements → Prop} (hf : ∀ ss, Post (runStmtsRec f ss) (Q ss))
    {cfgCmd : Option (Command → CoreTransformM (Option (List Command)))}
    (hcfg : ∀ h, cfgCmd = some h → ∀ g γ,
      PostGen (· = γ) (runCFGCmds h g) fun r γ' => r.1 = false ∧ γ' = γ)
    {cfgBody : Option (Procedure → DetCFG → CoreTransformM (Bool × DetCFG))}
    (hwhole : ∀ k, cfgBody = some k → ∀ proc g γ,
      PostGen (· = γ) (k proc g) fun r γ' => r.1 = false ∧ γ' = γ)
    (p : Program) :
    Post (runProgram f p (cfgCmd := cfgCmd) (cfgBody := cfgBody)) fun r =>
      ∃ rs : List (Bool × Decl),
      List.Rel₂ (DeclStep Q) p.decls rs ∧ r.2.decls = rs.map (·.2) ∧ r.1 = rs.any (·.1) :=
  fun σ a σ' hr => (runProgram_postGen (le := fun _ _ => True) (Q := fun ss _ r _ => Q ss r)
    (fun _ => trivial) (fun _ _ => trivial) (fun _ _ h => h)
    (fun ss _ => ((hf ss).postGen _).mono (fun _ h => h) fun _ _ h => ⟨trivial, h⟩)
    hcfg hwhole p σ.genState σ a σ' rfl hr).2

/-- **Bounded iteration of a statement-level transformation reaches measure zero, tracking the
    generator state.**  Let every successful run of `runProgram f q` from a generator state with
    `Inv q` end in one with `Inv` of the program it returns, of smaller measure `μ` when it
    reports a change and of measure zero when it reports none.  Then every successful run of
    `runProgramUntil f p (some n)` from a generator state with `Inv p`, where `μ p < n`, ends in
    one with `Inv` of the program it returns, of measure zero. -/
theorem runProgramUntil_postGen {f : Statement → CoreTransformM (Option (List Statement))}
    {Inv : Program → CoreGenState → Prop} {μ : Program → Nat}
    {cfgCmd : Option (Command → CoreTransformM (Option (List Command)))}
    (hstep : ∀ q, PostGen (Inv q) (runProgram f q (cfgCmd := cfgCmd)) fun r γ =>
      Inv r.2 γ ∧ (r.1 = true → μ r.2 < μ q) ∧ (r.1 = false → μ r.2 = 0))
    {p : Program} {n : Nat} (hn : μ p < n) :
    PostGen (Inv p) (runProgramUntil f p (some n) (cfgCmd := cfgCmd)) fun r γ =>
      Inv r.2 γ ∧ μ r.2 = 0 := by
  simp only [runProgramUntil]
  refine PostGen.bind (Q₁ := fun s γ => Inv s.1 γ ∧ μ s.1 = 0) ?_ fun _ =>
    PostGen.pure fun _ h => h
  refine PostGen.mono (PostGen.forIn
    (I := fun rest s γ => Inv s.1 γ ∧ μ s.1 + (n - rest.length) ≤ μ p) ?_ ?_ _ _)
    (fun _ h => ⟨h, by simp⟩) (fun _ _ h => h)
  · rintro s γ ⟨hi, hμ⟩
    refine ⟨hi, ?_⟩
    simp only [List.length_nil, Nat.sub_zero] at hμ
    omega
  · intro x rest s
    refine PostGen.of_forall fun γ ⟨hi, hμ⟩ => ?_
    refine PostGen.bind ((hstep s.1).mono (fun _ h => h ▸ hi) fun _ _ h => h) fun r => ?_
    obtain ⟨c, q'⟩ := r
    cases c <;>
      simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · exact PostGen.pure fun _ ⟨hi', _, hz⟩ => ⟨hi', hz trivial⟩
    · refine PostGen.pure fun _ ⟨hi', hlt, _⟩ => ⟨hi', ?_⟩
      have hlt' := hlt trivial
      simp only [List.length_cons] at hμ
      dsimp only at hlt' ⊢
      omega

/-- **Bounded iteration of a statement-level transformation reaches measure zero.**  Let every
    successful run of `runProgram f` from a program satisfying `Inv` return a program satisfying
    `Inv`, of smaller measure `μ` when it reports a change and of measure zero when it reports
    none.  Then every successful run of `runProgramUntil f p (some n)`, from `p` satisfying `Inv`
    with `μ p < n`, returns a program satisfying `Inv` of measure zero. -/
theorem runProgramUntil_post {f : Statement → CoreTransformM (Option (List Statement))}
    {Inv : Program → Prop} {μ : Program → Nat}
    {cfgCmd : Option (Command → CoreTransformM (Option (List Command)))}
    (hstep : ∀ q, Inv q → Post (runProgram f q (cfgCmd := cfgCmd)) fun r =>
      Inv r.2 ∧ (r.1 = true → μ r.2 < μ q) ∧ (r.1 = false → μ r.2 = 0))
    {p : Program} {n : Nat} (hp : Inv p) (hn : μ p < n) :
    Post (runProgramUntil f p (some n) (cfgCmd := cfgCmd)) fun r => Inv r.2 ∧ μ r.2 = 0 :=
  fun σ a σ' hr => runProgramUntil_postGen (Inv := fun q _ => Inv q)
    (fun q σ a σ' hq hr => hstep q hq σ a σ' hr) hn σ a σ' hp hr

variable (prefixStr : String)

variable (taken : Std.HashSet String)

/-- A name `CoreGenState.gen` draws at the prefix `prefixStr` has the `<prefix>_<n>` shape. -/
private theorem gen_form (γ : CoreGenState) :
    ∃ n : Nat, (CoreGenState.gen (⟨prefixStr, ()⟩ : CoreIdent) γ).1.name =
      prefixStr ++ "_" ++ toString n := by
  have hname : (CoreGenState.gen (⟨prefixStr, ()⟩ : CoreIdent) γ).1.name =
      prefixStr ++ "_" ++ toString (Counter.genCounter γ.cs.cs).1 := by
    simp only [CoreGenState.gen, StringGenState.gen]
  exact ⟨_, hname⟩

/-- A drawn type-var name is new, has the `<prefix>_<n>` shape, and lands in the output
    generator state, which is well formed and keeps every name of the input state. -/
private theorem genTyVarName_spec (γ γ' : CoreGenState) (f : Lambda.TyIdentifier)
    (hwf : γ.WF) (h : genTyVarName prefixStr taken γ = (f, γ')) :
    γ'.WF ∧ (⟨f, ()⟩ : CoreIdent) ∈ γ'.generated ∧ (⟨f, ()⟩ : CoreIdent) ∉ γ.generated ∧
      γ.generated ⊆ γ'.generated ∧ ∃ n : Nat, f = prefixStr ++ "_" ++ toString n := by
  unfold genTyVarName at h
  simp only [bind, StateT.bind, pure, StateT.pure] at h
  generalize hg : CoreGenState.genAvoiding taken ⟨prefixStr, ()⟩ γ = r at h
  obtain ⟨id, γ1⟩ := r
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  obtain ⟨hwf', hmem, hnot, hsub, -, γ₀, hγ₀⟩ := CoreGenState.genAvoiding_spec taken _ hwf hg
  obtain ⟨n, hn⟩ := gen_form prefixStr γ₀
  rw [hγ₀] at hn
  exact ⟨hwf', hmem, hnot, hsub, n, hn⟩

/-- Every name `genTyVarNames` draws is new, has the `<prefix>_<n>` shape, and lands in the
    output generator state, which is well formed and keeps every name of the input state. -/
private theorem genTyVarNames_spec (n : Nat) :
    ∀ (γ γ' : CoreGenState) (fs : List Lambda.TyIdentifier),
    γ.WF → genTyVarNames prefixStr taken n γ = (fs, γ') →
    γ'.WF ∧ γ.generated ⊆ γ'.generated ∧
      ∀ f ∈ fs, (⟨f, ()⟩ : CoreIdent) ∈ γ'.generated ∧ (⟨f, ()⟩ : CoreIdent) ∉ γ.generated ∧
        ∃ k : Nat, f = prefixStr ++ "_" ++ toString k := by
  induction n with
  | zero =>
    intro γ γ' fs hwf h
    simp only [genTyVarNames, List.replicate, List.mapM_nil, pure, StateT.pure] at h
    injection h with hfs hγ
    subst hfs hγ
    exact ⟨hwf, fun _ hx => hx, fun f hf => absurd hf List.not_mem_nil⟩
  | succ k ih =>
    intro γ γ' fs hwf h
    simp only [genTyVarNames, List.replicate, List.mapM_cons, bind, StateT.bind,
      pure, StateT.pure] at h
    split at h
    next f γ1 h1 =>
      split at h
      next fs' γ2 h2 =>
        injection h with hfs hγ
        subst hfs hγ
        obtain ⟨hwf1, hmem1, hnot1, hsub1, hform1⟩ :=
          genTyVarName_spec prefixStr taken γ γ1 f hwf h1
        obtain ⟨hwf2, hsub2, hall⟩ := ih γ1 γ2 fs' hwf1 h2
        refine ⟨hwf2, fun x hx => hsub2 (hsub1 hx), ?_⟩
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hg'
        · exact ⟨hsub2 hmem1, hnot1, hform1⟩
        · obtain ⟨hm, hn, hf⟩ := hall g hg'
          exact ⟨hm, fun hγ => hn (hsub1 hγ), hf⟩

/-- A monomorphic callee (`typeArgs = []`) yields the empty substitution and does
    not touch the generator — the exact no-op the docstring promises. -/
theorem freshenTypeArgsSubst_empty (γ : CoreGenState) :
    freshenTypeArgsSubst prefixStr taken [] γ = (Lambda.Subst.empty, γ) := by
  simp [freshenTypeArgsSubst, pure, StateT.pure]

/-- A polymorphic callee yields one substitution scope pairing each declared
    type variable with a type constant named by `genTyVarNames`. -/
private theorem freshenTypeArgsSubst_nonempty {S : Lambda.Subst}
    (typeArgs : List Lambda.TyIdentifier) (γ γ' : CoreGenState)
    (hne : typeArgs ≠ []) (h : freshenTypeArgsSubst prefixStr taken typeArgs γ = (S, γ')) :
    ∃ fresh, genTyVarNames prefixStr taken typeArgs.length γ = (fresh, γ') ∧
      S = Lambda.Subst.ofNullaryConsts (typeArgs.zip fresh) := by
  unfold freshenTypeArgsSubst at h
  rw [ite_eq_right (by simp [hne])] at h
  simp only [bind, StateT.bind, pure, StateT.pure] at h
  split at h
  next fresh γ1 hgen =>
    injection h with hS hγ
    exact ⟨fresh, by rw [← hγ]; exact hgen, hS.symm⟩

/-- Every type in the substitution's range is a type constant whose name the generator
    produced for this call site. -/
private theorem freshenTypeArgsSubst_range {S : Lambda.Subst}
    (typeArgs : List Lambda.TyIdentifier) (γ γ' : CoreGenState)
    (hne : typeArgs ≠ []) (h : freshenTypeArgsSubst prefixStr taken typeArgs γ = (S, γ')) :
    ∃ fresh, genTyVarNames prefixStr taken typeArgs.length γ = (fresh, γ') ∧
      ∀ v ∈ S.values, ∃ f ∈ fresh, v = Lambda.LMonoTy.tcons f [] := by
  obtain ⟨fresh, hgen, hS⟩ :=
    freshenTypeArgsSubst_nonempty prefixStr taken typeArgs γ γ' hne h
  refine ⟨fresh, hgen, ?_⟩
  intro v hv
  subst hS
  obtain ⟨tf, htf, hveq⟩ := Lambda.Subst.mem_values_ofNullaryConsts hv
  exact ⟨tf.2, (List.of_mem_zip htf).2, hveq⟩

/-- Freshness: for a polymorphic callee, every type in the range of the
    per-call-site substitution is a nullary type constant whose name (a) has the
    `<prefix>_<n>` shape, (b) is in the output generator state, and (c) is absent from
    the input state; the generator stays well-formed. -/
theorem freshenTypeArgsSubst_fresh {S : Lambda.Subst}
    (typeArgs : List Lambda.TyIdentifier) (γ γ' : CoreGenState)
    (hwf : γ.WF) (h : freshenTypeArgsSubst prefixStr taken typeArgs γ = (S, γ')) :
    γ'.WF ∧
    ∀ v ∈ S.values, ∃ f, v = Lambda.LMonoTy.tcons f [] ∧
      (∃ n : Nat, f = prefixStr ++ "_" ++ toString n) ∧
      (⟨f, ()⟩ : CoreIdent) ∈ γ'.generated ∧ (⟨f, ()⟩ : CoreIdent) ∉ γ.generated := by
  by_cases hne : typeArgs = []
  · subst hne
    have hempty := freshenTypeArgsSubst_empty prefixStr taken γ
    rw [h] at hempty; injection hempty with hS hγ; subst hS hγ
    refine ⟨hwf, fun v hv => ?_⟩
    obtain ⟨m, hm, _⟩ := (Strata.Util.HMaps.mem_values_iff_exists_scope _ v).mp hv
    simp at hm
  obtain ⟨fresh, hgen, hrange⟩ :=
    freshenTypeArgsSubst_range prefixStr taken typeArgs γ γ' hne h
  obtain ⟨hwf', -, hall⟩ := genTyVarNames_spec prefixStr taken _ γ γ' fresh hwf hgen
  refine ⟨hwf', ?_⟩
  intro v hv
  obtain ⟨f, hf_mem, hveq⟩ := hrange v hv
  obtain ⟨hm, hn, hform⟩ := hall f hf_mem
  exact ⟨f, hveq, hform, hm, hn⟩

/-- Cross-call-site disjointness: the substitutions from two successive call
    sites (the second threaded through the first's output generator state) have
    disjoint ranges. -/
theorem freshenTypeArgsSubst_disjoint {S1 S2 : Lambda.Subst}
    (ta1 ta2 : List Lambda.TyIdentifier) (γ γ1 γ2 : CoreGenState)
    (hwf : γ.WF)
    (h1 : freshenTypeArgsSubst prefixStr taken ta1 γ = (S1, γ1))
    (h2 : freshenTypeArgsSubst prefixStr taken ta2 γ1 = (S2, γ2)) :
    ∀ v ∈ S1.values, v ∉ S2.values := by
  have hwf1 : γ1.WF := (freshenTypeArgsSubst_fresh prefixStr taken ta1 γ γ1 hwf h1).1
  intro v hv1 hv2
  obtain ⟨g, hveq, _, hg_in1, _⟩ :=
    (freshenTypeArgsSubst_fresh prefixStr taken ta1 γ γ1 hwf h1).2 v hv1
  obtain ⟨g', hveq', _, _, hg'_notin1⟩ :=
    (freshenTypeArgsSubst_fresh prefixStr taken ta2 γ1 γ2 hwf1 h2).2 v hv2
  have hgg : g = g' := by rw [hveq] at hveq'; injection hveq'
  rw [hgg] at hg_in1
  exact hg'_notin1 hg_in1

/-! ## Statement builders and command builders -/

/-- The havoc statements are the havoc commands, each as a statement. -/
theorem createHavocs_eq_cmds (ids : List Expression.Ident) (md : Imperative.MetaData Expression) :
    createHavocs ids md = (createHavocCmds ids md).map .cmd := by
  simp [createHavocs, createHavocCmds, createHavoc, createHavocCmd, Function.comp_def]

/-- The init statements are the init commands, each as a statement. -/
theorem createInits_eq_cmds
    (trips : List ((Expression.Ident × Expression.Ty) × Expression.Expr))
    (md : Imperative.MetaData Expression) :
    createInits trips md = (createInitCmds trips md).map .cmd := by
  simp only [createInits, createInitCmds, List.map_map]
  congr 1

/-- The variable-init statements are the variable-init commands, each as a statement. -/
theorem createInitVars_eq_cmds
    (trips : List ((Expression.Ident × Expression.Ty) × Expression.Ident))
    (md : Imperative.MetaData Expression) :
    createInitVars trips md = (createInitVarCmds trips md).map .cmd := by
  simp only [createInitVars, createInitVarCmds, List.map_map]
  congr 1

end Transform

end Core

end -- public section
