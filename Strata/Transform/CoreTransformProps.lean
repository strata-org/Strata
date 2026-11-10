/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemanticsProps
public import Strata.Transform.CoreTransform
import all Strata.Transform.CoreTransform
import all Strata.Languages.Core.CoreGen

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

Properties of the per-call-site type-variable freshening in
`Strata.Transform.CoreTransform`, and of the successful runs of the generic runners
(`Post m Q`: every successful run of `m` returns a value satisfying `Q`; `PostGen P m Q`: every
successful run of `m` from a generator state satisfying `P` ends with a value and a generator
state satisfying `Q`). Key results:

- `runProgram_post` — `runProgram f p` replaces each structured procedure body by the result
  of a run of `runStmtsRec f` on it when that run reports a change (`DeclStep`), and reports a
  change exactly when one of these runs does.
- `runProgramUntil_post` — `runProgramUntil f p (some n)` keeps any invariant that each pass
  keeps, and returns a program of measure zero when the measure of `p` is below `n` and each
  pass lowers the measure when it reports a change and returns measure zero otherwise.
- `runProgram_postGen`, `runProgramUntil_postGen` — the same, following the generator state,
  so that a transformation can show that the names it draws in different passes differ; the
  two results above are their instances.

- `freshenTypeArgsSubst_fresh` — mechanism freshness: every type in the
  substitution's range is a fresh `<prefix>_<n>` variable, present in the output
  generator state and absent from the input's.
- `freshenTypeArgsSubst_disjoint` — cross-call-site disjointness: two successive
  call sites draw disjoint fresh ranges, which is what stops one inlined
  contract from unifying with another's.
- `freshenTypeArgsSubst_empty` — monomorphic callees (`typeArgs = []`) yield
  `Subst.empty` without touching the generator: an exact no-op.

The theorems are generic in the prefix string; call elimination and procedure
inlining instantiate it with `Lambda.callElimTyPrefix` and
`Lambda.inlineTyPrefix`.

Key definitions the reader needs: `freshenTypeArgsSubst`, `genTyVarName(s)`
(in `CoreTransform.lean`), and `CoreGenState.WF` (in `CoreGen.lean`).

Proven against `StringGenState`'s counter monotonicity (`CoreGenState.WFMono`),
independent of the `CallElimCorrect` correctness proof; the whole-program
"emitted program type-checks" theorem is out of scope for this file.

Scope note: `freshenTypeArgsSubst_fresh` proves each fresh name carries the
reserved `<prefix>_<n>` shape, so the names are structurally in the prefix's
namespace. The counter does not ingest existing program identifiers, so a
written `<prefix>_<n>` type variable is kept apart from the fresh names only by
the prefix being reserved (`Lambda.isAllowedName`). Freshness and
disjointness across call sites — the property that actually prevents
cross-site unification — is fully proven here.
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

/-- `r` is what `runProgram` makes of the declaration `d`, with its change flag, when every
    successful run of `runStmtsRec` on a list `ss` returning `(c, ss')` satisfies
    `Q ss (c, ss')`: a procedure with a structured body `ss` gets the body `ss'` when `c` is set
    and is kept otherwise; any other declaration is kept, with no change. -/
@[expose] def DeclStep (Q : Statements → Bool × Statements → Prop) (d : Decl)
    (r : Bool × Decl) : Prop :=
  match d with
  | .proc proc md => ∃ ss ss', proc.body = .structured ss ∧ Q ss (r.1, ss') ∧
      r.2 = if r.1 then .proc { proc with body := .structured ss' } md else .proc proc md
  | _ => r = (false, d)

/-- **What `runProgram` does to each declaration, tracking the generator state.**  Let `le` be
    a preorder on generator states, and let every successful run of `runStmtsRec f` on a list
    `ss` from a generator state `γ` end in a generator state `γ'` with `le γ γ'` and return a
    value `r` with `Q ss γ r γ'`, a property kept by any wider pair of generator states.  A
    successful run of `runProgram f p` from `γ₀` ends in some `γ₁` with `le γ₀ γ₁`, and returns
    the program of the declarations `rs` makes of those of `p` (`DeclStep (Q · γ₀ · γ₁)`),
    reporting a change exactly when one of them does. -/
theorem runProgram_postGen {f : Statement → CoreTransformM (Option (List Statement))}
    {le : CoreGenState → CoreGenState → Prop} (hrefl : ∀ γ, le γ γ)
    (htrans : ∀ {γ₁ γ₂ γ₃}, le γ₁ γ₂ → le γ₂ γ₃ → le γ₁ γ₃)
    {Q : Statements → CoreGenState → Bool × Statements → CoreGenState → Prop}
    (hQ : ∀ {ss γ₀ γ r γ' γ₁}, le γ₀ γ → le γ' γ₁ → Q ss γ r γ' → Q ss γ₀ r γ₁)
    (hf : ∀ ss γ, PostGen (· = γ) (runStmtsRec f ss) fun r γ' => le γ γ' ∧ Q ss γ r γ')
    (p : Program) (γ₀ : CoreGenState) :
    PostGen (· = γ₀) (runProgram f p) fun r γ₁ => le γ₀ γ₁ ∧ ∃ rs : List (Bool × Decl),
      List.Rel₂ (DeclStep fun ss r => Q ss γ₀ r γ₁) p.decls rs ∧ r.2.decls = rs.map (·.2) ∧
      r.1 = rs.any (·.1) := by
  -- The declarations made so far keep their property in a wider generator state.
  have hwiden : ∀ {γ γ'}, le γ γ' → ∀ {ds : List Decl} {rs : List (Bool × Decl)},
      List.Rel₂ (DeclStep fun ss r => Q ss γ₀ r γ) ds rs →
      List.Rel₂ (DeclStep fun ss r => Q ss γ₀ r γ') ds rs := fun hle _ _ h =>
    h.imp fun {d r} hd => by
      cases d
      case proc proc md =>
        obtain ⟨ss, ss', hb, hq, hr⟩ := hd
        exact ⟨ss, ss', hb, hQ (hrefl _) hle hq, hr⟩
      all_goals exact hd
  unfold runProgram
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
        refine PostGen.bind (PostGen.pure (a := ss) (Q := fun a γ' => a = ss ∧ γ' = γ)
          fun _ h => ⟨rfl, h⟩) fun a => ?_
        refine PostGen.of_forall fun γ' ⟨hss, hγ⟩ => ?_
        rw [hss, hγ]
        refine PostGen.bind (hf ss γ) fun r => ?_
        obtain ⟨c, ss'⟩ := r
        cases c
        · refine PostGen.pure fun γ' ⟨hle', hq⟩ => ?_
          obtain ⟨k', rs', h₁, h₂, h₃, h₄, h₅⟩ := hnext γ' (false, .proc proc md) hle'
            ⟨ss, ss', hbody, hQ hle (hrefl _) hq, by simp⟩
          exact ⟨htrans hle hle', k', rs', h₁, h₂, h₃, by rw [h2, hdrop]; exact h₄,
            by simpa using h₅⟩
        · refine PostGen.bind (PostGen.modify (Q := fun _ γ' => le γ γ' ∧ Q ss γ (true, ss') γ')
            (by intro; rfl) fun _ h => h) fun _ => PostGen.pure fun γ' ⟨hle', hq⟩ => ?_
          have hset : s.2.set k (.proc { proc with body := .structured ss' } md) =
              rs.map (·.2) ++ .proc { proc with body := .structured ss' } md ::
                p.decls.drop (k + 1) := by
            rw [h2, hdrop, List.set_append_right _ _ (by simp [hlen])]
            simp [hlen]
          obtain ⟨k', rs', h₁, h₂, h₃, h₄, h₅⟩ :=
            hnext γ' (true, .proc { proc with body := .structured ss' } md) hle'
              ⟨ss, ss', hbody, hQ hle (hrefl _) hq, by simp⟩
          exact ⟨htrans hle hle', k', rs', h₁, h₂, h₃, hset.trans h₄, by simpa using h₅⟩
      · exact PostGen.bind (Q₁ := fun _ _ => False) PostGen.throw fun _ _ _ _ h _ => h.elim
    all_goals
      refine PostGen.pure fun _ h => ?_
      rw [h]
      obtain ⟨k', rs', h₁, h₂, h₃, h₄, h₅⟩ := hnext γ (false, _) (hrefl _) rfl
      exact ⟨hle, k', rs', h₁, h₂, h₃, by rw [h2, hdrop]; exact h₄, by simpa using h₅⟩

/-- **What `runProgram` does to each declaration.**  When every successful run of
    `runStmtsRec f` on a list `ss` returns a value satisfying `Q ss`, a successful run of
    `runProgram f p` (over every procedure) returns the program of the declarations `rs` makes of
    those of `p` (`DeclStep Q`), and reports a change exactly when one of them does. -/
theorem runProgram_post {f : Statement → CoreTransformM (Option (List Statement))}
    {Q : Statements → Bool × Statements → Prop} (hf : ∀ ss, Post (runStmtsRec f ss) (Q ss))
    (p : Program) :
    Post (runProgram f p) fun r => ∃ rs : List (Bool × Decl),
      List.Rel₂ (DeclStep Q) p.decls rs ∧ r.2.decls = rs.map (·.2) ∧ r.1 = rs.any (·.1) :=
  fun σ a σ' hr => (runProgram_postGen (le := fun _ _ => True) (Q := fun ss _ r _ => Q ss r)
    (fun _ => trivial) (fun _ _ => trivial) (fun _ _ h => h)
    (fun ss _ => ((hf ss).postGen _).mono (fun _ h => h) fun _ _ h => ⟨trivial, h⟩)
    p σ.genState σ a σ' rfl hr).2

/-- **Bounded iteration of a statement-level transformation reaches measure zero, tracking the
    generator state.**  Let every successful run of `runProgram f q` from a generator state with
    `Inv q` end in one with `Inv` of the program it returns, of smaller measure `μ` when it
    reports a change and of measure zero when it reports none.  Then every successful run of
    `runProgramUntil f p (some n)` from a generator state with `Inv p`, where `μ p < n`, ends in
    one with `Inv` of the program it returns, of measure zero. -/
theorem runProgramUntil_postGen {f : Statement → CoreTransformM (Option (List Statement))}
    {Inv : Program → CoreGenState → Prop} {μ : Program → Nat}
    (hstep : ∀ q, PostGen (Inv q) (runProgram f q) fun r γ =>
      Inv r.2 γ ∧ (r.1 = true → μ r.2 < μ q) ∧ (r.1 = false → μ r.2 = 0))
    {p : Program} {n : Nat} (hn : μ p < n) :
    PostGen (Inv p) (runProgramUntil f p (some n)) fun r γ => Inv r.2 γ ∧ μ r.2 = 0 := by
  simp only [runProgramUntil]
  refine PostGen.bind (Q₁ := fun s γ => Inv s.1 γ ∧ μ s.1 = 0) ?_ fun _ =>
    PostGen.pure fun _ h => h
  refine PostGen.mono (PostGen.forIn
    (I := fun rest s γ => Inv s.1 γ ∧ μ s.1 + (n - rest.length) ≤ μ p) ?_ ?_ _ _)
    (fun _ h => ⟨h, by simp⟩) (fun _ _ h => h)
  · rintro s γ ⟨hi, hμ⟩
    exact ⟨hi, by simp only [List.length_nil, Nat.sub_zero] at hμ; omega⟩
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
    (hstep : ∀ q, Inv q → Post (runProgram f q) fun r =>
      Inv r.2 ∧ (r.1 = true → μ r.2 < μ q) ∧ (r.1 = false → μ r.2 = 0))
    {p : Program} {n : Nat} (hp : Inv p) (hn : μ p < n) :
    Post (runProgramUntil f p (some n)) fun r => Inv r.2 ∧ μ r.2 = 0 :=
  fun σ a σ' hr => runProgramUntil_postGen (Inv := fun q _ => Inv q)
    (fun q σ a σ' hq hr => hstep q hq σ a σ' hr) hn σ a σ' hp hr

variable (prefixStr : String)

/-- `genTyVarName` is `CoreGenState.gen` at the fresh type-var prefix, with the
    generated string reified back into the `CoreIdent`. -/
private theorem genTyVarName_gen (γ γ' : CoreGenState) (f : Lambda.TyIdentifier)
    (h : genTyVarName prefixStr γ = (f, γ')) :
    CoreGenState.gen (⟨prefixStr, ()⟩ : CoreIdent) γ = (⟨f, ()⟩, γ') := by
  unfold genTyVarName at h
  simp only [bind, StateT.bind, pure, StateT.pure] at h
  obtain ⟨hf, hγ⟩ := h
  simp only [CoreGenState.gen, StringGenState.gen]

/-- One type-var draw grows `generated` by exactly the fresh ident. -/
private theorem genTyVarName_generated (γ γ' : CoreGenState) (f : Lambda.TyIdentifier)
    (h : genTyVarName prefixStr γ = (f, γ')) :
    γ'.generated = (⟨f, ()⟩ : CoreIdent) :: γ.generated := by
  have hg := genTyVarName_gen prefixStr γ γ' f h
  simp only [CoreGenState.gen, Prod.mk.injEq, Lambda.Identifier.mk.injEq, and_true] at hg; rw [← hg.2, ← hg.1]

/-- One type-var draw preserves generator well-formedness. -/
private theorem genTyVarName_wf (γ γ' : CoreGenState) (f : Lambda.TyIdentifier)
    (hwf : γ.WF) (h : genTyVarName prefixStr γ = (f, γ')) : γ'.WF :=
  CoreGenState.WFMono' hwf (genTyVarName_gen prefixStr γ γ' f h)

/-- A drawn type-var name has the `<prefix>_<n>` shape — witnessing that it
    lives in the prefix's namespace (stronger than `startsWith`). -/
private theorem genTyVarName_form (γ γ' : CoreGenState) (f : Lambda.TyIdentifier)
    (h : genTyVarName prefixStr γ = (f, γ')) :
    ∃ n : Nat, f = prefixStr ++ "_" ++ toString n := by
  refine ⟨(Counter.genCounter γ.cs.cs).1, ?_⟩
  unfold genTyVarName at h
  simp only [bind, StateT.bind, pure, StateT.pure] at h
  have h1 : (CoreGenState.gen (⟨prefixStr, ()⟩ : CoreIdent) γ).fst.name = f :=
    congrArg Prod.fst h
  rw [← h1]; simp only [CoreGenState.gen, StringGenState.gen]

/-- Generating `n` type-var names grows `generated` by exactly those idents. -/
private theorem genTyVarNames_generated (n : Nat) :
    ∀ (γ γ' : CoreGenState) (fs : List Lambda.TyIdentifier),
    genTyVarNames prefixStr n γ = (fs, γ') →
    γ'.generated = (fs.reverse.map (fun f => (⟨f, ()⟩ : CoreIdent))) ++ γ.generated := by
  induction n with
  | zero =>
    intro γ γ' fs h
    simp only [genTyVarNames, List.replicate, List.mapM_nil, pure, StateT.pure] at h
    injection h with hfs hγ; subst hfs hγ; simp
  | succ k ih =>
    intro γ γ' fs h
    simp only [genTyVarNames, List.replicate, List.mapM_cons, bind, StateT.bind,
      pure, StateT.pure] at h
    split at h
    next f γ1 h1 =>
      split at h
      next fs' γ2 h2 =>
        injection h with hfs hγ; subst hfs hγ
        rw [ih γ1 γ2 fs' h2, genTyVarName_generated prefixStr γ γ1 f h1]
        simp [List.reverse_cons, List.map_append]

/-- Generating `n` type-var names preserves generator well-formedness. -/
private theorem genTyVarNames_wf (n : Nat) :
    ∀ (γ γ' : CoreGenState) (fs : List Lambda.TyIdentifier),
    γ.WF → genTyVarNames prefixStr n γ = (fs, γ') → γ'.WF := by
  induction n with
  | zero =>
    intro γ γ' fs hwf h
    simp only [genTyVarNames, List.replicate, List.mapM_nil, pure, StateT.pure] at h
    injection h with hfs hγ; subst hγ; exact hwf
  | succ k ih =>
    intro γ γ' fs hwf h
    simp only [genTyVarNames, List.replicate, List.mapM_cons, bind, StateT.bind,
      pure, StateT.pure] at h
    split at h
    next f γ1 h1 =>
      split at h
      next fs' γ2 h2 =>
        injection h with _ hγ; subst hγ
        exact ih γ1 _ fs' (genTyVarName_wf prefixStr γ γ1 f hwf h1) h2

/-- Every generated type-var name lands in the output generator state. -/
private theorem genTyVarNames_mem (n : Nat) (γ γ' : CoreGenState) (fs : List Lambda.TyIdentifier)
    (h : genTyVarNames prefixStr n γ = (fs, γ')) :
    ∀ f ∈ fs, (⟨f, ()⟩ : CoreIdent) ∈ γ'.generated := by
  intro f hf
  rw [genTyVarNames_generated prefixStr n γ γ' fs h]
  apply List.mem_append_left
  rw [List.map_reverse, List.mem_reverse]
  exact List.mem_map_of_mem hf

/-- Every generated type-var name is absent from the input generator state. -/
private theorem genTyVarNames_fresh (n : Nat) (γ γ' : CoreGenState) (fs : List Lambda.TyIdentifier)
    (hwf : γ.WF) (h : genTyVarNames prefixStr n γ = (fs, γ')) :
    ∀ f ∈ fs, (⟨f, ()⟩ : CoreIdent) ∉ γ.generated := by
  intro f hf
  have hnd : γ'.generated.Nodup := (genTyVarNames_wf prefixStr n γ γ' fs hwf h).2.2
  rw [genTyVarNames_generated prefixStr n γ γ' fs h] at hnd
  have hdisj := (List.nodup_append.mp hnd).2.2
  have hin_pref : (⟨f, ()⟩ : CoreIdent) ∈ (fs.reverse.map (fun f => (⟨f, ()⟩ : CoreIdent))) := by
    rw [List.map_reverse, List.mem_reverse]; exact List.mem_map_of_mem hf
  intro hmem
  exact hdisj _ hin_pref _ hmem rfl

/-- Every generated type-var name has the `<prefix>_<n>` shape. -/
private theorem genTyVarNames_form (n : Nat) :
    ∀ (γ γ' : CoreGenState) (fs : List Lambda.TyIdentifier),
    genTyVarNames prefixStr n γ = (fs, γ') →
    ∀ f ∈ fs, ∃ k : Nat, f = prefixStr ++ "_" ++ toString k := by
  induction n with
  | zero =>
    intro γ γ' fs h f hf
    simp only [genTyVarNames, List.replicate, List.mapM_nil, pure, StateT.pure] at h
    injection h with hfs _; subst hfs; simp at hf
  | succ k ih =>
    intro γ γ' fs h f hf
    simp only [genTyVarNames, List.replicate, List.mapM_cons, bind, StateT.bind,
      pure, StateT.pure] at h
    split at h
    next f0 γ1 h1 =>
      split at h
      next fs' γ2 h2 =>
        injection h with hfs hγ; subst hfs
        rw [List.mem_cons] at hf
        cases hf with
        | inl hh => subst hh; exact genTyVarName_form prefixStr γ γ1 f h1
        | inr hh => exact ih γ1 γ2 fs' h2 f hh

/-- A monomorphic callee (`typeArgs = []`) yields the empty substitution and does
    not touch the generator — the exact no-op the docstring promises. -/
theorem freshenTypeArgsSubst_empty (γ : CoreGenState) :
    freshenTypeArgsSubst prefixStr [] γ = (Lambda.Subst.empty, γ) := by
  simp [freshenTypeArgsSubst, pure, StateT.pure]

/-- A polymorphic callee yields one substitution scope pairing each declared
    type variable with a name drawn from `genTyVarNames`. -/
private theorem freshenTypeArgsSubst_nonempty {S : Lambda.Subst}
    (typeArgs : List Lambda.TyIdentifier) (γ γ' : CoreGenState)
    (hne : typeArgs ≠ []) (h : freshenTypeArgsSubst prefixStr typeArgs γ = (S, γ')) :
    ∃ fresh, genTyVarNames prefixStr typeArgs.length γ = (fresh, γ') ∧
      S = [Strata.Util.HMap.ofList
        ((typeArgs.zip fresh).map (fun tf => (tf.1, Lambda.LMonoTy.ftvar tf.2)))] := by
  unfold freshenTypeArgsSubst at h
  rw [ite_eq_right (by simp [hne])] at h
  simp only [bind, StateT.bind, pure, StateT.pure] at h
  split at h
  next fresh γ1 hgen =>
    injection h with hS hγ
    exact ⟨fresh, by rw [← hγ]; exact hgen, hS.symm⟩

/-- Every type in the substitution's range is a fresh type variable produced by
    the generator for this call site. -/
private theorem freshenTypeArgsSubst_range {S : Lambda.Subst}
    (typeArgs : List Lambda.TyIdentifier) (γ γ' : CoreGenState)
    (hne : typeArgs ≠ []) (h : freshenTypeArgsSubst prefixStr typeArgs γ = (S, γ')) :
    ∃ fresh, genTyVarNames prefixStr typeArgs.length γ = (fresh, γ') ∧
      ∀ v ∈ S.values, ∃ f ∈ fresh, v = Lambda.LMonoTy.ftvar f := by
  obtain ⟨fresh, hgen, hS⟩ := freshenTypeArgsSubst_nonempty prefixStr typeArgs γ γ' hne h
  refine ⟨fresh, hgen, ?_⟩
  intro v hv
  subst hS
  obtain ⟨m, hm, hvm⟩ := (Strata.Util.HMaps.mem_values_iff_exists_scope _ v).mp hv
  simp only [List.mem_singleton] at hm; subst hm
  have hv' := Strata.Util.HMap.mem_values_ofList _ v hvm
  simp only [List.map_map, List.mem_map] at hv'
  obtain ⟨tf, htf, hveq⟩ := hv'
  exact ⟨tf.2, (List.of_mem_zip htf).2, hveq.symm⟩

/-- Freshness: for a polymorphic callee, every type in the range of the
    per-call-site substitution is a fresh type variable that (a) carries the
    `<prefix>_<n>` shape (so it lies in the prefix's namespace),
    (b) is present in the output generator state, and (c) is absent from the input
    state — and the generator stays well-formed. This is the mechanism that keeps
    one call site's contract from unifying with another's. -/
theorem freshenTypeArgsSubst_fresh {S : Lambda.Subst}
    (typeArgs : List Lambda.TyIdentifier) (γ γ' : CoreGenState)
    (hwf : γ.WF) (h : freshenTypeArgsSubst prefixStr typeArgs γ = (S, γ')) :
    γ'.WF ∧
    ∀ v ∈ S.values, ∃ f, v = Lambda.LMonoTy.ftvar f ∧
      (∃ n : Nat, f = prefixStr ++ "_" ++ toString n) ∧
      (⟨f, ()⟩ : CoreIdent) ∈ γ'.generated ∧ (⟨f, ()⟩ : CoreIdent) ∉ γ.generated := by
  by_cases hne : typeArgs = []
  · subst hne
    have := freshenTypeArgsSubst_empty prefixStr γ
    rw [h] at this; injection this with hS hγ; subst hS hγ
    refine ⟨hwf, fun v hv => ?_⟩
    obtain ⟨m, hm, _⟩ := (Strata.Util.HMaps.mem_values_iff_exists_scope _ v).mp hv
    simp at hm
  obtain ⟨fresh, hgen, hrange⟩ := freshenTypeArgsSubst_range prefixStr typeArgs γ γ' hne h
  refine ⟨genTyVarNames_wf prefixStr _ γ γ' fresh hwf hgen, ?_⟩
  intro v hv
  obtain ⟨f, hf_mem, hveq⟩ := hrange v hv
  exact ⟨f, hveq,
    genTyVarNames_form prefixStr _ γ γ' fresh hgen f hf_mem,
    genTyVarNames_mem prefixStr _ γ γ' fresh hgen f hf_mem,
    genTyVarNames_fresh prefixStr _ γ γ' fresh hwf hgen f hf_mem⟩

/-- Cross-call-site disjointness: the substitutions from two successive call
    sites (the second threaded through the first's output generator state) have
    disjoint fresh type-variable ranges. A fresh variable from site 2 is absent
    from `γ1.generated`, while every fresh variable from site 1 is present in it —
    so no name is shared, which is exactly what stops the two sites' contracts
    from unifying. -/
theorem freshenTypeArgsSubst_disjoint {S1 S2 : Lambda.Subst}
    (ta1 ta2 : List Lambda.TyIdentifier) (γ γ1 γ2 : CoreGenState)
    (hwf : γ.WF)
    (h1 : freshenTypeArgsSubst prefixStr ta1 γ = (S1, γ1))
    (h2 : freshenTypeArgsSubst prefixStr ta2 γ1 = (S2, γ2)) :
    ∀ v ∈ S1.values, v ∉ S2.values := by
  have hwf1 : γ1.WF := (freshenTypeArgsSubst_fresh prefixStr ta1 γ γ1 hwf h1).1
  intro v hv1 hv2
  obtain ⟨g, hveq, _, hg_in1, _⟩ := (freshenTypeArgsSubst_fresh prefixStr ta1 γ γ1 hwf h1).2 v hv1
  obtain ⟨g', hveq', _, _, hg'_notin1⟩ := (freshenTypeArgsSubst_fresh prefixStr ta2 γ1 γ2 hwf1 h2).2 v hv2
  have hgg : g = g' := by rw [hveq] at hveq'; injection hveq'
  rw [hgg] at hg_in1
  exact hg'_notin1 hg_in1

end Transform

end Core

end -- public section
