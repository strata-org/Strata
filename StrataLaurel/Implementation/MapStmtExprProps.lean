/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.MapStmtExpr
public import StrataLaurel.Implementation.LaurelNodeKindProps
import all StrataLaurel.Implementation.MapStmtExpr
import Strata.Util.Tactics

/-!
# MapStmtExpr Properties

Facts about the shared bottom-up traversal `mapStmtExprUsedM`, independent of any
particular pass.

`mapStmtExprUsedM_contains` is the reusable half of a pass's `NodeKind`
specification (see `LaurelNodeKindProps.lean` for what the declarations mean):
if the rewrite maps every rebuilt node into the output set, so does the whole
traversal. A pass's own proof is then only the per-node obligation —
`EliminateDoWhileProps.rewriteNode_contains` is one, and the plumbing from there
to `LaurelProgram` is in that same file.

## Key results

* `mapStmtExprUsedM_contains` — the traversal lemma;
* `mapType_id`, `mapType_substUserDefined_names`, `mapType_substUserDefined_eq`
  — the universal properties of the `HighType` traversal `HighType.mapType`
  (see the section of that name below);
* `ShapeStable` / `mapStmtExprUsedM_isVarLocal` — its one side condition;
* `Rebuilt` — what the traversal hands the rewrite;
* `PostM` and its combinators — `post_bind`, `post_mapM`,
  `post_option_mapM_mem`, `post_mapIdxM`, `post_mapM_length`.

Two supporting pieces come with it:

* the `PostM` calculus — state-independent postconditions on `StateM` actions,
  with the bind/`mapM`/`Option.mapM`/`mapIdxM` combinators the traversal's arms
  need. It mirrors `ResolutionProps`'s `PostM`/`PostS`, which serve the same role
  for `ResolveM`;
* `ShapeStable`, the one non-obvious requirement the traversal lemma places on a
  rewrite. `NodeKind.ofStmtExpr` reads one *child's* constructor — an `Old`
  wrapping a bare local is `StmtExpr.Old.value.Var.Local` — so a bottom-up
  rewrite that could manufacture a bare local read out of something else would
  make the rebuilt `Old` satisfy a kind its input did not.
-/

namespace Strata.Laurel

public section

/-! ## A postcondition calculus, over any monad a pass runs in

`PostM a P` says the value `a` returns satisfies `P`. What that means depends on
the monad — for `StateM` it is "for every starting state", for `Id` it is just
`P a` — so it is a class with the four properties the traversal proofs use.
`StateM` covers a pass that threads a counter or diagnostics; `Id` covers a pure
one. -/

/-- A monad whose actions admit a value postcondition. `Post a P`: whatever `a`
    returns satisfies `P`. -/
class MonadPost (m : Type → Type) [Monad m] where
  /-- The postcondition judgement. -/
  Post {α : Type} : m α → (α → Prop) → Prop
  /-- A pure action satisfies every postcondition its value satisfies. -/
  postPure {α : Type} {x : α} {P : α → Prop} : P x → Post (pure x) P
  /-- Postconditions compose along `bind`: if `a` returns a `Q`-value and `f` turns
      any `Q`-value into a `P`-action, then `a >>= f` returns a `P`-value. -/
  postBind {α β : Type} {a : m α} {f : α → m β} {Q : α → Prop} {P : β → Prop} :
    Post a Q → (∀ x, Q x → Post (f x) P) → Post (a >>= f) P
  /-- A postcondition can be weakened. -/
  postMono {α : Type} {a : m α} {P Q : α → Prop} : Post a P → (∀ x, P x → Q x) → Post a Q
  /-- Two postconditions of the same action can be conjoined. -/
  postAnd {α : Type} {a : m α} {P Q : α → Prop} :
    Post a P → Post a Q → Post a (fun x => P x ∧ Q x)
  /-- Every action satisfies the trivial postcondition. -/
  postTrue {α : Type} {a : m α} : Post a (fun _ => True)

abbrev PostM {m : Type → Type} [Monad m] [MonadPost m] {α : Type}
    (a : m α) (P : α → Prop) : Prop := MonadPost.Post a P

/-- For `StateM`, a postcondition holds of the value returned from every starting
    state. The state itself is unconstrained, which is what lets a pass thread a
    fresh-name counter without the proof mentioning it. -/
instance {σ : Type} : MonadPost (StateM σ) where
  Post a P := ∀ st, P (a st).1
  postPure h := fun _ => h
  postBind ha hf := fun st => hf _ (ha st) _
  postMono h imp := fun st => imp _ (h st)
  postAnd hp hq := fun st => ⟨hp st, hq st⟩
  postTrue := fun _ => trivial

/-- For `Id`, a postcondition is a property of the result. -/
instance : MonadPost Id where
  Post a P := P a
  postPure h := h
  postBind ha hf := hf _ ha
  postMono h imp := imp _ h
  postAnd hp hq := ⟨hp, hq⟩
  postTrue := trivial

variable {m : Type → Type} [Monad m] [MonadPost m] {α β : Type}

/-- `pure x` satisfies every postcondition `x` satisfies. -/
theorem post_pure {x : α} {P : α → Prop} (h : P x) : PostM (m := m) (pure x) P :=
  MonadPost.postPure h

/-- Postconditions compose along `bind`. -/
theorem post_bind {a : m α} {f : α → m β} {Q : α → Prop} {P : β → Prop}
    (ha : PostM a Q) (hf : ∀ x, Q x → PostM (f x) P) : PostM (a >>= f) P :=
  MonadPost.postBind ha hf

/-- Postconditions compose along `bind` when nothing about the intermediate value
    is needed. -/
theorem post_bind_any {a : m α} {f : α → m β} {P : β → Prop}
    (hf : ∀ x, PostM (f x) P) : PostM (a >>= f) P :=
  post_bind (Q := fun _ => True) MonadPost.postTrue (fun x _ => hf x)

/-- A postcondition can be weakened. -/
private theorem post_mono {a : m α} {P Q : α → Prop} (h : PostM a P) (imp : ∀ x, P x → Q x) :
    PostM a Q := MonadPost.postMono h imp

/-- Two postconditions of the same action can be conjoined. -/
theorem post_and {a : m α} {P Q : α → Prop} (hp : PostM a P) (hq : PostM a Q) :
    PostM a (fun x => P x ∧ Q x) := MonadPost.postAnd hp hq

/-- In `Id` a postcondition is a property of the value, so a pure pass's proofs
    need no monadic plumbing. -/
theorem post_id {α : Type} {a : Id α} {P : α → Prop} (h : P a) : PostM (m := Id) a P := h

/-- `post_id` as a rewrite, usable in either direction. -/
@[simp] theorem postM_id_iff {α : Type} {a : Id α} {P : α → Prop} :
    PostM (m := Id) a P ↔ P a := Iff.rfl

/-- A postcondition of `g <$> a` follows from one of `a` stated through `g`. -/
private theorem post_map [LawfulMonad m] {a : m α} {g : α → β} {P : β → Prop}
    (h : PostM a (fun x => P (g x))) : PostM (g <$> a) P := by
  rw [map_eq_pure_bind]
  exact post_bind h (fun x hx => post_pure hx)

/-- `mapM`: a pointwise postcondition on each element's action lifts to "every
    element of the result". -/
theorem post_mapM [LawfulMonad m] (l : List α) (f : α → m β) {P : β → Prop}
    (h : ∀ x ∈ l, PostM (f x) P) :
    PostM (l.mapM f) (fun rs => ∀ r ∈ rs, P r) := by
  induction l with
  | nil => rw [List.mapM_nil]; exact post_pure (by simp)
  | cons hd tl ih =>
    have hhd := h hd (by simp)
    have htl := ih (fun x hx => h x (by simp [hx]))
    rw [List.mapM_cons]
    exact post_bind hhd (fun r hr =>
      post_bind htl (fun rs hrs =>
        post_pure (by
          intro x hx
          rcases List.mem_cons.mp hx with h1 | h2
          · exact h1 ▸ hr
          · exact hrs x h2)))

/-- `post_mapM` for the `List.attach` form the traversal's arms use, where the
    function receives each element paired with its membership proof. -/
private theorem post_attach_mapM [LawfulMonad m] (l : List α) (f : {x // x ∈ l} → m β) {P : β → Prop}
    (h : ∀ x, PostM (f x) P) :
    PostM (l.attach.mapM f) (fun rs => ∀ r ∈ rs, P r) :=
  post_mapM l.attach f (fun x _ => h x)

/-- `Option.mapM`: a postcondition of the element's action is a postcondition of
    the result, for the element actually present. -/
theorem post_option_mapM_mem [LawfulMonad m] (o : Option α) (f : α → m β) {P : β → Prop}
    (h : ∀ x ∈ o, PostM (f x) P) :
    PostM (o.mapM f) (fun r => ∀ x ∈ r, P x) := by
  cases o with
  | none =>
    simp only [Option.mapM]
    exact post_pure (by simp)
  | some v =>
    simp only [Option.mapM]
    refine post_map (post_mono (h v (by simp)) (fun x hx => ?_))
    intro y hy
    simp only [Option.mem_def, Option.some.injEq] at hy
    exact hy ▸ hx

/-- `post_option_mapM_mem` with the pointwise hypothesis given for every value. -/
private theorem post_option_mapM [LawfulMonad m] (o : Option α) (f : α → m β) {P : β → Prop}
    (h : ∀ x, PostM (f x) P) :
    PostM (o.mapM f) (fun r => ∀ x ∈ r, P x) :=
  post_option_mapM_mem o f (fun x _ => h x)

/-- `post_option_mapM` for the `Option.attach` form. -/
private theorem post_option_attach_mapM [LawfulMonad m] (o : Option α) (f : {x // x ∈ o} → m β) {P : β → Prop}
    (h : ∀ x, PostM (f x) P) :
    PostM (o.attach.mapM f) (fun r => ∀ x ∈ r, P x) :=
  post_option_mapM o.attach f (fun x => h x)

/-- The accumulator loop behind `mapIdxM`: if every element's action satisfies `P`,
    so does every entry of the accumulated prefix, hence of the result. -/
private theorem post_mapIdxM_go (f : Nat → α → m β) {P : β → Prop}
    (l : List α) (h : ∀ i x, PostM (f i x) P) (acc : Array β)
    (hacc : ∀ r ∈ acc.toList, P r) :
    PostM (List.mapIdxM.go f l acc) (fun rs => ∀ r ∈ rs, P r) := by
  induction l generalizing acc with
  | nil => rw [List.mapIdxM.go]; exact post_pure (by simpa using hacc)
  | cons hd tl ih =>
    rw [List.mapIdxM.go]
    exact post_bind (h acc.size hd) (fun b hb =>
      ih (acc.push b) (by
        intro r hr
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hr
        rcases hr with h1 | h2
        · exact hacc r h1
        · exact h2 ▸ hb))

/-- `mapIdxM`: as `post_mapM`, for the index-aware map a `Block`'s statements go
    through (the index decides whether a statement is in value position). -/
theorem post_mapIdxM (l : List α) (f : Nat → α → m β) {P : β → Prop}
    (h : ∀ i x, PostM (f i x) P) :
    PostM (l.mapIdxM f) (fun rs => ∀ r ∈ rs, P r) :=
  post_mapIdxM_go f l h #[] (by simp)

/-- `mapM` preserves length. Needed because a kind can be about a list being
    non-empty, and the rebuilt node must still satisfy it. -/
theorem post_mapM_length [LawfulMonad m] (l : List α) (f : α → m β) :
    PostM (l.mapM f) (fun rs => rs.length = l.length) := by
  induction l with
  | nil => rw [List.mapM_nil]; exact post_pure (by simp)
  | cons hd tl ih =>
    rw [List.mapM_cons]
    exact post_bind_any (fun r =>
      post_bind ih (fun rs hrs => post_pure (by simp [hrs])))

/-- `mapM` preserves emptiness. Needed by the kinds that hold when a list is
    non-empty. -/
private theorem post_mapM_isEmpty [LawfulMonad m] (l : List α) (f : α → m β) :
    PostM (l.mapM f) (fun rs => rs.isEmpty = l.isEmpty) :=
  post_mono (post_mapM_length l f) (fun rs h => by cases l <;> cases rs <;> simp_all)

/-- `Option.mapM` preserves presence. Needed by the kinds that hold when an option
    is `some`. -/
private theorem post_option_mapM_isSome [LawfulMonad m] (o : Option α) (f : α → m β) :
    PostM (o.mapM f) (fun r => r.isSome = o.isSome) := by
  cases o with
  | none => simp only [Option.mapM]; exact post_pure (by simp)
  | some v =>
    simp only [Option.mapM]
    exact post_map (post_mono MonadPost.postTrue (fun _ _ => by simp))

/-! ## Shape stability

`NodeKind.ofStmtExpr` reads one *child's* constructor: an `Old` wrapping a bare
local is `StmtExpr.Old.value.Var.Local`. A bottom-up traversal rewrites that
child, so the rebuilt `Old` can satisfy a kind its input did not — unless the
rewrite cannot manufacture a bare local out of something else. That is what
`ShapeStable` asks of a pass, and `mapStmtExprUsedM_isVarLocal` lifts it to the
whole traversal. -/

/-- A rewrite never turns a non-local into a bare local read. -/
@[expose] def ShapeStable {m : Type → Type} [Monad m] [MonadPost m]
    (f : Bool → StmtExprMd → m StmtExprMd) : Prop :=
  ∀ u e, PostM (f u e) (fun e' => isVarLocal e' → isVarLocal e)

/-- Shape stability lifts through the traversal. Only the top constructor
    matters, so this needs no recursion: the rebuilt node has the constructor of
    the input, and `f` is stable by assumption. -/
theorem mapStmtExprUsedM_isVarLocal {m : Type → Type} [Monad m] [LawfulMonad m] [MonadPost m]
    {f : Bool → StmtExprMd → m StmtExprMd}
    (hshape : ShapeStable f) (u : Bool) (e : StmtExprMd) :
    PostM (mapStmtExprUsedM f u e) (fun e' => isVarLocal e' → isVarLocal e) := by
  rw [mapStmtExprUsedM.eq_def]
  simp only []
  split <;>
    repeat' first
      | exact post_bind (Q := fun r => isVarLocal r → isVarLocal e)
          (post_pure (by simp [isVarLocal]))
          (fun x hx => post_mono (hshape u x) (fun r hr h => hx (hr h)))
      | refine post_bind_any (fun _ => ?_)

/-! ## The generic traversal lemma -/

/-- What `mapStmtExprUsedM` hands to `f`: a node whose own kinds and type
    annotations still come from the *input* set `s` (the traversal does not touch
    them), but whose children have already been rewritten and so are in the
    *output* set `t`. -/
@[expose] def Rebuilt (s t : KindSet) (e : StmtExprMd) : Prop :=
  (∀ k ∈ NodeKind.ofStmtExpr e.val, k ∈ s)
    ∧ (∀ ty ∈ stmtExprTypes e.val, ContainsType s ty)
    ∧ (∀ c ∈ stmtExprChildren e.val, Contains t c)

/-- `List.attach` preserves emptiness. -/
private theorem attach_isEmpty {α : Type} (l : List α) : l.attach.isEmpty = l.isEmpty := by
  cases l <;> simp

/-- `Option.attach` preserves presence. -/
private theorem option_attach_isSome {α : Type} (o : Option α) : o.attach.isSome = o.isSome := by
  cases o <;> simp [Option.attach]

/-- Every kind in the output of a bottom-up traversal is in `t`, provided the
    input's kinds are in `s` and the rewrite `f` maps each rebuilt node into `t`
    (`hf`) without manufacturing bare local reads (`hshape`, needed only for
    `StmtExpr.Old.value.Var.Local` — see `ShapeStable`).

    By induction on the `Contains` derivation, following the traversal arm for
    arm. -/
theorem mapStmtExprUsedM_contains {m : Type → Type} [Monad m] [LawfulMonad m] [MonadPost m]
    (f : Bool → StmtExprMd → m StmtExprMd)
    (s t : KindSet) (hf : ∀ u e, Rebuilt s t e → PostM (f u e) (Contains t))
    (hshape : ShapeStable f)
    {e : StmtExprMd} (h : Contains s e) :
    ∀ u : Bool, PostM (mapStmtExprUsedM f u e) (Contains t) := by
  induction h with
  | node e head types kids ih =>
    intro u
    obtain ⟨v, src⟩ := e
    simp only [] at head types kids ih
    rw [mapStmtExprUsedM.eq_def]
    simp only []
    -- Most arms peel their children with `ih` and close with `hf`. Six need more,
    -- and are proved by hand below: `Return`, `Call` and `Try` (a kind of theirs depends on
    -- a list being non-empty / an option being present, so the rebuilt node needs
    -- `mapM`'s preservation of that), `Assign` and `Try` again (children sit inside a
    -- `Variable` / `CatchClause`, so the per-element postcondition is not just
    -- `Contains t`), the non-field `CompoundAssign` (its target is copied) and `Old`
    -- (shape stability). The `h_N` tags below are `split`'s arm numbers; they shift
    -- if `mapStmtExprUsedM`'s arms are reordered, and the build says so when they do.
    split
    all_goals (try ((repeat' first
        | exact post_bind (Q := Rebuilt s t)
            (post_pure ⟨by first
                | (simp [NodeKind.ofStmtExpr, NodeKind.ofVariable]; done)
                | simpa [NodeKind.ofStmtExpr, NodeKind.ofVariable] using head,
              by first
                | (simp [stmtExprTypes, variableTypes]; done)
                | simpa [stmtExprTypes, variableTypes] using types,
              by grind [stmtExprChildren, variableChildren]⟩)
            (fun x hx => hf u x hx)
        | refine post_bind (ih _ (by simp [stmtExprChildren, variableChildren]) _)
            (fun _ _ => ?_)
        | refine post_bind (post_and
            (post_attach_mapM _ _ (fun x => ih x.1 (by
              have hx := x.2
              first
                | simp_all [stmtExprChildren]
                | (simp only [stmtExprChildren]; grind)) _))
            (post_mapM_length _ _)) (fun _ _ => ?_)
        | refine post_bind (post_mapIdxM _ _ (fun i x => ih x.1 (by
              have hx := x.2
              first
                | simp_all [stmtExprChildren]
                | (simp only [stmtExprChildren]; grind)) _)) (fun _ _ => ?_)
        | refine post_bind (post_and
            (post_option_attach_mapM _ _ (fun x => ih x.1 (by
              have hx := x.2
              first
                | simp_all [stmtExprChildren]
                | (simp only [stmtExprChildren]; grind)) _))
            (post_option_mapM_isSome _ _)) (fun _ _ => ?_)); done))
    -- `Block`: `StmtExpr.Block.invariants.cons` and `.decreases.some` hold of the
    -- rebuilt node because `mapM` preserves length and `Option.mapM` presence.
    case h_2 stmts label invs dec =>
      refine post_bind (post_and
        (post_attach_mapM _ _ (fun x => ih x.1 (by
          have hx := x.2
          simp only [stmtExprChildren, List.mem_append, Option.mem_toList]
          exact Or.inl (Or.inl hx)) true))
        (post_mapM_length _ _)) (fun invs' hinvs' => ?_)
      refine post_bind (post_and
        (post_option_attach_mapM _ _ (fun x => ih x.1 (by
          have hx := Option.mem_def.mp x.2
          simp [stmtExprChildren, hx]) true))
        (post_option_mapM_isSome _ _)) (fun dec' hdec' => ?_)
      refine post_bind (post_mapIdxM _ _ (fun i x => ih x.1 (by
          have hx := x.2
          simp only [stmtExprChildren, List.mem_append]
          exact Or.inr hx) _)) (fun stmts' hstmts' => ?_)
      refine post_bind (Q := Rebuilt s t) (post_pure ⟨?_, ?_, ?_⟩) (fun x hx => hf u x hx)
      · have hLen : invs'.length = invs.length := by simpa using hinvs'.2
        have hSome : dec'.isSome = dec.isSome := by
          simpa [option_attach_isSome] using hdec'.2
        have hEmpty : invs'.isEmpty = invs.isEmpty := by
          cases invs <;> cases invs' <;> simp_all
        intro k hk
        exact head k (by simpa [NodeKind.ofStmtExpr, hEmpty, hSome] using hk)
      · simp [stmtExprTypes]
      · intro c hc
        simp only [stmtExprChildren, List.mem_append, Option.mem_toList] at hc
        rcases hc with (hc | hc) | hc
        · exact hinvs'.1 c hc
        · exact hdec'.1 c hc
        · exact hstmts' c hc
    -- `Return`: `StmtExpr.Return.value.some` holds of the rebuilt node because
    -- `mapM` preserves emptiness.
    case h_4 values =>
      refine post_bind (post_and
        (post_attach_mapM _ _ (fun x => ih x.1 (by
          have hx := x.2; simp [stmtExprChildren, hx]) true))
        (post_mapM_isEmpty _ _)) (fun values' hvalues' => ?_)
      refine post_bind (Q := Rebuilt s t) (post_pure ⟨?_, ?_, ?_⟩) (fun x hx => hf u x hx)
      · have hEmpty : values'.isEmpty = values.isEmpty := by
          simpa [attach_isEmpty] using hvalues'.2
        intro k hk
        exact head k (by simpa [NodeKind.ofStmtExpr, hEmpty] using hk)
      · simp [stmtExprTypes]
      · intro c hc
        simp only [stmtExprChildren] at hc
        exact hvalues'.1 c hc
    -- `Call`: `StmtExpr.Call.receiver?.some` holds of the rebuilt node because
    -- `Option.mapM` preserves presence.
    case h_17 receiver? callee args tyArgs =>
      refine post_bind (post_and
        (post_option_attach_mapM _ _ (fun x => ih x.1 (by
          have hx := x.2
          simp only [stmtExprChildren, List.mem_append, Option.mem_toList]
          exact Or.inl (Option.mem_def.mp hx)) true))
        (post_option_mapM_isSome _ _)) (fun recv' hrecv' => ?_)
      refine post_bind (post_attach_mapM _ _ (fun x => ih x.1 (by
          have hx := x.2
          simp only [stmtExprChildren, List.mem_append]
          exact Or.inr hx) true)) (fun args' hargs' => ?_)
      refine post_bind (Q := Rebuilt s t) (post_pure ⟨?_, ?_, ?_⟩) (fun x hx => hf u x hx)
      · have hSome : recv'.isSome = receiver?.isSome := by
          simpa [option_attach_isSome] using hrecv'.2
        intro k hk
        refine head k ?_
        cases receiver? <;> cases recv' <;> simp_all [NodeKind.ofStmtExpr]
      · simpa [stmtExprTypes] using types
      · intro c hc
        simp only [stmtExprChildren, List.mem_append, Option.mem_toList] at hc
        rcases hc with hc | hc
        · exact hrecv'.1 c hc
        · exact hargs' c hc
    -- `Assign`: a target's rewritten child sits inside a `Variable`, so the
    -- per-target postcondition covers that `Variable`'s own types and children.
    case h_8 targets value =>
      refine post_bind (post_attach_mapM
        (P := fun v' => (∀ ty ∈ variableTypes v'.val, ContainsType s ty)
          ∧ (∀ c ∈ variableChildren v'.val, Contains t c)) _ _ (fun x => ?_))
        (fun _targets' htargets' => ?_)
      · obtain ⟨⟨tv, ts⟩, hmem⟩ := x
        cases tv with
        | Field target fieldName =>
          refine post_bind (ih target (by
            simp only [stmtExprChildren, List.mem_append, List.mem_flatMap]
            exact Or.inl ⟨_, hmem, by simp [variableChildren]⟩) true) (fun target' htarget' => ?_)
          exact post_pure ⟨by simp [variableTypes], by
            intro c hc
            simp only [variableChildren, List.mem_singleton] at hc
            exact hc ▸ htarget'⟩
        | Local name =>
          exact post_pure ⟨by simp [variableTypes], by simp [variableChildren]⟩
        | Declare parameter =>
          refine post_pure ⟨?_, by simp [variableChildren]⟩
          intro ty hty
          exact types ty (by
            simp only [stmtExprTypes, List.mem_flatMap]
            exact ⟨_, hmem, hty⟩)
        | Stack type =>
          refine post_pure ⟨?_, by simp [variableChildren]⟩
          intro ty hty
          exact types ty (by
            simp only [stmtExprTypes, List.mem_flatMap]
            exact ⟨_, hmem, hty⟩)
      · refine post_bind (ih value (by simp [stmtExprChildren]) true) (fun value' hvalue' => ?_)
        refine post_bind (Q := Rebuilt s t) (post_pure ⟨?_, ?_, ?_⟩) (fun x hx => hf u x hx)
        · simpa [NodeKind.ofStmtExpr] using head
        · intro ty hty
          simp only [stmtExprTypes, List.mem_flatMap] at hty
          obtain ⟨tgt, hmem, hty⟩ := hty
          exact (htargets' tgt hmem).1 ty hty
        · intro c hc
          simp only [stmtExprChildren, List.mem_append, List.mem_flatMap,
            List.mem_singleton] at hc
          rcases hc with ⟨tgt, hmem, hc⟩ | hc
          · exact (htargets' tgt hmem).2 c hc
          · exact hc ▸ hvalue'
    -- Non-field `CompoundAssign`: the target is passed through, so the negative
    -- pattern hypothesis is what says it has no children.
    case h_15 op target rhs hne =>
      obtain ⟨tv, ts⟩ := target
      cases tv
      case Field tgt fieldName => exact absurd rfl (hne tgt fieldName ts)
      all_goals
        refine post_bind (ih rhs (by simp [stmtExprChildren, variableChildren]) true)
          (fun rhs' hrhs' => ?_)
        refine post_bind (Q := Rebuilt s t) (post_pure ⟨?_, ?_, ?_⟩) (fun x hx => hf u x hx)
        · first
            | (simp [NodeKind.ofStmtExpr]; done)
            | simpa [NodeKind.ofStmtExpr] using head
        · first
            | (simp [stmtExprTypes, variableTypes]; done)
            | simpa [stmtExprTypes, variableTypes] using types
        · intro c hc
          simp only [stmtExprChildren, variableChildren, List.mem_singleton,
            List.nil_append] at hc
          exact hc ▸ hrhs'
    -- `Old`: `StmtExpr.Old.value.Var.Local` reads the child's constructor, so it
    -- transfers to the rebuilt node only because `f` is `ShapeStable`.
    case h_23 value label? =>
      refine post_bind (post_and (ih value (by simp [stmtExprChildren]) true)
        (mapStmtExprUsedM_isVarLocal hshape true value)) (fun value' hvalue' => ?_)
      refine post_bind (Q := Rebuilt s t) (post_pure ⟨?_, ?_, ?_⟩) (fun x hx => hf u x hx)
      · intro k hk
        refine head k ?_
        simp only [NodeKind.ofStmtExpr] at hk ⊢
        rcases List.mem_append.mp hk with h1 | h1
        · exact List.mem_append_left _ h1
        · refine List.mem_append_right _ ?_
          by_cases hv : isVarLocal value' = true
          · simp only [hvalue'.2 hv]
            simpa [hv] using h1
          · simp only [Bool.not_eq_true] at hv
            simp [hv] at h1
      · simp [stmtExprTypes]
      · intro c hc
        simp only [stmtExprChildren, List.mem_singleton] at hc
        exact hc ▸ hvalue'.1
    -- `Try`: children sit inside `CatchClause`es, whose `bindingType` is also a
    -- type annotation the node carries.
    case h_30 body catches finally? =>
      refine post_bind (ih body (by simp [stmtExprChildren]) false) (fun body' hbody' => ?_)
      refine post_bind (post_attach_mapM
        (P := fun c' => ContainsType s c'.bindingType
          ∧ (∀ e ∈ c'.predicate, Contains t e) ∧ Contains t c'.body) _ _ (fun x => ?_))
        (fun catches' hcatches' => ?_)
      · obtain ⟨c, hmem⟩ := x
        refine post_bind (post_option_attach_mapM _ _ (fun y => ih y.1 (by
          have hy := y.2
          simp only [stmtExprChildren, List.mem_append, List.mem_flatMap, List.mem_cons,
            Option.mem_toList, List.not_mem_nil, or_false]
          exact Or.inl (Or.inr ⟨c, hmem, Or.inl (Option.mem_def.mp hy)⟩)) true))
          (fun pred' hpred' => ?_)
        refine post_bind (ih c.body (by
          simp only [stmtExprChildren, List.mem_append, List.mem_flatMap, List.mem_cons,
            Option.mem_toList, List.not_mem_nil, or_false]
          exact Or.inl (Or.inr ⟨c, hmem, Or.inr rfl⟩)) false) (fun cbody' hcbody' => ?_)
        exact post_pure ⟨types c.bindingType (by
            simp only [stmtExprTypes, List.mem_map]
            exact ⟨c, hmem, rfl⟩), hpred', hcbody'⟩
      · refine post_bind (post_and
          (post_option_attach_mapM _ _ (fun x => ih x.1 (by
            have hx := x.2
            simp only [stmtExprChildren, List.mem_append, Option.mem_toList]
            exact Or.inr (Option.mem_def.mp hx)) false))
          (post_option_mapM_isSome _ _)) (fun fin' hfin' => ?_)
        refine post_bind (Q := Rebuilt s t) (post_pure ⟨?_, ?_, ?_⟩) (fun x hx => hf u x hx)
        · have hSome : fin'.isSome = finally?.isSome := by
            simpa [option_attach_isSome] using hfin'.2
          simpa [NodeKind.ofStmtExpr, hSome] using head
        · intro ty hty
          simp only [stmtExprTypes, List.mem_map] at hty
          obtain ⟨c, hmem, hty⟩ := hty
          exact hty ▸ (hcatches' c hmem).1
        · intro c hc
          simp only [stmtExprChildren, List.mem_append, List.mem_cons, List.mem_flatMap,
            Option.mem_toList, List.not_mem_nil, or_false] at hc
          rcases hc with (hc | ⟨cl, hmem, hc⟩) | hc
          · exact hc ▸ hbody'
          · rcases hc with hc | hc
            · exact (hcatches' cl hmem).2.1 c hc
            · exact hc ▸ (hcatches' cl hmem).2.2
          · exact hfin'.1 c hc

/-- A `mapM` result is empty only if its input was. -/
theorem ne_nil_of_length {α β : Type} {l' : List β} {l : List α}
    (hlen : l'.length = l.length) (h : l' ≠ []) : l ≠ [] := by
  cases l' <;> cases l <;> simp_all

/-! ## Properties of `HighType.mapType`

Universal properties of the `HighType` traversal, stated over every
constructor: `mapType_id`, `mapType_substUserDefined_names` and
`mapType_substUserDefined_eq`. The latter two are stated with
`HighType.userDefinedNames`, `HighType.substUserDefined` and the recursive
specification `HighType.substUserDefinedAll`. -/

/-- All `UserDefined` names occurring anywhere in a `HighType`. -/
def HighType.userDefinedNames (ty : HighType) : List String :=
  match ty with
  | .UserDefined n => [n.text]
  | .TSet e => HighType.userDefinedNames e.val
  | .TMap k v => HighType.userDefinedNames k.val ++ HighType.userDefinedNames v.val
  | .Applied base args =>
    HighType.userDefinedNames base.val
      ++ args.flatMap fun a => HighType.userDefinedNames a.val
  | .Intersection tys => tys.flatMap fun t => HighType.userDefinedNames t.val
  | .MultiValuedExpr tys => tys.flatMap fun t => HighType.userDefinedNames t.val
  | _ => []
  termination_by SizeOf.sizeOf ty
  decreasing_by
    all_goals first
      | (cases e; term_by_mem)
      | (cases k; term_by_mem)
      | (cases v; term_by_mem)
      | (cases base; term_by_mem)
      | (cases b; term_by_mem)
      | (cases a; term_by_mem)
      | (cases t; term_by_mem)
      | term_by_mem

/-- Leaf-substitution callback for `mapType`: rewrite `UserDefined` leaves via
    `g`, leave every other constructor unchanged. This is the callback shape
    `ConstrainedTypeElim.resolveBaseType` instantiates. -/
def HighType.substUserDefined (g : Identifier → HighType) : HighType → HighType
  | .UserDefined n => g n
  | t => t

/-- **Identity law**: `mapType` with the identity callback rebuilds every
    constructor unchanged. Subsumes any per-constructor "the traversal
    preserves structure" example test. -/
theorem mapType_id (ty : HighType) : HighType.mapType (fun t => t) ty = ty := by
  fun_induction HighType.mapType (fun t => t) ty with
  | case1 e ih => cases e; simp_all
  | case2 k v ih1 ih2 => cases k; cases v; simp_all
  | case3 base args ihbase ihargs =>
    cases base
    show HighType.Applied _ _ = _
    congr 1
    · simp_all
    · rw [List.map_congr_left fun a ha => by rw [ihargs a ha]]
      exact List.map_id' args
  | case4 tys ih =>
    show HighType.Intersection _ = _
    congr 1
    rw [List.map_congr_left fun t ht => by rw [ih t ht]]
    exact List.map_id' tys
  | case5 tys ih =>
    show HighType.MultiValuedExpr _ = _
    congr 1
    rw [List.map_congr_left fun t ht => by rw [ih t ht]]
    exact List.map_id' tys
  | case6 => rfl

/-- **Name-elimination**: for a leaf-substitution callback, every `UserDefined`
    name in the traversal's output satisfies any predicate `p` that holds on
    the callback's image. Instantiating `p := (· ∉ constrainedNames)` gives:
    after a `resolveBaseType`-style lowering, no constrained-type reference
    survives under **any** constructor — the universal form of per-constructor
    `.TSet`/`.TMap`/`.Intersection`/`.MultiValuedExpr`/`.Applied`
    lowering tests. -/
theorem mapType_substUserDefined_names (p : String → Prop)
    (g : Identifier → HighType)
    (hg : ∀ n, ∀ n' ∈ (g n).userDefinedNames, p n')
    (ty : HighType) :
    ∀ n' ∈ (HighType.mapType (HighType.substUserDefined g) ty).userDefinedNames, p n' := by
  fun_induction HighType.mapType (HighType.substUserDefined g) ty with
  | case1 e ih =>
    intro n' hn'
    simp only [HighType.substUserDefined, HighType.userDefinedNames] at hn'
    exact ih n' hn'
  | case2 k v ih1 ih2 =>
    intro n' hn'
    simp only [HighType.substUserDefined, HighType.userDefinedNames, List.mem_append] at hn'
    rcases hn' with h | h
    · exact ih1 n' h
    · exact ih2 n' h
  | case3 base args ihbase ihargs =>
    intro n' hn'
    simp only [HighType.substUserDefined, HighType.userDefinedNames, List.mem_append,
      List.flatMap_map, List.mem_flatMap] at hn'
    rcases hn' with h | ⟨a, ha, h⟩
    · exact ihbase n' h
    · exact ihargs a ha n' h
  | case4 tys ih =>
    intro n' hn'
    simp only [HighType.substUserDefined, HighType.userDefinedNames,
      List.flatMap_map, List.mem_flatMap] at hn'
    obtain ⟨t, ht, h⟩ := hn'
    exact ih t ht n' h
  | case5 tys ih =>
    intro n' hn'
    simp only [HighType.substUserDefined, HighType.userDefinedNames,
      List.flatMap_map, List.mem_flatMap] at hn'
    obtain ⟨t, ht, h⟩ := hn'
    exact ih t ht n' h
  | case6 ty h1 h2 h3 h4 h5 =>
    intro n' hn'
    match ty, h1, h2, h3, h4, h5 with
    | .UserDefined n, _, _, _, _, _ =>
      simp only [HighType.substUserDefined] at hn'
      exact hg n n' hn'
    | .TVoid, _, _, _, _, _ | .TBool, _, _, _, _, _ | .TInt, _, _, _, _, _
    | .TFloat64, _, _, _, _, _ | .TReal, _, _, _, _, _ | .TString, _, _, _, _, _
    | .TBv _, _, _, _, _, _ | .TVar _, _, _, _, _, _ | .Unknown, _, _, _, _, _ =>
      simp [HighType.substUserDefined, HighType.userDefinedNames] at hn'
    | .TSet e, h1, _, _, _, _ => exact absurd rfl (h1 e)
    | .TMap k v, _, h2, _, _, _ => exact absurd rfl (h2 k v)
    | .Applied b as, _, _, h3, _, _ => exact absurd rfl (h3 b as)
    | .Intersection ts, _, _, _, h4, _ => exact absurd rfl (h4 ts)
    | .MultiValuedExpr ts, _, _, _, _, h5 => exact absurd rfl (h5 ts)

/-- **Specification** for recursive leaf substitution: apply `g` to every
    `UserDefined` leaf, recurse through all component types, and preserve every
    other constructor together with its source annotations. Deliberately
    written as a direct recursion (no traversal combinator, no callback applied
    at interior nodes) so that `mapType_substUserDefined_eq` pins `mapType`'s
    output against an independently auditable definition. -/
def HighType.substUserDefinedAll (g : Identifier → HighType) (ty : HighType) : HighType :=
  match ty with
  | .UserDefined n => g n
  | .TSet e => .TSet ⟨HighType.substUserDefinedAll g e.val, e.source⟩
  | .TMap k v =>
    .TMap ⟨HighType.substUserDefinedAll g k.val, k.source⟩
          ⟨HighType.substUserDefinedAll g v.val, v.source⟩
  | .Applied base args =>
    .Applied ⟨HighType.substUserDefinedAll g base.val, base.source⟩
      (args.map fun a => ⟨HighType.substUserDefinedAll g a.val, a.source⟩)
  | .Intersection tys =>
    .Intersection (tys.map fun t => ⟨HighType.substUserDefinedAll g t.val, t.source⟩)
  | .MultiValuedExpr tys =>
    .MultiValuedExpr (tys.map fun t => ⟨HighType.substUserDefinedAll g t.val, t.source⟩)
  | t => t
  termination_by SizeOf.sizeOf ty
  decreasing_by
    all_goals first
      | (cases e; term_by_mem)
      | (cases k; term_by_mem)
      | (cases v; term_by_mem)
      | (cases base; term_by_mem)
      | (cases b; term_by_mem)
      | (cases a; term_by_mem)
      | (cases t; term_by_mem)
      | term_by_mem

/-- **Output characterization**: `mapType` with a leaf-substitution callback
    computes exactly the recursive substitution `substUserDefinedAll` — every
    constructor and source annotation preserved, every `UserDefined` leaf
    replaced by the callback's value, at every depth. This pins the concrete
    output for every input (per-constructor `#guard`s are instances), not just
    a property of it. -/
theorem mapType_substUserDefined_eq (g : Identifier → HighType) (ty : HighType) :
    HighType.mapType (HighType.substUserDefined g) ty
      = HighType.substUserDefinedAll g ty := by
  fun_induction HighType.mapType (HighType.substUserDefined g) ty with
  | case1 e ih =>
    simp [HighType.substUserDefined, HighType.substUserDefinedAll, ih]
  | case2 k v ih1 ih2 =>
    simp [HighType.substUserDefined, HighType.substUserDefinedAll, ih1, ih2]
  | case3 base args ihbase ihargs =>
    show HighType.Applied _ _ = _
    simp only [HighType.substUserDefinedAll]
    congr 1
    · simp [ihbase]
    · exact List.map_congr_left fun a ha => by rw [ihargs a ha]
  | case4 tys ih =>
    show HighType.Intersection _ = _
    simp only [HighType.substUserDefinedAll]
    congr 1
    exact List.map_congr_left fun t ht => by rw [ih t ht]
  | case5 tys ih =>
    show HighType.MultiValuedExpr _ = _
    simp only [HighType.substUserDefinedAll]
    congr 1
    exact List.map_congr_left fun t ht => by rw [ih t ht]
  | case6 ty h1 h2 h3 h4 h5 =>
    match ty, h1, h2, h3, h4, h5 with
    | .UserDefined n, _, _, _, _, _ =>
      simp [HighType.substUserDefined, HighType.substUserDefinedAll]
    | .TVoid, _, _, _, _, _ | .TBool, _, _, _, _, _ | .TInt, _, _, _, _, _
    | .TFloat64, _, _, _, _, _ | .TReal, _, _, _, _, _ | .TString, _, _, _, _, _
    | .TBv _, _, _, _, _, _ | .TVar _, _, _, _, _, _ | .Unknown, _, _, _, _, _ =>
      simp [HighType.substUserDefined, HighType.substUserDefinedAll]
    | .TSet e, h1, _, _, _, _ => exact absurd rfl (h1 e)
    | .TMap k v, _, h2, _, _, _ => exact absurd rfl (h2 k v)
    | .Applied b as, _, _, h3, _, _ => exact absurd rfl (h3 b as)
    | .Intersection ts, _, _, _, h4, _ => exact absurd rfl (h4 ts)
    | .MultiValuedExpr ts, _, _, _, _, h5 => exact absurd rfl (h5 ts)

end -- public section

end Strata.Laurel
