/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelAST
public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.Resolution
import all Strata.Languages.Laurel.Resolution
import all Strata.Languages.Laurel.MapStmtExpr

/-! # Resolution Properties

Key theorem: `resolve_fullyAnnotated'` — the resolution pass establishes the
fully-annotated invariant. On any input program `p`,
`validateFullyAnnotated (resolve p).program = []`: every `Declare` node in the
resolved output carries a `some ty` annotation (see the Var-Declare and
Decl-Synth rules in `Resolution.lean`, whose `.Declare` arms rewrite the
annotation to `some _` on every path).

The theorem is *conditional* on two master facts about the `Synth`/`Check`
dispatchers (every tree they emit is `Clean`); those are stated as the
commented `master` lemma at the bottom of the file, whose proof elaborates
but is currently too expensive to check into the build (see the TODO there).
Everything else — the traversal decomposition and the entire lift from the
dispatchers to `resolve` — is fully proven.

The proof is organized in three layers:

1. **The `Emits` calculus** (`CollectEmits`) — `collectStmtExprList` is a
   `StateM (List β)` fold; `Emits a out` says action `a` appends exactly
   `out` to any starting accumulator. This yields the per-constructor
   decomposition `collect_unfold` of `collectStmtExprList`, and hence
   `clean_iff` for the `Clean` predicate ("this tree has no unannotated
   `Declare`").

2. **The `PostM` calculus** (`ResolutionClean`) — state-independent value
   postconditions on `ResolveM` actions, with bind/pure/mapM/withScope
   combinators, plus `varDeclare_clean`, the crux single-rule fact that
   `Check.varDeclare` always emits an annotated `Declare`.

3. **Plumbing** — assuming the master facts as section hypotheses, `Clean`
   is lifted through `resolveBody` / `resolveProcedure` /
   `resolveInstanceProcedure` / `resolveTypeDefinition` / `resolveConstant`,
   and matched against the trees `validateFullyAnnotated` walks (via the
   `KeepsState` calculus over `mapProcedureM`), concluding in
   `resolve_fullyAnnotated'`.

The per-procedure obligation is `CleanProcFields`, which ranges over every
expression-bearing specification field `mapProcedureM` walks — including a
procedure's exceptional contract. Two results carry that last part:

- `CleanThrowsOnBlock` — the cleanliness of one `throwsOn` behavior case: its
  guard, each of its case postconditions, and each of its frame targets. Needed
  to read the `CleanProcFields` statement.
- `resolveExceptionalContract_clean` — `resolveExceptionalContract` produces
  clean cases, and so supplies the exceptional component of `CleanProcFields`
  for both `resolveProcedure_clean` and `resolveInstanceProcedure_clean`.
-/

namespace Strata.Laurel

public section

/-! ## Layer 1: the Emits calculus for `collectStmtExprList` -/

namespace CollectEmits

/-- A `StateM (List β)` action `a` *emits* `out`: running it from any
    accumulator appends exactly `out`. -/
def Emits {β : Type} (a : StateM (List β) Unit) (out : List β) : Prop :=
  ∀ acc, (a acc).2 = acc ++ out

/-- An action is prefix-independent: it has *some* emission. -/
def HasEmits {β : Type} (a : StateM (List β) Unit) : Prop :=
  ∃ out, Emits a out

theorem emits_modify {β : Type} (xs : List β) :
    Emits (modify (· ++ xs)) xs := fun _ => rfl

theorem emits_pure {β : Type} : Emits (pure () : StateM (List β) Unit) [] := by
  intro acc; simp [pure, StateT.pure]

theorem emits_seq {β : Type} {a b : StateM (List β) Unit} {xs ys : List β}
    (ha : Emits a xs) (hb : Emits b ys) :
    Emits (do a; b) (xs ++ ys) := by
  intro acc
  simp only [bind, StateT.bind]
  have h1 := ha acc
  cases hrun : a acc with
  | mk u s1 =>
    have hs1 : s1 = acc ++ xs := by rw [hrun] at h1; exact h1
    subst hs1
    have h2 := hb (acc ++ xs)
    simp [h2, List.append_assoc]

/-- Emission output is unique (run from `[]` and cancel). -/
theorem emits_unique {β : Type} {a : StateM (List β) Unit} {out₁ out₂ : List β}
    (h₁ : Emits a out₁) (h₂ : Emits a out₂) : out₁ = out₂ := by
  have e1 := h₁ []
  have e2 := h₂ []
  simp only [List.nil_append] at e1 e2
  rw [← e1, ← e2]

theorem hasEmits_pure {β : Type} : HasEmits (pure () : StateM (List β) Unit) :=
  ⟨[], emits_pure⟩

theorem hasEmits_modify {β : Type} (xs : List β) :
    HasEmits (modify (· ++ xs)) := ⟨xs, emits_modify xs⟩

theorem hasEmits_seq {β : Type} {a b : StateM (List β) Unit}
    (ha : HasEmits a) (hb : HasEmits b) : HasEmits (do a; b) := by
  obtain ⟨xs, hx⟩ := ha; obtain ⟨ys, hy⟩ := hb
  exact ⟨xs ++ ys, emits_seq hx hy⟩

theorem emits_forM {α β : Type} (l : List α) (g : α → StateM (List β) Unit)
    (out : α → List β) (h : ∀ x ∈ l, Emits (g x) (out x)) :
    Emits (l.forM g) (l.flatMap out) := by
  induction l with
  | nil => intro acc; simpa using emits_pure (β := β) acc
  | cons hd tl ih =>
    have hhd := h hd (by simp)
    have htl := ih (fun x hx => h x (by simp [hx]))
    intro acc
    have := emits_seq hhd htl acc
    simpa [List.forM_cons, List.flatMap_cons] using this

/-- `attach.forM` variant: the traversals iterate `l.attach.forM`. -/
theorem emits_attach_forM {α β : Type} (l : List α)
    (g : {x // x ∈ l} → StateM (List β) Unit)
    (out : α → List β) (h : ∀ x, Emits (g x) (out x.val)) :
    Emits (l.attach.forM g) (l.flatMap out) := by
  have := emits_forM l.attach g (fun x => out x.val) (fun x _ => h x)
  simpa using this

theorem emits_option_attach_forM {α β : Type} (o : Option α)
    (g : {x // o = some x} → StateM (List β) Unit)
    (out : α → List β) (h : ∀ x, Emits (g x) (out x.val)) :
    Emits (o.attach.forM g) (o.elim [] out) := by
  cases o with
  | none => intro acc; simpa using emits_pure (β := β) acc
  | some v =>
    intro acc
    have := h ⟨v, rfl⟩ acc
    simpa [Option.attach, Option.forM] using this

theorem hasEmits_forM {α β : Type} (l : List α) (g : α → StateM (List β) Unit)
    (h : ∀ x ∈ l, HasEmits (g x)) : HasEmits (l.forM g) := by
  induction l with
  | nil => exact hasEmits_pure
  | cons hd tl ih =>
    have hhd := h hd (by simp)
    have htl := ih (fun x hx => h x (by simp [hx]))
    obtain ⟨xs, hx⟩ := hhd; obtain ⟨ys, hy⟩ := htl
    exact ⟨xs ++ ys, by simpa [List.forM_cons] using emits_seq hx hy⟩

theorem hasEmits_attach_forM {α β : Type} (l : List α)
    (g : {x // x ∈ l} → StateM (List β) Unit)
    (h : ∀ x, HasEmits (g x)) : HasEmits (l.attach.forM g) :=
  hasEmits_forM l.attach g (fun x _ => h x)

theorem hasEmits_option_attach_forM {α β : Type} (o : Option α)
    (g : {x // o = some x} → StateM (List β) Unit)
    (h : ∀ x, HasEmits (g x)) : HasEmits (o.attach.forM g) := by
  cases o with
  | none => exact hasEmits_pure
  | some v =>
    obtain ⟨xs, hx⟩ := h ⟨v, rfl⟩
    exact ⟨xs, by simpa [Option.attach, Option.forM] using hx⟩

/-- The per-node visitor that phrases `collectStmtExprList` monadically. -/
def collectVisitor {β : Type} (g : StmtExprMd → List β) :
    StmtExprMd → StateM (List β) Unit :=
  fun n => modify (· ++ g n)

/-- Every fold action is prefix-independent. -/
theorem fold_hasEmits {β : Type} (g : StmtExprMd → List β) (e : StmtExprMd) :
    HasEmits (foldStmtExprM (m := StateM (List β)) (collectVisitor g) e) := by
  fun_induction foldStmtExprM (m := StateM (List β)) (collectVisitor g) e
  apply hasEmits_seq (hasEmits_modify _)
  split
  all_goals
    repeat'
      first
      | apply hasEmits_seq
      | apply hasEmits_pure
      | apply hasEmits_attach_forM
      | apply hasEmits_option_attach_forM
      | (solve | (intro x; solve_by_elim [x.property]))
      | (solve | (rintro ⟨⟨v, vsrc⟩, hmem⟩
                  cases v <;> dsimp only <;>
                    solve_by_elim [hasEmits_pure, hmem]))
      -- A `Try`'s catch clause is a structure rather than an `AstNode`, so the
      -- element pattern above does not fit: destructure the clause and discharge
      -- its optional guard and its handler body separately.
      | (solve | (rintro ⟨c, hmem⟩
                  refine hasEmits_seq ?_ ?_
                  · refine hasEmits_option_attach_forM _ _ ?_
                    rintro ⟨e, he⟩
                    solve_by_elim [hasEmits_pure, hmem, he]
                  · solve_by_elim [hasEmits_pure, hmem]))
      | split
      | solve_by_elim

/-- Bridge: whatever the fold emits *is* `collectStmtExprList`. -/
theorem collect_eq_of_emits {β : Type} (g : StmtExprMd → List β) (e : StmtExprMd)
    {out : List β}
    (h : Emits (foldStmtExprM (m := StateM (List β)) (collectVisitor g) e) out) :
    collectStmtExprList g e = out := by
  have := h []
  simpa [collectStmtExprList, foldStmtExpr, collectVisitor, StateT.run] using this

/-- The fold emits exactly the collected list. -/
theorem fold_emits {β : Type} (g : StmtExprMd → List β) (e : StmtExprMd) :
    Emits (foldStmtExprM (m := StateM (List β)) (collectVisitor g) e)
      (collectStmtExprList g e) := by
  obtain ⟨out, h⟩ := fold_hasEmits g e
  rwa [collect_eq_of_emits g e h]

end CollectEmits

open CollectEmits

/-! ## Layer 1b: per-constructor decomposition of `collectStmtExprList` -/

/-- The children contribution of one node, mirroring `foldStmtExprM`'s arms. -/
def childCollect {β : Type} (g : StmtExprMd → List β) (e : StmtExprMd) : List β :=
  match e.val with
  | .IfThenElse cond th el =>
    collectStmtExprList g cond ++ collectStmtExprList g th ++ el.elim [] (collectStmtExprList g)
  | .Block stmts _ => stmts.flatMap (collectStmtExprList g)
  | .While cond invs dec body _ =>
    collectStmtExprList g cond ++ invs.flatMap (collectStmtExprList g)
      ++ dec.elim [] (collectStmtExprList g) ++ collectStmtExprList g body
  | .Return v => v.elim [] (collectStmtExprList g)
  | .Assign targets value =>
    targets.flatMap (fun v => match v with
      | ⟨.Field target _, _⟩ => collectStmtExprList g target
      | _ => []) ++ collectStmtExprList g value
  | .Var (.Field target _) => collectStmtExprList g target
  | .IncrDecr _ _ target =>
    (match target with
     | ⟨.Field tgt _, _⟩ => collectStmtExprList g tgt
     | _ => [])
  | .CompoundAssign _ target rhs =>
    (match target with
     | ⟨.Field tgt _, _⟩ => collectStmtExprList g tgt
     | _ => []) ++ collectStmtExprList g rhs
  | .PureFieldUpdate target _ newValue =>
    collectStmtExprList g target ++ collectStmtExprList g newValue
  | .StaticCall _ args => args.flatMap (collectStmtExprList g)
  | .ReferenceEquals lhs rhs => collectStmtExprList g lhs ++ collectStmtExprList g rhs
  | .AsType target _ => collectStmtExprList g target
  | .IsType target _ => collectStmtExprList g target
  | .InstanceCall target _ args =>
    collectStmtExprList g target ++ args.flatMap (collectStmtExprList g)
  | .Quantifier _ _ trigger body =>
    trigger.elim [] (collectStmtExprList g) ++ collectStmtExprList g body
  | .Assigned name => collectStmtExprList g name
  | .Old value => collectStmtExprList g value
  | .Fresh value => collectStmtExprList g value
  | .Assert cond _ => collectStmtExprList g cond
  | .Assume cond => collectStmtExprList g cond
  | .Throw value => collectStmtExprList g value
  -- Mirrors `foldStmtExprM`'s `Try` arm: the body, then each catch clause's
  -- optional guard and handler body, then the `finally` arm. The `flatMap`/`elim`
  -- shapes line up with `emits_attach_forM` and `emits_option_attach_forM`.
  | .Try body catches finally? =>
    collectStmtExprList g body
      ++ catches.flatMap (fun c =>
           c.predicate.elim [] (collectStmtExprList g) ++ collectStmtExprList g c.body)
      ++ finally?.elim [] (collectStmtExprList g)
  | .ProveBy value proof => collectStmtExprList g value ++ collectStmtExprList g proof
  | .ContractOf _ func => collectStmtExprList g func
  | _ => []

theorem collect_unfold {β : Type} (g : StmtExprMd → List β) (e : StmtExprMd) :
    collectStmtExprList g e = g e ++ childCollect g e := by
  apply collect_eq_of_emits
  rw [foldStmtExprM.eq_def]
  apply emits_seq (emits_modify _)
  unfold childCollect
  split <;> rename_i heq <;> simp only [heq]
  all_goals
    repeat'
      first
      | rw [List.append_assoc]
      | apply emits_seq
      | exact emits_pure
      | exact fold_emits g _
      | (apply emits_attach_forM; intro x; exact fold_emits g _)
      | (apply emits_option_attach_forM; intro x; exact fold_emits g _)
      | (solve
          | (apply emits_attach_forM
             rintro ⟨⟨v, vsrc⟩, hmem⟩
             cases v <;> dsimp only <;>
               first
               | exact emits_pure
               | exact fold_emits g _))
      -- A `Try`'s catch clauses: each element is a structure whose traversal is
      -- itself a sequence (optional guard, then handler body), so it needs its own
      -- alternative rather than the single-fold element cases above.
      | (solve
          | (apply emits_attach_forM
             rintro ⟨c, hmem⟩
             refine emits_seq ?_ ?_ <;>
               first
               | (apply emits_option_attach_forM; intro x; exact fold_emits g _)
               | exact fold_emits g _
               | exact emits_pure))
      | (solve
          | (split <;> dsimp only <;>
               first
               | exact emits_pure
               | exact fold_emits g _))


/-! Clean corollaries -/

def Clean (e : StmtExprMd) : Prop :=
  collectStmtExprList unannotatedDeclares e = []

theorem clean_iff (e : StmtExprMd) :
    Clean e ↔ unannotatedDeclares e = [] ∧ childCollect unannotatedDeclares e = [] := by
  unfold Clean
  rw [collect_unfold]
  simp [List.append_eq_nil_iff]


/-! ## Layer 2: the `PostM` calculus for `ResolveM` postconditions -/

namespace ResolutionClean

open Resolution

def PostM {α : Type} (a : ResolveM α) (P : α → Prop) : Prop :=
  ∀ s, P (a s).1

theorem postM_pure {α : Type} {x : α} {P : α → Prop} (h : P x) :
    PostM (pure x) P := fun _ => h

theorem postM_bind {α β : Type} {a : ResolveM α} {f : α → ResolveM β}
    {Q : α → Prop} {P : β → Prop}
    (ha : PostM a Q) (hf : ∀ x, Q x → PostM (f x) P) :
    PostM (a >>= f) P := by
  intro s
  exact hf _ (ha s) ((a s).2)

theorem postM_bind_any {α β : Type} {a : ResolveM α} {f : α → ResolveM β}
    {P : β → Prop} (hf : ∀ x, PostM (f x) P) :
    PostM (a >>= f) P :=
  postM_bind (Q := fun _ => True) (fun _ => trivial) (fun x _ => hf x)

theorem postM_ite {α : Type} {c : Prop} [Decidable c] {a b : ResolveM α}
    {P : α → Prop} (ht : PostM a P) (he : PostM b P) :
    PostM (if c then a else b) P := by
  split <;> assumption

theorem postM_mono {α : Type} {a : ResolveM α} {P Q : α → Prop}
    (h : PostM a P) (imp : ∀ x, P x → Q x) : PostM a Q :=
  fun s => imp _ (h s)

theorem postM_map {α β : Type} {a : ResolveM α} {f : α → β} {P : β → Prop}
    (ha : PostM a (fun x => P (f x))) :
    PostM (f <$> a) P := by
  intro s
  have := ha s
  simpa [Functor.map, StateT.map] using this

/-- mapM: pointwise postcondition lifts to "all elements". -/
theorem postM_mapM {α β : Type} (l : List α) (f : α → ResolveM β) {P : β → Prop}
    (h : ∀ x ∈ l, PostM (f x) P) :
    PostM (l.mapM f) (fun rs => ∀ r ∈ rs, P r) := by
  induction l with
  | nil =>
    intro s
    simp [List.mapM, List.mapM.loop, pure, StateT.pure]
  | cons hd tl ih =>
    have hhd := h hd (by simp)
    have htl := ih (fun x hx => h x (by simp [hx]))
    rw [List.mapM_cons]
    exact postM_bind hhd (fun r hr =>
      postM_bind htl (fun rs hrs =>
        postM_pure (by
          intro x hx
          rcases List.mem_cons.mp hx with h1 | h2
          · exact h1 ▸ hr
          · exact hrs x h2)))

/-- attach.mapM variant. -/
theorem postM_attach_mapM {α β : Type} (l : List α)
    (f : {x // x ∈ l} → ResolveM β) {P : β → Prop}
    (h : ∀ x, PostM (f x) P) :
    PostM (l.attach.mapM f) (fun rs => ∀ r ∈ rs, P r) :=
  postM_mapM l.attach f (fun x _ => h x)

/-- Option.mapM. -/
theorem postM_option_mapM {α β : Type} (o : Option α) (f : α → ResolveM β) {P : β → Prop}
    (h : ∀ x, PostM (f x) P) :
    PostM (o.mapM f) (fun r => ∀ x ∈ r, P x) := by
  cases o with
  | none => intro s; simp [Option.mapM, pure, StateT.pure]
  | some v =>
    intro s
    have hv := h v s
    simp only [Option.mapM]
    show ∀ x ∈ ((f v >>= fun r => pure (some r) : ResolveM (Option β)) s).1, P x
    simp only [bind, StateT.bind, pure, StateT.pure]
    intro x hx
    cases hrun : f v s with
    | mk r s' =>
      rw [hrun] at hx
      simp only [Option.mem_def, Option.some.injEq] at hx
      subst hx
      rw [hrun] at hv
      exact hv

/-- withScope preserves value postconditions. -/
theorem postM_withScope {α : Type} {a : ResolveM α} {P : α → Prop}
    (h : PostM a P) : PostM (withScope a) P := by
  unfold withScope
  exact postM_bind_any fun saved1 =>
    postM_bind_any fun saved2 =>
    postM_bind_any fun _ =>
    postM_bind h fun result hres =>
    postM_bind_any fun _ =>
    postM_pure hres

-- Crux test: Check.varDeclare always returns Clean (annotated Declare).
/-- The single-node Clean fact: an annotated Declare node collects nothing. -/
theorem clean_declare_annotated (name : Identifier) (ty : HighTypeMd)
    (src : Strata.FileRange) :
    Clean { val := .Var (.Declare ⟨name, some ty⟩), source := src } := by
  unfold Clean
  apply collect_eq_of_emits
  rw [foldStmtExprM.eq_def]
  have h1 : unannotatedDeclares { val := .Var (.Declare ⟨name, some ty⟩), source := src } = [] := by
    simp [unannotatedDeclares]
  simp only [collectVisitor, h1]
  simpa using emits_seq (emits_modify (β := Strata.Message) []) emits_pure

theorem varDeclare_clean (param : Parameter?) (source : Strata.FileRange) :
    PostM (Check.varDeclare param source) Clean := by
  unfold Check.varDeclare
  cases param.type with
  | some ty =>
    exact postM_bind_any fun ty' =>
      postM_bind_any fun name' => postM_pure (clean_declare_annotated name' ty' source)
  | none =>
    refine postM_bind_any fun (_ : Unit) => ?_
    refine postM_bind_any fun (ty' : HighTypeMd) => ?_
    simp only []
    exact postM_bind_any fun name' =>
      postM_pure (clean_declare_annotated name' ty' source)


end ResolutionClean

/-! ## Layer 3: plumbing from the master lemma to the top-level theorem

The two *master facts* — every tree emitted by the `Synth`/`Check`
dispatchers is `Clean` — are taken as section hypotheses here and
discharged at the bottom of the file by `master`. -/

end -- public section

section Plumbing

open Resolution ResolutionClean

variable
  (masterSynth : ∀ e, PostM (Synth.resolveStmtExpr e) (fun r => Clean r.1))
  (masterCheck : ∀ e ty, PostM (Check.resolveStmtExpr e ty) Clean)

theorem validate_decompose (program : Program) :
    validateFullyAnnotated program =
      (program.staticProcedures ++ program.types.flatMap fun
        | .Composite ct => ct.instanceProcedures
        | _ => []).flatMap (fun proc =>
          (mapProcedureM (m := StateM (List Message))
            (fun e => do modify (· ++ collectStmtExprList unannotatedDeclares e); pure e)
            proc |>.run []).2)
      ++ (program.types.flatMap fun
        | .Constrained ct =>
          collectStmtExprList unannotatedDeclares ct.constraint
            ++ collectStmtExprList unannotatedDeclares ct.witness
        | _ => [])
      ++ program.constants.flatMap (fun c =>
          c.initializer.toList.flatMap (collectStmtExprList unannotatedDeclares))
      ++ program.staticFields.flatMap (fun f =>
          f.initializer.toList.flatMap (collectStmtExprList unannotatedDeclares)) := by
  rfl

include masterSynth in
/-- resolveStmtExpr wrapper is Clean. -/
theorem resolveStmtExpr_clean (e : StmtExprMd) :
    PostM (Strata.Laurel.resolveStmtExpr e) Clean := by
  unfold Strata.Laurel.resolveStmtExpr
  exact postM_bind (masterSynth e) (fun r hr => postM_pure hr)

/-- Condition.mapM with a Clean-producing function yields a Clean condition. -/
theorem condition_mapM_clean (c : Condition) (f : StmtExprMd → ResolveM StmtExprMd)
    (hf : ∀ e, PostM (f e) Clean) :
    PostM (Condition.mapM f c) (fun c' => Clean c'.condition) := by
  unfold Condition.mapM
  exact postM_bind (hf c.condition) (fun r hr => postM_pure hr)

/-- Clean constructor: a Var-Field node over a Clean target. -/
theorem clean_var_field (target : StmtExprMd) (f : Identifier)
    (src : Strata.FileRange) (h : Clean target) :
    Clean { val := .Var (.Field target f), source := src } := by
  rw [clean_iff]
  exact ⟨by simp [unannotatedDeclares], by simpa [childCollect] using h⟩

include masterSynth in
/-- resolveModifiesEntry yields Clean (when it yields anything). -/
theorem resolveModifiesEntry_clean (e : StmtExprMd) :
    PostM (Strata.Laurel.resolveModifiesEntry e) (fun r => ∀ x ∈ r, Clean x) := by
  unfold Strata.Laurel.resolveModifiesEntry
  refine postM_bind_any fun ctx => ?_
  split
  · -- .All arm: resolveStmtExpr wrapper then some
    refine postM_bind (resolveStmtExpr_clean masterSynth _) fun e' he' => ?_
    exact postM_pure (by simpa using he')
  · -- .Var (.Field target f) arm
    refine postM_bind (masterSynth _) fun (tp : StmtExprMd × HighTypeMd) htp => ?_
    refine postM_bind_any fun fieldName' => ?_
    by_cases hheap : isHeapRelevantType (ctx.typeLattice.unfold tp.snd).val
    · simp only [hheap, if_true]
      exact postM_pure (by
        intro x hx
        simp only [Option.mem_def, Option.some.injEq] at hx
        subst hx
        exact clean_var_field _ _ _ htp)
    · simp only [hheap]
      exact postM_bind_any fun _ => postM_pure (by simp)
  · -- wildcard arm
    refine postM_bind (masterSynth _) fun (tp : StmtExprMd × HighTypeMd) htp => ?_
    obtain ⟨e', ty⟩ := tp
    simp only [] at htp ⊢
    by_cases hheap : isHeapRelevantType (ctx.typeLattice.unfold ty).val
    · simp only [hheap, if_true]
      exact postM_pure (by
        intro x hx
        simp only [Option.mem_def, Option.some.injEq] at hx
        subst hx
        exact htp)
    · simp only [hheap]
      exact postM_bind_any fun _ => postM_pure (by simp)

/-- Body cleanliness: every StmtExpr tree in the body is Clean. -/
def CleanBody (b : Body) : Prop :=
  match b with
  | .Transparent e => Clean e
  | .Opaque posts impl mods =>
    (∀ p ∈ posts, Clean p.condition) ∧ (∀ e ∈ impl, Clean e) ∧ (∀ e ∈ mods, Clean e)
  | .Abstract posts => ∀ p ∈ posts, Clean p.condition
  | .External => True

include masterSynth in
omit masterCheck in
theorem resolveModifies_clean (mods : List StmtExprMd) :
    PostM (Strata.Laurel.resolveModifies mods) (fun ms => ∀ e ∈ ms, Clean e) := by
  unfold Strata.Laurel.resolveModifies
  refine postM_bind (postM_mapM mods _ (fun x _ => resolveModifiesEntry_clean masterSynth x))
    fun rs hrs => postM_pure ?_
  intro e he
  obtain ⟨o, ho, hoe⟩ := List.mem_filterMap.mp he
  exact hrs o ho e hoe

include masterSynth masterCheck in
theorem resolveBody_clean (body : Body) :
    PostM (resolveBody body) CleanBody := by
  unfold resolveBody
  split
  · -- Transparent
    exact postM_bind (masterSynth _) fun b hb => postM_pure hb
  · -- Opaque
    refine postM_bind (postM_mapM _ _ (fun c _ =>
        condition_mapM_clean c _
          (fun e => masterCheck e { val := .TBool, source := e.source })))
      fun posts' hposts => ?_
    refine postM_bind (postM_option_mapM _ _ (fun e => masterSynth e))
      fun impl' himpl => ?_
    refine postM_bind (resolveModifies_clean masterSynth _)
      fun mods' hmods => postM_pure ?_
    refine ⟨fun p hp => hposts p hp, ?_, hmods⟩
    intro e he
    -- impl'.map (·.1): e is the first component of some pair in impl'
    obtain ⟨pr, hpr, hpre⟩ := Option.map_eq_some_iff.mp he
    exact hpre ▸ himpl pr hpr
  · -- Abstract
    refine postM_bind (postM_mapM _ _ (fun c _ =>
        condition_mapM_clean c _
          (fun e => masterCheck e { val := .TBool, source := e.source })))
      fun posts' hposts => postM_pure ?_
    exact fun p hp => hposts p hp
  · -- External
    exact postM_pure trivial

/-- Cleanliness of one `throwsOn` behavior case: its guard, each of its case
    postconditions, and each of its frame targets. The case's clauses are ordinary
    expressions that `mapProcedureM` walks like any other specification field, so
    they carry the same obligation as the normal-path `ensures`/`modifies`. -/
def CleanThrowsOnBlock (blk : ThrowsOnBlock) : Prop :=
  Clean blk.guard ∧
  (∀ c ∈ blk.postconditions, Clean c.condition) ∧
  (∀ e ∈ blk.modifies, Clean e)

/-- Procedure-level: everything `mapProcedureM` walks in the RESOLVED procedure
    is Clean. Stated via the fields the validator's walk reads. -/
def CleanProcFields (proc : Procedure) : Prop :=
  (∀ p ∈ proc.preconditions, Clean p.condition) ∧
  (∀ e ∈ proc.decreases, Clean e) ∧
  CleanBody proc.body ∧
  (∀ e ∈ proc.invokeOn, Clean e) ∧
  (∀ e ∈ proc.axioms, Clean e) ∧
  (∀ blk ∈ proc.throwsOn, CleanThrowsOnBlock blk)

include masterSynth masterCheck in
/-- The exceptional contract resolves to clean cases. A case's guard and each of its
    postconditions are *checked* against `bool`, and each frame target is
    synthesized, so all three come back Clean by the same argument as the
    normal-path clauses. The declared `throws` type is a type rather than an
    expression, so it carries no cleanliness obligation. -/
theorem resolveExceptionalContract_clean (proc : Procedure) :
    PostM (resolveExceptionalContract proc)
      (fun r => ∀ blk ∈ r.2.2, CleanThrowsOnBlock blk) := by
  unfold resolveExceptionalContract
  refine postM_bind_any fun throwsType' => ?_
  refine postM_bind (postM_mapM _ _ (fun blk _ => ?_))
    fun throwsOn' hblks => postM_pure hblks
  refine postM_bind (masterCheck blk.guard _) fun guard' hguard => ?_
  -- The postconditions are resolved in a scope that binds the thrown value when
  -- `throws` names one; both arms of that match end in the same `mapM`.
  refine postM_bind (Q := fun posts' => ∀ c ∈ posts', Clean c.condition)
    (postM_withScope ?_) fun posts' hposts => ?_
  · split
    · refine postM_bind_any fun _ => ?_
      exact postM_mapM _ _ (fun c _ =>
        condition_mapM_clean c _ (fun e => masterCheck e _))
    · exact postM_mapM _ _ (fun c _ =>
        condition_mapM_clean c _ (fun e => masterCheck e _))
  refine postM_bind (postM_mapM _ _ (fun e _ => resolveStmtExpr_clean masterSynth e))
    fun mods' hmods => ?_
  exact postM_pure ⟨hguard, hposts, hmods⟩

include masterSynth masterCheck in
theorem resolveProcedure_clean (proc : Procedure) :
    PostM (resolveProcedure proc) CleanProcFields := by
  unfold resolveProcedure
  -- `let procName' ← match ← defIdForProcedure proc with ...`: the nested `←`
  -- is hoisted into its own bind, and the match's two arms feed one shared
  -- continuation (a do-block join point). Case on the overload id so the match
  -- reduces; each arm is then a plain bind into that continuation.
  refine postM_bind_any fun overloadId => ?_
  cases overloadId
  all_goals
    refine postM_bind_any fun procName' => ?_
    apply postM_withScope
    refine postM_bind_any fun inputs' => ?_
    refine postM_bind_any fun outputs' => ?_
    refine postM_bind (postM_mapM _ _ (fun c _ =>
        condition_mapM_clean c _
          (fun e => masterCheck e { val := .TBool, source := e.source })))
      fun pres' hpres => ?_
    refine postM_bind (postM_option_mapM _ _ (fun e => resolveStmtExpr_clean masterSynth e))
      fun dec' hdec => ?_
    refine postM_bind_any fun savedAnswer => ?_
    refine postM_bind_any fun _ => ?_
    refine postM_bind (resolveBody_clean masterSynth masterCheck _) fun body' hbody => ?_
    refine postM_bind_any fun _ => ?_
    refine postM_bind (postM_option_mapM _ _ (fun e => resolveStmtExpr_clean masterSynth e))
      fun invokeOn' hinv => ?_
    refine postM_bind (postM_mapM _ _ (fun e _ => resolveStmtExpr_clean masterSynth e))
      fun axioms' hax => ?_
    -- The exceptional contract is resolved in a bind of its own before the record is
    -- assembled; its cleanliness is the sixth component of `CleanProcFields`.
    refine postM_bind (resolveExceptionalContract_clean masterSynth masterCheck proc)
      fun exceptional hexc => ?_
    obtain ⟨throwsType', throwsBinding', throwsOn'⟩ := exceptional
    exact postM_pure ⟨hpres, hdec, hbody, hinv, hax, hexc⟩

/-! Bridge: `CleanProcFields proc` implies the validator's per-procedure walk
    emits nothing. The walk is `mapProcedureM` in `StateM (List Message)`
    with visitor `fun e => do modify (· ++ collect e); pure e`. -/

open CollectEmits in
/-- The validator's per-procedure walk, as used in `validateFullyAnnotated`. -/
def procWalk (proc : Procedure) : List Message :=
  (mapProcedureM (m := StateM (List Message))
    (fun e => do modify (· ++ collectStmtExprList unannotatedDeclares e); pure e)
    proc |>.run []).2

/-- A `StateM (List δ) α` action that never grows the accumulator. -/
def KeepsState {δ α : Type} (a : StateM (List δ) α) : Prop :=
  ∀ acc, (a acc).2 = acc

theorem keeps_pure {δ α : Type} (x : α) : KeepsState (δ := δ) (pure x) :=
  fun _ => rfl

theorem keeps_bind {δ α β : Type} {a : StateM (List δ) α} {f : α → StateM (List δ) β}
    (ha : KeepsState a) (hf : ∀ x, KeepsState (f x)) :
    KeepsState (a >>= f) := by
  intro acc
  simp only [bind, StateT.bind]
  cases hrun : a acc with
  | mk x s1 =>
    have hs : s1 = acc := by have := ha acc; rw [hrun] at this; exact this
    rw [hs]
    exact hf x acc

theorem keeps_mapM {δ α β : Type} (l : List α) (f : α → StateM (List δ) β)
    (h : ∀ x ∈ l, KeepsState (f x)) : KeepsState (l.mapM f) := by
  induction l with
  | nil => exact keeps_pure _
  | cons hd tl ih =>
    rw [List.mapM_cons]
    exact keeps_bind (h hd (by simp))
      (fun x => keeps_bind (ih (fun y hy => h y (by simp [hy]))) (fun rs => keeps_pure _))

theorem keeps_option_mapM {δ α β : Type} (o : Option α) (f : α → StateM (List δ) β)
    (h : ∀ x ∈ o, KeepsState (f x)) : KeepsState (o.mapM f) := by
  cases o with
  | none => exact keeps_pure _
  | some v =>
    simp only [Option.mapM]
    exact keeps_bind (h v rfl) (fun r => keeps_pure _)

theorem keeps_condition_mapM {δ : Type} (c : Condition)
    (f : StmtExprMd → StateM (List δ) StmtExprMd)
    (h : KeepsState (f c.condition)) : KeepsState (Condition.mapM f c) := by
  unfold Condition.mapM
  exact keeps_bind h (fun r => keeps_pure _)

/-- Value postcondition for a StateM action, independent of the entry state. -/
def PostS {δ α : Type} (a : StateM (List δ) α) (P : α → Prop) : Prop :=
  ∀ s, P (a s).1

theorem postS_pure {δ α : Type} {x : α} {P : α → Prop} (h : P x) :
    PostS (δ := δ) (pure x) P := fun _ => h

theorem postS_bind {δ α β : Type} {a : StateM (List δ) α} {f : α → StateM (List δ) β}
    {Q : α → Prop} {P : β → Prop}
    (ha : PostS a Q) (hf : ∀ x, Q x → PostS (f x) P) :
    PostS (a >>= f) P := by
  intro s
  exact hf _ (ha s) ((a s).2)

theorem postS_bind_any {δ α β : Type} {a : StateM (List δ) α} {f : α → StateM (List δ) β}
    {P : β → Prop} (hf : ∀ x, PostS (f x) P) : PostS (a >>= f) P :=
  postS_bind (Q := fun _ => True) (fun _ => trivial) (fun x _ => hf x)

/-- Bind that both keeps state and tracks the intermediate value's postcondition. -/
theorem keeps_bind_post {δ α β : Type} {a : StateM (List δ) α} {f : α → StateM (List δ) β}
    {Q : α → Prop}
    (ha : KeepsState a) (hq : PostS a Q) (hf : ∀ x, Q x → KeepsState (f x)) :
    KeepsState (a >>= f) := by
  intro acc
  simp only [bind, StateT.bind]
  cases hrun : a acc with
  | mk x s1 =>
    have hs : s1 = acc := by have := ha acc; rw [hrun] at this; exact this
    have hx : Q x := by have := hq acc; rw [hrun] at this; exact this
    rw [hs]
    exact hf x hx acc

/-- `mapProcedureBodiesM` with the validator's visitor preserves the spec fields. -/
theorem bodiesM_spec_fields (proc : Procedure) :
    PostS (δ := Message)
      (mapProcedureBodiesM (m := StateM (List Message))
        (fun e => do modify (· ++ collectStmtExprList unannotatedDeclares e); pure e)
        proc)
      (fun p1 => p1.preconditions = proc.preconditions ∧
        p1.decreases = proc.decreases ∧
        p1.invokeOn = proc.invokeOn ∧
        p1.axioms = proc.axioms ∧
        p1.throwsOn = proc.throwsOn) := by
  unfold mapProcedureBodiesM
  split
  all_goals
    repeat' first
      | exact postS_pure ⟨rfl, rfl, rfl, rfl, rfl⟩
      | (apply postS_bind_any; intro _)

open CollectEmits in
/-- The validator's visitor keeps the state exactly when the tree is Clean. -/
theorem keeps_visitor (e : StmtExprMd) (h : Clean e) :
    KeepsState (δ := Message)
      (do modify (· ++ collectStmtExprList unannotatedDeclares e); pure e) := by
  intro acc
  simp only [bind, StateT.bind, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    pure, StateT.pure]
  simp [Clean] at h
  simp [h]

open CollectEmits in
theorem procWalk_nil_of_clean (proc : Procedure) (h : CleanProcFields proc) :
    procWalk proc = [] := by
  obtain ⟨hpre, hdec, hbody, hinv, hax, hthrows⟩ := h
  have hwalk : KeepsState (δ := Message)
      (mapProcedureM (m := StateM (List Message))
        (fun e => do modify (· ++ collectStmtExprList unannotatedDeclares e); pure e) proc) := by
    unfold mapProcedureM mapProcedureBodiesM
    -- Body first (mapProcedureBodiesM), then the five spec fields.
    apply keeps_bind_post (Q := fun p1 => p1.preconditions = proc.preconditions ∧
        p1.decreases = proc.decreases ∧
        p1.invokeOn = proc.invokeOn ∧
        p1.axioms = proc.axioms ∧
        p1.throwsOn = proc.throwsOn)
      (hq := bodiesM_spec_fields proc)
    · -- mapProcedureBodiesM: match on proc.body
      rcases hb : proc.body with b | ⟨posts, impl, mods⟩ | posts | _
        <;> rw [hb] at hbody <;> unfold CleanBody at hbody <;> simp only [] at hbody
      · exact keeps_bind (keeps_visitor _ hbody) (fun _ => keeps_pure _)
      · obtain ⟨hposts, himpl, hmods⟩ := hbody
        apply keeps_bind (keeps_mapM _ _ (fun c hc =>
          keeps_condition_mapM c _ (keeps_visitor _ (hposts c hc))))
        intro posts'
        apply keeps_bind (keeps_option_mapM _ _ (fun e he =>
          keeps_visitor _ (himpl e he)))
        intro impl'
        apply keeps_bind (keeps_mapM _ _ (fun e he => keeps_visitor _ (hmods e he)))
        intro mods'
        exact keeps_pure _
      · apply keeps_bind (keeps_mapM _ _ (fun c hc =>
          keeps_condition_mapM c _ (keeps_visitor _ (hbody c hc))))
        intro posts'
        exact keeps_pure _
      · exact keeps_pure _
    · intro proc1 hfields
      obtain ⟨hf1, hf2, hf3, hf4, hf5⟩ := hfields
      apply keeps_bind (keeps_mapM _ _ (fun c hc =>
        keeps_condition_mapM c _ (keeps_visitor _ (hpre c (hf1 ▸ hc)))))
      intro pres'
      apply keeps_bind (keeps_option_mapM _ _ (fun e he =>
        keeps_visitor _ (hdec e (hf2 ▸ he))))
      intro dec'
      apply keeps_bind (keeps_option_mapM _ _ (fun e he =>
        keeps_visitor _ (hinv e (hf3 ▸ he))))
      intro invokeOn'
      apply keeps_bind (keeps_mapM _ _ (fun e he =>
        keeps_visitor _ (hax e (hf4 ▸ he))))
      intro axioms'
      -- Each `throwsOn` case walks its guard, then its postconditions, then its
      -- frame targets; all three are Clean by `CleanThrowsOnBlock`.
      apply keeps_bind (keeps_mapM _ _ (fun blk hblk => ?_))
      · intro throwsOn'
        exact keeps_pure _
      obtain ⟨hg, hp, hm⟩ := hthrows blk (hf5 ▸ hblk)
      apply keeps_bind (keeps_visitor _ hg)
      intro guard'
      apply keeps_bind (keeps_mapM _ _ (fun c hc =>
        keeps_condition_mapM c _ (keeps_visitor _ (hp c hc))))
      intro posts'
      apply keeps_bind (keeps_mapM _ _ (fun e he => keeps_visitor _ (hm e he)))
      intro mods'
      exact keeps_pure _
  have := hwalk []
  unfold procWalk
  simpa [StateT.run] using this

include masterSynth masterCheck in
theorem resolveInstanceProcedure_clean (typeName : Identifier) (proc : Procedure) :
    PostM (resolveInstanceProcedure typeName proc) CleanProcFields := by
  unfold resolveInstanceProcedure
  refine postM_bind_any fun resolved => ?_
  apply postM_withScope
  refine postM_bind_any fun savedInstType => ?_
  refine postM_bind_any fun _ => ?_
  refine postM_bind_any fun inputs' => ?_
  refine postM_bind_any fun outputs' => ?_
  refine postM_bind (postM_mapM _ _ (fun c _ =>
      condition_mapM_clean c _
        (fun e => masterCheck e { val := .TBool, source := e.source })))
    fun pres' hpres => ?_
  refine postM_bind (postM_option_mapM _ _ (fun e => resolveStmtExpr_clean masterSynth e))
    fun dec' hdec => ?_
  refine postM_bind_any fun savedAnswer => ?_
  refine postM_bind_any fun _ => ?_
  refine postM_bind (resolveBody_clean masterSynth masterCheck _) fun body' hbody => ?_
  refine postM_bind_any fun _ => ?_
  refine postM_bind (postM_option_mapM _ _ (fun e => resolveStmtExpr_clean masterSynth e))
    fun invokeOn' hinv => ?_
  refine postM_bind_any fun _ => ?_
  refine postM_bind (postM_mapM _ _ (fun e _ => resolveStmtExpr_clean masterSynth e))
    fun axioms' hax => ?_
  -- As in `resolveProcedure_clean`: the exceptional contract is resolved in its own
  -- bind before the record is assembled, and supplies the sixth component.
  refine postM_bind (resolveExceptionalContract_clean masterSynth masterCheck proc)
    fun exceptional hexc => ?_
  obtain ⟨throwsType', throwsBinding', throwsOn'⟩ := exceptional
  exact postM_pure ⟨hpres, hdec, hbody, hinv, hax, hexc⟩

/-- Cleanliness of a resolved type definition, matching what the validator walks. -/
def CleanTypeDef (td : TypeDefinition) : Prop :=
  match td with
  | .Composite ct => ∀ proc ∈ ct.instanceProcedures, CleanProcFields proc
  | .Constrained ct => Clean ct.constraint ∧ Clean ct.witness
  | _ => True

include masterSynth masterCheck in
theorem resolveTypeDefinition_clean (td : TypeDefinition) :
    PostM (resolveTypeDefinition td) CleanTypeDef := by
  unfold resolveTypeDefinition
  split
  · -- Composite
    refine postM_bind_any fun ctName' => ?_
    refine postM_bind_any fun extending' => ?_
    refine postM_bind_any fun fields' => ?_
    repeat'
      first
      | (refine postM_bind (postM_mapM _ _ (fun p _ =>
            resolveInstanceProcedure_clean masterSynth masterCheck ctName' p))
          fun instProcs' hinst => postM_pure (fun proc hp => hinst proc hp))
      | (refine postM_bind_any fun _ => ?_)
  · -- Constrained
    refine postM_bind_any fun ctName' => ?_
    refine postM_bind_any fun base' => ?_
    refine postM_bind (postM_withScope (P := fun (r : Identifier × StmtExprMd × StmtExprMd) =>
        Clean r.2.1 ∧ Clean r.2.2) ?_) fun r hr => postM_pure ?_
    · refine postM_bind_any fun valueName' => ?_
      refine postM_bind (masterSynth _) fun cw hcw => ?_
      refine postM_bind (masterSynth _) fun ww hww => postM_pure ?_
      exact ⟨hcw, hww⟩
    · exact hr
  · -- Datatype
    refine postM_bind_any fun dtName' => ?_
    -- the duplicate-type-parameter `unless` is an `if` whose branches each
    -- bind one action (`pure ()` / `modify`) before the shared continuation
    refine postM_ite ?_ ?_ <;>
      exact postM_bind_any fun _ =>
        postM_bind_any fun ctors' => postM_pure trivial
  · -- Alias
    refine postM_bind_any fun target' => ?_
    exact postM_bind_any fun taName' => postM_pure trivial

include masterCheck in
omit masterSynth in
theorem resolveConstant_clean (c : Constant) :
    PostM (resolveConstant c) (fun c' => ∀ e ∈ c'.initializer, Clean e) := by
  unfold resolveConstant
  refine postM_bind_any fun ty' => ?_
  refine postM_bind (postM_option_mapM _ _ (fun e => masterCheck e ty'))
    fun init' hinit => ?_
  exact postM_bind_any fun name' => postM_pure hinit

include masterCheck in
omit masterSynth in
theorem resolveField_clean (ownerName : Identifier) (f : Field) :
    PostM (resolveField ownerName f) (fun f' => ∀ e ∈ f'.initializer, Clean e) := by
  unfold resolveField
  refine postM_bind_any fun ty' => ?_
  refine postM_bind_any fun (_ : Unit) => ?_
  refine postM_bind_any fun resolved => ?_
  refine postM_bind (postM_option_mapM _ _ (fun e => masterCheck e ty'))
    fun init' hinit => ?_
  exact postM_pure hinit

/-! Final assembly -/

/-- A program is Clean when every tree the validator walks is Clean. -/
def CleanProgram (program : Program) : Prop :=
  (∀ proc ∈ program.staticProcedures, CleanProcFields proc) ∧
  (∀ td ∈ program.types, CleanTypeDef td) ∧
  (∀ c ∈ program.constants, ∀ e ∈ c.initializer, Clean e) ∧
  (∀ f ∈ program.staticFields, ∀ e ∈ f.initializer, Clean e)

open CollectEmits in
theorem validate_nil_of_cleanProgram (program : Program)
    (h : CleanProgram program) : validateFullyAnnotated program = [] := by
  obtain ⟨hprocs, htypes, hconsts, hfields⟩ := h
  rw [validate_decompose]
  refine List.append_eq_nil_iff.mpr
    ⟨List.append_eq_nil_iff.mpr ⟨List.append_eq_nil_iff.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- procedures: static ++ instance
    rw [List.flatMap_eq_nil_iff]
    intro proc hp
    rcases List.mem_append.mp hp with hstat | hinst
    · exact procWalk_nil_of_clean proc (hprocs proc hstat)
    · rw [List.mem_flatMap] at hinst
      obtain ⟨td, htd, hproc⟩ := hinst
      have := htypes td htd
      revert hproc this
      cases td with
      | Composite ct =>
        intro hproc hclean
        exact procWalk_nil_of_clean proc (hclean proc hproc)
      | Constrained ct => intro h _; cases h
      | Datatype dt => intro h _; cases h
      | Alias ta => intro h _; cases h
  · -- constrained types
    rw [List.flatMap_eq_nil_iff]
    intro td htd
    have := htypes td htd
    cases td with
    | Constrained ct =>
      obtain ⟨hc, hw⟩ := this
      simp [Clean] at hc hw
      simp [hc, hw]
    | Composite ct => simp
    | Datatype dt => simp
    | Alias ta => simp
  · -- constants
    rw [List.flatMap_eq_nil_iff]
    intro c hc
    rw [List.flatMap_eq_nil_iff]
    intro e he
    exact hconsts c hc e (Option.mem_toList.mp (by simpa using he))
  · -- file-scope globals
    rw [List.flatMap_eq_nil_iff]
    intro f hf
    rw [List.flatMap_eq_nil_iff]
    intro e he
    exact hfields f hf e (Option.mem_toList.mp (by simpa using he))

include masterSynth masterCheck in
theorem phase1_clean (program : Program) :
    PostM (do
      preRegisterTopLevel program
      let types' ← program.types.mapM resolveTypeDefinition
      let constants' ← program.constants.mapM resolveConstant
      let staticFields' ← program.staticFields.mapM (resolveField "$static")
      let staticProcs' ← program.staticProcedures.mapM resolveProcedure
      return { staticProcedures := staticProcs', staticFields := staticFields',
               types := types', constants := constants' : Program })
      CleanProgram := by
  refine postM_bind_any fun _ => ?_
  refine postM_bind (postM_mapM _ _ (fun td _ =>
      resolveTypeDefinition_clean masterSynth masterCheck td)) fun types' htypes => ?_
  refine postM_bind (postM_mapM _ _ (fun c _ =>
      resolveConstant_clean masterCheck c)) fun constants' hconsts => ?_
  refine postM_bind (postM_mapM _ _ (fun f _ =>
      resolveField_clean masterCheck "$static" f)) fun staticFields' hfields => ?_
  refine postM_bind (postM_mapM _ _ (fun p _ =>
      resolveProcedure_clean masterSynth masterCheck p)) fun staticProcs' hprocs => ?_
  exact postM_pure ⟨hprocs, htypes, hconsts, hfields⟩

include masterSynth masterCheck in
/-- **Resolution establishes the fully-annotated invariant**, conditional on
    the two master facts (see the commented `master` lemma below): given that
    every tree the `Synth`/`Check` dispatchers emit is `Clean`, the resolved
    program passes `validateFullyAnnotated` with no diagnostics. Holds for any
    lattice configuration (`gradualTypes`/`realizeCoercion`/`toBool`), since
    `PostM` quantifies over the entire resolve state. -/
public theorem resolve_fullyAnnotated' (p : Program)
    (existingModel : Option SemanticModel := none)
    (gradualTypes : Std.HashSet String := {})
    (realizeCoercion : Option (Coercion → StmtExprMd → StmtExprMd) := none)
    (toBool : Option (HighType → StmtExprMd → StmtExprMd) := none) :
    validateFullyAnnotated
      (resolve p existingModel gradualTypes realizeCoercion toBool).program = [] := by
  apply validate_nil_of_cleanProgram
  show CleanProgram (resolve p existingModel gradualTypes realizeCoercion toBool).program
  unfold resolve
  simp only []
  exact phase1_clean masterSynth masterCheck p _


end Plumbing

public section
/-! ## The master lemma and the main theorem -/

/-
TODO(proof): prove the master lemma below and reinstate the unconditional
`resolve_fullyAnnotated`. The conditional version `resolve_fullyAnnotated'`
above is fully proven; only the two master facts remain.

The master lemma follows by the functional mutual-induction principle
`Synth.resolveStmtExpr.mutual_induct` of the resolution mutual block
(34 motives — `PostM (…) Clean` for the `Check.*` rules and
`PostM (…) (fun r => ∀ src, Clean ⟨r.1, src⟩)` for the `Synth.*` rules —
and on the order of 125 case obligations). Each obligation discharges
mechanically with
the `PostM` combinators above: unfold the rule with `.eq_def`, chain
`postM_bind`/`postM_bind_any`/`postM_withScope` through the do-block
feeding the induction hypotheses to recursive calls, and close the
resulting `Clean ⟨node, src⟩` leaves with `clean_iff` + `simp` over
`unannotatedDeclares`/`childCollect`. The obligations elaborate this
way with no proof-level failures, but the resulting proof terms are
too large for the in-tree build (the kernel/elaborator overflow the
default thread stack and take tens of minutes even in 25-lemma chunks),
so the lemma is left admitted-and-commented until the proof can be made
cheap enough to check in.

theorem master :
    (∀ e, ResolutionClean.PostM (Resolution.Synth.resolveStmtExpr e) (fun r => Clean r.1)) ∧
    (∀ e ty, ResolutionClean.PostM (Resolution.Check.resolveStmtExpr e ty) Clean) := by
  sorry

/-- **Resolution establishes the fully-annotated invariant**: on any input
    program, `validateFullyAnnotated` reports nothing about the resolved
    output — every `Declare` node carries `some ty` (see the Var-Declare and
    Decl-Synth rules in `Resolution.lean`). -/
theorem resolve_fullyAnnotated (p : Program)
    (existingModel : Option SemanticModel := none) :
    validateFullyAnnotated (resolve p existingModel).program = [] :=
  resolve_fullyAnnotated' master.1 master.2 p existingModel {} none none
-/

end -- public section
end Strata.Laurel
