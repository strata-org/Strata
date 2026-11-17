/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PathExplorer
public import Strata.Languages.Core.SymExecProps
import all Strata.Languages.Core.PathExplorer
import all Strata.Languages.Core.SymExecProps
import all Strata.Languages.Core.Interpreter
import all Strata.DL.Imperative.CFGDominators
import all Strata.DL.Lambda.Denote.LExprDenoteEq
import Strata.DL.Lambda.LExprProps
import Strata.DL.Imperative.InterpreterConfigProps

/-! # Properties of the path explorer: merging, and options at their defaults

What merging the two branches of a fork at its join gives, per branch, for the merge of their
environments (`mergeEnvs`), which `mergeBranches` runs for every kind of configuration
(`mergeBranches_eq`):

* `mergeEnvs_store`: at a merge, each variable that both branches bind keeps its value when the
  branches agree on it (ignoring source locations), and becomes `if guard then va else vb` when
  they don't. Both stores must start from the same base store, as every path of one run does.
* `mergeEnvs_store_denote`: under any model, that value denotes what the then-branch's value
  denotes where the guard is true, and the else-branch's where it is false.
* `mergeEnvs_pc`: the merged path condition holds under a model iff the guard holds and the
  then-branch's path condition does, or the guard fails and the else-branch's does.
* `mergeChoices_nil`: a merge of branches that made no choices keeps the record of choices.

What each kind of configuration brings to a merge: a structured path its terminal environment
(`structuredShape_joinEnv_setJoinEnv`); a CFG path its environment without the locals of blocks that
do not dominate the join, keeping the store's base and every other variable's value
(`cfgShape_forMerge_block`).

And the explorer's options at their defaults: `failedCheckStatus_off` (no failed check ends a
path) and `overPathLimit_none` (no path limit is reached).
-/

namespace Core.SymExec

open Imperative Lambda

public section

/-- When `mergeEnvs` succeeds, the comparison of the two stores succeeded, and the merged
    environment and path state are built from its result. -/
private theorem mergeEnvs_some {scfg : ExploreCfg} {j : Join}
    {ea eb em : @IEnv Expression (symLang scfg)} {sa sb st : PathState} {n : Nat}
    (h : mergeEnvs j ea eb sa sb = some (em, st, n)) :
    letI := symLang scfg
    ∃ diffs,
      List.foldlM
        (fun acc k =>
          match ea.store.get k, eb.store.get k with
          | some va, some vb =>
            some (if va.beqIgnoringMetadata vb = true then acc
              else acc ++ [(k, LExpr.ite symExecLoc j.guard va vb)])
          | none, none => some acc
          | _, _ => none)
        [] (ea.store.writes.keys ++ eb.store.writes.keys).eraseDups = some diffs ∧
      em = { ea with store := diffs.foldl (fun σ x => σ.update x.fst x.snd) ea.store } ∧
      st = { sa with
              pc := (List.take (sb.pc.length - j.basePcLen) sb.pc).dropLast.map
                      (fun x => (x.fst, LExpr.ite symExecLoc j.guard Core.true x.snd)) ++
                    (List.take (sa.pc.length - j.basePcLen) sa.pc).dropLast.map
                      (fun x => (x.fst, LExpr.ite symExecLoc j.guard x.snd Core.true)) ++
                    List.drop (sa.pc.length - j.basePcLen) sa.pc,
              segment := [], merged := true,
              choices := mergeChoices j sa.choices sb.choices,
              next := max sa.next sb.next } := by
  letI := symLang scfg
  unfold mergeEnvs at h
  split at h
  · cases h
  simp only [] at h
  split at h
  · cases h
  · rename_i diffs hd
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨diffs, hd, h.1.symm, h.2.1.symm⟩

/-- `mergeBranches` waits for both branches at the join, takes what each brings to the merge
    (`ProcBodyShape.forMerge`), merges them with `mergeEnvs`, and continues at the then-branch's
    configuration. -/
theorem mergeBranches_eq {scfg : ExploreCfg} {C : Type} {sh : ProcBodyShape scfg C} {j : Join}
    {a b m : Entry C} {n : Nat} (h : mergeBranches sh j a b = some (m, n)) :
    ∃ ea eb em, sh.joinEnv a.cfg = some ea ∧ sh.joinEnv b.cfg = some eb ∧
      mergeEnvs j (sh.forMerge j.site ea) (sh.forMerge j.site eb) a.st b.st =
        some (em, m.st, n) ∧
      m.cfg = sh.setJoinEnv a.cfg em := by
  unfold mergeBranches at h
  split at h
  · rename_i ea eb hea heb
    split at h
    · rename_i em st k hm
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ea, eb, em, hea, heb, hm, rfl⟩
    · cases h
  · cases h

/-- `deepest` of `replaceDeepest` with a terminal configuration is that configuration. -/
private theorem deepest_replaceDeepest_terminal {scfg : ExploreCfg}
    (c : StmtConfig scfg) (e : @IEnv Expression (symLang scfg)) :
    letI := symLang scfg
    deepest (replaceDeepest c (.terminal e)) = .terminal e := by
  letI := symLang scfg
  induction c with
  | seq i r ih => simp only [replaceDeepest, deepest]; exact ih
  | seqs i k ih => simp only [replaceDeepest, deepest]; exact ih
  | block l f i ih => simp only [replaceDeepest, deepest]; exact ih
  | _ => rfl

/-- A merged structured path waits with the merged environment: its innermost configuration is
    terminal with that environment. -/
theorem structuredShape_joinEnv_setJoinEnv {scfg : ExploreCfg} (c : StmtConfig scfg)
    (e : @IEnv Expression (symLang scfg)) :
    (structuredShape scfg).joinEnv ((structuredShape scfg).setJoinEnv c e) = some e := by
  letI := symLang scfg
  show (match deepest (replaceDeepest c (.terminal e)) with
    | .terminal e => some e
    | _ => none) = some e
  rw [deepest_replaceDeepest_terminal]

/-- Looking only at the blocks that declare locals finds the same out-of-scope locals at `j` as
    looking at every block: the locals of each block that does not dominate `j`. -/
private theorem localsOutOfScope_filter (dom : Std.HashMap String (List String))
    (decls : List (String × List CoreIdent)) (j : String) :
    localsOutOfScope dom (decls.filter (!·.2.isEmpty)) j =
      decls.flatMap fun (d, xs) => if CFG.Dom.dominates dom d j then [] else xs := by
  have hf : ∀ l : List (String × List CoreIdent),
      (l.filter (!·.2.isEmpty)).flatMap (fun (d, xs) =>
          if CFG.Dom.dominates dom d j then [] else xs) =
        l.flatMap fun (d, xs) => if CFG.Dom.dominates dom d j then [] else xs := by
    intro l
    induction l with
    | nil => rfl
    | cons p l ih =>
      obtain ⟨d, xs⟩ := p
      cases xs <;> simp_all
  rw [← hf]
  unfold localsOutOfScope
  split
  · rename_i h
    simp [List.isEmpty_iff.mp h]
  · simp [CFG.Dom.dominates, Std.HashSet.contains_ofList]

/-- In a map built by inserting, for each block label `j`, a thunk of `f j`, every thunk found
    at a key `k` gives `f k`. -/
private theorem foldl_insert_thunk {β : Type} (f : String → List CoreIdent)
    (bs : List (String × β)) (m : Std.HashMap String (Thunk (List CoreIdent)))
    (hm : ∀ k t, m[k]? = some t → t.get = f k) :
    ∀ k t, (bs.foldl (fun m (j, _) => m.insert j (Thunk.mk fun _ => f j)) m)[k]? = some t →
      t.get = f k := by
  induction bs generalizing m with
  | nil => exact hm
  | cons b bs ih =>
    apply ih
    intro k t h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i hk
      cases h
      simp only [beq_iff_eq] at hk
      subst hk
      rfl
    · exact hm k t h

/-- A CFG path brings to a merge at block `j` its environment with the locals declared in
    blocks that do not dominate `j` left out (`IStore.drop`): the store keeps its base, and
    reads as `RStore.dropVars` of those locals, so every other variable keeps its value. -/
theorem cfgShape_forMerge_block {scfg : ExploreCfg} (g : Core.DetCFG) (j : String)
    (e : @IEnv Expression (symLang scfg)) :
    letI := symLang scfg
    ((cfgShape scfg g).forMerge (.block j) e).store.base = e.store.base ∧
      ((cfgShape scfg g).forMerge (.block j) e).store.get =
        RStore.dropVars ((g.blocks.map fun (d, b) => (d, blockInits b)).flatMap fun (d, xs) =>
          if CFG.Dom.dominates g.computeDominators d j then [] else xs) e.store.get :=
  letI := symLang scfg
  by
    refine ⟨rfl, ?_⟩
    simp only [cfgShape, IStore.get_drop]
    congr 1
    split
    · rename_i t h
      rw [foldl_insert_thunk _ _ _ (by simp) j t h, localsOutOfScope_filter]
    · exact localsOutOfScope_filter _ _ _

/-- When `acyclic` is true, the join `nestJoin` picks under an innermost open join at block `h`
    is block `h` or a block `y` with `reaches y h`. -/
private theorem nestJoin_nested {reaches : String → String → Bool} {acyclic : Bool} {h x y : String}
    (hac : acyclic = true) (hj : nestJoin reaches acyclic (some (.block h)) x = .block y) :
    y = h ∨ reaches y h = true := by
  simp only [nestJoin, hac, Bool.true_and] at hj
  split at hj
  · exact .inl (JoinSite.block.inj hj).symm
  · rename_i hr
    obtain rfl := (JoinSite.block.inj hj)
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hr
    exact .inr (by simpa using hr)

/-- **A CFG fork's join is, or reaches, the innermost open join's block.** In a CFG with no cycle
    reachable from its entry (`cfgAcyclic`), the join block a fork opens, under a path whose
    innermost open join is at block `h`, is `h` or a block that reaches `h` by the reach-to sets
    `cfgReachTo` (`reachesIn`, the test `passedJoin` uses). -/
private theorem cfgShape_forkSite_nested {scfg : ExploreCfg} {g : Core.DetCFG} {h y : String}
    {c : BlockConfig scfg} (hac : cfgAcyclic g = true)
    (hf : (cfgShape scfg g).forkSite (some (.block h)) c = some (.block y)) :
    y = h ∨ reachesIn (cfgReachTo g) y h = true := by
  simp only [cfgShape] at hf
  split at hf
  · obtain ⟨x, -, hx⟩ := Option.map_eq_some_iff.mp hf
    exact nestJoin_nested hac hx
  · exact absurd hf (by simp)

/-- Expressions equal up to source locations (`LExpr.beqIgnoringMetadata`) have equal metadata
    erasures. -/
private theorem eraseMetadata_eq_of_beqIgnoringMetadata :
    ∀ {a b : Expression.Expr}, a.beqIgnoringMetadata b = true →
      a.eraseMetadata = b.eraseMetadata := by
  intro a
  induction a with
  | const | op | bvar | fvar =>
    intro b h
    cases b <;>
      simp_all [LExpr.beqIgnoringMetadata, LExpr.eraseMetadata, LExpr.replaceMetadata]
  | abs m n ty e ih =>
    intro b h
    cases b <;> simp only [LExpr.beqIgnoringMetadata, Bool.and_eq_true, beq_iff_eq,
      reduceCtorEq] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    have := ih h; simp only [LExpr.eraseMetadata] at this
    simp [LExpr.eraseMetadata, LExpr.replaceMetadata, this]
  | quant m k n ty tr e iht ihe =>
    intro b h
    cases b <;> simp only [LExpr.beqIgnoringMetadata, Bool.and_eq_true, beq_iff_eq,
      reduceCtorEq] at h
    obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, h1⟩, h2⟩ := h
    have h1 := iht h1; have h2 := ihe h2; simp only [LExpr.eraseMetadata] at h1 h2
    simp [LExpr.eraseMetadata, LExpr.replaceMetadata, h1, h2]
  | app m f x ihf ihx =>
    intro b h
    cases b <;> simp only [LExpr.beqIgnoringMetadata, Bool.and_eq_true, reduceCtorEq] at h
    have h1 := ihf h.1; have h2 := ihx h.2; simp only [LExpr.eraseMetadata] at h1 h2
    simp [LExpr.eraseMetadata, LExpr.replaceMetadata, h1, h2]
  | ite m c t e ihc iht ihe =>
    intro b h
    cases b <;> simp only [LExpr.beqIgnoringMetadata, Bool.and_eq_true, reduceCtorEq] at h
    have h1 := ihc h.1.1; have h2 := iht h.1.2; have h3 := ihe h.2
    simp only [LExpr.eraseMetadata] at h1 h2 h3
    simp [LExpr.eraseMetadata, LExpr.replaceMetadata, h1, h2, h3]
  | eq m x y ihx ihy =>
    intro b h
    cases b <;> simp only [LExpr.beqIgnoringMetadata, Bool.and_eq_true, reduceCtorEq] at h
    have h1 := ihx h.1; have h2 := ihy h.2; simp only [LExpr.eraseMetadata] at h1 h2
    simp [LExpr.eraseMetadata, LExpr.replaceMetadata, h1, h2]

/-- What the merge assigns `x` given the two branch stores `sa` (then) and `sb` (else). -/
private def mergedVal (g : Expression.Expr) (sa sb : RStore Expression) (x : CoreIdent) :
    Option Expression.Expr :=
  match sa x, sb x with
  | some va, some vb =>
    some (if va.beqIgnoringMetadata vb = true then va else LExpr.ite symExecLoc g va vb)
  | _, _ => sa x

/-- Comparing the two stores over the variables `ks` extends a partial merge of `done` to a
    partial merge of `done ++ ks`. -/
private theorem foldlM_diffs {scfg : ExploreCfg} (g : Expression.Expr)
    (sa sb : @IStore Expression (symLang scfg)) :
    letI := symLang scfg
    ∀ (ks : List CoreIdent) (acc diffs : List (CoreIdent × Expression.Expr))
      (done : List CoreIdent),
      (∀ x, (acc.foldl (fun σ x => σ.update x.fst x.snd) sa).get x =
              (if x ∈ done then mergedVal g sa.get sb.get x else sa.get x)) →
      List.foldlM
        (fun acc k =>
          match sa.get k, sb.get k with
          | some va, some vb =>
            some (if va.beqIgnoringMetadata vb = true then acc
              else acc ++ [(k, LExpr.ite symExecLoc g va vb)])
          | none, none => some acc
          | _, _ => none) acc ks = some diffs →
      ∀ x, (diffs.foldl (fun σ x => σ.update x.fst x.snd) sa).get x =
              (if x ∈ done ++ ks then mergedVal g sa.get sb.get x else sa.get x) := by
  letI := symLang scfg
  intro ks
  induction ks with
  | nil =>
    intro acc diffs done hinv hf x
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at hf
    subst hf
    simpa using hinv x
  | cons k ks ih =>
    intro acc diffs done hinv hf x
    simp only [List.foldlM_cons] at hf
    have key : ∀ acc', (∀ y, (acc'.foldl (fun σ x => σ.update x.fst x.snd) sa).get y =
        (if y ∈ done ++ [k] then mergedVal g sa.get sb.get y else sa.get y)) →
        List.foldlM
          (fun acc k =>
            match sa.get k, sb.get k with
            | some va, some vb =>
              some (if va.beqIgnoringMetadata vb = true then acc
                else acc ++ [(k, LExpr.ite symExecLoc g va vb)])
            | none, none => some acc
            | _, _ => none) acc' ks = some diffs →
        (diffs.foldl (fun σ x => σ.update x.fst x.snd) sa).get x =
          (if x ∈ done ++ k :: ks then mergedVal g sa.get sb.get x else sa.get x) := by
      intro acc' hinv' hf'
      rw [ih acc' diffs (done ++ [k]) hinv' hf' x, List.append_assoc, List.singleton_append]
    -- The step at `k`.
    revert hf
    cases hka : sa.get k with
    | none =>
      cases hkb : sb.get k with
      | none =>
        intro hf
        apply key acc _ hf
        intro y
        rw [hinv y]
        by_cases hy : y = k
        · subst hy; simp [mergedVal, hka, hkb]
        · simp [hy]
      | some vb => intro hf; simp at hf
    | some va =>
      cases hkb : sb.get k with
      | none => intro hf; simp at hf
      | some vb =>
        intro hf
        simp only [Option.bind_eq_bind, Option.bind_some] at hf
        by_cases hab : va.beqIgnoringMetadata vb = true
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hab)] at hf
          apply key acc _ hf
          intro y
          rw [hinv y]
          by_cases hy : y = k
          · subst hy
            simp [mergedVal, hka, hkb, hab]
          · simp [hy]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hab)] at hf
          apply key _ _ hf
          intro y
          rw [List.foldl_append]
          simp only [List.foldl_cons, List.foldl_nil]
          rw [IStore.get_update]
          simp only [RStore.update]
          by_cases hy : y = k
          · subst hy
            simp [mergedVal, hka, hkb, hab]
          · simp only [hy, ↓reduceIte]; rw [hinv y]
            simp [hy]

/-- At a merge, each variable that both branches bind keeps its value when the branches agree
    on it (ignoring source locations), and becomes `if guard then va else vb` when they don't.
    Both stores must start from the same base store, as every path of one run does. -/
theorem mergeEnvs_store {scfg : ExploreCfg} {j : Join}
    {ea eb em : @IEnv Expression (symLang scfg)} {sa sb st : PathState} {n : Nat}
    (h : mergeEnvs j ea eb sa sb = some (em, st, n)) :
    letI := symLang scfg
    ea.store.base = eb.store.base →
    ∀ {x : CoreIdent} {va vb : Expression.Expr},
    ea.store.get x = some va → eb.store.get x = some vb →
      em.store.get x = some (if va.beqIgnoringMetadata vb = true then va
        else LExpr.ite symExecLoc j.guard va vb) := by
  letI := symLang scfg
  intro hbase x va vb hxa hxb
  obtain ⟨diffs, hd, rfl, -⟩ := mergeEnvs_some h
  have hfold := foldlM_diffs j.guard ea.store eb.store _ [] diffs []
    (by intro y; simp) hd x
  simp only [List.nil_append] at hfold
  show (diffs.foldl (fun σ x => σ.update x.fst x.snd) ea.store).get x = _
  rw [hfold]
  split
  · simp [mergedVal, hxa, hxb]
  · -- `x` was written in neither branch: both read the shared base.
    rename_i hx
    rw [List.mem_eraseDups, List.mem_append, Std.TreeMap.mem_keys, Std.TreeMap.mem_keys] at hx
    have hna : InterpLang.writesFind? ea.store.writes x = none := by
      show StoreWrites.find? _ _ = none
      unfold StoreWrites.find?
      exact Std.TreeMap.getElem?_eq_none (fun h => hx (Or.inl h))
    have hnb : InterpLang.writesFind? eb.store.writes x = none := by
      show StoreWrites.find? _ _ = none
      unfold StoreWrites.find?
      exact Std.TreeMap.getElem?_eq_none (fun h => hx (Or.inr h))
    have hab : va = vb := by
      simp only [IStore.get, hna, hnb] at hxa hxb
      rw [hbase] at hxa
      rw [hxa] at hxb
      exact Option.some.inj hxb
    subst hab
    simp [LExpr.beqIgnoringMetadata_refl va, hxa]

/-- When both branches bind `x`, to `va` and `vb`, under every model the merged value of `x`
    denotes `va` where the guard holds and `vb` where it doesn't. -/
theorem mergeEnvs_store_denote {scfg : ExploreCfg} {j : Join}
    {ea eb em : @IEnv Expression (symLang scfg)} {sa sb st : PathState} {n : Nat}
    (h : mergeEnvs j ea eb sa sb = some (em, st, n)) :
    letI := symLang scfg
    ea.store.base = eb.store.base →
    ∀ {x : CoreIdent} {va vb : Expression.Expr},
    ea.store.get x = some va → eb.store.get x = some vb →
    ∀ (tc : TyConstrInterp) (op : OpInterp tc) (fv : FreeVarVal CoreLParams tc) (vt : TyVarVal)
      {τ : LMonoTy} (hg : LExpr.HasTypeA [] j.guard .bool)
      (ha : LExpr.HasTypeA [] va τ) (hb : LExpr.HasTypeA [] vb τ),
    ∃ v, em.store.get x = some v ∧
      ∃ hv : LExpr.HasTypeA [] v τ,
        LExpr.denote tc op fv vt .nil v τ hv =
          bif LExpr.denote tc op fv vt .nil j.guard .bool hg
          then LExpr.denote tc op fv vt .nil va τ ha
          else LExpr.denote tc op fv vt .nil vb τ hb := by
  intro hbase x va vb hxa hxb tc op fv vt τ hg ha hb
  have hx := mergeEnvs_store h hbase hxa hxb
  refine ⟨_, hx, ?_⟩
  by_cases hab : va.beqIgnoringMetadata vb = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hab)]
    refine ⟨ha, ?_⟩
    have hmod : LExpr.eqModuloMeta va vb = true :=
      (LExpr.beq_eq va.eraseMetadata vb.eraseMetadata).mpr
        (eraseMetadata_eq_of_beqIgnoringMetadata hab)
    rw [← eqModuloMeta_true_implies_denote_eq tc op fv vt .nil ha hb hmod]
    cases LExpr.denote tc op fv vt .nil j.guard .bool hg <;> rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hab)]
    exact ⟨.ite hg ha hb, denote_ite .nil hg ha hb _⟩

/-- The merged path condition holds under a model exactly when the guard and the then-branch's
    path condition hold, or the guard fails and the else-branch's holds. This needs each
    branch's path condition to be its own entries, then the guard (then-branch) or its negation
    (else-branch), then a prefix of length `j.basePcLen` that both share, and the model's truth
    predicate to respect `negate` (`NegSound`), `if`, and `true`. -/
theorem mergeEnvs_pc {scfg : ExploreCfg} {j : Join}
    {ea eb em : @IEnv Expression (symLang scfg)} {sa sb st : PathState} {n : Nat}
    (h : mergeEnvs j ea eb sa sb = some (em, st, n))
    {holds : Expression.Expr → Prop} (hneg : NegSound holds)
    (hite : ∀ g t e,
      holds (LExpr.ite symExecLoc g t e) ↔ (holds g ∧ holds t) ∨ (¬ holds g ∧ holds e))
    (htrue : holds Core.true)
    {ownA ownB base : List (String × Expression.Expr)} {la lb : String}
    (hpa : sa.pc = ownA ++ (la, j.guard) :: base)
    (hpb : sb.pc = ownB ++ (lb, negate j.guard) :: base)
    (hlen : base.length = j.basePcLen) :
    PCHolds holds st ↔
      (holds j.guard ∧ PCHolds holds sa) ∨ (¬ holds j.guard ∧ PCHolds holds sb) := by
  obtain ⟨_, _, _, rfl⟩ := mergeEnvs_some h
  have own : ∀ (o : List (String × Expression.Expr)) (l : String) (g : Expression.Expr),
      (List.take ((o ++ (l, g) :: base).length - j.basePcLen) (o ++ (l, g) :: base)).dropLast = o ∧
      List.drop ((o ++ (l, g) :: base).length - j.basePcLen) (o ++ (l, g) :: base) = base := by
    intro o l g
    have e : o ++ (l, g) :: base = (o ++ [(l, g)]) ++ base := by simp
    have hl : (o ++ [(l, g)]).length = (o ++ [(l, g)] ++ base).length - j.basePcLen := by
      simp only [List.length_append, List.length_singleton, ← hlen]; omega
    rw [e, List.take_left' hl, List.drop_left' hl, List.dropLast_concat]
    exact ⟨rfl, rfl⟩
  obtain ⟨hoa, hba⟩ := own ownA la j.guard
  obtain ⟨hob, -⟩ := own ownB lb (negate j.guard)
  simp only [PCHolds, hpa, hpb, hoa, hba, hob, List.mem_append, List.mem_map, List.mem_cons]
  by_cases hg : holds j.guard
  · constructor
    · intro hm
      refine Or.inl ⟨hg, ?_⟩
      rintro p (hp | hp | hp)
      · have := hm (p.1, LExpr.ite symExecLoc j.guard p.2 Core.true)
          (Or.inl (Or.inr ⟨p, hp, rfl⟩))
        rcases (hite _ _ _).1 this with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact absurd hg h
      · rw [hp]; exact hg
      · exact hm p (Or.inr hp)
    · rintro (⟨-, ha⟩ | ⟨h, _⟩)
      · rintro p ((⟨q, -, rfl⟩ | ⟨q, hq, rfl⟩) | hp)
        · exact (hite _ _ _).2 (Or.inl ⟨hg, htrue⟩)
        · exact (hite _ _ _).2 (Or.inl ⟨hg, ha q (Or.inl hq)⟩)
        · exact ha p (Or.inr (Or.inr hp))
      · exact absurd hg h
  · have hng : holds (negate j.guard) := (hneg _).2 hg
    constructor
    · intro hm
      refine Or.inr ⟨hg, ?_⟩
      rintro p (hp | hp | hp)
      · have := hm (p.1, LExpr.ite symExecLoc j.guard Core.true p.2)
          (Or.inl (Or.inl ⟨p, hp, rfl⟩))
        rcases (hite _ _ _).1 this with ⟨h, _⟩ | ⟨_, h⟩
        · exact absurd h hg
        · exact h
      · rw [hp]; exact hng
      · exact hm p (Or.inr hp)
    · rintro (⟨h, _⟩ | ⟨-, hb⟩)
      · exact absurd h hg
      · rintro p ((⟨q, hq, rfl⟩ | ⟨q, -, rfl⟩) | hp)
        · exact (hite _ _ _).2 (Or.inr ⟨hg, hb q (Or.inl hq)⟩)
        · exact (hite _ _ _).2 (Or.inr ⟨hg, htrue⟩)
        · exact hb p (Or.inr (Or.inr hp))

/-- With `endOnFailedChecks` off, no failed check ends a path. -/
theorem failedCheckStatus_off {scfg : ExploreCfg} (h : scfg.endOnFailedChecks = false)
    (before : List (String × Expression.Expr)) (st : PathState) :
    failedCheckStatus scfg before st = none := by
  simp [failedCheckStatus, h]

/-- Without a path limit, the explorer is never over it. -/
theorem overPathLimit_none {scfg : ExploreCfg} {C : Type} (h : scfg.maxPaths = none)
    (s : DState C) : overPathLimit (scfg := scfg) s = false := by
  simp [overPathLimit, h]

/-- A merge whose branches added no entry to the record of choices keeps the record from the
    fork. -/
theorem mergeChoices_nil (j : Join) (ma mb : List Choice)
    (ha : ma.length = j.baseChoices) (hb : mb.length = j.baseChoices) :
    mergeChoices j ma mb = ma := by
  simp [mergeChoices, ha, hb]

end -- public section

end Core.SymExec
