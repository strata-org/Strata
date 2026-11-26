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
import Strata.Util.DecidableEqProps

/-! # Properties of the path explorer: merging, and options at their defaults

What merging the two branches of a fork at its join gives, per branch, for the merge of their
environments (`mergeEnvs`), which `mergeBranches` runs for every kind of configuration
(`mergeBranches_eq`):

* `mergeEnvs_store`: at a merge, each variable that both branches bind keeps its value when the
  branches agree on it (ignoring source locations), and becomes `if guard then va else vb` when
  they don't. Both stores must start from the same base store, as every path of one run does.
* `mergeEnvs_store_denote`: under any model, that value denotes what the then-branch's value
  denotes where the guard is true, and the else-branch's where it is false.
* `mergeEnvs_pc`, `mergeEnvs_pc_of_branch`: if the merged path condition holds under a model,
  the guard holds and the then-branch's path condition does, or the guard fails and the
  else-branch's does; conversely when, besides, the join definitions the other branch keeps
  unguarded (`mergeOwn`) hold.
* `nameJoinValues_spec`, `pcHolds_append`: naming the merged values adds their definitions
  `s == v`, with fresh symbols `s`, in front of the path condition, and binds each named variable
  to its symbol; the path condition then holds iff the old one and the definitions do.
* `mergeEnvs_shape`: a merge succeeds only on branches whose path conditions end in the guard
  (then-branch) or its negation (else-branch) above one shared prefix of the fork's length.
* `mergeChoices_nil`: a merge of branches that made no choices keeps the record of choices.

What each kind of configuration brings to a merge: a structured path its terminal environment
(`structuredShape_joinEnv_setJoinEnv`); a CFG path its environment without the locals that no block
dominating the join declares, keeping the store's base and every other variable's value
(`cfgShape_forMerge_block`), never one that a block dominating the join declares
(`cfgOutOfScope_not_dominating`).

How a step can end a path: `infeasibleStatus_infeasible` (only as infeasible, at a literal
`false`), and `infeasibleStatus_sound` (then no model satisfies its path condition). And the
explorer's options at their defaults: `overPathLimit_none` (no path limit is reached).
-/

namespace Core.SymExec

open Imperative Lambda

public section

/-- When `mergeEnvs` succeeds, the comparison of the two stores succeeded, and the merged
    environment and path state are built from its result. -/
private theorem mergeEnvs_some {scfg : ExploreCfg} {j : Join}
    {ea eb em : @IEnv Expression (symLang scfg)} {sa sb st : PathState}
    {ds : List (CoreIdent × Expression.Expr)}
    (h : mergeEnvs j ea eb sa sb = some (em, st, ds)) :
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
              pc := mergeOwn (LExpr.ite symExecLoc j.guard Core.true ·)
                      (joinDefsOf (List.drop (sa.pc.length - j.basePcLen) sa.pc))
                      (List.take (sb.pc.length - j.basePcLen) sb.pc).dropLast ++
                    mergeOwn (LExpr.ite symExecLoc j.guard · Core.true)
                      (joinDefsOf (List.drop (sa.pc.length - j.basePcLen) sa.pc))
                      (List.take (sa.pc.length - j.basePcLen) sa.pc).dropLast ++
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
    (`ProcBodyShape.forMerge`), merges them with `mergeEnvs`, names the merged values
    (`nameJoinValues`, counting from the join counter `joinNext`, with the types each branch
    recorded), and continues at the then-branch's configuration. -/
theorem mergeBranches_eq {scfg : ExploreCfg} {C : Type} {sh : ProcBodyShape scfg C} {j : Join}
    {joinNext : Nat} {a b m : Entry C} {n u k : Nat}
    (h : mergeBranches sh j joinNext a b = some (m, n, u, k)) :
    ∃ ea eb em st ds, sh.joinEnv a.cfg = some ea ∧ sh.joinEnv b.cfg = some eb ∧
      mergeEnvs j (sh.forMerge j.site ea) (sh.forMerge j.site eb) a.st b.st =
        some (em, st, ds) ∧ n = ds.length ∧
      m.cfg = sh.setJoinEnv a.cfg (nameJoinValues joinNext a.st.types b.st.types ds em st).1 ∧
      m.st = (nameJoinValues joinNext a.st.types b.st.types ds em st).2.1 ∧
      u = (nameJoinValues joinNext a.st.types b.st.types ds em st).2.2.1 ∧
      k = (nameJoinValues joinNext a.st.types b.st.types ds em st).2.2.2 := by
  unfold mergeBranches at h
  split at h
  · rename_i ea eb hea heb
    split at h
    · rename_i em st ds hm
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨ea, eb, em, st, ds, hea, heb, hm, rfl, rfl, rfl, rfl, rfl⟩
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

/-- The locals a merge at block `j` leaves out, given the dominators `dom` and each block's
    declared locals `decls`: those declared in a block that does not dominate `j` and in no block
    that does. -/
def cfgOutOfScope (dom : CFG.Dom.DomMap)
    (decls : List (String × List CoreIdent)) (j : String) : List CoreIdent :=
  let kept := decls.flatMap fun p => bif CFG.Dom.dominates dom p.1 j then p.2 else []
  decls.flatMap fun p =>
    bif CFG.Dom.dominates dom p.1 j then [] else p.2.filter (fun x => !kept.contains x)

/-- A `flatMap` whose function gives `[]` on an entry with no locals is unchanged by first
    dropping such entries. -/
private theorem flatMap_filter_nonempty (l : List (String × List CoreIdent))
    (f : String × List CoreIdent → List CoreIdent) (hf : ∀ d, f (d, []) = []) :
    (l.filter (!·.2.isEmpty)).flatMap f = l.flatMap f := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨d, xs⟩ := p
    cases xs with
    | nil => simp [ih, hf]
    | cons x xs => simp [ih]

/-- Looking only at the blocks that declare locals finds the same out-of-scope locals at `j` as
    looking at every block (`cfgOutOfScope`). -/
private theorem localsOutOfScope_filter (dom : CFG.Dom.DomMap)
    (decls : List (String × List CoreIdent)) (j : String) :
    localsOutOfScope dom (decls.filter (!·.2.isEmpty)) j = cfgOutOfScope dom decls j := by
  have hkept := flatMap_filter_nonempty decls
    (fun (p : String × List CoreIdent) => bif CFG.Dom.dominates dom p.1 j then p.2 else [])
    (fun d => by simp)
  unfold localsOutOfScope cfgOutOfScope
  split
  · rename_i h
    rw [← flatMap_filter_nonempty decls _ (fun d => by simp), List.isEmpty_iff.mp h]
    rfl
  · simp only [Std.HashSet.contains_ofList] at hkept ⊢
    rw [hkept]
    exact flatMap_filter_nonempty decls _ (fun d => by simp)

/-- A merge at `j` never leaves out a local that some block dominating `j` declares. -/
theorem cfgOutOfScope_not_dominating {dom : CFG.Dom.DomMap}
    {decls : List (String × List CoreIdent)} {j : String} {x : CoreIdent}
    (hx : x ∈ cfgOutOfScope dom decls j) :
    ∀ d xs, (d, xs) ∈ decls → CFG.Dom.dominates dom d j = true → x ∉ xs := by
  intro d xs hd hdom hxs
  simp only [cfgOutOfScope, List.mem_flatMap] at hx
  obtain ⟨p, _, hx⟩ := hx
  cases hp : CFG.Dom.dominates dom p.1 j with
  | true => simp [hp] at hx
  | false =>
    simp only [hp, cond_eq_ite, List.contains_eq_mem, List.mem_flatMap, List.mem_ite_nil_right,
      Prod.exists, Bool.false_eq_true, ↓reduceIte, List.mem_filter, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not, not_exists, not_and] at hx
    exact hx.2 d xs hd hdom hxs

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

/-- A CFG path brings to a merge at block `j` its environment without the locals that no block
    dominating `j` declares (`cfgOutOfScope`, `IStore.drop`): the store keeps its base, and reads
    as `RStore.dropVars` of those locals, so every other variable keeps its value. -/
theorem cfgShape_forMerge_block {scfg : ExploreCfg} (g : Core.DetCFG) (j : String)
    (e : @IEnv Expression (symLang scfg)) :
    letI := symLang scfg
    ((cfgShape scfg g).forMerge (.block j) e).store.base = e.store.base ∧
      ((cfgShape scfg g).forMerge (.block j) e).store.get =
        RStore.dropVars (cfgOutOfScope g.computeDominators
          (g.blocks.map fun (d, b) => (d, WF.blockInitVars b)) j) e.store.get :=
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
    {ea eb em : @IEnv Expression (symLang scfg)} {sa sb st : PathState}
    {ds : List (CoreIdent × Expression.Expr)}
    (h : mergeEnvs j ea eb sa sb = some (em, st, ds)) :
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
    {ea eb em : @IEnv Expression (symLang scfg)} {sa sb st : PathState}
    {ds : List (CoreIdent × Expression.Expr)}
    (h : mergeEnvs j ea eb sa sb = some (em, st, ds)) :
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
        (LExpr.eraseMetadata_eq_of_beqIgnoringMetadata hab)
    rw [← eqModuloMeta_true_implies_denote_eq tc op fv vt .nil ha hb hmod]
    cases LExpr.denote tc op fv vt .nil j.guard .bool hg <;> rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hab)]
    exact ⟨.ite hg ha hb, denote_ite .nil hg ha hb _⟩

/-- Each entry `mergeOwn` returns is an entry of `own`, as it is or under `wrap`, and each entry
    of `own` is returned in one of those two forms. -/
private theorem mergeOwn_mem (wrap : Expression.Expr → Expression.Expr)
    (defined : Std.HashSet String) (own : List (String × Expression.Expr)) :
    (∀ q ∈ mergeOwn wrap defined own, ∃ p ∈ own, q = p ∨ q = (p.1, wrap p.2)) ∧
    (∀ p ∈ own, p ∈ mergeOwn wrap defined own ∨ (p.1, wrap p.2) ∈ mergeOwn wrap defined own) := by
  unfold mergeOwn
  induction own with
  | nil => simp [mergeOwn.go]
  | cons a rest ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨l, e⟩ := a
    simp only [mergeOwn.go]
    generalize hr : mergeOwn.go wrap defined rest = r at ih1 ih2 ⊢
    obtain ⟨d, out⟩ := r
    simp only at ih1 ih2 ⊢
    split
    · refine ⟨?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact ⟨(l, e), List.mem_cons_self .., Or.inl rfl⟩
        · obtain ⟨p, hp, h⟩ := ih1 q hq
          exact ⟨p, List.mem_cons_of_mem _ hp, h⟩
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact Or.inl (List.mem_cons_self ..)
        · rcases ih2 p hp with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr (List.mem_cons_of_mem _ h)
    · refine ⟨?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact ⟨(l, e), List.mem_cons_self .., Or.inr rfl⟩
        · obtain ⟨p, hp, h⟩ := ih1 q hq
          exact ⟨p, List.mem_cons_of_mem _ hp, h⟩
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact Or.inr (List.mem_cons_self ..)
        · rcases ih2 p hp with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr (List.mem_cons_of_mem _ h)

/-- The merged path condition, for branches whose path conditions have the shape merging relies
    on: each branch's own entries as `mergeOwn` keeps them, then the shared prefix. -/
private theorem mergeEnvs_pc_eq {scfg : ExploreCfg} {j : Join}
    {ea eb em : @IEnv Expression (symLang scfg)} {sa sb st : PathState}
    {ds : List (CoreIdent × Expression.Expr)}
    (h : mergeEnvs j ea eb sa sb = some (em, st, ds))
    {ownA ownB base : List (String × Expression.Expr)} {la lb : String}
    (hpa : sa.pc = ownA ++ (la, j.guard) :: base)
    (hpb : sb.pc = ownB ++ (lb, negate j.guard) :: base)
    (hlen : base.length = j.basePcLen) :
    st.pc = mergeOwn (LExpr.ite symExecLoc j.guard Core.true ·) (joinDefsOf base) ownB ++
      mergeOwn (LExpr.ite symExecLoc j.guard · Core.true) (joinDefsOf base) ownA ++ base := by
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
  simp only [hpa, hpb, hoa, hba, hob]

/-- If the merged path condition holds under a model, the guard holds and the then-branch's path
    condition does, or the guard fails and the else-branch's does. This needs the model's truth
    predicate to respect `negate` (`NegSound`) and `if`; the form of the two path conditions it
    relies on, `mergeEnvs` checks (`mergeEnvs_shape`). -/
private theorem mergeEnvs_pc_of_shape {scfg : ExploreCfg} {j : Join}
    {ea eb em : @IEnv Expression (symLang scfg)} {sa sb st : PathState}
    {ds : List (CoreIdent × Expression.Expr)}
    (h : mergeEnvs j ea eb sa sb = some (em, st, ds))
    {holds : Expression.Expr → Prop} (hneg : NegSound holds)
    (hite : ∀ g t e,
      holds (LExpr.ite symExecLoc g t e) ↔ (holds g ∧ holds t) ∨ (¬ holds g ∧ holds e))
    {ownA ownB base : List (String × Expression.Expr)} {la lb : String}
    (hpa : sa.pc = ownA ++ (la, j.guard) :: base)
    (hpb : sb.pc = ownB ++ (lb, negate j.guard) :: base)
    (hlen : base.length = j.basePcLen) :
    PCHolds holds st →
      (holds j.guard ∧ PCHolds holds sa) ∨ (¬ holds j.guard ∧ PCHolds holds sb) := by
  have hst := mergeEnvs_pc_eq h hpa hpb hlen
  intro hm
  have inSt : ∀ p, p ∈ st.pc → holds p.2 := hm
  rw [hst] at inSt
  by_cases hg : holds j.guard
  · refine Or.inl ⟨hg, ?_⟩
    intro p hp
    rw [hpa] at hp
    rcases List.mem_append.1 hp with hp | hp
    · rcases (mergeOwn_mem _ (joinDefsOf base) ownA).2 p hp with hk | hw
      · exact inSt p (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hk))))
      · have := inSt _ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hw))))
        rcases (hite _ _ _).1 this with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact absurd hg h
    · rcases List.mem_cons.1 hp with rfl | hp
      · exact hg
      · exact inSt p (List.mem_append.2 (Or.inr hp))
  · refine Or.inr ⟨hg, ?_⟩
    intro p hp
    rw [hpb] at hp
    rcases List.mem_append.1 hp with hp | hp
    · rcases (mergeOwn_mem _ (joinDefsOf base) ownB).2 p hp with hk | hw
      · exact inSt p (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hk))))
      · have := inSt _ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hw))))
        rcases (hite _ _ _).1 this with ⟨h, _⟩ | ⟨_, h⟩
        · exact absurd h hg
        · exact h
    · rcases List.mem_cons.1 hp with rfl | hp
      · exact (hneg _).2 hg
      · exact inSt p (List.mem_append.2 (Or.inr hp))

/-- The merged path condition holds under a model when the guard and the then-branch's path
    condition hold, or the guard fails and the else-branch's holds, and the entries of the other
    branch that the merged path condition holds unguarded (its join definitions, `mergeOwn`) hold
    too. -/
private theorem mergeEnvs_pc_of_branch_of_shape {scfg : ExploreCfg} {j : Join}
    {ea eb em : @IEnv Expression (symLang scfg)} {sa sb st : PathState}
    {ds : List (CoreIdent × Expression.Expr)}
    (h : mergeEnvs j ea eb sa sb = some (em, st, ds))
    {holds : Expression.Expr → Prop}
    (hite : ∀ g t e,
      holds (LExpr.ite symExecLoc g t e) ↔ (holds g ∧ holds t) ∨ (¬ holds g ∧ holds e))
    (htrue : holds Core.true)
    {ownA ownB base : List (String × Expression.Expr)} {la lb : String}
    (hpa : sa.pc = ownA ++ (la, j.guard) :: base)
    (hpb : sb.pc = ownB ++ (lb, negate j.guard) :: base)
    (hlen : base.length = j.basePcLen) :
    (holds j.guard ∧ PCHolds holds sa ∧ ∀ p ∈ ownB, p ∈ st.pc → holds p.2) ∨
      (¬ holds j.guard ∧ PCHolds holds sb ∧ ∀ p ∈ ownA, p ∈ st.pc → holds p.2) →
      PCHolds holds st := by
  have hst := mergeEnvs_pc_eq h hpa hpb hlen
  rintro (⟨hg, ha, hB⟩ | ⟨hg, hb, hA⟩) p hp
  · have hp' := hp
    rw [hst] at hp'
    rcases List.mem_append.1 hp' with hp' | hp'
    · rcases List.mem_append.1 hp' with hq | hq
      · obtain ⟨q, hq', h⟩ := (mergeOwn_mem _ (joinDefsOf base) ownB).1 p hq
        rcases h with h | h
        · subst h; exact hB p hq' hp
        · subst h; exact (hite _ _ _).2 (Or.inl ⟨hg, htrue⟩)
      · obtain ⟨q, hq', h⟩ := (mergeOwn_mem _ (joinDefsOf base) ownA).1 p hq
        have hqa : holds q.2 := ha q (by rw [hpa]; exact List.mem_append.2 (Or.inl hq'))
        rcases h with h | h
        · subst h; exact hqa
        · subst h; exact (hite _ _ _).2 (Or.inl ⟨hg, hqa⟩)
    · exact ha p (by rw [hpa]; exact List.mem_append.2 (Or.inr (List.mem_cons_of_mem _ hp')))
  · have hp' := hp
    rw [hst] at hp'
    rcases List.mem_append.1 hp' with hp' | hp'
    · rcases List.mem_append.1 hp' with hq | hq
      · obtain ⟨q, hq', h⟩ := (mergeOwn_mem _ (joinDefsOf base) ownB).1 p hq
        have hqb : holds q.2 := hb q (by rw [hpb]; exact List.mem_append.2 (Or.inl hq'))
        rcases h with h | h
        · subst h; exact hqb
        · subst h; exact (hite _ _ _).2 (Or.inr ⟨hg, hqb⟩)
      · obtain ⟨q, hq', h⟩ := (mergeOwn_mem _ (joinDefsOf base) ownA).1 p hq
        rcases h with h | h
        · subst h; exact hA p hq' hp
        · subst h; exact (hite _ _ _).2 (Or.inr ⟨hg, htrue⟩)
    · exact hb p (by rw [hpb]; exact List.mem_append.2 (Or.inr (List.mem_cons_of_mem _ hp')))

/-- `isNegationOf ng g` holds only when `ng` is `negate g`. -/
private theorem isNegationOf_eq {ng g : Expression.Expr} (h : isNegationOf ng g = true) :
    ng = negate g := by
  unfold isNegationOf at h
  split at h
  · simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨hc, hm⟩, ht⟩, he⟩ := h
    rw [ptrFastEq_eq hc, ptrFastEq_eq hm, ptrFastEq_eq ht, ptrFastEq_eq he]
    rfl
  · cases h

/-- A merge succeeds only on branches whose path conditions have the form merging relies on:
    the then-branch's is its own entries, then the guard, then a prefix `base` of length
    `j.basePcLen`; the else-branch's is its own entries, then the guard's negation, then the same
    `base` (`mergeShapeOk`). -/
theorem mergeEnvs_shape {scfg : ExploreCfg} {j : Join}
    {ea eb em : @IEnv Expression (symLang scfg)} {sa sb st : PathState}
    {ds : List (CoreIdent × Expression.Expr)}
    (h : mergeEnvs j ea eb sa sb = some (em, st, ds)) :
    ∃ (ownA ownB base : List (String × Expression.Expr)) (la lb : String),
      sa.pc = ownA ++ (la, j.guard) :: base ∧ sb.pc = ownB ++ (lb, negate j.guard) :: base ∧
      base.length = j.basePcLen := by
  unfold mergeEnvs at h
  split at h
  · cases h
  rename_i hc
  have hok : mergeShapeOk j sa sb = true := by
    cases hm : mergeShapeOk j sa sb
    · simp [hm] at hc
    · rfl
  unfold mergeShapeOk at hok
  generalize hda : sa.pc.drop (sa.pc.length - (j.basePcLen + 1)) = da at hok
  generalize hdb : sb.pc.drop (sb.pc.length - (j.basePcLen + 1)) = db at hok
  match da, db, hok with
  | (la, ga) :: ba, (lb, gb) :: bb, hok =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨hlen, hga⟩, hgb⟩, hbb⟩ := hok
    refine ⟨sa.pc.take (sa.pc.length - (j.basePcLen + 1)),
      sb.pc.take (sb.pc.length - (j.basePcLen + 1)), ba, la, lb, ?_, ?_, hlen⟩
    · rw [← ptrFastEq_eq hga, ← hda, List.take_append_drop]
    · rw [← isNegationOf_eq hgb, ptrFastEq_eq hbb, ← hdb, List.take_append_drop]
  | [], _, hok => simp at hok
  | _ :: _, [], hok => simp at hok

/-- If the merged path condition holds under a model, the guard and the then-branch's path
    condition hold, or the guard fails and the else-branch's holds. This needs the model's truth
    predicate to respect `negate` (`NegSound`) and `if`; the form of the two path conditions it
    relies on, `mergeEnvs` checks (`mergeEnvs_shape`). -/
theorem mergeEnvs_pc {scfg : ExploreCfg} {j : Join}
    {ea eb em : @IEnv Expression (symLang scfg)} {sa sb st : PathState}
    {ds : List (CoreIdent × Expression.Expr)}
    (h : mergeEnvs j ea eb sa sb = some (em, st, ds))
    {holds : Expression.Expr → Prop} (hneg : NegSound holds)
    (hite : ∀ g t e,
      holds (LExpr.ite symExecLoc g t e) ↔ (holds g ∧ holds t) ∨ (¬ holds g ∧ holds e)) :
    PCHolds holds st →
      (holds j.guard ∧ PCHolds holds sa) ∨ (¬ holds j.guard ∧ PCHolds holds sb) := by
  obtain ⟨_, _, _, _, _, hpa, hpb, hlen⟩ := mergeEnvs_shape h
  exact mergeEnvs_pc_of_shape h hneg hite hpa hpb hlen

/-- With the branches' own entries `ownA` and `ownB` (`mergeEnvs_shape`): the merged path
    condition holds under a model when the guard and the then-branch's path condition hold,
    or the guard fails and the else-branch's holds, and the other branch's entries that the
    merged path condition holds unguarded (its join definitions, `mergeOwn`) hold too. This
    needs the model's truth predicate to respect `if` and `true`. -/
theorem mergeEnvs_pc_of_branch {scfg : ExploreCfg} {j : Join}
    {ea eb em : @IEnv Expression (symLang scfg)} {sa sb st : PathState}
    {ds : List (CoreIdent × Expression.Expr)}
    (h : mergeEnvs j ea eb sa sb = some (em, st, ds))
    {holds : Expression.Expr → Prop}
    (hite : ∀ g t e,
      holds (LExpr.ite symExecLoc g t e) ↔ (holds g ∧ holds t) ∨ (¬ holds g ∧ holds e))
    (htrue : holds Core.true) :
    ∃ (ownA ownB base : List (String × Expression.Expr)) (la lb : String),
      sa.pc = ownA ++ (la, j.guard) :: base ∧ sb.pc = ownB ++ (lb, negate j.guard) :: base ∧
      ((holds j.guard ∧ PCHolds holds sa ∧ ∀ p ∈ ownB, p ∈ st.pc → holds p.2) ∨
        (¬ holds j.guard ∧ PCHolds holds sb ∧ ∀ p ∈ ownA, p ∈ st.pc → holds p.2) →
        PCHolds holds st) := by
  obtain ⟨ownA, ownB, base, la, lb, hpa, hpb, hlen⟩ := mergeEnvs_shape h
  exact ⟨ownA, ownB, base, la, lb, hpa, hpb,
    mergeEnvs_pc_of_branch_of_shape h hite htrue hpa hpb hlen⟩

/-- One naming step either leaves the store, the path condition, the counter and the named
    values alone (a function-typed or untyped value; only the unnamed count may change), binds
    the variable to the symbol of a value named earlier at the join that equals its value up to
    source locations, or binds it to a fresh symbol numbered `k0` and defines that symbol. -/
private theorem nameJoinStep_cases {scfg : ExploreCfg}
    (ta tb : Std.TreeMap CoreIdent LMonoTy identCmp)
    (σ0 : @IStore Expression (symLang scfg)) (pc0 : List (String × Expression.Expr))
    (k0 u0 : Nat) (n0 : List (Expression.Expr × Expression.Expr)) (x : CoreIdent)
    (v : Expression.Expr) :
    letI := symLang scfg
    let r := nameJoinStep (scfg := scfg) ta tb (σ0, pc0, k0, u0, n0) (x, v)
    (r.1 = σ0 ∧ r.2.1 = pc0 ∧ r.2.2.1 = k0 ∧ r.2.2.2.2 = n0) ∨
    (∃ v' s, (v', s) ∈ n0 ∧ v'.beqIgnoringMetadata v = true ∧
      r = (σ0.update x s, pc0, k0, u0, n0)) ∨
    (∃ ty, r = (σ0.update x (mkSym scfg.joinPre k0 ty x.name),
      (joinValueLabel x, LExpr.eq symExecLoc (mkSym scfg.joinPre k0 ty x.name) v) :: pc0, k0 + 1,
      u0, (v, mkSym scfg.joinPre k0 ty x.name) :: n0)) := by
  letI := symLang scfg
  simp only [nameJoinStep]
  repeat' split
  all_goals first
    | exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    | exact Or.inr (Or.inr ⟨_, rfl⟩)
    | exact Or.inr (Or.inl ⟨_, _, List.mem_of_find?_eq_some ‹List.find? _ n0 = some _›,
        by have h := List.find?_some ‹List.find? _ n0 = some _›
           simp only [Bool.and_eq_true] at h
           exact h.1, rfl⟩)

/-- What naming a join's merged values does, from store `σ0`, path condition `pc0`, counter `k0`
    and values `n0` named so far (each defined in `pc0`): it adds definitions `defs` in front of
    `pc0`, each `s == v` for the merged value `v` of some variable of `ds` and a symbol `s`
    numbered from `k0` up to below the final count; and each variable keeps its value or is bound
    to a symbol defined in the final path condition as a value equal to its merged value up to
    source locations. -/
private theorem nameJoinStep_fold {scfg : ExploreCfg}
    (ta tb : Std.TreeMap CoreIdent LMonoTy identCmp)
    (ds : List (CoreIdent × Expression.Expr)) :
    letI := symLang scfg
    ∀ (σ0 : IStore Expression) (pc0 : List (String × Expression.Expr)) (k0 u0 : Nat)
      (n0 : List (Expression.Expr × Expression.Expr)),
    (∀ p ∈ n0, ∃ l, (l, LExpr.eq symExecLoc p.2 p.1) ∈ pc0) →
    let r := ds.foldl (nameJoinStep (scfg := scfg) ta tb) (σ0, pc0, k0, u0, n0)
    ∃ defs : List (String × Expression.Expr),
      r.2.1 = defs ++ pc0 ∧ k0 ≤ r.2.2.1 ∧
      (∀ d ∈ defs, ∃ x v ty k, (x, v) ∈ ds ∧ k0 ≤ k ∧ k < r.2.2.1 ∧
        d = (joinValueLabel x, LExpr.eq symExecLoc (mkSym scfg.joinPre k ty x.name) v)) ∧
      (∀ y, r.1.get y = σ0.get y ∨
        ∃ s v v' l, r.1.get y = some s ∧ (y, v) ∈ ds ∧ v'.beqIgnoringMetadata v = true ∧
          (l, LExpr.eq symExecLoc s v') ∈ r.2.1) := by
  letI := symLang scfg
  induction ds with
  | nil => intro σ0 pc0 k0 u0 n0 _; exact ⟨[], rfl, Nat.le_refl _, by simp, fun _ => Or.inl rfl⟩
  | cons p ds ih =>
    intro σ0 pc0 k0 u0 n0 hn
    obtain ⟨x, v⟩ := p
    simp only [List.foldl_cons]
    generalize hr0 : nameJoinStep (scfg := scfg) ta tb (σ0, pc0, k0, u0, n0) (x, v) = r0
    have hc := nameJoinStep_cases (scfg := scfg) ta tb σ0 pc0 k0 u0 n0 x v
    simp only [hr0] at hc
    rcases hc with ⟨h1, h2, h3, h4⟩ | ⟨v', s, hm, hb, hr⟩ | ⟨ty, hr⟩
    · have hr : r0 = (σ0, pc0, k0, r0.2.2.2.1, n0) := by
        obtain ⟨a, b, c, d, e⟩ := r0
        simp only at h1 h2 h3 h4 ⊢
        rw [h1, h2, h3, h4]
      rw [hr]
      obtain ⟨defs, e1, e2, e3, e4⟩ := ih σ0 pc0 k0 _ n0 hn
      refine ⟨defs, e1, e2, ?_, ?_⟩
      · intro d hd
        obtain ⟨x', v'', ty, k, hm', hk1, hk2, he⟩ := e3 d hd
        exact ⟨x', v'', ty, k, List.mem_cons_of_mem _ hm', hk1, hk2, he⟩
      · intro y
        rcases e4 y with h | ⟨s', w, w', l, hs, hm', hb', hd⟩
        · exact Or.inl h
        · exact Or.inr ⟨s', w, w', l, hs, List.mem_cons_of_mem _ hm', hb', hd⟩
    · rw [hr]
      obtain ⟨defs, e1, e2, e3, e4⟩ := ih (σ0.update x s) pc0 k0 u0 n0 hn
      refine ⟨defs, e1, e2, ?_, ?_⟩
      · intro d hd
        obtain ⟨x', v'', ty, k, hm', hk1, hk2, he⟩ := e3 d hd
        exact ⟨x', v'', ty, k, List.mem_cons_of_mem _ hm', hk1, hk2, he⟩
      · intro y
        rcases e4 y with h | ⟨s', w, w', l, hs, hm', hb', hd⟩
        · rw [IStore.get_update] at h
          by_cases hy : y = x
          · subst hy
            obtain ⟨l, hl⟩ := hn _ hm
            refine Or.inr ⟨s, v, v', l, ?_, List.mem_cons_self, hb, ?_⟩
            · rw [h]; simp [RStore.update]
            · rw [e1]; exact List.mem_append_right _ hl
          · left; rw [h]; simp [RStore.update, hy]
        · exact Or.inr ⟨s', w, w', l, hs, List.mem_cons_of_mem _ hm', hb', hd⟩
    · rw [hr]
      generalize hsym : mkSym scfg.joinPre k0 ty x.name = sym
      have hn' : ∀ p ∈ (v, sym) :: n0,
          ∃ l, (l, LExpr.eq symExecLoc p.2 p.1) ∈
            (joinValueLabel x, LExpr.eq symExecLoc sym v) :: pc0 := by
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨_, List.mem_cons_self⟩
        · obtain ⟨l, hl⟩ := hn p hp; exact ⟨l, List.mem_cons_of_mem _ hl⟩
      obtain ⟨defs, e1, e2, e3, e4⟩ := ih (σ0.update x sym)
        ((joinValueLabel x, LExpr.eq symExecLoc sym v) :: pc0) (k0 + 1) u0 ((v, sym) :: n0) hn'
      refine ⟨defs ++ [(joinValueLabel x, LExpr.eq symExecLoc sym v)], by simp [e1], by omega,
        ?_, ?_⟩
      · intro d hd
        rcases List.mem_append.1 hd with hd | hd
        · obtain ⟨x', v'', ty', k, hm', hk1, hk2, he⟩ := e3 d hd
          exact ⟨x', v'', ty', k, List.mem_cons_of_mem _ hm', by omega, hk2, he⟩
        · rw [List.mem_singleton] at hd
          exact ⟨x, v, ty, k0, List.mem_cons_self, Nat.le_refl _, by omega, by rw [hd, hsym]⟩
      · intro y
        rcases e4 y with h | ⟨s', w, w', l, hs, hm', hb', hd⟩
        · rw [IStore.get_update] at h
          by_cases hy : y = x
          · subst hy
            refine Or.inr ⟨sym, v, v, joinValueLabel y, ?_, List.mem_cons_self,
              LExpr.beqIgnoringMetadata_refl v, ?_⟩
            · rw [h]; simp [RStore.update]
            · rw [e1]; exact List.mem_append_right _ List.mem_cons_self
          · left; rw [h]; simp [RStore.update, hy]
        · exact Or.inr ⟨s', w, w', l, hs, List.mem_cons_of_mem _ hm', hb', hd⟩

/-- Naming a join's merged values (`nameJoinValues`) adds definitions `defs` in front of the path
    condition and keeps the rest of the path state; the join counter only grows: each
    definition is `s == v` for the merged value `v` of a variable of `ds` and a fresh symbol
    `s` (`ExploreCfg.joinPre`, numbered from `next` up to below the new counter); each variable
    keeps its value, or is bound to a symbol the new path condition defines as a value equal to
    its merged value up to source locations. So the named path condition holds under a model
    iff the unnamed one and the definitions do (`pcHolds_append`). -/
theorem nameJoinValues_spec {scfg : ExploreCfg} (next : Nat)
    (ta tb : Std.TreeMap CoreIdent LMonoTy identCmp)
    (ds : List (CoreIdent × Expression.Expr)) (env : @IEnv Expression (symLang scfg))
    (st : PathState) :
    letI := symLang scfg
    let r := nameJoinValues next ta tb ds env st
    ∃ defs : List (String × Expression.Expr),
      r.2.1 = { st with pc := defs ++ st.pc } ∧ next ≤ r.2.2.2 ∧
      r.1 = { env with store := r.1.store } ∧
      (∀ d ∈ defs, ∃ x v ty k, (x, v) ∈ ds ∧ next ≤ k ∧ k < r.2.2.2 ∧
        d = (joinValueLabel x, LExpr.eq symExecLoc (mkSym scfg.joinPre k ty x.name) v)) ∧
      (∀ y, r.1.store.get y = env.store.get y ∨
        ∃ s v v' l, r.1.store.get y = some s ∧ (y, v) ∈ ds ∧
          v'.beqIgnoringMetadata v = true ∧ (l, LExpr.eq symExecLoc s v') ∈ r.2.1.pc) := by
  letI := symLang scfg
  obtain ⟨defs, h1, h2, h3, h4⟩ :=
    nameJoinStep_fold (scfg := scfg) ta tb ds env.store st.pc next 0 [] (by simp)
  refine ⟨defs, ?_, h2, rfl, h3, h4⟩
  simp only [nameJoinValues]
  rw [h1]

/-- A path condition with entries `defs` in front holds under a model iff the path condition
    without them does and so do the entries: for naming a join's merged values, the named path
    condition holds iff the unnamed one and the definitions do (`nameJoinValues_spec`). -/
theorem pcHolds_append {holds : Expression.Expr → Prop} {st : PathState}
    {defs : List (String × Expression.Expr)} :
    PCHolds holds { st with pc := defs ++ st.pc } ↔
      PCHolds holds st ∧ ∀ d ∈ defs, holds d.2 := by
  simp only [PCHolds, List.mem_append]
  exact ⟨fun h => ⟨fun p hp => h p (Or.inr hp), fun d hd => h d (Or.inl hd)⟩,
    fun ⟨h1, h2⟩ p hp => hp.elim (h2 p) (h1 p)⟩

/-- Ending a path as infeasible is sound: if a step ends its path (`infeasibleStatus`), no model
    satisfies the path condition the step reached, for a model whose truth predicate holds of no
    literal `false`. So the path stands for no run, and dropping it loses no run's obligations. -/
theorem infeasibleStatus_sound {before : List (String × Expression.Expr)} {st : PathState}
    {s : NodeStatus} (h : infeasibleStatus before st = some s) {holds : Expression.Expr → Prop}
    (hfalse : ∀ c : Expression.Expr, LExpr.isFalse _ c = true → ¬ holds c) :
    ¬ PCHolds holds st := by
  intro hpc
  unfold infeasibleStatus at h
  split at h
  · rename_i l c rest hst
    have hcl : holds c := hpc (l, c) (by rw [hst]; exact List.mem_cons_self ..)
    by_cases hf : LExpr.isFalse _ c = true
    · exact hfalse c hf hcl
    · simp [hf] at h
  · cases h

/-- A step's outcome that continues ends its path only as infeasible. -/
theorem infeasibleStatus_infeasible {before : List (String × Expression.Expr)} {st : PathState}
    {s : NodeStatus} (h : infeasibleStatus before st = some s) : ∃ l, s = .infeasible l := by
  unfold infeasibleStatus at h
  split at h
  · rename_i l c _ _
    refine ⟨l, ?_⟩
    split at h <;> simp_all
  · cases h

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
