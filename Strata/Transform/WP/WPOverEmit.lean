/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WP
public import Strata.Util.RopeProps
public import Strata.Transform.Passive.SimulationProps
import Strata.DL.Imperative.BigStep.SemProps
import Strata.Transform.Passive.Shadow
import Strata.Util.ExceptProps

/-! # Emission keeps hits

A hit of the resolved items of the WP phase's output (a run stopping inside a side branch or
an arm of a real branch, failing a target on a feasible path) is a failure of the emitted
guarded program at an event of the same kind: resolution distributes over concatenation, merging
adjacent obligation runs keeps a failing hit, and nesting turns a hit into a reach.

Key theorems: `fails_of_emitK`, `fails_of_emit`, `hit_mergeOblsK`, `hit_mergeObls`, `hit_nest`,
`resolveItems_append`, `Rope.toList_ofList`.

Key definitions: `OblItemsOK`. -/

namespace Imperative
namespace WP

open Strata.Util

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iB : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iBo : HasBool P] [iFv : HasFvar P] [iSu : HasSubstFvar P] [iId : HasIdent P]
  [iLI : LawfulHasIdent P] [iHa : Hashable P.Ident] [iFs : HasFvars P] [iW : WPLang P]
  [iLV : LawfulHasVal P] [iOp : HasOps P] [iLF : LawfulHasFvar P] [iLFs : LawfulHasFvars P]
omit iLB iId iLI iLV iOp iLF iLFs
variable {F : P.Factory} {σ : SemanticStore P} {tr : List (Event P)}
  {T tys : Std.HashMap P.Ident P.Ty} {Y tyOf : Std.HashMap P.Ident P.Ident}

/-! ## Ropes -/

/-- The rope of a list has the elements of the list. -/
theorem Rope.toList_ofList {α : Type} (l : List α) : (Rope.ofList l).toList = l := by
  induction l <;> simp_all [Rope.ofList, Rope.toList_app, Rope.toList_one, Rope.toList_nil]

/-! ## Resolution -/

mutual
/-- The side branches of an item, and of the items of the arms of a real branch, consist of
    obligations (`assert` or `cover`). -/
@[expose] def OblItemOK : Item P → Prop
  | .plain _ => True
  | .obls _ cs => ∀ c ∈ cs, Stmt.isCheck c = true
  | .branch t e => OblItemsOK t ∧ OblItemsOK e
/-- The side branches of the items of a list, at every depth, consist of obligations. -/
@[expose] def OblItemsOK : List (Item P) → Prop
  | [] => True
  | it :: rest => OblItemOK it ∧ OblItemsOK rest
end

/-- Resolution of a concatenation succeeds exactly when the resolutions of both parts succeed,
    and then gives their concatenation. -/
theorem resolveItems_append (tys : Std.HashMap P.Ident P.Ty) (tyOf : Std.HashMap P.Ident P.Ident)
    (a b : List (WItem P)) {r : List (Item P)} :
    resolveItems tys tyOf (a ++ b) = .ok r ↔
      ∃ ra rb, resolveItems tys tyOf a = .ok ra ∧ resolveItems tys tyOf b = .ok rb ∧
        r = ra ++ rb := by
  induction a generalizing r <;> simp only [List.cons_append, resolveItems,
    Except.bind_is_ok, Except.pure_is_ok, *] <;> grind

/-- Resolution of a nonempty list resolves its head and its tail. -/
theorem resolveItems_cons_ok {a : WItem P} {l : List (WItem P)} {items : List (Item P)}
    (h : resolveItems T Y (a :: l) = .ok items) :
    ∃ ia il, resolveItem T Y a = .ok ia ∧ resolveItems T Y l = .ok il ∧ items = ia :: il := by
  grind [resolveItems, Except.bind_is_ok, Except.pure_is_ok]

/-- A resolved `set` item is the `set` of the resolved value. -/
theorem resolveItem_set {x : P.Ident} {e : WExpr P} {i : Item P}
    (h : resolveItem T Y (.set x (some e)) = .ok i) :
    ∃ e', resolveE T Y e = .ok e' ∧ i = .plain (.cmd (.cmd (.set x (.det e') .empty))) := by
  grind [resolveItem, resolveOE, Except.bind_is_ok, Except.pure_is_ok]

/-- A resolved deterministic `init` item of known type is the `init` of the resolved value. -/
theorem resolveItem_init_det {x : P.Ident} {ty : P.Ty} {e : WExpr P} {i : Item P}
    (h : resolveItem T Y (.init x (.known ty) (some e)) = .ok i) :
    ∃ e', resolveE T Y e = .ok e' ∧ i = .plain (mkInit x ty (.det e')) := by
  grind [resolveItem, resolveOE, Except.bind_is_ok, Except.pure_is_ok]

/-- A resolved `assume` item is the `assume` of the resolved condition. -/
theorem resolveItem_assume {l : String} {e : WExpr P} {md : MetaData P} {i : Item P}
    (h : resolveItem T Y (.assume l e md) = .ok i) :
    ∃ e', resolveE T Y e = .ok e' ∧ i = .plain (.cmd (.cmd (.assume l e' md))) := by
  grind [resolveItem, Except.bind_is_ok, Except.pure_is_ok]

omit iB iBo iFv iSu iHa iFs iW in
/-- Merging obligation runs keeps every side branch made of obligations. -/
theorem oblItemsOK_mergeObls : ∀ {l : List (Item P)}, OblItemsOK l → OblItemsOK (mergeObls l) :=
  fun h => by fun_induction mergeObls <;> grind [OblItemsOK, OblItemOK]

/-! ## Runs and hits of flat items -/

section
omit iB iHa

omit iDE iSu iFs iW in
/-- Main-path runs of `a` and `b` compose. -/
theorem MainRun.append :
    ∀ {a b : List (Item P)} {σ σ1 σ2 : SemanticStore P} {t1 t2 : List (Event P)},
      MainRun F a σ t1 σ1 → MainRun F b σ1 t2 σ2 → MainRun F (a ++ b) σ (t1 ++ t2) σ2 :=
  fun h1 h2 => by induction h1 <;> grind [MainRun]

omit iW in
/-- The `set` of a variable holding a Boolean to a Boolean value runs without events, updating
    the store. -/
theorem set_run (hF : WellFormedSemanticEvalBase F) {σ : SemanticStore P} {v : P.Ident}
    {e' : P.Expr} {w : P.Val}
    (hev : P.eval F σ e' = some w)
    (h0 : σ v = some (HasBool.ttVal F) ∨ σ v = some (HasBool.ffVal F))
    (hb : w = HasBool.ttVal F ∨ w = HasBool.ffVal F) :
    MainRun F [.plain (.cmd (.cmd (.set v (.det e') .empty)))] σ [] (σ.update v w) := by
  rcases h0 with h0 | h0 <;>
    exact .plain (evs1 := []) (evs2 := []) (.eval_set hev (.update h0 (update_facts σ v w).1
      (update_facts σ v w).2) ⟨_, _, h0, bool_valueOfTy (by simp), bool_valueOfTy hb⟩ hF.var) .nil

/-- A hit in the items `a` is a hit in `a ++ b`. -/
theorem HitIn.append_left : ∀ {a b : List (Item P)} {σ : SemanticStore P} {tr : List (Event P)},
    HitIn F a σ tr → HitIn F (a ++ b) σ tr := fun h => by induction h <;> grind [HitIn]

/-- A main-path run of `a` followed by a hit in `b` is a hit in `a ++ b`. -/
theorem HitIn.append_right :
    ∀ {a b : List (Item P)} {σ σ1 : SemanticStore P} {t1 t2 : List (Event P)},
      MainRun F a σ t1 σ1 → HitIn F b σ1 t2 → HitIn F (a ++ b) σ (t1 ++ t2) :=
  fun h1 h2 => by induction h1 <;> grind [HitIn]

/-! ## Merging obligation runs -/

omit iDE iSu iFs iW in
/-- A list of obligations runs from any store to itself, with no assumption event. -/
private theorem brun_obls : ∀ {cs : PStmts P}, (∀ c ∈ cs, Stmt.isCheck c = true) →
    ∀ σ, ∃ evs, BRun F cs σ evs (.normal σ) ∧ Trace.AssumptionsHold P evalInterp () evs
  | [], _, σ => ⟨[], .nil, nofun⟩
  | c :: cs, h, σ => by
    obtain ⟨evs, hr, hf⟩ := brun_obls (fun c hc => h c (.tail _ hc)) σ
    rcases c with ((_ | _ | _ | _ | _) | _) | _ <;> cases h _ (.head _) <;>
      exact ⟨_, .cons_normal (.cmd (by constructor)) hr,
        Trace.AssumptionsHold.append (fun _ => by simp) hf⟩

/-- A hit failing the target after the events `pre` at an event of kind `k` is matched by a hit,
    failing it at an event of kind `k`, in the items with adjacent obligation runs merged, when
    every side branch consists of obligations. -/
theorem hit_mergeOblsK {F : P.Factory} {t : AssertId P} {e : P.Expr} {k : Bool} :
    ∀ {items : List (Item P)} {σ : SemanticStore P} {tr : List (Event P)},
      OblItemsOK items → HitIn F items σ tr → ∀ pre, ClaimK k t e (pre ++ tr) →
        ∃ tr', HitIn F (mergeObls items) σ tr' ∧ ClaimK k t e (pre ++ tr')
  | _, _, tr, _, .here hb, pre, hc => by
    simp only [mergeObls]
    split <;> (try split) <;>
      exact ⟨tr, .here (by first | exact hb | simpa using breach_append_left hb), hc⟩
  | _ :: rest, _, _, ⟨hcs, hok⟩, .side hh, pre, hc => by
    have hpre {r σ tr} (h : BReach F (reachPre r) σ tr) : ∃ a, tr = [.assume a] := by
      rcases r with _ | (_ | _ | _ | _) <;> simp only [reachPre] at h <;>
        rcases h with ⟨⟨⟨⟩⟩⟩ | ⟨_, ⟨⟩⟩ <;> exact ⟨_, rfl⟩
    have hst {r σ1 σ tr} (h : BRun F (reachPre r) σ tr (.normal σ1)) : σ1 = σ := by
      rcases r with _ | (_ | _ | _ | _) <;> simp only [reachPre] at h <;>
        rcases h with _ | ⟨⟨⟨⟩⟩, ⟨⟩⟩ <;> rfl
    have hne {cs σ tr} (hc : ∀ c ∈ cs, Stmt.isCheck c) (h : BReach F cs σ tr) : tr ≠ [] := by
      rcases cs with _ | ⟨c, _⟩
      · cases h
      rcases c with ((_ | _ | _ | _ | _) | _) | _ <;> cases hc _ (.head _) <;>
        rcases h with ⟨⟨⟨⟩⟩⟩ | ⟨⟨⟨⟩⟩, -⟩ <;> exact List.cons_ne_nil _ _
    obtain ⟨tr', hh', hc'⟩ := hit_mergeOblsK hok hh pre hc
    have hm := oblItemsOK_mergeObls hok
    simp only [mergeObls]
    generalize mergeObls rest = m at hh' hm ⊢
    split <;> (try split) <;> first
      | exact ⟨tr', .side hh', hc'⟩
      | subst_vars
        rcases hh' with hb | _ | hh'
        · rcases breach_append_inv hb with hb | ⟨t1, σ1, t2, h1, h2, rfl⟩
          · grind [ClaimK, FailsAt, List.append_inj']
          · cases hst h1
            obtain ⟨evs, hr, hf⟩ := brun_obls hcs _
            obtain ⟨hp, h3⟩ := claimK_split (hne hm.1 h2) (List.append_assoc .. ▸ hc')
            exact ⟨_, .here (breach_append_run h1 (breach_append_run hr h2)),
              by simpa using claimK_prepend (Trace.AssumptionsHold.append hp hf) h3⟩
        · exact ⟨tr', .side hh', hc'⟩
  | _ :: _, _, _, hok, .plain (evs1 := evs1) hc0 hh, pre, hc => by
    obtain ⟨tr', hh', hc'⟩ := hit_mergeOblsK hok.2 hh (pre ++ evs1) (List.append_assoc .. ▸ hc)
    simp only [mergeObls]
    exact ⟨evs1 ++ tr', .plain hc0 hh', by simpa [List.append_assoc] using hc'⟩
  | _ :: _, _, _, hok, .branchT hh, pre, hc | _ :: _, _, _, hok, .branchE hh, pre, hc => by
    simp only [mergeObls]
    first
    | exact (hit_mergeOblsK hok.1.1 hh pre hc).imp fun _ h => ⟨.branchT h.1, h.2⟩
    | exact (hit_mergeOblsK hok.1.2 hh pre hc).imp fun _ h => ⟨.branchE h.1, h.2⟩

/-- A hit failing the target after the events `pre` at an occurrence of condition `e` is matched
    by a hit, failing it at an occurrence of condition `e`, in the items with adjacent obligation
    runs merged, when every side branch consists of obligations. -/
theorem hit_mergeObls {F : P.Factory} {t : AssertId P} {e : P.Expr} {items : List (Item P)}
    {σ : SemanticStore P} {tr : List (Event P)} (hok : OblItemsOK items) (hh : HitIn F items σ tr)
    (pre : List (Event P)) (hc : Claim t e (pre ++ tr)) :
    ∃ tr', HitIn F (mergeObls items) σ tr' ∧ Claim t e (pre ++ tr') :=
  hc.kind.elim fun _ hk => (hit_mergeOblsK hok hh pre hk).imp fun _ h => ⟨h.1, h.2.claim⟩

/-! ## Nesting -/

/-- A hit in the flat items is a reach of their nesting into a statement list. -/
theorem hit_nest {items : List (Item P)} {σ : SemanticStore P} {tr : List (Event P)}
    (h : HitIn F items σ tr) : BReach F (nest items) σ tr := by
  have hs : ∀ {items : List (Item P)} {σ tr}, HitIn F items σ tr → items.any Item.isBranching :=
    fun h => by induction h <;> simp_all [Item.isBranching]
  induction h <;> simp only [nest, nestCons] <;> (try split) <;>
    grind [BReach, BReachS, → BRunS.cmd]

end

/-! ## Emission -/

/-- **Emission keeps hits.**  If the guarded program `lay` is emitted from the rope `s` and the
    resolved items of `s` have a hit from the store `σ` whose trace fails the target `t` on a
    feasible path at an event of kind `k` with the condition `e`, then `lay` has a reach from `σ`
    whose trace fails `t` on a feasible path at an event of kind `k` with the condition `e`. -/
theorem fails_of_emitK {s : Rope (WItem P)} {lay : PStmts P} (h : emit tys tyOf s = .ok lay)
    {items : List (Item P)} (hr : resolveItems tys tyOf s.toList = .ok items) {σ : SemanticStore P}
    {tr : List (Event P)} {t : AssertId P} {e : P.Expr} {k : Bool} (hh : HitIn F items σ tr)
    (hc : ClaimK k t e tr) : ∃ tr', BReach F lay σ tr' ∧ ClaimK k t e tr' := by
  have hok : ∀ {l : List (WItem P)} {items}, resolveItems tys tyOf l = .ok items →
      OblItemsOK items := by
    intro l
    induction l using resolveItems.induct (tys := tys) (tyOf := tyOf)
      (motive_2 := fun it => ∀ i, resolveItem tys tyOf it = .ok i → OblItemOK i) <;>
      grind [resolveItems, resolveItem, OblItemsOK, OblItemOK, Except.bind_is_ok,
        Except.pure_is_ok, → mapM_except_mem_right, Stmt.isCheck]
  simp only [emit, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
  obtain ⟨tr', hh', hc'⟩ := hit_mergeOblsK (hok hr) hh [] hc
  exact ⟨tr', h ▸ hit_nest hh', hc'⟩

/-- **Emission keeps hits.**  If the guarded program `lay` is emitted from the rope `s` and the
    resolved items of `s` have a hit from the store `σ` whose trace fails the target `t` on a
    feasible path at an occurrence of condition `e`, then `lay` fails `t` from `σ` at an
    occurrence of condition `e`. -/
theorem fails_of_emit {s : Rope (WItem P)} {lay : PStmts P} (h : emit tys tyOf s = .ok lay)
    {items : List (Item P)} (hr : resolveItems tys tyOf s.toList = .ok items) {σ : SemanticStore P}
    {tr : List (Event P)} {t : AssertId P} {e : P.Expr} (hh : HitIn F items σ tr)
    (hc : Claim t e tr) : Fails F lay σ t e := by
  obtain ⟨_, hk⟩ := hc.kind
  obtain ⟨_, hb, hc'⟩ := fails_of_emitK h hr hh hk
  obtain ⟨evs, _, rfl, hf, hfe⟩ := hc'.claim
  exact ⟨evs, _, hb, hf, hfe⟩

end -- public section

end WP
end Imperative
