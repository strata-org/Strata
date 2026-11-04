/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.SSA.SSACoreProgram
public import Strata.Transform.SSA.SSAOver
public import Strata.Languages.Core.Logic.LangDef
import Strata.Util.ExceptProps
import Strata.Languages.Core.Logic.LangDefProps
import Strata.Util.OrderedSetProps
import Strata.Transform.DeadDefElimProps

/-! # Properties of the SSA phase on Core procedures and programs

The facts that relate the SSA phase of a program to the procedures of its input, used to lift
the per-procedure results of the phase to whole programs: a successful run of the SSA phase of
a program has the obligation procedure of every procedure of its input (`ssaProgram_mem`); and
the SSA phase keeps the obligation unit of a lemma (`ssaProc_lemmaUnit`).

The SSA phase keeps the initial-environment gate `BlockInitEnvWF` of a statement list in tree
form (`ssaEntry_blockInitEnvWF`): its output is passive and in tree form, defines only fresh
names, declares only inhabited types and uses only operators of the input (`ssaList_outFacts`).

Key theorems: `ssaEntry_blockInitEnvWF`. -/

namespace Core
namespace WP

open Imperative Imperative.BigStep Imperative.WP Core.Logic Strata.Logic Core.DeadDefElim

public section

/-- A successful run of `ssaProgram`: every procedure of the input has its obligation procedure
    in the output. -/
private theorem ssaProgram_mem {reserved : List Expression.Ident} {mid out : Program}
    (h : ssaProgram reserved mid = .ok out) :
    ∀ q md, Decl.proc q md ∈ mid.decls → ∃ d,
      ssaProc (IdSet.ofList (avoidOf [] (reserved ++ declNames mid))) q = .ok d ∧
        d ∈ out.decls := fun _ _ hq =>
  ((Except.bind_is_ok _ _ _).1 h).elim fun _ ⟨hm, rfl⟩ =>
    (mapM_except_mem_left _ _ _ hm _ hq).imp fun _ h => h.symm

/-- Substituting no variable leaves a Core expression unchanged. -/
private theorem substFn_none (e : Expression.Expr) : WPOps.substFn e (fun _ => none) = e :=
  (WPLang.substFn_eq e _ [] fun _ _ => rfl).trans (WPLang.substFvars_nil e)

/-- The SSA phase keeps the obligation unit of a lemma. -/
private theorem ssaProc_lemmaUnit (G : IdSet Expression) (name : String)
    (ob : Imperative.ProofObligation Expression) {P : Procedure}
    {md : Imperative.MetaData Expression} (h : lemmaUnit name ob = Decl.proc P md) :
    ssaProc G P = .ok (lemmaUnit name ob) := by
  cases h
  unfold ProofObligation.toCheckCmd
  split <;> simp [ssaProc, ssaLoopFree, ssaEntry, ssaBody, ssaList, pushObl, oblVar, renM',
    ssaEntryRen, Procedure.entryParams, Procedure.oldAliases, Strata.Util.OrderedSet.eraseDups_nil,
    substFn_none, lemmaUnit, ProofObligation.toCheckCmd, getInoutParams,
    Procedure.Header.getInoutParams, HAppend.hAppend, List.append, Except.pure_is_ok, *]

/-! ## The initial-environment gate -/

/-- Substituting expressions without operators for free variables adds no operator. -/
private theorem substFn_ops {look : Expression.Ident → Option Expression.Expr}
    (hl : ∀ x v, look x = some v → HasOps.getOps v = []) (e : Expression.Expr) :
    ∀ o ∈ HasOps.getOps (WPOps.substFn e look), o ∈ HasOps.getOps e :=
  Lambda.LExpr.getOps_substFvarsBy hl e

/-- A variable reference has no operator. -/
private theorem var_ops (y : Expression.Ident) (ty : Option Expression.Ty) :
    HasOps.getOps (HasFvar.mkVar y ty) = [] := by
  cases ty <;> rfl

/-- Folding adds no operator. -/
private theorem foldE_ops (ρ : Std.HashMap Expression.Ident (SVal Expression))
    (e : Expression.Expr) : ∀ o ∈ HasOps.getOps (foldE ρ e), o ∈ HasOps.getOps e := by
  have hite (c t f : Expression.Expr) : HasOps.getOps (WPOps.ite c t f) =
      HasOps.getOps c ++ HasOps.getOps t ++ HasOps.getOps f := rfl
  fun_induction foldE ρ e <;> intro o ho <;> (try obtain rfl := WPLang.iteView?_eq ‹_›)
  case case5 e _ =>
    refine substFn_ops (look := fun x => ρ[x]?.map SVal.expr) (fun x v h => ?_) e o ho
    obtain ⟨w, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rcases w with ⟨y, ty⟩ | ⟨_ | _, _⟩
    · exact var_ops y ty
    all_goals rfl
  all_goals grind

/-- The operators of the value an assignment's output defines are among the operators of the
    assigned expression `e`: the value is a Boolean literal or the folded `e`. -/
private theorem assignOps {ρ : Std.HashMap Expression.Ident (SVal Expression)}
    {e e' : Expression.Expr} (he : e' = tt ∨ e' = ff ∨ e' = foldE ρ e) :
    ∀ o ∈ HasOps.getOps e', o ∈ HasOps.getOps e := by
  rcases he with rfl | rfl | rfl
  · exact nofun
  · exact nofun
  · exact foldE_ops ρ e

/-- The facts the gate needs of an SSA output `out` of the statement list `ss` from the counter
    `n0`: `out` is in tree form and passive, every name it defines is a fresh name with the base of
    a name `ss` defines or modifies and a counter at least `n0`, every type it declares satisfies
    `Inh`, and its operators are operators of `ss`. -/
private def OutFacts (Inh : Expression.Ty → Prop) (ss : Statements) (n0 : Nat)
    (out : Statements) : Prop :=
  Block.treeForm out = true ∧ Block.passiveForm out = true ∧
    (∀ n ∈ Block.definedVars out false, ∃ x, (x ∈ Block.definedVars ss false ∨
      x ∈ Block.modifiedVars ss) ∧ ∃ j, n0 ≤ j ∧ n = freshName (baseOf x) j) ∧
    (∀ ty ∈ Block.initTypes out, Inh ty) ∧ ∀ o ∈ Block.getOps out, o ∈ Block.getOps ss

/-- `OutFacts` survives an input that defines or modifies more names and has more operators,
    and a smaller counter. -/
private theorem OutFacts.weaken {Inh : Expression.Ty → Prop} {ss ss' out : Statements}
    {n0 n1 : Nat} (h : OutFacts Inh ss n1 out)
    (hs : ∀ z, z ∈ Block.definedVars ss false ∨ z ∈ Block.modifiedVars ss →
      z ∈ Block.definedVars ss' false ∨ z ∈ Block.modifiedVars ss')
    (ho : ∀ o ∈ Block.getOps ss, o ∈ Block.getOps ss') (hn : n0 ≤ n1) :
    OutFacts Inh ss' n0 out := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, fun n hn' => ?_, h4, fun o h => ho o (h5 o h)⟩
  obtain ⟨z, hz, j, hj, rfl⟩ := h3 n hn'
  exact ⟨z, hs z hz, j, Nat.le_trans hn hj, rfl⟩

/-- `OutFacts` survives a statement in front of the input and a smaller counter. -/
private theorem OutFacts.mono {Inh : Expression.Ty → Prop} {st : Statement} {rest out : Statements}
    {n0 n1 : Nat} (h : OutFacts Inh rest n1 out) (hn : n0 ≤ n1) :
    OutFacts Inh (st :: rest) n0 out :=
  h.weaken (fun z hz => by
    simp only [Block.definedVars, Block.modifiedVars, List.mem_append]
    exact hz.imp .inr .inr) (fun o h => by simp [Block.getOps, h]) hn

/-- `OutFacts` survives an `init` in front of the output of a fresh name with the base of a name
    the input defines or modifies, a counter at least `n0`, a type satisfying `Inh` and a value
    with operators of the input. -/
private theorem OutFacts.init {Inh : Expression.Ty → Prop} {ss out : Statements} {n0 j : Nat}
    {x : Expression.Ident} {ty : Expression.Ty} {e : ExprOrNondet Expression}
    (h : OutFacts Inh ss n0 out) (hx : x ∈ Block.definedVars ss false ∨ x ∈ Block.modifiedVars ss)
    (hj : n0 ≤ j) (hty : Inh ty) (he : ∀ o ∈ e.getOps, o ∈ Block.getOps ss) :
    OutFacts Inh ss n0 (mkInit (freshName (baseOf x) j) ty e :: out) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨by simpa [Block.treeForm, mkInit] using h1, by simpa [Block.passiveForm, mkInit] using h2,
    fun n hn => ?_, fun t ht => ?_, fun o ho => ?_⟩
  · simp only [mkInit, Block.definedVars, Stmt.definedVars, HasVarsImp.definedVars,
      CmdExt.definedVars, Cmd.definedVars, List.mem_append, List.mem_singleton] at hn
    exact hn.elim (fun hn => ⟨x, hx, j, hj, hn⟩) (h3 n)
  · simp only [mkInit, Block.initTypes, Stmt.initTypes, HasInitTypesImp.initTypes,
      CmdExt.initTypes, Cmd.initTypes, List.mem_append, List.mem_singleton] at ht
    exact ht.elim (· ▸ hty) (h4 t)
  · rcases e with e | _ <;>
      simp only [mkInit, Block.getOps, Stmt.getOps, HasOpsImp.getOps, CmdExt.getOps, Cmd.getOps,
        ExprOrNondet.getOps, List.mem_append, List.nil_append] at ho he
    · exact ho.elim (he o) (h5 o)
    · exact h5 o ho

/-- `OutFacts` survives an `assume`, an `assert` or a `cover` in front of the output whose
    condition has operators of the input. -/
private theorem OutFacts.check {Inh : Expression.Ty → Prop} {ss out : Statements} {n0 : Nat}
    {mk : String → Expression.Expr → MetaData Expression → Cmd Expression}
    (hmk : mk = .assume ∨ mk = .assert ∨ mk = .cover) {l : String} {e : Expression.Expr}
    {md : MetaData Expression} (h : OutFacts Inh ss n0 out)
    (he : ∀ o ∈ HasOps.getOps e, o ∈ Block.getOps ss) :
    OutFacts Inh ss n0 (.cmd (.cmd (mk l e md)) :: out) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rcases hmk with rfl | rfl | rfl <;>
    exact ⟨by simpa [Block.treeForm] using h1, by simpa [Block.passiveForm] using h2,
      by simpa [Block.definedVars, HasVarsImp.definedVars, CmdExt.definedVars,
        Cmd.definedVars] using h3,
      by simpa [Block.initTypes, Stmt.initTypes, HasInitTypesImp.initTypes, CmdExt.initTypes,
        Cmd.initTypes] using h4,
      fun o ho => by
        simp only [Block.getOps, Stmt.getOps, HasOpsImp.getOps, CmdExt.getOps, Cmd.getOps,
          List.mem_append] at ho
        exact ho.elim (he o) (h5 o)⟩

/-- The types of the current values satisfy `Inh` on the names of `V` after binding `x` to a
    value whose type does, when they do before on the names of `V` other than `x`. -/
private theorem tyInh_insert {Inh : Expression.Ty → Prop} {ρ : Std.HashMap Expression.Ident
    (SVal Expression)} {x : Expression.Ident} {v : SVal Expression} {V : List Expression.Ident}
    (hv : ∀ t, v.ty? = some t → Inh t)
    (hold : ∀ y ∈ V, y ≠ x → ∀ t, (ρ[y]?.getD (.name y none)).ty? = some t → Inh t) :
    ∀ y ∈ V, ∀ t, ((ρ.insert x v)[y]?.getD (.name y none)).ty? = some t → Inh t := by
  intro y hy t ht
  by_cases hyx : y = x
  · subst hyx
    simp only [Std.HashMap.getElem?_insert_self, Option.getD_some] at ht
    exact hv t ht
  · exact hold y hy hyx t (by simpa [Std.HashMap.getElem?_insert, Ne.symm hyx] using ht)

/-- The SSA traversal's output on a list in tree form satisfies `OutFacts` from the current
    counter when the Boolean type, the types the list declares and the types of the current
    values of its free variables satisfy `Inh`. -/
private theorem ssaList_outFacts (Inh : Expression.Ty → Prop) (hb : Inh HasBool.boolTy)
    (ss : Statements) : ∀ {s s' : SSt Expression} {out : Statements},
    ssaList ss s = .ok (out, s') → Block.treeForm ss = true →
    (∀ ty ∈ Block.initTypes ss, Inh ty) →
    (∀ x ∈ Block.freeVars ss, ∀ ty, (s.ρ[x]?.getD (.name x none)).ty? = some ty → Inh ty) →
    OutFacts Inh ss s.next out := by
  intro s s' out h
  refine ssaList_ind
    (fun _ _ _ _ => by simp [OutFacts, Block.treeForm, Block.passiveForm, Block.initTypes])
    ?initDet ?initNondet ?setDet ?setNondet ?assume ?check ?ite ?typeDecl h
  case initDet =>
    intro x ty e md rest s o v s1 out s' hA ih hT hI hR
    obtain ⟨hρ, hn, hv, ho⟩ := assignVal_facts hA
    have hI' : ∀ t ∈ ty :: Block.initTypes rest, Inh t := by
      simpa [Block.initTypes, Stmt.initTypes, HasInitTypesImp.initTypes, CmdExt.initTypes,
        Cmd.initTypes] using hI
    have hr := ih (by simpa [Block.treeForm] using hT) (fun t ht => hI' t (.tail _ ht))
      (tyInh_insert (fun t ht => by
          rcases hv with hv | hv <;> rw [hv] at ht <;> cases ht
          · exact hb
          · exact hI' _ (.head _))
        fun y hy hyx => hρ ▸ hR y (by simp [Block.freeVars, hy, hyx]))
    rcases ho with rfl | ⟨j, ty', e', hj, hty', he', rfl⟩
    · exact hr.mono hn
    · exact (hr.mono hn).init (by simp [Block.definedVars, HasVarsImp.definedVars,
        CmdExt.definedVars, Cmd.definedVars]) hj (hty'.elim (· ▸ hb) (· ▸ hI' _ (.head _)))
        (fun o h => by simp [Block.getOps, Stmt.getOps, HasOpsImp.getOps, CmdExt.getOps,
          Cmd.getOps, assignOps he' o h])
  case initNondet =>
    intro x ty md rest s x' s1 out s' hF ih hT hI hR
    obtain ⟨j, hj, rfl, -, rfl⟩ := sFresh_ok hF
    have hI' : ∀ t ∈ ty :: Block.initTypes rest, Inh t := by
      simpa [Block.initTypes, Stmt.initTypes, HasInitTypesImp.initTypes, CmdExt.initTypes,
        Cmd.initTypes] using hI
    have hr := ih (by simpa [Block.treeForm] using hT) (fun t ht => hI' t (.tail _ ht))
      (tyInh_insert (fun t ht => by cases ht; exact hI' _ (.head _))
        fun y hy hyx => hR y (by simp [Block.freeVars, hy, hyx]))
    exact (hr.mono (Nat.le_succ_of_le hj)).init (by simp [Block.definedVars,
      HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars]) hj (hI' _ (.head _)) nofun
  case setDet =>
    intro x e md rest s ty o v s1 out s' hC hA ih hT hI hR
    obtain ⟨hρ, hn, hv, ho⟩ := assignVal_facts hA
    have hty := hR x (by simp [Block.freeVars, Stmt.freeVars]) ty (curTy_ok hC).2
    have hr := ih (by simpa [Block.treeForm] using hT) (by simpa [Block.initTypes, Stmt.initTypes,
        HasInitTypesImp.initTypes, CmdExt.initTypes, Cmd.initTypes] using hI)
      (tyInh_insert (fun t ht => by
          rcases hv with hv | hv <;> rw [hv] at ht <;> cases ht
          · exact hb
          · exact hty)
        fun y hy _ => hρ ▸ hR y (by simp [Block.freeVars, Stmt.freeVars, hy]))
    rcases ho with rfl | ⟨j, ty', e', hj, hty', he', rfl⟩
    · exact hr.mono hn
    · exact (hr.mono hn).init (by simp [Block.modifiedVars, HasVarsImp.modifiedVars,
        CmdExt.modifiedVars, Cmd.modifiedVars]) hj (hty'.elim (· ▸ hb) (· ▸ hty))
        (fun o h => by simp [Block.getOps, Stmt.getOps, HasOpsImp.getOps, CmdExt.getOps,
          Cmd.getOps, assignOps he' o h])
  case setNondet =>
    intro x md rest s ty x' s1 out s' hC hF ih hT hI hR
    obtain ⟨j, hj, rfl, -, rfl⟩ := sFresh_ok hF
    have hty := hR x (by simp [Block.freeVars, Stmt.freeVars]) ty (curTy_ok hC).2
    have hr := ih (by simpa [Block.treeForm] using hT) (by simpa [Block.initTypes, Stmt.initTypes,
        HasInitTypesImp.initTypes, CmdExt.initTypes, Cmd.initTypes] using hI)
      (tyInh_insert (fun t ht => by cases ht; exact hty)
        fun y hy _ => hR y (by simp [Block.freeVars, Stmt.freeVars, hy]))
    exact (hr.mono (Nat.le_succ_of_le hj)).init (by simp [Block.modifiedVars,
      HasVarsImp.modifiedVars, CmdExt.modifiedVars, Cmd.modifiedVars]) hj hty nofun
  case assume =>
    intro l a md rest s out s' ih hT hI hR
    have hr : OutFacts Inh (.cmd (.cmd (.assume l a md)) :: rest) s.next out :=
      (ih (by simpa [Block.treeForm] using hT) (by simpa [Block.initTypes, Stmt.initTypes,
          HasInitTypesImp.initTypes, CmdExt.initTypes, Cmd.initTypes] using hI)
        fun y hy => hR y (by simp [Block.freeVars, Stmt.freeVars, hy])).mono (Nat.le_refl _)
    split
    · exact hr
    · exact hr.check (.inl rfl) fun o h => by
        simp [Block.getOps, Stmt.getOps, HasOpsImp.getOps, CmdExt.getOps, Cmd.getOps,
          foldE_ops _ a o h]
  case check =>
    intro mk l e md rest s out s' hmk _ ih hT hI hR
    have hr : OutFacts Inh (.cmd (.cmd (mk l e md)) :: rest) s.next out :=
      (ih (by rcases hmk with rfl | rfl <;> simpa [Block.treeForm] using hT)
        (by rcases hmk with rfl | rfl <;> simpa [Block.initTypes, Stmt.initTypes,
          HasInitTypesImp.initTypes, CmdExt.initTypes, Cmd.initTypes] using hI)
        fun y hy => hR y (by
          rcases hmk with rfl | rfl <;> simp [Block.freeVars, Stmt.freeVars, hy])).mono
          (Nat.le_refl _)
    exact hr.check (.inr hmk) fun o h => by
      rcases hmk with rfl | rfl <;> simp [Block.getOps, Stmt.getOps, HasOpsImp.getOps,
        CmdExt.getOps, Cmd.getOps, substFn_ops (fun x v h => by
          obtain ⟨⟨y, ty⟩, -, rfl⟩ := Option.map_eq_some_iff.1 h
          exact var_ops y ty) e o h]
  case ite =>
    intro tss ess md s t sT sU e out s' hT ihT hU hE ihE h1 h2 h3 hTF hI hR
    obtain ⟨⟨-, hn, -⟩, hρ⟩ := undoTo_frame (ssaList_frame _ hT) hU
    simp only [Block.treeForm, List.isEmpty_nil, Bool.true_and, Bool.and_eq_true] at hTF
    have hI' : ∀ t ∈ Block.initTypes tss ++ Block.initTypes ess, Inh t := by
      simpa [Block.initTypes, Stmt.initTypes] using hI
    have hR' : ∀ y ∈ Block.freeVars tss ++ Block.freeVars ess, ∀ t,
        (s.ρ[y]?.getD (.name y none)).ty? = some t → Inh t := fun y hy => hR y (by
      simpa [Block.freeVars, Stmt.freeVars] using hy)
    have hs (z : Expression.Ident) (h : z ∈ Block.definedVars tss false ∨
        z ∈ Block.modifiedVars tss ∨ z ∈ Block.definedVars ess false ∨
        z ∈ Block.modifiedVars ess) :
        z ∈ Block.definedVars [.ite .nondet tss ess md] false ∨
          z ∈ Block.modifiedVars [.ite .nondet tss ess md] := by
      simp only [Block.definedVars, Stmt.definedVars, Block.modifiedVars, Stmt.modifiedVars,
        Bool.false_eq_true, ↓reduceIte, List.append_nil, List.mem_append]
      grind
    have rT := (ihT hTF.1 (fun t ht => hI' t (List.mem_append_left _ ht))
      fun y hy => hR' y (List.mem_append_left _ hy)).weaken (fun z hz => hs z (by grind))
        (fun o h => by simp [Block.getOps, Stmt.getOps, ExprOrNondet.getOps, h]) (Nat.le_refl _)
    have rE := (ihE hTF.2 (fun t ht => hI' t (List.mem_append_right _ ht))
      fun y hy => hρ y ▸ hR' y (List.mem_append_right _ hy)).weaken (fun z hz => hs z (by grind))
        (fun o h => by simp [Block.getOps, Stmt.getOps, ExprOrNondet.getOps, h]) hn
    by_cases ht : t = []
    · exact h1 ht ▸ rE
    by_cases he : e = []
    · exact h2 ht he ▸ rT
    obtain ⟨t1, t2, t3, t4, t5⟩ := rT
    obtain ⟨e1, e2, e3, e4, e5⟩ := rE
    refine h3 ht he ▸ ⟨by simp [Block.treeForm, t1, e1], by simp [Block.passiveForm, t2, e2],
      fun n hn => ?_,
      fun t ht => ?_, fun o ho => ?_⟩
    · simp only [Block.definedVars, Stmt.definedVars, Bool.false_eq_true, ↓reduceIte,
        List.append_nil, List.mem_append] at hn
      exact hn.elim (t3 n) (e3 n)
    · simp only [Block.initTypes, Stmt.initTypes, List.append_nil, List.mem_append] at ht
      exact ht.elim (t4 _) (e4 _)
    · simp only [Block.getOps, Stmt.getOps, ExprOrNondet.getOps, List.nil_append,
        List.append_nil, List.mem_append] at ho
      exact ho.elim (t5 o) (e5 o)
  case typeDecl =>
    intro _ _ _ _ _ _ _ hT
    simp [Block.treeForm] at hT

/-- A reserved prefix without `@` that is not a prefix of the name `x` is not a prefix of a
    fresh name whose base is a prefix of `x`. -/
private theorem fresh_notReserved {p b : String} {x : Expression.Ident} (j : Nat)
    (hp : '@' ∉ p.toList) (hb : b.toList <+: x.name.toList)
    (hn : ¬ p.toList.isPrefixOf x.name.toList) :
    ¬ p.toList.isPrefixOf (freshName (P := Expression) b j).name.toList := by
  intro h
  refine hn (List.isPrefixOf_iff_prefix.2 (List.IsPrefix.trans ?_ hb))
  obtain ⟨t, ht⟩ := List.isPrefixOf_iff_prefix.1 h
  have he : (freshName (P := Expression) b j).name.toList =
      b.toList ++ '@' :: (toString j).toList := by
    simp [freshName, HasIdent.ident]
  rw [he, List.append_eq_append_iff] at ht
  rcases ht with ⟨a, hb', -⟩ | ⟨c, hpc, hc⟩
  · exact ⟨a, hb'.symm⟩
  · rcases c with _ | ⟨d, c⟩
    · simp [hpc]
    · cases (List.cons.inj hc).1
      simp [hpc] at hp

/-- **The SSA phase keeps the initial-environment gate.**  For a Core statement list `ss₀` in
    tree form whose free variables are parameters of `xs` or aliases of `al`, on which
    `ssaEntry G tys xs al` succeeds with the entry renaming `ρ0` and the output `so.out`, every
    reserved prefix of `params` being free of `@` and every alias of `al` denoting a parameter of
    `xs`: when the environment `ρ` of `ss₀` satisfies `BlockInitEnvWF params ss₀`, and `ρ'` has the
    factory of `ρ`, holds under the entry name of each free variable of `ss₀` its (defined) value
    in `ρ`, typed by `tys`, and binds nothing else, while every parameter is defined in `ρ`, then
    `ρ'` satisfies `BlockInitEnvWF params so.out`, provided the type annotations of `so.out` agree
    with a typing of `ρ'` (`hty`). -/
theorem ssaEntry_blockInitEnvWF {params : InitEnvWFParams}
    (hp : ∀ p ∈ params.prefixIdents, '@' ∉ p.toList) {G : IdSet Expression}
    {tys : Tys Expression} {xs : List Expression.Ident}
    {al : List (Expression.Ident × Expression.Ident)} (hal : ∀ q ∈ al, q.2 ∈ xs)
    {ss₀ : Statements} {ρ0 : Ren Expression} {so : SOut Expression}
    (h : ssaEntry G tys xs al ss₀ = .ok (ρ0, so)) (hTF : Block.treeForm ss₀ = true)
    (hfv : ∀ x ∈ Block.freeVars ss₀, x ∈ xs ∨ x ∈ al.map (·.1)) {ρ ρ' : Env Expression}
    (hF : ρ'.factory = ρ.factory)
    (hval : ∀ x ∈ Block.freeVars ss₀, ρ.store x =
      ρ'.store ((ssaEntryRen (inputAvoid G tys ss₀) xs al 0).1.get x) ∧ (ρ.store x).isSome)
    (hparams : ∀ x ∈ xs, (ρ.store x).isSome)
    (htyOK : TyOK ρ.factory tys (Block.freeVars ss₀) (Block.freeVars ss₀) ρ.store)
    (hdomS : ∀ y, (ρ'.store y).isSome →
      ∃ x ∈ Block.freeVars ss₀, y = (ssaEntryRen (inputAvoid G tys ss₀) xs al 0).1.get x)
    (hwf : BlockInitEnvWF params ss₀ ρ)
    (hty : ∃ Γ, StoreHasTyping ρ'.factory ρ'.store Γ ∧ Block.fvarTypesWellAnnotated Γ so.out) :
    BlockInitEnvWF params so.out ρ' := by
  have hrd := ssaEntry_wellScopedFV h hal hfv
  obtain ⟨rfl, hb⟩ := ssaEntry_ok h
  obtain ⟨s1, h1, -⟩ := ssaBody_ok hb
  have hspec := ssaEntryRen_spec (inputAvoid G tys ss₀) xs al 0 hal
  have hdom (y : Expression.Ident) : (ρ'.store y).isSome = true ↔
      y ∈ (Block.freeVars ss₀).map ((ssaEntryRen (inputAvoid G tys ss₀) xs al 0).1).get := by
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · obtain ⟨x, hx, rfl⟩ := hdomS y hy
      exact List.mem_map_of_mem hx
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact (hval x hx).1 ▸ (hval x hx).2
  have hentry {y : Expression.Ident} (hy : (ρ'.store y).isSome = true) :
      ∃ q ∈ (ssaEntryRen (inputAvoid G tys ss₀) xs al 0).1, y = q.2 := by
    obtain ⟨x, hx, rfl⟩ := hdomS y hy
    exact (Ren.get_mem (hspec.2.2 x (hfv x hx))).imp fun _ ⟨hq, he⟩ => ⟨hq, he⟩
  obtain ⟨o1, o2, o3, o4, o5⟩ := ssaList_outFacts (fun ty => ∃ v, HasVal.valueOfTy ρ'.factory v ty)
    ⟨_, (HasBool.boolIsValOfTy _).1⟩ ss₀ h1 hTF (hF ▸ hwf.initTypesInhabited) fun x hx ty hty => by
      replace hty := (entryMap_ty tys _ x (hspec.2.2 x (hfv x hx))).symm.trans hty
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hval x hx).2
      exact ⟨w, hF ▸ htyOK x hx hx ty hty w hw⟩
  obtain ⟨d1, d2, d3, d4⟩ :=
    Block.defUseWellFormed_of_readsDefined (df := params.declaredFuncs) so.out hrd o1 o2
    hdom fun o ho => Block.getOps_declared_of_defUseWellFormed ss₀ hTF hwf.defUseOk o (o5 o ho)
  refine { toWellFormedSemanticEval := hF ▸ hwf.toWellFormedSemanticEval
           storeWellDefined := ?_
           readWritesDefined := ?_
           defsUndefined := ?_
           definedVarsNotReserved := ?_
           reservedFresh := ?_
           defUseOk := d1
           factoryDeclared := hwf.factoryDeclared
           initTypesInhabited := o4
           fvarTypesOk := hty }
  · intro y v hy
    obtain ⟨x, hx, rfl⟩ := hdomS y (by simp [hy])
    exact hF ▸ hwf.storeWellDefined x v ((hval x hx).1.trans hy)
  · intro n hn hnd
    simp only [Block.touchedVars, Block.modifiedOrDefinedVars, d2, List.nil_append,
      List.mem_append] at hn
    rcases hn with hn | hn
    · exact absurd (d3 n hn) hnd
    · exact (hdom n).2 ((d4 n hn).resolve_right hnd)
  · intro n hn
    obtain ⟨x, -, j, hj, rfl⟩ := o3 n hn
    refine Option.isNone_iff_eq_none.2 (Option.eq_none_iff_forall_ne_some.2 fun v hv => ?_)
    obtain ⟨q, hq, he⟩ := hentry (y := freshName (baseOf x) j) (by simp [hv])
    obtain ⟨⟨b, j', -, hj', hqb, -⟩, -⟩ := hspec.2.1 q hq
    exact absurd (freshName_counter_inj (he.trans hqb)) (Nat.ne_of_gt (Nat.lt_of_lt_of_le hj' hj))
  · intro n hn name hname p hpm
    obtain rfl : name = n.name := by rw [hname]; rfl
    obtain ⟨x, hx, j, -, rfl⟩ := o3 n hn
    refine fresh_notReserved j (hp p hpm) (baseOf_prefix x) ?_
    by_cases hxd : x ∈ Block.definedVars ss₀ false
    · exact hwf.definedVarsNotReservedCore x hxd p hpm
    · refine hwf.reservedFreshCore x (hwf.readWritesDefined x ?_ hxd) p hpm
      simp [Block.touchedVars, Block.modifiedOrDefinedVars, hx.resolve_left hxd]
  · intro n hn name hname p hpm
    obtain rfl : name = n.name := by rw [hname]; rfl
    obtain ⟨q, hq, rfl⟩ := hentry hn
    obtain ⟨w, hw, k, hk⟩ := ssaEntryRen_base _ xs al 0 hal q hq
    exact hk ▸ fresh_notReserved k (hp p hpm) (List.prefix_refl _)
      (hwf.reservedFreshCore w (hparams w hw) p hpm)

end -- public section
end WP
end Core
