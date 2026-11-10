/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPOverEffects
public import Strata.Util.RopeProps
import Strata.Transform.WP.WPOverEmit
import Strata.Transform.WP.WPOverEval
import Strata.Transform.WP.WPOverFacts
import Strata.DL.Imperative.PureExprProps
import Strata.Util.ExceptProps

/-! # The names the guarded program reads

The emission (`emit`) keeps a straight-line item only when a branching item (a run of
obligations or a real branch) follows it in its list, and ends a list at a real branch.  The
names the emitted guarded program reads before declaring them are therefore described on the
items of the WP walk by `wFV b`, `b` telling whether a branching item follows them; `wreads`
gives the names an item expression reads.  Every free variable of the emitted program is in
`wFV false` of the items (`emit_fv`).

Key definitions: `wreads`, `wFV`.

Key theorems: `emit_fv`. -/

namespace Imperative
namespace WP

open Strata.Util

open BigStep

public section

variable {P : PureExpr} [iDec : DecidableEq P.Ident] [iBEq : BEq P.Ident]
  [iLBEq : LawfulBEq P.Ident] [iBool : HasBool P] [iFvar : HasFvar P] [iSubst : HasSubstFvar P]
  [iId : HasIdent P] [iLId : LawfulHasIdent P] [iHash : Hashable P.Ident] [iFvars : HasFvars P]
  [iW : WPLang P] [iVal : LawfulHasVal P] [iOp : HasOps P] [iLFvar : LawfulHasFvar P]
  [iLFvars : LawfulHasFvars P]
omit iDec iBool iFvar iSubst iId iLId iHash iW iVal iOp iLFvar iLFvars
variable {κ : RE P} {x y n : P.Ident} {d : Nat} {T : Std.HashMap P.Ident P.Ty}
  {Y : Std.HashMap P.Ident P.Ident} {st' st : WSt P} {b f : Bool} {Lc S : List P.Ident}
  {rest body B : PStmts P} {l2 : List (WItem P)} {l : String} {s : PStmt P} {a : WRes P}


/-! ## Names read by items -/

/-- The names a guarded expression reads: the free variables of a loop-free expression that its
    renaming does not rename, the targets of the renaming, the variables, and the names its
    parts read. -/
@[expose] def wreads : WExpr P → List P.Ident
  | .user e ren => (exprFV e).filter (fun y => !(ren.any fun p => p.1 == y)) ++ ren.map (·.2)
  | .var x => [x]
  | .lit _ => []
  | .ite c t e => wreads c ++ wreads t ++ wreads e

/-- The names an optional guarded expression reads (none for a havoc). -/
@[expose] def oreads : Option (WExpr P) → List P.Ident
  | some e => wreads e
  | none => []

/-- The names the guarded program emitted from the items `l` reads before declaring them in
    `l`, `b` telling whether a branching item follows `l`: a straight-line item counts only when
    a branching item follows it, a `set` reads its target, and a real branch ends the list. -/
@[expose] def wFV (b : Bool) : List (WItem P) → List P.Ident
  | [] => []
  | .init x _ e :: rest =>
    (if b || rest.any WItem.isBranching then oreads e else []) ++
      (wFV b rest).filter (· != x)
  | .set x e :: rest =>
    (if b || rest.any WItem.isBranching then x :: oreads e else []) ++ wFV b rest
  | .assume _ e _ :: rest =>
    (if b || rest.any WItem.isBranching then wreads e else []) ++ wFV b rest
  | .obls r cs :: rest =>
    (r.map RE.vars).getD [] ++ cs.flatMap (fun c => wreads c.2.2.1) ++ wFV b rest
  | .branch t e :: _ => wFV false t ++ wFV false e
  termination_by l => sizeOf l

/-- The names the flat items `l` read before declaring them in `l`, `b` telling whether a
    branching item follows `l`, as `wFV` on the items before resolution. -/
@[expose] def itemsFV (b : Bool) : List (Item P) → List P.Ident
  | [] => []
  | .plain s :: rest =>
    (if b || rest.any Item.isBranching then Stmt.freeVars s else []) ++
      (itemsFV b rest).filter (fun y => !(Stmt.topInits s).contains y)
  | .obls r cs :: rest => Block.freeVars (reachPre r ++ cs) ++ itemsFV b rest
  | .branch t e :: _ => itemsFV false t ++ itemsFV false e
  termination_by l => sizeOf l

/-! ## Free variables of statement lists -/

include iHash in
/-- A free variable of `s :: rest` is one of `s`, or one of `rest` that `s` does not declare. -/
theorem mem_stmtsFV_cons (h : x ∈ Block.freeVars (s :: rest)) :
    x ∈ Stmt.freeVars s ∨ (x ∈ Block.freeVars rest ∧ x ∉ Stmt.topInits s) := by
  unfold Block.freeVars at h; split at h <;> grind [Stmt.topInits, Stmt.freeVars]

include iHash in
/-- A free variable of `A ++ B` is one of `A` or one of `B`. -/
theorem mem_stmtsFV_append :
    ∀ {A : PStmts P}, x ∈ Block.freeVars (A ++ B) → x ∈ Block.freeVars A ∨ x ∈ Block.freeVars B :=
  fun {A} => by induction A <;> grind [mem_stmtsFV_cons, Block.freeVars_cons_sub, fv_tail]

include iHash in
/-- A free variable of a list without top-level declarations, or of the list that follows it,
    is one of their concatenation. -/
private theorem Block.freeVars_append_noInit :
    ∀ {A : PStmts P}, (∀ s ∈ A, Stmt.topInits s = []) →
      x ∈ Block.freeVars A ∨ x ∈ Block.freeVars B → x ∈ Block.freeVars (A ++ B) :=
  fun {A} => by induction A <;> grind [mem_stmtsFV_cons, Block.freeVars_cons_sub,
    fv_tail, Block.freeVars]

/-! ## Resolution -/

section
include iDec iBool iFvar iSubst iW

include iLFvars iHash in
/-- The free variables of the condition of a reachability are its variables. -/
theorem fv_RE_expr {r : RE P} (h : y ∈ exprFV r.expr) : y ∈ RE.vars r := by
  cases r <;> simp only [RE.expr, HasFvar.mkBoolVar, notE, andE, mem_exprFV, WPLang.getFvars_ite,
    WPLang.getFvars_tt, WPLang.getFvars_ff, List.not_mem_nil] at h <;>
    grind [RE.vars, HasFvar.eq_of_mem_getFvars_mkVar]

omit iBEq iLBEq in
/-- The reachability assumption declares nothing. -/
private theorem reachPre_noInit (r : Option (RE P)) : ∀ s ∈ reachPre r, Stmt.topInits s = [] := by
  rcases r with _ | (_ | _ | _ | _) <;> simp [reachPre, Stmt.topInits]

include iHash in
/-- Merging adjacent obligation runs keeps which items leave the main path, and every free
    variable of the merged items is one of the items. -/
theorem mergeObls_fv : ∀ (l : List (Item P)),
    (mergeObls l).any Item.isBranching = l.any Item.isBranching ∧
      ∀ b, ∀ x ∈ itemsFV b (mergeObls l), x ∈ itemsFV b l := fun l => by
  fun_induction mergeObls l with
  | case2 cs rest r cs' rest' hm ih =>
    have hl := fun x => Block.freeVars_append_noInit (x := x) (B := cs) (reachPre_noInit r)
    have hr := fun x => Block.freeVars_append_noInit (x := x) (B := cs') (reachPre_noInit r)
    simp only [hm, itemsFV, Item.isBranching, List.any_cons, List.mem_append] at ih ⊢
    grind [mem_stmtsFV_append]
  | _ => (try cases ‹Item P›) <;> grind [itemsFV, Item.isBranching]

include iHash in
/-- Every free variable of the nesting of flat items is a name the items read. -/
theorem nest_fv : ∀ (l : List (Item P)), ∀ x ∈ Block.freeVars (nest l), x ∈ itemsFV false l
  | [], x, hx => by simp [nest, Block.freeVars] at hx
  | .plain _ :: rest, x, hx | .obls _ _ :: rest, x, hx => by
    simp only [nest, nestCons] at hx
    split at hx <;> grind [itemsFV, mem_stmtsFV_cons, nest_fv rest x, Block.freeVars, Stmt.freeVars]
  | .branch t e :: rest, x, hx => by
    simp only [nest, nestCons] at hx
    split at hx <;> grind [itemsFV, nest_fv t x, nest_fv e x, Block.freeVars, Stmt.freeVars]
  termination_by l => sizeOf l

include iHash iLFvars

/-- The free variables of a resolved guarded expression are names it reads. -/
theorem resolveE_fv {T : Std.HashMap P.Ident P.Ty} {Y : Std.HashMap P.Ident P.Ident} :
    ∀ {we : WExpr P} {e' : P.Expr}, resolveE T Y we = .ok e' → ∀ y ∈ exprFV e', y ∈ wreads we
  | .user e ren, e', h, y, hy => by
    obtain ⟨wsub, hsub, hcov, rfl⟩ := resolveE_user_eq h
    rcases WPLang.getFvars_substFvars _ _ y (mem_exprFV.1 hy) with ⟨hy, hn⟩ | ⟨x, v, -, hf, hyv⟩
    · grind [wreads, mem_exprFV, Map.findNone_eq_notmem_mapfst.2 hn]
    · obtain ⟨q, hq, ⟨⟩⟩ := List.mem_map.1 (Map.find?_mem _ _ _ hf)
      grind [wreads, HasFvar.eq_of_mem_getFvars_mkVar hyv, hsub q hq]
  | .var x, e', h, y, hy =>
    (resolveE_var h).elim fun _ he =>
      List.mem_singleton.2 (HasFvar.eq_of_mem_getFvars_mkVar (mem_exprFV.1 (he ▸ hy)))
  | .lit b, e', h, y, hy => by
    cases b <;> cases h <;> simp [mem_exprFV, WPLang.getFvars_tt, WPLang.getFvars_ff] at hy
  | .ite c t f, e', h, y, hy => by
    obtain ⟨c', t', f', hc, ht, hf, rfl⟩ := resolveE_ite.1 h
    grind [wreads, resolveE_fv hc y, resolveE_fv ht y, resolveE_fv hf y, mem_exprFV,
      WPLang.getFvars_ite]

/-- The free variables of resolved obligations are names their conditions read. -/
private theorem resolveObls_fv :
    ∀ (cs : List (Bool × String × WExpr P × MetaData P)) (cs' : PStmts P),
      cs.mapM (fun (isCover, l, e, md) => do
        let e ← resolveE T Y e
        pure (if isCover then (.cmd (.cmd (.cover l e md)) : PStmt P)
          else .cmd (.cmd (.assert l e md)))) = .ok cs' →
      ∀ x ∈ Block.freeVars cs', x ∈ cs.flatMap (fun c => wreads c.2.2.1)
  | [], _, rfl, x, hx => by simp [Block.freeVars] at hx
  | (b, l, e, md) :: cs, cs', h, x, hx => by
    simp only [List.mapM_cons, Except.bind_is_ok, Except.pure_is_ok] at h
    obtain ⟨c, ⟨e', he, rfl⟩, cs'', hcs, rfl⟩ := h
    cases b <;> grind [mem_stmtsFV_cons hx, resolveE_fv he x,
      resolveObls_fv cs cs'' hcs x, Stmt.freeVars]

/-- Resolution keeps which items leave the main path, and the free variables of the resolved
    items are names the items read. -/
theorem resolveItems_fv :
    ∀ (l : List (WItem P)) (items : List (Item P)), resolveItems T Y l = .ok items →
      items.any Item.isBranching = l.any WItem.isBranching ∧
        ∀ b, ∀ x ∈ itemsFV b items, x ∈ wFV b l
  | [], _, rfl => ⟨rfl, fun _ x hx => by simp [itemsFV] at hx⟩
  | it :: rest, items, h => by
    obtain ⟨a, r, ha, hr, rfl⟩ := resolveItems_cons_ok h
    obtain ⟨hbr, ih⟩ := resolveItems_fv rest r hr
    rcases hit : it with ⟨x, _ | ty, _ | e⟩ | ⟨x, _ | e⟩ | ⟨l, e, md⟩ | ⟨rc, cs⟩ | ⟨t, e⟩ <;>
      simp only [resolveItem, resolveOE, Except.bind_is_ok, Except.pure_is_ok, hit,
        exists_eq_left'] at ha
    all_goals refine ⟨by grind [Item.isBranching, WItem.isBranching], fun b y hy => ?_⟩
    rotate_right
    · obtain ⟨t', ht, e', he, rfl⟩ := ha
      grind [itemsFV, wFV, (resolveItems_fv t t' ht).2 false y, (resolveItems_fv e e' he).2 false y]
    case obls =>
      obtain ⟨cs', hcs, rfl⟩ := ha
      rcases rc with _ | (_ | _ | _ | _) <;> grind [itemsFV, wFV, mem_stmtsFV_append,
        resolveObls_fv cs cs' hcs, fv_RE_expr, reachPre, Block.freeVars, Stmt.freeVars]
    all_goals grind [itemsFV, wFV, Stmt.freeVars, mkInit, Stmt.topInits, resolveE_fv, oreads]
  termination_by l => sizeOf l
  decreasing_by all_goals subst_vars; simp_wf; omega

/-- **The free variables of the emitted guarded program** are names the items of the rope read
    (`wFV false`). -/
theorem emit_fv {s : Rope (WItem P)} {lay : PStmts P} (h : emit T Y s = .ok lay) :
    ∀ x ∈ Block.freeVars lay, x ∈ wFV false s.toList := by
  obtain ⟨items, hi, ⟨⟩⟩ := (Except.bind_is_ok _ _ _).1 h
  exact fun x hx => (resolveItems_fv _ _ hi).2 _ x ((mergeObls_fv _).2 _ x (nest_fv _ x hx))

end

/-! ## Names read by items, by construct -/

include iHash in
/-- The negation of a guarded expression reads what it reads. -/
theorem wreads_not {a : WExpr P} (h : y ∈ wreads a.not) : y ∈ wreads a := by
  cases a <;> simp_all [WExpr.not, wreads]

include iDec iBool iFvar iSubst iId iLId iHash iW in
/-- The renamed expression of a run of `wRen e` reads current names, after the run, of free
    variables of `e`. -/
theorem wRen_reads {e : P.Expr} {we : WExpr P} {rd : List P.Ident}
    (h : (wRen e).run st = .ok ((we, rd), st')) :
    ∀ y ∈ wreads we, ∃ z ∈ exprFV e, curName st' z = some y := by
  obtain ⟨⟨ren, rfl, hren, hcov, -⟩, -⟩ := wRen_run h
  grind [wreads]

include iHash in
/-- The value of a reach context reads its variables. -/
theorem wreads_kExpr (h : y ∈ wreads (kExpr κ)) : y ∈ RE.vars κ := by
  cases κ <;> simp_all [kExpr, wreads, RE.vars, WExpr.not, WExpr.and]

include iHash in
/-- `ite(κ, t, e)` reads the variables of `κ` and what `t` and `e` read. -/
theorem wreads_kIte {t e : WExpr P} (h : y ∈ wreads (kIte κ t e)) :
    y ∈ RE.vars κ ∨ y ∈ wreads t ∨ y ∈ wreads e := by
  cases κ <;> simp_all [kIte, wreads, RE.vars, or_assoc, or_comm, or_left_comm]

include iHash in
/-- A disjunction reads what its operands read. -/
private theorem wreads_disjW :
    ∀ {l : List (WExpr P)}, y ∈ wreads (disjW l) → ∃ a ∈ l, y ∈ wreads a :=
  fun {l} => by induction l using disjW.induct <;> grind [disjW, WExpr.or, wreads]

/-! ## Reads of concatenations and of item lists built by maps -/

include iHash in
/-- Counting the straight-line items as if a branching item followed reads more. -/
theorem wFV_true : ∀ {b : Bool} {l : List (WItem P)}, n ∈ wFV b l → n ∈ wFV true l :=
  fun {b l} h => by induction l generalizing b <;> (try cases ‹WItem P›) <;> grind [wFV]

include iHash in
/-- A name read by `set`s built by a map is the target of one of them or read by its value. -/
theorem mem_wFV_map_set {α : Type} (f : α → P.Ident) (v : α → Option (WExpr P)) :
    ∀ {l : List α}, n ∈ wFV b (l.map fun a => .set (f a) (v a)) →
      ∃ a ∈ l, n = f a ∨ n ∈ oreads (v a) :=
  fun {l} => by induction l <;> grind [wFV, WItem.isBranching]

include iHash in
/-- Without a branching item and with none following, the items read nothing. -/
theorem wFV_false_nil : ∀ {l : List (WItem P)}, l.any WItem.isBranching = false →
    wFV false l = [] :=
  fun {l} => by induction l <;> (try cases ‹WItem P›) <;> grind [wFV, WItem.isBranching]

include iHash in
/-- A name read by `l1 ++ l2` is read by `l1` (followed by what follows `l2` or a branching item
    of `l2`), or read by `l2` and not declared by `l1`. -/
theorem mem_wFV_append :
    ∀ {l1 : List (WItem P)}, n ∈ wFV b (l1 ++ l2) →
      n ∈ wFV (b || l2.any WItem.isBranching) l1 ∨ (n ∈ wFV b l2 ∧ n ∉ wDecls l1) :=
  fun {l1} => by induction l1 <;> (try cases ‹WItem P›) <;> grind [wFV, wDecls]

omit iBEq iLBEq iFvars in
/-- The names a concatenation of items declares are those of its parts. -/
theorem mem_wDecls_append :
    ∀ {l1 : List (WItem P)}, n ∈ wDecls (l1 ++ l2) ↔ n ∈ wDecls l1 ∨ n ∈ wDecls l2 :=
  fun {l} => by induction l <;> (try cases ‹WItem P›) <;> grind [wDecls]

include iHash in
/-- Every name `A ++ B` reads is declared by `Pre` or has the property `Q`, when this holds of
    every name `A` reads and every name `B` reads is declared by `Pre ++ A` or has `Q`. -/
theorem wFV_app_pre {Q : P.Ident → Prop} {Pre A B : List (WItem P)}
    (hA : ∀ n ∈ wFV true A, n ∈ wDecls Pre ∨ Q n)
    (hB : ∀ n ∈ wFV b B, n ∈ wDecls (Pre ++ A) ∨ Q n) :
    ∀ n ∈ wFV b (A ++ B), n ∈ wDecls Pre ∨ Q n := fun n hn => by
  grind [mem_wFV_append hn, wFV_true (b := b || B.any WItem.isBranching), mem_wDecls_append]

include iHash in
/-- The items of `setReach κ X`: none under `top`, otherwise one `set` of the variable `κ`
    writes, reading what `X` reads. -/
theorem setReach_items (κ : RE P) (X : WExpr P) :
    (setReach κ X).toList = [] ∨ ∃ r e, (setReach κ X).toList = [.set r (some e)] ∧
      r ∈ RE.vars κ ∧ ∀ y ∈ wreads e, y ∈ wreads X := by
  cases κ <;> grind [setReach, Rope.toList_nil, Rope.toList_one, RE.vars, wreads_not]

/-! ## The read facts of a walk -/

/-- The read facts of the walk of a fragment reading `V`, well scoped from `S`, under the
    context `κ`, ending in the state `st'` with the result `r`, `fol` telling whether an
    obligation follows the fragment:
    * when no branching item follows the output or an obligation follows the fragment, every
      name the output reads before declaring it is the current name after the walk of a
      variable of `S` the fragment reads, or a variable of `κ`;
    * a snapshot registered for a label after the walk that is a registration of `r`, and the
      copy and the selector names of a carried merge whose copy is a registration of `r`, are
      declared by the output; when an obligation follows, the target of such a merge is the
      current name of a variable of `S` the fragment reads, or declared by the output;
    * an output with a branching item comes from a result carrying an obligation. -/
structure ReadsOK (κ : RE P) (S V : List P.Ident) (fol : Bool) (st' : WSt P) (r : WRes P) :
    Prop where
  reads : ∀ b, (b = true → fol = true) → ∀ n ∈ wFV b r.out.toList,
    (∃ z ∈ S, z ∈ V ∧ curName st' z = some n) ∨ n ∈ RE.vars κ
  pend : ∀ l e, e ∈ st'.pending.getD l [] → e ∈ r.regs.toList → e ∈ wDecls r.out.toList
  car : ∀ k q, q ∈ st'.carries.getD k [] → q.2.2 ∈ r.regs.toList →
    q.2.2 ∈ wDecls r.out.toList ∧
    (∃ e, q.2.1 = .ite e (.var q.2.2) (.var q.1) ∧ ∀ y ∈ wreads e, y ∈ wDecls r.out.toList) ∧
    (fol = true → (∃ z ∈ S, z ∈ V ∧ curName st' z = some q.1) ∨ q.1 ∈ wDecls r.out.toList)
  br : r.out.toList.any WItem.isBranching = true → r.hasObl = true

/-- The read property of the walk `m` of a fragment `ss` (a list, or the one statement of a
    statement walk) under the context `κ` at block depth `d`, `fol` telling whether an obligation
    follows it: every walk from a well-formed state `st` whose label depths are at most `d`,
    without carried merges deeper than `d`, whose context variables are fresh names drawn before
    it, whose dead names are drawn before it (`DeadBelow`) and whose live names are `KeyOK`, of a
    fragment well scoped from `S` (`wf S`) whose identifiers and those of `S` are avoided if of
    fresh-name form, has the read facts `ReadsOK`. -/
@[expose] def ReadsSpec (κ : RE P) (d : Nat) (m : WM P (WRes P))
    (ss : PStmts P) (wf : List P.Ident → Prop) (fol : Bool) : Prop :=
  ∀ st r st', WFSt st → m.run st = .ok (r, st') →
  ∀ S, wf S → (∀ x ∈ S ++ Block.idents ss, AvoidedIfFresh st x) →
    (∀ (l : String) (t : Nat), st.labelDepth[l]? = some t → t ≤ d) →
    (∀ k, d < k → st.carries.getD k [] = []) →
    (∀ y ∈ RE.vars κ, ∃ b j, y = freshName b j ∧ j < st.next) → DeadBelow st → LiveKeys st →
    ReadsOK κ S (Block.freeVars ss) fol st' r

/-- `ReadsSpec` of a statement-list walk, for the walks that occur: under `top`, no obligation
    follows the list. -/
abbrev ListReads (Lc : List P.Ident) (κ : RE P) (d : Nat) (fEnd : Bool) (ss : PStmts P) : Prop :=
  (κ = .top → fEnd = false) →
    ReadsSpec κ d (wpList κ d fEnd ss) ss (fun S => Block.WellScoped Lc S ss) fEnd

/-- `ReadsSpec` of a statement walk. -/
abbrev StmtReads (Lc : List P.Ident) (κ : RE P) (d : Nat) (f : Bool) (s : PStmt P) : Prop :=
  ReadsSpec κ d (wpStmt κ d f s) [s] (fun S => Stmt.WellScoped Lc S s) f

/-! ## Commands -/

include iDec iBool iFvar iSubst iId iHash in
/-- A result without output and registrations has the read facts. -/
private theorem readsOK_nil {V : List P.Ident} {fol : Bool} {r : WRes P} (ho : r.out = .nil)
    (hr : r.regs = .nil) : ReadsOK κ S V fol st' r := by
  constructor <;> simp [ho, hr, wFV, Rope.toList_nil]


/-- Unfolds the names the items of a straight-line step of the WP walk read, in `h` and the goal. -/
local macro "rd_simp " h:ident : tactic => `(tactic| simp only [Rope.toList_app,
  Rope.toList_nil, Rope.toList_one, List.cons_append, List.nil_append, wFV, List.any_cons,
  WItem.isBranching, List.any_nil, Bool.or_false, oreads, wreads, List.filter_nil,
  List.append_nil, List.mem_filter, List.mem_ite_nil_right, List.mem_cons, List.mem_append,
  RE.vars, List.flatMap_cons, List.flatMap_nil, Option.map_some, Option.getD_some,
  Option.map_none, Option.getD_none, setReach, kExpr, WExpr.not, WExpr.and, List.not_mem_nil,
  or_false, and_false] at $h:ident ⊢)

/-- Inverts a successful run of a straight-line step of the WP walk in the hypothesis `h`. -/
local macro "wp_inv " h:ident : tactic => `(tactic| simp only [Bool.not_true, Bool.not_false,
  Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_get,
  StateT.run_set, StateT.run_pure, Except.bind_is_ok, Except.pure_is_ok, Except.ok.injEq,
  Prod.mk.injEq, exists_eq_left', liveDel, liveAdd, wFresh_run, wFreshBool_run] at $h:ident)

/-- Splits the read facts of a straight-line step without registrations, whose final state `st'`
    updates `s` in fields other than the names (`hst`), leaving the reads of the output,
    unfolded, as the goal. -/
local macro "rd_ok " hst:ident st':term:max s:term:max : tactic => `(tactic| (
  replace $hst:ident : ∀ z, curName $st' z = curName $s z := fun z => $hst ▸ rfl
  refine ⟨fun b _ y hy => ?_, fun _ _ _ h => by simp only [Rope.toList_nil, List.not_mem_nil] at h,
    fun _ _ _ h => by simp only [Rope.toList_nil, List.not_mem_nil] at h,
    by simp [Rope.toList_one, Rope.toList_app, WItem.isBranching]⟩
  rd_simp hy))

include iDec iBool iFvar iSubst iId iLId iHash iW

/-- The walk of a command has the read property. -/
theorem stmtReads_cmd (Lc : List P.Ident) (κ : RE P) (d : Nat) (f : Bool) (c : CmdExt P) :
    StmtReads Lc κ d f (.cmd c) := by
  rintro st a st' - h S hS - - - - - -
  unfold wpStmt at h
  rcases c with ((⟨x, ty, e | _, md⟩ | ⟨x, e | _, md⟩ | ⟨l, e, md⟩ | ⟨l, e, md⟩ | ⟨l, e, md⟩) |
    ⟨p, args, md⟩)
  all_goals try first | cases h | (cases f; cases h; exact readsOK_nil rfl rfl)
  all_goals wp_inv h
  · split at h <;> wp_inv h <;> obtain ⟨⟨⟨we, rd⟩, s1⟩, h1, ⟨n, s2⟩, h2, rfl, hst⟩ := h
    all_goals
      obtain ⟨-, -, hcur, -⟩ := wDecl_spec h2
      rd_ok hst st' s2
      grind [wRen_reads h1, Block.freeVars, Stmt.freeVars, Stmt.WellScoped, RE.vars, wreads,
        → wreads_kIte]
  · obtain ⟨⟨n, s2⟩, h2, rfl, hst⟩ := h
    rd_ok hst st' s2
  · split at h <;> wp_inv h <;> obtain ⟨⟨⟨we, rd⟩, s1⟩, h1, ⟨n, s2⟩, h2, rfl, hst⟩ := h
    all_goals
      rd_ok hst st' s2
      grind [wRen_reads h1, wName_curName_keep h2, wName_curName h2, Block.freeVars,
        Stmt.freeVars, Stmt.WellScoped, RE.vars, wreads, → wreads_kIte]
  · split at h <;> wp_inv h <;> obtain ⟨⟨n, s2⟩, h2, ⟨hv, s3⟩, h3, rfl, hst⟩ := h
    all_goals
      rd_ok hst st' s3
      grind [(wFreshLike_walk h3).names x n nofun (wName_curName h2), Block.freeVars,
        Stmt.freeVars, Stmt.WellScoped, RE.vars, wreads, → wreads_kIte]
  all_goals obtain ⟨⟨⟨we, rd⟩, s1⟩, h1, rfl, hst⟩ := h
  all_goals
    rd_ok hst st' s1
    grind [wRen_reads h1, Block.freeVars, Stmt.freeVars, Stmt.WellScoped, RE.vars, kImp, wreads,
      → wreads_kIte]

/-! ## Exits and statements without a rule -/

/-- The walk of an `exit` has the read property. -/
theorem stmtReads_exit (Lc : List P.Ident) (κ : RE P) (d : Nat) (f : Bool) (l : String)
    (md : MetaData P) : StmtReads Lc κ d f (.exit l md) := by
  rintro st a st' hwf h S - - - - - - -
  unfold wpStmt at h
  obtain ⟨k, hk, hkn, -⟩ := freshIn_spec st.avoid "r" st.next
  cases κ <;> wp_inv h <;> (try split at h) <;> cases f <;> (try wp_inv h) <;>
    obtain ⟨rfl, rfl⟩ := h
  all_goals try exact readsOK_nil rfl rfl
  all_goals
    refine ⟨fun b _ n hn => .inr ?_, fun _ e _ he => ?_, fun k' q hq hq2 => ?_, fun hb => ?_⟩
    · rd_simp hn
      grind
    · simp_all [Rope.toList_one, Rope.toList_app, Rope.toList_nil, wDecls]
    · obtain ⟨⟨b, j, hj, hlt⟩, -⟩ := hwf.carries_get hq
      grind [Rope.toList_one, Rope.toList_nil, freshName_counter_inj]
    · simp_all [Rope.toList_one, Rope.toList_app, setReach, WItem.isBranching]

omit iLId in
/-- The walk of a statement that is not a command, an `exit`, a block or a deterministic `ite`
    has the read property. -/
theorem stmtReads_other (Lc : List P.Ident) (κ : RE P) (d : Nat) (f : Bool) (s : PStmt P)
    (hs : (∀ c, s ≠ .cmd c) ∧ (∀ l md, s ≠ .exit l md) ∧ (∀ l b md, s ≠ .block l b md) ∧
      ∀ c t e md, s ≠ .ite (.det c) t e md) : StmtReads Lc κ d f s := by
  intro st a st' _ h
  obtain ⟨h1, h2, h3, h4⟩ := hs
  unfold wpStmt at h
  rcases s with _ | _ | ⟨_ | c, t, e, md⟩ | _ | _ | _ <;>
    first | exact absurd rfl (h4 _ _ _ _) | cases h | simp at h1 h2 h3
  exact fun _ _ _ _ _ _ _ _ => readsOK_nil rfl rfl

/-! ## Statement lists -/

/-- The walk of an `init` of `x` with an obligation following it declares the current name of `x`
    before the walk. -/
private theorem init_decl (h : (wpStmt κ d f s).run st = .ok (a, st')) (hf : f = true)
    (hx : x ∈ Stmt.topInits s) (hn : curName st x = some n) : n ∈ wDecls a.out.toList := by
  have hD : ∀ {s s' : WSt P} {n'}, curName s x = some n → (wDecl x).run s = .ok (n', s') →
      n' = n := fun hs h => let ⟨⟨_, hw⟩, _⟩ := wDecl_spec h
    Option.some.inj ((wName_curName hw).symm.trans (wName_curName_keep hw x n hs))
  rcases s with ((⟨y, ty, e | _, md⟩ | _ | _ | _ | _) | _) | _ | _ | _ | _ | _ <;>
    simp only [Stmt.topInits, List.mem_singleton, List.not_mem_nil] at hx
  all_goals
    subst hx hf
    unfold wpStmt at h
    wp_inv h
  · obtain ⟨⟨⟨we, rd⟩, s0⟩, h0, ⟨n', s1⟩, h1, h⟩ := h
    obtain ⟨-, -, -, hkeep⟩ := wRen_run h0
    split at h <;> wp_inv h <;> grind [wDecls, Rope.toList_app, Rope.toList_one,
      hD (hkeep x n hn) h1]
  · obtain ⟨⟨n', s1⟩, h1, rfl, -⟩ := h
    simp [wDecls, Rope.toList_one, hD hn h1]

omit iLId in
/-- The walk of the empty list has the read property. -/
theorem listReads_nil (Lc : List P.Ident) (κ : RE P) (d : Nat) (fEnd : Bool) :
    ListReads Lc κ d fEnd [] := fun _ _ _ _ _ h => by
  simp only [wpList, StateT.run_pure] at h
  cases h
  exact fun _ _ _ _ _ _ _ _ => readsOK_nil rfl rfl

/-- The walk of `s :: rest` has the read property when the walks of `s` (for every obligation
    bit) and of `rest` have it. -/
theorem listReads_cons {fEnd : Bool} (hs : ∀ f, StmtReads Lc κ d f s)
    (hr : ListReads Lc κ d fEnd rest) : ListReads Lc κ d fEnd (s :: rest) := by
  rintro htop st R st' hwf hrun S ⟨hwfs, hwfr⟩ hav hL hhigh hκ hD hLK
  obtain ⟨r, st1, a, st2, h1, h2, hcase⟩ := wpList_run_cons hrun
  have hw1 := wpList_walkOK h1
  have hw2 := wpStmt_walkOK h2
  have hidr : ∀ x ∈ Block.idents rest, AvoidedIfFresh st x := fun x hx =>
    hav x (List.mem_append_right _ (List.mem_append_right _ hx))
  have hids : ∀ x ∈ S ++ Block.idents [s], AvoidedIfFresh st x := fun x hx =>
    hav x (by grind [Block.idents])
  have hwf1 : WFSt st1 := hw1.wf hwf fun x hx => hidr x (stmtsInits_mem_idents x hx)
  have Rr := hr htop st r st1 hwf h1 (Stmt.topInits s ++ S) hwfr (fun x hx => by
      grind [hids x, hav x, mem_idents_of_topInit, Block.idents]) hL hhigh hκ hD hLK
  have hfol : fEnd = true → (r.hasObl || (fEnd && !r.drop)) = true := by grind [wpList_drop h1]
  have hbr : r.out.toList.any WItem.isBranching = true →
      (r.hasObl || (fEnd && !r.drop)) = true := fun h => by simp [Rr.br h]
  have Ra := hs (r.hasObl || (fEnd && !r.drop)) st1 a st2 hwf1 h2 S hwfs
    (fun x hx b j hj => hw1.avoid ▸ hids x hx b j hj) (fun l t hl => hL l t (hw1.labelDepth l ▸ hl))
    (fun k hk => List.eq_nil_iff_forall_not_mem.2 fun q hq => by
      simpa [hhigh k hk] using wpList_carries_high h1 hL k hk q hq)
    (fun y hy => (hκ y hy).imp fun _ => .imp fun _ ⟨h1, h2⟩ => ⟨h1, Nat.lt_of_lt_of_le h2 hw1.next⟩)
    (wpList_deadBelow h1 hD) (wpList_liveKeys h1 hwf hidr (fun y hy => .inr (hκ y hy)) hLK)
  have hS2 : ∀ z ∈ S, ∀ m, curName st1 z = some m → curName st2 z = some m :=
    fun z hz m hm => hw2.names z m (wfl_inits_disjoint S [s] ⟨hwfs, trivial⟩ z hz) hm
  have hlift : ∀ {n}, (∃ z ∈ S, z ∈ Block.freeVars [s] ∧ curName st2 z = some n) →
      ∃ z ∈ S, z ∈ Block.freeVars (s :: rest) ∧ curName st2 z = some n :=
    fun ⟨z, hz, hv, hc⟩ => ⟨z, hz, fv_head hv, hc⟩
  rcases hcase with ⟨-, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩
  rotate_right
  · refine ⟨fun b hb n hn => ?_, fun l e he hr => ?_, fun k q hq hr => ?_, fun h => ?_⟩
    · simp only [WRes.combine, Rope.toList_app] at hn
      rcases mem_wFV_append hn with hn | ⟨hn, hnd⟩
      · exact (Ra.reads _ (by grind) n hn).imp_left hlift
      cases b <;> grind [wFV_false_nil, fv_tail, init_decl h2, Rr.reads _ hb n hn]
    · simp only [WRes.combine, Rope.toList_app, List.mem_append, mem_wDecls_append] at hr ⊢
      exact hr.imp (Ra.pend l e he) fun hr => Rr.pend l e (pending_regs h1 h2 hr he) hr
    · simp only [WRes.combine, Rope.toList_app, List.mem_append, mem_wDecls_append] at hr ⊢
      rcases hr with hr | hr
      · obtain ⟨h1', ⟨e, he, h2'⟩, h3'⟩ := Ra.car k q hq hr
        exact ⟨.inl h1', ⟨e, he, fun y hy => .inl (h2' y hy)⟩,
          fun hf => (h3' (hfol hf)).imp hlift .inl⟩
      have hq1 : q ∈ st1.carries.getD k [] := by
        obtain ⟨b, j, hbj, -, hj, -⟩ := wpList_regs h1 _ hr
        grind [wpStmt_carries hwf hL h1 h2 k, wpList_regs_live h1 hD _ hr,
          (wpStmt_dead h2 (freshName b j)).2, wpStmt_regs h2, freshName_counter_inj]
      grind [fv_tail, init_decl h2, Rr.car k q hq1 hr]
    · simp only [WRes.combine, Rope.toList_app, List.any_append, Bool.or_eq_true] at h ⊢
      exact h.imp Ra.br Rr.br
  all_goals
    exact ⟨fun b hb n hn => (Ra.reads b (hfol ∘ hb) n hn).imp_left hlift, Ra.pend,
      fun k q hq hr => (Ra.car k q hq hr).imp_right <| .imp_right fun h3 hf =>
        (h3 (hfol hf)).imp_left hlift, Ra.br⟩

/-! ## Blocks -/

/-- The read facts of a block, from those of its body walk. -/
private theorem block_core {κB : RE P} {md : MetaData P} {s0 st1 : WSt P} {B : WRes P}
    {pre : List (WItem P)} {rLs : List P.Ident} {J : Rope (WItem P)} (hwf : WFSt st)
    (hκB : κB ≠ .top) (h5 : (wpList κB (d + 1) f body).run s0 = .ok (B, st1))
    (RB : ReadsOK κB S (Block.freeVars body) f st1 B) (hp0 : s0.pending.getD l [] = [])
    (hc0 : s0.carries.getD (d + 1) [] = [])
    (hL0 : ∀ (l : String) (t : Nat), s0.labelDepth[l]? = some t → t ≤ d + 1)
    (hnext : st.next ≤ s0.next) (hvars : ∀ y ∈ RE.vars κB, y ∈ RE.vars κ ∨ y ∈ rLs)
    (hJ : ∀ n ∈ wFV true J.toList, n ∈ RE.vars κ ∨ n ∈ rLs ∨
      n ∈ (st1.pending.getD l []).filter fun e => !st1.dead.contains e)
    (hJb : J.toList.any WItem.isBranching = false)
    (hpre : (∀ b X, ∀ n ∈ wFV b (pre ++ X), n ∈ wFV b X ∧ n ∉ rLs) ∧
      (∀ X n, n ∈ wDecls X → n ∈ wDecls (pre ++ X)) ∧ pre.any WItem.isBranching = false)
    (hout : let C := (st1.carries.getD (d + 1) []).filter fun q => !st1.dead.contains q.2.2
      let tail :=
          (B.out.app (C.foldl (fun acc q => acc.app (.one (.set q.1 (some q.2.1)))) .nil)).app J
      (tail.isNil = true ∧ a.out.toList = []) ∨ a.out.toList = pre ++ tail.toList)
    (hregs : a.regs = B.regs) (hobl : a.hasObl = B.hasObl)
    (hcur : ∀ z, curName st' z = curName st1 z)
    (hpend : ∀ l' e, e ∈ st'.pending.getD l' [] →
      e ∈ st1.pending.getD l' [] ∨ e ∈ st.pending.getD l [])
    (hcar : ∀ k q, q ∈ st'.carries.getD k [] → q ∈ st1.carries.getD k []) :
    ReadsOK κ S (Block.freeVars [.block l body md]) f st' a := by
  have hlift : ∀ {n}, (∃ z ∈ S, z ∈ Block.freeVars body ∧ curName st1 z = some n) →
      ∃ z ∈ S, z ∈ Block.freeVars [.block l body md] ∧ curName st' z = some n :=
    fun ⟨z, hz, hv, hc⟩ => ⟨z, hz, by simpa [Block.freeVars, Stmt.freeVars] using hv,
      (hcur z).trans hc⟩
  have hC := fun q (hq : q ∈ (st1.carries.getD (d + 1) []).filter
      fun q => !st1.dead.contains q.2.2) =>
    RB.car (d + 1) q (List.mem_filter.1 hq).1 ((body_carries hκB hL0 hc0 h5).1 q hq)
  dsimp only at hout
  generalize (st1.carries.getD (d + 1) []).filter (fun q => !st1.dead.contains q.2.2) = C
    at hC hout
  have hMgL : (C.foldl (fun acc q => acc.app (.one (WItem.set q.1 (some q.2.1)))) Rope.nil).toList =
      C.map fun q => WItem.set q.1 (some q.2.1) := by
    rw [← List.foldl_map, Rope.toList_foldl_app, List.flatMap_map, List.map_eq_flatMap]
    simp [Rope.toList_one, Rope.toList_nil]
  generalize C.foldl (fun acc q => acc.app (.one (WItem.set q.1 (some q.2.1)))) Rope.nil = Mg
    at hMgL hout
  have hMJb : (Mg.toList ++ J.toList).any WItem.isBranching = false := by
    simp [hMgL, WItem.isBranching, hJb]
  have hdecl : ∀ n, n ∈ wDecls B.out.toList → n ∈ wDecls a.out.toList := fun n hn => by
    rcases hout with ⟨ht, -⟩ | ho
    · simp [Rope.isNil_toList (by simp_all [Rope.isNil_app'] : B.out.isNil = true), wDecls] at hn
    · rw [ho, Rope.toList_app, Rope.toList_app, List.append_assoc]
      exact hpre.2.1 _ n (mem_wDecls_append.2 (.inl hn))
  refine ⟨fun b hb n hn => ?_, fun l' e he hr => ?_, fun k q hq hr => ?_, fun h => ?_⟩
  · rcases hout with ⟨-, ho⟩ | ho
    · simp [ho, wFV] at hn
    obtain ⟨hn, hnr⟩ := hpre.1 b _ n (ho ▸ hn)
    rw [Rope.toList_app, Rope.toList_app, List.append_assoc] at hn
    rcases mem_wFV_append hn with hn | ⟨hn, hnd⟩
    · rw [hMJb, Bool.or_false] at hn
      exact (RB.reads b hb n hn).imp hlift fun hn => (hvars n hn).resolve_right hnr
    · cases b
      · simp [wFV_false_nil hMJb] at hn
      rcases mem_wFV_append hn with hn | ⟨hn, -⟩
      · obtain ⟨q, hq, hnq⟩ := mem_wFV_map_set _ _ (hMgL ▸ hn)
        obtain ⟨hk, ⟨e, he, hsel⟩, htg⟩ := hC q hq
        simp only [he, oreads, wreads, List.mem_append, List.mem_singleton] at hnq
        rcases hnq with rfl | (hnq | rfl) | rfl <;>
          first | exact (htg (hb rfl)).imp hlift (absurd · hnd) | grind
      · exact .inr ((hJ n hn).resolve_right fun h => h.elim hnr fun he => hnd <|
          RB.pend l n (List.mem_filter.1 he).1 (body_snaps_regs hκB hp0 h5 n (by simpa using he)))
  · refine (hpend l' e he).elim (fun he => hdecl e (RB.pend l' e he (hregs ▸ hr))) fun he => ?_
    obtain ⟨b, j, rfl, hj⟩ := hwf.pending_fresh l e he
    grind [wpList_regs h5 _ (hregs ▸ hr), freshName_counter_inj]
  · obtain ⟨h1, ⟨e, he, h2⟩, h3⟩ := RB.car k q (hcar k q hq) (hregs ▸ hr)
    exact ⟨hdecl _ h1, ⟨e, he, fun y hy => hdecl y (h2 y hy)⟩,
      fun hf => (h3 hf).imp hlift (hdecl _)⟩
  · refine hobl ▸ RB.br ?_
    rcases hout with ⟨-, ho⟩ | ho
    · simp [ho] at h
    · simpa [ho, Rope.toList_app, hpre.2.2, hMgL, WItem.isBranching, hJb] using h

/-- The walk of a block has the read property when the walks of its body (at the next depth,
    under every context) have it. -/
theorem stmtReads_block (md : MetaData P) (hB : ∀ κB, ListReads Lc κB (d + 1) f body) :
    StmtReads Lc κ d f (.block l body md) := by
  intro st a st' hwf h S hS hav hL hhigh hκ hD hLK
  have hwf0 := hwf.block_entry l (d + 1) st.clock
  have hav0 : ∀ x ∈ S ++ Block.idents body, AvoidedIfFresh st x := fun x hx => hav x (by
    simpa [Block.idents, Stmt.idents, ExprOrNondet.getVars_det,
      ExprOrNondet.getVars_nondet, getFvars_mem_exprFV] using hx)
  have hL0 : ∀ l' t, (st.labelDepth.insert l (d + 1))[l']? = some t → t ≤ d + 1 := fun l' t ht => by
    rw [Std.HashMap.getElem?_insert] at ht
    split at ht <;> grind [hL l' t]
  have hh0 : ∀ k, d + 1 < k → (st.carries.insert (d + 1) []).getD k [] = [] := by grind
  unfold wpStmt at h
  wp_inv h
  split at h
  · wp_inv h
    obtain ⟨⟨B, s5⟩, h5, rfl, rfl⟩ := h
    obtain ⟨k, hk, hkn, -⟩ := freshIn_spec (P := P) st.avoid "r" st.next
    have hwf3 := (wFreshBool_walk (wFreshBool_run "r" _)).wf hwf0 nofun
    simp only [hk] at h5 hwf3 ⊢
    have RB := hB (.name (freshName "r" k)) nofun _ B s5 hwf3 h5 S hS hav0 hL0 hh0
      (fun y hy => ⟨"r", k, by simpa [RE.vars] using hy, Nat.lt_succ_self k⟩)
      (fun b j hj => Nat.lt_of_lt_of_le (hD b j hj) (by simp only; omega))
      (fun n t ht => KeyOK.of_le (st := st) rfl (by simp only; omega) (hLK n t ht))
    refine block_core (κB := .name (freshName "r" k)) (rLs := [freshName "r" k])
      (pre := [.init (freshName "r" k) (.known HasBool.boolTy) (some (.lit true))])
      (J := if (!f) = true then .nil else if leOpt B.minT d = true then .one (.assume joinLabel
        (disjW (.var (freshName "r" k) :: ((s5.pending.getD l []).filter
          fun e => !s5.dead.contains e).reverse.map .var)) .empty) else .nil) hwf nofun h5
      RB (by simp) (by simp) hL0 (by simp only; omega) (fun y hy => .inr hy) ?_ ?_ ?_ (by
        dsimp only
        generalize Rope.isNil _ = c
        cases c <;> simp [Rope.toList_app, Rope.toList_one, Rope.toList_nil]) rfl rfl (fun _ => rfl)
      (fun l' e he => by split at he <;> grind [Std.HashMap.getD_eq_getD_getElem?])
      (fun k q hq => by grind)
    · intro n hn
      split at hn <;> try split at hn
      all_goals simp only [Rope.toList_nil, Rope.toList_one, wFV, List.any_nil, Bool.or_false,
        ↓reduceIte, List.append_nil, List.not_mem_nil] at hn
      grind [wreads, wreads_disjW hn]
    · split <;> (try split) <;> simp [Rope.toList_nil, Rope.toList_one, WItem.isBranching]
    · exact ⟨fun b X n hn => by simp_all [wFV, oreads, wreads],
        fun X n hn => by simp [wDecls, hn], rfl⟩
  rename_i hκt
  wp_inv h
  obtain ⟨⟨B, s5⟩, h5, rfl, rfl⟩ := h
  refine block_core (rLs := []) (pre := []) hwf hκt h5
    (hB _ (absurd · hκt) _ B s5 hwf0 h5 S hS hav0 hL0 hh0 hκ hD hLK) (by simp) (by simp) hL0
    (Nat.le_refl _) (fun y hy => .inl hy) ?_ ?_ ⟨fun b X n hn => ⟨hn, nofun⟩,
      fun X n hn => hn, rfl⟩ (.inr rfl) rfl rfl (fun _ => rfl)
    (fun l' e he => by split at he <;> grind [Std.HashMap.getD_eq_getD_getElem?])
    (fun k q hq => by grind)
  · intro n hn
    split at hn <;> try split at hn
    all_goals try simp only [Rope.toList_nil, wFV, List.not_mem_nil] at hn
    rcases setReach_items κ (disjW (kExpr κ :: _)) with hs | ⟨r, e, hs, hr, he⟩ <;>
      rw [hs] at hn
    · simp [wFV] at hn
    simp only [wFV, oreads, Bool.true_or, ↓reduceIte, List.append_nil, List.mem_cons] at hn
    rcases hn with rfl | hn
    · exact .inl hr
    grind [wreads, wreads_kExpr, wreads_disjW (he n hn)]
  · split <;> (try split) <;> simp only [Rope.toList_nil, List.any_nil]
    rcases setReach_items κ (disjW (kExpr κ :: _)) with hs | ⟨r, e, hs, -⟩ <;> rw [hs] <;> rfl

/-! ## Real branches -/

/-- The walk of a real branch has the read property when the walks of its arms (under `top`,
    no obligation following them) have it. -/
theorem iteRealReads {c : P.Expr} {tss ess : PStmts P} (md : MetaData P)
    (hT : ListReads Lc .top d false tss) (hE : ListReads Lc .top d false ess) :
    ReadsSpec κ d (wpIteReal κ d c tss ess) [.ite (.det c) tss ess md]
      (fun S => Stmt.WellScoped Lc S (.ite (.det c) tss ess md)) false := by
  rintro st a st' hwf h S ⟨hcS, hSt, hSe⟩ hav - hhigh - hD -
  have h00 := h
  unfold wpIteReal at h
  wp_inv h
  obtain ⟨⟨E, s2⟩, h2, ⟨T, s4⟩, h4, h⟩ := h
  have hid : ∀ x, x ∈ S ++ Block.idents tss ∨ x ∈ S ++ Block.idents ess ∨ x ∈ stmtsInits ess →
      x ∈ S ++ Block.idents [.ite (.det c) tss ess md] := by
    grind [Block.idents, Stmt.idents, stmtsInits_mem_idents]
  have wfE : WFSt { st with live := {}, labelDepth := {}, pending := {} } :=
    { hwf with pending_fresh := by simp, live_stamp := by simp }
  have hE' := (hE (fun _ => rfl) _ E s2 wfE h2 S hSe (fun x hx => hav x (hid x (.inr (.inl hx))))
    (fun l t ht => by simp at ht) hhigh nofun hD (liveKeys_empty rfl)).reads false nofun
  have wE := wpList_walkOK h2
  have wfT : WFSt { s2 with live := {} } :=
    { wE.wf wfE (fun x hx => hav x (hid x (.inr (.inr hx)))) with live_stamp := by simp }
  have hT' := (hT (fun _ => rfl) _ T s4 wfT h4 S hSt
    (fun x hx => wE.avoid ▸ hav x (hid x (.inl hx))) (fun l t ht => by simp [wE.labelDepth] at ht)
    (fun k hk => List.eq_nil_iff_forall_not_mem.2 fun q hq => by
      simpa [hhigh k hk] using wpList_carries_high h2 (fun l t ht => by simp at ht) k hk q hq)
    nofun (wpList_deadBelow h2 hD : DeadBelow s2) (liveKeys_empty rfl)).reads false nofun
  have wT := wpList_walkOK h4
  split at h
  · cases h
    exact readsOK_nil rfl rfl
  wp_inv h
  obtain ⟨⟨⟨wc, rdc⟩, s7⟩, h7, rfl, hst⟩ := h
  obtain ⟨g, k', hgk⟩ : ∃ g k', freshIn s7.avoid "g" s7.next = (g, k') := ⟨_, _, rfl⟩
  simp only [hgk] at hst ⊢
  obtain ⟨-, -, hs7, hk7⟩ := wRen_run h7
  have hcT : ∀ z ∈ S, ∀ m, curName s4 z = some m → curName st' z = some m := fun z _ m hm =>
    hst ▸ hk7 z m hm
  have hcE : ∀ z ∈ S, ∀ m, curName s2 z = some m → curName st' z = some m := fun z hz m hm =>
    hcT z hz m (wT.names z m (wfl_inits_disjoint S tss hSt z hz) hm)
  have hV : ∀ z, z ∈ Block.freeVars tss ∨ z ∈ Block.freeVars ess ∨ z ∈ exprFV c →
      z ∈ Block.freeVars [.ite (.det c) tss ess md] := by grind [Block.freeVars, Stmt.freeVars]
  have hg : ∀ n ∈ wreads (kAnd κ wc), (∃ z ∈ S, z ∈ Block.freeVars [.ite (.det c) tss ess md] ∧
      curName st' z = some n) ∨ n ∈ RE.vars κ := fun n hn =>
    (wreads_kIte hn).elim .inr fun h => h.elim (fun hn => let ⟨z, hz, hc⟩ := wRen_reads h7 n hn
      .inl ⟨z, hcS z hz, hV z (.inr (.inr hz)), hst ▸ hc⟩) (by simp [wreads])
  have hregs : ∀ e ∈ (T.regs.app E.regs).toList, ∃ b j, e = freshName b j ∧ st.next ≤ j := by
    grind [Rope.toList_app, wpList_regs h4, wpList_regs h2, wE.next]
  refine ⟨fun b hb n hn => ?_, fun l e he hr => ?_, fun k q hq hr => ?_, fun _ => rfl⟩
  · obtain rfl : b = false := Bool.eq_false_iff.2 fun h => Bool.false_ne_true (hb h)
    split at hn <;> (try split at hn) <;> simp only [Rope.toList_app, Rope.toList_one,
      List.cons_append, List.nil_append, wFV, List.any_cons, List.any_nil, WItem.isBranching,
      Bool.or_false, Bool.or_true, Bool.false_or, ↓reduceIte, oreads, wreads, List.mem_append,
      List.mem_filter, bne_iff_ne, ne_eq] at hn
    all_goals grind [RE.vars, kAnd, → wreads_kIte, wreads, WExpr.not]
  · obtain ⟨b, j, rfl, hj⟩ := hregs e hr
    rw [← hst, hs7] at he
    grind [hwf.pending_fresh l _ he, freshName_counter_inj]
  · obtain ⟨b, j, he, hj⟩ := hregs _ hr
    obtain ⟨hc, -⟩ := hwf.carries_get (wpIteReal_carries_eq h00 k q hq)
    grind [freshName_counter_inj]

end -- public section

end WP
end Imperative
