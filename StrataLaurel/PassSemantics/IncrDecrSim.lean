/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.PassSemantics.ProgTrav
import StrataLaurel.Implementation.EliminateIncrDecrAndCompoundAssign
import StrataLaurel.PassSemantics.EntryAt
import StrataLaurel.PassSemantics.NoJump

/-!
# Correctness of `EliminateIncrDecrAndCompoundAssign`

This file proves that `eliminateIncrDecrAndCompoundAssignPass` preserves the meaning of
programs. The pass lowers `x++`, `x--` and compound assignments such as `x += e` to plain
assignments. For a field target it first stores the receiver in a fresh local `$recv_N`.
The proof instantiates `PassRel` with `K = 7` (`id_rel`) and applies `entry_sim` and
`procAt_all`.

* `eliminateIncrDecrAndCompoundAssignPass_correct`: for a whole-program run, running the
  pass's output with 7 times the fuel ends with the same outcome and the same number of
  failed checks as running the input, unless the input gets stuck. The interpreter runs
  without a step budget (`limitSteps = false`).
* `eliminateIncrDecrAndCompoundAssignPass_procAt`: the same for a run that starts at any
  static procedure of the input, compared with the corresponding procedure of the output.
* `PID`: what every term of the input must satisfy: `Basic`, `NamesOK`, and every
  compound operator is among `okOp` and no target is a declaration (`IDOK`).
* `DivDecls p`: `p` declares `$divT` and `$modT` at most once each.
* `RecvRes`: the reserved names, those starting with `$recv_` and their shadow keys.
* `E`, `Rw`: the term relation and the rewrite step.
-/

namespace Strata.Laurel.PassSemantics.IncrDecrSim

open Strata.Laurel
open Strata.Laurel.Interpreter
open EliminateIncrDecr

inductive RecvRes : String → Prop where
  | base {k : String} : "$recv_".toList <+: k.toList → RecvRes k
  | shadow {k : String} : RecvRes k → RecvRes (shadowKey k)

private theorem not_recv_shadow (n : String) : ¬ "$recv_".toList <+: (shadowKey n).toList := by
  intro h
  have h' : "$recv_".toList <+: "$shadowed$".toList := by
    simp only [shadowKey, String.toList_append] at h
    exact List.prefix_of_prefix_length_le h (List.prefix_append _ _) (by decide)
  exact absurd h' (by decide)

private theorem recvRes_shadow {n : String} (h : RecvRes (shadowKey n)) : RecvRes n := by
  generalize hk : shadowKey n = k at h
  cases h with
  | base hb => subst hk; exact absurd hb (not_recv_shadow n)
  | shadow h => rw [(String.append_right_inj _).mp hk]; exact h

def DivX (ix : ProgramIndex) : Prop :=
  ∀ op : Operation, (op = .DivT ∨ op = .ModT) →
    (ix.procsNamed[op.procName]?.getD []).length ≤ 1 ∧
      ix.procs[op.procName]? = (ix.procsNamed[op.procName]?.getD []).head?

private theorem DivX.congr {ix jx : ProgramIndex} (h2 : jx.procs = ix.procs) (h11 : jx.procsNamed = ix.procsNamed)
    (h : DivX ix) : DivX jx := by
  intro op hop
  rw [h2, h11]
  exact h op hop

instance : Reserved where
  res := RecvRes
  shadow := fun _ hn h => hn (recvRes_shadow h)
  shadow_res := fun _ h => .shadow h
  resProc := fun _ => False
  retLabel := none
  noGlobals := False
  ren := fun _ _ => False
  vret := none
  vret_ok := fun _ h => (by cases h)
  vret_noret := fun _ h => (by cases h)
  ex := fun _ _ _ => False
  ixX _ ix _ := DivX ix
  ixX_congr _ _ _ _ _ _ h2 _ _ _ _ _ _ _ _ h11 _ _ h := DivX.congr h2 h11 h

instance : TyEqC := ⟨fun _ _ => Iff.rfl⟩

private theorem fresh_prefix (c : Nat) : "$recv_".toList <+: (s!"$recv_{c}").toList := by
  simp only [String.toList_append]
  exact List.prefix_append _ _

private theorem fresh_res (c : Nat) : Reserved.res s!"$recv_{c}" := .base (fresh_prefix c)

private theorem fresh_not_shadow (c : Nat) (k : String) : shadowKey k ≠ s!"$recv_{c}" := by
  intro h
  exact not_recv_shadow k (h ▸ fresh_prefix c)

def plainOp : Operation → Bool
  | .Eq | .Neq | .And | .Or | .Not | .Neg | .Add | .Sub | .Mul | .StrConcat => true
  | _ => false

def okOp : Operation → Bool
  | .DivT | .ModT => true
  | op => plainOp op

def NotDeclare (v : VariableMd) : Prop := ∀ p, v.val ≠ .Declare p

def IDOK (e : StmtExprMd) : Prop :=
  match e.val with
  | .IncrDecr _ _ t => NotDeclare t
  | .CompoundAssign op t _ => NotDeclare t ∧ okOp op = true
  | _ => True

def PID (e : StmtExprMd) : Prop := Basic e ∧ NamesOK e ∧ IDOK e

def Gl (_ : String) : Prop := True

section
variable (rt : StmtExprMd → Option Identifier)

abbrev fID : Bool → StmtExprMd → ElimM StmtExprMd := fun _ e => rewriteNode rt e

abbrev E : StmtExprMd → StmtExprMd → Prop := TE (fID rt) PID

def Rw (s t : StmtExprMd) : Prop :=
  ∃ r st, Shape (E rt) s r ∧ t = ((rewriteNode rt r).run st).1 ∧ IDOK s ∧
    ((∃ m o v, s.val = .IncrDecr m o v) ∨ ∃ o v e, s.val = .CompoundAssign o v e)

end

section
variable {rt : StmtExprMd → Option Identifier}

private theorem rewriteNode_other (r : StmtExprMd) (st : ElimState)
    (h1 : ∀ m o v, r.val ≠ .IncrDecr m o v) (h2 : ∀ o v e, r.val ≠ .CompoundAssign o v e) :
    (rewriteNode rt r).run st = (r, st) := by
  unfold rewriteNode
  split
  · rename_i m o v heq; exact absurd heq (h1 m o v)
  · rename_i o v e heq; exact absurd heq (h2 o v e)
  · rfl

private theorem lowerIncrDecr_notYield (m : IncrDecrMode) (o : IncrDecrOp) (t : VariableMd) (src : FileRange) :
    NotYield (lowerIncrDecr m o t src) := by
  cases m <;> simp [NotYield, lowerIncrDecr, lowerToAssign, lowerOpAssign]

private theorem rewriteNode_notYield (u : Bool) (r : StmtExprMd) (st : ElimState) (h : NotYield r) :
    NotYield ((fID rt u r).run st).1 := by
  show NotYield ((rewriteNode rt r).run st).1
  unfold rewriteNode withReceiverBound
  split
  all_goals (try split)
  all_goals first
    | exact h
    | exact lowerIncrDecr_notYield _ _ _ _
    | simp [NotYield, lowerOpAssign]
    | simp [NotYield, StateT.run, bind, StateT.bind, freshReceiver, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, pure, StateT.pure]

private theorem sl_assign (ts : List VariableMd) (v : StmtExprMd) (src : FileRange) :
    statementLabels ⟨.Assign ts v, src⟩ = [] :=
  statementLabels_other _ _ (by intros; nofun) (by intros; nofun)

private theorem sa_assign (ts : List VariableMd) (v : StmtExprMd) (src : FileRange) :
    (stackAnnotation? ⟨.Assign ts v, src⟩).isNone = true := by
  simp [stackAnnotation?]

private theorem sl_call (r : Option StmtExprMd) (f : Identifier) (as : List StmtExprMd) (ta : List HighTypeMd)
    (src : FileRange) : statementLabels ⟨.Call r f as ta, src⟩ = [] :=
  statementLabels_other _ _ (by intros; nofun) (by intros; nofun)

private theorem lowerOpAssign_plain (op : Operation) (t : VariableMd) (R : StmtExprMd) (src : FileRange) :
    statementLabels (lowerOpAssign op t R src) = [] ∧ (stackAnnotation? (lowerOpAssign op t R src)).isNone = true := by
  simp [lowerOpAssign, sl_assign, stackAnnotation?]

private theorem lowerIncrDecr_plain (m : IncrDecrMode) (o : IncrDecrOp) (t : VariableMd) (src : FileRange) :
    statementLabels (lowerIncrDecr m o t src) = [] ∧ (stackAnnotation? (lowerIncrDecr m o t src)).isNone = true := by
  cases m <;> simp [lowerIncrDecr, lowerToAssign, lowerOpAssign, sl_assign, sl_call, stackAnnotation?]

private theorem rewriteNode_plain (r : StmtExprMd) (st : ElimState)
    (hk : (∃ m o v, r.val = .IncrDecr m o v) ∨ ∃ o v e, r.val = .CompoundAssign o v e) :
    statementLabels ((rewriteNode rt r).run st).1 = [] ∧ (stackAnnotation? ((rewriteNode rt r).run st).1).isNone = true := by
  rcases r with ⟨rv, rs⟩
  rcases hk with ⟨m, o, v, hv⟩ | ⟨o, v, e, hv⟩ <;> dsimp only at hv <;> subst hv <;>
    (rcases v with ⟨vv, vs⟩; cases vv) <;>
    simp [rewriteNode, withReceiverBound, lowerIncrDecr_plain, lowerOpAssign_plain, statementLabels_block,
      sl_assign, StateT.run, bind, StateT.bind, freshReceiver, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, pure, StateT.pure] <;> simp [stackAnnotation?]

/-- The term relation `E rt` of `EliminateIncrDecrAndCompoundAssign` is closed under
`NR (E rt) (Rw rt) Gl`: a term and its traversal result either have the same shape with related
value children, or the term is an `IncrDecr` or `CompoundAssign` and the result is its rewrite
(`Rw rt`). -/
theorem closed (s t : StmtExprMd) (h : E rt s t) : NR (E rt) (Rw rt) Gl s t := by
  obtain ⟨⟨u, st, rfl⟩, hs⟩ := h
  obtain ⟨r, st1, heq, hsh⟩ := trav_shape (f := fID rt) (fun e he => he.1) (fun e he => he.2.1)
    rewriteNode_notYield u s st hs
  rw [heq]
  by_cases hk : (∃ m o v, s.val = .IncrDecr m o v) ∨ ∃ o v e, s.val = .CompoundAssign o v e
  · exact .inr ⟨r, st1, hsh, rfl, hs.here.2.2, hk⟩
  · have h1 : ∀ m o v, r.val ≠ .IncrDecr m o v := by
      intro m o v hr
      cases hsh <;> simp_all [Unsup]
    have h2 : ∀ o v e, r.val ≠ .CompoundAssign o v e := by
      intro o v e hr
      cases hsh <;> simp_all [Unsup]
    show NR _ _ _ s ((rewriteNode rt r).run st1).1
    rw [rewriteNode_other r st1 h1 h2]
    exact nr_triv (fun _ _ => trivial) (fun _ _ => trivial) hsh (fun _ _ _ => trivial)

end

section Local
variable {rt : StmtExprMd → Option Identifier} {G : StackFrame} {cfg : ExternalBackendM PM}
  {T U : SimRel}

private theorem fsr_modify {g : EvalState → EvalState} {x : EvalM PM α} {k : PUnit → EvalM PM β} {A : α → β → Prop}
    (hg : ∀ σ σ', StRel G (IxRel (E rt)) σ σ' → StRel G (IxRel (E rt)) σ (g σ'))
    (hk : FSH (Sm (E rt) Gl G) T U A x (k ())) :
    FSH (Sm (E rt) Gl G) T U A x (modify g >>= k) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  rw [run_bind, run_modify]
  exact hk.sim σ (g σ') τ τ' (hg σ σ' hs) ht hn

private theorem fsr_get {x : EvalM PM α} {k : EvalState → EvalM PM β} {A : α → β → Prop}
    (hk : ∀ s', s'.coroSelf = none → FSH (Sm (E rt) Gl G) T U A x (k s')) :
    FSH (Sm (E rt) Gl G) T U A x (get >>= k) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have hs' : StRel G (IxRel (E rt)) σ σ' := hs
  rw [run_bind, run_get]
  exact (hk σ' hs'.coroSelf').sim σ σ' τ τ' hs ht hn

private theorem fs_readLocal {x x' : Identifier} (hx : x.text = x'.text) (hr : ¬ Reserved.res x.text) {n M : Nat}
    (hM : n ≤ M) :
    FS (Sm (E rt) Gl G) Eq (evalExpr cfg n (.Var (.Local x))) (evalExpr cfg M (.Var (.Local x'))) := by
  rcases n with _ | n
  · exact fs_vac rfl
  obtain ⟨M, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  simp only [evalExpr]
  refine fs_bind fs_get (fun σ σ' hσ => ?_)
  have hσ : StRel G (IxRel (E rt)) σ σ' := hσ
  rw [← hx, lookupVar_congr hσ hr (.inl (notV_none rfl _))]
  cases lookupVar σ x.text with
  | some v => exact fs_pure rfl
  | none => exact fs_stuck _ _

private theorem opCall_plain {op : Operation} (h : plainOp op = true) (args : List Value) :
    opCall cfg op args = evalOp cfg op args := by
  cases op <;> simp [plainOp] at h <;> simp [opCall, bvCmpName]

private theorem fs_liftM_eq {X : PM α} (hX : PConst X) {S : SimRel} :
    FSH S S U (fun a b => a = b ∧ ∀ τ, X τ = .ok (a, τ)) (liftM X : EvalM PM α) (liftM X) := by
  refine ⟨fun σ σ' τ τ' hs ht _ => ?_⟩
  rcases hX with ⟨a, ha⟩ | ⟨e, he⟩
  · simp only [run_lift, ha, RR, ExRel]
    exact ⟨by simp, hs, ht⟩
  · simp only [run_lift, he, RR]
    exact id

private theorem not_coro (op : Operation) : ((mkId op.procName).text == coroCompletionName) = false := by
  cases op <;> decide

private theorem of_procName (op : Operation) : opOf? (mkId op.procName).text = some op := by
  cases op <;> rfl

private theorem tcall (k : Nat) (c : Identifier) (args : List StmtExprMd) (ta : List HighTypeMd) (src : FileRange) :
    evalExprMd cfg (k + 1) ⟨.Call none c args ta, src⟩ =
      (modify fun (s : EvalState) => { s with callSite := src }) >>= fun _ => evalExpr cfg k (.Call none c args ta) :=
  jumpBoundary_noJ (NoJ.bind (NoJ.modify _) (fun _ => noJ_callNone cfg _ _ _ _))

private theorem tvar (k : Nat) (x : Identifier) (src : FileRange) :
    evalExprMd cfg (k + 1) ⟨.Var (.Local x), src⟩ = evalExpr cfg k (.Var (.Local x)) :=
  jumpBoundary_noJ (noJ_varLocal cfg _ _)

private theorem tlit (k : Nat) (i : Int) (src : FileRange) :
    evalExprMd cfg (k + 2) ⟨.LiteralInt i, src⟩ = pure (.int ⟨i⟩) :=
  jumpBoundary_noJ (NoJ.pure _)

private theorem tassign (k : Nat) (t : VariableMd) (v : StmtExprMd) (src : FileRange) :
    evalExprMd cfg (k + 1) ⟨.Assign [t] v, src⟩ = evalExpr cfg k (.Assign [t] v) :=
  jumpBoundary_noJ (noJ_assign1 cfg _ _ _)

private theorem lookupCallee_mkId (ix : ProgramIndex) (n : String) : lookupCallee ix (mkId n) = ix.procs[n]? := by
  simp [lookupCallee, mkId]

private theorem divX_some {ix : ProgramIndex} (h : DivX ix) {op : Operation} (hop : op = .DivT ∨ op = .ModT) {old : Value}
    {P : Procedure} (hd : divProc? ix op old = some P) : lookupCallee ix (mkId op.procName) = some P := by
  obtain ⟨hl, hp⟩ := h op hop
  unfold divProc? at hd
  have hm := List.mem_of_find?_eq_some hd
  rw [lookupCallee_mkId, hp]
  revert hl hm
  generalize (ix.procsNamed[op.procName]?.getD []) = l
  intro hl hm
  match l, hl, hm with
  | [Q], _, hm => simp at hm; simp [hm]
  | _ :: _ :: _, hl, _ => simp at hl

private theorem divX_none {ix : ProgramIndex} (h : DivX ix) {op : Operation} (hop : op = .DivT ∨ op = .ModT)
    (he : (ix.procsNamed[op.procName]?.getD []).isEmpty = true) : lookupCallee ix (mkId op.procName) = none := by
  obtain ⟨-, hp⟩ := h op hop
  rw [lookupCallee_mkId, hp]
  revert he
  cases ix.procsNamed[op.procName]?.getD [] <;> simp

private theorem fs_stuck_bind {S T U : SimRel} {A : α → β → Prop} (m : String) (k : γ → EvalM PM α) (y : EvalM PM β) :
    FSH S T U A (stuckError m >>= k) y :=
  ⟨fun _ _ _ _ _ _ _ => by
    show RR T U A (.error (.stuck m)) _
    exact RR.ofStuck (.mk m) _⟩

private theorem fs_divPre {G' : StackFrame} {op : Operation} (hop : op = .DivT ∨ op = .ModT) {old : Value}
    {args : List Value} {n M : Nat} {k : EvalM PM α} {t : EvalM PM γ} {k' : γ → EvalM PM α}
    (hpre : ∀ (site site' : FileRange) (P P' : Procedure), ProcRelB (E rt) P P' →
      FS (Sm (E rt) Gl G') Eq (checkPreconditions cfg n site P args) (checkPreconditions cfg M site' P' args))
    (hk : FS (Sm (E rt) Gl G') Eq k (t >>= k')) :
    FS (Sm (E rt) Gl G') Eq
      (get >>= fun (st : EvalState) => match divProc? st.index op old with
        | some P => checkPreconditions cfg n st.stmtSite P args >>= fun _ => k
        | none => noFitPrelude st.index op args >>= fun _ => k)
      (get >>= fun (st : EvalState) => (match lookupCallee st.index (mkId op.procName) with
        | some P => checkPreconditions cfg M st.stmtSite P args >>= fun _ => t
        | none => missingPrelude (mkId op.procName).text args >>= fun _ => t) >>= k') := by
  refine fs_bind fs_get (fun σ σ' hσ => ?_)
  have hσ : StRel G' (IxRel (E rt)) σ σ' := hσ
  have hx : DivX σ.index := hσ.index.extra
  have hcal := hσ.index.callee (mkId op.procName) (fun h => h)
  cases hd : divProc? σ.index op old with
  | some P =>
    rw [divX_some hx hop hd] at hcal
    revert hcal
    cases lookupCallee σ'.index (mkId op.procName) with
    | none => simp [ORel]
    | some P' =>
      intro hP
      simp only [bind_assoc]
      exact fs_bind (hpre _ _ _ _ hP.toB) (fun _ _ _ => hk)
  | none =>
    unfold noFitPrelude
    by_cases he : (σ.index.procsNamed[op.procName]?.getD []).isEmpty = true
    · rw [divX_none hx hop he] at hcal
      revert hcal
      cases lookupCallee σ'.index (mkId op.procName) with
      | some _ => simp [ORel]
      | none =>
        intro _
        simp only [he, ite_true, bind_assoc]
        exact fs_bind (fs_missingPrelude _ _) (fun _ _ _ => hk)
    · simp only [he, Bool.false_eq_true, ite_false]
      exact fs_stuck_bind _ _ _

private theorem cmp_local {op : Operation} (hop : okOp op = true) {x x' : Identifier} (hx : x.text = x'.text)
    (hr : ¬ Reserved.res x.text) {ts ts' src' : FileRange} {R R' : StmtExprMd} {n M : Nat}
    (hR : FS (Sm (E rt) Gl G) Eq (evalExprMd cfg (n + 1) R) (evalExprMd cfg (M + 1) R'))
    (hpre : ∀ args (site site' : FileRange) (P P' : Procedure), ProcRelB (E rt) P P' →
      FS (Sm (E rt) Gl G) Eq (checkPreconditions cfg (n + 1) site P args) (checkPreconditions cfg (M + 1) site' P' args))
    (hc : CfgB cfg) (hM : n ≤ M) :
    FS (Sm (E rt) Gl G) Eq (evalExpr cfg (n + 2) (.CompoundAssign op ⟨.Local x, ts⟩ R))
      (evalExpr cfg (M + 4) (lowerOpAssign op ⟨.Local x', ts'⟩ R' src').val) := by
  cases op <;> simp only [okOp, plainOp, Bool.false_eq_true] at hop
  all_goals
    simp only [evalExpr, tcall, tvar, readForUpdate, lowerOpAssign, targetAsRead, assignTarget, writeUpdate,
      List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind, not_coro, of_procName, hc.strict, Bool.false_eq_true,
      isPartialOp, opCall, bvCmpName, Option.bind_eq_bind, Option.bind_none, ↓reduceIte]
    refine fsr_modify (fun σ σ' h => by strel h) ?_
    refine fsr_get (fun _ _ => ?_)
    refine fs_bind (fs_readLocal hx hr hM) (fun a b hab => ?_)
    subst hab
    refine fs_bind hR (fun r r' h => ?_)
    subst h
    first
    | (refine fs_bind (fs_liftM (evalOp_pconst hc _ _)) (fun v v' h => ?_)
       subst h
       exact fs_bind (fs_assignLocal x x' hx hr (notV_none rfl _) v) (fun _ _ _ => fs_pure rfl))
    | (refine fs_divPre (by simp) (hpre _) ?_
       refine fs_bind (fs_liftM (evalOp_pconst hc _ _)) (fun v v' h => ?_)
       subst h
       exact fs_bind (fs_assignLocal x x' hx hr (notV_none rfl _) v) (fun _ _ _ => fs_pure rfl))

private theorem tlit1 (k : Nat) (i : Int) (src : FileRange) :
    evalExprMd cfg (k + 1) ⟨.LiteralInt i, src⟩ = evalExpr cfg k (.LiteralInt i) :=
  jumpBoundary_noJ (noJ_literalInt cfg _ _)

def addSub : IncrDecrOp → Operation
  | .Incr => .Add
  | .Decr => .Sub

def subAdd : IncrDecrOp → Operation
  | .Incr => .Sub
  | .Decr => .Add

private theorem inverse (o : IncrDecrOp) {old v : Value}
    (hX : ∀ τ, evalOp cfg (addSub o) [old, .int ⟨1⟩] τ = .ok (v, τ)) :
    evalOp cfg (subAdd o) [v, .int ⟨1⟩] = pure old := by
  cases o <;> cases old
  case Incr.int p =>
    obtain ⟨a⟩ := p
    have := hX {}
    simp only [addSub, evalOp] at this
    cases this
    show (pure (Value.int ⟨a + 1 - 1⟩) : PM Value) = _
    rw [Int.add_sub_cancel]
  case Decr.int p =>
    obtain ⟨a⟩ := p
    have := hX {}
    simp only [addSub, evalOp] at this
    cases this
    show (pure (Value.int ⟨a - 1 + 1⟩) : PM Value) = _
    rw [Int.sub_add_cancel]
  all_goals
    have := hX {}
    simp only [evalOp, addSub, opIllTyped, InterpHost.stuck, List.map_cons, List.map_nil] at this
    all_goals first | cases this | skip

private theorem pre_local (o : IncrDecrOp) {x x' : Identifier} (hx : x.text = x'.text) (hr : ¬ Reserved.res x.text)
    {ts ts' src' : FileRange} {n M : Nat} (hc : CfgB cfg) (hM : n ≤ M) :
    FS (Sm (E rt) Gl G) Eq (evalExpr cfg (n + 2) (.IncrDecr .Pre o ⟨.Local x, ts⟩))
      (evalExpr cfg (M + 4) (lowerIncrDecr .Pre o ⟨.Local x', ts'⟩ src').val) := by
  cases o
  all_goals
    simp only [evalExpr, tcall, tvar, tlit1, readForUpdate, lowerIncrDecr, lowerToAssign, lowerOpAssign,
      targetAsRead, assignTarget, writeUpdate, List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind, not_coro,
      of_procName, hc.strict, Bool.false_eq_true, ite_false, isPartialOp, opCall, bvCmpName, Option.bind_eq_bind,
      Option.bind_none]
    rcases n with _ | n
    · exact fs_vac rfl
    obtain ⟨M, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
    simp only [show evalExpr cfg (M + 1) (.LiteralInt 1) = pure (.int ⟨1⟩) from rfl, pure_bind]
    refine fsr_modify (fun σ σ' h => by strel h) ?_
    refine fsr_get (fun _ _ => ?_)
    refine fs_bind (fs_readLocal hx hr (by omega)) (fun a b hab => ?_)
    subst hab
    refine fs_bind (fs_liftM (evalOp_pconst hc _ _)) (fun v v' h => ?_)
    subst h
    exact fs_bind (fs_assignLocal x x' hx hr (notV_none rfl _) v) (fun _ _ _ => fs_pure rfl)

private theorem post_local (o : IncrDecrOp) {x x' : Identifier} (hx : x.text = x'.text) (hr : ¬ Reserved.res x.text)
    {ts ts' src' : FileRange} {n M : Nat} (hc : CfgB cfg) (hM : n ≤ M) :
    FS (Sm (E rt) Gl G) Eq (evalExpr cfg (n + 2) (.IncrDecr .Post o ⟨.Local x, ts⟩))
      (evalExpr cfg (M + 6) (lowerIncrDecr .Post o ⟨.Local x', ts'⟩ src').val) := by
  cases o
  all_goals
    simp only [evalExpr, tcall, tvar, tlit1, tassign, readForUpdate, lowerIncrDecr, lowerToAssign,
      lowerOpAssign, targetAsRead, assignTarget, writeUpdate, List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind,
      not_coro, of_procName, hc.strict, Bool.false_eq_true, ite_false, isPartialOp, opCall, bvCmpName, Option.bind_eq_bind,
      Option.bind_none]
    rcases n with _ | n
    · exact fs_vac rfl
    obtain ⟨M, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
    simp only [show evalExpr cfg (M + 1) (.LiteralInt 1) = pure (.int ⟨1⟩) from rfl, pure_bind]
    refine fsr_get (fun _ _ => ?_)
    refine fsr_modify (fun σ σ' h => by strel h) ?_
    refine fsr_get (fun _ _ => ?_)
    refine fs_bind (fs_readLocal hx hr (by omega)) (fun a b hab => ?_)
    subst hab
    refine fs_bind (fs_liftM_eq (evalOp_pconst hc _ _)) (fun v v' ⟨h, hX⟩ => ?_)
    subst h
    refine fs_bind (fs_assignLocal x x' hx hr (notV_none rfl _) v) (fun _ _ _ => ?_)
    simp (config := { decide := true }) only [ite_true, ite_false] at hX ⊢
    first
      | (have hi := inverse (o := .Incr) hX; simp only [subAdd] at hi; rw [hi]; exact fs_pure rfl)
      | (have hi := inverse (o := .Decr) hX; simp only [subAdd] at hi; rw [hi]; exact fs_pure rfl)

end Local

section Field
variable {rt : StmtExprMd → Option Identifier} {G : StackFrame} {cfg : ExternalBackendM PM} {T U : SimRel}

def SmU (G G' : StackFrame) : SimRel :=
  ⟨fun σ σ' => StRel G (IxRel (E rt)) σ σ' ∨ StRel G' (IxRel (E rt)) σ σ', EvRel (E rt), CtlOK Gl G,
    Reserved.retLabel, fun _ _ _ => False⟩

private theorem FSH.errU {S T U V : SimRel} {x : EvalM PM α} {y : EvalM PM β} {A : α → β → Prop}
    (h : FSH S T U A x y) (hst : ∀ σ σ', U.st σ σ' → V.st σ σ') (hok : ∀ c, U.ok c → V.ok c)
    (htr : ∀ τ τ', TrRel U τ τ' → TrRel V τ τ') (hr : U.ret = V.ret := by rfl)
    (hw : ∀ v σ σ', U.win v σ σ' → V.win v σ σ' := by
      intro _ _ _ h; first | exact False.elim h | exact absurd h.1 (not_free_none rfl _)) : FSH S T V A x y := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have r := h.sim σ σ' τ τ' hs ht hn
  revert r
  rcases run x σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;> rcases run y σ' τ' with e' | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;>
    simp only [RR, ExRel, imp_self, false_and]
  exact fun ⟨h1, h4⟩ => ⟨h1.mono hr hok hst hw, htr _ _ h4⟩

private theorem toU {x : EvalM PM α} {y : EvalM PM β} {A : α → β → Prop} {G' : StackFrame} {T : SimRel}
    (h : FSH (Sm (E rt) Gl G) T (Sm (E rt) Gl G) A x y) :
    FSH (Sm (E rt) Gl G) T (SmU (rt := rt) G G') A x y :=
  FSH.errU h (fun _ _ h => .inl h) (fun _ h => h) (fun _ _ h => h)

private theorem toU' {x : EvalM PM α} {y : EvalM PM β} {A : α → β → Prop} {G' : StackFrame} {S T : SimRel}
    (h : FSH S T (Sm (E rt) Gl G') A x y) :
    FSH S T (SmU (rt := rt) G G') A x y :=
  FSH.errU h (fun _ _ h => .inr h) (fun _ h => CtlOK.none rfl h) (fun _ _ h => h)

private theorem fsr_switch {g : EvalState → EvalState} {G' : StackFrame} {x : EvalM PM α} {k : PUnit → EvalM PM β}
    {A : α → β → Prop}
    (hg : ∀ σ σ', StRel G (IxRel (E rt)) σ σ' → StRel G' (IxRel (E rt)) σ (g σ'))
    (hk : FSH (Sm (E rt) Gl G') T U A x (k ())) :
    FSH (Sm (E rt) Gl G) T U A x (modify g >>= k) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  rw [run_bind, run_modify]
  exact hk.sim σ (g σ') τ τ' (hg σ σ' hs) ht hn

private theorem fs_fail_both {S : SimRel} {x : EvalM PM α} {y : EvalM PM β} {A : α → β → Prop} (P : EvalState → Prop)
    (hP : ∀ σ σ', S.st σ σ' → P σ')
    (hx : ∀ σ τ, ∃ e, run x σ τ = .error e) (hy : ∀ σ' τ', P σ' → ∃ m, run y σ' τ' = .error (.fail m)) :
    FSH S T U A x y := by
  refine ⟨fun σ σ' τ τ' hs _ _ => ?_⟩
  obtain ⟨e, he⟩ := hx σ τ
  obtain ⟨e', he'⟩ := hy σ' τ' (hP σ σ' hs)
  rw [he, he']
  exact fun h => absurd h stuck_fail

private theorem lookup_ghost {G' : StackFrame} {σ σ' : EvalState} (h : StRel G' (IxRel (E rt)) σ σ') {x : String}
    (hx : Reserved.res x) {v : Value} (hv : G'[x]? = some v) : lookupVar σ' x = some v := by
  simp only [lookupVar, h.stack.ghost x hx (fun h => h) (fun h => h), hv]
  rfl

private theorem fsr_lookup {G' : StackFrame} {x : Identifier} (hx : Reserved.res x.text) {v : Value}
    (hv : G'[x.text]? = some v) {y : EvalM PM α} {f : Value → EvalM PM β} {A : α → β → Prop} (k : Nat)
    (hk : FSH (Sm (E rt) Gl G') T U A y (f v)) :
    FSH (Sm (E rt) Gl G') T U A y (evalExpr cfg (k + 1) (.Var (.Local x)) >>= f) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have hs' : StRel G' (IxRel (E rt)) σ σ' := hs
  simp only [evalExpr, bind_assoc]
  rw [run_bind, run_get]
  simp only [lookup_ghost hs' hx hv, pure_bind]
  exact hk.sim σ σ' τ τ' hs ht hn

def Bnd (G : StackFrame) (n : String) : SimRel :=
  ⟨fun σ σ' => ∃ v, StRel (bindCatch G n v) (IxRel (E rt)) σ σ', EvRel (E rt), CtlOK Gl G, Reserved.retLabel,
    fun _ _ _ => False⟩

def Mix (G : StackFrame) (n : String) : SimRel :=
  ⟨fun σ σ' => StRel G (IxRel (E rt)) σ σ' ∨ ∃ v, StRel (bindCatch G n v) (IxRel (E rt)) σ σ',
    EvRel (E rt), CtlOK Gl G, Reserved.retLabel, fun _ _ _ => False⟩

private theorem trk (G : StackFrame) (k : String) : Tracked G k := ⟨fun h => h, fun h => h⟩

private theorem plainI (G : StackFrame) : Plain G := ⟨fun _ h => h, fun _ => rfl⟩

private theorem StRel.restack {G' : StackFrame} {σ σ' : EvalState} (h : StRel G' (IxRel (E rt)) σ σ') {f : StackFrame}
    (hs : SR G σ.globals σ.stack f) (hwf : WFG G) : StRel G (IxRel (E rt)) σ { σ' with stack := f } :=
  { h with stack := hs, wf := hwf, entR := h.entR.plain (plainI _) (plainI _) (fun _ => trivial) }

private theorem unwind_back {n : String} (hn : Reserved.res n) {σ σ' : EvalState} (hwf : WFG G)
    (h : StRel G (IxRel (E rt)) σ σ' ∨ ∃ v, StRel (bindCatch G n v) (IxRel (E rt)) σ σ') :
    StRel G (IxRel (E rt)) σ { σ' with stack := popShadowsTo σ'.stack n (shadowDepth G n) } := by
  rcases h with h | ⟨v, h⟩
  · have e : popShadowsTo σ'.stack n (shadowDepth G n) = σ'.stack := by
      unfold popShadowsTo
      exact popShadowsGo_stop (by rw [h.stack.shadowDepth_r hn (trk _ _)]; omega) _
    rw [e]
    exact h
  · exact StRel.restack h (h.stack.unwind_r hn hwf (trk _ _) (trk _ _)) hwf

private theorem fsr_wbs {stmts : List StmtExprMd} {n : String} (hd : blockDeclarations stmts = [n]) (hn : Reserved.res n)
    {x : EvalM PM α} {act : EvalM PM β} {A : α → β → Prop}
    (hact : FSH (Sm (E rt) Gl G) (Bnd (rt := rt) G n) (Mix (rt := rt) G n) A x act) :
    FS (Sm (E rt) Gl G) A x (withBlockScope stmts act) := by
  refine ⟨fun σ σ' τ τ' hs ht hno => ?_⟩
  have hs' : StRel G (IxRel (E rt)) σ σ' := hs
  have hdep : shadowDepth σ'.stack n = shadowDepth G n := hs'.stack.shadowDepth_r hn (trk _ _)
  unfold withBlockScope
  simp only [hd, List.isEmpty_cons, Bool.false_eq_true, ite_false]
  rw [run_bind, run_get]
  simp only [hs'.coroSelf', Option.isSome_none, Bool.false_eq_true, ite_false, List.map_cons, List.map_nil,
    List.foldl_cons, List.foldl_nil, hdep]
  have r0 := hact.sim σ σ' τ τ' hs ht hno
  rw [run_bind, run_tryCatch]
  rcases r : run x σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;> rw [r] at r0 <;>
    rcases r' : run act σ' τ' with e' | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;> rw [r'] at r0 <;>
    simp only [RR, ExRel, false_and] at r0
  all_goals try (first | exact r0 | exact RR.ofStuck r0 _)
  · obtain ⟨hsg, htr⟩ := r0
    obtain ⟨hcr, hok, hst⟩ := hsg.same (fun _ h => h)
    rcases CtlR.eq hcr with rfl | ⟨_, _, rfl, rfl⟩
    · dsimp only
      cases c
      case suspended => exact absurd hok id
      all_goals
        simp only [run_bind, run_modify, run_throw, RR, ExRel]
        exact ⟨.inl ⟨.inl rfl, hok, unwind_back hn hs'.wf hst⟩, htr⟩
    · simp only [run_bind, run_modify, run_throw, RR, ExRel]
      exact ⟨.inl ⟨.inr (.inr ⟨_, _, rfl, rfl⟩), hok, unwind_back hn hs'.wf hst⟩, htr⟩
  · obtain ⟨hab, ⟨v, hst⟩, htr⟩ := r0
    dsimp only
    simp only [run_bind, run_modify, run_pure, RR, ExRel]
    exact ⟨hab, unwind_back hn hs'.wf (.inr ⟨v, hst⟩), htr⟩

private theorem fsr_getR {G' : StackFrame} {x : EvalM PM α} {k : EvalState → EvalM PM β} {A : α → β → Prop}
    (hk : ∀ s', (∃ s, StRel G' (IxRel (E rt)) s s') → FSH (Sm (E rt) Gl G') T U A x (k s')) :
    FSH (Sm (E rt) Gl G') T U A x (get >>= k) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  rw [run_bind, run_get]
  exact (hk σ' ⟨σ, hs⟩).sim σ σ' τ τ' hs ht hn

set_option hygiene false in
macro "lookup_tac" : tactic => `(tactic| (
  refine fsr_getR (fun s' ⟨_, hs'⟩ => ?_)
  rw [lookup_ghost hs' hres hv]
  simp only [pure_bind]))

private theorem tvarField (k : Nat) (t : StmtExprMd) (f : Identifier) (src : FileRange) :
    evalExprMd cfg (k + 1) ⟨.Var (.Field t f), src⟩ = evalExpr cfg k (.Var (.Field t f)) :=
  jumpBoundary_noJ (noJ_varField cfg _ _ _)

private theorem pre_field (o : IncrDecrOp) {G' : StackFrame} {recv : Identifier} (hres : Reserved.res recv.text)
    {v : Value} (hv : G'[recv.text]? = some v) {fn fn' : Identifier} (hfn : fn.text = fn'.text)
    {s1 ts' src' : FileRange} (K : Nat) (hc : CfgB cfg) :
    FS (Sm (E rt) Gl G') Eq
      (do
        let old ← readField v fn.text
        let new ← liftM (evalOp cfg (if (o == IncrDecrOp.Incr) = true then Operation.Add else Operation.Sub)
          [old, Value.int ⟨1⟩])
        writeField v fn.text new
        pure new)
      (evalExprMd cfg (K + 9) (lowerIncrDecr .Pre o ⟨.Field ⟨.Var (.Local recv), s1⟩ fn', ts'⟩ src')) := by
  cases o
  all_goals
    simp only [evalExpr, -evalExpr.eq_5, tcall, tvar, tlit, tassign, tvarField, lowerIncrDecr, lowerToAssign,
      lowerOpAssign, targetAsRead, assignTarget, writeUpdate, List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind, not_coro,
      of_procName, hc.strict, strictField_none hc.strict, Bool.false_eq_true, ite_false, isPartialOp, opCall, bvCmpName, Option.bind_eq_bind,
      Option.bind_none]
    lookup_tac
    refine fsr_modify (fun σ σ' h => by strel h) ?_
    refine fsr_get (fun _ _ => ?_)
    lookup_tac
    refine fs_bind (fs_readField v fn.text fn'.text hfn) (fun old old' h => ?_)
    subst h
    simp (config := { decide := true }) only [ite_true, ite_false]
    refine fs_bind (fs_liftM (evalOp_pconst hc _ _)) (fun nw nw' h => ?_)
    subst h
    exact fs_bind (fs_writeField v fn.text fn'.text hfn nw) (fun _ _ _ => fs_pure rfl)

private theorem post_field (o : IncrDecrOp) {G' : StackFrame} {recv : Identifier} (hres : Reserved.res recv.text)
    {v : Value} (hv : G'[recv.text]? = some v) {fn fn' : Identifier} (hfn : fn.text = fn'.text)
    {s1 ts' src' : FileRange} (K : Nat) (hc : CfgB cfg) :
    FS (Sm (E rt) Gl G') Eq
      (do
        let old ← readField v fn.text
        let new ← liftM (evalOp cfg (if (o == IncrDecrOp.Incr) = true then Operation.Add else Operation.Sub)
          [old, Value.int ⟨1⟩])
        writeField v fn.text new
        pure old)
      (evalExprMd cfg (K + 11) (lowerIncrDecr .Post o ⟨.Field ⟨.Var (.Local recv), s1⟩ fn', ts'⟩ src')) := by
  cases o
  all_goals
    simp only [evalExpr, tcall, tvar, tlit, tassign, tvarField, lowerIncrDecr, lowerToAssign,
      lowerOpAssign, targetAsRead, assignTarget, writeUpdate, List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind, not_coro,
      of_procName, hc.strict, strictField_none hc.strict, Bool.false_eq_true, ite_false, isPartialOp, opCall, bvCmpName, Option.bind_eq_bind,
      Option.bind_none]
    refine fsr_modify (fun σ σ' h => by strel h) ?_
    refine fsr_get (fun _ _ => ?_)
    lookup_tac
    refine fsr_modify (fun σ σ' h => by strel h) ?_
    refine fsr_get (fun _ _ => ?_)
    lookup_tac
    refine fs_bind (fs_readField v fn.text fn'.text hfn) (fun old old' h => ?_)
    subst h
    simp (config := { decide := true }) only [ite_true, ite_false]
    refine fs_bind (fs_liftM_eq (evalOp_pconst hc _ _)) (fun nw nw' ⟨h, hX⟩ => ?_)
    subst h
    refine fs_bind (fs_writeField v fn.text fn'.text hfn nw) (fun _ _ _ => ?_)
    first
      | (have hi := inverse (o := .Incr) hX; simp only [subAdd] at hi; rw [hi]; exact fs_pure rfl)
      | (have hi := inverse (o := .Decr) hX; simp only [subAdd] at hi; rw [hi]; exact fs_pure rfl)

private theorem cmp_field {op : Operation} (hop : plainOp op = true) {G' : StackFrame} {recv : Identifier}
    (hres : Reserved.res recv.text) {v : Value} (hv : G'[recv.text]? = some v) {fn fn' : Identifier}
    (hfn : fn.text = fn'.text) {s1 ts' src' : FileRange} {R R' : StmtExprMd} {n K : Nat}
    (hR : FS (Sm (E rt) Gl G') Eq (evalExprMd cfg n R) (evalExprMd cfg (K + 4) R')) (hc : CfgB cfg) :
    FS (Sm (E rt) Gl G') Eq
      (do
        let old ← readField v fn.text
        let r ← evalExprMd cfg n R
        let new ← liftM (evalOp cfg op [old, r])
        writeField v fn.text new
        pure new)
      (evalExprMd cfg (K + 8) (lowerOpAssign op ⟨.Field ⟨.Var (.Local recv), s1⟩ fn', ts'⟩ R' src')) := by
  cases op <;> simp only [plainOp, Bool.false_eq_true] at hop
  all_goals
    simp only [evalExpr, tcall, tvar, tassign, tvarField, lowerOpAssign, targetAsRead, assignTarget, writeUpdate, List.mapM_cons,
      List.mapM_nil, bind_assoc, pure_bind, not_coro, of_procName, hc.strict, strictField_none hc.strict, Bool.false_eq_true, ite_false, isPartialOp,
      opCall, bvCmpName, Option.bind_eq_bind, Option.bind_none]
    lookup_tac
    refine fsr_modify (fun σ σ' h => by strel h) ?_
    refine fsr_get (fun _ _ => ?_)
    lookup_tac
    refine fs_bind (fs_readField v fn.text fn'.text hfn) (fun old old' h => ?_)
    subst h
    refine fs_bind hR (fun r r' h => ?_)
    subst h
    refine fs_bind (fs_liftM (evalOp_pconst hc _ _)) (fun nw nw' h => ?_)
    subst h
    exact fs_bind (fs_writeField v fn.text fn'.text hfn nw) (fun _ _ _ => fs_pure rfl)

private theorem cmp_field_div {op : Operation} (hop : op = .DivT ∨ op = .ModT) {G' : StackFrame} {recv : Identifier}
    (hres : Reserved.res recv.text) {v : Value} (hv : G'[recv.text]? = some v) {fn fn' : Identifier}
    (hfn : fn.text = fn'.text) {s1 ts' src' : FileRange} {R R' : StmtExprMd} {n K : Nat}
    (hR : FS (Sm (E rt) Gl G') Eq (evalExprMd cfg n R) (evalExprMd cfg (K + 4) R'))
    (hpre : ∀ args (site site' : FileRange) (P P' : Procedure), ProcRelB (E rt) P P' →
      FS (Sm (E rt) Gl G') Eq (checkPreconditions cfg n site P args) (checkPreconditions cfg (K + 4) site' P' args))
    (hc : CfgB cfg) :
    FS (Sm (E rt) Gl G') Eq
      (readField v fn.text >>= fun old => evalExprMd cfg n R >>= fun r => get >>= fun (st : EvalState) =>
        match divProc? st.index op old with
        | some P => checkPreconditions cfg n st.stmtSite P [old, r] >>= fun _ =>
            liftM (evalOp cfg op [old, r]) >>= fun new => writeField v fn.text new >>= fun _ => pure new
        | none => noFitPrelude st.index op [old, r] >>= fun _ =>
            liftM (evalOp cfg op [old, r]) >>= fun new => writeField v fn.text new >>= fun _ => pure new)
      (evalExprMd cfg (K + 8) (lowerOpAssign op ⟨.Field ⟨.Var (.Local recv), s1⟩ fn', ts'⟩ R' src')) := by
  rcases hop with rfl | rfl
  all_goals
    simp only [evalExpr, tcall, tvar, tassign, tvarField, lowerOpAssign, targetAsRead, assignTarget, writeUpdate, List.mapM_cons,
      List.mapM_nil, bind_assoc, pure_bind, not_coro, of_procName, hc.strict, strictField_none hc.strict, Bool.false_eq_true, isPartialOp,
      opCall, bvCmpName, Option.bind_eq_bind, Option.bind_none, ↓reduceIte]
    lookup_tac
    refine fsr_modify (fun σ σ' h => by strel h) ?_
    refine fsr_get (fun _ _ => ?_)
    lookup_tac
    refine fs_bind (fs_readField v fn.text fn'.text hfn) (fun old old' h => ?_)
    subst h
    refine fs_bind hR (fun r r' h => ?_)
    subst h
    refine fs_divPre (by simp) (hpre _) ?_
    refine fs_bind (fs_liftM (evalOp_pconst hc _ _)) (fun nw nw' h => ?_)
    subst h
    exact fs_bind (fs_writeField v fn.text fn'.text hfn nw) (fun _ _ _ => fs_pure rfl)

private theorem run_hostFail (msg : String) (σ : EvalState) (τ : Trace) :
    run (hostFail msg : EvalM PM α) σ τ = .error (.fail msg) := by
  rw [hostFail, run_lift]; rfl

private theorem readField_data_fails (c : String) (a : Array Value) (f : String) (σ : EvalState) (τ : Trace) :
    ∃ e, run (readField (.data c a) f : EvalM PM Value) σ τ = .error e := by
  simp only [readField, evalError, run_bind, run_get, run_hostFail]
  exact ⟨_, rfl⟩

private theorem pre_field_fails (hc : CfgB cfg) (o : IncrDecrOp) {recv : Identifier} {v : Value} (hab : IsAbsent v) {fn' : Identifier}
    {s1 ts' src' : FileRange} (K : Nat) :
    ∀ σ' τ', σ'.stack[recv.text]? = some v → ∃ m,
      run (evalExprMd cfg (K + 9) (lowerIncrDecr .Pre o ⟨.Field ⟨.Var (.Local recv), s1⟩ fn', ts'⟩ src')) σ' τ' =
        .error (.fail m) := by
  cases o
  all_goals
    simp only [evalExpr, tcall, tvar, tlit, tassign, tvarField, lowerIncrDecr, lowerToAssign,
      lowerOpAssign, targetAsRead, assignTarget, List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind, not_coro,
      of_procName, hc.strict, strictField_none hc.strict, Bool.false_eq_true, ite_false, isPartialOp, opCall, bvCmpName, Option.bind_eq_bind,
      Option.bind_none]
    intro σ' τ' hst
    obtain ⟨a, rfl⟩ := hab
    simp only [run_bind, run_modify, run_get]
    simp only [lookupVar, hst, HOrElse.hOrElse, OrElse.orElse, Option.orElse, run_pure, readField,
      evalError, run_bind, run_get, run_hostFail]
    exact ⟨_, rfl⟩

private theorem post_field_fails (hc : CfgB cfg) (o : IncrDecrOp) {recv : Identifier} {v : Value} (hab : IsAbsent v) {fn' : Identifier}
    {s1 ts' src' : FileRange} (K : Nat) :
    ∀ σ' τ', σ'.stack[recv.text]? = some v → ∃ m,
      run (evalExprMd cfg (K + 11) (lowerIncrDecr .Post o ⟨.Field ⟨.Var (.Local recv), s1⟩ fn', ts'⟩ src')) σ' τ' =
        .error (.fail m) := by
  cases o
  all_goals
    simp only [evalExpr, tcall, tvar, tlit, tassign, tvarField, lowerIncrDecr, lowerToAssign,
      lowerOpAssign, targetAsRead, assignTarget, List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind, not_coro,
      of_procName, hc.strict, strictField_none hc.strict, Bool.false_eq_true, ite_false, isPartialOp, opCall, bvCmpName, Option.bind_eq_bind,
      Option.bind_none]
    intro σ' τ' hst
    obtain ⟨a, rfl⟩ := hab
    simp only [run_bind, run_modify, run_get]
    simp only [lookupVar, hst, HOrElse.hOrElse, OrElse.orElse, Option.orElse, run_pure, readField,
      evalError, run_bind, run_get, run_hostFail]
    exact ⟨_, rfl⟩

private theorem cmp_field_fails (hc : CfgB cfg) {op : Operation} (hop : okOp op = true) {recv : Identifier} {v : Value}
    (hab : IsAbsent v) {fn' : Identifier} {s1 ts' src' : FileRange} {R' : StmtExprMd} (K : Nat) :
    ∀ σ' τ', σ'.stack[recv.text]? = some v → ∃ m,
      run (evalExprMd cfg (K + 8) (lowerOpAssign op ⟨.Field ⟨.Var (.Local recv), s1⟩ fn', ts'⟩ R' src')) σ' τ' =
        .error (.fail m) := by
  cases op <;> simp only [okOp, plainOp, Bool.false_eq_true] at hop
  all_goals
    simp only [evalExpr, tcall, tvar, tassign, tvarField, lowerOpAssign, targetAsRead, assignTarget, List.mapM_cons,
      List.mapM_nil, bind_assoc, pure_bind, not_coro, of_procName, hc.strict, strictField_none hc.strict, Bool.false_eq_true, isPartialOp,
      opCall, bvCmpName, Option.bind_eq_bind, Option.bind_none, ↓reduceIte]
    intro σ' τ' hst
    obtain ⟨a, rfl⟩ := hab
    simp only [run_bind, run_modify, run_get]
    simp only [lookupVar, hst, HOrElse.hOrElse, OrElse.orElse, Option.orElse, run_pure, readField,
      evalError, run_bind, run_get, run_hostFail]
    exact ⟨_, rfl⟩

private theorem src_fails {v : Value} (hab : IsAbsent v) (f : String) (k : Value → EvalM PM α) (σ : EvalState) (τ : Trace) :
    ∃ e, run (readField v f >>= k) σ τ = .error e := by
  obtain ⟨a, rfl⟩ := hab
  obtain ⟨e, he⟩ := readField_data_fails "$absent" a f σ τ
  rw [run_bind, he]
  exact ⟨e, rfl⟩

private theorem field_core {tg tg' : StmtExprMd} (hy : NotYield tg') {recv : Identifier} (hres : Reserved.res recv.text)
    (hnk : ∀ k, shadowKey k ≠ recv.text) {ty : Option HighTypeMd} {s1 : FileRange} {n M : Nat}
    {REST : Value → EvalM PM α} {Y : EvalM PM β} {A : α → β → Prop}
    (htg : FS (Sm (E rt) Gl G) Eq (evalExprMd cfg n tg) (evalExprMd cfg (M + 1) tg'))
    (hL : ∀ v, ¬ IsAbsent v →
      FSH (Sm (E rt) Gl (bindCatch G recv.text v)) (Bnd (rt := rt) G recv.text) (Mix (rt := rt) G recv.text) A
        (REST v) Y)
    (hFs : ∀ v, IsAbsent v → ∀ σ τ, ∃ e, run (REST v) σ τ = .error e)
    (hFt : ∀ v, IsAbsent v → ∀ σ' τ', σ'.operands = [] → σ'.stack[recv.text]? = some v →
      ∃ m, run Y σ' τ' = .error (.fail m)) :
    FSH (Sm (E rt) Gl G) (Bnd (rt := rt) G recv.text) (Mix (rt := rt) G recv.text) A
      (evalExprMd cfg n tg >>= REST)
      (evalStmt cfg (M + 2) ⟨.Assign [⟨.Declare ⟨recv, ty⟩, s1⟩] tg', s1⟩ >>= fun _ => Y) := by
  simp only [evalStmt, isStackPushTarget, List.any_cons, List.any_nil, isStackVar, Bool.or_false,
    Bool.false_eq_true, ite_false, assignTarget, writeUpdate, pure_bind]
  split
  · rename_i heq; simp [NotYield, heq] at hy
  simp only [bind_assoc]
  refine fs_bind (FSH.errU (U := Sm (E rt) Gl G) htg (fun _ _ h => .inl h) (fun _ h => h) (fun _ _ h => h)) (fun v v' h => ?_)
  subst h
  by_cases hab : IsAbsent v
  · refine fs_fail_both (fun σ' => σ'.operands = []) (fun _ _ h => (h : StRel G (IxRel (E rt)) _ _).ops')
      (hFs v hab) (fun σ' τ' hop => ?_)
    rw [run_bind, run_modify]
    exact hFt v hab _ τ' hop (by simp [declareLocal, bindCatch])
  · refine fsr_switch (G' := bindCatch G recv.text v) (fun σ σ' h => ?_) (hL v hab)
    exact StRel.restack h (h.stack.bind_r hres v (trk _ _) (trk _ _)) (h.wf.bind hnk hab)

private theorem fails_wow {s : StmtExprMd} {x : EvalM PM α} {σ : EvalState} {τ : Trace} (hop : σ.operands = [])
    (h : ∃ m, run x σ τ = .error (.fail m)) : ∃ m, run (withOperandWindow s x) σ τ = .error (.fail m) := by
  rw [run_wow_nil hop]
  exact h

private theorem fails_wowB {s : StmtExprMd} {x : EvalM PM α} {f : α → EvalM PM β} {σ : EvalState} {τ : Trace}
    (hop : σ.operands = []) (h : ∃ m, run (x >>= f) σ τ = .error (.fail m)) :
    ∃ m, run (withOperandWindow s x >>= f) σ τ = .error (.fail m) := by
  rw [run_bind, run_wow_nil hop, ← run_bind]
  exact h

private theorem bindCatch_self (f : StackFrame) (n : String) (v : Value) : (bindCatch f n v)[n]? = some v := by
  simp [bindCatch]

private theorem toBnd {n : String} {v : Value} {x : EvalM PM α} {y : EvalM PM β} {A : α → β → Prop}
    (h : FS (Sm (E rt) Gl (bindCatch G n v)) A x y) :
    FSH (Sm (E rt) Gl (bindCatch G n v)) (Bnd (rt := rt) G n) (Mix (rt := rt) G n) A x y := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have r := h.sim σ σ' τ τ' hs ht hn
  revert r
  rcases run x σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;> rcases run y σ' τ' with e' | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;>
    simp only [RR, ExRel, imp_self, false_and]
  · exact fun ⟨h1, h3⟩ => ⟨h1.mono rfl (fun _ h => CtlOK.none rfl h) (fun _ _ h => .inr ⟨v, h⟩)
      (fun _ _ _ h => (not_free_none rfl _ h.1).elim), h3⟩
  · exact fun ⟨h1, h2, h3⟩ => ⟨h1, ⟨v, h2⟩, h3⟩

private theorem field_pre_expr (o : IncrDecrOp) {tg tg' : StmtExprMd} (hy : NotYield tg') {fn fn' : Identifier}
    (hfn : fn.text = fn'.text) {recv : Identifier} (hres : Reserved.res recv.text)
    (hnk : ∀ k, shadowKey k ≠ recv.text) {ty : Option HighTypeMd} {s1 ts ts' src' : FileRange} {n K : Nat}
    (htg : FS (Sm (E rt) Gl G) Eq (evalExprMd cfg n tg) (evalExprMd cfg (K + 10) tg')) (hc : CfgB cfg) :
    FS (Sm (E rt) Gl G) Eq (evalExpr cfg (n + 2) (.IncrDecr .Pre o ⟨.Field tg fn, ts⟩))
      (evalExpr cfg (K + 13) (.Block [⟨.Assign [⟨.Declare ⟨recv, ty⟩, s1⟩] tg', s1⟩,
        lowerIncrDecr .Pre o ⟨.Field ⟨.Var (.Local recv), s1⟩ fn', ts'⟩ src'] none [] none)) := by
  have hd : blockDeclarations [⟨.Assign [⟨.Declare ⟨recv, ty⟩, s1⟩] tg', s1⟩,
      lowerIncrDecr .Pre o ⟨.Field ⟨.Var (.Local recv), s1⟩ fn', ts'⟩ src'] = [recv.text] := by
    cases o <;> rfl
  rw [show evalExpr cfg (K + 13) (.Block _ none [] none) = withBlockScope _ (evalStmtList cfg (K + 12) _ true) from rfl]
  refine fsr_wbs hd hres ?_
  simp only [evalExpr, readForUpdate, writeUpdate, bind_assoc, pure_bind]
  simp only [evalStmtList, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.forM_eq_forM, List.forM_cons, List.forM_nil, bind_assoc, pure_bind]
  refine fsr_get (fun st hco => ?_)
  simp (config := { decide := true }) only [hco, Option.isNone_none, ite_true]
  refine fsr_modify (fun σ σ' h => by strel h) ?_
  refine fs_wowRb ?_
  refine field_core hy hres hnk htg (fun v hab => ?_) (fun v hab σ τ => src_fails hab _ _ σ τ)
    (fun v hab σ' τ' hop hst => ?_)
  · refine fsr_modify (fun σ σ' h => by strel h) ?_
    refine fs_wowR ?_
    exact toBnd (pre_field o hres (bindCatch_self _ _ _) hfn (K + 2) hc)
  · rw [run_bind, run_modify]
    refine fails_wow hop ?_
    exact pre_field_fails hc o hab (K + 2) _ τ' (by simpa using hst)

private theorem field_post_expr (o : IncrDecrOp) {tg tg' : StmtExprMd} (hy : NotYield tg') {fn fn' : Identifier}
    (hfn : fn.text = fn'.text) {recv : Identifier} (hres : Reserved.res recv.text)
    (hnk : ∀ k, shadowKey k ≠ recv.text) {ty : Option HighTypeMd} {s1 ts ts' src' : FileRange} {n K : Nat}
    (htg : FS (Sm (E rt) Gl G) Eq (evalExprMd cfg n tg) (evalExprMd cfg (K + 10) tg')) (hc : CfgB cfg) :
    FS (Sm (E rt) Gl G) Eq (evalExpr cfg (n + 2) (.IncrDecr .Post o ⟨.Field tg fn, ts⟩))
      (evalExpr cfg (K + 13) (.Block [⟨.Assign [⟨.Declare ⟨recv, ty⟩, s1⟩] tg', s1⟩,
        lowerIncrDecr .Post o ⟨.Field ⟨.Var (.Local recv), s1⟩ fn', ts'⟩ src'] none [] none)) := by
  have hd : blockDeclarations [⟨.Assign [⟨.Declare ⟨recv, ty⟩, s1⟩] tg', s1⟩,
      lowerIncrDecr .Post o ⟨.Field ⟨.Var (.Local recv), s1⟩ fn', ts'⟩ src'] = [recv.text] := by
    cases o <;> rfl
  rw [show evalExpr cfg (K + 13) (.Block _ none [] none) = withBlockScope _ (evalStmtList cfg (K + 12) _ true) from rfl]
  refine fsr_wbs hd hres ?_
  simp only [evalExpr, readForUpdate, writeUpdate, bind_assoc, pure_bind]
  simp only [evalStmtList, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.forM_eq_forM, List.forM_cons, List.forM_nil, bind_assoc, pure_bind]
  refine fsr_get (fun st hco => ?_)
  simp (config := { decide := true }) only [hco, Option.isNone_none, ite_true]
  refine fsr_modify (fun σ σ' h => by strel h) ?_
  refine fs_wowRb ?_
  refine field_core hy hres hnk htg (fun v hab => ?_) (fun v hab σ τ => src_fails hab _ _ σ τ)
    (fun v hab σ' τ' hop hst => ?_)
  · refine fsr_modify (fun σ σ' h => by strel h) ?_
    refine fs_wowR ?_
    exact toBnd (post_field o hres (bindCatch_self _ _ _) hfn K hc)
  · rw [run_bind, run_modify]
    refine fails_wow hop ?_
    exact post_field_fails hc o hab K _ τ' (by simpa using hst)

private theorem field_cmp_expr {op : Operation} (hop : okOp op = true) {tg tg' : StmtExprMd} (hy : NotYield tg')
    {fn fn' : Identifier} (hfn : fn.text = fn'.text) {recv : Identifier} (hres : Reserved.res recv.text)
    (hnk : ∀ k, shadowKey k ≠ recv.text) {ty : Option HighTypeMd} {s1 ts ts' src' : FileRange} {R R' : StmtExprMd}
    {n K : Nat}
    (htg : FS (Sm (E rt) Gl G) Eq (evalExprMd cfg n tg) (evalExprMd cfg (K + 10) tg'))
    (hR : ∀ G', FS (Sm (E rt) Gl G') Eq (evalExprMd cfg (n + 1) R) (evalExprMd cfg (K + 7) R'))
    (hpre : ∀ G' args (site site' : FileRange) (P P' : Procedure), ProcRelB (E rt) P P' →
      FS (Sm (E rt) Gl G') Eq (checkPreconditions cfg (n + 1) site P args) (checkPreconditions cfg (K + 7) site' P' args))
    (hc : CfgB cfg) :
    FS (Sm (E rt) Gl G) Eq (evalExpr cfg (n + 2) (.CompoundAssign op ⟨.Field tg fn, ts⟩ R))
      (evalExpr cfg (K + 13) (.Block [⟨.Assign [⟨.Declare ⟨recv, ty⟩, s1⟩] tg', s1⟩,
        lowerOpAssign op ⟨.Field ⟨.Var (.Local recv), s1⟩ fn', ts'⟩ R' src'] none [] none)) := by
  have hd : blockDeclarations [⟨.Assign [⟨.Declare ⟨recv, ty⟩, s1⟩] tg', s1⟩,
      lowerOpAssign op ⟨.Field ⟨.Var (.Local recv), s1⟩ fn', ts'⟩ R' src'] = [recv.text] := rfl
  rw [show evalExpr cfg (K + 13) (.Block _ none [] none) = withBlockScope _ (evalStmtList cfg (K + 12) _ true) from rfl]
  refine fsr_wbs hd hres ?_
  cases op <;> simp only [okOp, plainOp, Bool.false_eq_true] at hop
  case DivT | ModT =>
    simp only [evalExpr, readForUpdate, writeUpdate, bind_assoc, pure_bind]
    simp only [evalStmtList, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.forM_eq_forM, List.forM_cons, List.forM_nil, bind_assoc, pure_bind]
    refine fsr_get (fun st hco => ?_)
    simp (config := { decide := true }) only [hco, Option.isNone_none, ite_true]
    refine fsr_modify (fun σ σ' h => by strel h) ?_
    refine fs_wowRb ?_
    refine field_core hy hres hnk htg (fun v hab => ?_) (fun v hab σ τ => src_fails hab _ _ σ τ)
      (fun v hab σ' τ' hop hst => ?_)
    · refine fsr_modify (fun σ σ' h => by strel h) ?_
      refine fs_wowR ?_
      exact toBnd (cmp_field_div (by simp) hres (bindCatch_self _ _ _) hfn (hR _) (hpre _) hc)
    · rw [run_bind, run_modify]
      refine fails_wow hop ?_
      exact cmp_field_fails hc (show okOp _ = true from rfl) hab (K + 3) _ τ' (by simpa using hst)
  all_goals
    simp only [evalExpr, readForUpdate, writeUpdate, bind_assoc, pure_bind]
    simp only [evalStmtList, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.forM_eq_forM, List.forM_cons, List.forM_nil, bind_assoc, pure_bind]
    refine fsr_get (fun st hco => ?_)
    simp (config := { decide := true }) only [hco, Option.isNone_none, ite_true]
    refine fsr_modify (fun σ σ' h => by strel h) ?_
    refine fs_wowRb ?_
    refine field_core hy hres hnk htg (fun v hab => ?_) (fun v hab σ τ => src_fails hab _ _ σ τ)
      (fun v hab σ' τ' hop hst => ?_)
    · refine fsr_modify (fun σ σ' h => by strel h) ?_
      refine fs_wowR ?_
      exact toBnd (cmp_field (show plainOp _ = true from rfl) hres (bindCatch_self _ _ _) hfn (hR _) hc)
    · rw [run_bind, run_modify]
      refine fails_wow hop ?_
      exact cmp_field_fails hc (show okOp _ = true from rfl) hab (K + 3) _ τ' (by simpa using hst)

private theorem fsr_charge {x : EvalM PM α} {k : Unit → EvalM PM β} {A : α → β → Prop}
    (hk : FSH (Sm (E rt) Gl G) T U A x (k ())) :
    FSH (Sm (E rt) Gl G) T U A x (chargeStep >>= k) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have hs' : StRel G (IxRel (E rt)) σ σ' := hs
  rw [run_bind, run_chargeStep hs'.steps']
  exact hk.sim σ σ' τ τ' hs ht hn

private theorem stmt_assign (k : Nat) (t : VariableMd) (v : StmtExprMd) (src : FileRange) (hv : NotYield v)
    (ht : isStackVar t = false) :
    evalStmt cfg (k + 1) ⟨.Assign [t] v, src⟩ = (evalExprMd cfg (k + 2) ⟨.Assign [t] v, src⟩ >>= fun _ => pure ()) := by
  have hnp : isStackPushTarget [t] = false := by simp [isStackPushTarget, ht]
  rcases v with ⟨vv, vs⟩
  cases vv
  case Yield => simp [NotYield] at hv
  all_goals rw [tassign]; simp [evalStmt, evalExpr, hnp]

private theorem stmt_incr (k : Nat) (m : IncrDecrMode) (o : IncrDecrOp) (t : VariableMd) (src : FileRange) :
    evalStmt cfg (k + 2) ⟨.IncrDecr m o t, src⟩ = (evalExpr cfg k (.IncrDecr m o t) >>= fun _ => pure ()) := by
  show (evalExprMd cfg (k + 1) ⟨.IncrDecr m o t, src⟩ >>= fun _ => pure ()) = _
  rw [show evalExprMd cfg (k + 1) ⟨.IncrDecr m o t, src⟩ = jumpBoundary (evalExpr cfg k (.IncrDecr m o t)) from rfl,
    jumpBoundary_noJ (noJ_incrDecr cfg _ _ _ _)]

private theorem stmt_cmp (k : Nat) (op : Operation) (t : VariableMd) (R : StmtExprMd) (src : FileRange) :
    evalStmt cfg (k + 2) ⟨.CompoundAssign op t R, src⟩ = (evalExpr cfg k (.CompoundAssign op t R) >>= fun _ => pure ()) := by
  show (evalExprMd cfg (k + 1) ⟨.CompoundAssign op t R, src⟩ >>= fun _ => pure ()) = _
  rw [show evalExprMd cfg (k + 1) ⟨.CompoundAssign op t R, src⟩ =
    jumpBoundary (evalExpr cfg k (.CompoundAssign op t R)) from rfl, jumpBoundary_noJ (noJ_compoundAssign cfg _ _ _ _)]

private theorem stmt_call (k : Nat) (c : Identifier) (args : List StmtExprMd) (ta : List HighTypeMd) (src : FileRange) :
    evalStmt cfg (k + 1) ⟨.Call none c args ta, src⟩ = (evalExprMd cfg k ⟨.Call none c args ta, src⟩ >>= fun _ => pure ()) :=
  rfl

private theorem fails_bind {x : EvalM PM α} {f : α → EvalM PM β} {σ : EvalState} {τ : Trace} (h : ∃ e, run x σ τ = .error e) :
    ∃ e, run (x >>= f) σ τ = .error e := by
  obtain ⟨e, he⟩ := h
  rw [run_bind, he]
  exact ⟨e, rfl⟩

private theorem fails_bindF {x : EvalM PM α} {f : α → EvalM PM β} {σ : EvalState} {τ : Trace}
    (h : ∃ m, run x σ τ = .error (.fail m)) : ∃ m, run (x >>= f) σ τ = .error (.fail m) := by
  obtain ⟨m, he⟩ := h
  rw [run_bind, he]
  exact ⟨m, rfl⟩

private theorem wbs_nil {l : List StmtExprMd} (hl : blockDeclarations l = []) (x : EvalM PM α) :
    withBlockScope l x = x := by
  unfold withBlockScope
  simp only [hl, List.isEmpty_nil, ite_true]

private theorem fs_then_r {S T U : SimRel} {x : EvalM PM α} {y : EvalM PM β} {A : α → β → Prop} {B : α → γ → Prop}
    {k : β → EvalM PM γ} (h : FSH S T U A x y) (hk : ∀ a b, A a b → FSH T T U B (pure a) (k b)) :
    FSH S T U B x (y >>= k) := by
  rw [← bind_pure x]
  exact fs_bind h hk

private theorem pre_stmt_eq (o : IncrDecrOp) (t : VariableMd) (src : FileRange) (k : Nat) (ht : isStackVar t = false) :
    evalStmt cfg (k + 1) (lowerIncrDecr .Pre o t src) =
      (evalExprMd cfg (k + 2) (lowerIncrDecr .Pre o t src) >>= fun _ => pure ()) := by
  cases o <;> exact stmt_assign _ _ _ _ (by simp [NotYield]) ht

private theorem cmp_stmt_eq (op : Operation) (t : VariableMd) (R : StmtExprMd) (src : FileRange) (k : Nat)
    (ht : isStackVar t = false) :
    evalStmt cfg (k + 1) (lowerOpAssign op t R src) =
      (evalExprMd cfg (k + 2) (lowerOpAssign op t R src) >>= fun _ => pure ()) :=
  stmt_assign _ _ _ _ (by simp [NotYield]) ht

private theorem post_stmt_eq (o : IncrDecrOp) (t : VariableMd) (src : FileRange) (k : Nat) :
    evalStmt cfg (k + 1) (lowerIncrDecr .Post o t src) =
      (evalExprMd cfg k (lowerIncrDecr .Post o t src) >>= fun _ => pure ()) := by
  cases o <;> rfl

private theorem field_pre_stmt (o : IncrDecrOp) {tg tg' : StmtExprMd} (hy : NotYield tg') {fn fn' : Identifier}
    (hfn : fn.text = fn'.text) {recv : Identifier} (hres : Reserved.res recv.text)
    (hnk : ∀ k, shadowKey k ≠ recv.text) {ty : Option HighTypeMd} {s1 ts ts' src src' : FileRange} {n K : Nat}
    (htg : FS (Sm (E rt) Gl G) Eq (evalExprMd cfg n tg) (evalExprMd cfg (K + 11) tg')) (hc : CfgB cfg) :
    FS (Sm (E rt) Gl G) Eq (evalStmt cfg (n + 4) ⟨.IncrDecr .Pre o ⟨.Field tg fn, ts⟩, src⟩)
      (evalStmt cfg (K + 14) ⟨.Block [⟨.Assign [⟨.Declare ⟨recv, ty⟩, s1⟩] tg', s1⟩,
        lowerIncrDecr .Pre o ⟨.Field ⟨.Var (.Local recv), s1⟩ fn', ts'⟩ src'] none [] none, src'⟩) := by
  have hd : blockDeclarations [⟨.Assign [⟨.Declare ⟨recv, ty⟩, s1⟩] tg', s1⟩,
      lowerIncrDecr .Pre o ⟨.Field ⟨.Var (.Local recv), s1⟩ fn', ts'⟩ src'] = [recv.text] := by
    cases o <;> rfl
  rw [show evalStmt cfg (n + 4) ⟨.IncrDecr .Pre o ⟨.Field tg fn, ts⟩, src⟩ =
    (evalExpr cfg (n + 2) (.IncrDecr .Pre o ⟨.Field tg fn, ts⟩) >>= fun _ => pure ()) from stmt_incr _ _ _ _ _]
  simp only [evalStmt]
  refine fsr_charge ?_
  refine fs_bind (A := fun _ _ => True) (fsr_wbs hd hres ?_) (fun _ _ _ => fs_pure rfl)
  simp only [evalExpr, readForUpdate, writeUpdate, bind_assoc, pure_bind]
  rw [evalStmtList_plain (by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact sl_assign _ _ _
    · first | exact (lowerIncrDecr_plain _ _ _ _).1 | exact (lowerOpAssign_plain _ _ _ _).1)]
  simp only [List.forM_eq_forM, List.forM_cons, List.forM_nil, bind_assoc, pure_bind, sa_assign,
    (lowerIncrDecr_plain _ _ _ _).2, ite_true]
  refine fsr_get (fun st hco => ?_)
  simp only [hco, Option.isNone_none, ite_true]
  refine fsr_modify (fun σ σ' h => by strel h) ?_
  refine fs_wowRb ?_
  refine field_core hy hres hnk htg (fun v hab => ?_) (fun v hab σ τ => src_fails hab _ _ σ τ)
    (fun v hab σ' τ' hop hst => ?_)
  · refine fsr_modify (fun σ σ' h => by strel h) ?_
    refine fs_wowRb ?_
    rw [pre_stmt_eq (t := ⟨.Field _ _, _⟩) (ht := rfl)]
    simp only [bind_assoc, pure_bind]
    exact fs_then_r (toBnd (pre_field o hres (bindCatch_self _ _ _) hfn (K + 4) hc)) (fun _ _ _ => fs_pure trivial)
  · rw [run_bind, run_modify]
    refine fails_wowB hop ?_
    rw [pre_stmt_eq (t := ⟨.Field _ _, _⟩) (ht := rfl)]
    simp only [bind_assoc]
    exact fails_bindF (pre_field_fails hc o hab (K + 4) _ τ' (by simpa using hst))

private theorem field_post_stmt (o : IncrDecrOp) {tg tg' : StmtExprMd} (hy : NotYield tg') {fn fn' : Identifier}
    (hfn : fn.text = fn'.text) {recv : Identifier} (hres : Reserved.res recv.text)
    (hnk : ∀ k, shadowKey k ≠ recv.text) {ty : Option HighTypeMd} {s1 ts ts' src src' : FileRange} {n K : Nat}
    (htg : FS (Sm (E rt) Gl G) Eq (evalExprMd cfg n tg) (evalExprMd cfg (K + 11) tg')) (hc : CfgB cfg) :
    FS (Sm (E rt) Gl G) Eq (evalStmt cfg (n + 4) ⟨.IncrDecr .Post o ⟨.Field tg fn, ts⟩, src⟩)
      (evalStmt cfg (K + 14) ⟨.Block [⟨.Assign [⟨.Declare ⟨recv, ty⟩, s1⟩] tg', s1⟩,
        lowerIncrDecr .Post o ⟨.Field ⟨.Var (.Local recv), s1⟩ fn', ts'⟩ src'] none [] none, src'⟩) := by
  have hd : blockDeclarations [⟨.Assign [⟨.Declare ⟨recv, ty⟩, s1⟩] tg', s1⟩,
      lowerIncrDecr .Post o ⟨.Field ⟨.Var (.Local recv), s1⟩ fn', ts'⟩ src'] = [recv.text] := by
    cases o <;> rfl
  rw [show evalStmt cfg (n + 4) ⟨.IncrDecr .Post o ⟨.Field tg fn, ts⟩, src⟩ =
    (evalExpr cfg (n + 2) (.IncrDecr .Post o ⟨.Field tg fn, ts⟩) >>= fun _ => pure ()) from stmt_incr _ _ _ _ _]
  simp only [evalStmt]
  refine fsr_charge ?_
  refine fs_bind (A := fun _ _ => True) (fsr_wbs hd hres ?_) (fun _ _ _ => fs_pure rfl)
  simp only [evalExpr, readForUpdate, writeUpdate, bind_assoc, pure_bind]
  rw [evalStmtList_plain (by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact sl_assign _ _ _
    · first | exact (lowerIncrDecr_plain _ _ _ _).1 | exact (lowerOpAssign_plain _ _ _ _).1)]
  simp only [List.forM_eq_forM, List.forM_cons, List.forM_nil, bind_assoc, pure_bind, sa_assign,
    (lowerIncrDecr_plain _ _ _ _).2, ite_true]
  refine fsr_get (fun st hco => ?_)
  simp only [hco, Option.isNone_none, ite_true]
  refine fsr_modify (fun σ σ' h => by strel h) ?_
  refine fs_wowRb ?_
  refine field_core hy hres hnk htg (fun v hab => ?_) (fun v hab σ τ => src_fails hab _ _ σ τ)
    (fun v hab σ' τ' hop hst => ?_)
  · refine fsr_modify (fun σ σ' h => by strel h) ?_
    refine fs_wowRb ?_
    rw [post_stmt_eq]
    simp only [bind_assoc, pure_bind]
    exact fs_then_r (toBnd (post_field o hres (bindCatch_self _ _ _) hfn K hc)) (fun _ _ _ => fs_pure trivial)
  · rw [run_bind, run_modify]
    refine fails_wowB hop ?_
    rw [post_stmt_eq]
    simp only [bind_assoc]
    exact fails_bindF (post_field_fails hc o hab K _ τ' (by simpa using hst))

private theorem field_cmp_stmt {op : Operation} (hop : okOp op = true) {tg tg' : StmtExprMd} (hy : NotYield tg')
    {fn fn' : Identifier} (hfn : fn.text = fn'.text) {recv : Identifier} (hres : Reserved.res recv.text)
    (hnk : ∀ k, shadowKey k ≠ recv.text) {ty : Option HighTypeMd} {s1 ts ts' src src' : FileRange}
    {R R' : StmtExprMd} {n K : Nat}
    (htg : FS (Sm (E rt) Gl G) Eq (evalExprMd cfg n tg) (evalExprMd cfg (K + 11) tg'))
    (hR : ∀ G', FS (Sm (E rt) Gl G') Eq (evalExprMd cfg (n + 1) R) (evalExprMd cfg (K + 9) R'))
    (hpre : ∀ G' args (site site' : FileRange) (P P' : Procedure), ProcRelB (E rt) P P' →
      FS (Sm (E rt) Gl G') Eq (checkPreconditions cfg (n + 1) site P args) (checkPreconditions cfg (K + 9) site' P' args))
    (hc : CfgB cfg) :
    FS (Sm (E rt) Gl G) Eq (evalStmt cfg (n + 4) ⟨.CompoundAssign op ⟨.Field tg fn, ts⟩ R, src⟩)
      (evalStmt cfg (K + 14) ⟨.Block [⟨.Assign [⟨.Declare ⟨recv, ty⟩, s1⟩] tg', s1⟩,
        lowerOpAssign op ⟨.Field ⟨.Var (.Local recv), s1⟩ fn', ts'⟩ R' src'] none [] none, src'⟩) := by
  have hd : blockDeclarations [⟨.Assign [⟨.Declare ⟨recv, ty⟩, s1⟩] tg', s1⟩,
      lowerOpAssign op ⟨.Field ⟨.Var (.Local recv), s1⟩ fn', ts'⟩ R' src'] = [recv.text] := rfl
  rw [show evalStmt cfg (n + 4) ⟨.CompoundAssign op ⟨.Field tg fn, ts⟩ R, src⟩ =
    (evalExpr cfg (n + 2) (.CompoundAssign op ⟨.Field tg fn, ts⟩ R) >>= fun _ => pure ()) from stmt_cmp _ _ _ _ _]
  simp only [evalStmt]
  refine fsr_charge ?_
  refine fs_bind (A := fun _ _ => True) (fsr_wbs hd hres ?_) (fun _ _ _ => fs_pure rfl)
  cases op <;> simp only [okOp, plainOp, Bool.false_eq_true] at hop
  case DivT | ModT =>
    simp only [evalExpr, readForUpdate, writeUpdate, bind_assoc, pure_bind]
    rw [evalStmtList_plain (by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact sl_assign _ _ _
      · first | exact (lowerIncrDecr_plain _ _ _ _).1 | exact (lowerOpAssign_plain _ _ _ _).1)]
    simp only [List.forM_eq_forM, List.forM_cons, List.forM_nil, bind_assoc, pure_bind, sa_assign,
      (lowerOpAssign_plain _ _ _ _).2, ite_true]
    refine fsr_get (fun st hco => ?_)
    simp only [hco, Option.isNone_none, ite_true]
    refine fsr_modify (fun σ σ' h => by strel h) ?_
    refine fs_wowRb ?_
    refine field_core hy hres hnk htg (fun v hab => ?_) (fun v hab σ τ => src_fails hab _ _ σ τ)
      (fun v hab σ' τ' hop hst => ?_)
    · refine fsr_modify (fun σ σ' h => by strel h) ?_
      refine fs_wowRb ?_
      rw [cmp_stmt_eq (t := ⟨.Field _ _, _⟩) (ht := rfl)]
      simp only [bind_assoc, pure_bind]
      exact fs_then_r (toBnd (cmp_field_div (by simp) hres (bindCatch_self _ _ _) hfn
          (hR _) (hpre _) hc)) (fun _ _ _ => fs_pure trivial)
    · rw [run_bind, run_modify]
      refine fails_wowB hop ?_
      rw [cmp_stmt_eq (t := ⟨.Field _ _, _⟩) (ht := rfl)]
      simp only [bind_assoc]
      exact fails_bindF (cmp_field_fails hc (show okOp _ = true from rfl) hab (K + 5) _ τ' (by simpa using hst))
  all_goals
    simp only [evalExpr, readForUpdate, writeUpdate, bind_assoc, pure_bind]
    rw [evalStmtList_plain (by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact sl_assign _ _ _
      · first | exact (lowerIncrDecr_plain _ _ _ _).1 | exact (lowerOpAssign_plain _ _ _ _).1)]
    simp only [List.forM_eq_forM, List.forM_cons, List.forM_nil, bind_assoc, pure_bind, sa_assign,
      (lowerOpAssign_plain _ _ _ _).2, ite_true]
    refine fsr_get (fun st hco => ?_)
    simp only [hco, Option.isNone_none, ite_true]
    refine fsr_modify (fun σ σ' h => by strel h) ?_
    refine fs_wowRb ?_
    refine field_core hy hres hnk htg (fun v hab => ?_) (fun v hab σ τ => src_fails hab _ _ σ τ)
      (fun v hab σ' τ' hop hst => ?_)
    · refine fsr_modify (fun σ σ' h => by strel h) ?_
      refine fs_wowRb ?_
      rw [cmp_stmt_eq (t := ⟨.Field _ _, _⟩) (ht := rfl)]
      simp only [bind_assoc, pure_bind]
      exact fs_then_r (toBnd (cmp_field (show plainOp _ = true from rfl) hres (bindCatch_self _ _ _) hfn
          (hR _) hc)) (fun _ _ _ => fs_pure trivial)
    · rw [run_bind, run_modify]
      refine fails_wowB hop ?_
      rw [cmp_stmt_eq (t := ⟨.Field _ _, _⟩) (ht := rfl)]
      simp only [bind_assoc]
      exact fails_bindF (cmp_field_fails hc (show okOp _ = true from rfl) hab (K + 5) _ τ' (by simpa using hst))

end Field

section Wire
variable {rt : StmtExprMd → Option Identifier}

def recvBlock (c : Nat) (ty : Option HighTypeMd) (tg' : StmtExprMd) (fn' : Identifier) (vs : FileRange)
    (lower : VariableMd → StmtExprMd) (src : FileRange) : StmtExprMd :=
  ⟨.Block [⟨.Assign [⟨.Declare ⟨mkId s!"$recv_{c}", ty⟩, tg'.source⟩] tg', tg'.source⟩,
    lower ⟨.Field ⟨.Var (.Local (mkId s!"$recv_{c}")), tg'.source⟩ fn', vs⟩] none [] none, src⟩

private theorem rw_incr_local (m : IncrDecrMode) (o : IncrDecrOp) (x : Identifier) (vs src : FileRange) (st : ElimState) :
    ((rewriteNode rt ⟨.IncrDecr m o ⟨.Local x, vs⟩, src⟩).run st).1 = lowerIncrDecr m o ⟨.Local x, vs⟩ src := rfl

private theorem rw_cmp_local (op : Operation) (x : Identifier) (R : StmtExprMd) (vs src : FileRange) (st : ElimState) :
    ((rewriteNode rt ⟨.CompoundAssign op ⟨.Local x, vs⟩ R, src⟩).run st).1 = lowerOpAssign op ⟨.Local x, vs⟩ R src := rfl

private theorem rw_incr_field (m : IncrDecrMode) (o : IncrDecrOp) (tg' : StmtExprMd) (fn' : Identifier) (vs src : FileRange)
    (st : ElimState) :
    ((rewriteNode rt ⟨.IncrDecr m o ⟨.Field tg' fn', vs⟩, src⟩).run st).1 =
      recvBlock st.freshCounter ((rt tg').map fun n => ⟨.UserDefined n, tg'.source⟩) tg' fn' vs
        (fun t => lowerIncrDecr m o t src) src := rfl

private theorem rw_cmp_field (op : Operation) (tg' : StmtExprMd) (fn' : Identifier) (R : StmtExprMd) (vs src : FileRange)
    (st : ElimState) :
    ((rewriteNode rt ⟨.CompoundAssign op ⟨.Field tg' fn', vs⟩ R, src⟩).run st).1 =
      recvBlock st.freshCounter ((rt tg').map fun n => ⟨.UserDefined n, tg'.source⟩) tg' fn' vs
        (fun t => lowerOpAssign op t R src) src := rfl

private theorem rw_cases {s t : StmtExprMd} (h : Rw rt s t) :
    (∃ m o x x' vs vs' src rsrc, s = ⟨.IncrDecr m o ⟨.Local x, vs⟩, src⟩ ∧
      t = lowerIncrDecr m o ⟨.Local x', vs'⟩ rsrc ∧ x.text = x'.text ∧ ¬ Reserved.res x.text) ∨
    (∃ op x x' vs vs' R R' src rsrc, s = ⟨.CompoundAssign op ⟨.Local x, vs⟩ R, src⟩ ∧
      t = lowerOpAssign op ⟨.Local x', vs'⟩ R' rsrc ∧ x.text = x'.text ∧ ¬ Reserved.res x.text ∧
      E rt R R' ∧ okOp op = true) ∨
    (∃ m o tg tg' fn fn' vs vs' src rsrc c ty, s = ⟨.IncrDecr m o ⟨.Field tg fn, vs⟩, src⟩ ∧
      t = recvBlock c ty tg' fn' vs' (fun t => lowerIncrDecr m o t rsrc) rsrc ∧ E rt tg tg' ∧ fn.text = fn'.text) ∨
    (∃ op tg tg' fn fn' vs vs' R R' src rsrc c ty, s = ⟨.CompoundAssign op ⟨.Field tg fn, vs⟩ R, src⟩ ∧
      t = recvBlock c ty tg' fn' vs' (fun t => lowerOpAssign op t R' rsrc) rsrc ∧ E rt tg tg' ∧ fn.text = fn'.text ∧
      E rt R R' ∧ okOp op = true) := by
  obtain ⟨r, st, hsh, rfl, hid, hk⟩ := h
  rcases s with ⟨sv, ssrc⟩
  rcases hk with ⟨m, o, v, hv⟩ | ⟨op, v, e, hv⟩ <;> dsimp only at hv <;> subst hv
  · cases hsh with
    | @incr _ _ v v' _ rsrc hvar _ =>
      rcases v with ⟨vv, vs⟩
      rcases v' with ⟨vv', vs'⟩
      cases vv <;> cases vv' <;> simp only [VarRel] at hvar
      · exact .inl ⟨m, o, _, _, vs, vs', ssrc, rsrc, rfl, rw_incr_local _ _ _ _ _ _, hvar.1, hvar.2⟩
      · exact .inr (.inr (.inl ⟨m, o, _, _, _, _, vs, vs', ssrc, rsrc, _, _, rfl, rw_incr_field _ _ _ _ _ _ _,
          hvar.1, hvar.2⟩))
      · exact absurd rfl (hid _)
    | unsup hu => simp [Unsup] at hu
  · cases hsh with
    | @compound _ v v' _ _ _ rsrc hvar _ he =>
      rcases v with ⟨vv, vs⟩
      rcases v' with ⟨vv', vs'⟩
      cases vv <;> cases vv' <;> simp only [VarRel] at hvar
      · exact .inr (.inl ⟨op, _, _, vs, vs', _, _, ssrc, rsrc, rfl, rw_cmp_local _ _ _ _ _ _, hvar.1, hvar.2,
          he, hid.2⟩)
      · exact .inr (.inr (.inr ⟨op, _, _, _, _, vs, vs', _, _, ssrc, rsrc, _, _, rfl, rw_cmp_field _ _ _ _ _ _ _,
          hvar.1, hvar.2, he, hid.2⟩))
      · exact absurd rfl (hid.1 _)
    | unsup hu => simp [Unsup] at hu

private theorem E_notYield {a a' : StmtExprMd} (h : E rt a a') : NotYield a' := by
  obtain ⟨⟨u, st, rfl⟩, hs⟩ := h
  refine trav_notYield rewriteNode_notYield u a st ?_
  have hb := hs.here.1
  unfold Basic at hb
  unfold NotYield
  split <;> simp_all

private theorem rewrite_lit_none (r : StmtExprMd) (st : ElimState)
    (h : (∃ m o v, r.val = .IncrDecr m o v) ∨ ∃ op v e, r.val = .CompoundAssign op v e) :
    literalValue? ((rewriteNode rt r).run st).1.val = none := by
  rcases r with ⟨rv, rsrc⟩
  rcases h with ⟨m, o, v, hv⟩ | ⟨op, v, e, hv⟩ <;> dsimp only at hv <;> subst hv <;> rcases v with ⟨vv, vs⟩ <;>
    cases vv
  all_goals first
    | (rw [rw_incr_local]; cases m <;> rfl)
    | (rw [rw_cmp_local]; rfl)
    | (rw [rw_incr_field]; rfl)
    | (rw [rw_cmp_field]; rfl)
    | (unfold rewriteNode withReceiverBound; cases m <;> rfl)
    | (unfold rewriteNode withReceiverBound; rfl)

private theorem id_trav_out {u : Bool} {w : StmtExprMd} {st : ElimState} (hw : Hered PID w) :
    ∃ r, Shape (E rt) w r ∧ (((mapStmtExprUsedM (fID rt) u w).run st).1 = r ∨
      (((∃ m o v, r.val = .IncrDecr m o v) ∨ ∃ op v e, r.val = .CompoundAssign op v e) ∧
        literalValue? ((mapStmtExprUsedM (fID rt) u w).run st).1.val = none)) := by
  obtain ⟨r, st1, heq, hsh⟩ := trav_shape (f := fID rt) (fun e he => he.1) (fun e he => he.2.1)
    rewriteNode_notYield u w st hw
  refine ⟨r, hsh, ?_⟩
  rw [heq]
  by_cases hk : (∃ m o v, r.val = .IncrDecr m o v) ∨ ∃ op v e, r.val = .CompoundAssign op v e
  · exact .inr ⟨hk, rewrite_lit_none r st1 hk⟩
  · left
    exact rewriteNode_other r st1 (fun m o v h => hk (.inl ⟨m, o, v, h⟩)) (fun o v e h => hk (.inr ⟨o, v, e, h⟩)) ▸ rfl

private theorem id_lit_iff {a a' : StmtExprMd} (h : E rt a a') :
    (∀ n, a.val = .LiteralInt n ↔ a'.val = .LiteralInt n) ∧
      (∀ d, a.val = .LiteralDecimal d ↔ a'.val = .LiteralDecimal d) := by
  obtain ⟨⟨u, st, rfl⟩, hw⟩ := h
  obtain ⟨r, hsh, hout | ⟨hk, hl⟩⟩ := id_trav_out (rt := rt) (u := u) (st := st) hw
  · rw [hout]
    cases hsh
    case unsup hu hu' =>
      exact ⟨fun n => ⟨fun h => by dsimp only at h; subst h; simp [Unsup] at hu,
          fun h => by dsimp only at h; subst h; simp [Unsup] at hu'⟩,
        fun d => ⟨fun h => by dsimp only at h; subst h; simp [Unsup] at hu,
          fun h => by dsimp only at h; subst h; simp [Unsup] at hu'⟩⟩
    all_goals simp_all
  · refine ⟨fun n => ⟨fun h => ?_, fun h => ?_⟩, fun d => ⟨fun h => ?_, fun h => ?_⟩⟩
    all_goals first
      | (rw [h] at hl; simp [literalValue?] at hl)
      | (rcases hk with ⟨m, o, v, hv⟩ | ⟨op, v, e, hv⟩ <;> cases hsh <;> simp_all [Unsup])

private theorem id_lit (w : StmtExprMd) (st : ElimState) (hw : Hered PID w) :
    literalValue? ((mapStmtExprM (rewriteNode rt) w).run st).1.val = literalValue? w.val := by
  obtain ⟨r, hsh, hout | ⟨hk, hl⟩⟩ := id_trav_out (rt := rt) (u := false) (st := st) hw
  · show literalValue? ((mapStmtExprUsedM (fID rt) false w).run st).1.val = _
    rw [hout]
    cases hsh with
    | @call f f' as as' ta ta' _ _ has hta hcr =>
      obtain ⟨rfl, -⟩ := hcr.resolve_right (fun h => h)
      rcases has with _ | ⟨ha, _ | ⟨hb, hr⟩⟩
      · rfl
      · rename_i a a'
        have ⟨hi, hd⟩ := id_lit_iff ha
        rcases a with ⟨av, asrc⟩
        rcases a' with ⟨av', asrc'⟩
        dsimp only at hi hd
        cases av <;> cases av' <;> first
          | rfl
          | (have e := (hi _).mp rfl; simp only [StmtExpr.LiteralInt.injEq] at e; subst e; rfl)
          | (have e := (hd _).mp rfl; simp only [StmtExpr.LiteralDecimal.injEq] at e; subst e; rfl)
          | simp_all
      · simp only [literalValue_two]
    | unsup hu hu' => rename_i v v' _ _; cases v <;> simp [Unsup] at hu <;> cases v' <;> simp [Unsup] at hu' <;> rfl
    | _ => rfl
  · show literalValue? ((mapStmtExprUsedM (fID rt) false w).run st).1.val = _
    rw [hl]
    rcases hk with ⟨m, o, v, hv⟩ | ⟨op, v, e, hv⟩ <;> cases hsh <;> simp_all [Unsup, literalValue?]

end Wire

section Step
variable {rt : StmtExprMd → Option Identifier} {G : StackFrame} {cfg : ExternalBackendM PM}
  (hc : CfgB cfg) {n : Nat} (ihs : ∀ k ≤ n, FundAt cfg (E rt) (Rw rt) 7 Gl k)

include hc ihs in
private theorem id_expr {s t : StmtExprMd} (hrw : Rw rt s t) (M : Nat) (hM : 7 * (n + 1) ≤ M) :
    FS (Sm (E rt) Gl G) Eq (evalExpr cfg (n + 1) s.val) (evalExpr cfg M t.val) := by
  rcases n with _ | n
  · rcases rw_cases hrw with ⟨m, o, x, x', vs, vs', src, rsrc, rfl, rfl, -⟩ | ⟨op, x, x', vs, vs', R, R', src, rsrc, rfl, rfl, -⟩ |
      ⟨m, o, tg, tg', fn, fn', vs, vs', src, rsrc, c, ty, rfl, rfl, -⟩ |
      ⟨op, tg, tg', fn, fn', vs, vs', R, R', src, rsrc, c, ty, rfl, rfl, -⟩ <;> exact fs_vac rfl
  rcases rw_cases hrw with ⟨m, o, x, x', vs, vs', src, rsrc, rfl, rfl, hx, hr⟩ |
    ⟨op, x, x', vs, vs', R, R', src, rsrc, rfl, rfl, hx, hr, hR, hop⟩ |
    ⟨m, o, tg, tg', fn, fn', vs, vs', src, rsrc, c, ty, rfl, rfl, htg, hfn⟩ |
    ⟨op, tg, tg', fn, fn', vs, vs', R, R', src, rsrc, c, ty, rfl, rfl, htg, hfn, hR, hop⟩
  · cases m
    · obtain ⟨M, rfl⟩ : ∃ k, M = k + 4 := ⟨M - 4, by omega⟩
      exact pre_local o hx hr hc (by omega)
    · obtain ⟨M, rfl⟩ : ∃ k, M = k + 6 := ⟨M - 6, by omega⟩
      exact post_local o hx hr hc (by omega)
  · obtain ⟨M, rfl⟩ : ∃ k, M = k + 4 := ⟨M - 4, by omega⟩
    exact cmp_local hop hx hr ((ihs (n + 1) (Nat.le_refl _)).exprMdT (fun _ _ => trivial) _ _ (closed _ _ hR) (ovOK_none rfl _ _) _ (by omega))
      (fun args site site' P P' hP => (ihs (n + 1) (Nat.le_refl _)).pre site site' P P' args hP (M + 1) (by omega)) hc (by omega)
  · obtain ⟨M, rfl⟩ : ∃ k, M = k + 13 := ⟨M - 13, by omega⟩
    have h1 := (ihs n (by omega)).exprMdT (fun _ _ => trivial) (G := G) _ _ (closed _ _ htg) (ovOK_none rfl _ _) (M + 10) (by omega)
    cases m
    · exact field_pre_expr o (E_notYield htg) hfn (fresh_res c) (fresh_not_shadow c) h1 hc
    · exact field_post_expr o (E_notYield htg) hfn (fresh_res c) (fresh_not_shadow c) h1 hc
  · obtain ⟨M, rfl⟩ : ∃ k, M = k + 13 := ⟨M - 13, by omega⟩
    have h1 := (ihs n (by omega)).exprMdT (fun _ _ => trivial) (G := G) _ _ (closed _ _ htg) (ovOK_none rfl _ _) (M + 10) (by omega)
    exact field_cmp_expr hop (E_notYield htg) hfn (fresh_res c) (fresh_not_shadow c) h1
      (fun G' => (ihs (n + 1) (Nat.le_refl _)).exprMdT (fun _ _ => trivial) (G := G') _ _ (closed _ _ hR) (ovOK_none rfl _ _) (M + 7) (by omega))
      (fun G' args site site' P P' hP => (ihs (n + 1) (Nat.le_refl _)).pre (G := G') site site' P P' args hP (M + 7) (by omega)) hc

include ihs in
private theorem id_exprMd {s t : StmtExprMd} (hrw : Rw rt s t) (M : Nat) (hM : 7 * (n + 1) ≤ M) :
    FS (Sm (E rt) Gl G) Eq (evalExprMd cfg (n + 1) s) (evalExprMd cfg M t) := by
  have hN : NR (E rt) (Rw rt) Gl s t := .inr hrw
  obtain ⟨M, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  have he := (ihs n (Nat.le_refl n)).exprT (fun _ _ => trivial) (G := G) _ _ hN (ovOK_none rfl _ _) M (by omega)
  rcases rw_cases hrw with ⟨m, o, x, x', vs, vs', src, rsrc, rfl, rfl, -⟩ | ⟨op, x, x', vs, vs', R, R', src, rsrc, rfl, rfl, -⟩ |
    ⟨m, o, tg, tg', fn, fn', vs, vs', src, rsrc, c, ty, rfl, rfl, -⟩ |
    ⟨op, tg, tg', fn, fn', vs, vs', R, R', src, rsrc, c, ty, rfl, rfl, -⟩
  · cases m <;> cases o
    all_goals first
      | exact fs_jumpBoundary he
      | exact fs_jumpBoundary (fsr_modify (fun σ σ' h => by strel h) he)
  · exact fs_jumpBoundary he
  · exact fs_jumpBoundary he
  · exact fs_jumpBoundary he

include ihs in
private theorem id_outputs {s t : StmtExprMd} (hrw : Rw rt s t) (M : Nat) (hM : 7 * (n + 1) ≤ M) :
    FS (Sm (E rt) Gl G) Eq (evalCallOutputs cfg (n + 1) s.val) (evalCallOutputs cfg M t.val) := by
  have hN : NR (E rt) (Rw rt) Gl s t := .inr hrw
  obtain ⟨M, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  have he := (ihs n (Nat.le_refl n)).exprT (fun _ _ => trivial) (G := G) _ _ hN (ovOK_none rfl _ _) M (by omega)
  rcases rw_cases hrw with ⟨m, o, x, x', vs, vs', src, rsrc, rfl, rfl, -⟩ | ⟨op, x, x', vs, vs', R, R', src, rsrc, rfl, rfl, -⟩ |
    ⟨m, o, tg, tg', fn, fn', vs, vs', src, rsrc, c, ty, rfl, rfl, -⟩ |
    ⟨op, tg, tg', fn, fn', vs, vs', R, R', src, rsrc, c, ty, rfl, rfl, -⟩
  all_goals (try (cases m <;> cases o))
  all_goals
    simp only [evalCallOutputs, lowerIncrDecr, lowerToAssign, lowerOpAssign, recvBlock, of_procName] at he ⊢
    exact fs_bind he (fun v v' hv => by subst hv; exact fs_pure rfl)

include ihs in
private theorem id_scoped {s t : StmtExprMd} (hrw : Rw rt s t) (M : Nat) (hM : 7 * (n + 1) ≤ M) :
    FS (Sm (E rt) Gl G) Eq (evalScopedStmt cfg (n + 1) s) (evalScopedStmt cfg M t) := by
  have hN : NR (E rt) (Rw rt) Gl s t := .inr hrw
  obtain ⟨M, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  have hst := (ihs n (Nat.le_refl n)).stmt (G := G) _ _ hN (ovOK_none rfl _ _) M (by omega)
  rcases rw_cases hrw with ⟨m, o, x, x', vs, vs', src, rsrc, rfl, rfl, -⟩ | ⟨op, x, x', vs, vs', R, R', src, rsrc, rfl, rfl, -⟩ |
    ⟨m, o, tg, tg', fn, fn', vs, vs', src, rsrc, c, ty, rfl, rfl, -⟩ |
    ⟨op, tg, tg', fn, fn', vs, vs', R, R', src, rsrc, c, ty, rfl, rfl, -⟩
  all_goals (try (cases m <;> cases o))
  all_goals
    simp only [evalScopedStmt, lowerIncrDecr, lowerToAssign, lowerOpAssign, recvBlock] at hst ⊢
    first
      | exact hst
      | (rw [wbs_nil rfl, wbs_nil rfl]; exact fs_wow hst)
      | (rw [wbs_nil rfl]; exact fs_wowL hst)
      | (rw [wbs_nil rfl]; exact fs_wow hst)

include hc ihs in
private theorem id_stmt {s t : StmtExprMd} (hrw : Rw rt s t) (M : Nat) (hM : 7 * (n + 1) ≤ M) :
    FS (Sm (E rt) Gl G) Eq (evalStmt cfg (n + 1) s) (evalStmt cfg M t) := by
  have hN : NR (E rt) (Rw rt) Gl s t := .inr hrw
  rcases n with _ | _ | _ | n
  all_goals (try (rcases rw_cases hrw with ⟨m, o, x, x', vs, vs', src, rsrc, rfl, rfl, -⟩ |
    ⟨op, x, x', vs, vs', R, R', src, rsrc, rfl, rfl, -⟩ | ⟨m, o, tg, tg', fn, fn', vs, vs', src, rsrc, c, ty, rfl, rfl, -⟩ |
    ⟨op, tg, tg', fn, fn', vs, vs', R, R', src, rsrc, c, ty, rfl, rfl, -⟩ <;> exact fs_vac rfl))
  obtain ⟨M, rfl⟩ : ∃ k, M = k + 14 := ⟨M - 14, by omega⟩
  rcases rw_cases hrw with ⟨m, o, x, x', vs, vs', src, rsrc, rfl, rfl, hx, hr⟩ |
    ⟨op, x, x', vs, vs', R, R', src, rsrc, rfl, rfl, hx, hr, hR, hop⟩ |
    ⟨m, o, tg, tg', fn, fn', vs, vs', src, rsrc, c, ty, rfl, rfl, htg, hfn⟩ |
    ⟨op, tg, tg', fn, fn', vs, vs', R, R', src, rsrc, c, ty, rfl, rfl, htg, hfn, hR, hop⟩
  · have he := (ihs (n + 2) (by omega)).exprT (fun _ _ => trivial) (G := G) _ _ hN (ovOK_none rfl _ _) (M + 12) (by omega)
    have he' := (ihs (n + 2) (by omega)).exprT (fun _ _ => trivial) (G := G) _ _ hN (ovOK_none rfl _ _) (M + 14) (by omega)
    rw [show evalStmt cfg (n + 4) ⟨.IncrDecr m o ⟨.Local x, vs⟩, src⟩ =
      (evalExpr cfg (n + 2) (.IncrDecr m o ⟨.Local x, vs⟩) >>= fun _ => pure ()) from stmt_incr _ _ _ _ _]
    cases m
    · rw [pre_stmt_eq (t := ⟨.Local _, _⟩) (ht := rfl)]
      exact fs_bind (fs_jumpBoundaryR (noJ_incrDecr cfg _ _ _ _) he') (fun _ _ _ => fs_pure rfl)
    · rw [post_stmt_eq]
      cases o
      all_goals
        simp only [lowerIncrDecr, tcall, bind_assoc] at he ⊢
        exact fsr_modify (fun σ σ' h => by strel h) (fs_bind he (fun _ _ _ => fs_pure rfl))
  · have he' := (ihs (n + 2) (by omega)).exprT (fun _ _ => trivial) (G := G) _ _ hN (ovOK_none rfl _ _) (M + 14) (by omega)
    rw [show evalStmt cfg (n + 4) ⟨.CompoundAssign op ⟨.Local x, vs⟩ R, src⟩ =
      (evalExpr cfg (n + 2) (.CompoundAssign op ⟨.Local x, vs⟩ R) >>= fun _ => pure ()) from stmt_cmp _ _ _ _ _, cmp_stmt_eq (t := ⟨.Local _, _⟩) (ht := rfl)]
    exact fs_bind (fs_jumpBoundaryR (noJ_compoundAssign cfg _ _ _ _) he') (fun _ _ _ => fs_pure rfl)
  · have h1 := (ihs n (by omega)).exprMdT (fun _ _ => trivial) (G := G) _ _ (closed _ _ htg) (ovOK_none rfl _ _) (M + 11) (by omega)
    cases m
    · exact field_pre_stmt o (E_notYield htg) hfn (fresh_res c) (fresh_not_shadow c) h1 hc
    · exact field_post_stmt o (E_notYield htg) hfn (fresh_res c) (fresh_not_shadow c) h1 hc
  · have h1 := (ihs n (by omega)).exprMdT (fun _ _ => trivial) (G := G) _ _ (closed _ _ htg) (ovOK_none rfl _ _) (M + 11) (by omega)
    exact field_cmp_stmt hop (E_notYield htg) hfn (fresh_res c) (fresh_not_shadow c) h1
      (fun G' => (ihs (n + 1) (by omega)).exprMdT (fun _ _ => trivial) (G := G') _ _ (closed _ _ hR) (ovOK_none rfl _ _) (M + 9) (by omega))
      (fun G' args site site' P P' hP => (ihs (n + 1) (by omega)).pre (G := G') site site' P P' args hP (M + 9) (by omega)) hc

end Step

private theorem id_decl {rt : StmtExprMd → Option Identifier} {s t : StmtExprMd} (hrw : Rw rt s t) :
    blockDeclarations [s] = blockDeclarations [t] := by
  rcases rw_cases hrw with ⟨m, o, x, x', vs, vs', src, rsrc, rfl, rfl, -⟩ | ⟨op, x, x', vs, vs', R, R', src, rsrc, rfl, rfl, -⟩ |
    ⟨m, o, tg, tg', fn, fn', vs, vs', src, rsrc, c, ty, rfl, rfl, -⟩ |
    ⟨op, tg, tg', fn, fn', vs, vs', R, R', src, rsrc, c, ty, rfl, rfl, -⟩
  all_goals (try (cases m <;> cases o))
  all_goals rfl

private theorem recvBlock_plain (c : Nat) (ty : Option HighTypeMd) (tg' : StmtExprMd) (fn' : Identifier)
    (vs : FileRange) (lower : VariableMd → StmtExprMd) (src : FileRange)
    (hl : ∀ t, statementLabels (lower t) = [] ∧ (stackAnnotation? (lower t)).isNone = true) :
    statementLabels (recvBlock c ty tg' fn' vs lower src) = [] ∧
      (stackAnnotation? (recvBlock c ty tg' fn' vs lower src)).isNone = true := by
  simp [recvBlock, statementLabels_block, sl_assign, (hl _).1, stackAnnotation?]

/-- A rewrite step of `EliminateIncrDecrAndCompoundAssign` holds no statement-position label and neither side is
a stack annotation. -/
private theorem id_rwLab {rt : StmtExprMd → Option Identifier} (s t : StmtExprMd) (hrw : Rw rt s t) :
    (∀ l, ¬ Reserved.resLabel l → l ∉ statementLabels s ∧ l ∉ statementLabels t) ∧
      (stackAnnotation? s).isNone = true ∧ (stackAnnotation? t).isNone = true := by
  rcases rw_cases hrw with ⟨m, o, x, x', vs, vs', src, rsrc, rfl, rfl, -⟩ | ⟨op, x, x', vs, vs', R, R', src, rsrc, rfl, rfl, -⟩ |
    ⟨m, o, tg, tg', fn, fn', vs, vs', src, rsrc, c, ty, rfl, rfl, -⟩ |
    ⟨op, tg, tg', fn, fn', vs, vs', R, R', src, rsrc, c, ty, rfl, rfl, -⟩
  · have := lowerIncrDecr_plain m o ⟨.Local x', vs'⟩ rsrc
    exact ⟨fun l _ => ⟨by rw [statementLabels_other _ _ (by intros; nofun) (by intros; nofun)]; simp,
      by rw [this.1]; simp⟩, by simp [stackAnnotation?], this.2⟩
  · have := lowerOpAssign_plain op ⟨.Local x', vs'⟩ R' rsrc
    exact ⟨fun l _ => ⟨by rw [statementLabels_other _ _ (by intros; nofun) (by intros; nofun)]; simp,
      by rw [this.1]; simp⟩, by simp [stackAnnotation?], this.2⟩
  · have := recvBlock_plain c ty tg' fn' vs' (fun t => lowerIncrDecr m o t rsrc) rsrc (fun t => lowerIncrDecr_plain m o t rsrc)
    exact ⟨fun l _ => ⟨by rw [statementLabels_other _ _ (by intros; nofun) (by intros; nofun)]; simp,
      by rw [this.1]; simp⟩, by simp [stackAnnotation?], this.2⟩
  · have := recvBlock_plain c ty tg' fn' vs' (fun t => lowerOpAssign op t R' rsrc) rsrc (fun t => lowerOpAssign_plain op t R' rsrc)
    exact ⟨fun l _ => ⟨by rw [statementLabels_other _ _ (by intros; nofun) (by intros; nofun)]; simp,
      by rw [this.1]; simp⟩, by simp [stackAnnotation?], this.2⟩

/-- Every pair of terms related by `E rt` holds the same statement-position labels. -/
private theorem id_labE {rt : StmtExprMd → Option Identifier} (s t : StmtExprMd) (h : E rt s t) (l : String)
    (hl : ¬ Reserved.resLabel l) : (l ∈ statementLabels s ↔ l ∈ statementLabels t) := by
  obtain ⟨⟨u, st, rfl⟩, hs⟩ := h
  refine (trav_labels (f := fID rt) (P := PID) (fun e he => he.1) (fun e he => he.2.1) rewriteNode_notYield
    (fun u r st l hl => ?_) (fun l hl a ts h => h.elim) l hl s u st hs).symm
  show l ∈ statementLabels ((rewriteNode rt r).run st).1 ↔ _
  by_cases hk : (∃ m o v, r.val = .IncrDecr m o v) ∨ ∃ o v e, r.val = .CompoundAssign o v e
  · have h1 := (rewriteNode_plain (rt := rt) r st hk).1
    have h2 : statementLabels r = [] := by
      rcases r with ⟨rv, rs⟩
      rcases hk with ⟨m, o, v, hv⟩ | ⟨o, v, e, hv⟩ <;> dsimp only at hv <;> subst hv <;>
        exact statementLabels_other _ _ (by intros; nofun) (by intros; nofun)
    rw [h1, h2]
  · have h1 : ∀ m o v, r.val ≠ .IncrDecr m o v := fun m o v h => hk (.inl ⟨m, o, v, h⟩)
    have h2 : ∀ o v e, r.val ≠ .CompoundAssign o v e := fun o v e h => hk (.inr ⟨o, v, e, h⟩)
    rw [rewriteNode_other r st h1 h2]

/-- `EliminateIncrDecrAndCompoundAssign`, for every receiver-type function `rt`, satisfies
`PassRel cfg (E rt) (Rw rt) 7 Gl` for every backend `cfg` that satisfies `CfgB`. -/
theorem id_rel {rt : StmtExprMd → Option Identifier} {cfg : ExternalBackendM PM} (hc : CfgB cfg) :
    PassRel cfg (E rt) (Rw rt) 7 Gl where
  K_pos := by omega
  cfg_ok := hc
  closed := closed
  decl := fun _ _ _ hrw => id_decl hrw
  declX := fun _ _ _ hrw => .ofEq (id_decl hrw)
  declOK := fun s t hrw x hx => by
    rcases rw_cases hrw with ⟨m, o, x, x', vs, vs', src, rsrc, rfl, -⟩ | ⟨op, x, x', vs, vs', R, R', src, rsrc, rfl, -⟩ |
      ⟨m, o, tg, tg', fn, fn', vs, vs', src, rsrc, c, ty, rfl, -⟩ |
      ⟨op, tg, tg', fn, fn', vs, vs', R, R', src, rsrc, c, ty, rfl, -⟩ <;> simp [blockDeclarations] at hx
  exDecl := fun _ _ _ h => h.elim
  exDeclOK := fun _ _ h => h.elim
  retV := fun h => absurd rfl h
  retHook := fun _ _ _ => trivial
  retPlain := fun _ _ => ⟨fun _ h => h, fun _ => rfl⟩
  retGl := fun _ h => by cases h
  retRes := fun _ h => by cases h
  glRes := fun _ _ h => h
  labE := fun s t h l hl => id_labE s t h l hl
  rwLab := fun s t hrw => id_rwLab s t hrw
  exLab := fun _ _ h => h.elim
  renAnn := fun _ _ h => h.elim
  retK := fun h => absurd rfl h
  retNG := fun h => absurd rfl h
  retVok := fun h => absurd rfl h
  renOp := fun _ _ h => (h : False).elim
  step := fun _ ihs => {
    scoped_ := fun _ _ hrw _ M hM => id_scoped ihs hrw M hM
    exprMd := fun _ _ hrw _ M hM => FS.vr (id_exprMd ihs hrw M hM)
    expr := fun _ _ hrw _ M hM => FS.vr (id_expr hc ihs hrw M hM)
    stmt := fun _ _ hrw _ M hM => id_stmt hc ihs hrw M hM
    outputs := fun _ _ hrw _ M hM => FS.vr (id_outputs ihs hrw M hM)
    exStmt := fun _ _ h => h.elim
    exLast := fun _ _ h => h.elim }

private theorem pass_eq (p : LaurelProgram) (rt : StmtExprMd → Option Identifier) :
    eliminateIncrDecrAndCompoundAssign (.Unordered p) rt =
      .Unordered ((mapLaurelProgramStmtExprM (rewriteNode rt) p).run {}).1 := rfl

private theorem id_hc (r : StmtExprMd) (st : ElimState) :
    ((rewriteNode rt r).run st).1 = r ∨ NodeRw r ((rewriteNode rt r).run st).1 := by
  rcases r with ⟨v, s⟩
  unfold rewriteNode
  split
  · rename_i m o t heq
    dsimp only at heq
    subst heq
    right
    refine ⟨(fun _ _ h => by simp at h), rfl, (fun _ _ h => ?_), ?_⟩ <;> (try unfold withReceiverBound at *) <;>
      (try split at h) <;> (try split) <;> (try cases m) <;>
      simp_all [lowerIncrDecr, lowerToAssign, lowerOpAssign, freshReceiver, StateT.run, bind, StateT.bind,
        modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, StmtExprMd.isWildcard]
  · rename_i o t e heq
    dsimp only at heq
    subst heq
    right
    refine ⟨(fun _ _ h => by simp at h), rfl, (fun _ _ h => ?_), ?_⟩ <;> (try unfold withReceiverBound at *) <;>
      (try split at h) <;> (try split) <;>
      simp_all [lowerOpAssign, freshReceiver, StateT.run, bind, StateT.bind,
        modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, StmtExprMd.isWildcard]
  · left; rfl

private theorem id_trav : TravOK (rewriteNode rt) := travOK_mk id_hc

def DivDecls (p : LaurelProgram) : Prop :=
  ∀ op : Operation, (op = .DivT ∨ op = .ModT) →
    ((p.staticFunctions ++ p.staticProcedures).filter (fun pr => pr.name.text == op.procName)).length ≤ 1

private theorem liftCoroutineYields_name (pr : Procedure) : (liftCoroutineYields pr).name = pr.name := by
  unfold liftCoroutineYields
  split <;> rfl

private theorem foldl_named (L : List Procedure) (acc : Std.HashMap String (List Procedure)) (k : String) :
    ((L.foldl (fun acc pr => acc.insert pr.name.text ((acc.getD pr.name.text []) ++ [pr])) acc)[k]?.getD []) =
      (acc[k]?.getD []) ++ L.filter (fun pr => pr.name.text == k) := by
  induction L generalizing acc with
  | nil => simp
  | cons pr L ih =>
    simp only [List.foldl_cons, ih, Std.HashMap.getElem?_insert, List.filter_cons]
    by_cases h : pr.name.text = k
    · subst h; simp [Std.HashMap.getD_eq_getD_getElem?]
    · simp [h]

private theorem foldl_procs (L : List Procedure) (acc : Std.HashMap String Procedure) (k : String) :
    (L.foldl (fun acc pr => acc.insert pr.name.text pr) acc)[k]? =
      ((L.filter (fun pr => pr.name.text == k)).getLast? <|> acc[k]?) := by
  induction L generalizing acc with
  | nil => simp
  | cons pr L ih =>
    simp only [List.foldl_cons, ih, Std.HashMap.getElem?_insert, List.filter_cons]
    by_cases h : pr.name.text = k
    · subst h
      cases hl : (L.filter (fun q => q.name.text == pr.name.text)).getLast? with
      | none =>
        simp_all only [Option.orElse_eq_orElse, Option.orElse_eq_or, Option.none_or, List.getLast?_filter, List.find?_eq_none, List.mem_reverse, beq_iff_eq, BEq.rfl, ↓reduceIte, Option.or_some, Option.getD_none, List.getLast?_cons, Option.some_or, Option.some.injEq]
        rw [List.find?_eq_none.2 (fun x hx => by simpa using hl x (List.mem_reverse.1 hx))]
        rfl
      | some x => simp_all [List.getLast?_cons]
    · simp [h]

private theorem ixX_of {E : StmtExprMd → StmtExprMd → Prop} {ix ix' : ProgramIndex} (h : DivX ix) :
    Reserved.ixX E ix ix' := h

private theorem buildIndex_divX {p : LaurelProgram} (h : DivDecls p) : DivX (buildIndex p) := by
  intro op hop
  have hn : (buildIndex p).procsNamed = ((p.staticFunctions ++ p.staticProcedures).map fun pr =>
      if pr.is_coroutine then liftCoroutineYields pr else pr).foldl
        (fun acc pr => acc.insert pr.name.text ((acc.getD pr.name.text []) ++ [pr])) {} := rfl
  have hp : (buildIndex p).procs = ((p.staticFunctions ++ p.staticProcedures).map fun pr =>
      if pr.is_coroutine then liftCoroutineYields pr else pr).foldl (fun acc pr => acc.insert pr.name.text pr) {} := rfl
  rw [hn, hp, foldl_named, foldl_procs]
  generalize hL : (p.staticFunctions ++ p.staticProcedures) = L
  have hlen := h op hop
  rw [hL] at hlen
  have hfm : (L.map fun pr => if pr.is_coroutine then liftCoroutineYields pr else pr).filter
      (fun pr => pr.name.text == op.procName) =
      (L.filter (fun pr => pr.name.text == op.procName)).map
        (fun pr => if pr.is_coroutine then liftCoroutineYields pr else pr) := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro x _
    simp only [Function.comp]
    split <;> simp [liftCoroutineYields_name]
  rw [hfm]
  generalize L.filter (fun pr => pr.name.text == op.procName) = l at hlen ⊢
  match l, hlen with
  | [], _ => simp
  | [_], _ => simp
  | _ :: _ :: _, hl => simp at hl

private theorem id_progRel {rt : StmtExprMd → Option Identifier} {p : LaurelProgram} (hp : ProgOK (Hered PID) p)
    (hdiv : DivDecls p) : ProgRel (E rt) p ((mapLaurelProgramStmtExprM (rewriteNode rt) p).run {}).1 :=
  prog_trav_ix id_trav (fun _ _ _ => trivial) rfl rfl (fun _ _ => trivial) id
    (fun _ _ h => (h : False).elim) hp (ixX_of (buildIndex_divX hdiv)) id_lit

/-- `mapLaurelProgramStmtExprM (rewriteNode rt)` preserves a whole-program run of any program satisfying
`ProgOK (Hered PID)` that declares `$divT` and `$modT` at most once each (`DivDecls`): running the
rewritten program with 7 times the fuel gives an `ERel`-related result to running the input, unless
the input gets stuck or runs out of fuel. The backend satisfies `CfgB`, neither run uses a step
budget, both use the same entry procedure and `printAsserts`, and the traces are related. -/
private theorem eliminateIncrDecr_correct {rt : StmtExprMd → Option Identifier} {cfg : ExternalBackendM PM}
    (hc : CfgB cfg) {p : LaurelProgram} (hp : ProgOK (Hered PID) p) (hdiv : DivDecls p) {o o' : Options} {n : Nat}
    (hn : o.fuel = n) (hM : 7 * n ≤ o'.fuel) (he : o.entryProcedure = o'.entryProcedure)
    (hl : o.limitSteps = false) (hl' : o'.limitSteps = false) (hq : o.printAsserts = o'.printAsserts)
    {τ τ' : Trace} (ht : TrRel (Sm (E rt) Gl {}) τ τ') (hnf : NotOOFEntry (runEntry cfg o p τ)) :
    ERel (Sm (E rt) Gl {}) (runEntry cfg o p τ)
      (runEntry cfg o' ((mapLaurelProgramStmtExprM (rewriteNode rt) p).run {}).1 τ') :=
  entry_sim (id_rel hc) (id_progRel hp hdiv) hn hM he hl hl' hq (fun h => h)
    (fun h => absurd rfl h) (fun h => absurd rfl h) (fun _ _ => valued_none rfl _) ht hnf

private theorem eliminateIncrDecr_procAt {rt : StmtExprMd → Option Identifier} {cfg : ExternalBackendM PM}
    (hc : CfgB cfg) {p : LaurelProgram} (hp : ProgOK (Hered PID) p) (hdiv : DivDecls p) {o o' : Options} {n : Nat}
    (hn : o.fuel = n + 1) (hM : 7 * (n + 1) ≤ o'.fuel)
    (hl : o.limitSteps = false) (hl' : o'.limitSteps = false) (hq : o.printAsserts = o'.printAsserts)
    {P : Procedure} (hPm : P ∈ p.staticProcedures) :
    ∃ P' ∈ ((mapLaurelProgramStmtExprM (rewriteNode rt) p).run {}).1.staticProcedures, ∀ τ τ', TrRel (Sm (E rt) Gl {}) τ τ' → NotOOFEntry (runProcAt cfg o p P τ) →
      ERel (Sm (E rt) Gl {}) (runProcAt cfg o p P τ) (runProcAt cfg o' ((mapLaurelProgramStmtExprM (rewriteNode rt) p).run {}).1 P' τ') :=
  procAt_all (id_rel hc) (id_progRel hp hdiv) hn hM hl hl' hq rfl hPm

private theorem pass_out {opts : LaurelTranslateOptions} {p q : LaurelProgram} {m : SemanticModel} {d : List Message}
    {st : Statistics} (hrun : eliminateIncrDecrAndCompoundAssignPass.run opts (.Unordered p) m = (.Unordered q, d, st)) :
    q = ((mapLaurelProgramStmtExprM (rewriteNode (receiverBaseType (.Unordered p) m)) p).run {}).1 := by
  have h0 : eliminateIncrDecrAndCompoundAssignPass.run opts (.Unordered p) m =
      (eliminateIncrDecrAndCompoundAssign (.Unordered p) (receiverBaseType (.Unordered p) m), [], {}) := rfl
  rw [h0, pass_eq] at hrun
  simp only [Prod.mk.injEq, Program.Unordered.injEq] at hrun
  exact hrun.1.symm

/-- `EliminateIncrDecrAndCompoundAssign` preserves a whole-program run: for any program whose
compound operators are among `okOp` (every operator the bytecode front end emits) and that declares
`$divT` and `$modT` at most once, running the pass's output with 7 times the fuel ends with the same
outcome and the same number of failed checks as running the input, unless the input gets stuck. The interpreter runs without a step budget (`limitSteps = false`): with the budget on, the
output can need more steps than any constant multiple of the input's, because each lowered field
compound assignment enters a block. -/
theorem eliminateIncrDecrAndCompoundAssignPass_correct {cfg : ExternalBackendM PM} (hc : CfgB cfg)
    (opts : LaurelTranslateOptions) {p q : LaurelProgram} {m : SemanticModel} {d : List Message} {st : Statistics}
    (hrun : eliminateIncrDecrAndCompoundAssignPass.run opts (.Unordered p) m = (.Unordered q, d, st))
    (hp : ProgOK (Hered PID) p) (hdiv : DivDecls p) {o o' : Options} {n : Nat}
    (hn : o.fuel = n) (hM : 7 * n ≤ o'.fuel) (he : o.entryProcedure = o'.entryProcedure)
    (hl : o.limitSteps = false) (hl' : o'.limitSteps = false) (hq : o.printAsserts = o'.printAsserts)
    {τ τ' : Trace} (ht : TrRel (Sm (E (receiverBaseType (.Unordered p) m)) Gl {}) τ τ')
    (hnf : NotOOFEntry (runEntry cfg o p τ)) :
    ERel (Sm (E (receiverBaseType (.Unordered p) m)) Gl {}) (runEntry cfg o p τ) (runEntry cfg o' q τ') := by
  rw [pass_out hrun]
  exact eliminateIncrDecr_correct hc hp hdiv hn hM he hl hl' hq ht hnf

/-- `EliminateIncrDecrAndCompoundAssign` preserves a run started at any static procedure: for any
program whose compound operators are among `okOp` and that declares `$divT` and `$modT` at most
once, running the pass's output from that procedure with 7 times the fuel ends with the same
outcome and the same number of failed checks as running the input from it, unless the input gets
stuck. The interpreter runs without a step budget (`limitSteps = false`). -/
theorem eliminateIncrDecrAndCompoundAssignPass_procAt {cfg : ExternalBackendM PM} (hc : CfgB cfg)
    (opts : LaurelTranslateOptions) {p q : LaurelProgram} {m : SemanticModel} {d : List Message} {st : Statistics}
    (hrun : eliminateIncrDecrAndCompoundAssignPass.run opts (.Unordered p) m = (.Unordered q, d, st))
    (hp : ProgOK (Hered PID) p) (hdiv : DivDecls p) {o o' : Options} {n : Nat}
    (hn : o.fuel = n + 1) (hM : 7 * (n + 1) ≤ o'.fuel)
    (hl : o.limitSteps = false) (hl' : o'.limitSteps = false) (hq : o.printAsserts = o'.printAsserts)
    {P : Procedure} (hPm : P ∈ p.staticProcedures) :
    ∃ P' ∈ q.staticProcedures, ∀ τ τ', TrRel (Sm (E (receiverBaseType (.Unordered p) m)) Gl {}) τ τ' →
      NotOOFEntry (runProcAt cfg o p P τ) →
      ERel (Sm (E (receiverBaseType (.Unordered p) m)) Gl {}) (runProcAt cfg o p P τ) (runProcAt cfg o' q P' τ') := by
  rw [pass_out hrun]
  exact eliminateIncrDecr_procAt hc hp hdiv hn hM hl hl' hq hPm

end Strata.Laurel.PassSemantics.IncrDecrSim
