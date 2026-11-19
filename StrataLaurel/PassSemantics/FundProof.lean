/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.PassSemantics.Wrap

/-!
# The fundamental simulation theorem

`fund` says that the interpreter run on a source term with fuel `n` is simulated (`FS`) by
the run on a related target term with fuel `M`, for every `M ≥ K * n`. It holds for each
of the interpreter's mutual functions. Terms are related by `NR`: they have the same shape,
or the pass rewrote one into the other (`Rw`). The proof is one induction on `n`; each
`fstep_*` lemma handles one interpreter function.

* `PassRel cfg E Rw K Gl`: what a pass must provide. `E` is closed under `NR`, the backend
  satisfies `CfgB`, declarations are preserved, and each rewrite step simulates (`RwStep`)
  given `FundAt` for all smaller fuel.
* `NR E Rw Gl s t`: `Shape E s t` with allowed exits (`ExitOK`) and related value children
  (`ValKids`), or `Rw s t`.
* `FundAt cfg E Rw K Gl n`: the simulation statement for fuel `n`, one field per
  interpreter function, including those that run a statement list from the labelled block a
  jump lands in (`runFrom`, `stmtFrom`, `blockFrom`) and that restart a labelled block
  (`blockLoop`).
* `LandRel`: the relation between the jump a source statement list catches and the one its
  target catches.
* `fund_le`, `fund`: `FundAt` holds for every `n`.
-/

namespace Strata.Laurel.PassSemantics

open Strata.Laurel
open Strata.Laurel.Interpreter

def UTRel [Reserved] : UpdateTarget → UpdateTarget → Prop
  | .local n, .local n' => n.text = n'.text ∧ ¬ Reserved.res n.text ∧ NotV n.text
  | .field v f, .field v' f' => v = v' ∧ f = f'
  | .declare n, .declare n' => n = n' ∧ ¬ Reserved.res n ∧ NotV n
  | _, _ => False

def UpdRel [Reserved] (a b : Value × UpdateTarget) : Prop := a.1 = b.1 ∧ UTRel a.2 b.2

def OkOpt [Reserved] (Gl : String → Prop) (G : StackFrame) : Option Control → Option Control → Prop
  | none, none => True
  | some c, some c' => CtlR Reserved.retLabel c c' ∧ CtlOK Gl G c
  | _, _ => False

section
variable [Reserved] (cfg : ExternalBackendM PM) (E Rw : StmtExprMd → StmtExprMd → Prop) (K : Nat)
  (Gl : String → Prop)

def ExitOK (s : StmtExprMd) : Prop := ∀ l d, s.val = .Goto l d → Gl l

def NR (s t : StmtExprMd) : Prop := (Shape E s t ∧ ExitOK Gl s ∧ ValKids E s t) ∨ Rw s t

def OvV (G : StackFrame) (v : Variable) : Prop := ∀ c ∈ variableChildren v, OvOK G c

def OvO (G : StackFrame) (f : Option StmtExprMd) : Prop := ∀ x, f = some x → OvOK G x

def OvC (G : StackFrame) (c : CatchClause) : Prop := OvO G c.predicate ∧ OvOK G c.body

structure FundAt (n : Nat) : Prop where
  scoped_ : ∀ {G : StackFrame} s t, NR E Rw Gl s t → OvOK G s → ∀ M, K * n ≤ M →
    FS (Sm E Gl G) Eq (evalScopedStmt cfg n s) (evalScopedStmt cfg M t)
  exprMd : ∀ {G : StackFrame} s t, NR E Rw Gl s t → OvOK G s → ∀ M, K * n ≤ M →
    FS (Sm E Gl G) (VRel (Reserved.vok E s t)) (evalExprMd cfg n s) (evalExprMd cfg M t)
  expr : ∀ {G : StackFrame} s t, NR E Rw Gl s t → OvOK G s → ∀ M, K * n ≤ M →
    FS (Sm E Gl G) (VRel (Reserved.vok E s t)) (evalExpr cfg n s.val) (evalExpr cfg M t.val)
  stmt : ∀ {G : StackFrame} s t, NR E Rw Gl s t → OvOK G s → ∀ M, K * n ≤ M →
    FS (Sm E Gl G) Eq (evalStmt cfg n s) (evalStmt cfg M t)
  outputs : ∀ {G : StackFrame} s t, NR E Rw Gl s t → OvOK G s → ∀ M, K * n ≤ M →
    FS (Sm E Gl G) (VRel (Reserved.vok E s t)) (evalCallOutputs cfg n s.val) (evalCallOutputs cfg M t.val)
  assign : ∀ {G : StackFrame} v v', VarRel E v v' → VV E v v' → WOK v → OvV G v → ∀ M, K * n ≤ M →
    FS (Sm E Gl G) UTRel (assignTarget cfg n v) (assignTarget cfg M v')
  update : ∀ {G : StackFrame} v v', VarRel E v v' → VV E v v' → WOK v → OvV G v →
    (∀ a, v = .Local a → Reserved.nodeOK G ⟨.Var (.Local a), .unknown⟩) → ∀ M, K * n ≤ M →
    FS (Sm E Gl G) UpdRel (readForUpdate cfg n v) (readForUpdate cfg M v')
  iter : ∀ {G : StackFrame} c c' b b' p ci ci' eb eb', E c c' → Reserved.vok E c c' → E b b' → OvOK G c → OvOK G b →
    FS (Sm E Gl G) Eq ci ci' → FS (Sm E Gl G) Eq eb eb' →
    ∀ M, K * n ≤ M → FS (Sm E Gl G) Eq (evalWhileIter cfg c b p ci eb n) (evalWhileIter cfg c' b' p ci' eb' M)
  blockLoop : ∀ {G : StackFrame} ss ss' lab base base', LX E (Reserved.ex E) ss ss' → LabOK (some lab) →
    (∀ x ∈ ss, OvOK G x) → ∀ M, K * n ≤ M →
    FS (Sm E Gl G) Eq (evalBlockLoop cfg n ss lab [] base) (evalBlockLoop cfg M ss' lab [] base')
  blockFrom : ∀ {G : StackFrame} ss ss' bl k k' l d, Corr E l ss ss' k k' → LabOK (some bl) →
    (∀ x ∈ ss, OvOK G x) → Gl l → ∀ M, K * n ≤ M →
    FS (Sm E Gl G) Eq (evalBlockFrom cfg n ss bl [] k l d) (evalBlockFrom cfg M ss' bl [] k' l d)
  stmtFrom : ∀ {G : StackFrame} s t l d, NR E Rw Gl s t → OvOK G s → Gl l → l ∈ statementLabels s → ∀ M, K * n ≤ M →
    FS (Sm E Gl G) Eq (evalStmtFrom cfg n s l d) (evalStmtFrom cfg M t l d)
  runFrom : ∀ {G : StackFrame} ss ss' k k' l d, Corr E l ss ss' k k' → (∀ x ∈ ss, OvOK G x) → Gl l → ∀ M, K * n ≤ M →
    FS (Sm E Gl G) Eq (runFrom cfg n ss k l d) (runFrom cfg M ss' k' l d)
  fin : ∀ {G : StackFrame} f f' base base' k, ORel E f f' → OvO G f → ∀ M, K * n ≤ M →
    FS (Sm E Gl G) Eq (runTryFinally cfg n f false base k) (runTryFinally cfg M f' false base' k)
  finish : ∀ {G : StackFrame} f f' base base' k c c', ORel E f f' → CatchRel E c c' → FinOK f → OvO G f →
    OvC G c → ∀ M, K * n ≤ M →
    FS (Sm E Gl G) Eq (finishCatchClause cfg n f false base k c) (finishCatchClause cfg M f' false base' k c')
  clauses : ∀ {G : StackFrame} f f' base base' k v j cs cs', ORel E f f' → L2 (CatchRel E) cs cs' →
    L2 (fun c c' => OV E c.predicate c'.predicate) cs cs' → FinOK f → OvO G f → (∀ c ∈ cs, OvC G c) → ∀ M, K * n ≤ M →
    FS (Sm E Gl G) Eq (tryCatchClauses cfg n f false base k v j cs) (tryCatchClauses cfg M f' false base' k v j cs')
  list : ∀ {G : StackFrame} ss ss' a, LX E (Reserved.ex E) ss ss' → (∀ x ∈ ss, OvOK G x) → ∀ M, K * n ≤ M →
    FS (Sm E Gl G) (VRel (a = true → LXv E (Reserved.ex E) ss ss')) (evalStmtList cfg n ss a) (evalStmtList cfg M ss' a)
  callee : ∀ {G : StackFrame} site site' c args, ¬ Reserved.resCall c → ∀ M, K * n ≤ M →
    FS (Sm E Gl G) Eq (invokeCallee cfg n site c args) (invokeCallee cfg M site' c args)
  pre : ∀ {G : StackFrame} site site' P P' args, ProcRelB E P P' → ∀ M, K * n ≤ M →
    FS (Sm E Gl G) Eq (checkPreconditions cfg n site P args) (checkPreconditions cfg M site' P' args)
  post : ∀ {G : StackFrame} P P' ps ps' fr fr' ef ent ent' xf xf' r r', ProcRelB E P P' → L2 (CondRel E) ps ps' →
    L2 (GroupRel E) fr fr' →
    (∀ c ∈ ps, OvOK condG c.condition) → postOutputs P r xf = postOutputs P' r' xf' →
    Clean ef → (∀ k, NG k → ent.2.contains k = false) → ent'.1 = ent.1 → GlR ent.2 ent'.2 →
    (∀ k, NG k → ent'.2.contains k = false) → (∀ k, ¬ Reserved.aliasOf G k) →
    (∀ k v, Reserved.frozenOf G k = some v → ent.2[k]? = some v) → ∀ M, K * n ≤ M →
    FSH (Sm E Gl G) (Sm E Gl (Reserved.postOf G condG)) (Sm E Gl (Reserved.postOf G condG)) Eq
      (checkPostconditions cfg n P ps fr ef ent xf r)
      (checkPostconditions cfg M P' ps' fr' ef ent' xf' r')
  proc : ∀ {G : StackFrame} site site' P P' args, ProcRelB E P P' → ∀ M, K * n ≤ M →
    FS (Sm E Gl G) Eq (invokeProc cfg n site P args) (invokeProc cfg M site' P' args)

variable {cfg E Rw K Gl} in
theorem FundAt.exprMdT {n : Nat} (ih : FundAt cfg E Rw K Gl n) (hv : ∀ a b, Reserved.vok E a b) {G : StackFrame}
    (s t : StmtExprMd) (h : NR E Rw Gl s t) (ho : OvOK G s) (M : Nat) (hM : K * n ≤ M) :
    FS (Sm E Gl G) Eq (evalExprMd cfg n s) (evalExprMd cfg M t) :=
  (ih.exprMd s t h ho M hM).weaken (fun _ _ f => f (hv _ _))

variable {cfg E Rw K Gl} in
theorem FundAt.exprT {n : Nat} (ih : FundAt cfg E Rw K Gl n) (hv : ∀ a b, Reserved.vok E a b) {G : StackFrame}
    (s t : StmtExprMd) (h : NR E Rw Gl s t) (ho : OvOK G s) (M : Nat) (hM : K * n ≤ M) :
    FS (Sm E Gl G) Eq (evalExpr cfg n s.val) (evalExpr cfg M t.val) :=
  (ih.expr s t h ho M hM).weaken (fun _ _ f => f (hv _ _))

variable {cfg E Rw K Gl} in
theorem FundAt.outputsT {n : Nat} (ih : FundAt cfg E Rw K Gl n) (hv : ∀ a b, Reserved.vok E a b) {G : StackFrame}
    (s t : StmtExprMd) (h : NR E Rw Gl s t) (ho : OvOK G s) (M : Nat) (hM : K * n ≤ M) :
    FS (Sm E Gl G) Eq (evalCallOutputs cfg n s.val) (evalCallOutputs cfg M t.val) :=
  (ih.outputs s t h ho M hM).weaken (fun _ _ f => f (hv _ _))

def runSt (cfg : ExternalBackendM PM) (n : Nat) (s : StmtExprMd) : EvalM PM Unit := do
  modify fun (st : EvalState) => { st with stmtSite := s.source }
  if (stackAnnotation? s).isNone then withOperandWindow s (evalStmt cfg n s)

structure RwStep (n : Nat) : Prop where
  scoped_ : ∀ {G : StackFrame} s t, Rw s t → OvOK G s → ∀ M, K * (n + 1) ≤ M →
    FS (Sm E Gl G) Eq (evalScopedStmt cfg (n + 1) s) (evalScopedStmt cfg M t)
  exprMd : ∀ {G : StackFrame} s t, Rw s t → OvOK G s → ∀ M, K * (n + 1) ≤ M →
    FS (Sm E Gl G) (VRel (Reserved.vok E s t)) (evalExprMd cfg (n + 1) s) (evalExprMd cfg M t)
  expr : ∀ {G : StackFrame} s t, Rw s t → OvOK G s → ∀ M, K * (n + 1) ≤ M →
    FS (Sm E Gl G) (VRel (Reserved.vok E s t)) (evalExpr cfg (n + 1) s.val) (evalExpr cfg M t.val)
  stmt : ∀ {G : StackFrame} s t, Rw s t → OvOK G s → ∀ M, K * (n + 1) ≤ M →
    FS (Sm E Gl G) Eq (evalStmt cfg (n + 1) s) (evalStmt cfg M t)
  outputs : ∀ {G : StackFrame} s t, Rw s t → OvOK G s → ∀ M, K * (n + 1) ≤ M →
    FS (Sm E Gl G) (VRel (Reserved.vok E s t)) (evalCallOutputs cfg (n + 1) s.val) (evalCallOutputs cfg M t.val)
  exStmt : ∀ {G : StackFrame} s ts, Reserved.ex E s ts → OvOK G s → ∀ M, K * n ≤ M →
    FS (Sm E Gl G) Eq (runSt cfg n s) (ts.forM (runSt cfg M))
  exLast : ∀ {G : StackFrame} s ts, Reserved.ex E s ts → OvOK G s → ∀ M, K * n ≤ M →
    ∃ ts0 t, ts = ts0 ++ [t] ∧ FS (Sm E Gl G) (VRel (Reserved.vokX E s ts))
      (do modify fun (st : EvalState) => { st with stmtSite := s.source }; withOperandWindow s (evalExprMd cfg n s))
      (do ts0.forM (runSt cfg M); modify fun (st : EvalState) => { st with stmtSite := t.source };
          withOperandWindow t (evalExprMd cfg M t))

structure PassRel : Prop where
  K_pos : 1 ≤ K
  cfg_ok : CfgB cfg
  closed : ∀ s t, E s t → NR E Rw Gl s t
  decl : Reserved.retLabel ≠ none → ∀ s t, Rw s t → blockDeclarations [s] = blockDeclarations [t]
  declX : ∀ G s t, Rw s t → LooseExt G (blockDeclarations [s]) (blockDeclarations [t])
  declOK : ∀ s t, Rw s t → ∀ x ∈ blockDeclarations [s], ¬ Reserved.res x ∧ NotV x
  exDecl : ∀ G s ts, Reserved.ex E s ts → LooseExt G (blockDeclarations [s]) (blockDeclarations ts)
  exDeclOK : ∀ s ts, Reserved.ex E s ts → ∀ x ∈ blockDeclarations [s], ¬ Reserved.res x ∧ NotV x
  retGl : ∀ L, Reserved.retLabel = some L → ¬ Gl L
  retRes : ∀ L, Reserved.retLabel = some L → Reserved.resLabel L
  glRes : ∀ l, Gl l → ¬ Reserved.resLabel l
  labE : ∀ s t, E s t → ∀ l, ¬ Reserved.resLabel l → (l ∈ statementLabels s ↔ l ∈ statementLabels t)
  rwLab : ∀ s t, Rw s t → (∀ l, ¬ Reserved.resLabel l → l ∉ statementLabels s ∧ l ∉ statementLabels t) ∧
    (stackAnnotation? s).isNone ∧ (stackAnnotation? t).isNone
  exLab : ∀ s ts, Reserved.ex E s ts → ∀ l, ¬ Reserved.resLabel l → l ∉ statementLabels s ∧ ∀ t ∈ ts, l ∉ statementLabels t
  renAnn : ∀ f f', Reserved.ren f f' → f.text ≠ stackShapeName ∧ f'.text ≠ stackShapeName
  retK : Reserved.retLabel ≠ none → 3 ≤ K
  retNG : Reserved.retLabel ≠ none → Reserved.noGlobals
  retV : Reserved.retLabel ≠ none → Reserved.vret = none
  retHook : Reserved.retLabel ≠ none → ∀ G e, Reserved.nodeOK G e
  retPlain : Reserved.retLabel ≠ none → ∀ G, Plain G
  retVok : Reserved.retLabel ≠ none → ∀ a b, Reserved.vok E a b
  renOp : ∀ f f', Reserved.ren f f' → ∃ op, opOf? f.text = some op ∧ opOf? f'.text = some op
  step : ∀ n, (∀ k ≤ n, FundAt cfg E Rw K Gl k) → RwStep cfg E Rw K Gl n

end

section
variable [Reserved]

omit [Reserved] in
theorem inouts_keys_gen {Q : String → Prop} (ins : List Parameter) (ef : StackFrame) :
    ∀ (l : List Parameter) (acc : StackFrame), (∀ k v, acc[k]? = some v → Q k) →
      (∀ o ∈ l, ins.any (·.name.text == o.name.text) = true → Q o.name.text) →
      ∀ k v, (l.foldl (init := acc) fun acc o =>
        if ins.any (·.name.text == o.name.text) then
          match ef[o.name.text]? with
          | some v => acc.insert o.name.text v
          | none => acc
        else acc)[k]? = some v → Q k := by
  intro l
  induction l with
  | nil => intro acc ha _; exact ha
  | cons o os ih =>
    intro acc ha hl
    simp only [List.foldl_cons]
    refine ih _ ?_ (fun o' ho' hi => hl o' (List.mem_cons_of_mem _ ho') hi)
    intro k v hk
    split at hk
    · rename_i hi
      split at hk
      · rw [Std.HashMap.getElem?_insert] at hk
        split at hk
        · rename_i he
          simp only [beq_iff_eq] at he
          rw [← he]; exact hl o (List.mem_cons_self ..) hi
        · exact ha k v hk
      · exact ha k v hk
    · exact ha k v hk

omit [Reserved] in
theorem inouts_keys {Q : String → Prop} {P : Procedure}
    (h : ∀ o ∈ P.outputs, P.inputs.any (·.name.text == o.name.text) = true → Q o.name.text) (ef : StackFrame) :
    ∀ k v, (P.outputs.foldl (init := ({} : StackFrame)) fun acc o =>
        if P.inputs.any (·.name.text == o.name.text) then
          match ef[o.name.text]? with
          | some v => acc.insert o.name.text v
          | none => acc
        else acc)[k]? = some v → Q k :=
  inouts_keys_gen P.inputs ef P.outputs {} (fun k v h => by rw [Std.HashMap.getElem?_empty] at h; cases h) h

end

section Steps
variable [Reserved] {G : StackFrame} {cfg : ExternalBackendM PM} {E Rw : StmtExprMd → StmtExprMd → Prop} {K : Nat} {Gl : String → Prop}
  (hp : PassRel cfg E Rw K Gl)

include hp

theorem exprMdE {n : Nat} (ih : FundAt cfg E Rw K Gl n) {a b : StmtExprMd} (h : E a b) (hv : Reserved.vok E a b)
    (ho : OvOK G a) {M : Nat} (hM : K * n ≤ M) : FS (Sm E Gl G) Eq (evalExprMd cfg n a) (evalExprMd cfg M b) :=
  (ih.exprMd _ _ (hp.closed _ _ h) ho M hM).weaken (fun _ _ f => f hv)

theorem outputsE {n : Nat} (ih : FundAt cfg E Rw K Gl n) {a b : StmtExprMd} (h : E a b) (hv : Reserved.vok E a b)
    (ho : OvOK G a) {M : Nat} (hM : K * n ≤ M) :
    FS (Sm E Gl G) Eq (evalCallOutputs cfg n a.val) (evalCallOutputs cfg M b.val) :=
  (ih.outputs _ _ (hp.closed _ _ h) ho M hM).weaken (fun _ _ f => f hv)

omit hp in
theorem excTypeOK_congr {σ σ' : EvalState} (h : StRel G (IxRel E) σ σ') {ty ty' : HighType}
    (hty : Reserved.tyR ty ty') (v : Value) : excTypeOK σ' v ty' = excTypeOK σ v ty := by
  have hb : σ'.index.exceptionBase ty' = σ.index.exceptionBase ty := by
    simp only [ProgramIndex.exceptionBase, h.index.unalias _ _ hty, h.index.exceptionBases]
  simp only [excTypeOK, hb, h.index.ancestors, h.index.testers]

omit hp in
theorem excOK_of {P P' : Procedure} (ht : P.throwsType = P'.throwsType)
    (hty : ∀ t, P.throwsType = some t → Reserved.tyR t.val t.val) : ExcOK (Sm E Gl G) P P' :=
  fun σ σ' v t hs htt => ⟨t, by rw [← ht]; exact htt, excTypeOK_congr hs (hty t htt) v⟩

omit hp in
theorem fs_checkCaught {cs cs' : List CatchClause} (hcs : L2 (CatchRel E) cs cs') (v : Value) :
    FS (Sm E Gl G) Eq (checkCaught cs v) (checkCaught cs' v) := by
  cases hcs with
  | nil => exact fs_pure rfl
  | cons hc _ =>
    refine ⟨fun σ σ' τ τ' hs ht _ => ?_⟩
    have hσ : StRel G (IxRel E) σ σ' := hs
    simp only [checkCaught, run_bind, run_get]
    rw [hσ.index.unalias _ _ hc.2.2.2.2.2]
    split
    · exact fun _ => ⟨_⟩
    · rw [run_checkExcType, run_checkExcType, excTypeOK_congr hσ hc.2.2.2.2.2]
      split
      · exact ⟨rfl, hs, ht⟩
      · exact fun _ => ⟨_⟩

omit [Reserved] hp in
theorem fs_oofSrc {S T U : SimRel} {A : α → β → Prop} {y : EvalM PM β} :
    FSH S T U A (throw .outOfFuel) y :=
  ⟨fun _ _ _ _ _ _ hn => absurd (by simp [run_throw, OOF]) hn⟩

set_option hygiene false in
macro "ovk" : tactic => `(tactic| first
  | exact hov
  | exact Hered.kid hov (by simp [stmtExprChildren, variableChildren])
  | exact Hered.kid hov (by simp_all [stmtExprChildren, variableChildren]))

omit hp in
theorem OvOK.relax {G : StackFrame} {e : StmtExprMd} (h : OvOK G e) (ds : List String) :
    OvOK (Reserved.relax G ds) e :=
  h.regime (sameRegime_relax G ds) (fun e h => (Reserved.nodeOK_relax G ds e).mpr h)

omit hp in
theorem fs_wbs' {l l' : List StmtExprMd} {G : StackFrame} (hn : LooseExt G (blockDeclarations l) (blockDeclarations l'))
    (hr : ∀ n ∈ blockDeclarations l, ¬ Reserved.res n ∧ NotV n)
    {β : Type} {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β}
    (h : FS (Sm E Gl (Reserved.relax G (blockDeclarations l'))) A x y) :
    FS (Sm E Gl G) A (withBlockScope l x) (withBlockScope l' y) :=
  fs_wbsX hn (fun n h => (hr n h).1) (fun n h => (hr n h).2) h

omit [Reserved] hp in
theorem unsup_decl {v : StmtExpr} (hu : Unsup v) (src : FileRange) :
    blockDeclarations [⟨v, src⟩] = [] := by
  cases v <;> simp only [Unsup] at hu <;> rfl

omit hp in
theorem L2.declTargets {ts ts' : List VariableMd} (h : L2 (fun a b => VarRel E a.val b.val ∧ WOK a.val) ts ts') :
    ts.filterMap (fun t => match t.val with | .Declare p => some p.name.text | _ => none) =
      ts'.filterMap (fun t => match t.val with | .Declare p => some p.name.text | _ => none) := by
  induction h with
  | nil => rfl
  | @cons a b as bs hab _ ih =>
    replace hab := hab.1
    rcases a with ⟨av, _⟩
    rcases b with ⟨bv, _⟩
    cases av <;> cases bv <;> simp only [VarRel] at hab <;> simp [ih, hab]

omit hp in
theorem L2.noPush {ts ts' : List VariableMd} (h : L2 (fun a b => VarRel E a.val b.val ∧ WOK a.val) ts ts') :
    isStackPushTarget ts = false ∧ isStackPushTarget ts' = false := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | @cons a b as bs hab _ ih =>
    replace hab := hab.1
    rcases a with ⟨av, _⟩
    rcases b with ⟨bv, _⟩
    cases av <;> cases bv <;> simp only [VarRel] at hab <;>
      simpa only [isStackPushTarget, List.any_cons, isStackVar, Bool.false_or] using ih

omit hp in
theorem Shape.decl {s t : StmtExprMd} (h : Shape E s t) : blockDeclarations [s] = blockDeclarations [t] := by
  cases h with
  | @var v v' _ _ hv =>
    cases v <;> cases v' <;> simp only [VarRel] at hv <;> simp [Interpreter.blockDeclarations, hv]
  | assign hts =>
    simp only [Interpreter.blockDeclarations, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact hts.declTargets
  | @unsup v v' _ _ hu hu' =>
    rw [unsup_decl hu, unsup_decl hu']
  | _ => rfl

theorem NR.decl {s t : StmtExprMd} (h : NR E Rw Gl s t) (G : StackFrame) :
    LooseExt G (blockDeclarations [s]) (blockDeclarations [t]) := by
  rcases h with ⟨h, -⟩ | h
  · exact .ofEq h.decl
  · exact hp.declX G s t h

theorem NR.declEq (hL : Reserved.retLabel ≠ none) {s t : StmtExprMd} (h : NR E Rw Gl s t) :
    blockDeclarations [s] = blockDeclarations [t] := by
  rcases h with ⟨h, -⟩ | h
  · exact h.decl
  · exact hp.decl hL s t h

omit hp in
theorem L2.declOK {ts ts' : List VariableMd} (h : L2 (fun a b => VarRel E a.val b.val ∧ WOK a.val) ts ts') :
    ∀ x ∈ ts.filterMap (fun t => match t.val with | .Declare p => some p.name.text | _ => none),
      ¬ Reserved.res x ∧ NotV x := by
  induction h with
  | nil => simp
  | @cons a b as bs hab _ ih =>
    replace hab := hab.1
    rcases a with ⟨av, _⟩
    rcases b with ⟨bv, _⟩
    intro x hx
    cases av <;> cases bv <;> simp only [VarRel] at hab <;> simp only [List.filterMap_cons] at hx
    all_goals first
      | exact ih x hx
      | (simp only [List.mem_cons] at hx
         rcases hx with rfl | hx
         · exact hab.2.2
         · exact ih x hx)

omit hp in
theorem Shape.declOK {s t : StmtExprMd} (h : Shape E s t) :
    ∀ x ∈ blockDeclarations [s], ¬ Reserved.res x ∧ NotV x := by
  cases h with
  | @var v v' _ _ hv =>
    cases v <;> cases v' <;> simp only [VarRel] at hv <;>
      simp only [Interpreter.blockDeclarations, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq, false_implies, implies_true]
    exact hv.2.2
  | assign hts =>
    simp only [Interpreter.blockDeclarations, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact hts.declOK
  | @unsup v v' _ _ hu hu' =>
    rw [unsup_decl hu]; simp
  | _ => simp [Interpreter.blockDeclarations]

theorem NR.declOK {s t : StmtExprMd} (h : NR E Rw Gl s t) :
    ∀ x ∈ blockDeclarations [s], ¬ Reserved.res x ∧ NotV x := by
  rcases h with ⟨h, -⟩ | h
  · exact h.declOK
  · exact hp.declOK s t h

omit [Reserved] hp in
theorem unsup_expr {v : StmtExpr} (hu : Unsup v) (n : Nat) :
    evalExpr cfg (n + 1) v = evalError s!"unsupported expression: {v.constrName}" := by
  cases v <;> simp only [Unsup] at hu <;> first
    | rfl
    | (rename_i ty _; cases ty <;> first | exact absurd rfl hu | rfl)

omit [Reserved] hp in
theorem unsup_exprMd {v : StmtExpr} (hu : Unsup v) (n : Nat) (src : FileRange) :
    evalExprMd cfg (n + 1) ⟨v, src⟩ = jumpBoundary (evalExpr cfg n v) := by
  cases v <;> simp only [Unsup] at hu <;> rfl

omit [Reserved] hp in
theorem unsup_stmt {v : StmtExpr} (hu : Unsup v) (n : Nat) (src : FileRange) :
    evalStmt cfg (n + 1) ⟨v, src⟩ = (do let _ ← evalExprMd cfg n ⟨v, src⟩; pure ()) := by
  cases v <;> simp only [Unsup] at hu <;> rfl

omit [Reserved] hp in
theorem unsup_scoped {v : StmtExpr} (hu : Unsup v) (n : Nat) (src : FileRange) :
    evalScopedStmt cfg (n + 1) ⟨v, src⟩ = withBlockScope [⟨v, src⟩] (withOperandWindow ⟨v, src⟩ (evalStmt cfg n ⟨v, src⟩)) := by
  cases v <;> simp only [Unsup] at hu <;> rfl

omit [Reserved] hp in
theorem unsup_outputs {v : StmtExpr} (hu : Unsup v) (n : Nat) :
    evalCallOutputs cfg (n + 1) v = (do let x ← evalExpr cfg n v; pure #[x]) := by
  cases v <;> simp only [Unsup] at hu <;> rfl

theorem fstep_scoped {n : Nat} (ih : FundAt cfg E Rw K Gl n) (ihs : ∀ k ≤ n, FundAt cfg E Rw K Gl k) :
    ∀ s t, NR E Rw Gl s t → OvOK G s → ∀ M, K * (n + 1) ≤ M →
      FS (Sm E Gl G) Eq (evalScopedStmt cfg (n + 1) s) (evalScopedStmt cfg M t) := by
  intro s t hst hov M' hM'
  rcases hst with ⟨hsh, hex⟩ | hrw
  · obtain ⟨M, rfl, hM⟩ := fuel_split hp.K_pos hM'
    have hd := hsh.decl
    have hdo := hsh.declOK
    have hN : NR E Rw Gl s t := .inl ⟨hsh, hex⟩
    cases hsh
    case unsup hu hu' =>
      rw [unsup_scoped hu, unsup_scoped hu']
      exact fs_wbs' (.ofEq hd) hdo (fs_wow (ih.stmt _ _ hN (hov.relax _) M hM))
    all_goals
      simp only [evalScopedStmt]
      first
      | exact ih.stmt _ _ hN hov M hM
      | exact fs_wbs' (.ofEq hd) hdo (fs_wow (ih.stmt _ _ hN (hov.relax _) M hM))
  · exact (hp.step n ihs).scoped_ s t hrw hov M' hM'

set_option maxHeartbeats 1000000 in
/-- `evalExprMd` with fuel `n + 1` on `NR`-related terms is simulated, given `FundAt` up to `n`. -/
theorem fstep_exprMd {n : Nat} (ih : FundAt cfg E Rw K Gl n) (ihs : ∀ k ≤ n, FundAt cfg E Rw K Gl k) :
    ∀ s t, NR E Rw Gl s t → OvOK G s → ∀ M, K * (n + 1) ≤ M →
      FS (Sm E Gl G) (VRel (Reserved.vok E s t)) (evalExprMd cfg (n + 1) s) (evalExprMd cfg M t) := by
  intro s t hst hov M' hM'
  rcases hst with ⟨hsh, hex⟩ | hrw
  · obtain ⟨M, rfl, hM⟩ := fuel_split hp.K_pos hM'
    have hN : NR E Rw Gl s t := .inl ⟨hsh, hex⟩
    cases hsh
    case unsup hu hu' =>
      rw [unsup_exprMd hu, unsup_exprMd hu']
      exact fs_jumpBoundary (ih.expr _ _ hN hov M hM)
    all_goals
      simp only [evalExprMd]
      refine fs_jumpBoundary ?_
      first
      | exact fs_bind (fs_modifyRel (fun a a' ha => by strel ha)) (fun _ _ _ => ih.expr _ _ hN hov M hM)
      | exact fs_bind (ih.stmt _ _ hN hov M hM) (fun _ _ _ => fs_pure (fun _ => rfl))
      | exact ih.expr _ _ hN hov M hM
  · exact (hp.step n ihs).exprMd s t hrw hov M' hM'

theorem fstep_assign {n : Nat} (ih : FundAt cfg E Rw K Gl n) :
    ∀ v v', VarRel E v v' → VV E v v' → WOK v → OvV G v → ∀ M, K * (n + 1) ≤ M →
      FS (Sm E Gl G) UTRel (assignTarget cfg (n + 1) v) (assignTarget cfg M v') := by
  intro v v' hv hvv hw hov M' hM'
  obtain ⟨M, rfl, hM⟩ := fuel_split hp.K_pos hM'
  cases v <;> cases v' <;> simp only [VarRel] at hv <;> simp only [assignTarget]
  · exact fs_pure ⟨hv.1, hv.2, hw⟩
  · exact fs_bind (exprMdE hp ih hv.1 (hvv _ _ _ _ rfl rfl) (hov _ (by simp [variableChildren])) hM)
      (fun a b hab => by subst hab; simp only [strictField_none hp.cfg_ok.strict]; exact fs_pure ⟨rfl, hv.2⟩)
  · exact fs_pure ⟨hv.1, hv.2.2.1, hv.2.2.2⟩

omit hp in
theorem lookupVar_congr {σ σ' : EvalState} (h : StRel G (IxRel E) σ σ') {x : String} (hx : ¬ Reserved.res x)
    (hv : NotV x ∨ Strict G) : lookupVar σ' x = lookupVar σ x := by
  simp only [lookupVar, h.stack.get hx hv, h.globals x hx]

omit hp in
theorem fs_readLocalVar {a b : Identifier} (hv : a.text = b.text ∧ ¬ Reserved.res a.text)
    (hn : NotV a.text ∨ Strict G) :
    FS (Sm E Gl G) Eq (do
        match lookupVar (← get) a.text with
        | some v => pure v
        | none => (stuckError s!"undefined identifier '{a.text}'" : EvalM PM Value))
      (do
        match lookupVar (← get) b.text with
        | some v => pure v
        | none => (stuckError s!"undefined identifier '{b.text}'" : EvalM PM Value)) := by
  refine fs_bind fs_get (fun σ σ' hσ => ?_)
  have hσ : StRel G (IxRel E) σ σ' := hσ
  rw [← hv.1, lookupVar_congr hσ hv.2 hn]
  cases lookupVar σ _ with
  | none => exact fs_stuck _ _
  | some x => exact fs_pure rfl

theorem fstep_update {n : Nat} (ih : FundAt cfg E Rw K Gl n) :
    ∀ v v', VarRel E v v' → VV E v v' → WOK v → OvV G v →
      (∀ a, v = .Local a → Reserved.nodeOK G ⟨.Var (.Local a), .unknown⟩) → ∀ M, K * (n + 1) ≤ M →
      FS (Sm E Gl G) UpdRel (readForUpdate cfg (n + 1) v) (readForUpdate cfg M v') := by
  intro v v' hv hvv hw hov hvk M' hM'
  obtain ⟨M, rfl, hM⟩ := fuel_split hp.K_pos hM'
  cases v <;> cases v' <;> simp only [VarRel] at hv <;> simp only [readForUpdate]
  · rename_i a b
    cases n with
    | zero => exact ⟨fun _ _ _ _ _ _ hn => absurd (by simp [evalExpr, run_throw, OOF]) hn⟩
    | succ n0 =>
      obtain ⟨M0, rfl⟩ : ∃ M0, M = M0 + 1 := ⟨M - 1, by have := hp.K_pos; simp only [Nat.mul_succ] at hM; omega⟩
      simp only [evalExpr]
      exact fs_bind (fs_readLocalVar hv (.inl hw))
        (fun x y hxy => fs_pure ⟨hxy, hv.1, hv.2, hw⟩)
  · refine fs_bind (exprMdE hp ih hv.1 (hvv _ _ _ _ rfl rfl) (hov _ (by simp [variableChildren])) hM)
      (fun a b hab => ?_)
    subst hab
    exact fs_bind (fs_readField _ _ _ hv.2) (fun x y hxy => fs_pure ⟨hxy, rfl, hv.2⟩)
  · exact fs_evalError _ _

omit hp in
theorem fs_writeUpdate (u u' : UpdateTarget) (hu : UTRel u u') (x : Value) :
    FS (Sm E Gl G) Eq (writeUpdate u x : EvalM PM Unit) (writeUpdate u' x) := by
  cases u <;> cases u' <;> simp only [UTRel] at hu <;> simp only [writeUpdate]
  · exact fs_assignLocal _ _ hu.1 hu.2.1 hu.2.2 x
  · obtain ⟨rfl, rfl⟩ := hu
    exact fs_writeField _ _ _ rfl x
  · obtain ⟨rfl, hr, hv⟩ := hu
    exact fs_modifyRel (fun a a' ha => ha.with_stack (ha.stack.declareLocal hr hv x))

theorem fstep_fin {n : Nat} (ih : FundAt cfg E Rw K Gl n) :
    ∀ f f' base base' k, ORel E f f' → OvO G f → ∀ M, K * (n + 1) ≤ M →
      FS (Sm E Gl G) Eq (runTryFinally cfg (n + 1) f false base k) (runTryFinally cfg M f' false base' k) := by
  intro f f' base base' k hf hof M' hM'
  obtain ⟨M, rfl, hM⟩ := fuel_split hp.K_pos hM'
  cases f <;> cases f' <;> simp only [ORel] at hf <;> simp only [runTryFinally]
  · exact fs_pure rfl
  · simp only [Bool.false_eq_true, ite_false]
    exact ih.scoped_ _ _ (hp.closed _ _ hf) (hof _ rfl) M hM

omit hp in
theorem fs_finW {n M : Nat} (ih : FundAt cfg E Rw K Gl n) (hM : K * n ≤ M) {f f' : Option StmtExprMd}
    (hf : ORel E f f') (hfo : FinOK f) (base base' : List Nat) (k : Nat) (v : Value) {B : α → β → Prop} :
    FSH ((Sm E Gl G).atWin v) (Sm E Gl G) (Sm E Gl G) B
      (runTryFinally cfg n f false base k >>= fun _ => (throw (.return_ [v]) : EvalM PM α))
      (runTryFinally cfg M f' false base' k >>= fun _ => (throw (.return_ []) : EvalM PM β)) := by
  by_cases hfree : Free G
  · obtain ⟨o, hvr, _⟩ := id hfree
    have hfin := ih.fin (G := exactG G o v) f f' base base' k hf hfo.ov M hM
    refine fs_bind (hfin.reg (S := (Sm E Gl G).atWin v) (T := (Sm E Gl G).atWin v) (U := Sm E Gl G)
      (fun σ σ' h => h.2.1.toExact hvr (h.2.2 o hvr)) rfl
      (fun σ σ' h => ⟨hfree, (StRel.ofExact hvr hfree h).1, fun o' ho' => ?_⟩) rfl
      (fun c c' σ σ' h => SigR.ofExact _ hvr hfree h) rfl) (fun _ _ _ => fs_throwW v)
    rw [hvr] at ho'
    cases ho'
    exact (StRel.ofExact hvr hfree h).2
  · exact fs_noPre (fun _ _ h => hfree h.1)

def Cap (G : StackFrame) (o o' : Option Control) (σ σ' : EvalState) : Prop :=
  (OkOpt Gl G o o' ∧ StRel G (IxRel E) σ σ') ∨
    (∃ v, o = some (.return_ [v]) ∧ o' = some (.return_ []) ∧ (Sm E Gl G).win v σ σ')

omit hp in
theorem win_restack {v : Value} {σ σ' : EvalState} (h : (Sm E Gl G).win v σ σ') {f f' : StackFrame}
    (hs : SR G σ.globals f f') (ho : ∀ o, Reserved.vret = some o → f'[o]? = σ'.stack[o]?) :
    (Sm E Gl G).win v { σ with stack := f } { σ' with stack := f' } :=
  ⟨h.1, h.2.1.with_stack hs, fun o hvo => (ho o hvo).trans (h.2.2 o hvo)⟩

omit hp in
theorem win_unbind {v : Value} {σ σ' : EvalState} (h : (Sm E Gl G).win v σ σ') {n : String}
    (hn : ¬ Reserved.res n) (hv : NotV n) :
    (Sm E Gl G).win v { σ with stack := unbindCatch σ.stack n } { σ' with stack := unbindCatch σ'.stack n } :=
  win_restack h (h.2.1.stack.unbindCatch hn hv)
    (fun o hvo => unbindCatch_ne (fun e => hv o hvo e) (fun e => (Reserved.vret_ok o hvo).2.2 n e))

theorem fstep_finish {n : Nat} (ih : FundAt cfg E Rw K Gl n) :
    ∀ f f' base base' k c c', ORel E f f' → CatchRel E c c' → FinOK f → OvO G f → OvC G c → ∀ M, K * (n + 1) ≤ M →
      FS (Sm E Gl G) Eq (finishCatchClause cfg (n + 1) f false base k c)
        (finishCatchClause cfg M f' false base' k c') := by
  intro f f' base base' k c c' hf hc hfo hof hoc M' hM'
  obtain ⟨M, rfl, hM⟩ := fuel_split hp.K_pos hM'
  simp only [finishCatchClause]
  refine fs_bindV (A := Cap (E := E) (Gl := Gl) G) (fs_tryCatchVW
    (FSV.ofFSH (fs_bind (ih.scoped_ _ _ (hp.closed _ _ hc.2.2.1) hoc.2 M hM)
      (fun _ _ _ => fs_pure (A := OkOpt Gl G) trivial)) (fun a b σ σ' hab hst => .inl ⟨hab, hst⟩))
    (fun sig hsig => FSV.ofFSH (by cases sig <;> first | exact fs_throw _ hsig | exact fs_pure ⟨.inl rfl, hsig⟩)
      (fun a b σ σ' hab hst => .inl ⟨hab, hst⟩)) ?_
    (fun L hL hok => FSV.ofFSH (fs_pure ⟨.inr (.inl ⟨L, hL, rfl, rfl⟩), hok⟩) (fun a b σ σ' hab hst => .inl ⟨hab, hst⟩))
    (fun w => ⟨fun σ σ' τ τ' hs ht _ => ?_⟩))
    (fun h h' σ0 σ0' hh => ?_)
  · intro σ τ
    simp [run_throw, OOF]
  · simp only [run_pure, RV]
    exact ⟨.inr ⟨w, rfl, rfl, hs⟩, ht⟩
  · rcases hh with ⟨hh, hst⟩ | ⟨w, rfl, rfl, hw⟩
    · refine FSH.ofAt ?_ hst (fun _ => rfl)
      refine fs_bind (fs_modifyRel (fun a a' ha => by
          simp only [← hc.1]; exact ha.with_stack (ha.stack.unbindCatch hc.2.2.2.1 hc.2.2.2.2.1)))
        (fun _ _ _ => fs_bind (ih.fin _ _ _ _ _ hf hof M hM) (fun _ _ _ => ?_))
      cases h <;> cases h' <;> simp only [OkOpt] at hh
      · exact fs_pure rfl
      · exact fs_throwR hh.2 hh.1
    · refine FSH.ofAt (S := (Sm E Gl G).atWin w) ?_ hw (fun _ => rfl)
      rw [← hc.1]
      refine fs_bind (fs_modify (S := (Sm E Gl G).atWin w) (fun a a' h => win_unbind (Gl := Gl) h hc.2.2.2.1 hc.2.2.2.2.1))
        (fun _ _ _ => ?_)
      exact fs_finW ih hM hf hfo _ _ _ w

theorem fstep_clauses {n : Nat} (ih : FundAt cfg E Rw K Gl n) :
    ∀ f f' base base' k v j cs cs', ORel E f f' → L2 (CatchRel E) cs cs' →
      L2 (fun c c' => OV E c.predicate c'.predicate) cs cs' → FinOK f → OvO G f →
      (∀ c ∈ cs, OvC G c) → ∀ M, K * (n + 1) ≤ M →
      FS (Sm E Gl G) Eq (tryCatchClauses cfg (n + 1) f false base k v j cs)
        (tryCatchClauses cfg M f' false base' k v j cs') := by
  intro f f' base base' k v j cs cs' hf hcs hpv hfo hof hocs M' hM'
  obtain ⟨M, rfl, hM⟩ := fuel_split hp.K_pos hM'
  cases hcs with
  | nil =>
    simp only [tryCatchClauses]
    exact fs_bind (ih.fin _ _ _ _ _ hf hof M hM) (fun _ _ _ => fs_throw _)
  | @cons c c' cs cs' hc hrest =>
    have hpv1 : OV E c.predicate c'.predicate := by cases hpv; assumption
    have hpvr : L2 (fun c c' => OV E c.predicate c'.predicate) cs cs' := by cases hpv; assumption
    simp only [tryCatchClauses]
    refine fs_bind (fs_modifyRel (fun a a' ha => by
        simp only [← hc.1]; exact ha.with_stack (ha.stack.bindCatch hc.2.2.2.1 hc.2.2.2.2.1 _)))
      (fun _ _ _ => ?_)
    have hoc := hocs _ (List.mem_cons_self ..)
    have hocs' : ∀ c ∈ cs, OvC G c := fun c hc => hocs c (List.mem_cons_of_mem _ hc)
    obtain ⟨hb1, hpr, hbody, hres⟩ := hc
    rcases c with ⟨cb, cp, cbody, cty⟩
    rcases c' with ⟨cb', cp', cbody', cty'⟩
    dsimp only at hpr hb1 hbody hres hoc
    have rest : ∀ b : Bool, FS (Sm E Gl G) Eq
        (if b = true then
          (if false = true then (do enterChild base (j + 1) none
                                    finishCatchClause cfg n f false base k ⟨cb, cp, cbody, cty⟩)
           else (finishCatchClause cfg n f false base k ⟨cb, cp, cbody, cty⟩))
         else (do modify fun s => { s with stack := unbindCatch s.stack cb.text }
                  tryCatchClauses cfg n f false base k v (j + 1) cs))
        (if b = true then
          (if false = true then (do enterChild base' (j + 1) none
                                    finishCatchClause cfg M f' false base' k ⟨cb', cp', cbody', cty'⟩)
           else (finishCatchClause cfg M f' false base' k ⟨cb', cp', cbody', cty'⟩))
         else (do modify fun s => { s with stack := unbindCatch s.stack cb'.text }
                  tryCatchClauses cfg M f' false base' k v (j + 1) cs')) := by
      intro b
      refine fs_ite (fun _ => ?_) (fun _ => ?_)
      · simp only [Bool.false_eq_true, ite_false]
        exact ih.finish _ _ _ _ _ _ _ hf ⟨hb1, hpr, hbody, hres⟩ hfo hof hoc M hM
      · exact fs_bind (fs_modifyRel (fun a a' ha => by
              simp only [← hb1]; exact ha.with_stack (ha.stack.unbindCatch hres.1 hres.2.1)))
          (fun _ _ _ => ih.clauses _ _ _ _ _ _ _ _ _ hf hrest hpvr hfo hof hocs' M hM)
    cases cp <;> cases cp' <;> simp only [ORel] at hpr
    · exact fs_bind (fs_pure rfl) (fun b b' hb => by subst hb; exact rest b)
    · refine fs_bind (fs_tryCatch (exprMdE hp ih hpr (hpv1 _ _ rfl rfl) (hoc.1 _ rfl) hM) (fun sig hsig => ?_) ?_
          (fun L hL hok => ?_) (fun w => ?_)) (fun x y hxy => ?_)
      · cases sig <;> dsimp only <;> (try simp only [↓reduceIte, Bool.false_eq_true]) <;> first
          | exact fs_throw _ hsig
          | exact fs_bind (fs_pure rfl) (fun _ _ _ => fs_throw _ hsig)
          | exact fs_bind (ih.fin _ _ _ _ _ hf hof M hM) (fun _ _ _ => fs_throw _ hsig)
          | exact fs_bind (fs_modifyRel (fun a a' ha => by
              simp only [← hb1]; exact ha.with_stack (ha.stack.unbindCatch hres.1 hres.2.1)))
              (fun _ _ _ => fs_bind (ih.fin _ _ _ _ _ hf hof M hM) (fun _ _ _ => fs_throw _ hsig))
          | exact fs_bind (fs_bind (fs_modifyRel (fun a a' ha => by
              simp only [← hb1]; exact ha.with_stack (ha.stack.unbindCatch hres.1 hres.2.1)))
              (fun _ _ _ => ih.fin _ _ _ _ _ hf hof M hM)) (fun _ _ _ => fs_throw _ hsig)
      · intro σ τ
        simp [run_throw, OOF]
      · dsimp only
        (try simp only [↓reduceIte, Bool.false_eq_true])
        first
          | exact fs_bind (fs_modifyRel (fun a a' ha => by
              simp only [← hb1]; exact ha.with_stack (ha.stack.unbindCatch hres.1 hres.2.1)))
              (fun _ _ _ => fs_bind (ih.fin _ _ _ _ _ hf hof M hM) (fun _ _ _ => fs_throwM hL hok))
          | exact fs_bind (fs_bind (fs_modifyRel (fun a a' ha => by
              simp only [← hb1]; exact ha.with_stack (ha.stack.unbindCatch hres.1 hres.2.1)))
              (fun _ _ _ => ih.fin _ _ _ _ _ hf hof M hM)) (fun _ _ _ => fs_throwM hL hok)
      · dsimp only
        (try simp only [↓reduceIte, Bool.false_eq_true])
        refine fs_bind (fs_modify (S := (Sm E Gl G).atWin w) (fun a a' h => ?_)) (fun _ _ _ => fs_finW ih hM hf hfo _ _ _ w)
        rw [← hb1]
        exact win_unbind (Gl := Gl) h hres.1 hres.2.1
      · subst hxy
        exact fs_bind (fs_liftM (isTrue_pconst _)) (fun b b' hb => by subst hb; exact rest b)

theorem fstep_iter {n : Nat} (ih : FundAt cfg E Rw K Gl n) :
    ∀ c c' b b' p ci ci' eb eb', E c c' → Reserved.vok E c c' → E b b' → OvOK G c → OvOK G b →
      FS (Sm E Gl G) Eq ci ci' → FS (Sm E Gl G) Eq eb eb' →
      ∀ M, K * (n + 1) ≤ M →
        FS (Sm E Gl G) Eq (evalWhileIter cfg c b p ci eb (n + 1)) (evalWhileIter cfg c' b' p ci' eb' M) := by
  intro c c' b b' p ci ci' eb eb' hc hcv hb hoc hob hci heb M' hM'
  obtain ⟨M, rfl, hM⟩ := fuel_split hp.K_pos hM'
  simp only [evalWhileIter]
  refine fs_bind (fs_chargeIteration b b') (fun _ _ _ => fs_bind heb (fun _ _ _ => ?_))
  refine fs_bind (exprMdE hp ih hc hcv hoc hM) (fun v v' hv => ?_)
  subst hv
  refine fs_ite (fun _ => ?_) (fun _ => fs_bind hci (fun _ _ _ => ?_))
  all_goals
    refine fs_bind (fs_liftM (isTrue_pconst _)) (fun x y hxy => ?_)
    subst hxy
    refine fs_ite (fun _ => ?_) (fun _ => fs_pure rfl)
    refine fs_ite (fun _ => fs_bind hci (fun _ _ _ => ?_)) (fun _ => ?_)
    all_goals
      exact fs_bind (ih.scoped_ _ _ (hp.closed _ _ hb) hob M hM)
        (fun _ _ _ => ih.iter _ _ _ _ _ _ _ _ _ hc hcv hb hoc hob hci heb M hM)

omit hp in
theorem fs_forM_run {l l' : List StmtExprMd} (hl : L2 E l l')
    {f g : StmtExprMd → EvalM PM PUnit} (h : ∀ a b, E a b → FS (Sm E Gl G) Eq (f a) (g b)) :
    FS (Sm E Gl G) Eq (l.forM f) (l'.forM g) := by
  induction hl with
  | nil => exact fs_pure rfl
  | cons hab _ ih' => exact fs_bind (h _ _ hab) (fun _ _ _ => ih')

omit [Reserved] hp in
theorem lforM_append (l₁ l₂ : List γ) (f : γ → EvalM PM PUnit) :
    (l₁ ++ l₂).forM f = (do l₁.forM f; l₂.forM f) := by
  induction l₁ with
  | nil => simp [List.forM]
  | cons x xs ih => simp [List.forM]

omit hp in
theorem fs_forM_LX {X : StmtExprMd → List StmtExprMd → Prop} {l l' : List StmtExprMd} (hl : LX E X l l')
    {f g : StmtExprMd → EvalM PM PUnit} (hov : ∀ x ∈ l, OvOK G x)
    (h : ∀ a b, E a b → OvOK G a → FS (Sm E Gl G) Eq (f a) (g b))
    (hx : ∀ a ts, X a ts → OvOK G a → FS (Sm E Gl G) Eq (f a) (ts.forM g)) :
    FS (Sm E Gl G) Eq (l.forM f) (l'.forM g) := by
  induction hl with
  | nil => exact fs_pure rfl
  | cons hab _ ih' =>
    exact fs_bind (h _ _ hab (hov _ (List.mem_cons_self ..)))
      (fun _ _ _ => ih' (fun x hx => hov x (List.mem_cons_of_mem _ hx)))
  | expand hab _ ih' =>
    rw [lforM_append]
    exact fs_bind (hx _ _ hab (hov _ (List.mem_cons_self ..)))
      (fun _ _ _ => ih' (fun x hx => hov x (List.mem_cons_of_mem _ hx)))

omit [Reserved] hp in
theorem LX.last {X : StmtExprMd → List StmtExprMd → Prop} {l l' : List StmtExprMd} (h : LX E X l l') :
    (l = [] ∧ l' = []) ∨
    (∃ i x i' y, l = i ++ [x] ∧ l' = i' ++ [y] ∧ LX E X i i' ∧ E x y) ∨
    (∃ i x i' ts, l = i ++ [x] ∧ l' = i' ++ ts ∧ LX E X i i' ∧ X x ts) := by
  induction h with
  | nil => exact .inl ⟨rfl, rfl⟩
  | @cons a b as bs hab hr ih =>
    rcases ih with ⟨rfl, rfl⟩ | ⟨i, x, i', y, rfl, rfl, hi, hxy⟩ | ⟨i, x, i', ts, rfl, rfl, hi, hx⟩
    · exact .inr (.inl ⟨[], a, [], b, rfl, rfl, .nil, hab⟩)
    · exact .inr (.inl ⟨a :: i, x, b :: i', y, rfl, rfl, .cons hab hi, hxy⟩)
    · exact .inr (.inr ⟨a :: i, x, b :: i', ts, rfl, rfl, .cons hab hi, hx⟩)
  | @expand a ts as bs hab hr ih =>
    rcases ih with ⟨rfl, rfl⟩ | ⟨i, x, i', y, rfl, rfl, hi, hxy⟩ | ⟨i, x, i', ts', rfl, rfl, hi, hx⟩
    · exact .inr (.inr ⟨[], a, [], ts, rfl, by simp, .nil, hab⟩)
    · exact .inr (.inl ⟨a :: i, x, ts ++ i', y, rfl, by simp, .expand hab hi, hxy⟩)
    · exact .inr (.inr ⟨a :: i, x, ts ++ i', ts', rfl, by simp, .expand hab hi, hx⟩)

omit hp in
theorem LX.toLXv (hv : ∀ a b, Reserved.vok E a b) (hx : ∀ a ts, Reserved.vokX E a ts)
    {l l' : List StmtExprMd} (h : LX E (Reserved.ex E) l l') : LXv E (Reserved.ex E) l l' := by
  rcases h.last with ⟨rfl, rfl⟩ | ⟨i, x, i', y, rfl, rfl, hi, hxy⟩ | ⟨i, x, i', ts, rfl, rfl, hi, hxt⟩
  · exact .nil
  · exact .snoc_e hi hxy (hv x y)
  · exact .snoc_x hi hxt (hx x ts)

omit hp in
theorem L2.vokOf {R : StmtExprMd → StmtExprMd → Prop} (hv : ∀ a b, Reserved.vok E a b) {l l' : List StmtExprMd}
    (h : L2 R l l') : LV E l l' :=
  h.imp (fun a b _ => hv a b)

omit hp in
theorem valKids_triv (hv : ∀ a b, Reserved.vok E a b) (hx : ∀ a ts, Reserved.vokX E a ts) {s t : StmtExprMd}
    (h : Shape E s t) : ValKids E s t := by
  cases h with
  | ite => exact ⟨hv _ _, fun _ => ⟨hv _ _, fun _ _ _ _ => hv _ _⟩⟩
  | block hss => exact fun _ => LX.toLXv hv hx hss
  | while_ _ his => exact ⟨hv _ _, his.vokOf hv⟩
  | ret _ hvs => exact hvs.vokOf hv
  | var => exact fun _ _ _ _ _ _ => hv _ _
  | assign hts => exact ⟨hts.imp (fun _ _ _ _ _ _ _ _ _ => hv _ _), hv _ _⟩
  | call has => exact has.vokOf hv
  | icall _ _ has => exact ⟨hv _ _, has.vokOf hv⟩
  | isType => exact hv _ _
  | asType => exact hv _ _
  | refEq => exact ⟨hv _ _, hv _ _⟩
  | throw_ => exact hv _ _
  | try_ _ hcs => exact hcs.imp (fun _ _ _ _ _ _ _ => hv _ _)
  | assert => exact hv _ _
  | assume => exact hv _ _
  | old => exact hv _ _
  | incr => exact fun _ _ _ _ _ _ => hv _ _
  | compound => exact ⟨fun _ _ _ _ _ _ => hv _ _, hv _ _⟩
  | quant => exact hv _ _
  | @unsup v v' _ _ hu hu' =>
    cases v <;> simp only [Unsup] at hu <;> cases v' <;> simp only [Unsup] at hu' <;> trivial
  | _ => trivial

omit hp in
theorem nr_triv (hv : ∀ a b, Reserved.vok E a b) (hx : ∀ a ts, Reserved.vokX E a ts) {s t : StmtExprMd}
    (h : Shape E s t) (he : ExitOK Gl s) : NR E Rw Gl s t :=
  .inl ⟨h, he, valKids_triv hv hx h⟩

omit hp in
def LandRel (Gl : String → Prop) (ss ss' : List StmtExprMd) :
    Option (Nat × String × GotoDestination) → Option (Nat × String × GotoDestination) → Prop
  | none, none => True
  | some (j, l, d), some (j', l', d') => Gl l ∧ l = l' ∧ d = d' ∧ Corr E l ss ss' j j'
  | _, _ => False

theorem NR.ann {s t : StmtExprMd} (h : NR E Rw Gl s t) : (stackAnnotation? s).isNone = (stackAnnotation? t).isNone := by
  rcases h with ⟨hsh, -, -⟩ | hrw
  · exact Shape.ann _ hp.renAnn hsh
  · have := hp.rwLab _ _ hrw
    exact this.2.1.trans this.2.2.symm

theorem NR.labels {s t : StmtExprMd} (h : NR E Rw Gl s t) {l : String} (hl : ¬ Reserved.resLabel l) :
    (l ∈ statementLabels s ↔ l ∈ statementLabels t) := by
  rcases h with ⟨hsh, -, -⟩ | hrw
  · exact Shape.labels _ (fun a ts h => hp.exLab a ts h l hl) hsh (fun a b hab _ => hp.labE a b hab l hl)
  · have := (hp.rwLab _ _ hrw).1 l hl
    exact iff_of_false this.1 this.2

theorem fs_run1 {n M : Nat} (ih : FundAt cfg E Rw K Gl n) (hM : K * n ≤ M) :
    ∀ x y, E x y → OvOK G x → FS (Sm E Gl G) Eq
      (do modify fun (st : EvalState) => { st with stmtSite := x.source }
          if (stackAnnotation? x).isNone then withOperandWindow x (evalStmt cfg n x))
      (do modify fun (st : EvalState) => { st with stmtSite := y.source }
          if (stackAnnotation? y).isNone then withOperandWindow y (evalStmt cfg M y)) := by
  intro x y hxy hox
  have hann := (hp.closed x y hxy).ann hp
  refine fs_bind (fs_modifyRel (fun a a' ha => by strel ha)) (fun _ _ _ => ?_)
  by_cases h : (stackAnnotation? x).isNone = true
  · have h' : (stackAnnotation? y).isNone = true := hann ▸ h
    simp only [h, h', ite_true]
    exact fs_wow (ih.stmt _ _ (hp.closed _ _ hxy) hox M hM)
  · have h' : ¬ (stackAnnotation? y).isNone = true := hann ▸ h
    simp only [h, h']
    exact fs_pure rfl

theorem fs_landHandler {ss ss' : List StmtExprMd} (hss : LX E (Reserved.ex E) ss ss') (c : Control)
    (hc : CtlOK Gl G c) :
    FS (Sm E Gl G) (LandRel (E := E) Gl ss ss')
      ((fun (c : Control) => match c with
        | .jump_ l d =>
          (match ss.findIdx? (fun t => (statementLabels t).contains l) with
            | some j => pure (some (j, l, d))
            | none => throw (.jump_ l d) : EvalM PM (Option (Nat × String × GotoDestination)))
        | other => throw other) c)
      ((fun (c : Control) => match c with
        | .jump_ l d =>
          (match ss'.findIdx? (fun t => (statementLabels t).contains l) with
            | some j => pure (some (j, l, d))
            | none => throw (.jump_ l d) : EvalM PM (Option (Nat × String × GotoDestination)))
        | other => throw other) c) := by
  cases c with
  | jump_ l d =>
    have hnr := hp.glRes l hc
    have hf := LX.find (E := E) (fun a b h => hp.labE a b h l hnr) (fun a ts h => hp.exLab a ts h l hnr) hss
    dsimp only
    cases h1 : ss.findIdx? (fun t => (statementLabels t).contains l) <;>
      cases h2 : ss'.findIdx? (fun t => (statementLabels t).contains l) <;>
      rw [h1, h2] at hf <;> simp only [ORel] at hf
    · exact fs_throw _ hc
    · exact fs_pure ⟨hc, rfl, rfl, hf⟩
  | _ => exact fs_throw _ hc

theorem fstep_list {n : Nat} (ih : FundAt cfg E Rw K Gl n) (ihs : ∀ k ≤ n, FundAt cfg E Rw K Gl k) :
    ∀ ss ss' a, LX E (Reserved.ex E) ss ss' → (∀ x ∈ ss, OvOK G x) → ∀ M, K * (n + 1) ≤ M →
      FS (Sm E Gl G) (VRel (a = true → LXv E (Reserved.ex E) ss ss')) (evalStmtList cfg (n + 1) ss a)
        (evalStmtList cfg M ss' a) := by
  intro ss ss' a hss hov M' hM'
  obtain ⟨M, rfl, hM⟩ := fuel_split hp.K_pos hM'
  have run1 := fs_run1 hp ih hM (G := G)
  have runX : ∀ x ts, Reserved.ex E x ts → OvOK G x → FS (Sm E Gl G) Eq
      (do modify fun (st : EvalState) => { st with stmtSite := x.source }
          if (stackAnnotation? x).isNone then withOperandWindow x (evalStmt cfg n x))
      (ts.forM fun y => do
        modify fun (st : EvalState) => { st with stmtSite := y.source }
        if (stackAnnotation? y).isNone then withOperandWindow y (evalStmt cfg M y)) :=
    fun x ts hx hox => (hp.step n ihs).exStmt x ts hx hox M hM
  simp only [evalStmtList]
  refine fs_bind fs_get (fun σ σ' hσ => ?_)
  have hσ : StRel G (IxRel E) σ σ' := hσ
  simp only [hσ.coroSelf, hσ.coroSelf', Option.isNone_none, ite_true]
  cases a
  · simp only [Bool.false_eq_true, ite_false]
    refine fs_bind (fs_tryCatch (A := LandRel (E := E) Gl ss ss')
      (fs_bind (fs_forM_LX hss hov run1 runX) (fun _ _ _ => fs_pure trivial))
      (fun c hc => fs_landHandler hp hss c hc) ?_ (fun L hL hok => fs_throwTM hL hok) (fun w => fs_throwW w))
      (fun x y hxy => ?_)
    · intro σ τ
      simp [run_throw, OOF]
    · rcases x with _ | ⟨j, l, d⟩ <;> rcases y with _ | ⟨j', l', d'⟩ <;> simp only [LandRel] at hxy
      · exact fs_pure (fun _ => rfl)
      · obtain ⟨hGl, rfl, rfl, hc⟩ := hxy
        exact fs_bind fs_chargeStep (fun _ _ _ => fs_bind (ih.runFrom ss ss' j j' l d hc hov hGl M hM)
          (fun _ _ _ => fs_pure (fun _ => rfl)))
  · simp only [ite_true]
    by_cases hv : LXv E (Reserved.ex E) ss ss'
    · cases hv with
      | nil => exact fs_pure (fun _ => rfl)
      | @snoc_e i i' x y hi hxy hvxy =>
        have hoi : ∀ z ∈ i, OvOK G z := fun z hz => hov z (by simp [hz])
        have hox : OvOK G x := hov x (by simp)
        simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.singleton_append, List.reverse_reverse]
        exact fs_bind (fs_forM_LX hi hoi run1 runX) (fun _ _ _ =>
          fs_bind (fs_modifyRel (fun a a' ha => by strel ha))
            (fun _ _ _ => fs_wow ((exprMdE hp ih hxy hvxy hox hM).weaken (fun _ _ h _ => h))))
      | @snoc_x i i' ts x hi hx hvx =>
        have hoi : ∀ z ∈ i, OvOK G z := fun z hz => hov z (by simp [hz])
        have hox : OvOK G x := hov x (by simp)
        obtain ⟨ts0, t, rfl, hl⟩ := (hp.step n ihs).exLast x _ hx hox M hM
        simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.singleton_append, List.reverse_reverse]
        rw [List.cons_append]
        simp only [List.reverse_append, List.reverse_reverse]
        rw [lforM_append]
        simp only [bind_assoc]
        exact fs_bind (fs_forM_LX hi hoi run1 runX) (fun _ _ _ => hl.weaken (fun _ _ h _ => h hvx))
    · rcases hss.last with ⟨rfl, rfl⟩ | ⟨i, x, i', y, rfl, rfl, hi, hxy⟩ | ⟨i, x, i', ts, rfl, rfl, hi, hx⟩
      · exact fs_pure (fun _ => rfl)
      · have hoi : ∀ z ∈ i, OvOK G z := fun z hz => hov z (by simp [hz])
        have hox : OvOK G x := hov x (by simp)
        simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.singleton_append, List.reverse_reverse]
        exact fs_bind (fs_forM_LX hi hoi run1 runX) (fun _ _ _ =>
          fs_bind (fs_modifyRel (fun a a' ha => by strel ha))
            (fun _ _ _ => fs_wow ((ih.exprMd _ _ (hp.closed _ _ hxy) hox M hM).weaken (fun _ _ _ h => absurd (h (by simp)) hv))))
      · have hoi : ∀ z ∈ i, OvOK G z := fun z hz => hov z (by simp [hz])
        have hox : OvOK G x := hov x (by simp)
        obtain ⟨ts0, t, rfl, hl⟩ := (hp.step n ihs).exLast x _ hx hox M hM
        simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.singleton_append, List.reverse_reverse]
        rw [List.cons_append]
        simp only [List.reverse_append, List.reverse_reverse]
        rw [lforM_append]
        simp only [bind_assoc]
        exact fs_bind (fs_forM_LX hi hoi run1 runX) (fun _ _ _ => hl.weaken (fun _ _ _ h => absurd (h (by simp)) hv))

omit [Reserved] hp in
theorem blockDeclarations_append (l l' : List StmtExprMd) :
    blockDeclarations (l ++ l') = blockDeclarations l ++ blockDeclarations l' := by
  simp [Interpreter.blockDeclarations]

theorem LX.decls_ext {G : StackFrame} {ss ss' : List StmtExprMd} (h : LX E (Reserved.ex E) ss ss') :
    LooseExt G (Interpreter.blockDeclarations ss) (Interpreter.blockDeclarations ss') := by
  induction h with
  | nil => exact .nil
  | @cons a b as bs hab _ ih =>
    rw [blockDeclarations_cons a as, blockDeclarations_cons b bs]
    exact ((hp.closed _ _ hab).decl hp G).append ih
  | @expand a ts as bs hx _ ih =>
    rw [blockDeclarations_cons a as, blockDeclarations_append]
    exact (hp.exDecl G _ _ hx).append ih

theorem LX.decls_ok {ss ss' : List StmtExprMd} (h : LX E (Reserved.ex E) ss ss') :
    ∀ x ∈ Interpreter.blockDeclarations ss, ¬ Reserved.res x ∧ NotV x := by
  induction h with
  | nil => simp [Interpreter.blockDeclarations]
  | @cons a b as bs hab _ ih =>
    intro x hx
    rw [blockDeclarations_cons, List.mem_append] at hx
    rcases hx with hx | hx
    · exact (hp.closed _ _ hab).declOK hp x hx
    · exact ih x hx
  | @expand a ts as bs hx _ ih =>
    intro x hm
    rw [blockDeclarations_cons, List.mem_append] at hm
    rcases hm with hm | hm
    · exact hp.exDeclOK _ _ hx x hm
    · exact ih x hm

theorem fs_blockBody {n M : Nat} (ih : FundAt cfg E Rw K Gl n) (hM : K * n ≤ M) {ss ss' : List StmtExprMd}
    (hss : LX E (Reserved.ex E) ss ss') (hos : ∀ x ∈ ss, OvOK G x) :
    FS (Sm E Gl G) Eq (do let _ ← withBlockScope ss (evalStmtList cfg n ss (asExpr := false)); pure ())
      (do let _ ← withBlockScope ss' (evalStmtList cfg M ss' (asExpr := false)); pure ()) :=
  fs_bind (fs_wbs' (LX.decls_ext hp hss) (LX.decls_ok hp hss) ((ih.list _ _ _ hss (fun x hx => (hos x hx).relax _) M hM).weaken
    (fun _ _ h => h (fun e => absurd e (by decide))))) (fun _ _ _ => fs_pure rfl)

omit hp in
theorem fs_blockHandler {n M : Nat} (ih : FundAt cfg E Rw K Gl n) (hM : K * n ≤ M) {ss ss' : List StmtExprMd}
    (hss : LX E (Reserved.ex E) ss ss') (hlab : LabOK (some lab)) (hos : ∀ x ∈ ss, OvOK G x) (base base' : List Nat)
    (c : Control) (hc : CtlOK Gl G c) :
    FS (Sm E Gl G) Eq
      ((fun (c : Control) => match c with
        | .exit_ l =>
            if l == lab then
              modify fun (s : EvalState) => { s with cursor := base, seek := none }
            else throw (.exit_ l)
        | .goto_ l =>
            if l == lab then do
              modify fun (s : EvalState) => { s with cursor := base, seek := none }
              chargeStep
              evalBlockLoop cfg n ss lab [] base
            else throw (.goto_ l)
        | other => throw other : Control → EvalM PM Unit) c)
      ((fun (c : Control) => match c with
        | .exit_ l =>
            if l == lab then
              modify fun (s : EvalState) => { s with cursor := base', seek := none }
            else throw (.exit_ l)
        | .goto_ l =>
            if l == lab then do
              modify fun (s : EvalState) => { s with cursor := base', seek := none }
              chargeStep
              evalBlockLoop cfg M ss' lab [] base'
            else throw (.goto_ l)
        | other => throw other : Control → EvalM PM Unit) c) := by
  cases c with
  | exit_ l => exact fs_ite (fun _ => fs_modifyRel (fun a a' ha => by strel ha)) (fun _ => fs_throw _ hc)
  | goto_ l =>
    exact fs_ite (fun _ => fs_bind (fs_modifyRel (fun a a' ha => by strel ha)) (fun _ _ _ =>
      fs_bind fs_chargeStep (fun _ _ _ => ih.blockLoop ss ss' lab base base' hss hlab hos M hM))) (fun _ => fs_throw _ hc)
  | _ => exact fs_throw _ hc

theorem fstep_blockLoop {n : Nat} (ih : FundAt cfg E Rw K Gl n) :
    ∀ ss ss' lab base base', LX E (Reserved.ex E) ss ss' → LabOK (some lab) → (∀ x ∈ ss, OvOK G x) → ∀ M, K * (n + 1) ≤ M →
      FS (Sm E Gl G) Eq (evalBlockLoop cfg (n + 1) ss lab [] base) (evalBlockLoop cfg M ss' lab [] base') := by
  intro ss ss' lab base base' hss hlab hos M' hM'
  obtain ⟨M, rfl, hM⟩ := fuel_split hp.K_pos hM'
  simp only [evalBlockLoop, List.forIn_nil, pure_bind]
  refine fs_tryCatch (fs_blockBody hp ih hM hss hos) (fun c hc => fs_blockHandler ih hM hss hlab hos base base' c hc)
    ?_ (fun L hL hok => ?_) (fun w => fs_throwW w)
  · intro σ τ
    simp [run_throw, OOF]
  · have hne : (L == lab) = false := by
      have := hlab L hL
      simp only [beq_eq_false_iff_ne]
      exact fun h => this (by rw [h])
    simp only [hne, Bool.false_eq_true, ite_false]
    exact fs_throwM hL hok

theorem fstep_blockFrom {n : Nat} (ih : FundAt cfg E Rw K Gl n) :
    ∀ ss ss' bl k k' l d, Corr E l ss ss' k k' → LabOK (some bl) → (∀ x ∈ ss, OvOK G x) → Gl l → ∀ M, K * (n + 1) ≤ M →
      FS (Sm E Gl G) Eq (evalBlockFrom cfg (n + 1) ss bl [] k l d) (evalBlockFrom cfg M ss' bl [] k' l d) := by
  intro ss ss' bl k k' l d hc hlab hos hGl M' hM'
  obtain ⟨M, rfl, hM⟩ := fuel_split hp.K_pos hM'
  have hss : LX E (Reserved.ex E) ss ss' := by
    obtain ⟨pre, a, post, pre', b, post', rfl, rfl, -, -, h1, h2, h3, -⟩ := hc
    exact LX.append E h1 (.cons h2 h3)
  simp only [evalBlockFrom]
  refine fs_bind fs_get (fun σ σ' hσ => ?_)
  refine fs_withOpenLabel bl (fs_tryCatch (fs_wbs' (LX.decls_ext hp hss) (LX.decls_ok hp hss)
    (ih.runFrom ss ss' k k' l d hc (fun x hx => (hos x hx).relax _) hGl M hM))
    (fun c hc' => fs_blockHandler ih hM hss hlab hos σ.cursor σ'.cursor c hc') ?_ (fun L hL hok => ?_)
    (fun w => fs_throwW w))
  · intro σ τ
    simp [run_throw, OOF]
  · have hne : (L == bl) = false := by
      have := hlab L hL
      simp only [beq_eq_false_iff_ne]
      exact fun h => this (by rw [h])
    simp only [hne, Bool.false_eq_true, ite_false]
    exact fs_throwM hL hok

theorem fstep_runFrom {n : Nat} (ih : FundAt cfg E Rw K Gl n) (ihs : ∀ k ≤ n, FundAt cfg E Rw K Gl k) :
    ∀ ss ss' k k' l d, Corr E l ss ss' k k' → (∀ x ∈ ss, OvOK G x) → Gl l → ∀ M, K * (n + 1) ≤ M →
      FS (Sm E Gl G) Eq (runFrom cfg (n + 1) ss k l d) (runFrom cfg M ss' k' l d) := by
  intro ss ss' k k' l d hc hov hGl M' hM'
  obtain ⟨M, rfl, hM⟩ := fuel_split hp.K_pos hM'
  have hc0 := hc
  obtain ⟨pre, a, post, pre', b, post', rfl, rfl, rfl, rfl, hpre, hab, hpost, hla⟩ := hc
  have hss : LX E (Reserved.ex E) (pre ++ a :: post) (pre' ++ b :: post') := LX.append E hpre (.cons hab hpost)
  have run1 := fs_run1 hp ih hM (G := G)
  have runX : ∀ x ts, Reserved.ex E x ts → OvOK G x → FS (Sm E Gl G) Eq
      (do modify fun (st : EvalState) => { st with stmtSite := x.source }
          if (stackAnnotation? x).isNone then withOperandWindow x (evalStmt cfg n x))
      (ts.forM fun y => do
        modify fun (st : EvalState) => { st with stmtSite := y.source }
        if (stackAnnotation? y).isNone then withOperandWindow y (evalStmt cfg M y)) :=
    fun x ts hx hox => (hp.step n ihs).exStmt x ts hx hox M hM
  simp only [runFrom, List.drop_left]
  refine fs_bind (fs_tryCatch (A := LandRel (E := E) Gl (pre ++ a :: post) (pre' ++ b :: post'))
    (fs_bind (fs_modifyRel (fun a a' ha => by strel ha)) (fun _ _ _ =>
      fs_bind (ih.stmtFrom a b _ _ (hp.closed _ _ hab) (hov a (by simp)) hGl hla M hM) (fun _ _ _ =>
        fs_bind (fs_forM_LX hpost (fun x hx => hov x (by simp [hx])) run1 runX) (fun _ _ _ => fs_pure trivial))))
    (fun c hc => fs_landHandler hp hss c hc) ?_ (fun L hL hok => fs_throwM hL hok) (fun w => fs_throwW w))
    (fun x y hxy => ?_)
  · intro σ τ
    simp [run_throw, OOF]
  · rcases x with _ | ⟨j, l', d'⟩ <;> rcases y with _ | ⟨j', l'', d''⟩ <;> simp only [LandRel] at hxy
    · exact fs_pure rfl
    · obtain ⟨hGl', rfl, rfl, hc⟩ := hxy
      exact fs_bind fs_chargeStep (fun _ _ _ => ih.runFrom _ _ j j' l' d' hc hov hGl' M hM)

theorem fstep_stmtFrom {n : Nat} (ih : FundAt cfg E Rw K Gl n) :
    ∀ s t l d, NR E Rw Gl s t → OvOK G s → Gl l → l ∈ statementLabels s → ∀ M, K * (n + 1) ≤ M →
      FS (Sm E Gl G) Eq (evalStmtFrom cfg (n + 1) s l d) (evalStmtFrom cfg M t l d) := by
  intro s t l d hst hov hGl hl M' hM'
  obtain ⟨M, rfl, hM⟩ := fuel_split hp.K_pos hM'
  have hnr := hp.glRes l hGl
  rcases hst with ⟨hsh, hex, hvk⟩ | hrw
  · have hN : NR E Rw Gl s t := .inl ⟨hsh, hex, hvk⟩
    cases hsh with
    | @block ss ss' lab _ _ hss hlab =>
      have hos : ∀ x ∈ ss, OvOK G x := fun x hx => Hered.kid hov (by simp [stmtExprChildren, hx])
      simp only [evalStmtFrom]
      by_cases hb : (lab == some l) = true
      · simp only [hb, ite_true]
        cases d
        · exact ih.stmt _ _ hN hov M hM
        · exact fs_pure rfl
      · simp only [hb, Bool.false_eq_true, ite_false]
        have hf := LX.find (E := E) (fun a b h => hp.labE a b h l hnr) (fun a ts h => hp.exLab a ts h l hnr) hss
        have hmem : l ∈ (ss.map statementLabels).flatten := by
          rw [statementLabels_block, List.mem_append] at hl
          rcases hl with hl | hl
          · exact absurd (by cases lab <;> simp_all) hb
          · exact hl
        have hsome : (ss.findIdx? (fun t => (statementLabels t).contains l)).isSome = true := by
          rw [List.findIdx?_isSome]
          simp only [List.mem_flatten, List.mem_map] at hmem
          obtain ⟨_, ⟨t, ht, rfl⟩, hlt⟩ := hmem
          simp only [List.any_eq_true, List.contains_iff_mem]
          exact ⟨t, ht, hlt⟩
        revert hf hsome
        rcases h1 : ss.findIdx? (fun t => (statementLabels t).contains l) with _ | k <;>
          rcases h2 : ss'.findIdx? (fun t => (statementLabels t).contains l) with _ | k' <;> intro hc hsome <;>
          simp only [ORel, Option.isSome_none, Bool.false_eq_true] at hc hsome
        · simp only [List.findIdx_eq_getD_findIdx?, h1, h2, Option.getD_some]
          cases lab with
          | none =>
            exact fs_wbs' (LX.decls_ext hp hss) (LX.decls_ok hp hss)
              (ih.runFrom ss ss' k k' l d hc (fun x hx => (hos x hx).relax _) hGl M hM)
          | some bl => exact ih.blockFrom ss ss' bl k k' l d hc hlab hos hGl M hM
    | @ite c th c' th' el el' _ _ h1 h2 h3 =>
      have hth : (statementLabels th).contains l = (statementLabels th').contains l := by
        exact Bool.eq_iff_iff.mpr (by rw [List.contains_iff_mem, List.contains_iff_mem]; exact hp.labE _ _ h2 l hnr)
      simp only [evalStmtFrom, hth]
      split
      · rename_i hc
        exact ih.stmtFrom th th' l d (hp.closed _ _ h2) (Hered.kid hov (by simp [stmtExprChildren])) hGl
          ((hp.labE _ _ h2 l hnr).mpr (by simpa [List.contains_iff_mem] using hc)) M hM
      · rename_i hc
        rw [statementLabels_ite] at hl
        have hl' : l ∈ (el.map statementLabels).getD [] := by
          rcases List.mem_append.mp hl with h | h
          · exact absurd (by simpa [List.contains_iff_mem] using (hp.labE _ _ h2 l hnr).mp h) hc
          · exact h
        cases el <;> cases el' <;> simp only [ORel] at h3
        · simp at hl'
        · exact ih.stmtFrom _ _ l d (hp.closed _ _ h3) (Hered.kid hov (by simp [stmtExprChildren])) hGl
            (by simpa using hl') M hM
    | @unsup v v' _ _ hu hu' =>
      rw [statementLabels_other v _ (by intros; rintro rfl; exact hu) (by intros; rintro rfl; exact hu)] at hl
      cases hl
    | _ =>
      rw [statementLabels_other _ _ (by intros; nofun) (by intros; nofun)] at hl
      cases hl
  · exact absurd hl ((hp.rwLab s t hrw).1 l hnr).1

theorem fs_const {n M : Nat} (ih : FundAt cfg E Rw K Gl n) (hM : K * n ≤ M) {i i' : StmtExprMd} (hi : E i i')
    (hov : OvOK condG i) (hv : Reserved.vok E i i') :
    FS (Sm E Gl G) Eq
      (do
        let caller ← get
        modify fun (st : EvalState) => { st with stack := {}, cursor := [], seek := none, coroSelf := none, entryState := none }
        let v ← tryCatch (evalExprMd cfg n i) fun sig => do
          modify fun (st : EvalState) => { st with stack := caller.stack, globals := caller.globals, cursor := caller.cursor, seek := caller.seek, coroSelf := caller.coroSelf, entryState := caller.entryState }
          throw sig
        modify fun (st : EvalState) => { st with stack := caller.stack, globals := caller.globals, cursor := caller.cursor, seek := caller.seek, coroSelf := caller.coroSelf, entryState := caller.entryState }
        pure #[v])
      (do
        let caller ← get
        modify fun (st : EvalState) => { st with stack := {}, cursor := [], seek := none, coroSelf := none, entryState := none }
        let v ← tryCatch (evalExprMd cfg M i') fun sig => do
          modify fun (st : EvalState) => { st with stack := caller.stack, globals := caller.globals, cursor := caller.cursor, seek := caller.seek, coroSelf := caller.coroSelf, entryState := caller.entryState }
          throw sig
        modify fun (st : EvalState) => { st with stack := caller.stack, globals := caller.globals, cursor := caller.cursor, seek := caller.seek, coroSelf := caller.coroSelf, entryState := caller.entryState }
        pure #[v]) := by
  refine fs_bind fs_get (fun σ σ' hσ => ?_)
  have hσ : StRel G (IxRel E) σ σ' := hσ
  refine fs_switch (G' := condG) (fun a a' ha => by
    have := SR.freshC (gs := a.globals) Clean.empty; strel ha) ?_
  refine fs_bind (fs_tryCatch (exprMdE hp ih hi hv hov hM)
    (fun sig hsig => ?_) ?_ (fun L hL hok => ?_) (fun v => fs_noWin _ not_free_condG v)) (fun v v' hvv => ?_)
  · exact fs_switch (G := condG) (fun a a' ha => by
      have := hσ.stack; have := hσ.wf; have := hσ.gk; have := hσ.gk'; have := hσ.entR; have := hσ.globals; have := hσ.entryClean; have := hσ.egk; strelw ha [hσ.seek, hσ.seek', hσ.coroSelf, hσ.coroSelf', hσ.globals, hσ.ops, hσ.ops'])
      (fs_throwT _ (CtlOK.ofCond hsig))
  · intro σ τ
    simp [run_bind, run_throw, run_modify, OOF]
  · exact fs_switch (G := condG) (fun a a' ha => by
      have := hσ.stack; have := hσ.wf; have := hσ.gk; have := hσ.gk'; have := hσ.entR; have := hσ.globals; have := hσ.entryClean; have := hσ.egk; strelw ha [hσ.seek, hσ.seek', hσ.coroSelf, hσ.coroSelf', hσ.globals, hσ.ops, hσ.ops'])
      (fs_throwTM hL (CtlOK.ofCond (Gl := Gl) (c := .return_ []) hok))
  · subst hvv
    exact fs_bind (fs_switch1 (G := condG) (fun a a' ha => by
      have := hσ.stack; have := hσ.wf; have := hσ.gk; have := hσ.gk'; have := hσ.entR; have := hσ.globals; have := hσ.entryClean; have := hσ.egk; strelw ha [hσ.seek, hσ.seek', hσ.coroSelf, hσ.coroSelf', hσ.globals, hσ.ops, hσ.ops']))
      (fun _ _ _ => fs_pure rfl)

theorem fstep_callee {n : Nat} (ih : FundAt cfg E Rw K Gl n) :
    ∀ site site' c args, ¬ Reserved.resCall c → ∀ M, K * (n + 1) ≤ M →
      FS (Sm E Gl G) Eq (invokeCallee cfg (n + 1) site c args) (invokeCallee cfg M site' c args) := by
  intro site site' c args hc M' hM'
  obtain ⟨M, rfl, hM⟩ := fuel_split hp.K_pos hM'
  simp only [invokeCallee]
  refine fs_bind fs_get (fun σ σ' hσ => ?_)
  have hσ : StRel G (IxRel E) σ σ' := hσ
  rw [hσ.index.overloaded c.text (not_resProc_of_call hc)]
  have hl := hσ.index.callee c hc
  refine fs_ite (fun _ => fs_bind (fs_evalError (A := Eq) _ _) (fun _ _ _ => ?_))
    (fun _ => ?_)
  all_goals
    refine fs_ite (fun _ => fs_bind fs_allocateObject (fun a b h => by subst h; exact fs_pure rfl)) (fun _ => ?_)
    revert hl
    cases lookupCallee σ.index c <;> cases lookupCallee σ'.index c <;>
      simp only [ORel, false_implies, true_implies]
    · have hk := hσ.index.consts c.text (not_resProc_of_call hc)
      revert hk
      rcases σ.index.constants[c.text]? with _ | ⟨cn, ty, _ | i⟩ <;>
        rcases σ'.index.constants[c.text]? with _ | ⟨cn', ty', _ | i'⟩ <;>
        simp only [ORel, ConstRel, false_implies, true_implies, false_and] <;>
        (try exact fun _ => fs_evalError _ _)
      · exact fs_evalError _ _
      · rintro ⟨hi, hov, hv⟩
        exact fs_const hp ih hM hi (hov _ rfl) (hv _ _ rfl rfl)
    · exact fun h => ih.proc _ _ _ _ _ h.toB M hM

omit [Reserved] hp in
theorem L2.isEmpty_eq {R : α → β → Prop} {l : List α} {l' : List β} (h : L2 R l l') :
    l.isEmpty = l'.isEmpty := by
  cases h <;> rfl

omit [Reserved] hp in
theorem L2.of_map_eq {f : α → γ} {l l' : List α} (h : l.map f = l'.map f) :
    L2 (fun a b => f a = f b) l l' := by
  induction l generalizing l' with
  | nil => cases l' <;> simp at h; exact .nil
  | cons a as ih =>
    cases l' with
    | nil => simp at h
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at h
      exact .cons h.1 (ih h.2)

omit [Reserved] hp in
theorem L2.foldl_congr {R : α → β → Prop} {l : List α} {l' : List β} (h : L2 R l l')
    {F : δ → α → δ} {G : δ → β → δ} (hF : ∀ acc a b, R a b → F acc a = G acc b) (init : δ) :
    l.foldl F init = l'.foldl G init := by
  induction h generalizing init with
  | nil => rfl
  | cons hab _ ih => simp only [List.foldl_cons, hF _ _ _ hab, ih]

omit [Reserved] hp in
theorem L2.foldl_zip_congr {R : α → β → Prop} {l : List α} {l' : List β} (h : L2 R l l')
    {F : δ → α × γ → δ} {G : δ → β × γ → δ} (hF : ∀ acc a b c, R a b → F acc (a, c) = G acc (b, c))
    (xs : List γ) (init : δ) : (l.zip xs).foldl F init = (l'.zip xs).foldl G init := by
  induction h generalizing xs init with
  | nil => rfl
  | cons hab _ ih =>
    cases xs with
    | nil => rfl
    | cons x xs => simp only [List.zip_cons_cons, List.foldl_cons, hF _ _ _ _ hab, ih]

omit hp in
theorem L2.paramR_length {a b : List Parameter} (h : L2 ParamR a b) : b.length = a.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

omit hp in
theorem zipFold_sig {a b : List Parameter} (h : L2 ParamR a b) {F : StackFrame → Parameter × Value → StackFrame}
    (hF : ∀ acc x y v, x.name = y.name → F acc (x, v) = F acc (y, v)) (vs : List Value) (init : StackFrame) :
    (b.zip vs).foldl F init = (a.zip vs).foldl F init :=
  (L2.foldl_zip_congr h (fun acc x y c hxy => hF acc x y c hxy.1) vs init).symm

omit hp in
theorem head_sig {a b : List Parameter} (h : L2 ParamR a b) {f : Parameter → γ}
    (hf : ∀ x y, x.name = y.name → f x = f y) : b.head?.map f = a.head?.map f := by
  cases h with
  | nil => rfl
  | cons hxy _ => exact congrArg some (hf _ _ hxy.1).symm

omit hp in
theorem L2.paramR_single {a b : List Parameter} (h : L2 ParamR a b) {o : Parameter} (ha : a = [o]) :
    ∃ o', b = [o'] ∧ o.name = o'.name := by
  subst ha
  rcases h with _ | ⟨hxy, hr⟩
  cases hr
  exact ⟨_, rfl, hxy.1⟩

omit hp in
theorem all_sig {a b : List Parameter} (h : L2 ParamR a b) {f g : Parameter → Bool}
    (hfg : ∀ x y, ParamR x y → f x = g y) : a.all f = b.all g := by
  induction h with
  | nil => rfl
  | cons hxy _ ih => simp only [List.all_cons, ih, hfg _ _ hxy]

omit hp in
theorem foldl_names {a b : List Parameter} (h : L2 ParamR a b) {F : δ → Parameter → δ}
    (hF : ∀ acc x y, x.name = y.name → F acc x = F acc y) (init : δ) :
    b.foldl F init = a.foldl F init :=
  (L2.foldl_congr h (fun acc x y hxy => hF acc x y hxy.1) init).symm

omit hp in
theorem defaults_sig {a b : List Parameter} (h : L2 ParamR a b) {ix ix' : ProgramIndex} (hix : IxRel E ix ix')
    (init : StackFrame) :
    b.foldl (init := init) (fun acc o => if acc.contains o.name.text then acc
      else acc.insert o.name.text (defaultValue ix' o.type.val)) =
    a.foldl (init := init) (fun acc o => if acc.contains o.name.text then acc
      else acc.insert o.name.text (defaultValue ix o.type.val)) :=
  (L2.foldl_congr h (fun acc x y hxy => by rw [hxy.1, hix.defaultR hxy.2]) init).symm

omit hp in
theorem extract_sig {a b : List Parameter} (h : L2 ParamR a b) (f : StackFrame) :
    (b.toArray.map fun o => f[o.name.text]?.getD .unset) = (a.toArray.map fun o => f[o.name.text]?.getD .unset) := by
  simp only [List.map_toArray]
  rw [L2.map_eq h (f := fun o => f[o.name.text]?.getD .unset) (g := fun o => f[o.name.text]?.getD .unset)
    (fun x y hxy => by rw [hxy.1])]

omit hp in
theorem names_sig {a b : List Parameter} (h : L2 ParamR a b) : b.map (·.name) = a.map (·.name) :=
  (L2.map_eq h (fun _ _ hxy => hxy.1)).symm

omit hp in
theorem any_sig {a b : List Parameter} (h : L2 ParamR a b) (t : String) :
    b.any (·.name.text == t) = a.any (·.name.text == t) := by
  induction h with
  | nil => rfl
  | cons hxy _ ih => simp only [List.any_cons, ih, hxy.1]

omit hp in
theorem postOutputs_sig {P P' : Procedure} (h : L2 ParamR P.outputs P'.outputs) (r : Option Value) (xf : StackFrame) :
    postOutputs P' r xf = postOutputs P r xf := by
  unfold Interpreter.postOutputs
  generalize P.outputs = a at h
  generalize P'.outputs = b at h
  rcases h with _ | ⟨h1, _ | ⟨h2, hr⟩⟩
  · cases r <;> rfl
  · cases r
    · exact foldl_names (.cons h1 .nil) (fun acc x y h => by simp only [h]) _
    · simp only [h1.1]
  · cases r <;> exact foldl_names (.cons h1 (.cons h2 hr)) (fun acc x y h => by simp only [h]) _

theorem fs_checkConds {n M : Nat} (ih : FundAt cfg E Rw K Gl n) (hM : K * n ≤ M) (kind : CheckKind)
    (mk : Condition → Strata.Message) (mk' : Condition → Strata.Message)
    {cs cs' : List Condition} (hcs : L2 (CondRel E) cs cs') (hov : ∀ c ∈ cs, OvOK G c.condition) :
    FS (Sm E Gl G) Eq
      (forIn cs PUnit.unit fun c _ =>
        if c.mode.doesAssert = true then do
          let before ← get
          let v ← evalExprMd cfg n c.condition
          let holds ← liftM (Interpreter.isTrue cfg v)
          emitEvent (.check kind (some c.condition) (mk c) holds before)
          if holds then do
              pure PUnit.unit
              pure (ForInStep.yield PUnit.unit)
            else do
              modify fun st => { st with assertFailures := st.assertFailures.push (mk c) }
              pure (ForInStep.yield PUnit.unit)
        else do
          pure PUnit.unit
          pure (ForInStep.yield PUnit.unit))
      (forIn cs' PUnit.unit fun c _ =>
        if c.mode.doesAssert = true then do
          let before ← get
          let v ← evalExprMd cfg M c.condition
          let holds ← liftM (Interpreter.isTrue cfg v)
          emitEvent (.check kind (some c.condition) (mk' c) holds before)
          if holds then do
              pure PUnit.unit
              pure (ForInStep.yield PUnit.unit)
            else do
              modify fun st => { st with assertFailures := st.assertFailures.push (mk' c) }
              pure (ForInStep.yield PUnit.unit)
        else do
          pure PUnit.unit
          pure (ForInStep.yield PUnit.unit)) := by
  refine fs_forIn hcs.withMem (fun c c' ⟨hc, hm⟩ _ => ?_)
  rw [← hc.1]
  refine fs_ite (fun _ => ?_) (fun _ => fs_pure rfl)
  refine fs_bind fs_get (fun σ σ' hσ => ?_)
  refine fs_bind (exprMdE hp ih hc.2.1 hc.2.2 (hov c hm) hM) (fun v v' hv => ?_)
  subst hv
  refine fs_bind (fs_liftM (isTrue_pconst _)) (fun b b' hb => ?_)
  subst hb
  refine fs_bind (fs_emit (evRel_fail (E := _)) ⟨rfl, hc.2.1, rfl, _, hσ⟩) (fun _ _ _ => ?_)
  refine fs_ite (fun _ => fs_pure rfl) (fun _ => ?_)
  exact fs_bind (fs_modifyRel (fun a a' ha => by strel ha)) (fun _ _ _ => fs_pure rfl)

theorem fstep_pre {n : Nat} (ih : FundAt cfg E Rw K Gl n) :
    ∀ site site' P P' args, ProcRelB E P P' → ∀ M, K * (n + 1) ≤ M →
      FS (Sm E Gl G) Eq (checkPreconditions cfg (n + 1) site P args) (checkPreconditions cfg M site' P' args) := by
  intro site site' P P' args hP M' hM'
  obtain ⟨M, rfl, hM⟩ := fuel_split hp.K_pos hM'
  have hcs := hP.pre
  simp only [checkPreconditions]
  have hlen : P.preconditions.isEmpty =
      P'.preconditions.isEmpty := by
    exact hcs.isEmpty_eq
  rw [← hlen]
  refine fs_ite (fun _ => fs_pure rfl) (fun _ => ?_)
  refine ?_
  refine fs_bind fs_get (fun σ σ' hσ => ?_)
  have hσ : StRel G (IxRel E) σ σ' := hσ
  rw [hσ.muted]
  refine fs_ite (fun _ => fs_pure rfl) (fun _ => ?_)
  rw [zipFold_sig hP.inputs (fun acc x y v h => by simp only [h])]
  refine fs_switch (G' := condG) (fun a a' ha => by
    have := SR.freshC (gs := a.globals) (Clean.params P.inputs args hP.inNames); strel ha) ?_
  refine fs_bind (fs_tryCatch (fs_bind (fs_checkConds hp ih hM .precondition _ _ hcs
      (fun c hc => hP.preOK c hc)) (fun _ _ _ => fs_pure rfl))
    (fun sig hsig => ?_) ?_ (fun L hL hok => ?_) (fun v => fs_noWin _ not_free_condG v)) (fun _ _ _ => ?_)
  · exact fs_switch (G := condG) (fun a a' ha => by
      have := hσ.stack; have := hσ.wf; have := hσ.gk; have := hσ.gk'; have := hσ.entR; have := hσ.globals; have := hσ.entryClean; have := hσ.egk; strelw ha [hσ.seek, hσ.seek', hσ.coroSelf, hσ.coroSelf', hσ.globals, hσ.ops, hσ.ops'])
      (fs_throwT _ (CtlOK.ofCond hsig))
  · intro σ τ
    simp [run_bind, run_throw, run_modify, OOF]
  · exact fs_switch (G := condG) (fun a a' ha => by
      have := hσ.stack; have := hσ.wf; have := hσ.gk; have := hσ.gk'; have := hσ.entR; have := hσ.globals; have := hσ.entryClean; have := hσ.egk; strelw ha [hσ.seek, hσ.seek', hσ.coroSelf, hσ.coroSelf', hσ.globals, hσ.ops, hσ.ops'])
      (fs_throwTM hL (CtlOK.ofCond (Gl := Gl) (c := .return_ []) hok))
  · exact fs_switch1 (G := condG) (fun a a' ha => by
      have := hσ.stack; have := hσ.wf; have := hσ.gk; have := hσ.gk'; have := hσ.entR; have := hσ.globals; have := hσ.entryClean; have := hσ.egk; strelw ha [hσ.seek, hσ.seek', hσ.coroSelf, hσ.coroSelf', hσ.globals, hσ.ops, hσ.ops'])

theorem fstep_post {n : Nat} (ih : FundAt cfg E Rw K Gl n) :
    ∀ {G : StackFrame} P P' ps ps' fr fr' ef ent ent' xf xf' r r', ProcRelB E P P' → L2 (CondRel E) ps ps' →
      L2 (GroupRel E) fr fr' →
      (∀ c ∈ ps, OvOK condG c.condition) → postOutputs P r xf = postOutputs P' r' xf' →
      Clean ef → (∀ k, NG k → ent.2.contains k = false) → ent'.1 = ent.1 → GlR ent.2 ent'.2 →
      (∀ k, NG k → ent'.2.contains k = false) → (∀ k, ¬ Reserved.aliasOf G k) →
      (∀ k v, Reserved.frozenOf G k = some v → ent.2[k]? = some v) → ∀ M, K * (n + 1) ≤ M →
      FSH (Sm E Gl G) (Sm E Gl (Reserved.postOf G condG)) (Sm E Gl (Reserved.postOf G condG)) Eq
        (checkPostconditions cfg (n + 1) P ps fr ef ent xf r) (checkPostconditions cfg M P' ps' fr' ef ent' xf' r') := by
  intro G P P' ps ps' fr fr' ef ent ent' xf xf' r r' hP hps hfr hov hpo hef hent he1 he2 he3 hna hfz M' hM'
  obtain ⟨M, rfl, hM⟩ := fuel_split hp.K_pos hM'
  have hout : Clean (postOutputs P' r' xf') := by
    rw [postOutputs_sig hP.outputs]
    unfold Interpreter.postOutputs
    split
    · rename_i o _
      exact Clean.empty.insert (hP.outNames o (by simp_all)) _
    · exact Clean.empty.foldl _ _ (fun x hx => hP.outNames x hx)
  simp only [checkPostconditions]
  rw [hpo]
  simp only [any_sig hP.inputs]
  rw [foldl_names hP.outputs (fun acc x y h => by simp only [h])]
  refine fs_bind fs_get (fun σ σ' hσ => ?_)
  have hσ : StRel G (IxRel E) σ σ' := hσ
  have hPG : ∀ k v, Reserved.frozenOf (Reserved.postOf G condG) k = some v → Reserved.frozenOf G k = some v :=
    fun k v h => (Reserved.postOf_frozen G condG k v h).elim (fun h' => by rw [frozen_condG] at h'; cases h') id
  have hE : EntR (Reserved.postOf G condG) σ.entryState σ'.entryState :=
    hσ.entR.noAlias hna (noAlias_postOf G alias_condG) hPG (Reserved.entOK_postOf G condG alias_condG)
  have hW := (sameRegime_postOf G condG).wfg WFG.condG
  have hin : Clean (P.outputs.foldl (init := ({} : StackFrame)) fun acc o =>
      if P.inputs.any (·.name.text == o.name.text) then
        match ef[o.name.text]? with
        | some v => acc.insert o.name.text v
        | none => acc
      else acc) := by
    refine Clean.empty.foldl_gen (fun acc ha o ho => ?_)
    split
    · split
      · exact ha.insert (hP.outNames o ho) _
      · exact ha
    · exact ha
  refine fs_switch (G' := Reserved.postOf G condG) (fun a a' ha => by
    have := (SR.freshC (gs := a.globals) (Clean.fold hout hef)).ofRegime (sameRegime_postOf G condG)
      (fun k => (Reserved.postOf_alias G condG k)) (fun k v h => ha.stack.frozen k v (hPG k v h))
      (fun k => Reserved.loose_postOf G condG k) (fun k => Reserved.pin_postOf G condG k)
    have : EntR (Reserved.postOf G condG) (some (ent.1, ent.2, _)) (some (ent'.1, ent'.2, _)) :=
      ⟨he1, he2, he3, ⟨fun _ _ => rfl, fun k hk _ => hin k hk, fun k h => absurd h (noAlias_postOf G alias_condG k),
        fun k v h => hfz k v (hPG k v h), Reserved.entOK_postOf G condG alias_condG,
        inouts_keys (fun o ho hi => hP.inouts o ho hi) ef⟩⟩
    strel ha) ?_
  refine fs_bind (fs_tryCatch (fs_bind (B := Eq) (V := Sm E Gl (Reserved.postOf G condG)) (fs_checkConds hp ih hM .postcondition _ _ hps
      (fun c hc => (hov c hc).regime (sameRegime_postOf G condG) (Reserved.nodeOK_postOf G condG · alias_condG)))
    (fun _ _ _ => ?frames)) (fun sig hsig => ?_) ?_ (fun L hL hok => ?_)
    (fun v => fs_noWin _ (fun h => not_free_condG ((sameRegime_postOf G condG).free.mp h)) v))
    (fun _ _ _ => ?_)
  case frames =>
    have hreg : ∀ e, OvOK condG e → OvOK (Reserved.postOf G condG) e := fun e h =>
      h.regime (sameRegime_postOf G condG) (Reserved.nodeOK_postOf G condG · alias_condG)
    refine fs_bind (fs_forIn hfr (fun g g' hg _ => ?_)) (fun _ _ _ => fs_pure rfl)
    obtain ⟨hgd, hgv, hgo, hts⟩ := hg
    rcases g with ⟨ts, gd, sm⟩
    rcases g' with ⟨ts', gd', sm'⟩
    dsimp only at hgd hgv hgo hts ⊢
    cases gd <;> cases gd' <;> simp only [ORel] at hgd
    all_goals dsimp only
    · refine fs_bind (fs_pure rfl) (fun b b' hb => ?_)
      subst hb
      refine fs_ite (fun _ => ?_) (fun _ => fs_pure rfl)
      refine fs_bind (fs_mapM hts (fun t t' ht => ?_)) (fun cs cs' hcs => ?_)
      · rcases ht with ⟨o, f, sx, o', f', sx', rfl, rfl, hf, ho, hov, hoo⟩ | ⟨hn, hn', hE, hv, hov⟩
        · exact fs_bind (exprMdE hp ih ho hov (hreg _ hoo) hM) (fun v v' hv => by subst hv; simp only [strictField_none hp.cfg_ok.strict]; rw [hf]; exact fs_pure rfl)
        · split <;> (try split) <;> first
            | exact absurd (by assumption) (hn _ _)
            | exact absurd (by assumption) (hn' _ _)
            | exact fs_bind (exprMdE hp ih hE hv (hreg _ hov) hM) (fun v v' hv => by subst hv; exact fs_pure rfl)
      · subst hcs
        refine fs_bind fs_get (fun σ σ' hσ => ?_)
        have hσ : StRel (Reserved.postOf G condG) (IxRel E) σ σ' := hσ
        rw [hσ.heap, he1]
        refine fs_bind (fs_emit (evRel_fail (E := _)) ⟨rfl, trivial, rfl, _, hσ⟩) (fun _ _ _ => ?_)
        refine fs_ite (fun _ => fs_pure rfl) (fun _ => ?_)
        exact fs_bind (fs_modifyRel (fun a a' ha => by strel ha)) (fun _ _ _ => fs_pure rfl)
    · refine fs_bind (exprMdE hp ih hgd (hgv _ _ rfl rfl) (hreg _ (hgo _ rfl)) hM) (fun v v' hv => ?_)
      subst hv
      refine fs_bind (fs_liftM (isTrue_pconst _)) (fun b b' hb => ?_)
      subst hb
      refine fs_ite (fun _ => ?_) (fun _ => fs_pure rfl)
      refine fs_bind (fs_mapM hts (fun t t' ht => ?_)) (fun cs cs' hcs => ?_)
      · rcases ht with ⟨o, f, sx, o', f', sx', rfl, rfl, hf, ho, hov, hoo⟩ | ⟨hn, hn', hE, hv, hov⟩
        · exact fs_bind (exprMdE hp ih ho hov (hreg _ hoo) hM) (fun v v' hv => by subst hv; simp only [strictField_none hp.cfg_ok.strict]; rw [hf]; exact fs_pure rfl)
        · split <;> (try split) <;> first
            | exact absurd (by assumption) (hn _ _)
            | exact absurd (by assumption) (hn' _ _)
            | exact fs_bind (exprMdE hp ih hE hv (hreg _ hov) hM) (fun v v' hv => by subst hv; exact fs_pure rfl)
      · subst hcs
        refine fs_bind fs_get (fun σ σ' hσ => ?_)
        have hσ : StRel (Reserved.postOf G condG) (IxRel E) σ σ' := hσ
        rw [hσ.heap, he1]
        refine fs_bind (fs_emit (evRel_fail (E := _)) ⟨rfl, trivial, rfl, _, hσ⟩) (fun _ _ _ => ?_)
        refine fs_ite (fun _ => fs_pure rfl) (fun _ => ?_)
        exact fs_bind (fs_modifyRel (fun a a' ha => by strel ha)) (fun _ _ _ => fs_pure rfl)
  · exact fs_bind (fs_modifyRel (fun a a' ha => by have := hσ.entryClean; have := hσ.egk; have := hE; strel ha))
      (fun _ _ _ => fs_throw _ hsig)
  · intro σ τ
    simp [run_bind, run_throw, run_modify, OOF]
  · exact fs_bind (fs_modifyRel (fun a a' ha => by have := hσ.entryClean; have := hσ.egk; have := hE; strel ha))
      (fun _ _ _ => fs_throwM hL hok)
  · exact fs_modifyRel (fun a a' ha => by have := hσ.entryClean; have := hσ.egk; have := hE; strel ha)

omit hp in
theorem undetermined_congr {P P' : Procedure} (hP : ProcRelB E P P') {b b' : Body}
    (h : (bodyModifies b).any (!·.targets.isEmpty) = (bodyModifies b').any (!·.targets.isEmpty)) :
    undeterminedOf P' b' = undeterminedOf P b := by
  unfold undeterminedOf
  rw [head_sig hP.outputs (fun x y h => by simp only [h]), ← hP.writes, ← hP.throws, h]

omit hp in
theorem fs_bodiless {P P' : Procedure} (hP : ProcRelB E P P') :
    FS (Sm E Gl G) Eq
      (do
        let st ← get
        P.outputs.toArray.mapM fun o =>
          chooseValue (some (st.index.unalias o.type.val)) (defaultValue st.index o.type.val) : EvalM PM (Array Value))
      (do
        let st ← get
        P'.outputs.toArray.mapM fun o =>
          chooseValue (some (st.index.unalias o.type.val)) (defaultValue st.index o.type.val)) := by
  refine fs_bind fs_get (fun σ σ' hσ => ?_)
  have hσ : StRel G (IxRel E) σ σ' := hσ
  simp only [Array.mapM_eq_mapM_toList, map_eq_pure_bind]
  refine fs_bind (fs_mapM hP.outputs (fun a b hab => ?_)) (fun _ _ h => fs_pure (by rw [h]))
  rw [hσ.index.defaultR hab.2]
  exact fs_choose _ _ _

omit hp in
theorem callee_clean {P P' : Procedure} (hP : ProcRelB E P P') (args : List Value) (ix : ProgramIndex) :
    Clean (P.outputs.foldl (init := (P.inputs.zip args).foldl (fun acc (param, v) => acc.insert param.name.text v) {})
      fun acc o => if acc.contains o.name.text then acc else acc.insert o.name.text (defaultValue ix o.type.val)) := by
  refine (Clean.params P.inputs args hP.inNames).foldl_gen (fun acc ha o ho => ?_)
  split
  · exact ha
  · exact ha.insert (hP.outNames o ho) _

theorem decls_eq (hL : Reserved.retLabel ≠ none) {ss ss' : List StmtExprMd} (h : L2 E ss ss') :
    Interpreter.blockDeclarations ss = Interpreter.blockDeclarations ss' :=
  h.blockDeclarations (fun s t hst => (hp.closed s t hst).declEq hp hL)

theorem decls_ok {ss ss' : List StmtExprMd} (h : L2 E ss ss') :
    ∀ x ∈ Interpreter.blockDeclarations ss, ¬ Reserved.res x ∧ NotV x := by
  induction h with
  | nil => simp [Interpreter.blockDeclarations]
  | @cons a b as bs hab _ ih =>
    intro x hx
    rw [blockDeclarations_cons, List.mem_append] at hx
    rcases hx with hx | hx
    · exact (hp.closed _ _ hab).declOK hp x hx
    · exact ih x hx

theorem wrap_block {n : Nat} (ihs : ∀ k ≤ n, FundAt cfg E Rw K Gl k) {ss ss' : List StmtExprMd}
    {s s' : FileRange} {L : String} (hL : Reserved.retLabel = some L) (hss : L2 E ss ss') :
    ∀ M, K * (n + 1) ≤ M + 1 →
      FSH (Sm E Gl {}) (Sm E Gl {}) (Sm0 E Gl {}) Eq (runB (evalStmt cfg n ⟨.Block ss none [] none, s⟩))
        (runB (evalStmt cfg M ⟨.Block ss' (some L) [] none, s'⟩)) := by
  intro M hM
  cases n with
  | zero => exact ⟨fun σ _ τ _ _ _ hn => absurd (by simp [runB, evalStmt, run_tryCatch, run_throw, OOF]) hn⟩
  | succ n1 =>
    have := hp.K_pos
    simp only [Nat.mul_succ] at hM
    obtain ⟨M1, rfl⟩ : ∃ M1, M = M1 + 1 := ⟨M - 1, by omega⟩
    have hvn := hp.retV (by rw [hL]; simp)
    refine body_wrap hL (hp.retGl L hL) hvn (hp.retRes L hL) (fs_wrapBlock_inner (fs_wbs' (.ofEq (decls_eq hp (by rw [hL]; simp) hss)) (decls_ok hp hss)
      (((ihs n1 (by omega)).list _ _ _ (LX.ofL2 _ hss) (fun x _ => ovOK_none hvn _ x (hp.retHook (by rw [hL]; simp))) M1 (by omega)).weaken
        (fun _ _ h => h (fun e => absurd e (by decide))))))

theorem wrap_other {n : Nat} (ih : FundAt cfg E Rw K Gl n) {b b' : StmtExprMd} {s' : FileRange} {L : String}
    (hL : Reserved.retLabel = some L) (hb : E b b') (hd : blockDeclarations [b] = [])
    (hlb : ∀ l, ¬ Reserved.resLabel l → l ∉ statementLabels b) (hann : (stackAnnotation? b).isNone = true) :
    ∀ M, K * (n + 1) ≤ M + 1 →
      FSH (Sm E Gl {}) (Sm E Gl {}) (Sm0 E Gl {}) Eq (runB (evalStmt cfg n b))
        (runB (evalStmt cfg M ⟨.Block [b'] (some L) [] none, s'⟩)) := by
  intro M hM
  have hK := hp.retK (by rw [hL]; simp)
  simp only [Nat.mul_succ] at hM
  obtain ⟨M2, rfl⟩ : ∃ M2, M = M2 + 2 := ⟨M - 2, by omega⟩
  have hd' : blockDeclarations [b'] = [] := by rw [← NR.declEq hp (by rw [hL]; simp) (hp.closed _ _ hb)]; exact hd
  have hvn := hp.retV (by rw [hL]; simp)
  have hl' : ∀ l, Gl l → l ∉ statementLabels b' := fun l hl h =>
    hlb l (hp.glRes l hl) (((hp.closed _ _ hb).labels hp (hp.glRes l hl)).mpr h)
  have hann' : (stackAnnotation? b').isNone = true := ((hp.closed _ _ hb).ann hp) ▸ hann
  exact body_wrap hL (hp.retGl L hL) hvn (hp.retRes L hL) (cfg := cfg) (fs_wrapOther_inner hd' hl' hann'
    (ih.stmt _ _ (hp.closed _ _ hb) (ovOK_none hvn _ _ (hp.retHook (by rw [hL]; simp))) M2 (by omega)))

theorem wrap_valued {n : Nat} (ihs : ∀ k ≤ n, FundAt cfg E Rw K Gl k) {e e' : StmtExprMd} {o : Parameter}
    {s s' s1 s2 s3 : FileRange} {L : String} (hL : Reserved.retLabel = some L) (he : E e e') (hy : NotYield e') :
    ∀ M, K * (n + 1) ≤ M + 1 →
      FSV (Sm E Gl {}) (Sm E Gl {}) (Sm0 E Gl {}) (VA E o) (runB (evalStmt cfg n ⟨.Return [e], s⟩))
        (runB (evalStmt cfg M ⟨.Block [⟨.Assign [⟨.Local o.name, s1⟩] e', s2⟩, ⟨.Goto L .blockEnd, s3⟩] (some L) [] none, s'⟩)) := by
  intro M hM
  have hK := hp.retK (by rw [hL]; simp)
  cases n with
  | zero =>
    exact ⟨fun σ _ τ _ _ _ hn => absurd (by simp [runB, evalStmt, run_tryCatch, run_throw, OOF]) hn⟩
  | succ n1 =>
    simp only [Nat.mul_succ] at hM
    obtain ⟨M4, rfl⟩ : ∃ M4, M = M4 + 4 := ⟨M - 4, by omega⟩
    have hvn := hp.retV (by rw [hL]; simp)
    refine body_valued_gen hL (hp.retGl L hL) (hp.retNG (by rw [hL]; simp)) hvn (hp.retRes L hL) ?_ rfl (by simp [blockDeclarations])
      (by simp [stackAnnotation?]) (statementLabels_other _ _ (by intros; nofun) (by intros; nofun))
      (exprMdE hp (ihs n1 (by omega)) he (hp.retVok (by rw [hL]; simp) _ _) (ovOK_none hvn _ _ (hp.retHook (by rw [hL]; simp))) (by omega))
    rw [evalStmt_assign1 hy _ rfl]
    simp only [assignTarget, writeUpdate, pure_bind]

set_option linter.unusedSimpArgs false in
theorem wrap_valuedB {n : Nat} (ihs : ∀ k ≤ n, FundAt cfg E Rw K Gl k) {e e' : StmtExprMd} {o : Parameter}
    {s s' s0 s1 s2 s3 s4 : FileRange} {L : String} (hL : Reserved.retLabel = some L) (he : E e e')
    (hy : NotYield e') :
    ∀ M, K * (n + 1) ≤ M + 1 →
      FSV (Sm E Gl {}) (Sm E Gl {}) (Sm0 E Gl {}) (VA E o)
        (runB (evalStmt cfg n ⟨.Block [⟨.Return [e], s0⟩] none [] none, s⟩))
        (runB (evalStmt cfg M
          ⟨.Block [⟨.Block [⟨.Assign [⟨.Local o.name, s1⟩] e', s2⟩, ⟨.Goto L .blockEnd, s3⟩] none [] none, s4⟩] (some L) [] none, s'⟩)) := by
  intro M hM
  have hK := hp.retK (by rw [hL]; simp)
  rcases n with _ | _ | _ | n1
  · exact ⟨fun σ σ' τ _ hs _ hn => absurd (by
      have hs' : StRel {} (IxRel E) σ σ' := hs
      have hd0 : blockDeclarations [(⟨.Return [e], s0⟩ : StmtExprMd)] = [] := by simp [blockDeclarations]
      simp [runB, evalStmt, run_tryCatch, run_throw, run_bind, run_get, evalStmtList, run_chargeStep hs'.steps,
        hs'.coroSelf, withBlockScope_nil hd0, run_modify, withOperandWindow, hs'.ops, stackAnnotation?, OOF]) hn⟩
  · exact ⟨fun σ σ' τ _ hs _ hn => absurd (by
      have hs' : StRel {} (IxRel E) σ σ' := hs
      have hd0 : blockDeclarations [(⟨.Return [e], s0⟩ : StmtExprMd)] = [] := by simp [blockDeclarations]
      simp [runB, evalStmt, run_tryCatch, run_throw, run_bind, run_get, evalStmtList, run_chargeStep hs'.steps,
        hs'.coroSelf, withBlockScope_nil hd0, run_modify, withOperandWindow, hs'.ops, stackAnnotation?, OOF]) hn⟩
  · exact ⟨fun σ σ' τ _ hs _ hn => absurd (by
      have hs' : StRel {} (IxRel E) σ σ' := hs
      have hd0 : blockDeclarations [(⟨.Return [e], s0⟩ : StmtExprMd)] = [] := by simp [blockDeclarations]
      simp [runB, evalStmt, run_tryCatch, run_throw, run_bind, run_get, evalStmtList, run_chargeStep hs'.steps,
        hs'.coroSelf, withBlockScope_nil hd0, run_modify, withOperandWindow, hs'.ops, stackAnnotation?, OOF]) hn⟩
  simp only [Nat.mul_succ] at hM
  obtain ⟨M6, rfl⟩ : ∃ M6, M = M6 + 6 := ⟨M - 6, by omega⟩
  have hvn := hp.retV (by rw [hL]; simp)
  refine body_valuedB_gen hL (hp.retGl L hL) (hp.retNG (by rw [hL]; simp)) hvn (hp.retRes L hL) ?_ rfl (by simp [blockDeclarations])
      (by simp [stackAnnotation?]) (statementLabels_other _ _ (by intros; nofun) (by intros; nofun))
    (exprMdE hp (ihs n1 (by omega)) he (hp.retVok (by rw [hL]; simp) _ _) (ovOK_none hvn _ _ (hp.retHook (by rw [hL]; simp))) (by omega))
  rw [evalStmt_assign1 hy _ rfl]
  simp only [assignTarget, writeUpdate, pure_bind]

omit hp in
theorem postOutputs_congr {P P' : Procedure} (hP : ProcRelB E P P') {G' xf xf' : StackFrame} {gs' : Std.HashMap String Value} (hx : SR G' gs' xf xf')
    (hv : ∀ x ∈ P.outputs, NotV x.name.text) (r : Option Value) :
    postOutputs P r xf = postOutputs P' r xf' := by
  rw [postOutputs_sig hP.outputs]
  unfold Interpreter.postOutputs
  split
  · rfl
  · exact (hx.outsFold hP.outNames (fun x h => .inl (hv x h)) _).symm

omit hp in
theorem outV_void {P P' : Procedure} (hP : ProcRelB E P P') (hv : valued P = false) :
    ∀ x ∈ P.outputs, NotV x.name.text := fun x hx => (hP.outV x hx).resolve_right (by rw [hv]; simp)

omit [Reserved] hp in
theorem fsh_nc {S T U : SimRel} {x y : EvalM PM Unit} (h : FSH S T U Eq x y)
    (hnc : ∀ σ τ σ' τ', run x σ τ ≠ .ok ((.ok (), σ'), τ')) : FSH S T U (fun _ _ => False) x y := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have r := h.sim σ σ' τ τ' hs ht hn
  revert r
  rcases hx : run x σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;> rcases run y σ' τ' with e' | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;>
    simp only [RR, ExRel, imp_self, false_and]
  exact absurd hx (hnc _ _ _ _)

omit hp in
theorem postOutputs_some {P P' : Procedure} (hP : ProcRelB E P P') (hv : valued P = true) (v : Value)
    (xf xf' : StackFrame) : postOutputs P (some v) xf = postOutputs P' (some v) xf' := by
  obtain ⟨o, x, ho, hx, hxo⟩ := valued_outputs hv
  rw [postOutputs_sig hP.outputs]
  unfold Interpreter.postOutputs
  rw [hx]

omit hp in
theorem postOutputs_win {P P' : Procedure} (hP : ProcRelB E P P') (hv : valued P = true) (v : Value)
    (xf : StackFrame) {xf' : StackFrame} (hx' : ∀ o, Reserved.vret = some o → xf'[o]? = some v) :
    postOutputs P (some v) xf = postOutputs P' none xf' := by
  obtain ⟨o, x, ho, hx, hxo⟩ := valued_outputs hv
  rw [postOutputs_sig hP.outputs]
  unfold Interpreter.postOutputs
  rw [hx]
  have := hx' o ho
  rw [← hxo] at this
  simp [this]

omit hp in
theorem outputs_win {P : Procedure} (hv : valued P = true) {v : Value} {f : StackFrame}
    (hf : ∀ o, Reserved.vret = some o → f[o]? = some v) :
    P.outputs.toArray.map (fun o => f[o.name.text]?.getD .unset) = #[v] := by
  obtain ⟨o, x, ho, hx, hxo⟩ := valued_outputs hv
  rw [hx]
  have hval := hf o ho
  rw [← hxo] at hval
  simp [hval]

omit hp in
theorem procG_void {P : Procedure} (hv : valued P = false) : procG P = {} := by simp [procG, hv]

set_option hygiene false in
macro "rstr" : tactic => `(tactic| (
  have : SR G a.globals c.stack c'.stack := by
    first
    | exact hc.stack.restorePost ha.stack
    | exact hc.stack.restoreFz ha.stack
    | exact hc.stack.regs (by assumption) a.globals
  have := hc.wf; have := hc.gk; have := hc.gk'; have := hc.entR; have := hc.globals; have := hc.entryClean
  have := hc.egk
  strelw ha [hc.coroSelf, hc.coroSelf', hc.seek, hc.seek', hc.ops, hc.ops']))

set_option hygiene false in
macro "proc_post" hps:term:max hpo:term:max hov:term:max : tactic => `(tactic| (
  refine fs_bind (fs_tryCatch (ih.post _ _ _ _ _ _ _ _ _ _ _ _ _ hP $hps hP.frames $hov $hpo (callee_clean hP args s0.index)
      (fun k hg => by first | exact hcur.gk k hg | (split <;> simp [hcur.gk k hg]))
      (by first | rfl | (split <;> first | rfl | exact hcur.heap))
      (by first | exact hcur.globals | (split <;> first | exact GlR.refl _ | exact hcur.globals))
      (fun k hg => by first | exact hcur.gk' k hg | (split <;> simp [hcur.gk' k hg]))
      (by first | exact Reserved.alias_empty | exact noAlias_freeze _ _ Reserved.alias_empty | exact noAlias_freeze _ _ alias_freeG)
      (fun k v hk => by first | (rw [Reserved.frozen_empty] at hk; cases hk) | (split <;> first | contradiction | exact hcur.stack.frozen k v hk)) M hM)
      (fun sig hsig => fs_switch (G := _) (fun a a' ha => by
        rstr)
        (fs_throwT sig (CtlOK.ofCond (hsig.regime (sameRegime_postOf _ condG).symm)))) ?_ (fun L hL hok => fs_switch (G := _) (fun a a' ha => by
        rstr)
        (fs_throwTM hL (CtlOK.ofCond (Gl := Gl) (c := .return_ []) (CtlOK.regime hok (sameRegime_postOf _ condG).symm))))
        (fun v => fs_noWin _ (fun h => not_free_condG ((sameRegime_postOf _ condG).free.mp h)) v))
      (fun _ _ _ => fs_bind (fs_switch1 (G := _) (fun a a' ha => by
        rstr))
        (fun _ _ _ => ?_))
  · intro σ τ
    simp [run_bind, run_throw, run_modify, OOF]))

set_option hygiene false in
macro "proc_rest" hn:ident h:ident hps:term:max hov:term:max hbo:term:max hvo:term:max : tactic => `(tactic| (
  refine fs_bind (fs_pure (A := fun a b => E a b ∧ OvOK {} a) ⟨$h, $hbo⟩) (fun y y' hy => ?_)
  refine fs_bind fs_get (fun s0 s0' h0 => ?_)
  refine fs_withLabels (fun _ => []) (fun _ => []) (fun _ _ _ _ _ => Iff.rfl) ?_
  refine fs_getAt (fun c c' hc => ?_)
  have h0 : StRel G (IxRel E) s0 s0' := h0
  have hc : StRel G (IxRel E) c c' := hc
  simp only [defaults_sig hP.outputs h0.index]
  refine fs_switchAt (G' := Reserved.freeze G c.globals {}) (fun ha => by
    have := (SR.fresh (gs := c.globals) (callee_clean hP args s0.index)).ofRegime (sameRegime_freeze G c.globals {})
      (fun k => Reserved.freeze_alias G c.globals {} k)
      (fun k v h => (Reserved.freeze_frozen G c.globals {} k v h).elim
        (fun h' => by rw [Reserved.frozen_empty] at h'; cases h') id)
      (fun k => Reserved.loose_freeze G c.globals {} k) (fun k => Reserved.pin_freeze G c.globals {} k)
    have := (sameRegime_freeze G c.globals {}).wfg WFG.empty
    strel ha) ?_
  refine fs_bind fs_get (fun cur cur' hcur => ?_)
  have hcur : StRel (Reserved.freeze G c.globals {}) (IxRel E) cur cur' := hcur
  simp only [entrySnapshot, hcur.heap]
  refine fs_bind (fs_tryCatch (fs_bind (ih.stmt _ _ (hp.closed _ _ hy.1)
      (hy.2.regime (sameRegime_freeze G c.globals {}) (Reserved.nodeOK_freeze G c.globals {} · Reserved.alias_empty)) M hM)
      (fun _ _ _ => fs_pure rfl))
    (fun sig hsig => ?_) ?_ (fun L hL _ => absurd (($hn).symm.trans hL) (by simp))
    (fun v => fs_noWin _ (fun h => not_free_empty ((sameRegime_freeze G c.globals {}).free.mp h)) v)) (fun r r' hr => ?_)
  · cases sig <;> first
      | (rename_i vs; rcases vs with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> first | exact fs_pure rfl | exact (hsig : False).elim)
      | exact fs_pure rfl
      | exact fs_switch (G := _) (fun a a' ha => by
          rstr)
          (fs_throwT _ hsig)
  · intro σ τ
    simp [run_bind, run_throw, run_modify, OOF]
  · subst hr
    refine fs_bind fs_get (fun f f' hf => ?_)
    have hf : StRel (Reserved.freeze G c.globals {}) (IxRel E) f f' := hf
    have hpf := ($hps)
    simp only [hpf.isEmpty_eq, hP.frames.isEmpty_eq, hf.stack.outs hP.outNames (fun x hx => .inl ($hvo x hx))]
    refine fs_ite (fun _ => ?_) (fun _ => ?_)
    · refine fs_bind (fs_switch1 (G := _) (G' := G) (fun a a' ha => by
        rstr))
        (fun _ _ _ => ?_)
      cases r <;> exact fs_pure rfl
    · proc_post hpf (postOutputs_congr hP hf.stack $hvo r)
        (fun c hc => $hov c hc)
      cases r <;> exact fs_pure rfl))

omit [Reserved] hp in
theorem FSH.pre {S S' T U : SimRel} {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β} (h : FSH S' T U A x y)
    (hs : ∀ σ σ', S.st σ σ' → S'.st σ σ') (he : S.ev = S'.ev) : FSH S T U A x y :=
  h.reg hs he (fun _ _ h => h) rfl (fun _ _ _ _ h => h) rfl

omit hp in
theorem not_strict_freeG {o : String} (ho : Reserved.vret = some o) : ¬ Strict freeG :=
  fun h => (h o ho).1 (by obtain ⟨o', ho', hc⟩ := freeG_free ho; rw [ho] at ho'; cases ho'; exact hc)

set_option hygiene false in
macro "proc_restE" hn:ident h:ident hps:term:max hov:term:max hbo:term:max hnc:term:max hv:term:max :
    tactic => `(tactic| (
  refine fs_bind (fs_pure (A := fun a b => E a b ∧ OvOK freeG a ∧ NC a) ⟨$h, $hbo, $hnc⟩) (fun y y' hy => ?_)
  refine fs_bind fs_get (fun s0 s0' h0 => ?_)
  refine fs_withLabels (fun _ => []) (fun _ => []) (fun _ _ _ _ _ => Iff.rfl) ?_
  refine fs_getAt (fun c c' hc => ?_)
  have h0 : StRel G (IxRel E) s0 s0' := h0
  have hc : StRel G (IxRel E) c c' := hc
  simp only [defaults_sig hP.outputs h0.index]
  refine fs_switchAt (G' := Reserved.freeze G c.globals freeG) (fun ha => by
    have := (SR.freshF (gs := c.globals) (callee_clean hP args s0.index)).ofRegime
      (sameRegime_freeze G c.globals freeG) (fun k => Reserved.freeze_alias G c.globals freeG k)
      (fun k v h => (Reserved.freeze_frozen G c.globals freeG k v h).elim
        (fun h' => by rw [frozen_freeG] at h'; cases h') id)
      (fun k => Reserved.loose_freeze G c.globals freeG k) (fun k => Reserved.pin_freeze G c.globals freeG k)
    have := (sameRegime_freeze G c.globals freeG).wfg WFG.freeG
    strel ha) ?_
  refine fs_bind fs_get (fun cur cur' hcur => ?_)
  have hcur : StRel (Reserved.freeze G c.globals freeG) (IxRel E) cur cur' := hcur
  simp only [entrySnapshot, hcur.heap]
  obtain ⟨vo, vx, hvo, hvx, hvxo⟩ := valued_outputs $hv
  refine fs_bindV (T := Sm E Gl (Reserved.freeze G c.globals freeG)) (A := fun (r r' : Option Value) σ σ' =>
      (r = r' ∧ r ≠ none ∧ StRel (Reserved.freeze G c.globals freeG) (IxRel E) σ σ') ∨
      (∃ w, r = some w ∧ r' = none ∧ (Sm E Gl (Reserved.freeze G c.globals freeG)).win w σ σ'))
    (fs_tryCatchVW (FSV.ofFSH (A' := fun _ _ => False)
        (fs_bind (fsh_nc (ih.stmt _ _ (hp.closed _ _ hy.1)
          (hy.2.1.regime (sameRegime_freeze G c.globals freeG) (Reserved.nodeOK_freeze G c.globals freeG · alias_freeG)) M hM)
          (hy.2.2 cfg n))
          (fun _ _ h => h.elim)) (fun _ _ _ _ h _ => h.elim))
      (fun sig hsig => ?_) ?_ (fun L hL _ => absurd (($hn).symm.trans hL) (by simp))
      (fun w => ⟨fun σ σ' τ τ' hs ht _ => ?_⟩)) (fun r r' σ0 σ0' hr => ?_)
  · cases sig with
    | return_ w =>
      rcases w with _ | ⟨w, _ | ⟨_, _⟩⟩
      · exact absurd hsig.1 (fun h => not_strict_freeG hvo ((sameRegime_freeze G c.globals freeG).strict.mp h))
      · exact FSV.ofFSH (fs_pure (A := fun a b => a = some w ∧ b = some w) ⟨rfl, rfl⟩)
          (fun a b σ σ' hab hst => .inl ⟨hab.1.trans hab.2.symm, by rw [hab.1]; simp, hst⟩)
      · first | exact (hsig : False).elim | exact (hok : False).elim | exact (h : False).elim | exact (hc : False).elim
    | _ =>
      exact FSV.ofFSH (A' := fun _ _ => False) (fs_switch (G := _) (fun a a' ha => by
          rstr)
          (fs_throwT _ hsig)) (fun _ _ _ _ h _ => h.elim)
  · intro σ τ
    simp [run_bind, run_throw, run_modify, OOF]
  · dsimp only
    rw [returnedValues_single, returnedValues_nil, run_pure, run_pure]
    exact ⟨.inr ⟨w, rfl, rfl, hs⟩, ht⟩
  · have hpf := ($hps)
    rcases hr with ⟨rfl, hne, hst⟩ | ⟨w, rfl, rfl, hw⟩
    · obtain ⟨w, rfl⟩ := Option.ne_none_iff_exists'.mp hne
      refine FSH.ofAt ?_ hst (fun _ => rfl)
      refine fs_bind fs_get (fun f f' hf => ?_)
      have hf : StRel (Reserved.freeze G c.globals freeG) (IxRel E) f f' := hf
      simp only [hpf.isEmpty_eq, hP.frames.isEmpty_eq]
      refine fs_ite (fun _ => ?_) (fun _ => ?_)
      · refine fs_bind (fs_switch1 (G := _) (G' := G) (fun a a' ha => by
          rstr))
          (fun _ _ _ => ?_)
        exact fs_pure rfl
      · proc_post hpf (postOutputs_some hP $hv w _ _) (fun c hc => $hov c hc)
        exact fs_pure rfl
    · refine FSH.ofAt (S := (Sm E Gl (Reserved.freeze G c.globals freeG)).atWin w) ?_ hw (fun _ => rfl)
      refine fs_bind fs_get (fun f f' hf => ?_)
      obtain ⟨-, hfst, hfo⟩ := hf
      refine FSH.pre (S' := Sm E Gl (Reserved.freeze G c.globals freeG)) ?_ (fun _ _ h => h.2.1) rfl
      simp only [hpf.isEmpty_eq, hP.frames.isEmpty_eq, outputs_win $hv hfo]
      refine fs_ite (fun _ => ?_) (fun _ => ?_)
      · refine fs_bind (fs_switch1 (G := _) (G' := G) (fun a a' ha => by
          rstr))
          (fun _ _ _ => ?_)
        exact fs_pure rfl
      · proc_post hpf (postOutputs_win hP $hv w _ hfo) (fun c hc => $hov c hc)
        exact fs_pure rfl))

set_option hygiene false in
macro "proc_tail" hps:term:max hov:term:max : tactic => `(tactic| (
  refine fs_bind fs_get (fun f f' hf => ?_)
  have hf : StRel {} (IxRel E) f f' := hf
  have hpf := ($hps)
  have hvo : ∀ x ∈ P.outputs, NotV x.name.text := fun x _ => notV_none hvn _
  simp only [hpf.isEmpty_eq, hP.frames.isEmpty_eq, hf.stack.outs hP.outNames (fun x hx => .inl (hvo x hx))]
  refine fs_ite (fun _ => ?_) (fun _ => ?_)
  · refine fs_bind (fs_switch1 (G := _) (G' := G) (fun a a' ha => by
      rstr))
      (fun _ _ _ => ?_)
    cases r <;> exact fs_pure rfl
  · proc_post hpf (postOutputs_congr hP hf.stack hvo r) (fun c hc => $hov c hc)
    cases r <;> exact fs_pure rfl))

set_option hygiene false in
macro "proc_restW" hbody:term:max hps:term:max hov:term:max : tactic => `(tactic| (
  refine fs_bind (fs_pure (A := fun a b => a = _ ∧ b = _) ⟨rfl, rfl⟩) (fun y y' hy => ?_)
  obtain ⟨rfl, rfl⟩ := hy
  refine fs_bind fs_get (fun s0 s0' h0 => ?_)
  refine fs_withLabels (fun _ => []) (fun _ => []) (fun _ _ _ _ _ => Iff.rfl) ?_
  refine fs_bind fs_get (fun c c' hc => ?_)
  have h0 : StRel G (IxRel E) s0 s0' := h0
  have hc : StRel G (IxRel E) c c' := hc
  simp only [defaults_sig hP.outputs h0.index]
  refine fs_switch (G' := {}) (fun a a' ha => by
    have := SR.fresh (gs := a.globals) (callee_clean hP args s0.index); strel ha) ?_
  refine fs_bind fs_get (fun cur cur' hcur => ?_)
  have hcur : StRel {} (IxRel E) cur cur' := hcur
  simp only [entrySnapshot, hcur.heap]
  rw [tc_runB _ _ rfl (fun _ => rfl), tc_runB _ _ rfl (fun _ => rfl)]
  refine fs_bind (fs_tryCatch $hbody (fun sig hsig => ?_) ?_) (fun r r' hr => ?_)
  · apply fsh_sm0
    cases sig <;> first
      | (rename_i vs; rcases vs with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> first | exact fs_pure rfl | exact (hsig : False).elim)
      | exact fs_pure rfl
      | exact fs_switch (G := _) (fun a a' ha => by
          rstr)
          (fs_throwT _ hsig)
  · intro σ τ
    simp [run_bind, run_throw, run_modify, OOF]
  · subst hr
    proc_tail $hps $hov))

set_option hygiene false in
macro "proc_restV" hbody:term:max hps:term:max ho:term:max hov:term:max : tactic => `(tactic| (
  refine fs_bind (fs_pure (A := fun a b => a = _ ∧ b = _) ⟨rfl, rfl⟩) (fun y y' hy => ?_)
  obtain ⟨rfl, rfl⟩ := hy
  refine fs_bind fs_get (fun s0 s0' h0 => ?_)
  refine fs_withLabels (fun _ => []) (fun _ => []) (fun _ _ _ _ _ => Iff.rfl) ?_
  refine fs_bind fs_get (fun c c' hc => ?_)
  have h0 : StRel G (IxRel E) s0 s0' := h0
  have hc : StRel G (IxRel E) c c' := hc
  simp only [defaults_sig hP.outputs h0.index]
  refine fs_switch (G' := {}) (fun a a' ha => by
    have := SR.fresh (gs := a.globals) (callee_clean hP args s0.index); strel ha) ?_
  refine fs_bind fs_get (fun cur cur' hcur => ?_)
  have hcur : StRel {} (IxRel E) cur cur' := hcur
  simp only [entrySnapshot, hcur.heap]
  rw [tc_runB _ _ rfl (fun _ => rfl), tc_runB _ _ rfl (fun _ => rfl)]
  refine fs_bindV (fs_tryCatchV $hbody (fun sig hsig => ?_) ?_) (fun r r' σ0 σ0' hA => ?_)
  · refine FSV.ofFSH (A' := Eq) ?_ (fun a b σ σ' hab hst => .inl ⟨hab, hst⟩)
    apply fsh_sm0
    cases sig <;> first
      | (rename_i vs; rcases vs with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> first | exact fs_pure rfl | exact (hsig : False).elim)
      | exact fs_pure rfl
      | exact fs_switch (G := _) (fun a a' ha => by
          rstr)
          (fs_throwT _ hsig)
  · intro σ τ
    simp [run_bind, run_throw, run_modify, OOF]
  · rcases hA with ⟨rfl, hst⟩ | ⟨v, sx, rfl, rfl, hstk, hst⟩
    · refine FSH.ofAt ?_ hst (fun _ => rfl)
      proc_tail $hps $hov
    · show FSH _ _ _ _ _ (procTail cfg _ _ _ _ _ _ _ _ _ none)
      obtain ⟨o'', ho'', hn''⟩ := L2.paramR_single hP.outputs $ho
      refine procTail_ofAt ho'' (by rw [← hn'']) $ho (fun _ _ => rfl) ?_ hst hstk
      unfold procTail
      generalize (some v : Option Value) = r
      proc_tail $hps $hov))

set_option hygiene false in
macro "icall_mod" : tactic => `(tactic| (
  refine fs_bind fs_get (fun σ1 σ1' hσ1 => ?_)
  have hσ1 : StRel _ (IxRel E) σ1 σ1' := hσ1
  rw [← hid]
  cases f.uniqueId with
  | none =>
    first
    | exact fs_stuckError _ _
    | exact fs_bind (fs_stuckError (A := Eq) _ _) (fun _ _ _ => fs_pure rfl)
  | some id =>
    dsimp only
    have hm := hσ1.index.methodsById hrm id
    revert hm
    cases σ1.index.methodsById[id]? <;> cases σ1'.index.methodsById[id]? <;>
      simp only [ORel, false_implies, true_implies]
    · first
      | exact fs_stuckError _ _
      | exact fs_bind (fs_stuckError (A := Eq) _ _) (fun _ _ _ => fs_pure rfl)
    · intro hs
      refine fs_bind (ih.pre _ _ _ _ _ hs.1.toB M hM) (fun _ _ _ => ?_)
      first
      | exact fs_muteE (fs_bind (fs_resolveOverride _ _ hs.2.1 hs.2.2 hrm) (fun P P' hP => ih.proc _ _ _ _ _ hP.toB M hM))
      | exact fs_bind (fs_muteE (fs_bind (fs_resolveOverride _ _ hs.2.1 hs.2.2 hrm) (fun P P' hP => ih.proc _ _ _ _ _ hP.toB M hM)))
          (fun a b hab => by subst hab; exact fs_pure rfl)))

set_option maxHeartbeats 8000000 in
/-- `invokeProc` with fuel `n + 1` on `ProcRelB`-related procedures is simulated, given `FundAt` up to `n`. -/
theorem fstep_procT {n : Nat} (ih : FundAt cfg E Rw K Gl n) (ihs : ∀ k ≤ n, FundAt cfg E Rw K Gl k) (top : Bool) :
    ∀ site site' P P' args, ProcRelB E P P' → ∀ M, K * (n + 1) ≤ M →
      FS (Sm E Gl G) Eq (invokeProc cfg (n + 1) site P args top) (invokeProc cfg M site' P' args top) := by
  intro site site' P P' args hP M' hM'
  obtain ⟨M, rfl, hM⟩ := fuel_split hp.K_pos hM'
  simp only [invokeProc]
  refine fs_jumpBoundary ?_
  simp only [hp.cfg_ok.strict, Option.isSome_none, Bool.false_and,
    Bool.false_eq_true, ite_false, get_bind_ignore]
  simp only [L2.paramR_length hP.inputs, extract_sig hP.outputs, hP.coro, hP.coro',
    Bool.false_eq_true, ite_false]
  rw [zipFold_sig hP.inputs (fun acc x y v h => by simp only [h])]
  have hext : P.body = .External → P'.name.text = P.name.text := hP.ext
  refine fs_ite (fun _ => fs_bind (fs_fail (A := Eq) (T := Sm E Gl G) _ _) (fun _ _ _ => ?_))
    (fun _ => ?_)
  all_goals
    refine ?_
    refine fs_bind (ih.pre _ _ _ _ _ hP M hM) (fun _ _ _ => ?_)
    refine fs_muteSel ?_
    refine fs_escape (by rw [hP.throws]) (excOK_of hP.throws hP.throwsTy) ?_ trivial (fun _ _ _ _ ha => by strel ha)
    have hB := hP.body
    have hPO := hP.postOK
    have hBO := hP.bodyOK
    have hNC := hP.nc
    revert hB hext hPO hBO hNC
    generalize P.body = b
    generalize P'.body = b'
    intro hext hB hPO hBO hNC
    cases hB with
    | external =>
      rw [hext rfl]
      exact fs_bind (fs_liftM (hp.cfg_ok.call _ _)) (fun x y hxy => by subst hxy; exact fs_pure rfl)
    | transparent h =>
      simp only [Body.implementation, Body.postconditions]
      cases h with
      | plain hn h =>
        by_cases hv : valued P = true
        · proc_restE hn h (L2.nil : L2 (CondRel E) [] []) (fun c hc => by simp at hc)
            (by have := hBO _ rfl; rwa [procG_valued hv] at this) (hNC hv _ rfl) hv
        · have hv' : valued P = false := by simpa using hv
          proc_rest hn h (L2.nil : L2 (CondRel E) [] []) (fun c hc => by simp at hc)
            (by have := hBO _ rfl; rwa [procG_void hv'] at this) (outV_void hP hv')
      | wrapBlock hL hss =>
        have hvn := hp.retV (by rw [hL]; simp)
        have hplG : Plain G := hp.retPlain (by rw [hL]; simp) G
        proc_restW (wrap_block hp ihs hL hss M hM') (L2.nil : L2 (CondRel E) [] []) (fun c hc => by simp at hc)
      | wrapOther hL hb hd hlb hann =>
        have hvn := hp.retV (by rw [hL]; simp)
        have hplG : Plain G := hp.retPlain (by rw [hL]; simp) G
        proc_restW (wrap_other hp ih hL hb hd hlb hann M hM') (L2.nil : L2 (CondRel E) [] []) (fun c hc => by simp at hc)
      | valued hL ho he hy =>
        have hvn := hp.retV (by rw [hL]; simp)
        have hplG : Plain G := hp.retPlain (by rw [hL]; simp) G
        proc_restV (wrap_valued hp ihs hL he hy M hM') (L2.nil : L2 (CondRel E) [] []) ho
          (fun c hc => by simp at hc)
      | valuedB hL ho he hy =>
        have hvn := hp.retV (by rw [hL]; simp)
        have hplG : Plain G := hp.retPlain (by rw [hL]; simp) G
        proc_restV (wrap_valuedB hp ihs hL he hy M hM') (L2.nil : L2 (CondRel E) [] []) ho
          (fun c hc => by simp at hc)
    | opq hps hi hms =>
      rename_i ps ps' i i' ms ms'
      cases i <;> cases i' <;> simp only [ORel] at hi
      · simp only [Body.implementation]
        rw [undetermined_congr hP (b := Body.Opaque _ none ms) (b' := Body.Opaque _ none ms')
          (by simp only [bodyModifies, hms])]
        cases undeterminedOf _ _ with
        | none => exact fs_bodiless hP
        | some w => exact fs_bind (fs_refuse (A := Eq) _ _) (fun _ _ _ => fs_bodiless hP)
      · simp only [Body.implementation, Body.postconditions]
        have hPO' : ∀ c ∈ ps, OvOK condG c.condition := hPO
        cases hi with
        | plain hn hi =>
          by_cases hv : valued P = true
          · proc_restE hn hi hps hPO' (by have := hBO _ rfl; rwa [procG_valued hv] at this) (hNC hv _ rfl) hv
          · have hv' : valued P = false := by simpa using hv
            proc_rest hn hi hps hPO' (by have := hBO _ rfl; rwa [procG_void hv'] at this) (outV_void hP hv')
        | wrapBlock hL hss =>
          have hvn := hp.retV (by rw [hL]; simp)
          have hplG : Plain G := hp.retPlain (by rw [hL]; simp) G
          proc_restW (wrap_block hp ihs hL hss M hM') hps hPO'
        | wrapOther hL hb hd hlb hann =>
          have hvn := hp.retV (by rw [hL]; simp)
          have hplG : Plain G := hp.retPlain (by rw [hL]; simp) G
          proc_restW (wrap_other hp ih hL hb hd hlb hann M hM') hps hPO'
        | valued hL ho he hy =>
          have hvn := hp.retV (by rw [hL]; simp)
          have hplG : Plain G := hp.retPlain (by rw [hL]; simp) G
          proc_restV (wrap_valued hp ihs hL he hy M hM') hps ho hPO'
        | valuedB hL ho he hy =>
          have hvn := hp.retV (by rw [hL]; simp)
          have hplG : Plain G := hp.retPlain (by rw [hL]; simp) G
          proc_restV (wrap_valuedB hp ihs hL he hy M hM') hps ho hPO'
    | abs _ =>
      simp only [Body.implementation]
      rw [undetermined_congr hP (b := Body.Abstract _) (b' := Body.Abstract _) (by simp only [bodyModifies])]
      cases undeterminedOf _ _ with
      | none => exact fs_bodiless hP
      | some w => exact fs_bind (fs_refuse (A := Eq) _ _) (fun _ _ _ => fs_bodiless hP)

theorem fstep_proc {n : Nat} (ih : FundAt cfg E Rw K Gl n) (ihs : ∀ k ≤ n, FundAt cfg E Rw K Gl k) :
    ∀ site site' P P' args, ProcRelB E P P' → ∀ M, K * (n + 1) ≤ M →
      FS (Sm E Gl G) Eq (invokeProc cfg (n + 1) site P args) (invokeProc cfg M site' P' args) :=
  fstep_procT hp ih ihs false

omit hp in
theorem absent_congr {ix ix' : ProgramIndex} (h : IxRel E ix ix') {ta ta' : List HighTypeMd}
    (hta : L2 (fun a b => Reserved.tyR a.val b.val) ta ta') : absentOf ix' ta' = absentOf ix ta := by
  unfold absentOf
  rcases hta with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, hr⟩⟩⟩
  · rfl
  · rfl
  · exact h.defaultR h2
  · rfl

theorem fstep_outputs {n : Nat} (ih : FundAt cfg E Rw K Gl n) (ihs : ∀ k ≤ n, FundAt cfg E Rw K Gl k) :
    ∀ s t, NR E Rw Gl s t → OvOK G s → ∀ M, K * (n + 1) ≤ M →
      FS (Sm E Gl G) (VRel (Reserved.vok E s t)) (evalCallOutputs cfg (n + 1) s.val) (evalCallOutputs cfg M t.val) := by
  intro s t hst hov M' hM'
  rcases hst with ⟨hsh, hex, hvk⟩ | hrw
  · obtain ⟨M, rfl, hM⟩ := fuel_split hp.K_pos hM'
    have hN : NR E Rw Gl s t := .inl ⟨hsh, hex, hvk⟩
    cases hsh with
    | @call f f' as as' ta ta' _ _ has hta hcr =>
      rcases hcr with ⟨rfl, hf⟩ | hren
      case inr =>
        obtain ⟨op, hop, hop'⟩ := hp.renOp f f' hren
        simp only [evalCallOutputs, hop, hop']
        exact fs_bind (ih.expr _ _ hN hov M hM) (fun v v' hv => fs_pure (fun h => by rw [hv h]))
      simp only [evalCallOutputs]
      split
      · exact fs_bind (ih.expr _ _ hN hov M hM) (fun v v' hv => fs_pure (fun h => by rw [hv h]))
      · refine fs_bind fs_get (fun σ σ' hσ => fs_bind fs_get (fun σ1 σ1' hσ1 => ?_))
        have hσ1 : StRel G (IxRel E) σ1 σ1' := hσ1
        have hl := hσ1.index.callee f hf
        have hiso : (lookupCallee σ1.index f).isNone = (lookupCallee σ1'.index f).isNone := by
          revert hl
          cases lookupCallee σ1.index f <;> cases lookupCallee σ1'.index f <;> simp [ORel]
        rw [← hiso, absent_congr hσ1.index hta]
        refine fs_ite (fun _ => fs_bind (ih.expr _ _ hN hov M hM) (fun v v' hv => fs_pure (fun h => by rw [hv h])))
          (fun _ => ?_)
        simp only [ValKids, LV] at hvk
        refine fs_bind (fs_mapM (has.and hvk).withMem (fun a b hab => exprMdE hp ih hab.1.1 hab.1.2 (Hered.kid hov (by simp [stmtExprChildren, hab.2])) hM)) (fun xs ys hxs => ?_)
        subst hxs
        have hb := callBuiltin_pconst f.text xs (absentOf σ1.index ta)
        revert hb
        cases callBuiltin (m := PM) f.text xs (absentOf σ1.index ta) with
        | some act =>
          intro hb
          exact fs_bind (fs_liftM (hb act rfl)) (fun v v' hv => by subst hv; exact fs_pure (fun _ => rfl))
        | none => intro _; exact FS.vr (ih.callee _ _ _ _ hf M hM)
    | @icall tg tg' f f' as as' _ _ _ _ htg hf has hr hrm hid =>
      simp only [evalCallOutputs]
      simp only [ValKids, LV] at hvk
      refine fs_bind fs_get (fun σ σ' hσ => ?_)
      refine fs_bind (exprMdE hp ih htg hvk.1 (by ovk) hM) (fun v v' hv => ?_)
      subst hv
      refine fs_bind (fs_mapM (has.and hvk.2).withMem (fun a b hab => exprMdE hp ih hab.1.1 hab.1.2 (Hered.kid hov (by simp [stmtExprChildren, hab.2])) hM)) (fun xs ys hxs => ?_)
      subst hxs
      refine FS.vr (fs_ite (fun _ => ?_) (fun _ => fs_bind (fs_resolveMethod _ _ _ hf hr hrm) (fun P P' hP => ih.proc _ _ _ _ _ hP.toB M hM)))
      icall_mod
    | unsup hu hu' =>
      rw [unsup_outputs hu, unsup_outputs hu']
      exact fs_bind (ih.expr _ _ hN hov M hM) (fun v v' hv => fs_pure (fun h => by rw [hv h]))
    | _ =>
      simp only [evalCallOutputs]
      exact fs_bind (ih.expr _ _ hN hov M hM) (fun v v' hv => fs_pure (fun h => by rw [hv h]))
  · exact (hp.step n ihs).outputs s t hrw hov M' hM'

omit hp in
theorem missingWitness_congr {ix ix' : ProgramIndex} (h : IxRel E ix ix') {ty ty' : Option HighTypeMd}
    (hty : ORel (fun a b => Reserved.tyR a.val b.val) ty ty') :
    missingWitness ix' (ty'.map (·.val)) = missingWitness ix (ty.map (·.val)) := by
  unfold missingWitness
  rcases ty with _ | a <;> rcases ty' with _ | b <;> simp only [ORel] at hty
  · rfl
  · simp only [Option.map_some, h.unalias _ _ hty, h.noWitness]

omit hp in
theorem defaultOf_congr {ix ix' : ProgramIndex} (h : IxRel E ix ix') {ty ty' : Option HighTypeMd}
    (hty : ORel (fun a b => Reserved.tyR a.val b.val) ty ty') :
    defaultOf ix' (ty'.map (·.val)) = defaultOf ix (ty.map (·.val)) := by
  rcases ty with _ | a <;> rcases ty' with _ | b <;> simp only [ORel] at hty
  · rfl
  · exact h.defaultR hty

theorem fstep_stmt {n : Nat} (ih : FundAt cfg E Rw K Gl n) (ihs : ∀ k ≤ n, FundAt cfg E Rw K Gl k) :
    ∀ s t, NR E Rw Gl s t → OvOK G s → ∀ M, K * (n + 1) ≤ M →
      FS (Sm E Gl G) Eq (evalStmt cfg (n + 1) s) (evalStmt cfg M t) := by
  intro s t hst hov M' hM'
  rcases hst with ⟨hsh, hex, hvk⟩ | hrw
  · obtain ⟨M, rfl, hM⟩ := fuel_split hp.K_pos hM'
    have hN : NR E Rw Gl s t := .inl ⟨hsh, hex, hvk⟩
    have fallback : FS (Sm E Gl G) Eq (do let _ ← evalExprMd cfg n s; pure ()) (do let _ ← evalExprMd cfg M t; pure ()) :=
      fs_bind (ih.exprMd _ _ hN hov M hM) (fun _ _ _ => fs_pure rfl)
    cases hsh with
    | @block ss ss' l _ _ hss hlab =>
      have hos : ∀ x ∈ ss, OvOK G x := fun x hx => Hered.kid hov (by simp [stmtExprChildren, hx])
      cases l with
      | none =>
        simp only [evalStmt]
        exact fs_bind fs_chargeStep (fun _ _ _ =>
          fs_bind (fs_wbs' (LX.decls_ext hp hss) (LX.decls_ok hp hss) ((ih.list _ _ _ hss (fun x hx => (hos x hx).relax _) M hM).weaken
            (fun _ _ h => h (fun e => absurd e (by decide)))))
            (fun _ _ _ => fs_pure rfl))
      | some lab =>
        simp only [evalStmt, List.forIn_nil, pure_bind]
        refine fs_bind fs_get (fun σ σ' hσ => ?_)
        have hσ : StRel G (IxRel E) σ σ' := hσ
        refine fs_withOpenLabel lab (fs_tryCatch (fs_blockBody hp ih hM hss hos)
          (fun c hc => ?_) ?_ (fun L hL hok => ?_) (fun w => fs_throwW w))
        · cases c with
          | exit_ l => exact fs_ite (fun _ => fs_modifyRel (fun a a' ha => by strel ha)) (fun _ => fs_throw _ hc)
          | goto_ l =>
            exact fs_ite (fun _ => fs_bind (fs_modifyRel (fun a a' ha => by strel ha)) (fun _ _ _ =>
              fs_bind fs_chargeStep (fun _ _ _ =>
                ih.blockLoop ss ss' lab σ.cursor σ'.cursor hss hlab hos M hM))) (fun _ => fs_throw _ hc)
          | _ => exact fs_throw _ hc
        · intro σ τ
          simp [run_throw, OOF]
        · have hne : (L == lab) = false := by
            have := hlab L hL
            simp only [beq_eq_false_iff_ne]
            exact fun h => this (by rw [h])
          simp only [hne, Bool.false_eq_true, ite_false]
          exact fs_throwM hL hok
    | @jump l d _ _ =>
      simp only [evalStmt]
      refine fs_bind fs_get (fun σ σ' hσ => ?_)
      have hσ : StRel G (IxRel E) σ σ' := hσ
      have hGl := hex l d rfl
      have hct : σ'.openLabels.contains l = σ.openLabels.contains l := by
        exact Bool.eq_iff_iff.mpr (by
          rw [List.contains_iff_mem, List.contains_iff_mem]; exact (hσ.openLabels l (hp.glRes l hGl)).symm)
      rw [hct]
      split
      · cases d <;> exact fs_throw _ hGl
      · exact fs_throw _ hGl
    | @assign ts ts' v v' _ _ hts hv hy hy' =>
      have hov' : OvOK G v := Hered.kid hov (by simp [stmtExprChildren])
      have hot : ∀ t ∈ ts, OvV G t.val := fun t ht c hc =>
        Hered.kid hov (by simp only [stmtExprChildren, List.mem_append, List.mem_flatMap]; exact .inl ⟨t, ht, hc⟩)
      have multi : ∀ (l : List VariableMd) (l' : List VariableMd),
          L2 (fun a b => ((VarRel E a.val b.val ∧ WOK a.val) ∧ VV E a.val b.val) ∧ a ∈ ts) l l' →
          FS (Sm E Gl G) Eq
            (do
              let writes ← l.mapM (assignTarget cfg n ·.val)
              modify fun (s : EvalState) => { s with callSite := v.source }
              let outs ← evalCallOutputs cfg n v.val
              if outs.size != l.length then
                hostFail s!"assignment expects {l.length} values, call produced {outs.size}"
              for (w, x) in writes.zip outs.toList do
                writeUpdate w x)
            (do
              let writes ← l'.mapM (assignTarget cfg M ·.val)
              modify fun (s : EvalState) => { s with callSite := v'.source }
              let outs ← evalCallOutputs cfg M v'.val
              if outs.size != l'.length then
                hostFail s!"assignment expects {l'.length} values, call produced {outs.size}"
              for (w, x) in writes.zip outs.toList do
                writeUpdate w x) := by
        intro l l' hl
        refine fs_bind (fs_mapM_L2 hl (fun a b hab =>
          ih.assign _ _ hab.1.1.1 hab.1.2 hab.1.1.2 (hot a hab.2) M hM)) (fun w w' hw => ?_)
        refine fs_bind (fs_modifyRel (fun a a' ha => by strel ha)) (fun _ _ _ => ?_)
        refine fs_bind (outputsE hp ih hv hvk.2 hov' hM) (fun o o' ho => ?_)
        subst ho
        rw [← hl.length_eq]
        refine fs_ite (fun _ => fs_bind (fs_fail (A := Eq) (T := Sm E Gl G) _ _) (fun _ _ _ => ?_))
          (fun _ => ?_)
        all_goals
          dsimp only
          refine fs_bind (fs_forIn (hw.zip o.toList) (fun a b hab c => ?_)) (fun _ _ _ => fs_pure rfl)
          rcases a with ⟨u, x⟩
          rcases b with ⟨u', x'⟩
          obtain ⟨hu, rfl⟩ := hab
          exact fs_bind (fs_writeUpdate _ _ hu _) (fun _ _ _ => fs_pure rfl)
      simp only [ValKids] at hvk
      obtain ⟨hnp, hnp'⟩ := hts.noPush
      have hts' := (hts.and hvk.1).withMem
      cases hts' with
      | nil => simp only [evalStmt, hnp, Bool.false_eq_true, ite_false]; exact multi _ _ .nil
      | cons ht hr =>
        cases hr with
        | nil =>
          simp only [evalStmt, hnp, hnp', Bool.false_eq_true, ite_false]
          simp only [NotYield] at hy hy'
          refine fs_bind (ih.assign _ _ ht.1.1.1 ht.1.2 ht.1.1.2 (hot _ ht.2) M hM) (fun u u' hu => ?_)
          split <;> split <;> first
            | (simp only [‹v.val = StmtExpr.Yield›] at hy)
            | (simp only [‹v'.val = StmtExpr.Yield›] at hy')
            | exact fs_bind (exprMdE hp ih hv hvk.2 hov' hM)
                (fun a b hab => by subst hab; exact fs_writeUpdate _ _ hu _)
        | cons ht2 hr2 => simp only [evalStmt, hnp, hnp', Bool.false_eq_true, ite_false]; exact multi _ _ (.cons ht (.cons ht2 hr2))
    | @var v v' _ _ hv =>
      cases v <;> cases v' <;> simp only [VarRel] at hv
      · exact fallback
      · exact fallback
      · rename_i p p'
        simp only [evalStmt]
        refine fs_bind fs_get (fun σ σ' hσ => ?_)
        have hσ : StRel G (IxRel E) σ σ' := hσ
        rw [missingWitness_congr hσ.index hv.2.1]
        have rest : FS (Sm E Gl G) Eq
            (do
              let s ← get
              let x ← chooseValue (p.type.map (s.index.unalias ·.val)) (defaultOf s.index (p.type.map (·.val)))
              modify fun (s : EvalState) => { s with stack := declareLocal s.stack p.name.text x })
            (do
              let s ← get
              let x ← chooseValue (p'.type.map (s.index.unalias ·.val)) (defaultOf s.index (p'.type.map (·.val)))
              modify fun (s : EvalState) => { s with stack := declareLocal s.stack p'.name.text x }) := by
          refine fs_bind fs_get (fun s s' hs => ?_)
          have hs : StRel G (IxRel E) s s' := hs
          rw [defaultOf_congr hs.index hv.2.1]
          refine fs_bind (fs_choose _ _ _) (fun x y hxy => ?_)
          subst hxy
          exact fs_modifyRel (fun a a' ha => by
            simp only [← hv.1]; exact ha.with_stack (ha.stack.declareLocal hv.2.2.1 hv.2.2.2 x))
        cases missingWitness σ.index _ with
        | none => exact rest
        | some w => exact fs_bind (fs_evalError (A := Eq) _ _) (fun _ _ _ => rest)
    | @ite c th c' th' el el' _ _ h1 h2 h3 =>
      simp only [evalStmt]
      refine fs_bind fs_get (fun σ σ' hσ => ?_)
      have hσ : StRel G (IxRel E) σ σ' := hσ
      simp only [hσ.coroSelf, hσ.coroSelf', Option.isNone_none, ite_true]
      simp only [ValKids] at hvk
      refine fs_bind (exprMdE hp ih h1 hvk.1 (by ovk) hM) (fun v v' hv => ?_)
      subst hv
      refine fs_bind (fs_liftM (isTrue_pconst v)) (fun b b' hb => ?_)
      subst hb
      refine fs_ite (fun _ => ih.scoped_ _ _ (hp.closed _ _ h2) (by ovk) M hM) (fun _ => ?_)
      cases el <;> cases el' <;> simp only [ORel] at h3
      · exact fs_pure rfl
      · exact ih.scoped_ _ _ (hp.closed _ _ h3) (by ovk) M hM
    | @while_ c c' b b' is is' d d' pt _ _ hc his hb =>
      simp only [evalStmt]
      refine fs_bind fs_get (fun σ σ' hσ => ?_)
      have hσ : StRel G (IxRel E) σ σ' := hσ
      simp only [hσ.seek, hσ.seek', hσ.coroSelf, hσ.coroSelf', Option.isNone_none, Option.isSome_none,
        Bool.and_true, Bool.false_eq_true, ite_false]
      have hoc : OvOK G c := by ovk
      have hob : OvOK G b := by ovk
      simp only [ValKids, LV] at hvk
      have hci : FS (Sm E Gl G) Eq
          (forIn is PUnit.unit fun inv _ => do
            evalStmt cfg n ⟨.Assert inv none, inv.source⟩
            pure (ForInStep.yield PUnit.unit))
          (forIn is' PUnit.unit fun inv _ => do
            evalStmt cfg M ⟨.Assert inv none, inv.source⟩
            pure (ForInStep.yield PUnit.unit)) :=
        fs_forIn (his.and hvk.2).withMem (fun a a' ha _ => fs_bind (ih.stmt _ _ (.inl ⟨.assert ha.1.1, (fun _ _ h => by cases h), ha.1.2⟩)
          (.node _ ⟨trivial, hov.here.1 a ha.2⟩ (fun x hx => by
            simp only [stmtExprChildren, List.mem_singleton] at hx
            subst hx
            exact Hered.kid hov (by simp [stmtExprChildren, ha.2]))) M hM) (fun _ _ _ => fs_pure rfl))
      have hci' : FS (Sm E Gl G) Eq
          (do
            forIn is PUnit.unit fun inv _ => do
              evalStmt cfg n ⟨.Assert inv none, inv.source⟩
              pure (ForInStep.yield PUnit.unit)
            pure PUnit.unit)
          (do
            forIn is' PUnit.unit fun inv _ => do
              evalStmt cfg M ⟨.Assert inv none, inv.source⟩
              pure (ForInStep.yield PUnit.unit)
            pure PUnit.unit) :=
        fs_bind hci (fun _ _ _ => fs_pure rfl)
      cases pt
      · simp only [Bool.false_eq_true, ite_false]
        exact 
          ih.iter _ _ _ _ _ _ _ _ _ hc hvk.1 hb hoc hob hci' (fs_pure rfl) M hM
      · simp only [ite_true]
        exact fs_bind hci' (fun _ _ _ => fs_bind (ih.scoped_ _ _ (hp.closed _ _ hb) hob M hM) (fun _ _ _ =>
          ih.iter _ _ _ _ _ _ _ _ _ hc hvk.1 hb hoc hob hci' (fs_pure rfl) M hM))
    | @try_ b b' cs cs' f f' _ _ hb hcs hf hfo =>
      simp only [evalStmt]
      refine fs_bind fs_get (fun σ σ' hσ => ?_)
      have hσ : StRel G (IxRel E) σ σ' := hσ
      simp only [hσ.seek, hσ.seek', hσ.coroSelf, hσ.coroSelf',
        Option.isSome_none, Bool.false_eq_true, ite_false, ← hcs.length_eq]
      have hof : OvO G f := fun x hx => Hered.kid hov (by simp [stmtExprChildren, hx])
      have hocs : ∀ c ∈ cs, OvC G c := fun c hc =>
        ⟨fun x hx => Hered.kid hov (List.mem_append_left _ (List.mem_append_right _
            (List.mem_flatMap.mpr ⟨c, hc, List.mem_append_left _ (by simp [hx])⟩))),
         Hered.kid hov (List.mem_append_left _ (List.mem_append_right _
            (List.mem_flatMap.mpr ⟨c, hc, List.mem_append_right _ (List.mem_singleton_self _)⟩)))⟩
      refine ?_
      refine fs_bindV (A := Cap (E := E) (Gl := Gl) G) (fs_tryCatchVW
        (FSV.ofFSH (fs_bind (ih.scoped_ _ _ (hp.closed _ _ hb) (by ovk) M hM)
          (fun _ _ _ => fs_pure (A := OkOpt Gl G) trivial)) (fun a b σ σ' hab hst => .inl ⟨hab, hst⟩))
        (fun c hc => FSV.ofFSH (by cases c <;> first | exact fs_throw _ hc | exact fs_pure ⟨.inl rfl, hc⟩)
          (fun a b σ σ' hab hst => .inl ⟨hab, hst⟩)) ?_
        (fun L hL hok => FSV.ofFSH (fs_pure ⟨.inr (.inl ⟨L, hL, rfl, rfl⟩), hok⟩) (fun a b σ σ' hab hst => .inl ⟨hab, hst⟩))
        (fun w => ⟨fun σ σ' τ τ' hs ht _ => ?_⟩)) (fun o o' σ0 σ0' ho => ?_)
      · intro σ τ
        simp [run_throw, OOF]
      · simp only [run_pure, RV]
        exact ⟨.inr ⟨w, rfl, rfl, hs⟩, ht⟩
      · rcases ho with ⟨ho, hst⟩ | ⟨w, rfl, rfl, hw⟩
        · refine FSH.ofAt ?_ hst (fun _ => rfl)
          rcases o with _ | c <;> rcases o' with _ | c' <;> simp only [OkOpt] at ho
          · exact ih.fin _ _ _ _ _ hf hof M hM
          · obtain ⟨hcr, hok⟩ := ho
            rcases hcr with rfl | ⟨L, hL, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
            · cases c with
              | suspended => exact absurd hok id
              | throw_ v => exact fs_bind (fs_checkCaught hcs v) (fun _ _ _ => ih.clauses _ _ _ _ _ _ _ _ _ hf hcs hvk hfo hof hocs M hM)
              | refused _ => exact fs_throw _ hok
              | _ => exact fs_bind (ih.fin _ _ _ _ _ hf hof M hM) (fun _ _ _ => fs_throw _ hok)
            · exact fs_bind (ih.fin _ _ _ _ _ hf hof M hM) (fun _ _ _ => fs_throwM hL hok)
            · exact fs_throwTR hok (.inr (.inr ⟨_, _, rfl, rfl⟩))
        · refine FSH.ofAt (S := (Sm E Gl G).atWin w) ?_ hw (fun _ => rfl)
          exact fs_finW ih hM hf hfo _ _ _ w
    | ret hl hv =>
      simp only [evalStmt]
      rename_i v v' _ _
      have hn := hov.here
      rcases hv with _ | ⟨hx, hv⟩
      · simp only [NodeOK] at hn
        simp only [List.mapM_nil]
        exact fs_throw _ hn.1
      · rcases hv with _ | ⟨_, _⟩
        · simp only [NodeOK] at hn
          simp only [List.mapM_cons, List.mapM_nil, bind_assoc, pure_bind]
          exact fs_bind (exprMdE hp ih hx (by cases hvk; assumption) (by ovk) hM)
            (fun a b hab => by subst hab; exact fs_throw _ hn.1.2)
        · simp at hl
    | throw_ hv =>
      simp only [evalStmt]
      exact fs_bind (exprMdE hp ih hv hvk (by ovk) hM) (fun a b hab => by subst hab; exact fs_throw _)
    | assume hc =>
      simp only [evalStmt]
      refine fs_bind fs_get (fun σ σ' hσ => ?_)
      refine fs_bind (fs_emitE (S := Sm E Gl G) (evRel_fail (E := _)) ⟨hc, _, hσ⟩) (fun _ _ _ => ?_)
      refine fs_bind (exprMdE hp ih hc hvk (by ovk) hM) (fun v v' hv => ?_)
      subst hv
      refine fs_bind (fs_liftM (isTrue_pconst _)) (fun b b' hb => ?_)
      subst hb
      exact fs_ite (fun _ => fs_pure rfl) (fun _ => fs_throw _)
    | assert hc =>
      simp only [evalStmt]
      refine fs_bind fs_get (fun σ σ' hσ => ?_)
      refine fs_bind (exprMdE hp ih hc hvk (by ovk) hM) (fun v v' hv => ?_)
      subst hv
      refine fs_bind (fs_liftM (isTrue_pconst _)) (fun b b' hb => ?_)
      subst hb
      refine fs_bind (fs_emitE (S := Sm E Gl G) (evRel_fail (E := _)) ⟨rfl, hc, rfl, _, hσ⟩) (fun _ _ _ => ?_)
      exact fs_ite (fun _ => fs_pure rfl) (fun _ => fs_modifyRel (fun a a' ha => by strel ha))
    | call has hta _ => simp only [evalStmt]; exact fallback
    | unsup hu hu' => rw [unsup_stmt hu, unsup_stmt hu']; exact fallback
    | _ => simp only [evalStmt]; exact fallback
  · exact (hp.step n ihs).stmt s t hrw hov M' hM'

omit hp in
theorem isInstance_congr {σ σ' : EvalState} (h : StRel G (IxRel E) σ σ') {ty ty' : HighType}
    (hty : Reserved.tyR ty ty') (v : Value) : isInstance σ' v ty' = isInstance σ v ty := by
  simp only [isInstance, h.index.ancestors, h.index.unalias _ _ hty]

omit hp in
theorem divProc_congr {ix ix' : ProgramIndex} (h : IxRel E ix ix') (op : Operation) (old : Value)
    (hop : ¬ Reserved.resProc op.procName) :
    ORel (ProcRel E) (divProc? ix op old) (divProc? ix' op old) := by
  unfold divProc?
  exact (h.procsNamed _ hop).find? (fun a b hab =>
    all_sig hab.inputs (fun x y hxy => by simp only [h.unalias _ _ hxy.2]))

theorem fs_wbs1 {s t : StmtExprMd} (h : NR E Rw Gl s t) {A : α → α → Prop} {x y : EvalM PM α}
    (hxy : FS (Sm E Gl (Reserved.relax G (blockDeclarations [t]))) A x y) :
    FS (Sm E Gl G) A (withBlockScope [s] x) (withBlockScope [t] y) :=
  fs_wbs' (h.decl hp G) (h.declOK hp) hxy

omit [Reserved] hp in
theorem opCall_pconst {cfg : ExternalBackendM PM} (hc : CfgB cfg) (op : Operation) (args : List Value) :
    PConst (opCall cfg op args) := by
  unfold opCall
  cases bvCmpName op args with
  | none => exact evalOp_pconst hc _ _
  | some nm =>
    have hb := bvBuiltin_pconst nm args
    revert hb
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases bvBuiltin? (m := PM) nm args with
    | none => intro _; exact evalOp_pconst hc _ _
    | some act => intro hb; exact hb act rfl

omit hp in
theorem datatypeOp_congr {ix ix' : ProgramIndex} (h : IxRel E ix ix') (name : String) (args : List Value) :
    datatypeOp? ix' name args = datatypeOp? ix name args := by
  simp only [datatypeOp?, h.ctors, h.testers, h.destructors]

set_option hygiene false in
macro "call_rest" : tactic => `(tactic| (
  simp only [hp.cfg_ok.strict, Option.isSome_none, Bool.false_and, Bool.false_eq_true, ite_false, ↓reduceIte, ↓reduceDIte]
  refine fs_ite (fun _ => fs_allocateObject) (fun _ => ?_)
  have hb := callBuiltin_pconst f.text xs (absentOf s.index ta)
  revert hb
  cases callBuiltin (m := PM) f.text xs (absentOf s.index ta) with
  | some act => intro hb; exact fs_liftM (hb act rfl)
  | none =>
    intro _
    cases datatypeOp? s.index f.text xs with
    | none => exact fs_bind (ih.callee _ _ _ _ hf M hM) (fun a b hab => by subst hab; exact fs_pure rfl)
    | some r =>
      cases r with
      | ok v => exact fs_pure rfl
      | error msg => exact fs_fail _ _
      | badCtor fty =>
        dsimp only
        refine fs_ite (fun _ => fs_pure rfl) (fun _ => ?_)
        refine fs_bind fs_get (fun a a' ha => ?_)
        exact fs_bind (fs_emitE (S := Sm E Gl G) (evRel_fail (E := _)) ⟨rfl, trivial, rfl, _, ha⟩)
          (fun _ _ _ => fs_bind (fs_modifyRel (fun b b' hb => by strel hb)) (fun _ _ _ => fs_pure rfl))))

theorem fstep_call {n : Nat} (ih : FundAt cfg E Rw K Gl n) {M : Nat} (hM : K * n ≤ M)
    {f f' : Identifier} {as as' : List StmtExprMd} {ta ta' : List HighTypeMd}
    (has : L2 E as as') (hav : LV E as as') (hoa : ∀ a ∈ as, OvOK G a) (hta : L2 (fun a b => Reserved.tyR a.val b.val) ta ta')
    (hcr : CallRel f f') :
    FS (Sm E Gl G) Eq (evalExpr cfg (n + 1) (.Call none f as ta)) (evalExpr cfg (M + 1) (.Call none f' as' ta')) := by
  replace has := (has.and hav).withMem.imp
    (fun a b h => (⟨h.1.1, h.1.2, hoa a h.2⟩ : E a b ∧ Reserved.vok E a b ∧ OvOK G a))
  rcases hcr with ⟨rfl, hf⟩ | hren
  case inr =>
    obtain ⟨op, hop, hop'⟩ := hp.renOp f f' hren
    have ev : ∀ a a', E a a' ∧ Reserved.vok E a a' ∧ OvOK G a → FS (Sm E Gl G) Eq (evalExprMd cfg n a) (evalExprMd cfg M a') :=
      fun a a' h => exprMdE hp ih h.1 h.2.1 h.2.2 hM
    have tr : ∀ v, FS (Sm E Gl G) Eq (liftM (Interpreter.isTrue cfg v) : EvalM PM Bool) (liftM (Interpreter.isTrue cfg v)) :=
      fun v => fs_liftM (isTrue_pconst v)
    have hcc : ∀ g : Identifier, opOf? g.text = some op → (g.text == coroCompletionName) = false := by
      intro g hg
      simp only [beq_eq_false_iff_ne]
      intro he
      rw [he, show opOf? coroCompletionName = none by decide] at hg
      cases hg
    simp only [evalExpr]
    refine fs_bind fs_get (fun σ σ' hσ => ?_)
    simp only [hcc f hop, hcc f' hop', Bool.false_eq_true, ite_false]
    refine ?_
    rw [hop, hop']
    cases op
    case AndThen =>
      rcases has with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc, hr⟩⟩⟩
      · exact fs_fail _ _
      · exact fs_fail _ _
      · dsimp only
        refine fs_bind (ev _ _ ha) (fun x y hxy => ?_)
        subst hxy
        refine fs_bind (tr x) (fun c c' hc => ?_)
        subst hc
        refine fs_ite (fun _ => ?_) (fun _ => fs_pure rfl)
        refine fs_bind (ev _ _ hb) (fun z z' hz => ?_)
        subst hz
        exact fs_bind (tr z) (fun d d' hd => by subst hd; exact fs_pure rfl)
      · exact fs_fail _ _
    case OrElse =>
      rcases has with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc, hr⟩⟩⟩
      · exact fs_fail _ _
      · exact fs_fail _ _
      · dsimp only
        refine fs_bind (ev _ _ ha) (fun x y hxy => ?_)
        subst hxy
        refine fs_bind (tr x) (fun c c' hc => ?_)
        subst hc
        refine fs_ite (fun _ => fs_pure rfl) (fun _ => ?_)
        refine fs_bind (ev _ _ hb) (fun z z' hz => ?_)
        subst hz
        exact fs_bind (tr z) (fun d d' hd => by subst hd; exact fs_pure rfl)
      · exact fs_fail _ _
    case Implies =>
      rcases has with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc, hr⟩⟩⟩
      · exact fs_fail _ _
      · exact fs_fail _ _
      · dsimp only
        refine fs_bind (ev _ _ ha) (fun x y hxy => ?_)
        subst hxy
        refine fs_bind (tr x) (fun c c' hc => ?_)
        subst hc
        refine fs_ite (fun _ => ?_) (fun _ => fs_pure rfl)
        refine fs_bind (ev _ _ hb) (fun z z' hz => ?_)
        subst hz
        exact fs_bind (tr z) (fun d d' hd => by subst hd; exact fs_pure rfl)
      · exact fs_fail _ _
    all_goals
      refine fs_bind (fs_mapM has ev) (fun xs ys hxs => ?_)
      subst hxs
      simp only [hp.cfg_ok.strict]
      simp only [isPartialOp, Bool.false_eq_true, ite_false, ite_true]
      first
      | exact fs_liftM (opCall_pconst hp.cfg_ok _ _)
      | exact fs_bind (fs_pure rfl) (fun _ _ _ => fs_liftM (opCall_pconst hp.cfg_ok _ _))
      | (refine fs_bind fs_get (fun s s' hs => ?_)
         have hs : StRel G (IxRel E) s s' := hs
         obtain ⟨P, P', hl, hl', hP⟩ := hs.index.renCallee f f' hren
         rw [lookupCallee_of_byId hl, lookupCallee_of_byId hl']
         exact fs_bind (ih.pre _ _ _ _ _ hP.toB M hM) (fun _ _ _ => fs_liftM (opCall_pconst hp.cfg_ok _ _)))
  have ev : ∀ a a', E a a' ∧ Reserved.vok E a a' ∧ OvOK G a → FS (Sm E Gl G) Eq (evalExprMd cfg n a) (evalExprMd cfg M a') :=
    fun a a' h => exprMdE hp ih h.1 h.2.1 h.2.2 hM
  have tr : ∀ v, FS (Sm E Gl G) Eq (liftM (Interpreter.isTrue cfg v) : EvalM PM Bool) (liftM (Interpreter.isTrue cfg v)) :=
    fun v => fs_liftM (isTrue_pconst v)
  simp only [evalExpr]
  refine fs_bind fs_get (fun σ σ' hσ => ?_)
  by_cases hcc : (f.text == coroCompletionName) = true
  · simp only [hcc, ite_true]
    rcases has with _ | ⟨ha, _ | ⟨hb, hr⟩⟩
    · exact fs_evalError _ _
    · dsimp only
      refine fs_bind (ev _ _ ha) (fun x y hxy => ?_)
      subst hxy
      refine fs_bind (fs_coroInstance _ _ _) (fun p p' hpp => ?_)
      subst hpp
      refine fs_ite (fun _ => fs_bind (fs_evalError (A := Eq) _ _) (fun _ _ _ => fs_pure rfl))
        (fun _ => fs_pure rfl)
    · exact fs_evalError _ _
  simp only [hcc, Bool.false_eq_true, ite_false]
  refine ?_
  cases hop : opOf? f.text with
  | some op =>
    cases op
    case AndThen =>
      rcases has with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc, hr⟩⟩⟩
      · exact fs_fail _ _
      · exact fs_fail _ _
      · dsimp only
        refine fs_bind (ev _ _ ha) (fun x y hxy => ?_)
        subst hxy
        refine fs_bind (tr x) (fun c c' hc => ?_)
        subst hc
        refine fs_ite (fun _ => ?_) (fun _ => fs_pure rfl)
        refine fs_bind (ev _ _ hb) (fun z z' hz => ?_)
        subst hz
        exact fs_bind (tr z) (fun d d' hd => by subst hd; exact fs_pure rfl)
      · exact fs_fail _ _
    case OrElse =>
      rcases has with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc, hr⟩⟩⟩
      · exact fs_fail _ _
      · exact fs_fail _ _
      · dsimp only
        refine fs_bind (ev _ _ ha) (fun x y hxy => ?_)
        subst hxy
        refine fs_bind (tr x) (fun c c' hc => ?_)
        subst hc
        refine fs_ite (fun _ => fs_pure rfl) (fun _ => ?_)
        refine fs_bind (ev _ _ hb) (fun z z' hz => ?_)
        subst hz
        exact fs_bind (tr z) (fun d d' hd => by subst hd; exact fs_pure rfl)
      · exact fs_fail _ _
    case Implies =>
      rcases has with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc, hr⟩⟩⟩
      · exact fs_fail _ _
      · exact fs_fail _ _
      · dsimp only
        refine fs_bind (ev _ _ ha) (fun x y hxy => ?_)
        subst hxy
        refine fs_bind (tr x) (fun c c' hc => ?_)
        subst hc
        refine fs_ite (fun _ => ?_) (fun _ => fs_pure rfl)
        refine fs_bind (ev _ _ hb) (fun z z' hz => ?_)
        subst hz
        exact fs_bind (tr z) (fun d d' hd => by subst hd; exact fs_pure rfl)
      · exact fs_fail _ _
    all_goals
      refine fs_bind (fs_mapM has ev) (fun xs ys hxs => ?_)
      subst hxs
      simp only [hp.cfg_ok.strict]
      simp only [isPartialOp, Bool.false_eq_true, ite_false, ite_true]
      first
      | exact fs_liftM (opCall_pconst hp.cfg_ok _ _)
      | exact fs_bind (fs_pure rfl) (fun _ _ _ => fs_liftM (opCall_pconst hp.cfg_ok _ _))
      | (refine fs_bind fs_get (fun s s' hs => ?_)
         have hs : StRel G (IxRel E) s s' := hs
         have hl := hs.index.callee f hf
         revert hl
         cases lookupCallee s.index f <;> cases lookupCallee s'.index f <;>
           simp only [ORel, false_implies, true_implies]
         · exact fs_bind (fs_missingPrelude _ _) (fun _ _ _ => fs_liftM (opCall_pconst hp.cfg_ok _ _))
         · exact fun hP => fs_bind (ih.pre _ _ _ _ _ hP.toB M hM) (fun _ _ _ => fs_liftM (opCall_pconst hp.cfg_ok _ _)))
  | none =>
    refine fs_bind (fs_mapM has ev) (fun xs ys hxs => ?_)
    subst hxs
    refine fs_bind fs_get (fun s s' hs => ?_)
    have hs : StRel G (IxRel E) s s' := hs
    rw [absent_congr hs.index hta, datatypeOp_congr hs.index]
    try simp only [defaultValueU_congr hs.index.witnesses]
    refine fs_ite (fun _ => ?_) (fun _ => ?_)
    · have hl := hs.index.callee f hf
      revert hl
      cases lookupCallee s.index f <;> cases lookupCallee s'.index f <;>
        simp only [ORel, false_implies, true_implies]
      · refine fs_bind (fs_missingPrelude _ _) (fun _ _ _ => ?_)
        call_rest
      · exact fun hP => fs_bind (ih.pre _ _ _ _ _ hP.toB M hM) (fun _ _ _ => by call_rest)
    · call_rest

theorem fstep_expr {n : Nat} (ih : FundAt cfg E Rw K Gl n) (ihs : ∀ k ≤ n, FundAt cfg E Rw K Gl k) :
    ∀ s t, NR E Rw Gl s t → OvOK G s → ∀ M, K * (n + 1) ≤ M →
      FS (Sm E Gl G) (VRel (Reserved.vok E s t)) (evalExpr cfg (n + 1) s.val) (evalExpr cfg M t.val) := by
  intro s t hst hov M' hM'
  rcases hst with ⟨hsh, hex, hvk⟩ | hrw
  · obtain ⟨M, rfl, hM⟩ := fuel_split hp.K_pos hM'
    cases hsh with
    | litInt => simp only [evalExpr]; exact fs_pure (fun _ => rfl)
    | litBool => simp only [evalExpr]; exact fs_pure (fun _ => rfl)
    | litString => simp only [evalExpr]; exact fs_pure (fun _ => rfl)
    | litDecimal => simp only [evalExpr]; exact fs_pure (fun _ => rfl)
    | litBv => simp only [evalExpr]; exact fs_pure (fun _ => rfl)
    | @var v v' _ _ hv =>
      refine FS.vr ?_
      cases v <;> cases v' <;> simp only [VarRel] at hv
      · simp only [evalExpr]
        refine fs_bind fs_get (fun σ σ' hσ => ?_)
        have hσ : StRel G (IxRel E) σ σ' := hσ
        rw [← hv.1, lookupVar_congr hσ hv.2 (by have := hov.here.1; simpa [NodeOK] using this)]
        cases lookupVar σ _ with
        | none => exact fs_stuck _ _
        | some x => exact fs_pure rfl
      · simp only [evalExpr]
        exact fs_bind (exprMdE hp ih hv.1 (hvk _ _ _ _ rfl rfl) (by ovk) hM)
          (fun a b hab => by subst hab; simp only [strictField_none hp.cfg_ok.strict]; exact fs_readField _ _ _ hv.2)
      · simp only [evalExpr]; exact fs_evalError _ _
    | @hole d d' ty ty' _ _ hty =>
      refine FS.vr ?_
      simp only [evalExpr]
      refine fs_bind fs_get (fun σ σ' hσ => ?_)
      have hσ : StRel G (IxRel E) σ σ' := hσ
      rw [hσ.index.defaultR hty]
      exact fs_choose _ _ _
    | @ite c th c' th' el el' _ _ h1 h2 h3 =>
      simp only [ValKids] at hvk
      simp only [evalExpr]
      refine fs_bind (exprMdE hp ih h1 hvk.1 (by ovk) hM) (fun v v' hv => ?_)
      subst hv
      refine fs_bind (fs_liftM (isTrue_pconst v)) (fun b b' hb => ?_)
      subst hb
      refine fs_ite (fun _ => fs_wbs1 hp (hp.closed _ _ h2) ((ih.exprMd _ _ (hp.closed _ _ h2) (OvOK.relax (by ovk) _) M hM).weaken
          (fun _ _ h hv => h (hvk.2 hv).1)))
        (fun _ => ?_)
      cases el <;> cases el' <;> simp only [ORel] at h3
      · exact fs_pure (fun _ => rfl)
      · exact fs_wbs1 hp (hp.closed _ _ h3) ((ih.exprMd _ _ (hp.closed _ _ h3) (OvOK.relax (by ovk) _) M hM).weaken
          (fun _ _ h hv => h ((hvk.2 hv).2 _ _ rfl rfl)))
    | @block ss ss' l _ _ hss =>
      cases l with
      | none =>
        simp only [evalExpr]
        exact fs_wbs' (LX.decls_ext hp hss) (LX.decls_ok hp hss)
          ((ih.list _ _ _ hss (fun x hx => OvOK.relax (Hered.kid hov (by simp [stmtExprChildren, hx])) _) M hM).weaken
            (fun _ _ h hv => h (fun _ => hvk hv)))
      | some _ => simp only [evalExpr]; exact fs_evalError _ _
    | @new_ r r' o o' _ _ hr =>
      refine FS.vr ?_
      simp only [evalExpr, hp.cfg_ok.strict]
      refine fs_bind fs_get (fun σ σ' hσ => ?_)
      refine ?_
      have hσ : StRel G (IxRel E) σ σ' := hσ
      have hn := hr _ _ _ hσ.index.extra hσ.index.unalias
      have hfs := hσ.index.fields (σ.index.allocName r o).text
      rw [← hn, hσ.heap]
      refine fs_bind (fs_modifyRel (fun a a' ha => by strel ha)) (fun _ _ _ => ?_)
      refine fs_bind (fs_forIn hfs (fun a b hab c => ?_)) (fun _ _ _ => fs_pure rfl)
      rcases a with ⟨fn, fty, init⟩
      rcases b with ⟨fn', fty', init'⟩
      obtain ⟨h1, h2, h3, h4⟩ := hab
      dsimp only at h1 h2 h3 h4 ⊢
      subst h1
      have wr : ∀ x, FS (Sm E Gl G) Eq
          (do writeField (Value.ref σ.heap.size (σ.index.allocName r o).text) fn x; pure (ForInStep.yield PUnit.unit))
          (do writeField (Value.ref σ.heap.size (σ.index.allocName r o).text) fn x; pure (ForInStep.yield PUnit.unit)) :=
        fun x => fs_bind (fs_writeField _ _ _ rfl _) (fun _ _ _ => fs_pure rfl)
      cases init <;> cases init' <;> simp only [ORel] at h3
      · rw [hσ.index.defaultR h2]
        exact fs_bind (fs_pure rfl) (fun x y hxy => by subst hxy; exact wr x)
      · exact fs_bind (exprMdE hp ih h3 (h4.2 _ _ rfl rfl) (h4.1.ov _ rfl) hM) (fun x y hxy => by subst hxy; exact wr x)
    | @isType tg tg' ty ty' _ _ htg hty =>
      refine FS.vr ?_
      simp only [evalExpr, hp.cfg_ok.strict, Option.isSome_none, Bool.false_and, Bool.false_eq_true, ite_false]
      refine fs_bind (exprMdE hp ih htg hvk (by ovk) hM) (fun v v' hv => ?_)
      subst hv
      refine fs_bind fs_get (fun _ _ _ => ?_)
      refine ?_
      refine fs_bind fs_get (fun σ σ' hσ => ?_)
      have hσ : StRel G (IxRel E) σ σ' := hσ
      rw [isInstance_congr hσ hty]
      exact fs_liftM (hostOfExcept_pconst _)
    | @asType tg tg' ty ty' _ _ htg hty =>
      refine FS.vr ?_
      simp only [evalExpr, hp.cfg_ok.strict, Option.isSome_none, Bool.false_and, Bool.false_eq_true, ite_false]
      refine fs_bind (exprMdE hp ih htg hvk (by ovk) hM) (fun v v' hv => ?_)
      subst hv
      refine fs_bind fs_get (fun σ σ' hσ => ?_)
      have hσ : StRel G (IxRel E) σ σ' := hσ
      refine ?_
      rw [isInstance_congr hσ hty]
      refine fs_bind (fs_liftM (hostOfExcept_pconst _)) (fun r r' hr => ?_)
      subst hr
      refine fs_bind (fs_liftM (isTrue_pconst _)) (fun b b' hb => ?_)
      subst hb
      rw [hσ.muted]
      refine fs_ite (fun _ => fs_pure rfl) (fun _ => ?_)
      refine fs_bind (fs_emitE (S := Sm E Gl G) (evRel_fail (E := _)) ⟨rfl, trivial, rfl, _, hσ⟩) (fun _ _ _ => ?_)
      exact fs_ite (fun _ => fs_pure rfl)
        (fun _ => fs_bind (fs_modifyRel (fun a a' ha => by strel ha)) (fun _ _ _ => fs_pure rfl))
    | refEq ha hb =>
      refine FS.vr ?_
      simp only [ValKids] at hvk
      simp only [evalExpr]
      exact fs_bind (exprMdE hp ih ha hvk.1 (by ovk) hM) (fun x y hxy => by
        subst hxy
        exact fs_bind (exprMdE hp ih hb hvk.2 (by ovk) hM) (fun x' y' hxy' => by
          subst hxy'; exact fs_pure rfl))
    | @assert c c' m m' _ _ hc =>
      refine FS.vr ?_
      simp only [evalExpr]
      exact fs_bind (ih.stmt _ _ (.inl ⟨.assert hc, (fun _ _ h => by cases h), by exact hvk⟩) (hov.resrc _) M hM)
        (fun _ _ _ => fs_pure rfl)
    | @assume c c' _ _ hc =>
      refine FS.vr ?_
      simp only [evalExpr]
      exact fs_bind (ih.stmt _ _ (.inl ⟨.assume hc, (fun _ _ h => by cases h), by exact hvk⟩) (hov.resrc _) M hM)
        (fun _ _ _ => fs_pure rfl)
    | @old v v' l _ _ hv =>
      refine FS.vr ?_
      cases l with
      | some _ => simp only [evalExpr]; exact fs_evalError _ _
      | none =>
        simp only [evalExpr, hp.cfg_ok.strict, Option.isSome_none, Bool.false_and, Bool.false_eq_true, ite_false]
        refine fs_bind fs_get (fun σ σ' hσ => ?_)
        have hσ : StRel G (IxRel E) σ σ' := hσ
        have hE := hσ.entR
        rcases he : σ.entryState with _ | ⟨hh, gg, ii⟩ <;> rcases he' : σ'.entryState with _ | ⟨hh', gg', ii'⟩ <;>
          rw [he, he'] at hE
        · exact fs_evalError _ _
        · exact hE.elim
        · exact hE.elim
        · obtain ⟨rfl, hgl, hgg', hok⟩ := hE
          have hgg : ∀ k, NG k → gg.contains k = false := fun k hk => hσ.egk _ _ _ he k hk
          have hS : Strict G := by have := hov.here.1; simpa [NodeOK] using this
          refine fs_bind (fs_modifyRel (fun a a' ha => by
            have := hσ.stack.foldEnt hS (hσ.entryClean _ _ _ he) hok; have := hgl; have := hgg'; strel ha)) (fun _ _ _ => ?_)
          refine fs_bind (fs_tryCatch (exprMdE hp ih hv hvk (by ovk) hM)
            (fun sig hsig => fs_bind (fs_modifyRel (fun a a' ha => by
              have := hσ.stack; have := hσ.wf; have := hσ.gk; have := hσ.gk'; have := hσ.entR; have := hσ.globals; have := hσ.entryClean; have := hσ.egk; strelw ha [hσ.heap, hσ.inOld])) (fun _ _ _ => fs_throw sig hsig)) ?_
            (fun L hL hok => fs_bind (fs_modifyRel (fun a a' ha => by
              have := hσ.stack; have := hσ.wf; have := hσ.gk; have := hσ.gk'; have := hσ.entR; have := hσ.globals; have := hσ.entryClean; have := hσ.egk; strelw ha [hσ.heap, hσ.inOld])) (fun _ _ _ => fs_throwM hL hok))
            (fun w => fs_noWin _ hS.not_free w))
            (fun x y hxy => ?_)
          · intro σ τ
            simp [run_bind, run_throw, run_modify, OOF]
          · subst hxy
            refine fs_bind fs_get (fun a a' ha => ?_)
            have ha : StRel G (IxRel E) a a' := ha
            rw [ha.heap]
            refine fs_ite (fun _ => fs_bind (fs_modifyRel (fun b b' hb => by
              have := hσ.stack; have := hσ.wf; have := hσ.gk; have := hσ.gk'; have := hσ.entR; have := hσ.globals; have := hσ.entryClean; have := hσ.egk; strelw hb [hσ.heap, hσ.inOld])) (fun _ _ _ => fs_bind (fs_evalError (A := Eq) _ _)
                (fun _ _ _ => ?_))) (fun _ => ?_)
            all_goals exact fs_bind (fs_modifyRel (fun b b' hb => by
              have := hσ.stack; have := hσ.wf; have := hσ.gk; have := hσ.gk'; have := hσ.entR; have := hσ.globals; have := hσ.entryClean; have := hσ.egk; strelw hb [hσ.heap, hσ.inOld])) (fun _ _ _ => fs_pure rfl)
    | @assign ts ts' v v' _ _ hts hv hy hy' =>
      refine FS.vr ?_
      have hvk0 := hvk
      simp only [ValKids] at hvk
      cases hts with
      | nil =>
        simp only [evalExpr]
        exact fs_bind (ih.stmt _ _ (.inl ⟨.assign .nil hv hy hy', (fun _ _ h => by cases h), by exact hvk0⟩) (hov.resrc _) M hM)
          (fun _ _ _ => fs_pure rfl)
      | cons ht hr =>
        cases hr with
        | nil =>
          simp only [evalExpr]
          refine fs_bind (ih.assign _ _ ht.1 (L2.head (R := fun (a b : VariableMd) => VV E a.val b.val) hvk.1) ht.2 (fun c hc => Hered.kid hov (by simp [stmtExprChildren, hc])) M hM)
            (fun u u' hu => ?_)
          exact fs_bind (exprMdE hp ih hv hvk.2 (by ovk) hM) (fun x y hxy => by
            subst hxy
            exact fs_bind (fs_writeUpdate _ _ hu _) (fun _ _ _ => fs_pure rfl))
        | cons ht2 hr2 =>
          simp only [evalExpr]
          exact fs_bind (ih.stmt _ _ (.inl ⟨.assign (.cons ht (.cons ht2 hr2)) hv hy hy', (fun _ _ h => by cases h), by exact hvk0⟩)
            (hov.resrc _) M hM)
            (fun _ _ _ => fs_pure rfl)
    | @incr md o t t' _ _ ht hw =>
      refine FS.vr ?_
      simp only [evalExpr]
      refine fs_bind (ih.update _ _ ht hvk hw (fun c hc => Hered.kid hov (by simp [stmtExprChildren, hc]))
        (fun a ha => hov.here.1 a (by rw [ha])) M hM)
        (fun a b hab => ?_)
      rcases a with ⟨x, u⟩
      rcases b with ⟨x', u'⟩
      obtain ⟨hx, hu⟩ := hab
      dsimp only at hx hu ⊢
      subst hx
      refine fs_bind (fs_liftM (evalOp_pconst hp.cfg_ok _ _)) (fun y y' hy => ?_)
      subst hy
      exact fs_bind (fs_writeUpdate _ _ hu _) (fun _ _ _ => fs_pure rfl)
    | @compound o t t' r r' _ _ ht hw hr hop =>
      refine FS.vr ?_
      simp only [ValKids] at hvk
      simp only [evalExpr]
      refine fs_bind (ih.update _ _ ht hvk.1 hw (fun c hc => Hered.kid hov (by simp [stmtExprChildren, hc]))
        (fun a ha => hov.here.1 a (by rw [ha])) M hM)
        (fun a b hab => ?_)
      rcases a with ⟨x, u⟩
      rcases b with ⟨x', u'⟩
      obtain ⟨hx, hu⟩ := hab
      dsimp only at hx hu ⊢
      subst hx
      refine fs_bind (exprMdE hp ih hr hvk.2 (by ovk) hM) (fun y y' hy => ?_)
      subst hy
      have rest : FS (Sm E Gl G) Eq
          (do
            let new ← liftM (evalOp cfg o [x, y])
            writeUpdate u new
            pure new)
          (do
            let new ← liftM (evalOp cfg o [x, y])
            writeUpdate u' new
            pure new) :=
        fs_bind (fs_liftM (evalOp_pconst hp.cfg_ok _ _)) (fun z z' hz => by
          subst hz; exact fs_bind (fs_writeUpdate _ _ hu _) (fun _ _ _ => fs_pure rfl))
      cases o
      all_goals first
        | exact rest
        | exact fs_bind (fs_pure rfl) (fun _ _ _ => rest)
        | (refine fs_bind fs_get (fun σ σ' hσ => ?_)
           have hσ : StRel G (IxRel E) σ σ' := hσ
           have hd := divProc_congr hσ.index .Div x hop
           revert hd
           cases divProc? σ.index .Div x <;> cases divProc? σ'.index .Div x <;>
             simp only [ORel, false_implies, true_implies]
           · exact fs_bind (fs_noFitPrelude hσ.index _ hop _) (fun _ _ _ => rest)
           · exact fun hP => fs_bind (ih.pre _ _ _ _ _ hP.toB M hM) (fun _ _ _ => rest))
        | (refine fs_bind fs_get (fun σ σ' hσ => ?_)
           have hσ : StRel G (IxRel E) σ σ' := hσ
           have hd := divProc_congr hσ.index .Mod x hop
           revert hd
           cases divProc? σ.index .Mod x <;> cases divProc? σ'.index .Mod x <;>
             simp only [ORel, false_implies, true_implies]
           · exact fs_bind (fs_noFitPrelude hσ.index _ hop _) (fun _ _ _ => rest)
           · exact fun hP => fs_bind (ih.pre _ _ _ _ _ hP.toB M hM) (fun _ _ _ => rest))
        | (refine fs_bind fs_get (fun σ σ' hσ => ?_)
           have hσ : StRel G (IxRel E) σ σ' := hσ
           have hd := divProc_congr hσ.index .DivT x hop
           revert hd
           cases divProc? σ.index .DivT x <;> cases divProc? σ'.index .DivT x <;>
             simp only [ORel, false_implies, true_implies]
           · exact fs_bind (fs_noFitPrelude hσ.index _ hop _) (fun _ _ _ => rest)
           · exact fun hP => fs_bind (ih.pre _ _ _ _ _ hP.toB M hM) (fun _ _ _ => rest))
        | (refine fs_bind fs_get (fun σ σ' hσ => ?_)
           have hσ : StRel G (IxRel E) σ σ' := hσ
           have hd := divProc_congr hσ.index .ModT x hop
           revert hd
           cases divProc? σ.index .ModT x <;> cases divProc? σ'.index .ModT x <;>
             simp only [ORel, false_implies, true_implies]
           · exact fs_bind (fs_noFitPrelude hσ.index _ hop _) (fun _ _ _ => rest)
           · exact fun hP => fs_bind (ih.pre _ _ _ _ _ hP.toB M hM) (fun _ _ _ => rest))
    | @icall tg tg' f f' as as' _ _ _ _ htg hf has hr hrm hid =>
      refine FS.vr ?_
      simp only [ValKids, LV] at hvk
      simp only [evalExpr]
      refine fs_bind fs_get (fun σ σ' hσ => ?_)
      refine fs_bind (exprMdE hp ih htg hvk.1 (by ovk) hM) (fun v v' hv => ?_)
      subst hv
      refine fs_bind (fs_mapM (has.and hvk.2).withMem (fun a b hab => exprMdE hp ih hab.1.1 hab.1.2 (Hered.kid hov (by simp [stmtExprChildren, hab.2])) hM)) (fun xs ys hxs => ?_)
      subst hxs
      refine fs_ite (fun _ => ?_) (fun _ => fs_bind (fs_resolveMethod _ _ _ hf hr hrm) (fun P P' hP =>
        fs_bind (ih.proc _ _ _ _ _ hP.toB M hM) (fun a b hab => by subst hab; exact fs_pure rfl)))
      icall_mod
    | call has hta hf =>
      exact FS.vr (fstep_call hp ih hM has hvk (fun a ha => Hered.kid hov (by simp [stmtExprChildren, ha])) hta hf)
    | unsup hu hu' => rw [unsup_expr hu, unsup_expr hu']; exact fs_evalError _ _
    | holeNone => refine FS.vr ?_; simp only [evalExpr]; exact fs_choose _ _ _
    | @quant md p p' tr tr' b b' _ _ hn ht hr hvq hb =>
      refine FS.vr ?_
      simp only [evalExpr]
      refine fs_bind fs_get (fun σq σq' hσq => ?_)
      have hσq : StRel G (IxRel E) σq σq' := hσq
      rw [hσq.index.unalias _ _ ht, ← hn]
      cases hce : cfg.canEnumerate
      · simp only [Bool.false_eq_true, ↓reduceIte]
        first
        | exact fs_refuse_bind _ _ _ _
        | exact fs_refuse _ _
      simp only [↓reduceIte]
      refine fs_bind (fs_liftM (hp.cfg_ok.enumerate _)) (fun vals vals' hv => ?_)
      subst hv
      refine fs_bind (fs_forIn (L2.refl vals) (fun v v' hvv acc => ?_)) (fun r r' hr' => ?_)
      · subst hvv
        refine fs_bind (fs_modifyRel (fun a a' ha => ha.with_stack (ha.stack.bindCatch hr hvq v))) (fun _ _ _ => ?_)
        refine fs_bind (fs_tryCatch (fs_bind (exprMdE hp ih hb hvk (by ovk) hM)
          (fun x y hxy => by subst hxy; exact fs_liftM (isTrue_pconst x))) (fun sig hsig => ?_) ?_
          (fun L hL hok => fs_bind (fs_modifyRel (fun a a' ha => ha.with_stack (ha.stack.unbindCatch hr hvq)))
            (fun _ _ _ => fs_throwM hL hok))
          (fun w => fs_bind (fs_modify (S := (Sm E Gl G).atWin w)
            (fun a a' h => win_unbind (Gl := Gl) h hr hvq)) (fun _ _ _ => fs_throwW w)))
          (fun c c' hcc => ?_)
        · exact fs_bind (fs_modifyRel (fun a a' ha => ha.with_stack (ha.stack.unbindCatch hr hvq)))
            (fun _ _ _ => fs_throw _ hsig)
        · intro σ τ
          simp [run_bind, run_throw, run_modify, OOF]
        · subst hcc
          exact fs_bind (fs_modifyRel (fun a a' ha => ha.with_stack (ha.stack.unbindCatch hr hvq)))
            (fun _ _ _ => fs_pure rfl)
      · subst hr'
        exact fs_pure rfl
    | @ret v v' _ _ hl hv =>
      refine FS.vr ?_
      simp only [evalExpr]
      exact fs_bind (ih.stmt ⟨.Return v, .unknown⟩ ⟨.Return v', .unknown⟩ (.inl ⟨.ret hl hv, ⟨(fun l d h => by simp at h), hvk⟩⟩)
        (OvOK.resrc hov _) M hM) (fun _ _ _ => fs_pure rfl)
    | @jump l d _ _ =>
      refine FS.vr ?_
      simp only [evalExpr]
      exact fs_bind (ih.stmt ⟨.Goto l d, .unknown⟩ ⟨.Goto l d, .unknown⟩ (.inl ⟨.jump, ⟨(fun l' d' h => hex l' d' h), trivial⟩⟩)
        (OvOK.resrc hov _) M hM) (fun _ _ _ => fs_pure rfl)
    | _ => simp only [evalExpr]; exact fs_evalError _ _
  · exact (hp.step n ihs).expr s t hrw hov M' hM'

omit [Reserved] hp in
theorem fs_vac {A : α → β → Prop} {S T U : SimRel} {x : EvalM PM α} {y : EvalM PM β} (h : x = throw .outOfFuel) :
    FSH S T U A x y :=
  ⟨fun σ _ τ _ _ _ hn => absurd (by rw [h]; exact trivial) hn⟩

/-- Given `PassRel cfg E Rw K Gl`, `FundAt cfg E Rw K Gl k` holds for every `k ≤ n`, for every `n`.
This is the induction on fuel behind `fund`. -/
theorem fund_le : ∀ n, ∀ k ≤ n, FundAt cfg E Rw K Gl k
  | 0 => fun k hk => by
      obtain rfl : k = 0 := by omega
      exact {
        scoped_ := fun _ _ _ _ _ _ => fs_vac rfl
        exprMd := fun _ _ _ _ _ _ => fs_vac rfl
        expr := fun _ _ _ _ _ _ => fs_vac rfl
        stmt := fun _ _ _ _ _ _ => fs_vac rfl
        outputs := fun _ _ _ _ _ _ => fs_vac rfl
        assign := fun _ _ _ _ _ _ _ _ => fs_vac rfl
        update := fun _ _ _ _ _ _ _ _ _ => fs_vac rfl
        iter := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fs_vac rfl
        blockLoop := fun _ _ _ _ _ _ _ _ _ _ => fs_vac rfl
        blockFrom := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => fs_vac rfl
        stmtFrom := fun _ _ _ _ _ _ _ _ _ _ => fs_vac rfl
        runFrom := fun _ _ _ _ _ _ _ _ _ _ _ => fs_vac rfl
        fin := fun _ _ _ _ _ _ _ _ _ => fs_vac rfl
        finish := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fs_vac rfl
        clauses := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fs_vac rfl
        list := fun _ _ _ _ _ _ _ => fs_vac rfl
        callee := fun _ _ _ _ _ _ _ => fs_vac rfl
        pre := fun _ _ _ _ _ _ _ _ => fs_vac rfl
        post := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fs_vac rfl
        proc := fun _ _ _ _ _ _ _ _ => fs_vac rfl }
  | n + 1 => fun k hk => by
      have ihs := fund_le n
      rcases Nat.lt_or_ge k (n + 1) with h | h
      · exact ihs k (by omega)
      obtain rfl : k = n + 1 := by omega
      have ih := ihs n (Nat.le_refl n)
      exact {
        scoped_ := fstep_scoped hp ih ihs
        exprMd := fstep_exprMd hp ih ihs
        expr := fstep_expr hp ih ihs
        stmt := fstep_stmt hp ih ihs
        outputs := fstep_outputs hp ih ihs
        assign := fstep_assign hp ih
        update := fstep_update hp ih
        iter := fstep_iter hp ih
        blockLoop := fstep_blockLoop hp ih
        blockFrom := fstep_blockFrom hp ih
        stmtFrom := fstep_stmtFrom hp ih
        runFrom := fstep_runFrom hp ih ihs
        fin := fstep_fin hp ih
        finish := fstep_finish hp ih
        clauses := fstep_clauses hp ih
        list := fstep_list hp ih ihs
        callee := fstep_callee hp ih
        pre := fstep_pre hp ih
        post := fstep_post hp ih
        proc := fstep_proc hp ih ihs }

/-- The fundamental simulation theorem: given `PassRel cfg E Rw K Gl`, for every fuel `n` and every
interpreter function, running it with fuel `n` on a source term is simulated (`FS (Sm E Gl G)`) by
running it with any fuel `M ≥ K * n` on a target term related by `NR E Rw Gl`, for source terms that
satisfy the pass's node condition `OvOK G` (`FundAt`). -/
theorem fund (n : Nat) : FundAt cfg E Rw K Gl n := fund_le hp n n (Nat.le_refl n)

end Steps

end Strata.Laurel.PassSemantics
