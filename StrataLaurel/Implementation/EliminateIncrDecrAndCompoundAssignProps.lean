/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.LaurelPassProps
public import StrataLaurel.Implementation.LaurelASTProps
public import StrataLaurel.Implementation.EliminateIncrDecrAndCompoundAssign
import all StrataLaurel.Implementation.EliminateIncrDecrAndCompoundAssign
import all StrataLaurel.Implementation.MapStmtExpr

/-!
# EliminateIncrDecrAndCompoundAssign Properties

Proves that `eliminateIncrDecrAndCompoundAssignPass` does what its `NodeKind`
declarations say:

```
Contains s p → Contains ((s \ pass.removes) ∪ pass.creates) (pass.run opts p model).1
```

so no `StmtExpr.IncrDecr` and no `StmtExpr.CompoundAssign` survives, and the
lowering introduces only `Assign`, `Block`, static `Call`, `Var` and `Var.var.Field`.

The key result is `eliminateIncrDecr_spec`. It reuses `mapStmtExprUsedM_contains`
and `ProgramLift.lift_program` unchanged, instantiated at `StateM`, whose state
numbers the fresh receiver locals.

The one part specific to this pass is `rewriteNode_contains`: the lowered form
`x := x ⊕ rhs` reads its own target, which is where `Var` and — for a field
target — `Var.var.Field` come from, and a compound assignment's operator becomes
a call to that operator's built-in wrapper, so the operator's own kind is carried
across rather than created (`ofProcName?_procName`).
-/

namespace Strata.Laurel

namespace ElimIncrDecrProps

open EliminateIncrDecr

public section

/-! ## The pass's declared effect -/

/-- The kind set `eliminateIncrDecrAndCompoundAssignPass` claims to map `s` into. -/
@[expose] def outSet (s : KindSet) : KindSet :=
  (s \ KindSet.ofList eliminateIncrDecrAndCompoundAssignPass.removes)
    ∪ KindSet.ofList eliminateIncrDecrAndCompoundAssignPass.creates

/-- A kind the pass creates is in the output set, whatever the input set. -/
private theorem mem_outSet_of_creates {s : KindSet} {k : NodeKind}
    (hk : k ∈ eliminateIncrDecrAndCompoundAssignPass.creates) : k ∈ outSet s :=
  KindSet.mem_union.mpr (Or.inr (KindSet.mem_ofList.mpr hk))

/-- A kind of the input survives unless it is one of the two the pass removes. -/
private theorem mem_outSet_of_mem {s : KindSet} {k : NodeKind} (hk : k ∈ s)
    (h1 : k ≠ NodeKind.StmtExpr.IncrDecr) (h2 : k ≠ NodeKind.StmtExpr.CompoundAssign) :
    k ∈ outSet s :=
  KindSet.mem_union.mpr (Or.inl (KindSet.mem_sdiff.mpr ⟨hk, by
    simp [KindSet.mem_ofList, eliminateIncrDecrAndCompoundAssignPass, h1, h2]⟩))

/-- Type annotations carry across: no `HighType` kind is one the pass removes. -/
private theorem ContainsType.toOut {s : KindSet} {ty : HighTypeMd} (h : ContainsType s ty) :
    ContainsType (outSet s) ty := by
  induction h with
  | node ty head kids ih =>
    refine .node ty (fun k hk => ?_) (fun c hc => ih c hc)
    rcases ofHighType_mem hk with h1 | h1 <;> exact mem_outSet_of_mem (head k hk) (by simp [h1])
      (by simp [h1])

/-- No container kind is one the pass removes, so the generic lift applies. -/
private theorem containerKinds_ne :
    ∀ k ∈ containerKinds, k ≠ NodeKind.StmtExpr.IncrDecr
      ∧ k ≠ NodeKind.StmtExpr.CompoundAssign := by decide

/-! ## `rewriteNode`

The pass is pure, so these are plain facts about `rewriteNode`; `post_id` lifts
them into the `Id` postcondition the traversal lemma asks for. -/

variable (recvType : StmtExprMd → Option Identifier)

/-- Neither lowered form is a bare local read: `lowerIncrDecr` and `lowerOpAssign` never
    return a `Var (.Local _)` node. -/
private theorem lowered_not_isVarLocal (mode : IncrDecrMode) (op : IncrDecrOp) (opn : Operation)
    (t : VariableMd) (rhs : StmtExprMd) (src : FileRange) :
    ¬ isVarLocal (lowerIncrDecr mode op t src) ∧ ¬ isVarLocal (lowerOpAssign opn t rhs src) := by
  constructor
  · simp only [lowerIncrDecr, lowerToAssign, lowerOpAssign]
    split <;> simp [isVarLocal]
  · simp [lowerOpAssign, isVarLocal]

/-- If `lower` never returns a bare local read, then `withReceiverBound` never returns
    one either, so its result satisfies every `Q` that holds of all terms that are
    not bare local reads. -/
private theorem withReceiverBound_isVarLocal (target : VariableMd) (lower : VariableMd → StmtExprMd)
    (src : FileRange) (hlower : ∀ t, ¬ isVarLocal (lower t)) {Q : StmtExprMd → Prop}
    (hQ : ∀ e', ¬ isVarLocal e' → Q e') : PostM (withReceiverBound recvType target lower src) Q := by
  rw [withReceiverBound]
  split
  · exact post_bind_any (fun _ => post_pure (hQ _ (by simp [isVarLocal])))
  · exact post_pure (hQ _ (hlower _))

/-- `rewriteNode` returns its input, a `Block`, an `Assign`, or a static `Call`, so it
    never turns something else into a bare local read. -/
private theorem rewriteNode_shapeStable :
    ShapeStable (fun (_ : Bool) e => rewriteNode recvType e) := by
  intro _ e
  show PostM (rewriteNode recvType e) _
  rw [rewriteNode]
  split
  · exact withReceiverBound_isVarLocal recvType _ _ _
      (fun t => (lowered_not_isVarLocal _ _ .Add t ⟨.LiteralInt 1, e.source⟩ e.source).1)
      (Q := fun e' => isVarLocal e' → isVarLocal e) (fun _ h h' => absurd h' h)
  · exact withReceiverBound_isVarLocal recvType _ _ _
      (fun t => (lowered_not_isVarLocal .Pre .Incr _ t _ e.source).2)
      (Q := fun e' => isVarLocal e' → isVarLocal e) (fun _ h h' => absurd h' h)
  · exact post_pure (fun h => h)

/-- The read side of a target contributes `Var`, and `Var.var.Field` for a field
    target — both declared — and its only child is the target's own object
    subtree. -/
private theorem targetAsRead_contains {s : KindSet} {target : VariableMd}
    (hkids : ∀ c ∈ variableChildren target.val, Contains (outSet s) c) :
    Contains (outSet s) (targetAsRead target) := by
  rw [targetAsRead]
  split
  case h_1 name heq =>
    refine .node _ (fun k hk => ?_) (by simp [stmtExprTypes, variableTypes])
      (by intro c hc; simp [stmtExprChildren, variableChildren] at hc)
    have hk' : k = NodeKind.StmtExpr.Var := by
      simpa [NodeKind.ofStmtExpr, NodeKind.ofVariable] using hk
    exact mem_outSet_of_creates (by simp [hk', eliminateIncrDecrAndCompoundAssignPass])
  case h_2 tgt fieldName heq =>
    refine .node _ (fun k hk => ?_) (by simp [stmtExprTypes, variableTypes]) ?_
    · refine mem_outSet_of_creates ?_
      have hk' : k = NodeKind.StmtExpr.Var ∨ k = NodeKind.StmtExpr.Var.var.Field := by
        simpa [NodeKind.ofStmtExpr, NodeKind.ofVariable] using hk
      rcases hk' with h1 | h1 <;> simp [h1, eliminateIncrDecrAndCompoundAssignPass]
    · intro c hc
      simp only [stmtExprChildren, variableChildren, List.mem_singleton] at hc
      exact hc ▸ hkids tgt (by rw [heq]; simp [variableChildren])
  case h_3 param heq =>
    refine .node _ (fun k hk => ?_) (by simp [stmtExprTypes, variableTypes])
      (by intro c hc; simp [stmtExprChildren, variableChildren] at hc)
    have hk' : k = NodeKind.StmtExpr.Var := by
      simpa [NodeKind.ofStmtExpr, NodeKind.ofVariable] using hk
    exact mem_outSet_of_creates (by simp [hk', eliminateIncrDecrAndCompoundAssignPass])
  case h_4 t heq =>
    refine .node _ (fun k hk => ?_) (by simp [stmtExprTypes, variableTypes])
      (by intro c hc; simp [stmtExprChildren, variableChildren] at hc)
    have hk' : k = NodeKind.StmtExpr.Var := by
      simpa [NodeKind.ofStmtExpr, NodeKind.ofVariable] using hk
    exact mem_outSet_of_creates (by simp [hk', eliminateIncrDecrAndCompoundAssignPass])

/-- `x := x ⊕ rhs`: an `Assign` whose value is a call to the operator's wrapper,
    reading the target. The operator's own kind, if it has one, is carried over
    from the input rather than created. -/
private theorem lowerOpAssign_contains {s : KindSet} {primOp : Operation}
    {target : VariableMd} {rhs : StmtExprMd} {src : FileRange}
    (hop : ∀ k ∈ NodeKind.ofOperation primOp, k ∈ s)
    (htypes : ∀ ty ∈ variableTypes target.val, ContainsType s ty)
    (hkids : ∀ c ∈ variableChildren target.val, Contains (outSet s) c)
    (hrhs : Contains (outSet s) rhs) :
    Contains (outSet s) (lowerOpAssign primOp target rhs src) := by
  have hcall : Contains (outSet s)
      (⟨.Call none (mkId primOp.procName) [targetAsRead target, rhs] [], src⟩ : StmtExprMd) := by
    refine .node _ (fun k hk => ?_) (by simp [stmtExprTypes]) ?_
    · simp only [NodeKind.ofStmtExpr, NodeKind.ofCallee, mkId, List.mem_cons,
        ofProcName?_procName] at hk
      rcases hk with h1 | h1
      · exact mem_outSet_of_creates (by simp [h1, eliminateIncrDecrAndCompoundAssignPass])
      · rcases ofOperation_mem h1 with h2 | h2 <;>
          exact mem_outSet_of_mem (hop _ h1) (by simp [h2]) (by simp [h2])
    · intro c hc
      simp only [stmtExprChildren, Option.toList_none, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc
      · exact hc ▸ targetAsRead_contains hkids
      · exact hc ▸ hrhs
  rw [lowerOpAssign]
  refine .node _ (fun k hk => ?_) (fun ty hty => ?_) ?_
  · have hk' : k = NodeKind.StmtExpr.Assign := by simpa [NodeKind.ofStmtExpr] using hk
    exact mem_outSet_of_creates (by simp [hk', eliminateIncrDecrAndCompoundAssignPass])
  · refine ContainsType.toOut (htypes ty ?_)
    simpa [stmtExprTypes] using hty
  · intro c hc
    simp only [stmtExprChildren, List.mem_append, List.mem_flatMap,
      List.mem_singleton] at hc
    rcases hc with ⟨t, ht, hc⟩ | hc
    · exact hkids c (ht ▸ hc)
    · exact hc ▸ hcall

/-- Lowering `++`/`--` on a target whose own types are in `s` and whose children are
    already in the output set lands in the output set. -/
private theorem lowerIncrDecr_contains {s : KindSet} {mode : IncrDecrMode} {op : IncrDecrOp}
    {target : VariableMd} {src : FileRange}
    (htypes' : ∀ ty ∈ variableTypes target.val, ContainsType s ty)
    (hkids' : ∀ c ∈ variableChildren target.val, Contains (outSet s) c) :
    Contains (outSet s) (lowerIncrDecr mode op target src) := by
  have hone : Contains (outSet s) (⟨.LiteralInt 1, src⟩ : StmtExprMd) :=
    .node _ (by simp [NodeKind.ofStmtExpr]) (by simp [stmtExprTypes])
      (by simp [stmtExprChildren])
  have hassign : ∀ primOp : Operation, NodeKind.ofOperation primOp = [] →
      Contains (outSet s) (lowerOpAssign primOp target ⟨.LiteralInt 1, src⟩ src) := fun primOp hp =>
    lowerOpAssign_contains (by simp [hp]) htypes' hkids' hone
  simp only [lowerIncrDecr, lowerToAssign]
  split
  · cases op <;> exact hassign _ (by simp [NodeKind.ofOperation])
  · refine .node _ (fun k hk => ?_) (by simp [stmtExprTypes]) ?_
    · simp only [NodeKind.ofStmtExpr, NodeKind.ofCallee, mkId, List.mem_cons,
        ofProcName?_procName] at hk
      rcases hk with h1 | h1
      · exact mem_outSet_of_creates (by simp [h1, eliminateIncrDecrAndCompoundAssignPass])
      · cases op <;> simp [NodeKind.ofOperation] at h1
    · intro c hc
      simp only [stmtExprChildren, Option.toList_none, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc
      · refine hc ▸ ?_
        cases op <;> exact hassign _ (by simp [NodeKind.ofOperation])
      · exact hc ▸ hone

/-- Binding a field target's receiver keeps everything in the output set: the
    `Block` and the `Assign` declaring the receiver are declared kinds, the receiver
    itself was already rewritten, and the new target `$recv_n#f` reads a plain local. -/
private theorem withReceiverBound_contains {s : KindSet} {target : VariableMd}
    {lower : VariableMd → StmtExprMd} {src : FileRange}
    (htypes : ∀ ty ∈ variableTypes target.val, ContainsType s ty)
    (hkids : ∀ c ∈ variableChildren target.val, Contains (outSet s) c)
    (hlower : ∀ t : VariableMd, (∀ ty ∈ variableTypes t.val, ContainsType s ty) →
      (∀ c ∈ variableChildren t.val, Contains (outSet s) c) → Contains (outSet s) (lower t)) :
    PostM (withReceiverBound recvType target lower src) (Contains (outSet s)) := by
  rw [withReceiverBound]
  split
  case h_1 tgt fieldName heq =>
    refine post_bind_any (fun recv => post_pure ?_)
    have htgt : Contains (outSet s) tgt := hkids tgt (by rw [heq]; simp [variableChildren])
    have hrecv : Contains (outSet s) (⟨.Var (.Local recv), tgt.source⟩ : StmtExprMd) := by
      refine .node _ (fun k hk => ?_) (by simp [stmtExprTypes, variableTypes])
        (by intro c hc; simp [stmtExprChildren, variableChildren] at hc)
      have hk' : k = NodeKind.StmtExpr.Var := by
        simpa [NodeKind.ofStmtExpr, NodeKind.ofVariable] using hk
      exact mem_outSet_of_creates (by simp [hk', eliminateIncrDecrAndCompoundAssignPass])
    have hbind : Contains (outSet s)
        (⟨.Assign [⟨.Declare ⟨recv, (recvType tgt).map fun n => (⟨.UserDefined n, tgt.source⟩ : HighTypeMd)⟩,
          tgt.source⟩] tgt, tgt.source⟩ : StmtExprMd) := by
      have hty : ∀ ty ∈ ((recvType tgt).map fun n => (⟨.UserDefined n, tgt.source⟩ : HighTypeMd)).toList,
          ContainsType (outSet s) ty := by
        intro ty hty
        rcases hr : recvType tgt with _ | n <;> simp only [hr, Option.map_none, Option.map_some, Option.toList_none, Option.toList_some, List.mem_cons, List.not_mem_nil, or_false] at hty
        subst hty
        exact .node _ (by simp [NodeKind.ofHighType]) (by simp [highTypeChildren])
      refine .node _ (fun k hk => ?_) (by simpa [stmtExprTypes, variableTypes] using hty) ?_
      · have hk' : k = NodeKind.StmtExpr.Assign := by simpa [NodeKind.ofStmtExpr] using hk
        exact mem_outSet_of_creates (by simp [hk', eliminateIncrDecrAndCompoundAssignPass])
      · intro c hc
        simp only [stmtExprChildren, variableChildren, List.flatMap_cons, List.flatMap_nil,
          List.nil_append, List.append_nil, List.mem_singleton] at hc
        exact hc ▸ htgt
    have hlow := hlower ⟨.Field ⟨.Var (.Local recv), tgt.source⟩ fieldName, target.source⟩
      (by simp [variableTypes])
      (by intro c hc; simp only [variableChildren, List.mem_singleton] at hc; exact hc ▸ hrecv)
    refine .node _ (fun k hk => ?_) (by simp [stmtExprTypes]) ?_
    · have hk' : k = NodeKind.StmtExpr.Block := by simpa [NodeKind.ofStmtExpr] using hk
      exact mem_outSet_of_creates (by simp [hk', eliminateIncrDecrAndCompoundAssignPass])
    · intro c hc
      simp only [stmtExprChildren, List.nil_append, Option.toList_none, List.mem_cons, List.not_mem_nil,
        or_false] at hc
      rcases hc with hc | hc
      · exact hc ▸ hbind
      · exact hc ▸ hlow
  case h_2 hne =>
    exact post_pure (hlower _ htypes hkids)

/-- The per-node obligation the traversal asks for: rewriting one node maps every
    kind of the lowered result into the output set. -/
private theorem rewriteNode_contains (s : KindSet) (e : StmtExprMd)
    (h : Rebuilt s (outSet s) e) : PostM (rewriteNode recvType e) (Contains (outSet s)) := by
  obtain ⟨hhead, htypes, hkids⟩ := h
  rw [rewriteNode]
  split
  case h_1 mode op target heq =>
    rw [heq] at hhead htypes hkids
    exact withReceiverBound_contains recvType
      (fun ty hty => htypes ty (by simpa [stmtExprTypes] using hty))
      (fun c hc => hkids c (by simpa [stmtExprChildren] using hc))
      (fun _ ht hk => lowerIncrDecr_contains ht hk)
  case h_2 op target rhs heq =>
    rw [heq] at hhead htypes hkids
    exact withReceiverBound_contains recvType
      (fun ty hty => htypes ty (by simpa [stmtExprTypes] using hty))
      (fun c hc => hkids c (by simp [stmtExprChildren, hc]))
      (fun _ ht hk => lowerOpAssign_contains (fun k hk' => hhead k (by simp [NodeKind.ofStmtExpr, hk']))
        ht hk (hkids rhs (by simp [stmtExprChildren])))
  case h_3 hne1 hne2 =>
    refine post_pure (.node e (fun k hk => ?_) (fun ty hty => ContainsType.toOut (htypes ty hty)) hkids)
    refine mem_outSet_of_mem (hhead k hk) ?_ ?_
    · intro hk'
      obtain ⟨mode, op, target, hv⟩ := ofStmtExpr_incrDecr (hk' ▸ hk)
      exact absurd hv (hne1 mode op target)
    · intro hk'
      obtain ⟨op, target, rhs, hv⟩ := ofStmtExpr_compoundAssign (hk' ▸ hk)
      exact absurd hv (hne2 op target rhs)

/-- Rewriting one expression bottom-up maps every kind of it into `outSet s`. -/
private theorem elim_stmtExpr {s : KindSet} {e : StmtExprMd} (h : Contains s e) :
    PostM (mapStmtExprM (rewriteNode recvType) e) (Contains (outSet s)) :=
  mapStmtExprUsedM_contains (fun _ e => rewriteNode recvType e) s (outSet s)
    (fun _ e he => rewriteNode_contains recvType s e he) (rewriteNode_shapeStable recvType) h false

/-- The three facts the generic program-level lift asks of a pass: the
    per-expression rewrite maps kinds into `outSet`, type annotations carry
    across, and no container kind is one this pass removes. -/
private theorem elim_lift (s : KindSet) : ProgramLift.Lift (rewriteNode recvType) s (outSet s) where
  expr h := elim_stmtExpr recvType h
  type h := ContainsType.toOut h
  keep k hk hks := mem_outSet_of_mem hks (containerKinds_ne k hk).1 (containerKinds_ne k hk).2

/-! ## The specification of `eliminateIncrDecrAndCompoundAssignPass` -/

/-- **The specification.** If every node kind in `p` is in `s`, then every node kind
    of the pass's output is in `(s \ pass.removes) ∪ pass.creates`: no `IncrDecr`
    and no `CompoundAssign` remains, and the lowering introduces no kind it does
    not declare. -/
theorem eliminateIncrDecr_spec (s : KindSet) (opts : LaurelTranslateOptions)
    (model : SemanticModel) (p : Program) (h : Program.Contains s p) :
    Program.Contains
      ((s \ KindSet.ofList eliminateIncrDecrAndCompoundAssignPass.removes)
        ∪ KindSet.ofList eliminateIncrDecrAndCompoundAssignPass.creates)
      (eliminateIncrDecrAndCompoundAssignPass.run opts p model).1 := by
  have hrun := ProgramLift.lift_program (elim_lift (receiverBaseType p model) s) h {}
  simpa [eliminateIncrDecrAndCompoundAssignPass, eliminateIncrDecrAndCompoundAssign,
    outSet, StateT.run] using hrun

end -- public section

end ElimIncrDecrProps

end Strata.Laurel
