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
lowering introduces only `Assign`, `StaticCall`, `Var` and `Var.var.Field`.

The key result is `eliminateIncrDecr_spec`. It reuses `mapStmtExprUsedM_contains`
and `ProgramLift.lift_program` unchanged; this pass is pure, so everything is
instantiated at the `Id` monad rather than `StateM`.

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

/-- `rewriteNode` returns its input, an `Assign`, or a `StaticCall`, so it never
    turns something else into a bare local read. The `Var` it builds is nested
    inside, which `ShapeStable` does not constrain. -/
private theorem rewriteNode_isVarLocal (e : StmtExprMd) :
    isVarLocal (rewriteNode e) → isVarLocal e := by
  rw [rewriteNode]
  split
  · simp only [lowerIncrDecr, lowerToAssign, lowerOpAssign]
    split <;> simp [isVarLocal]
  · simp [lowerOpAssign, isVarLocal]
  · exact fun h => h

/-- The traversal's side condition for this pass: a lowered node is a bare local
    read only if the node it replaced was one. -/
private theorem rewriteNode_shapeStable :
    ShapeStable (m := Id) (fun (_ : Bool) e => rewriteNode e) :=
  fun _ e => post_id (rewriteNode_isVarLocal e)

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
      (⟨.StaticCall (mkId primOp.procName) [targetAsRead target, rhs], src⟩ : StmtExprMd) := by
    refine .node _ (fun k hk => ?_) (by simp [stmtExprTypes]) ?_
    · simp only [NodeKind.ofStmtExpr, NodeKind.ofCallee, mkId, List.mem_cons,
        ofProcName?_procName] at hk
      rcases hk with h1 | h1
      · exact mem_outSet_of_creates (by simp [h1, eliminateIncrDecrAndCompoundAssignPass])
      · rcases ofOperation_mem h1 with h2 | h2 <;>
          exact mem_outSet_of_mem (hop _ h1) (by simp [h2]) (by simp [h2])
    · intro c hc
      simp only [stmtExprChildren, List.mem_cons, List.not_mem_nil, or_false] at hc
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

/-- The per-node obligation: every kind of a lowered node is in the output set. -/
private theorem rewriteNode_contains' {s : KindSet} {e : StmtExprMd}
    (h : Rebuilt s (outSet s) e) : Contains (outSet s) (rewriteNode e) := by
  obtain ⟨hhead, htypes, hkids⟩ := h
  rw [rewriteNode]
  split
  case h_1 mode op target heq =>
    rw [heq] at hhead htypes hkids
    have hkids' : ∀ c ∈ variableChildren target.val, Contains (outSet s) c := fun c hc =>
      hkids c (by simpa [stmtExprChildren] using hc)
    have htypes' : ∀ ty ∈ variableTypes target.val, ContainsType s ty := fun ty hty =>
      htypes ty (by simpa [stmtExprTypes] using hty)
    have hone : Contains (outSet s) (⟨.LiteralInt 1, e.source⟩ : StmtExprMd) :=
      .node _ (by simp [NodeKind.ofStmtExpr]) (by simp [stmtExprTypes])
        (by simp [stmtExprChildren])
    have hassign : ∀ primOp : Operation, NodeKind.ofOperation primOp = [] →
        Contains (outSet s)
          (lowerOpAssign primOp target ⟨.LiteralInt 1, e.source⟩ e.source) := fun primOp hp =>
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
        simp only [stmtExprChildren, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with hc | hc
        · refine hc ▸ ?_
          cases op <;> exact hassign _ (by simp [NodeKind.ofOperation])
        · exact hc ▸ hone
  case h_2 op target rhs heq =>
    rw [heq] at hhead htypes hkids
    refine lowerOpAssign_contains (fun k hk => hhead k ?_) (fun ty hty => htypes ty ?_)
      (fun c hc => hkids c ?_) (hkids rhs ?_)
    · simp [NodeKind.ofStmtExpr, hk]
    · simpa [stmtExprTypes] using hty
    · simp [stmtExprChildren, hc]
    · simp [stmtExprChildren]
  case h_3 hne1 hne2 =>
    refine .node e (fun k hk => ?_) (fun ty hty => ContainsType.toOut (htypes ty hty)) hkids
    refine mem_outSet_of_mem (hhead k hk) ?_ ?_
    · intro hk'
      obtain ⟨mode, op, target, hv⟩ := ofStmtExpr_incrDecr (hk' ▸ hk)
      exact absurd hv (hne1 mode op target)
    · intro hk'
      obtain ⟨op, target, rhs, hv⟩ := ofStmtExpr_compoundAssign (hk' ▸ hk)
      exact absurd hv (hne2 op target rhs)

/-- The per-node obligation the traversal asks for, at the `Id` monad: rewriting
    one node maps every kind of the lowered result into the output set. -/
private theorem rewriteNode_contains (s : KindSet) (e : StmtExprMd)
    (h : Rebuilt s (outSet s) e) :
    PostM (m := Id) (rewriteNode e) (Contains (outSet s)) :=
  post_id (rewriteNode_contains' h)

/-- Rewriting one expression bottom-up maps every kind of it into `outSet s`. -/
private theorem elim_stmtExpr {s : KindSet} {e : StmtExprMd} (h : Contains s e) :
    Contains (outSet s) (mapStmtExpr rewriteNode e) :=
  mapStmtExprUsedM_contains (m := Id) (fun _ e => rewriteNode e) s (outSet s)
    (fun _ e he => rewriteNode_contains s e he) rewriteNode_shapeStable h false

/-- The three facts the generic program-level lift asks of a pass: the
    per-expression rewrite maps kinds into `outSet`, type annotations carry
    across, and no container kind is one this pass removes. -/
private theorem elim_lift (s : KindSet) :
    ProgramLift.Lift (m := Id) rewriteNode s (outSet s) where
  expr h := elim_stmtExpr h
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
  have hrun := ProgramLift.lift_program (elim_lift s) h
  simpa [eliminateIncrDecrAndCompoundAssignPass, eliminateIncrDecrAndCompoundAssign,
    outSet, mapProgramStmtExpr] using hrun

end -- public section

end ElimIncrDecrProps

end Strata.Laurel
