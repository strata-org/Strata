/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.LaurelPassProps
public import StrataLaurel.Implementation.EliminateDoWhile
public import StrataLaurel.Implementation.LaurelASTProps
import all StrataLaurel.Implementation.EliminateDoWhile
import all StrataLaurel.Implementation.MapStmtExpr

/-!
# EliminateDoWhile Properties

Proves that `eliminateDoWhilePass` does what its `NodeKind` declarations say:

```
Contains s p → Contains ((s \ pass.removes) ∪ pass.creates) (pass.run opts p model).1
```

The key result is `eliminateDoWhile_spec`. Reading it needs two definitions:
`Contains` (`LaurelNodeKindProps.lean`) and `outSet`, the set
`(s \ pass.removes) ∪ pass.creates` the declarations promise. The per-node
obligation the traversal leaves is `rewriteNode_contains`, and
`rewriteNode_shapeStable` discharges the traversal's `ShapeStable` side condition;
`elim_program` is the lift from one expression to a whole program.
`sampleProgram_doWhile_eliminated` instantiates the theorem on a loop outside any
procedure.

Everything here is about *this* pass. The reusable half — the `PostM` calculus
for `StateM` postconditions, and `mapStmtExprUsedM_contains`, which lifts a
per-node obligation through the shared bottom-up traversal — lives in
`MapStmtExprProps.lean`, so the next pass's specification does not repeat it.
-/

namespace Strata.Laurel

namespace ElimDoWhileProps

open EliminateDoWhile

public section

/-! ## The pass's declared effect

`outSet s` is `(s \ removes) ∪ creates` for `eliminateDoWhilePass`: the set its
declarations promise the output lives in. -/

/-- The kind set `eliminateDoWhilePass` claims to map `s` into. -/
@[expose] def outSet (s : KindSet) : KindSet :=
  (s \ KindSet.ofList eliminateDoWhilePass.removes) ∪ KindSet.ofList eliminateDoWhilePass.creates

/-- A kind the pass creates is in the output set, whatever the input set. -/
private theorem mem_outSet_of_creates {s : KindSet} {k : NodeKind}
    (hk : k ∈ eliminateDoWhilePass.creates) : k ∈ outSet s :=
  KindSet.mem_union.mpr (Or.inr (KindSet.mem_ofList.mpr hk))

/-- A kind of the input survives into the output set unless it is the one the
    pass removes. -/
private theorem mem_outSet_of_mem {s : KindSet} {k : NodeKind} (hk : k ∈ s)
    (hne : k ≠ NodeKind.StmtExpr.While.postTest.true) : k ∈ outSet s :=
  KindSet.mem_union.mpr (Or.inl (KindSet.mem_sdiff.mpr ⟨hk, by
    simp [KindSet.mem_ofList, eliminateDoWhilePass, hne]⟩))

/-- Dropping the removed kind from `s` lands inside the output set. -/
private theorem sdiff_removes_subset_outSet (s : KindSet) :
    KindSet.Subset (s \ KindSet.ofList eliminateDoWhilePass.removes) (outSet s) :=
  fun _ hk => KindSet.mem_union.mpr (Or.inl hk)

/-- Type annotations therefore move to the output set unconditionally. -/
private theorem ContainsType.toOut {s : KindSet} {ty : HighTypeMd} (h : ContainsType s ty) :
    ContainsType (outSet s) ty := by
  induction h with
  | node ty head kids ih =>
    refine .node ty (fun k hk => mem_outSet_of_mem (head k hk) ?_) (fun c hc => ih c hc)
    rcases ofHighType_mem hk with h1 | h1 <;> simp [h1]

/-- A subtree free of post-test loops moves to the output set. -/
private theorem Contains.toOut {s : KindSet} {e : StmtExprMd}
    (h : Contains (s \ KindSet.ofList eliminateDoWhilePass.removes) e) :
    Contains (outSet s) e :=
  h.mono (sdiff_removes_subset_outSet s)

/-! ## `rewriteNode` -/

/-- `rewriteNode` never turns something else into a bare local read: it either
    returns its input or a `Block`. This is what `ShapeStable` asks. -/
private theorem rewriteNode_shapeStable : ShapeStable (fun (_ : Bool) e => rewriteNode e) := by
  intro u e
  show PostM (rewriteNode e) _
  rw [rewriteNode]
  split
  · exact post_bind_any (fun _ => post_pure (by simp [isVarLocal]))
  · exact post_pure (fun h => h)

/-- The crux: the desugaring `{ while(true) invariant I { BODY; if (!COND) exit L } } L`
    uses only kinds the pass declares in `creates`, keeps every child in the
    output set, and emits a pre-test loop — so the removed kind is gone. -/
private theorem rewriteNode_contains (s : KindSet) (e : StmtExprMd) (h : Rebuilt s (outSet s) e) :
    PostM (rewriteNode e) (Contains (outSet s)) := by
  obtain ⟨hhead, htypes, hkids⟩ := h
  rw [rewriteNode]
  split
  case h_1 cond invs dec body heq =>
    rw [heq] at hhead htypes hkids
    refine post_bind_any (fun exitLabel => post_pure ?_)
    have hcond : Contains (outSet s) cond := hkids cond (by simp [stmtExprChildren])
    have hbody : Contains (outSet s) body := hkids body (by simp [stmtExprChildren])
    -- `!COND`
    have hnot : Contains (outSet s)
        (⟨.StaticCall (mkId Operation.Not.procName) [cond], e.source⟩ : StmtExprMd) := by
      refine .node _ (fun k hk => mem_outSet_of_creates ?_) (by simp [stmtExprTypes]) ?_
      · have hk' : k = NodeKind.StmtExpr.StaticCall := by
          simpa [NodeKind.ofStmtExpr, NodeKind.ofCallee, NodeKind.ofOperation,
            Operation.procName, Operation.ofProcName?, mkId] using hk
        simp [hk', eliminateDoWhilePass]
      · intro c hc
        simp only [stmtExprChildren, List.mem_singleton] at hc
        exact hc ▸ hcond
    -- `exit L`
    have hexit : Contains (outSet s) (⟨.Exit exitLabel, e.source⟩ : StmtExprMd) := by
      refine .node _ (fun k hk => mem_outSet_of_creates ?_) (by simp [stmtExprTypes]) ?_
      · have hk' : k = NodeKind.StmtExpr.Exit := by simpa [NodeKind.ofStmtExpr] using hk
        simp [hk', eliminateDoWhilePass]
      · intro c hc; simp [stmtExprChildren] at hc
    -- `if (!COND) exit L`
    have hguard : Contains (outSet s)
        (⟨.IfThenElse ⟨.StaticCall (mkId Operation.Not.procName) [cond], e.source⟩
          ⟨.Exit exitLabel, e.source⟩ none, e.source⟩ : StmtExprMd) := by
      refine .node _ (fun k hk => mem_outSet_of_creates ?_) (by simp [stmtExprTypes]) ?_
      · have hk' : k = NodeKind.StmtExpr.IfThenElse := by simpa [NodeKind.ofStmtExpr] using hk
        simp [hk', eliminateDoWhilePass]
      · intro c hc
        simp only [stmtExprChildren, List.mem_cons, Option.toList_none,
          List.append_nil, List.not_mem_nil, or_false] at hc
        rcases hc with hc | hc
        · exact hc ▸ hnot
        · exact hc ▸ hexit
    -- `{ BODY; if (!COND) exit L }`
    have hloopBody : Contains (outSet s)
        (⟨.Block [body, ⟨.IfThenElse ⟨.StaticCall (mkId Operation.Not.procName) [cond], e.source⟩
          ⟨.Exit exitLabel, e.source⟩ none, e.source⟩] none, e.source⟩ : StmtExprMd) := by
      refine .node _ (fun k hk => mem_outSet_of_creates ?_) (by simp [stmtExprTypes]) ?_
      · have hk' : k = NodeKind.StmtExpr.Block := by simpa [NodeKind.ofStmtExpr] using hk
        simp [hk', eliminateDoWhilePass]
      · intro c hc
        simp only [stmtExprChildren, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with hc | hc
        · exact hc ▸ hbody
        · exact hc ▸ hguard
    -- `while(true) invariant I { … }`, pre-test
    have hwhile : Contains (outSet s)
        (⟨.While ⟨.LiteralBool true, e.source⟩ invs dec
          ⟨.Block [body, ⟨.IfThenElse ⟨.StaticCall (mkId Operation.Not.procName) [cond], e.source⟩
            ⟨.Exit exitLabel, e.source⟩ none, e.source⟩] none, e.source⟩ false,
          e.source⟩ : StmtExprMd) := by
      refine .node _ (fun k hk => ?_) (by simp [stmtExprTypes]) ?_
      · -- the emitted loop is pre-test, so its only kind is `StmtExpr.While`
        have hk' : k = NodeKind.StmtExpr.While := by
          simpa [NodeKind.ofStmtExpr] using hk
        exact mem_outSet_of_creates (by simp [hk', eliminateDoWhilePass])
      · intro c hc
        simp only [stmtExprChildren, List.mem_cons, List.mem_append, Option.mem_toList,
          List.not_mem_nil, or_false] at hc
        rcases hc with ((hc | hc) | hc) | hc
        · refine hc ▸ .node _ (fun k hk => ?_) (by simp [stmtExprTypes]) ?_
          · have hk' : k = NodeKind.StmtExpr.LiteralBool := by
              simpa [NodeKind.ofStmtExpr] using hk
            exact mem_outSet_of_creates (by simp [hk', eliminateDoWhilePass])
          · intro c' hc'; simp [stmtExprChildren] at hc'
        · exact hkids c (by simp [stmtExprChildren, hc])
        · exact hkids c (by simp [stmtExprChildren, hc])
        · exact hc ▸ hloopBody
    -- `{ while(true) … } L`
    refine .node _ (fun k hk => ?_) (by simp [stmtExprTypes]) ?_
    · have hk' : k = NodeKind.StmtExpr.Block := by simpa [NodeKind.ofStmtExpr] using hk
      exact mem_outSet_of_creates (by simp [hk', eliminateDoWhilePass])
    · intro c hc
      simp only [stmtExprChildren, List.mem_cons, List.not_mem_nil, or_false] at hc
      exact hc ▸ hwhile
  case h_2 hne =>
    refine post_pure (.node e (fun k hk => ?_) (fun ty hty => ContainsType.toOut (htypes ty hty)) hkids)
    refine mem_outSet_of_mem (hhead k hk) ?_
    intro hk'
    obtain ⟨cond, invs, dec, body, hv⟩ := ofStmtExpr_postTest_true (hk' ▸ hk)
    exact absurd hv (hne cond invs dec body)

/-- Rewriting one expression bottom-up maps every kind of it into `outSet s`,
    by discharging the two obligations of `mapStmtExprUsedM_contains`. -/
private theorem elim_stmtExpr {s : KindSet} {e : StmtExprMd} (h : Contains s e) :
    PostM (mapStmtExprM rewriteNode e) (Contains (outSet s)) :=
  mapStmtExprUsedM_contains (fun _ e => rewriteNode e) s (outSet s)
    (fun _ e he => rewriteNode_contains s e he) rewriteNode_shapeStable h false


/-! ## Applying the generic program-level lift -/

/-- No container kind is the one this pass removes, so the generic lift applies. -/
private theorem containerKinds_ne_postTest :
    ∀ k ∈ containerKinds, k ≠ NodeKind.StmtExpr.While.postTest.true := by decide

/-- The three facts `ProgramLift.lift_program` asks of a pass. -/
private theorem elim_lift (s : KindSet) : ProgramLift.Lift rewriteNode s (outSet s) where
  expr h := elim_stmtExpr h
  type h := ContainsType.toOut h
  keep k hk hks := mem_outSet_of_mem hks (containerKinds_ne_postTest k hk)

/-! ## The specification of `eliminateDoWhilePass`

`Contains s p` says every node kind in `p` is in `s`. The theorem says: run the
pass on such a program and every kind of the result is in
`(s \ removes) ∪ creates` — the pass's own declarations. In particular
`StmtExpr.While.postTest.true` is *gone* (that is what `removes` claims) and no
kind outside `creates` has appeared.

There is no side condition: `eliminateDoWhile` walks `mapProgramStmtExprM`, which
reaches every expression position in a program — procedures (body, specification
fields and, via `mapProcedureM`, a coroutine's `relies`/`guarantees`), a
constrained type's constraint and witness, a composite's field initializers,
constant initializers and file-scope globals' initializers. -/
/-- **The specification of `eliminateDoWhilePass`.** If every node kind in `p` is
    in `s`, then every node kind of the pass's output is in
    `(s \ pass.removes) ∪ pass.creates`: the pass removes every post-test `While`
    and introduces no kind it does not declare. -/
theorem eliminateDoWhile_spec (s : KindSet) (opts : LaurelTranslateOptions)
    (model : SemanticModel) (p : Program) (h : Program.Contains s p) :
    Program.Contains
      ((s \ KindSet.ofList eliminateDoWhilePass.removes)
        ∪ KindSet.ofList eliminateDoWhilePass.creates)
      (eliminateDoWhilePass.run opts p model).1 := by
  have hrun := ProgramLift.lift_program (elim_lift s) h {}
  simpa [eliminateDoWhilePass, eliminateDoWhile, outSet, StateT.run] using hrun

/-! ## A do-while outside a procedure

The sample below puts a post-test loop in a file-scope global's initializer — a
position outside any procedure — and the theorem is `eliminateDoWhile_spec`
applied to it with the set of *all* kinds as input. The conclusion's kind set
excludes `StmtExpr.While.postTest.true` (see `postTest_not_mem_outSet`), so it
says the loop is gone. -/

/-- A `do … while` loop, as a closed term. -/
def sampleDoWhile : StmtExprMd :=
  ⟨.While ⟨.LiteralBool true, .unknown⟩ [] none ⟨.Block [] none, .unknown⟩ true, .unknown⟩

/-- A file-scope global whose initializer is that loop. -/
def sampleField : Field where
  name := mkId "g"
  isMutable := false
  type := ⟨.TInt, .unknown⟩
  initializer := some sampleDoWhile

/-- The sample program: one global, whose initializer is that loop. -/
def sampleProgram : Program where
  staticProcedures := []
  staticFields := [sampleField]
  types := []
  constants := []

/-- Every kind of the sample program is in the universal kind set. -/
private theorem sampleProgram_contains : Program.Contains (fun _ => True) sampleProgram := by
  have hleaf : ∀ (v : StmtExpr), stmtExprChildren v = [] → stmtExprTypes v = [] →
      Contains (fun _ => True) (⟨v, .unknown⟩ : StmtExprMd) := fun v hc ht =>
    .node _ (fun _ _ => trivial) (by simp [ht]) (by simp [hc])
  have hlit : Contains (fun _ => True) (⟨.LiteralBool true, .unknown⟩ : StmtExprMd) :=
    hleaf _ (by simp [stmtExprChildren]) (by simp [stmtExprTypes])
  have hblock : Contains (fun _ => True) (⟨.Block [] none, .unknown⟩ : StmtExprMd) :=
    hleaf _ (by simp [stmtExprChildren]) (by simp [stmtExprTypes])
  have hdw : Contains (fun _ => True) sampleDoWhile := by
    refine .node _ (fun _ _ => trivial) (by simp [sampleDoWhile, stmtExprTypes]) ?_
    intro c hc
    simp only [sampleDoWhile, stmtExprChildren, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false, Option.toList_none] at hc
    rcases hc with hc | hc
    · exact hc ▸ hlit
    · exact hc ▸ hblock
  refine ⟨⟨by simp [sampleProgram], by simp [sampleProgram]⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro hne; trivial
  · intro fld hfld
    simp only [sampleProgram, List.mem_singleton] at hfld
    subst hfld
    exact ⟨.node _ (fun _ _ => trivial) (by simp [sampleField, highTypeChildren]), by
      intro e he
      simp only [sampleField, Option.mem_def, Option.some.injEq] at he
      exact he ▸ hdw⟩
  · intro hne; trivial
  · intro td htd; simp [sampleProgram] at htd
  · intro c hc; simp [sampleProgram] at hc

/-- The loop in the global's initializer is eliminated: the output's kinds avoid
    `StmtExpr.While.postTest.true`, because `outSet` removes it and `creates` does
    not put it back. -/
theorem sampleProgram_doWhile_eliminated (opts : LaurelTranslateOptions)
    (model : SemanticModel) :
    Program.Contains (outSet (fun _ => True))
      (eliminateDoWhilePass.run opts sampleProgram model).1 :=
  eliminateDoWhile_spec _ opts model sampleProgram sampleProgram_contains

/-- The removed kind is absent from the output set whenever the input set already
    excludes it — so a `Contains (outSet …)` conclusion states its absence. -/
theorem postTest_not_mem_outSet (s : KindSet) :
    NodeKind.StmtExpr.While.postTest.true ∉
      outSet (fun k => k ∈ s ∧ k ≠ NodeKind.StmtExpr.While.postTest.true) := by
  simp [outSet, KindSet.mem_union, KindSet.mem_sdiff, KindSet.mem_ofList,
    eliminateDoWhilePass]

end -- public section

end ElimDoWhileProps

end Strata.Laurel
