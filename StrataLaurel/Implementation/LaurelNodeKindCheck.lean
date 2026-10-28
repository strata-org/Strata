/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.LaurelNodeKindProps

namespace Strata.Laurel

public section

abbrev KindSet.ofPred (s : NodeKind → Bool) : KindSet := fun k => s k = true

private theorem highTypeChildren_sizeOf_lt (t c : HighTypeMd) (h : c ∈ highTypeChildren t.val) :
    sizeOf c < sizeOf t := by
  have ht := AstNode.sizeOf_val_lt t
  rcases t with ⟨v, src⟩
  cases v <;> simp only [highTypeChildren, List.mem_cons, List.not_mem_nil, or_false] at h ht ⊢
  all_goals first
    | (rcases h with rfl | rfl <;> simp_all <;> omega)
    | (subst h; simp_all; omega)
    | (have := List.sizeOf_lt_of_mem h; simp_all; omega)
    | (rcases h with rfl | h
       · simp_all; omega
       · have := List.sizeOf_lt_of_mem h; simp_all; omega)

def containsTypeB (s : NodeKind → Bool) (t : HighTypeMd) : Bool :=
  (NodeKind.ofHighType t.val).all s
    && (highTypeChildren t.val).attach.all fun ⟨c, _⟩ => containsTypeB s c
termination_by sizeOf t
decreasing_by exact highTypeChildren_sizeOf_lt t c ‹_›

private theorem containsTypeB_sound (s : NodeKind → Bool) (t : HighTypeMd)
    (h : containsTypeB s t = true) : ContainsType (KindSet.ofPred s) t := by
  rw [containsTypeB] at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact .node t (fun k hk => h.1 k hk)
    (fun c hc => containsTypeB_sound s c (h.2 ⟨c, hc⟩ (List.mem_attach _ _)))
termination_by sizeOf t
decreasing_by exact highTypeChildren_sizeOf_lt t c hc


private theorem variableChildren_sizeOf_lt (v : Variable) (c : StmtExprMd)
    (h : c ∈ variableChildren v) : sizeOf c < sizeOf v := by
  cases v <;> simp only [variableChildren, List.mem_cons, List.not_mem_nil, or_false] at h
  subst h; simp <;> omega

private theorem stmtExprChildren_sizeOf_lt (e c : StmtExprMd) (h : c ∈ stmtExprChildren e.val) :
    sizeOf c < sizeOf e := by
  have he := AstNode.sizeOf_val_lt e
  rcases e with ⟨v, src⟩
  simp only at he
  cases v <;> simp only [stmtExprChildren, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_flatMap, Option.mem_toList] at h
  all_goals repeat' (first | (obtain h | h := (h : _ ∨ _)) | (obtain ⟨a, ha, h⟩ := (h : ∃ _, _)))
  all_goals refine Nat.lt_trans ?_ he
  all_goals first
    | (subst_vars; simp <;> omega)
    | (have := List.sizeOf_lt_of_mem h; simp <;> omega)
    | (have := variableChildren_sizeOf_lt _ _ h; simp <;> omega)
    | (have := variableChildren_sizeOf_lt _ _ h
       have := AstNode.sizeOf_val_lt ‹AstNode Variable›
       simp <;> omega)
    | (have := variableChildren_sizeOf_lt _ _ h
       have := AstNode.sizeOf_val_lt a
       have := List.sizeOf_lt_of_mem ha
       simp <;> omega)
    | (have hmem := List.sizeOf_lt_of_mem ha
       have hpred := CatchClause.sizeOf_predicate_lt a
       rw [h] at hpred
       simp at hmem hpred ⊢ <;> omega)
    | (have := List.sizeOf_lt_of_mem ha
       have := CatchClause.sizeOf_body_lt a
       subst h; simp <;> omega)

def containsB (s : NodeKind → Bool) (e : StmtExprMd) : Bool :=
  (NodeKind.ofStmtExpr e.val).all s
    && (stmtExprTypes e.val).all (containsTypeB s)
    && (stmtExprChildren e.val).attach.all fun ⟨c, _⟩ => containsB s c
termination_by sizeOf e
decreasing_by exact stmtExprChildren_sizeOf_lt e c ‹_›

private theorem containsB_sound (s : NodeKind → Bool) (e : StmtExprMd)
    (h : containsB s e = true) : Contains (KindSet.ofPred s) e := by
  rw [containsB] at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact .node e (fun k hk => h.1.1 k hk) (fun t ht => containsTypeB_sound s t (h.1.2 t ht))
    (fun c hc => containsB_sound s c (h.2 ⟨c, hc⟩ (List.mem_attach _ _)))
termination_by sizeOf e
decreasing_by exact stmtExprChildren_sizeOf_lt e c hc

private def consB (s : NodeKind → Bool) (l : List α) (k : NodeKind) : Bool := l.isEmpty || s k

private def someB (s : NodeKind → Bool) (o : Option α) (k : NodeKind) : Bool := o.isNone || s k

private theorem consB_sound {s : NodeKind → Bool} {l : List α} {k : NodeKind}
    (h : consB s l k = true) : ConsKind (KindSet.ofPred s) l k := by
  intro hne
  cases l with
  | nil => exact absurd rfl hne
  | cons => show s k = true; simpa [consB] using h

private theorem someB_sound {s : NodeKind → Bool} {o : Option α} {k : NodeKind}
    (h : someB s o k = true) : SomeKind (KindSet.ofPred s) o k := by
  intro hs
  cases o with
  | none => simp at hs
  | some => show s k = true; simpa [someB] using h

private def Condition.containsB (s : NodeKind → Bool) (c : Condition) : Bool :=
  Laurel.containsB s c.condition
    && match c.mode with
       | .Assume => s NodeKind.Condition.mode.Assume
       | _ => true

private theorem Condition.containsB_sound (s : NodeKind → Bool) (c : Condition)
    (h : Condition.containsB s c = true) : Condition.Contains (KindSet.ofPred s) c := by
  simp only [Condition.containsB, Bool.and_eq_true] at h
  refine ⟨Laurel.containsB_sound s _ h.1, fun hm => ?_⟩
  have h2 := h.2
  rw [hm] at h2
  exact h2

private def Parameter.containsB (s : NodeKind → Bool) (p : Parameter) : Bool :=
  containsTypeB s p.type

private def Body.containsB (s : NodeKind → Bool) (b : Body) : Bool :=
  match b with
  | .Transparent body => Laurel.containsB s body
  | .Opaque postconditions implementation modifies =>
    postconditions.all (Condition.containsB s)
      && consB s postconditions NodeKind.Body.postconditions.cons
      && implementation.all (Laurel.containsB s)
      && modifies.all (fun g => g.targets.all (Laurel.containsB s) && g.guard.all (Laurel.containsB s))
      && consB s modifies NodeKind.Body.modifies.cons
  | .Abstract postconditions =>
    postconditions.all (Condition.containsB s)
      && consB s postconditions NodeKind.Body.postconditions.cons
  | .External => true

private def CoroutineContracts.containsB (s : NodeKind → Bool) (c : CoroutineContracts) : Bool :=
  c.relies.all (Condition.containsB s)
    && c.guarantees.all (Condition.containsB s)
    && c.yields.all (Parameter.containsB s)
    && c.resumes.all (Parameter.containsB s)
    && match c.kind with
       | .Coroutine => s NodeKind.Procedure.contracts.Coroutine
       | _ => true

private def ThrowsOnBlock.containsB (s : NodeKind → Bool) (b : ThrowsOnBlock) : Bool :=
  Laurel.containsB s b.guard
    && b.postconditions.all (Condition.containsB s)
    && b.modifies.all (Laurel.containsB s)

private def Procedure.containsB (s : NodeKind → Bool) (p : Procedure) : Bool :=
  p.inputs.all (Parameter.containsB s)
    && consB s p.inputs NodeKind.Procedure.inputs.cons
    && p.outputs.all (Parameter.containsB s)
    && p.preconditions.all (Condition.containsB s)
    && consB s p.preconditions NodeKind.Procedure.preconditions.cons
    && CoroutineContracts.containsB s p.contracts
    && p.decreases.all (Laurel.containsB s)
    && Body.containsB s p.body
    && p.invokeOn.all (Laurel.containsB s)
    && p.axioms.all (Laurel.containsB s)
    && p.throwsType.all (containsTypeB s)
    && someB s p.throwsType NodeKind.Procedure.throwsType.some
    && p.throwsOn.all (ThrowsOnBlock.containsB s)
    && consB s p.throwsOn NodeKind.Procedure.throwsOn.cons

private def Field.containsB (s : NodeKind → Bool) (f : Field) : Bool :=
  containsTypeB s f.type && f.initializer.all (Laurel.containsB s)

private def TypeDefinition.containsOutsideProceduresB (s : NodeKind → Bool)
    (td : TypeDefinition) : Bool :=
  match td with
  | .Composite c =>
    s NodeKind.TypeDefinition.Composite
      && consB s c.typeArgs NodeKind.CompositeType.typeArgs.cons
      && c.extending.all (containsTypeB s)
      && c.fields.all (Field.containsB s)
      && consB s c.instanceProcedures NodeKind.CompositeType.instanceProcedures.cons
  | .Constrained c =>
    s NodeKind.TypeDefinition.Constrained
      && containsTypeB s c.base && Laurel.containsB s c.constraint && Laurel.containsB s c.witness
  | .Datatype d =>
    s NodeKind.TypeDefinition.Datatype
      && d.constructors.all (fun ctor => ctor.args.all (Parameter.containsB s))
  | .Alias a => s NodeKind.TypeDefinition.Alias && containsTypeB s a.target
  | .Opaque _ => true

def LaurelProgram.containsB (s : NodeKind → Bool) (p : LaurelProgram) : Bool :=
  p.staticProcedures.all (Procedure.containsB s)
    && p.staticFunctions.all (Procedure.containsB s)
    && p.types.all (fun td => match td with
         | .Composite c => c.instanceProcedures.all (Procedure.containsB s)
         | _ => true)
    && consB s p.staticProcedures NodeKind.LaurelProgram.staticProcedures.cons
    && consB s p.staticFunctions NodeKind.LaurelProgram.staticFunctions.cons
    && p.staticFields.all (Field.containsB s)
    && consB s p.staticFields NodeKind.LaurelProgram.staticFields.cons
    && p.types.all (TypeDefinition.containsOutsideProceduresB s)
    && p.constants.all (fun c => containsTypeB s c.type && c.initializer.all (Laurel.containsB s))

private def Constant.containsB (s : NodeKind → Bool) (c : Constant) : Bool :=
  containsTypeB s c.type && c.initializer.all (Laurel.containsB s)

private def OrderedDecl.containsB (s : NodeKind → Bool) : OrderedDecl → Bool
  | .funcs fs _ => fs.all (Procedure.containsB s)
  | .procedure proc => Procedure.containsB s proc
  | .datatypes dts =>
    dts.all fun d => s NodeKind.TypeDefinition.Datatype
      && d.constructors.all (fun ctor => ctor.args.all (Parameter.containsB s))
  | .opaqueType _ => true
  | .constant c => Constant.containsB s c

def Program.containsB (s : NodeKind → Bool) : Program → Bool
  | .Unordered p => s NodeKind.Program.Unordered && LaurelProgram.containsB s p
  | .Ordered (.WithLaurelTypes p) =>
    s NodeKind.Program.Ordered && s NodeKind.OrderedProgram.WithLaurelTypes
      && p.decls.all (OrderedDecl.containsB s)
  | .Ordered (.Core _) => s NodeKind.Program.Ordered && s NodeKind.OrderedProgram.Core

private theorem all_sound {l : List α} {f : α → Bool} {P : α → Prop}
    (hf : ∀ x, f x = true → P x) (h : l.all f = true) : ∀ x ∈ l, P x := by
  intro x hx
  exact hf x (List.all_eq_true.mp h x hx)

private theorem optAll_sound {o : Option α} {f : α → Bool} {P : α → Prop}
    (hf : ∀ x, f x = true → P x) (h : o.all f = true) : ∀ x ∈ o, P x := by
  intro x hx
  cases o with
  | none => cases hx
  | some y => cases hx; exact hf _ (by simpa using h)

private theorem Body.containsB_sound (s : NodeKind → Bool) (b : Body)
    (h : Body.containsB s b = true) : Body.Contains (KindSet.ofPred s) b := by
  cases b with
  | Transparent body => exact Laurel.containsB_sound s body h
  | Opaque posts impl mods =>
    simp only [Body.containsB, Bool.and_eq_true, and_assoc] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    refine ⟨all_sound (Condition.containsB_sound s) h1, consB_sound h2,
      optAll_sound (Laurel.containsB_sound s) h3, all_sound (fun g hg => ?_) h4, consB_sound h5⟩
    simp only [Bool.and_eq_true] at hg
    exact ⟨all_sound (Laurel.containsB_sound s) hg.1, optAll_sound (Laurel.containsB_sound s) hg.2⟩
  | Abstract posts =>
    simp only [Body.containsB, Bool.and_eq_true] at h
    exact ⟨all_sound (Condition.containsB_sound s) h.1, consB_sound h.2⟩
  | External => trivial

private theorem CoroutineContracts.containsB_sound (s : NodeKind → Bool) (c : CoroutineContracts)
    (h : CoroutineContracts.containsB s c = true) :
    CoroutineContracts.Contains (KindSet.ofPred s) c := by
  simp only [CoroutineContracts.containsB, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨all_sound (Condition.containsB_sound s) h1, all_sound (Condition.containsB_sound s) h2,
    all_sound (fun p hp => containsTypeB_sound s p.type hp) h3,
    all_sound (fun p hp => containsTypeB_sound s p.type hp) h4, fun hk => ?_⟩
  rw [hk] at h5
  exact h5

private theorem ThrowsOnBlock.containsB_sound (s : NodeKind → Bool) (b : ThrowsOnBlock)
    (h : ThrowsOnBlock.containsB s b = true) : ThrowsOnBlock.Contains (KindSet.ofPred s) b := by
  simp only [ThrowsOnBlock.containsB, Bool.and_eq_true, and_assoc] at h
  exact ⟨Laurel.containsB_sound s _ h.1, all_sound (Condition.containsB_sound s) h.2.1,
    all_sound (Laurel.containsB_sound s) h.2.2⟩

private theorem Procedure.containsB_sound (s : NodeKind → Bool) (p : Procedure)
    (h : Procedure.containsB s p = true) : Procedure.Contains (KindSet.ofPred s) p := by
  simp only [Procedure.containsB, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨all_sound (fun p hp => containsTypeB_sound s p.type hp) h1, consB_sound h2,
    all_sound (fun p hp => containsTypeB_sound s p.type hp) h3,
    all_sound (Condition.containsB_sound s) h4, consB_sound h5,
    CoroutineContracts.containsB_sound s _ h6, optAll_sound (Laurel.containsB_sound s) h7,
    Body.containsB_sound s _ h8, optAll_sound (Laurel.containsB_sound s) h9,
    all_sound (Laurel.containsB_sound s) h10, optAll_sound (containsTypeB_sound s) h11,
    someB_sound h12, all_sound (ThrowsOnBlock.containsB_sound s) h13, consB_sound h14⟩

private theorem Field.containsB_sound (s : NodeKind → Bool) (f : Field)
    (h : Field.containsB s f = true) : Field.Contains (KindSet.ofPred s) f := by
  simp only [Field.containsB, Bool.and_eq_true] at h
  exact ⟨containsTypeB_sound s _ h.1, optAll_sound (Laurel.containsB_sound s) h.2⟩

private theorem TypeDefinition.containsOutsideProceduresB_sound (s : NodeKind → Bool)
    (td : TypeDefinition) (h : TypeDefinition.containsOutsideProceduresB s td = true) :
    TypeDefinition.ContainsOutsideProcedures (KindSet.ofPred s) td := by
  cases td with
  | Composite c =>
    simp only [TypeDefinition.containsOutsideProceduresB, Bool.and_eq_true, and_assoc] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    exact ⟨h1, consB_sound h2, all_sound (containsTypeB_sound s) h3,
      all_sound (Field.containsB_sound s) h4, consB_sound h5⟩
  | Constrained c =>
    simp only [TypeDefinition.containsOutsideProceduresB, Bool.and_eq_true, and_assoc] at h
    exact ⟨h.1, containsTypeB_sound s _ h.2.1, Laurel.containsB_sound s _ h.2.2.1,
      Laurel.containsB_sound s _ h.2.2.2⟩
  | Datatype d =>
    simp only [TypeDefinition.containsOutsideProceduresB, Bool.and_eq_true] at h
    refine ⟨h.1, fun ctor hc arg ha => ?_⟩
    exact containsTypeB_sound s _ (List.all_eq_true.mp (List.all_eq_true.mp h.2 ctor hc) arg ha)
  | Alias a =>
    simp only [TypeDefinition.containsOutsideProceduresB, Bool.and_eq_true] at h
    exact ⟨h.1, containsTypeB_sound s _ h.2⟩
  | Opaque _ => trivial

private theorem LaurelProgram.containsB_sound (s : NodeKind → Bool) (p : LaurelProgram)
    (h : LaurelProgram.containsB s p = true) : LaurelProgram.Contains (KindSet.ofPred s) p := by
  simp only [LaurelProgram.containsB, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨⟨all_sound (Procedure.containsB_sound s) h1, all_sound (Procedure.containsB_sound s) h2,
      fun td htd c hc => ?_⟩,
    consB_sound h4, consB_sound h5, all_sound (Field.containsB_sound s) h6, consB_sound h7,
    all_sound (TypeDefinition.containsOutsideProceduresB_sound s) h8, fun c hc => ?_⟩
  · have hprocs := List.all_eq_true.mp h3 td htd
    subst hc
    exact all_sound (Procedure.containsB_sound s) hprocs
  · have hconst := List.all_eq_true.mp h9 c hc
    simp only [Bool.and_eq_true] at hconst
    exact ⟨containsTypeB_sound s _ hconst.1, optAll_sound (Laurel.containsB_sound s) hconst.2⟩

private theorem Constant.containsB_sound (s : NodeKind → Bool) (c : Constant)
    (h : Constant.containsB s c = true) : Constant.Contains (KindSet.ofPred s) c := by
  simp only [Constant.containsB, Bool.and_eq_true] at h
  exact ⟨containsTypeB_sound s _ h.1, optAll_sound (Laurel.containsB_sound s) h.2⟩

private theorem OrderedDecl.containsB_sound (s : NodeKind → Bool) (d : OrderedDecl)
    (h : OrderedDecl.containsB s d = true) : OrderedDecl.Contains (KindSet.ofPred s) d := by
  cases d with
  | funcs fs _ => exact all_sound (Procedure.containsB_sound s) h
  | procedure proc => exact Procedure.containsB_sound s proc h
  | datatypes dts =>
    refine all_sound (fun d hd => ?_) h
    simp only [Bool.and_eq_true] at hd
    refine ⟨hd.1, fun ctor hc arg ha => ?_⟩
    exact containsTypeB_sound s _ (List.all_eq_true.mp (List.all_eq_true.mp hd.2 ctor hc) arg ha)
  | opaqueType _ => trivial
  | constant c => exact Constant.containsB_sound s c h

theorem Program.containsB_sound (s : NodeKind → Bool) (p : Program)
    (h : Program.containsB s p = true) : Program.Contains (KindSet.ofPred s) p := by
  match p with
  | .Unordered p =>
    simp only [Program.containsB, Bool.and_eq_true] at h
    exact ⟨h.1, LaurelProgram.containsB_sound s p h.2⟩
  | .Ordered (.WithLaurelTypes p) =>
    simp only [Program.containsB, Bool.and_eq_true, and_assoc] at h
    exact ⟨h.1, h.2.1, all_sound (OrderedDecl.containsB_sound s) h.2.2⟩
  | .Ordered (.Core _) =>
    simp only [Program.containsB, Bool.and_eq_true] at h
    exact ⟨h.1, h.2⟩

def Program.presentKinds (kinds : List NodeKind) (p : Program) : List NodeKind :=
  kinds.filter fun k => !Program.containsB (· != k) p

theorem Program.presentKinds_sound (kinds : List NodeKind) (p : Program) (k : NodeKind)
    (hk : k ∈ kinds) (h : k ∉ Program.presentKinds kinds p) :
    Program.Contains (KindSet.ofPred (· != k)) p := by
  have hc : Program.containsB (· != k) p = true := by
    cases hb : Program.containsB (· != k) p
    · exact absurd (List.mem_filter.mpr ⟨hk, by simp [hb]⟩) h
    · rfl
  exact Program.containsB_sound _ p hc

end -- public section

end Strata.Laurel
