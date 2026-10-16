/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.MapStmtExprProps
public import StrataLaurel.Implementation.LaurelASTProps
import all StrataLaurel.Implementation.MapStmtExpr

/-!
# Lifting a NodeKind Specification to a Program

`mapStmtExprUsedM_contains` (`MapStmtExprProps.lean`) takes a per-node obligation
to one *expression*. This file takes one expression to a whole `Program`: the walk
`mapProgramStmtExprM` threads a rewrite through every `Condition`, `Body`,
`ModifiesGroup`, `ThrowsOnBlock`, `Procedure`, `TypeDefinition`, `Constant` and
`Field` a program holds, and `lift_program` says the kinds follow.

None of it depends on which pass is running. A pass supplies three facts:

* `hexpr` — its per-expression conclusion, from `mapStmtExprUsedM_contains`;
* `htype` — that a type annotation's kinds move from `s` to `t`;
* `hkeep` — that the *container* kinds (`containerKinds`: the `Owner.field.cons`
  and `.some` refinements on `Program`/`Procedure`/`Body`/`CompositeType`, the
  `TypeDefinition.*` kinds, `Condition.mode.Assume` and the two `HighType` kinds)
  move from `s` to `t`.

`hkeep` is the one real restriction, and it is the honest one: these lemmas copy
container kinds across untouched, so a pass that *removes* one of them — as
`GlobalParameterization` does with `Program.staticFields.cons` — cannot use this
lift and needs its own. For a pass that only rewrites inside expressions,
`hkeep` follows from its `removes` list by `decide`.

## Key results

* `Lift` — the three facts a pass supplies;
* `lift_program` — the whole-program conclusion;
* `lift_procedure`, `lift_bodies`, `lift_specs` — the intermediate steps, in case a
  pass needs to stop short of a whole `Program`.

See `EliminateDoWhileProps.eliminateDoWhile_spec` for the whole chain in use.
-/

namespace Strata.Laurel

namespace ProgramLift

public section

variable {m : Type → Type} [Monad m] [MonadPost m]
  {f : StmtExprMd → m StmtExprMd} {s t : KindSet}

/-- What a pass supplies in order to lift its per-expression fact to a whole
    program. `t` is the pass's output kind set — typically
    `(s \ pass.removes) ∪ pass.creates`. -/
structure Lift {m : Type → Type} [Monad m] [MonadPost m]
    (f : StmtExprMd → m StmtExprMd) (s t : KindSet) : Prop where
  /-- The pass's per-expression conclusion, usually from
      `mapStmtExprUsedM_contains`. -/
  expr : ∀ {e : StmtExprMd}, Contains s e → PostM (mapStmtExprM f e) (Contains t)
  /-- Type annotations, which no expression rewrite touches, carry across. -/
  type : ∀ {ty : HighTypeMd}, ContainsType s ty → ContainsType t ty
  /-- Container kinds, which this lift copies rather than rewrites, carry across.
      This is what a pass removing one of them cannot supply. -/
  keep : ∀ k ∈ containerKinds, k ∈ s → k ∈ t

/-- A container kind of the input is a kind of the output. -/
private theorem mem_keep (L : Lift f s t) {k : NodeKind} (h : k ∈ s)
    (hk : k ∈ containerKinds) : k ∈ t := L.keep k hk h

/-- An `Owner.field.cons` kind carries across. -/
private theorem ConsKind.mono (L : Lift f s t) {α : Type} {l : List α} {k : NodeKind}
    (h : ConsKind s l k) (hk : k ∈ containerKinds) : ConsKind t l k :=
  fun hl => L.keep k hk (h hl)

/-- An `Owner.field.some` kind carries across. -/
private theorem SomeKind.mono (L : Lift f s t) {α : Type} {o : Option α} {k : NodeKind}
    (h : SomeKind s o k) (hk : k ∈ containerKinds) : SomeKind t o k :=
  fun ho => L.keep k hk (h ho)

/-- A parameter carries only a type annotation. -/
private theorem Parameter.mono (L : Lift f s t) {p : Parameter}
    (h : Parameter.Contains s p) : Parameter.Contains t p := L.type h

/-! ## Lifting to procedures

`mapProcedureM` walks the body and the specification fields; the signature
fields it copies. A copied kind survives into the output set because it is not
the kind the pass removes (`mem_outSet_of_mem` with a decidable disequality). -/

/-- One condition: its expression is rewritten and its `free` mode is preserved. -/
private theorem lift_condition [LawfulMonad m] (L : Lift f s t) {c : Condition} (h : Condition.Contains s c) :
    PostM (Condition.mapM (mapStmtExprM f) c) (Condition.Contains t) := by
  rw [Condition.mapM]
  refine post_bind (L.expr h.1) (fun cond' hcond' => post_pure ⟨hcond', ?_⟩)
  intro hmode
  exact mem_keep L (h.2 hmode) (by simp [containerKinds])

/-- Rewriting every condition of a list maps each one's kinds into `t`. -/
private theorem lift_conditions [LawfulMonad m] (L : Lift f s t) {cs : List Condition}
    (h : ∀ c ∈ cs, Condition.Contains s c) :
    PostM (cs.mapM (Condition.mapM (mapStmtExprM f)))
      (fun cs' => ∀ c ∈ cs', Condition.Contains t c) :=
  post_mapM cs _ (fun c hc => lift_condition L (h c hc))

/-- Rewriting every expression of a list maps each one's kinds into `t`. -/
private theorem lift_exprs [LawfulMonad m] (L : Lift f s t) {es : List StmtExprMd} (h : ∀ e ∈ es, Contains s e) :
    PostM (es.mapM (mapStmtExprM f)) (fun es' => ∀ e ∈ es', Contains t e) :=
  post_mapM es _ (fun e he => L.expr (h e he))

/-- Rewriting an optional expression maps its kinds into `t` when it is present. -/
private theorem lift_optExpr [LawfulMonad m] (L : Lift f s t) {o : Option StmtExprMd} (h : ∀ e ∈ o, Contains s e) :
    PostM (o.mapM (mapStmtExprM f)) (fun o' => ∀ e ∈ o', Contains t e) :=
  post_option_mapM_mem o _ (fun e he => L.expr (h e he))

/-- A procedure's `modifies` groups: each group's targets and its guard. -/
private theorem lift_modifiesGroups [LawfulMonad m] (L : Lift f s t) {gs : List ModifiesGroup}
    (h : ∀ grp ∈ gs, ModifiesGroup.Contains s grp) :
    PostM (gs.mapM (fun grp => do
        let targets' ← grp.targets.mapM (mapStmtExprM f)
        let guard' ← grp.guard.mapM (mapStmtExprM f)
        pure { grp with targets := targets', guard := guard' }))
      (fun gs' => ∀ grp ∈ gs', ModifiesGroup.Contains t grp) :=
  post_mapM gs _ (fun grp hgrp =>
    post_bind (lift_exprs L (h grp hgrp).1) (fun _targets' htargets' =>
      post_bind (lift_optExpr L (h grp hgrp).2) (fun _guard' hguard' =>
        post_pure ⟨htargets', hguard'⟩)))

/-- A procedure's `throwsOn` cases: guard, postconditions and frame targets. -/
private theorem lift_throwsOn [LawfulMonad m] (L : Lift f s t) {bs : List ThrowsOnBlock}
    (h : ∀ b ∈ bs, ThrowsOnBlock.Contains s b) :
    PostM (bs.mapM (fun blk => do
        pure { blk with
          guard := ← (mapStmtExprM f) blk.guard
          postconditions := ← blk.postconditions.mapM (Condition.mapM (mapStmtExprM f))
          modifies := ← blk.modifies.mapM (mapStmtExprM f) }))
      (fun bs' => ∀ b ∈ bs', ThrowsOnBlock.Contains t b) :=
  post_mapM bs _ (fun b hb =>
    post_bind (L.expr (h b hb).1) (fun _guard' hguard' =>
      post_bind (lift_conditions L (h b hb).2.1) (fun _posts' hposts' =>
        post_bind (lift_exprs L (h b hb).2.2) (fun _mods' hmods' =>
          post_pure ⟨hguard', hposts', hmods'⟩))))

/-- `mapProcedureBodiesM` rewrites the body and copies every other field. -/
private theorem lift_bodies [LawfulMonad m] (L : Lift f s t) {p : Procedure} (h : Body.Contains s p.body) :
    PostM (mapProcedureBodiesM (mapStmtExprM f) p)
      (fun p' => Body.Contains t p'.body
        ∧ p'.inputs = p.inputs ∧ p'.outputs = p.outputs
        ∧ p'.preconditions = p.preconditions ∧ p'.contracts = p.contracts
        ∧ p'.decreases = p.decreases ∧ p'.invokeOn = p.invokeOn ∧ p'.axioms = p.axioms
        ∧ p'.throwsType = p.throwsType ∧ p'.throwsOn = p.throwsOn) := by
  rw [mapProcedureBodiesM]
  split
  case h_1 body heq =>
    rw [heq] at h
    simp only [Body.Contains] at h
    exact post_bind (L.expr h) (fun body' hbody' =>
      post_pure (by simp [Body.Contains, hbody']))
  case h_2 posts impl mods heq =>
    rw [heq] at h
    simp only [Body.Contains] at h
    refine post_bind (post_and (lift_conditions L h.1) (post_mapM_length _ _))
      (fun posts' hposts' => ?_)
    refine post_bind (lift_optExpr L h.2.2.1) (fun _impl' himpl' => ?_)
    refine post_bind (post_and (lift_modifiesGroups L h.2.2.2.1) (post_mapM_length _ _))
      (fun mods' hmods' => ?_)
    refine post_pure ⟨?_, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp⟩
    simp only [Body.Contains]
    refine ⟨hposts'.1, fun hne => mem_keep L
        (h.2.1 (ne_nil_of_length hposts'.2 hne)) (by simp [containerKinds]),
      himpl', hmods'.1, fun hne => mem_keep L
        (h.2.2.2.2 (ne_nil_of_length hmods'.2 hne)) (by simp [containerKinds])⟩
  case h_3 posts heq =>
    rw [heq] at h
    simp only [Body.Contains] at h
    refine post_bind (post_and (lift_conditions L h.1) (post_mapM_length _ _))
      (fun posts' hposts' => ?_)
    refine post_pure ⟨?_, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp⟩
    simp only [Body.Contains]
    exact ⟨hposts'.1, fun hne => mem_keep L
      (h.2 (ne_nil_of_length hposts'.2 hne)) (by simp [containerKinds])⟩
  case h_4 heq =>
    refine post_pure ⟨?_, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp⟩
    rw [heq]
    simp [Body.Contains]

/-- `mapProcedureSpecificationsWithM`: the specification fields are rewritten,
    the signature fields (and the coroutine clauses) are copied. -/
private theorem lift_specs [LawfulMonad m] (L : Lift f s t) {p : Procedure}
    (hpre : ∀ c ∈ p.preconditions, Condition.Contains s c)
    (hdec : ∀ e ∈ p.decreases, Contains s e)
    (hinvoke : ∀ e ∈ p.invokeOn, Contains s e)
    (hax : ∀ e ∈ p.axioms, Contains s e)
    (hthrowsOn : ∀ b ∈ p.throwsOn, ThrowsOnBlock.Contains s b) :
    PostM (mapProcedureSpecificationsWithM (mapStmtExprM f)
        (mapStmtExprM f) p)
      (fun p' => (∀ c ∈ p'.preconditions, Condition.Contains t c)
        ∧ p'.preconditions.length = p.preconditions.length
        ∧ (∀ e ∈ p'.decreases, Contains t e)
        ∧ (∀ e ∈ p'.invokeOn, Contains t e)
        ∧ (∀ e ∈ p'.axioms, Contains t e)
        ∧ (∀ b ∈ p'.throwsOn, ThrowsOnBlock.Contains t b)
        ∧ p'.throwsOn.length = p.throwsOn.length
        ∧ p'.inputs = p.inputs ∧ p'.outputs = p.outputs ∧ p'.contracts = p.contracts
        ∧ p'.body = p.body ∧ p'.throwsType = p.throwsType) := by
  rw [mapProcedureSpecificationsWithM]
  refine post_bind (post_and (lift_conditions L hpre) (post_mapM_length _ _))
    (fun pre' hpre' => ?_)
  refine post_bind (lift_optExpr L hdec) (fun dec' hdec' => ?_)
  refine post_bind (lift_optExpr L hinvoke) (fun inv' hinv' => ?_)
  refine post_bind (lift_exprs L hax) (fun ax' hax' => ?_)
  refine post_bind (post_and (lift_throwsOn L hthrowsOn) (post_mapM_length _ _))
    (fun th' hth' => ?_)
  exact post_pure ⟨hpre'.1, hpre'.2, hdec', hinv', hax', hth'.1, hth'.2,
    rfl, rfl, rfl, rfl, rfl⟩

/-- The whole procedure walk: body, specification fields, and — since
    `mapProcedureM` uses `mapProcedureSpecificationsWithCoroutineM'` — a
    coroutine's `relies`/`guarantees` clauses. Every expression a procedure holds
    is rewritten, so no hypothesis about untouched positions is needed. -/
private theorem lift_procedure [LawfulMonad m] (L : Lift f s t) {p : Procedure} (h : Procedure.Contains s p) :
    PostM (mapProcedureM (mapStmtExprM f) p)
      (Procedure.Contains t) := by
  obtain ⟨hin, hinCons, hout, hpre, hpreCons, hcoro, hdec, hbody, hinvoke, hax, hthrowsTy,
    hthrowsTySome, hthrowsOn, hthrowsOnCons⟩ := h
  obtain ⟨hrel, hguar, hyields, hresumes, hkind⟩ := hcoro
  rw [mapProcedureM]
  refine post_bind (lift_bodies L hbody) (fun p' hp' => ?_)
  obtain ⟨hbody', hin', hout', hpre', hcoro', hdec', hinvoke', hax', hthrowsTy', hthrowsOn'⟩ := hp'
  rw [mapProcedureSpecificationsWithCoroutineM', mapProcedureSpecificationsWithCoroutineM]
  refine post_bind (lift_specs L (by rw [hpre']; exact hpre) (by rw [hdec']; exact hdec)
    (by rw [hinvoke']; exact hinvoke) (by rw [hax']; exact hax)
    (by rw [hthrowsOn']; exact hthrowsOn)) (fun p'' hp'' => ?_)
  obtain ⟨hpre'', hpreLen, hdec'', hinv'', hax'', hth'', hthLen, hin'', hout'', hcoro'',
    hbody'', hthrowsTy''⟩ := hp''
  -- The two coroutine clause lists, walked after the specification record.
  refine post_bind (lift_conditions L (s := s) ?_) (fun rel'' hrel'' => ?_)
  · intro c hc
    exact hrel c (by
      simp only [Procedure.relies, hcoro'', hcoro'] at hc
      simpa [Procedure.relies] using hc)
  refine post_bind (lift_conditions L (s := s) ?_) (fun guar'' hguar'' => ?_)
  · intro c hc
    exact hguar c (by
      simp only [Procedure.guarantees, hcoro'', hcoro'] at hc
      simpa [Procedure.guarantees] using hc)
  refine post_pure ?_
  refine ⟨?_, ?_, ?_, hpre'', ?_, ?_, hdec'', ?_, hinv'', hax'', ?_, ?_, hth'', ?_⟩
  · intro i hi
    refine Parameter.mono L (hin i ?_)
    rw [← hin', ← hin'']
    simpa using hi
  · intro hne
    refine mem_keep L (hinCons ?_) (by simp [containerKinds])
    rw [← hin', ← hin'']
    simpa using hne
  · intro o ho
    refine Parameter.mono L (hout o ?_)
    rw [← hout', ← hout'']
    simpa using ho
  · intro hne
    refine mem_keep L (hpreCons ?_) (by simp [containerKinds])
    have hlen : p''.preconditions.length = p.preconditions.length := by
      rw [hpreLen, hpre']
    exact ne_nil_of_length hlen (by simpa using hne)
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      exact hrel'' c (mem_relies_withClauses _ _ _ _ _ (by simpa [Procedure.relies] using hc))
    · intro c hc
      exact hguar'' c
        (mem_guarantees_withClauses _ _ _ _ _ (by simpa [Procedure.guarantees] using hc))
    · intro q hq
      refine Parameter.mono L (hyields q ?_)
      have h2 := mem_yields_withClauses _ _ _ _ _ (by simpa [Procedure.yields] using hq)
      rw [hcoro'', hcoro'] at h2
      simpa [Procedure.yields] using h2
    · intro q hq
      refine Parameter.mono L (hresumes q ?_)
      have h2 := mem_resumes_withClauses _ _ _ _ _ (by simpa [Procedure.resumes] using hq)
      rw [hcoro'', hcoro'] at h2
      simpa [Procedure.resumes] using h2
    · intro hk
      refine mem_keep L (hkind ?_) (by simp [containerKinds])
      have h2 := kind_coroutine_withClauses _ _ _ _ _ (by simpa [Procedure.kind] using hk)
      rw [hcoro'', hcoro'] at h2
      simpa [Procedure.kind] using h2
  · simpa [hbody''] using hbody'
  · intro ty hty
    refine L.type (hthrowsTy ty ?_)
    rw [← hthrowsTy', ← hthrowsTy'']
    simpa using hty
  · intro ho
    refine mem_keep L (hthrowsTySome ?_) (by simp [containerKinds])
    rw [← hthrowsTy', ← hthrowsTy'']
    simpa using ho
  · intro hne
    refine mem_keep L (hthrowsOnCons ?_) (by simp [containerKinds])
    have hlen : p''.throwsOn.length = p.throwsOn.length := by rw [hthLen, hthrowsOn']
    exact ne_nil_of_length hlen (by simpa using hne)

/-! ## The program

`mapProgramStmtExprM` runs in four phases: every procedure (via
`mapProgramProceduresM ∘ mapProcedureM`), then the type definitions' own
expressions (a constrained type's constraint and witness, a composite's field
initializers), then the constants, then the file-scope globals. Between them,
positions not yet visited still live in the *input* set `s`, which is why the
phase postconditions mention both sets. -/

/-- What the procedure phase establishes: the procedures are rewritten, the rest
    of the program is untouched (so still in `s`), and the two list lengths that
    `Program.*.cons` kinds depend on are preserved. -/
def AfterProcedures (s t : KindSet) (p prog : Program) : Prop :=
  (∀ proc ∈ prog.staticProcedures, Procedure.Contains t proc)
    ∧ prog.staticProcedures.length = p.staticProcedures.length
    ∧ (∀ td ∈ prog.types, TypeDefinition.ContainsOutsideProcedures s td)
    ∧ (∀ td ∈ prog.types, ∀ c : CompositeType, td = .Composite c →
        ∀ proc ∈ c.instanceProcedures, Procedure.Contains t proc)
    ∧ prog.types.length = p.types.length
    ∧ prog.staticFields = p.staticFields
    ∧ prog.constants = p.constants

/-- **The generic program-level lift.** Rewriting every expression position of a
    program with `f` maps a `Contains s` program to a `Contains t` one. The pass
    supplies `Lift` — its per-expression fact plus the two carry-across facts —
    and everything between one expression and a whole `Program` is done here
    once. -/
theorem lift_program [LawfulMonad m] (L : Lift f s t) {p : Program} (h : Program.Contains s p) :
    PostM (mapProgramStmtExprM f p) (Program.Contains t) := by
  obtain ⟨⟨hstatic, htypeProcs⟩, hstaticCons, hfields, hfieldsCons, htypes, hconsts⟩ := h
  rw [mapProgramStmtExprM, mapProgramProceduresM]
  -- Phase 1: every procedure (static, and every composite's methods).
  refine post_bind (Q := AfterProcedures s t p) ?_ (fun prog1 hprog1 => ?_)
  · refine post_bind (post_and
      (post_mapM p.staticProcedures _ (fun proc hproc => lift_procedure L (hstatic proc hproc)))
      (post_mapM_length _ _)) (fun procs1 hprocs1 => ?_)
    refine post_bind (post_and (post_mapM p.types _
        (P := fun td' => TypeDefinition.ContainsOutsideProcedures s td'
          ∧ (∀ c : CompositeType, td' = .Composite c →
              ∀ proc ∈ c.instanceProcedures, Procedure.Contains t proc))
        (fun td htd => ?_))
      (post_mapM_length _ _)) (fun types1 htypes1 => ?_)
    · -- one type definition: only its instance procedures are rewritten here
      cases td with
      | Composite ct =>
        have hOut := htypes _ htd
        simp only [TypeDefinition.ContainsOutsideProcedures] at hOut
        obtain ⟨hkind, hargs, hext, hflds, hprocsCons⟩ := hOut
        refine post_bind (post_and
          (post_mapM ct.instanceProcedures _ (fun proc hproc =>
            lift_procedure L (htypeProcs _ htd ct rfl proc hproc)))
          (post_mapM_length _ _)) (fun procs' hprocs' => ?_)
        refine post_pure ⟨?_, ?_⟩
        · simp only [TypeDefinition.ContainsOutsideProcedures]
          exact ⟨hkind, hargs, hext, hflds,
            fun hne => hprocsCons (ne_nil_of_length hprocs'.2 hne)⟩
        · intro c hc
          simp only [TypeDefinition.Composite.injEq] at hc
          subst hc
          exact hprocs'.1
      | Constrained ct => exact post_pure ⟨htypes _ htd, by simp⟩
      | Datatype dt => exact post_pure ⟨htypes _ htd, by simp⟩
      | Opaque ot => exact post_pure ⟨htypes _ htd, by simp⟩
      | Alias ta => exact post_pure ⟨htypes _ htd, by simp⟩
    refine post_pure ⟨hprocs1.1, by simpa using hprocs1.2,
      fun td htd => (htypes1.1 td htd).1, fun td htd => (htypes1.1 td htd).2,
      by simpa using htypes1.2, rfl, rfl⟩
  obtain ⟨hprocs, hprocsLen, hOut, hInnerProcs, _, hfieldsEq, hconstsEq⟩ := hprog1
  -- Phase 2: the type definitions' own expressions.
  refine post_bind (post_and (post_mapM prog1.types _
      (P := fun td' => TypeDefinition.ContainsOutsideProcedures t td'
        ∧ (∀ c : CompositeType, td' = .Composite c →
            ∀ proc ∈ c.instanceProcedures, Procedure.Contains t proc))
      (fun td htd => ?_))
    (post_mapM_length _ _)) (fun types2 htypes2 => ?_)
  · cases td with
    | Composite ct =>
      have hc := hOut _ htd
      simp only [TypeDefinition.ContainsOutsideProcedures] at hc
      obtain ⟨hkind, hargs, hext, hflds, hprocsCons⟩ := hc
      refine post_bind (post_and
        (post_mapM ct.fields _ (P := Field.Contains t) (fun fld hfld =>
          post_bind (lift_optExpr L (hflds fld hfld).2) (fun init' hinit' =>
            post_pure ⟨L.type (hflds fld hfld).1, hinit'⟩)))
        (post_mapM_length _ _)) (fun fields' hfields' => ?_)
      refine post_pure ⟨?_, ?_⟩
      · simp only [TypeDefinition.ContainsOutsideProcedures]
        exact ⟨mem_keep L hkind (by simp [containerKinds]), ConsKind.mono L hargs (by simp [containerKinds]),
          fun ty hty => L.type (hext ty hty),
          hfields'.1, ConsKind.mono L hprocsCons (by simp [containerKinds])⟩
      · intro c hc'
        simp only [TypeDefinition.Composite.injEq] at hc'
        subst hc'
        simpa using hInnerProcs _ htd ct rfl
    | Constrained ct =>
      have hc := hOut _ htd
      simp only [TypeDefinition.ContainsOutsideProcedures, TypeDefinition.Contains] at hc
      obtain ⟨hkind, hbase, hconstraint, hwitness⟩ := hc
      refine post_bind (L.expr hconstraint) (fun constraint' hconstraint' => ?_)
      refine post_bind (L.expr hwitness) (fun witness' hwitness' => ?_)
      refine post_pure ⟨?_, by simp⟩
      simp only [TypeDefinition.ContainsOutsideProcedures, TypeDefinition.Contains]
      exact ⟨mem_keep L hkind (by simp [containerKinds]), L.type hbase,
        hconstraint', hwitness'⟩
    | Datatype dt =>
      have hc := hOut _ htd
      simp only [TypeDefinition.ContainsOutsideProcedures, TypeDefinition.Contains] at hc
      refine post_pure ⟨?_, by simp⟩
      simp only [TypeDefinition.ContainsOutsideProcedures, TypeDefinition.Contains]
      exact ⟨mem_keep L hc.1 (by simp [containerKinds]), fun ctor hctor arg harg =>
        Parameter.mono L (hc.2 ctor hctor arg harg)⟩
    | Opaque ot =>
      refine post_pure ⟨?_, by simp⟩
      simp [TypeDefinition.ContainsOutsideProcedures, TypeDefinition.Contains]
    | Alias ta =>
      have hc := hOut _ htd
      simp only [TypeDefinition.ContainsOutsideProcedures, TypeDefinition.Contains] at hc
      refine post_pure ⟨?_, by simp⟩
      simp only [TypeDefinition.ContainsOutsideProcedures, TypeDefinition.Contains]
      exact ⟨mem_keep L hc.1 (by simp [containerKinds]), L.type hc.2⟩
  -- Phase 3: constants.
  refine post_bind (post_mapM prog1.constants _ (P := Constant.Contains t)
    (fun c hc =>
    post_bind (lift_optExpr L (hconsts c (by rw [← hconstsEq]; exact hc)).2)
      (fun init' hinit' =>
        post_pure ⟨L.type (hconsts c (by rw [← hconstsEq]; exact hc)).1, hinit'⟩)))
    (fun consts2 hconsts2 => ?_)
  -- Phase 4: file-scope globals.
  refine post_bind (post_and (post_mapM prog1.staticFields _
      (P := Field.Contains t) (fun fld hfld =>
      post_bind (lift_optExpr L (hfields fld (by rw [← hfieldsEq]; exact hfld)).2)
        (fun init' hinit' =>
          post_pure ⟨L.type (hfields fld (by rw [← hfieldsEq]; exact hfld)).1,
            hinit'⟩)))
    (post_mapM_length _ _)) (fun fields2 hfields2 => ?_)
  refine post_pure ⟨⟨hprocs, ?_⟩, ?_, hfields2.1, ?_,
    fun td htd => (htypes2.1 td htd).1, hconsts2⟩
  · intro td htd c hc
    exact (htypes2.1 td htd).2 c hc
  · exact fun hne => mem_keep L (hstaticCons (ne_nil_of_length hprocsLen hne)) (by simp [containerKinds])
  · refine fun hne => mem_keep L (hfieldsCons ?_) (by simp [containerKinds])
    have hlen : fields2.length = p.staticFields.length := by
      rw [hfields2.2, hfieldsEq]
    exact ne_nil_of_length hlen hne

end -- public section

end ProgramLift

end Strata.Laurel
