/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.InsertLoopInvariantAsserts
public import Strata.DL.Imperative.StmtProps
public import Strata.DL.Imperative.CmdTrace
public import Strata.Languages.Core.Logic.LangDef
import Strata.Languages.Core.ExpressionsProps
import Strata.Languages.Core.Logic.LangDefProps
import all Strata.Languages.Core.Factory
import all Strata.Transform.InsertLoopInvariantAsserts
public import Strata.Transform.CoreTransformProps
import all Strata.Transform.CoreTransform
import all Strata.Languages.Core.CoreGen
import all Strata.Transform.LoopElim
public import Strata.Transform.LoopElimProps

/-! # Properties of the insertion of loop invariant checks

`InsertLoopInvAsserts.StmtRel` / `BlockRel` relate a statement and a statement list to the
statements with the checks of their loops inserted: each loop carrying invariants or a measure
becomes its checked form (`Stmt.invChecked`, which `Core.insertInvariantAsserts` builds), whose
measure snapshot variable is none of those of the enclosing loops, with the checks of its body's
loops inserted the same way.

The pass `Core.insertLoopInvariantAsserts` inserts the checks of the outermost loops not checked
yet in each of its passes, numbering them by names its generator has not drawn before
(`BlockRelStep`), and keeps the procedure bodies those of its input with the checks of some loops
inserted (`BlockRelSome`, `BlockRelSome.trans_step`); after its last pass no loop carrying
invariants or a measure is left, so each procedure body it returns is related to the input's by
`BlockRel` (`Core.InsertLoopInvAsserts.insertLoopInvariantAsserts_blockRel`, through
`BlockRelSome.blockRel`).  The pass's generic runners are followed through the generator state
(`Transform.PostGen`).

Related lists have the same `exit` targets and no measure (`BlockRel.labels_measures`), define
the same variables at top level and, at any depth, only those and measure snapshots, with no
new `init` type but the integer type (`BlockRel.defs`).  When the measure snapshots are
reserved, the output is def-use well formed wherever the input is
(`BlockRel.defUseWellFormed`) and has its free-variable annotations checked wherever the input
does (`BlockRel.fvarTypesWellAnnotated`), provided the inserted conditions read, annotate and
refer to nothing new but the snapshots and declared operators (`CheckExprFacts`, which Core's
expressions satisfy).  For Core, the output satisfies the gate `BlockInitEnvWF` wherever the
input does with the prefix of the snapshots reserved
(`Core.InsertLoopInvAsserts.blockInitEnvWF_of_blockRel`).

Key theorems: `BlockRel.labels_measures`, `BlockRel.defs`,
`BlockRel.defUseWellFormed`, `BlockRel.fvarTypesWellAnnotated`, `BlockRelSome.trans_step`,
`BlockRelSome.blockRel`, `Core.InsertLoopInvAsserts.insertLoopInvariantAsserts_blockRel`,
`Core.InsertLoopInvAsserts.insertLoopInvariantAsserts_body_blockRel`,
`Core.InsertLoopInvAsserts.blockInitEnvWF_of_blockRel`. -/

namespace Imperative
namespace InsertLoopInvAsserts

public section

variable {P : PureExpr} [HasIdent P] [HasFvar P] [HasFvars P] [HasBoolOps P] [HasInt P]
  [HasIntOps P]

/-! ## The relation -/

mutual
/-- `ss` is the statement `s` with the checks of its loops inserted: each loop with invariants
    or a measure is replaced by its checked form, numbered by some `n`, whose measure snapshot
    variable is not in `E` (the snapshot variables of the enclosing loops), with in place of
    its body a list that is its body with its loops' checks inserted. -/
inductive StmtRel : List P.Ident → Stmt P (CmdExt P) → List (Stmt P (CmdExt P)) → Prop where
  | cmd {E : List P.Ident} {c : CmdExt P} : StmtRel E (.cmd c) [.cmd c]
  | exit {E : List P.Ident} {l : String} {md : MetaData P} : StmtRel E (.exit l md) [.exit l md]
  | typeDecl {E : List P.Ident} {tc : TypeConstructor} {md : MetaData P} :
      StmtRel E (.typeDecl tc md) [.typeDecl tc md]
  | block {E : List P.Ident} {l : String} {bss bss' : List (Stmt P (CmdExt P))}
      {md : MetaData P} :
      BlockRel E bss bss' → StmtRel E (.block l bss md) [.block l bss' md]
  | ite {E : List P.Ident} {c : ExprOrNondet P} {tss tss' ess ess' : List (Stmt P (CmdExt P))}
      {md : MetaData P} :
      BlockRel E tss tss' → BlockRel E ess ess' →
      StmtRel E (.ite c tss ess md) [.ite c tss' ess' md]
  | loopBare {E : List P.Ident} {g : ExprOrNondet P} {body body' : List (Stmt P (CmdExt P))}
      {md : MetaData P} :
      BlockRel E body body' → StmtRel E (.loop g none [] body md) [.loop g none [] body' md]
  | loop {E : List P.Ident} {g : ExprOrNondet P} {m : Option P.Expr}
      {inv : List (String × P.Expr)} {body body' : List (Stmt P (CmdExt P))} {md : MetaData P}
      (n : String) :
      (∀ x ∈ measureVars n m, x ∉ E) → BlockRel (measureVars n m ++ E) body body' →
      StmtRel E (.loop g m inv body md) (Stmt.invChecked n g m inv body' md)

/-- `ss'` is the statement list `ss` with the checks of its loops inserted, statement by
    statement (`StmtRel`). -/
inductive BlockRel : List P.Ident → List (Stmt P (CmdExt P)) → List (Stmt P (CmdExt P)) →
    Prop where
  | nil {E : List P.Ident} : BlockRel E [] []
  | cons {E : List P.Ident} {s : Stmt P (CmdExt P)} {ss rest rest' : List (Stmt P (CmdExt P))} :
      StmtRel E s ss → BlockRel E rest rest' → BlockRel E (s :: rest) (ss ++ rest')
end

/-! ## The inserted assertions of invariants -/

/-- The labels of the assertions of the invariants of a loop that its checked form inserts:
    before the loop and at the end of an iteration.  The assumptions of the invariants follow
    them. -/
@[expose] def invCheckLabel (l : String) : Bool :=
  l.startsWith s!"{Core.insertLoopInvAssertPrefix}entry_invariant_" ||
    l.startsWith s!"{Core.insertLoopInvAssertPrefix}arbitrary_iter_maintain_invariant_"

/-- The condition of an assertion of an invariant that the checked form of a loop inserts
    (`invCheckLabel`). -/
@[expose] def InvCheck (c : EventArg P) : Prop := invCheckLabel c.label = Bool.true

/-! ## The inserted statements

The statements the checked form of a loop inserts are commands: assertions and assumptions of
the invariants, of the negated guard and of the measure checks (`PassiveOver`), and the measure
snapshot. -/

/-- Every statement of `ss` is an assertion or an assumption of a condition satisfying `R`. -/
def PassiveOver (R : P.Expr → Prop) (ss : List (Stmt P (CmdExt P))) : Prop :=
  ∀ s ∈ ss, ∃ l e md, R e ∧
    (s = .cmd (.cmd (.assert l e md)) ∨ s = .cmd (.cmd (.assume l e md)))

/-- The condition of one of the invariants `inv`. -/
def InvExpr (inv : List (String × P.Expr)) (e : P.Expr) : Prop := ∃ p ∈ inv, e = p.2

omit [HasIdent P] [HasFvar P] [HasFvars P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
/-- A list of assertions of the invariants is passive over them. -/
private theorem passiveOver_mapIdx_assert (inv : List (String × P.Expr))
    (lab : Nat → String × P.Expr → String) (mdf : Nat → MetaData P) :
    PassiveOver (InvExpr inv) (inv.mapIdx fun i a =>
      Stmt.cmd (CmdExt.cmd (Cmd.assert (lab i a) a.2 (mdf i)))) := fun _ hs => by
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.1 hs
  exact ⟨_, _, _, ⟨_, List.getElem_mem hi, rfl⟩, .inl rfl⟩

omit [HasIdent P] [HasFvar P] [HasFvars P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
/-- A list of assumptions of the invariants is passive over them. -/
private theorem passiveOver_mapIdx_assume (inv : List (String × P.Expr))
    (lab : Nat → String × P.Expr → String) (mdf : Nat → MetaData P) :
    PassiveOver (InvExpr inv) (inv.mapIdx fun i a =>
      Stmt.cmd (CmdExt.cmd (Cmd.assume (lab i a) a.2 (mdf i)))) := fun _ hs => by
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.1 hs
  exact ⟨_, _, _, ⟨_, List.getElem_mem hi, rfl⟩, .inr rfl⟩

omit [HasIdent P] [HasFvar P] [HasFvars P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
/-- Passive lists concatenate. -/
private theorem PassiveOver.append {R : P.Expr → Prop} {a b : List (Stmt P (CmdExt P))}
    (ha : PassiveOver R a) (hb : PassiveOver R b) : PassiveOver R (a ++ b) := fun s hs =>
  (List.mem_append.1 hs).elim (ha s) (hb s)

omit [HasIdent P] [HasFvar P] [HasFvars P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
/-- A passive list is passive over any weaker condition. -/
private theorem PassiveOver.mono {R R' : P.Expr → Prop} {ss : List (Stmt P (CmdExt P))}
    (h : PassiveOver R ss) (hR : ∀ e, R e → R' e) : PassiveOver R' ss := fun s hs =>
  have ⟨l, e, md, he, hs⟩ := h s hs; ⟨l, e, md, hR e he, hs⟩

omit [HasIdent P] [HasFvar P] [HasFvars P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
/-- The assertions of the invariants before loop `n` are passive over them. -/
private theorem entryAsserts_passive (n : String) (inv : List (String × P.Expr))
    (md : MetaData P) : PassiveOver (InvExpr inv) (entryAsserts n inv md) :=
  passiveOver_mapIdx_assert inv (fun i a => entryAssertLabel n i a.1) md.invariantMd

omit [HasIdent P] [HasFvar P] [HasFvars P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
/-- The assumptions of the invariants before loop `n` are passive over them. -/
private theorem entryAssumes_passive (n : String) (inv : List (String × P.Expr))
    (md : MetaData P) : PassiveOver (InvExpr inv) (entryAssumes n inv md) :=
  passiveOver_mapIdx_assume inv (fun i a => entryAssumeLabel n i a.1) md.invariantMd

omit [HasIdent P] [HasFvar P] [HasFvars P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
/-- The assumptions of the invariants at the start of an iteration of loop `n` are passive
    over them. -/
private theorem midAssumes_passive (n : String) (inv : List (String × P.Expr))
    (md : MetaData P) : PassiveOver (InvExpr inv) (midAssumes n inv md) :=
  passiveOver_mapIdx_assume inv (fun i a => midAssumeLabel n i a.1) md.invariantMd

omit [HasIdent P] [HasFvar P] [HasFvars P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
/-- The assertions of the invariants at the end of an iteration of loop `n` are passive over
    them. -/
private theorem maintainAsserts_passive (n : String) (inv : List (String × P.Expr))
    (md : MetaData P) : PassiveOver (InvExpr inv) (maintainAsserts n inv md) :=
  passiveOver_mapIdx_assert inv (fun i a => maintainAssertLabel n i a.1) md.invariantMd

omit [HasIdent P] [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] in
/-- The checks after loop `n` are passive over its invariants and the negation of its
    guard. -/
private theorem exitAssumes_passive (n : String) (g : ExprOrNondet P)
    (inv : List (String × P.Expr)) (md : MetaData P) :
    PassiveOver (fun e => InvExpr inv e ∨ ∃ g', g = .det g' ∧ e = HasBoolOps.not g')
      (exitAssumes n g inv md) := by
  refine PassiveOver.append ((passiveOver_mapIdx_assume inv
    (fun i a => exitAssumeLabel n i a.1) md.invariantMd).mono fun _ h => .inl h) ?_
  cases g with
  | det g =>
    intro s hs
    simp only [List.mem_singleton] at hs
    exact ⟨_, _, _, .inr ⟨g, rfl, rfl⟩, .inr hs⟩
  | nondet => intro s hs; cases hs

/-- The condition asserted at the start of an iteration of loop `n`: its measure is not
    negative. -/
abbrev lbExpr (n : String) : P.Expr :=
  HasBoolOps.not (HasIntOps.lt (HasFvar.mkTypedFvar (measureIdent n) HasInt.intTy) HasInt.zero)

/-- The condition asserted at the end of an iteration of loop `n` with measure `m`: the
    measure decreased. -/
abbrev decExpr (n : String) (m : P.Expr) : P.Expr :=
  HasIntOps.lt m (HasFvar.mkTypedFvar (measureIdent n) HasInt.intTy)

/-- The checks of the measure at the end of an iteration of loop `n` are passive over the
    decrease of the measure. -/
private theorem measurePost_passive (n : String) (m : Option P.Expr) (md : MetaData P) :
    PassiveOver (fun e => ∃ m', m = some m' ∧ e = decExpr n m') (measurePost n m md) := by
  cases m with
  | none => intro s hs; cases hs
  | some m =>
    intro s hs
    simp only [measurePost, List.mem_singleton] at hs
    exact ⟨_, _, _, ⟨m, rfl, rfl⟩, .inl hs⟩

omit [HasIdent P] [HasFvar P] [HasFvars P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
/-- A list of commands has no `exit` and no loop measure. -/
private theorem labels_measures_of_cmds {ss : List (Stmt P (CmdExt P))}
    (h : ∀ s ∈ ss, ∃ c, s = .cmd c) : Block.labels ss = [] ∧ Block.measures ss = [] := by
  obtain ⟨cs, rfl⟩ : ∃ cs : List (CmdExt P), ss = cs.map Stmt.cmd := by
    induction ss with
    | nil => exact ⟨[], rfl⟩
    | cons s rest ih =>
      obtain ⟨c, rfl⟩ := h s List.mem_cons_self
      obtain ⟨cs, hcs⟩ := ih fun s hs => h s (List.mem_cons_of_mem _ hs)
      exact ⟨c :: cs, by rw [hcs]; rfl⟩
  exact ⟨Block.labels_map_cmd id cs, Block.measures_map_cmd id cs⟩

omit [HasIdent P] [HasFvar P] [HasFvars P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
/-- A passive list is a list of commands. -/
private theorem PassiveOver.cmds {R : P.Expr → Prop} {ss : List (Stmt P (CmdExt P))}
    (h : PassiveOver R ss) : ∀ s ∈ ss, ∃ c, s = .cmd c := fun s hs => by
  obtain ⟨l, e, md, -, hs | hs⟩ := h s hs <;> exact ⟨_, hs⟩

/-- The measure snapshot and its check are commands. -/
private theorem measurePre_cmds (n : String) (m : Option P.Expr) (md : MetaData P) :
    ∀ s ∈ (measurePre n m md : List (Stmt P (CmdExt P))), ∃ c, s = .cmd c := by
  cases m <;> simp [measurePre]

/-- The labels and measures of the checked form of a loop are those of its body. -/
private theorem invChecked_labels_measures (n : String) (g : ExprOrNondet P)
    (m : Option P.Expr) (inv : List (String × P.Expr)) (body' : List (Stmt P (CmdExt P)))
    (md : MetaData P) :
    Block.labels (Stmt.invChecked n g m inv body' md) = Block.labels body' ∧
      Block.measures (Stmt.invChecked n g m inv body' md) = Block.measures body' := by
  have h1 := labels_measures_of_cmds (entryAsserts_passive n inv md).cmds
  have h2 := labels_measures_of_cmds (entryAssumes_passive n inv md).cmds
  have h3 := labels_measures_of_cmds (exitAssumes_passive n g inv md).cmds
  have h4 := labels_measures_of_cmds (midAssumes_passive n inv md).cmds
  have h5 := labels_measures_of_cmds (measurePre_cmds n m md)
  have h6 := labels_measures_of_cmds (maintainAsserts_passive n inv md).cmds
  have h7 := labels_measures_of_cmds (measurePost_passive n m md).cmds
  simp only [Stmt.invChecked, loopBody, Block.labels_append, Block.measures_append, Block.labels,
    Block.measures, Stmt.labels, Stmt.measures, h1, h2, h3, h4, h5, h6, h7, Option.toList_none,
    List.nil_append, List.append_nil]
  exact ⟨trivial, trivial⟩

mutual
/-- The statements with the checks of a statement's loops inserted have its `exit` targets and
    no loop measure. -/
private theorem StmtRel.labels_measures {E : List P.Ident} {s : Stmt P (CmdExt P)}
    {ss : List (Stmt P (CmdExt P))} (h : StmtRel E s ss) :
    Block.labels ss = Stmt.labels s ∧ Block.measures ss = [] := by
  match h with
  | .cmd | .exit | .typeDecl => simp [Block.labels, Block.measures, Stmt.measures]
  | .block hb =>
    have hl := hb.labels_measures
    simp [Block.labels, Block.measures, Stmt.labels, Stmt.measures, hl.1, hl.2]
  | .ite ht he =>
    have h1 := ht.labels_measures
    have h2 := he.labels_measures
    simp [Block.labels, Block.measures, Stmt.labels, Stmt.measures, h1.1, h1.2, h2.1, h2.2]
  | .loopBare hb =>
    have hl := hb.labels_measures
    simp [Block.labels, Block.measures, Stmt.labels, Stmt.measures, hl.1, hl.2]
  | .loop n _ hb =>
    have hl := hb.labels_measures
    rw [(invChecked_labels_measures ..).1, (invChecked_labels_measures ..).2, hl.1, hl.2]
    exact ⟨rfl, rfl⟩

/-- The list with the checks of a list's loops inserted has its `exit` targets and no loop
    measure. -/
theorem BlockRel.labels_measures {E : List P.Ident} {ss ss' : List (Stmt P (CmdExt P))}
    (h : BlockRel E ss ss') : Block.labels ss' = Block.labels ss ∧ Block.measures ss' = [] := by
  match h with
  | .nil => exact ⟨rfl, rfl⟩
  | .cons hs hr =>
    have h1 := hs.labels_measures
    have h2 := hr.labels_measures
    simp [Block.labels_append, Block.measures_append, Block.labels, h1.1, h1.2, h2.1, h2.2]
end

omit [HasIdent P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
/-- A passive list defines no variable and declares no `init` type. -/
private theorem PassiveOver.defs {R : P.Expr → Prop} {ss : List (Stmt P (CmdExt P))}
    (h : PassiveOver R ss) (b : Bool) :
    Block.definedVars ss b = [] ∧ Block.initTypes ss = [] := by
  induction ss with
  | nil => exact ⟨rfl, rfl⟩
  | cons s rest ih =>
    obtain ⟨l, e, md, -, rfl | rfl⟩ := h s List.mem_cons_self <;>
    obtain ⟨h1, h2⟩ := ih fun s hs => h s (List.mem_cons_of_mem _ hs) <;>
    simp [Block.definedVars, Block.initTypes, Stmt.initTypes, h1, h2, HasVarsImp.definedVars,
      CmdExt.definedVars, Cmd.definedVars, HasInitTypesImp.initTypes, CmdExt.initTypes,
      Cmd.initTypes]

/-- The measure snapshot defines only the snapshot variable, of the integer type. -/
private theorem measurePre_defs (n : String) (m : Option P.Expr) (md : MetaData P) (b : Bool) :
    (∀ x ∈ Block.definedVars (measurePre (C := CmdExt P) n m md) b, x = measureIdent n) ∧
      ∀ ty ∈ Block.initTypes (measurePre (C := CmdExt P) n m md), ty = HasInt.intTy := by
  cases m <;> simp [measurePre, Block.definedVars, Block.initTypes, Stmt.initTypes,
    HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars, HasInitTypesImp.initTypes,
    CmdExt.initTypes, Cmd.initTypes, HasInit.init, HasPassiveCmds.assert]

/-- The checked form of a loop defines, at any depth, only the variables of its body and the
    measure snapshot, with no new type but the integer type, and nothing at top level. -/
private theorem invChecked_defs (n : String) (g : ExprOrNondet P) (m : Option P.Expr)
    (inv : List (String × P.Expr)) (body' : List (Stmt P (CmdExt P))) (md : MetaData P) :
    Block.definedVars (Stmt.invChecked n g m inv body' md) true = [] ∧
    (∀ x ∈ Block.definedVars (Stmt.invChecked n g m inv body' md) false,
      x ∈ Block.definedVars body' false ∨ x = measureIdent n) ∧
    ∀ ty ∈ Block.initTypes (Stmt.invChecked n g m inv body' md),
      ty ∈ Block.initTypes body' ∨ ty = HasInt.intTy := by
  have h1 := (entryAsserts_passive n inv md).defs
  have h2 := (entryAssumes_passive n inv md).defs
  have h3 := (exitAssumes_passive n g inv md).defs
  have h4 := (midAssumes_passive n inv md).defs
  have h6 := (maintainAsserts_passive n inv md).defs
  have h7 := (measurePost_passive n m md).defs
  have h5 := measurePre_defs n m md false
  simp only [Stmt.invChecked, loopBody, Block.definedVars_append, Block.initTypes_append,
    Block.definedVars, Block.initTypes, Stmt.definedVars, Stmt.initTypes, (h1 true).1,
    (h2 true).1, (h3 true).1, (h1 false).1, (h2 false).1, (h3 false).1, (h4 false).1,
    (h6 false).1, (h7 false).1, (h1 true).2, (h2 true).2, (h3 true).2, (h4 true).2,
    (h6 true).2, (h7 true).2, ite_true, Bool.false_eq_true, ite_false, List.nil_append,
    List.append_nil, List.mem_append]
  refine ⟨trivial, fun x hx => ?_, fun ty hty => ?_⟩
  · rcases hx with hx | hx
    · exact .inr (h5.1 x hx)
    · exact .inl hx
  · rcases hty with hty | hty
    · exact .inr (h5.2 ty hty)
    · exact .inl hty

mutual
/-- The statements with the checks of a statement's loops inserted define, at top level, the
    variables it defines, and at any depth, only those it defines and measure snapshots, with no
    new type but the integer type. -/
private theorem StmtRel.defs {E : List P.Ident} {s : Stmt P (CmdExt P)}
    {ss : List (Stmt P (CmdExt P))} (h : StmtRel E s ss) :
    (∀ x, x ∈ Block.definedVars ss true ↔ x ∈ Stmt.definedVars s true) ∧
    (∀ x ∈ Block.definedVars ss false, x ∈ Stmt.definedVars s false ∨ ∃ n, x = measureIdent n) ∧
    ∀ ty ∈ Block.initTypes ss, ty ∈ Stmt.initTypes s ∨ ty = HasInt.intTy := by
  match h with
  | .cmd | .exit | .typeDecl =>
    exact ⟨fun x => by simp [Block.definedVars], fun x hx => .inl (by
      simp only [Block.definedVars, List.append_nil] at hx; exact hx), fun ty hty => .inl (by
      simp only [Block.initTypes, List.append_nil] at hty; exact hty)⟩
  | .block hb =>
    have hd := hb.defs
    refine ⟨fun x => by simp [Block.definedVars], fun x hx => ?_, fun ty hty => ?_⟩
    · simp only [Block.definedVars, Stmt.definedVars, Bool.false_eq_true, ite_false,
        List.append_nil] at hx ⊢
      exact hd.2.1 x hx
    · simp only [Block.initTypes, Stmt.initTypes, List.append_nil] at hty ⊢
      exact hd.2.2 ty hty
  | .ite ht he =>
    have h1 := ht.defs
    have h2 := he.defs
    refine ⟨fun x => by simp [Block.definedVars], fun x hx => ?_, fun ty hty => ?_⟩
    · simp only [Block.definedVars, Stmt.definedVars, Bool.false_eq_true, ite_false,
        List.append_nil, List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · exact (h1.2.1 x hx).imp_left .inl
      · exact (h2.2.1 x hx).imp_left .inr
    · simp only [Block.initTypes, Stmt.initTypes, List.append_nil, List.mem_append] at hty ⊢
      rcases hty with hty | hty
      · exact (h1.2.2 ty hty).imp_left .inl
      · exact (h2.2.2 ty hty).imp_left .inr
  | .loopBare hb =>
    have hd := hb.defs
    refine ⟨fun x => by simp [Block.definedVars], fun x hx => ?_, fun ty hty => ?_⟩
    · simp only [Block.definedVars, Stmt.definedVars, Bool.false_eq_true, ite_false,
        List.append_nil] at hx ⊢
      exact hd.2.1 x hx
    · simp only [Block.initTypes, Stmt.initTypes, List.append_nil] at hty ⊢
      exact hd.2.2 ty hty
  | .loop (g := g) (m := m) (inv := inv) (body' := body') (md := md) n _ hb =>
    have hd := hb.defs
    have hc := invChecked_defs n g m inv body' md
    refine ⟨fun x => by simp [hc.1], fun x hx => ?_, fun ty hty => ?_⟩
    · rcases hc.2.1 x hx with hx | hx
      · simpa [Stmt.definedVars] using hd.2.1 x hx
      · exact .inr ⟨n, hx⟩
    · rcases hc.2.2 ty hty with hty | hty
      · simpa [Stmt.initTypes] using hd.2.2 ty hty
      · exact .inr hty

/-- The list with the checks of a list's loops inserted defines, at top level, the variables
    it defines, and at any depth, only those it defines and measure snapshots, with no new type
    but the integer type. -/
theorem BlockRel.defs {E : List P.Ident} {ss ss' : List (Stmt P (CmdExt P))}
    (h : BlockRel E ss ss') :
    (∀ x, x ∈ Block.definedVars ss' true ↔ x ∈ Block.definedVars ss true) ∧
    (∀ x ∈ Block.definedVars ss' false,
      x ∈ Block.definedVars ss false ∨ ∃ n, x = measureIdent n) ∧
    ∀ ty ∈ Block.initTypes ss', ty ∈ Block.initTypes ss ∨ ty = HasInt.intTy := by
  match h with
  | .nil => exact ⟨fun _ => Iff.rfl, fun x hx => .inl hx, fun ty hty => .inl hty⟩
  | .cons hs hr =>
    have h1 := hs.defs
    have h2 := hr.defs
    refine ⟨fun x => ?_, fun x hx => ?_, fun ty hty => ?_⟩
    · simp only [Block.definedVars_append, Block.definedVars, List.mem_append, h1.1, h2.1]
    · simp only [Block.definedVars_append, Block.definedVars, List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · exact (h1.2.1 x hx).imp_left .inl
      · exact (h2.2.1 x hx).imp_left .inr
    · simp only [Block.initTypes_append, Block.initTypes, List.mem_append] at hty ⊢
      rcases hty with hty | hty
      · exact (h1.2.2 ty hty).imp_left .inl
      · exact (h2.2.2 ty hty).imp_left .inr
end

/-! ## Def-use well-formedness -/

section DefUse
variable [HasOps P]

/-- What the def-use and annotation checks of the inserted conditions need of the expression
    constructors, under the operator declarations `df`: negation reads, annotates and refers to
    nothing new but the declared, the non-negativity check of a measure snapshot reads and
    annotates only the snapshot variable at the integer type and refers only to declared
    operators, and the decrease check of a measure reads and annotates only the measure's
    variables and the snapshot variable, and refers only to the measure's operators and the
    declared ones. -/
structure CheckExprFacts (df : P.Ident → Bool) : Prop where
  notFv : ∀ g : P.Expr, ∀ x ∈ HasFvars.getFvars (HasBoolOps.not g), x ∈ HasFvars.getFvars g
  notOps : ∀ g : P.Expr, ∀ o ∈ HasOps.getOps (HasBoolOps.not g),
    o ∈ HasOps.getOps g ∨ df o = Bool.true
  notTy : ∀ g : P.Expr, ∀ p ∈ HasFvars.getTypedFvars (HasBoolOps.not g),
    p ∈ HasFvars.getTypedFvars g
  lbFv : ∀ n, ∀ x ∈ HasFvars.getFvars (lbExpr (P := P) n), x = measureIdent n
  lbOps : ∀ n, ∀ o ∈ HasOps.getOps (lbExpr (P := P) n), df o = Bool.true
  lbTy : ∀ n, ∀ p ∈ HasFvars.getTypedFvars (lbExpr (P := P) n),
    p = (measureIdent n, HasInt.intTy)
  decFv : ∀ n (m : P.Expr), ∀ x ∈ HasFvars.getFvars (decExpr n m),
    x ∈ HasFvars.getFvars m ∨ x = measureIdent n
  decOps : ∀ n (m : P.Expr), ∀ o ∈ HasOps.getOps (decExpr n m),
    o ∈ HasOps.getOps m ∨ df o = Bool.true
  decTy : ∀ n (m : P.Expr), ∀ p ∈ HasFvars.getTypedFvars (decExpr n m),
    p ∈ HasFvars.getTypedFvars m ∨ p = (measureIdent n, HasInt.intTy)

omit [HasIdent P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
/-- Def-use well-formedness depends only on which variables the predicate marks defined. -/
private theorem defUse_congr {D₁ D₂ df : P.Ident → Bool} (h : ∀ x, D₁ x = true ↔ D₂ x = true)
    (ss : List (Stmt P (CmdExt P))) :
    Block.defUseWellFormed D₁ df ss = Block.defUseWellFormed D₂ df ss := by
  have hD : D₁ = D₂ := funext fun x => Bool.eq_iff_iff.2 (h x)
  rw [hD]

omit [HasIdent P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
/-- A list defining nothing at top level followed by another is def-use well formed when both
    are. -/
private theorem defUse_append_noDefs {D df : P.Ident → Bool} {a b : List (Stmt P (CmdExt P))}
    (ha : Block.definedVars a true = []) (h1 : Block.defUseWellFormed D df a = true)
    (h2 : Block.defUseWellFormed D df b = true) :
    Block.defUseWellFormed D df (a ++ b) = true := by
  rw [Block.defUseWellFormed_append, ha, h1, Bool.true_and, ← h2]
  exact defUse_congr (fun x => by simp) b

omit [HasIdent P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
/-- A passive list over conditions reading defined variables and referring to declared operators
    is def-use well formed. -/
private theorem PassiveOver.defUse {R : P.Expr → Prop} {ss : List (Stmt P (CmdExt P))}
    (h : PassiveOver R ss) {D df : P.Ident → Bool}
    (hR : ∀ e, R e → (∀ x ∈ HasFvars.getFvars e, D x = true) ∧
      ∀ o ∈ HasOps.getOps e, df o = true) :
    Block.defUseWellFormed D df ss = true := by
  induction ss with
  | nil => rfl
  | cons s rest ih =>
    have ih' := ih fun s hs => h s (List.mem_cons_of_mem _ hs)
    obtain ⟨l, e, md, he, rfl | rfl⟩ := h s List.mem_cons_self <;>
    · obtain ⟨hv, ho⟩ := hR e he
      refine defUse_append_noDefs (a := [_]) (by simp [Block.definedVars, HasVarsImp.definedVars,
        CmdExt.definedVars, Cmd.definedVars]) ?_ ih'
      simp only [Block.defUseWellFormed, Stmt.defUseWellFormed, HasVarsImp.readVars,
        CmdExt.readVars, Cmd.getVars, HasVarsImp.modifiedVars, CmdExt.modifiedVars,
        Cmd.modifiedVars, HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars,
        HasOpsImp.getOps, CmdExt.getOps, Cmd.getOps, List.all_eq_true, List.all_nil,
        Bool.and_true, Bool.and_eq_true]
      exact ⟨hv, ho⟩

omit [HasOps P] in
/-- The top-level definitions of the measure snapshot are the snapshot variable. -/
private theorem measurePre_topDefs (n : String) (m : Option P.Expr) (md : MetaData P)
    (x : P.Ident) :
    x ∈ Block.definedVars (measurePre (C := CmdExt P) n m md) true ↔ x ∈ measureVars n m := by
  cases m <;> simp [measurePre, measureVars, Block.definedVars, HasVarsImp.definedVars,
    CmdExt.definedVars, Cmd.definedVars, HasInit.init, HasPassiveCmds.assert]

mutual
/-- **The checks of a def-use well-formed statement's loops keep it def-use well formed**, from
    a predicate marking defined the variables the source's does and the measure snapshots of the
    enclosing loops `E`, which satisfy `Res`, as the snapshot variables do and no variable of the
    statement or marked by the source's predicate does. -/
private theorem StmtRel.defUseWellFormed {E : List P.Ident} {s : Stmt P (CmdExt P)}
    {ss : List (Stmt P (CmdExt P))} (h : StmtRel E s ss) {Res : P.Ident → Prop}
    (hres : ∀ n, Res (measureIdent (P := P) n)) (hER : ∀ x ∈ E, Res x)
    (hid : ∀ x ∈ Stmt.idents s, ¬ Res x) {D D' df : P.Ident → Bool}
    (hDD : ∀ x, D' x = true ↔ D x = true ∨ x ∈ E) (hDR : ∀ x, D x = true → ¬ Res x)
    (hf : CheckExprFacts df) (hdu : Stmt.defUseWellFormed D df s = true) :
    Block.defUseWellFormed D' df ss = true := by
  have hmono : ∀ x, D x = true → D' x = true := fun x hx => (hDD x).2 (.inl hx)
  match h with
  | .cmd (c := c) =>
    simp only [Block.defUseWellFormed, Bool.and_true]
    simp only [Stmt.defUseWellFormed, Bool.and_eq_true, List.all_eq_true] at hdu ⊢
    obtain ⟨⟨⟨hr, hm⟩, hd⟩, ho⟩ := hdu
    refine ⟨⟨⟨fun x hx => hmono x (hr x hx), fun x hx => hmono x (hm x hx)⟩, fun x hx => ?_⟩,
      ho⟩
    have hx' := hd x hx
    have hR := hid x (Stmt.definedVars_subset_idents (.cmd c) false x hx)
    have hDx : D' x = D x := Bool.eq_iff_iff.2 ⟨fun h => ((hDD x).1 h).resolve_right
      fun hE => hR (hER x hE), hmono x⟩
    simpa [hDx] using hx'
  | .exit | .typeDecl => simp [Block.defUseWellFormed, Stmt.defUseWellFormed]
  | .block hb =>
    simp only [Block.defUseWellFormed, Bool.and_true, Stmt.defUseWellFormed] at hdu ⊢
    exact hb.defUseWellFormed hres hER (fun x hx => hid x (by simpa [Stmt.idents])) hDD hDR hf
      hdu
  | .ite (c := c) ht he =>
    simp only [Block.defUseWellFormed, Bool.and_true, Stmt.defUseWellFormed, Bool.and_eq_true,
      List.all_eq_true] at hdu ⊢
    obtain ⟨⟨⟨hc, hco⟩, hdt⟩, hde⟩ := hdu
    exact ⟨⟨⟨fun x hx => hmono x (hc x hx), hco⟩,
      ht.defUseWellFormed hres hER (fun x hx => hid x (by simp [Stmt.idents, hx])) hDD hDR hf
        hdt⟩,
      he.defUseWellFormed hres hER (fun x hx => hid x (by simp [Stmt.idents, hx])) hDD hDR hf
        hde⟩
  | .loopBare hb =>
    simp only [Block.defUseWellFormed, Bool.and_true, Stmt.defUseWellFormed, Bool.and_eq_true,
      List.all_eq_true] at hdu ⊢
    obtain ⟨⟨⟨⟨⟨⟨hg, hgo⟩, hmv⟩, hmo⟩, hiv⟩, hio⟩, hbody⟩ := hdu
    exact ⟨⟨⟨⟨⟨⟨fun x hx => hmono x (hg x hx), hgo⟩, fun x hx => by simp at hx⟩, hmo⟩,
      fun x hx => by simp at hx⟩, hio⟩,
      hb.defUseWellFormed hres hER (fun x hx => hid x (by simp [Stmt.idents, hx])) hDD hDR hf
        hbody⟩
  | .loop (g := g) (m := m) (inv := inv) (body' := body') (md := md) n hfresh hb =>
    simp only [Stmt.defUseWellFormed, Bool.and_eq_true, List.all_eq_true] at hdu
    obtain ⟨⟨⟨⟨⟨⟨hg, hgo⟩, hmv⟩, hmo⟩, hiv⟩, hio⟩, hbody⟩ := hdu
    -- The conditions the checks read: the invariants and the negated guard, read where the loop
    -- starts.
    have hinv : ∀ (D₀ : P.Ident → Bool), (∀ x, D x = true → D₀ x = true) → ∀ e, InvExpr inv e →
        (∀ x ∈ HasFvars.getFvars e, D₀ x = true) ∧ ∀ o ∈ HasOps.getOps e, df o = true := by
      rintro D₀ hD₀ e ⟨p, hp, rfl⟩
      exact ⟨fun x hx => hD₀ x (hiv x (List.mem_flatMap.2 ⟨p, hp, hx⟩)),
        fun o ho => hio o (List.mem_flatMap.2 ⟨p, hp, ho⟩)⟩
    have hgD : ∀ g', g = .det g' → (∀ x ∈ HasFvars.getFvars g', D x = true) ∧
        ∀ o ∈ HasOps.getOps g', df o = true := by
      rintro g' rfl
      exact ⟨fun x hx => hg x (by simpa [ExprOrNondet.getVars] using hx),
        fun o ho => hgo o (by simpa [ExprOrNondet.getOps] using ho)⟩
    have hXA := (exitAssumes_passive n g inv md).defUse (D := D') (df := df) fun e he => by
      rcases he with he | ⟨g', rfl, rfl⟩
      · exact hinv D' hmono e he
      · obtain ⟨hv, ho⟩ := hgD g' rfl
        exact ⟨fun x hx => hmono x (hv x (hf.notFv g' x hx)),
          fun o ho' => (hf.notOps g' o ho').elim (ho o) id⟩
    have hEA := (entryAsserts_passive n inv md).defUse (D := D') (df := df) (hinv D' hmono)
    have hEAs := (entryAssumes_passive n inv md).defUse (D := D') (df := df) (hinv D' hmono)
    have hd1 := (entryAsserts_passive n inv md).defs true
    have hd2 := (entryAssumes_passive n inv md).defs true
    -- The predicates along the body of the checked loop.
    let D₁ : P.Ident → Bool := fun x =>
      D' x || decide (x ∈ Block.definedVars (measurePre (C := CmdExt P) n m md) true)
    let D₂ : P.Ident → Bool := fun x => D₁ x || decide (x ∈ Block.definedVars body' true)
    have hD₁ : ∀ x, D₁ x = true ↔ D x = true ∨ x ∈ measureVars n m ++ E := fun x => by
      simp only [D₁, Bool.or_eq_true, decide_eq_true_eq, measurePre_topDefs, hDD,
        List.mem_append]
      exact or_right_comm.trans or_assoc
    have hmold : ∀ x ∈ measureVars n m, D₁ x = true := fun x hx =>
      (hD₁ x).2 (.inr (List.mem_append_left _ hx))
    have hD₁D : ∀ x, D x = true → D₂ x = true := fun x hx => by
      simp only [D₂, Bool.or_eq_true]; exact .inl ((hD₁ x).2 (.inl hx))
    have hNB : Block.defUseWellFormed D' df (loopBody n m inv body' md) = true := by
      simp only [loopBody, List.append_assoc]
      refine defUse_append_noDefs ((midAssumes_passive n inv md).defs true).1
        ((midAssumes_passive n inv md).defUse (hinv D' hmono)) ?_
      rw [Block.defUseWellFormed_append, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · cases m with
        | none => rfl
        | some D_m =>
          have hm1 : ∀ x ∈ HasFvars.getFvars D_m, D x = true := fun x hx => hmv x (by simpa)
          have hm2 : ∀ o ∈ HasOps.getOps D_m, df o = true := fun o ho => hmo o (by simpa)
          have hnot : D' (measureIdent n) = false := by
            cases hm : D' (measureIdent n)
            · rfl
            · rcases (hDD _).1 hm with h | h
              · exact absurd (hres n) (hDR _ h)
              · exact absurd h (hfresh _ (List.mem_singleton_self _))
          have hlb := hf.lbFv n
          have hlbo := hf.lbOps n
          simp only [measurePre, HasInit.init, HasPassiveCmds.assert, Block.defUseWellFormed,
            Stmt.defUseWellFormed, HasVarsImp.readVars, CmdExt.readVars, Cmd.getVars,
            ExprOrNondet.getVars, HasVarsImp.modifiedVars, CmdExt.modifiedVars,
            Cmd.modifiedVars, HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars,
            HasOpsImp.getOps, CmdExt.getOps, Cmd.getOps, List.all_eq_true, Bool.and_eq_true,
            List.all_cons, List.all_nil, Bool.and_true, hnot, Stmt.definedVars,
            List.mem_singleton, decide_eq_true_eq, Bool.or_eq_true]
          exact ⟨⟨⟨fun x hx => hmono x (hm1 x hx), by simp⟩, hm2⟩,
            fun x hx => .inr (hlb x hx), hlbo⟩
      · rw [Block.defUseWellFormed_append, Bool.and_eq_true]
        refine ⟨?_, ?_⟩
        · exact (defUse_congr (fun x => by rfl) _).trans
            (hb.defUseWellFormed hres (fun x hx => by
                rcases List.mem_append.1 hx with hx | hx
                · cases m with
                  | none => cases hx
                  | some _ => rw [List.mem_singleton.1 hx]; exact hres n
                · exact hER x hx)
              (fun x hx => hid x (by simp [Stmt.idents, hx])) hD₁ hDR hf hbody)
        · refine defUse_append_noDefs ((maintainAsserts_passive n inv md).defs true).1
            ((maintainAsserts_passive n inv md).defUse (hinv D₂ hD₁D)) ?_
          refine (measurePost_passive n m md).defUse fun e ⟨m', hm, he⟩ => ?_
          subst hm he
          refine ⟨fun x hx => ?_, fun o ho => (hf.decOps n m' o ho).elim
            (fun ho => hmo o (by simpa using ho)) id⟩
          rcases hf.decFv n m' x hx with hx | rfl
          · exact hD₁D x (hmv x (by simpa using hx))
          · exact Bool.or_eq_true_iff.2 (.inl (hmold _ (List.mem_singleton_self _)))
    have hL : Block.defUseWellFormed D' df [.loop g none [] (loopBody n m inv body' md) md] =
        true := by
      simp only [Block.defUseWellFormed, Stmt.defUseWellFormed, Bool.and_true, Bool.and_eq_true,
        List.all_eq_true, Option.map_none, Option.getD_none, List.flatMap_nil, List.not_mem_nil,
        hNB]
      exact ⟨⟨⟨⟨⟨fun x hx => hmono x (hg x hx), hgo⟩, fun _ h => h.elim⟩, fun _ h => h.elim⟩,
        fun _ h => h.elim⟩, fun _ h => h.elim⟩
    simp only [Stmt.invChecked]
    refine defUse_append_noDefs ?_ ?_ hXA
    · simp [Block.definedVars_append, hd1.1, hd2.1, Block.definedVars, Stmt.definedVars]
    · refine defUse_append_noDefs (by simp [Block.definedVars_append, hd1.1, hd2.1]) ?_ hL
      exact defUse_append_noDefs hd1.1 hEA hEAs

/-- **The checks of a def-use well-formed list's loops keep it def-use well formed**, as
    `StmtRel.defUseWellFormed`. -/
theorem BlockRel.defUseWellFormed {E : List P.Ident} {ss ss' : List (Stmt P (CmdExt P))}
    (h : BlockRel E ss ss') {Res : P.Ident → Prop} (hres : ∀ n, Res (measureIdent (P := P) n))
    (hER : ∀ x ∈ E, Res x) (hid : ∀ x ∈ Block.idents ss, ¬ Res x) {D D' df : P.Ident → Bool}
    (hDD : ∀ x, D' x = true ↔ D x = true ∨ x ∈ E) (hDR : ∀ x, D x = true → ¬ Res x)
    (hf : CheckExprFacts df) (hdu : Block.defUseWellFormed D df ss = true) :
    Block.defUseWellFormed D' df ss' = true := by
  match h with
  | .nil => rfl
  | .cons (s := s) (ss := ss₁) hs hr =>
    simp only [Block.defUseWellFormed, Bool.and_eq_true] at hdu
    rw [Block.defUseWellFormed_append, Bool.and_eq_true]
    refine ⟨hs.defUseWellFormed hres hER (fun x hx => hid x (by simp [Block.idents, hx])) hDD
      hDR hf hdu.1, hr.defUseWellFormed hres hER
        (fun x hx => hid x (by simp [Block.idents, hx])) (fun x => ?_) (fun x hx => ?_) hf hdu.2⟩
    · simp only [Bool.or_eq_true, decide_eq_true_eq, hDD, hs.defs.1]
      exact or_right_comm
    · simp only [Bool.or_eq_true, decide_eq_true_eq] at hx
      rcases hx with hx | hx
      · exact hDR x hx
      · exact hid x (by
          simp only [Block.idents, List.mem_append]
          exact .inl (Stmt.definedVars_subset_idents s true x hx))
end

end DefUse

/-! ## Free-variable annotations -/

/-- The typing after the definitions of the statement list `ss`, as the annotation check of a
    list threads it. -/
def extendBlock (Γ : VarTyping P) (ss : List (Stmt P (CmdExt P))) : VarTyping P :=
  ss.foldl (fun Γ s => Γ.extend (Stmt.typedDefinedVars s)) Γ

omit [HasIdent P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
/-- The annotation check of a concatenation is that of its parts, the second checked after the
    definitions of the first. -/
private theorem fvarTypes_append (Γ : VarTyping P) (a b : List (Stmt P (CmdExt P))) :
    Block.fvarTypesWellAnnotated Γ (a ++ b) ↔
      Block.fvarTypesWellAnnotated Γ a ∧ Block.fvarTypesWellAnnotated (extendBlock Γ a) b := by
  induction a generalizing Γ with
  | nil => simp [Block.fvarTypesWellAnnotated, extendBlock]
  | cons s a ih =>
    simp only [List.cons_append, Block.fvarTypesWellAnnotated, ih, extendBlock, List.foldl_cons,
      and_assoc]

omit [HasIdent P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
/-- A list of statements defining nothing at top level leaves the typing unchanged. -/
private theorem extendBlock_of_noDefs {Γ : VarTyping P} {a : List (Stmt P (CmdExt P))}
    (h : ∀ s ∈ a, Stmt.typedDefinedVars s = []) : extendBlock Γ a = Γ := by
  induction a generalizing Γ with
  | nil => rfl
  | cons s a ih =>
    simp only [extendBlock, List.foldl_cons, h s List.mem_cons_self]
    exact ih fun s hs => h s (List.mem_cons_of_mem _ hs)

omit [HasIdent P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
/-- The variables a statement defines with their types are among those it defines. -/
private theorem typedDefinedVars_names (s : Stmt P (CmdExt P)) :
    ∀ x ∈ (Stmt.typedDefinedVars s).map Prod.fst, x ∈ Stmt.definedVars s true := by
  rcases s with ((x | _ | _ | _ | _) | _) | _ | _ | _ | _ | _ <;>
    simp [Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars, CmdExt.typedDefinedVars,
      Cmd.typedDefinedVars, HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars]

omit [HasIdent P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
/-- The typing after the definitions of a list types the variables it does not define at top
    level as before. -/
private theorem extendBlock_of_not_mem {Γ : VarTyping P} {a : List (Stmt P (CmdExt P))}
    {x : P.Ident} (hx : x ∉ Block.definedVars a true) : extendBlock Γ a x = Γ x := by
  induction a generalizing Γ with
  | nil => rfl
  | cons s a ih =>
    simp only [Block.definedVars, List.mem_append, not_or] at hx
    simp only [extendBlock, List.foldl_cons]
    rw [show List.foldl (fun Γ s => Γ.extend (Stmt.typedDefinedVars s)) _ a = extendBlock _ a
      from rfl, ih hx.2]
    exact VarTyping.extend_of_not_mem fun h => hx.1 (typedDefinedVars_names s x h)

omit [HasIdent P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
/-- A passive list over conditions whose annotations a typing gives has its annotations
    checked. -/
private theorem PassiveOver.fvarTypes {R : P.Expr → Prop} {ss : List (Stmt P (CmdExt P))}
    (h : PassiveOver R ss) {Γ : VarTyping P}
    (hR : ∀ e, R e → Γ.annotates (HasFvars.getTypedFvars e)) :
    Block.fvarTypesWellAnnotated Γ ss := by
  induction ss with
  | nil => trivial
  | cons s rest ih =>
    have ih' := ih fun s hs => h s (List.mem_cons_of_mem _ hs)
    obtain ⟨l, e, md, he, rfl | rfl⟩ := h s List.mem_cons_self <;>
    · exact ⟨by simpa [Stmt.fvarTypesWellAnnotated, HasTypedVarsImp.typedReadVars,
        CmdExt.typedReadVars, Cmd.getTypedVars] using hR e he,
        ih'⟩

omit [HasIdent P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
/-- A passive list defines nothing with a type. -/
private theorem PassiveOver.typedDefs {R : P.Expr → Prop} {ss : List (Stmt P (CmdExt P))}
    (h : PassiveOver R ss) : ∀ s ∈ ss, Stmt.typedDefinedVars s = [] := fun s hs => by
  obtain ⟨l, e, md, -, rfl | rfl⟩ := h s hs <;> rfl

/-- The statements with the checks of a statement's loops inserted extend a typing as the
    statement does. -/
private theorem StmtRel.extendBlock {E : List P.Ident} {s : Stmt P (CmdExt P)}
    {ss : List (Stmt P (CmdExt P))} (h : StmtRel E s ss) (Γ : VarTyping P) :
    extendBlock Γ ss = Γ.extend (Stmt.typedDefinedVars s) := by
  match h with
  | .cmd | .exit | .typeDecl | .block _ | .ite _ _ | .loopBare _ => rfl
  | .loop (g := g) (m := m) (inv := inv) (body' := body') (md := md) n _ _ =>
    refine extendBlock_of_noDefs fun s hs => ?_
    simp only [Stmt.invChecked, List.mem_append, List.mem_singleton] at hs
    rcases hs with ((hs | hs) | hs) | hs
    · exact (entryAsserts_passive n inv md).typedDefs s hs
    · exact (entryAssumes_passive n inv md).typedDefs s hs
    · rw [hs]; rfl
    · exact (exitAssumes_passive n g inv md).typedDefs s hs

section Annot
variable [HasOps P]

mutual
/-- **The checks of a statement's loops keep its free-variable annotations checked**, under a
    typing agreeing with the source's outside the measure snapshots of the enclosing loops `E`,
    which it types as integers, when the source's typing and the predicate the statement is
    def-use well formed from mark no variable satisfying `Res`, which the snapshot variables
    and those of `E` satisfy and no variable of the statement does. -/
private theorem StmtRel.fvarTypesWellAnnotated [LawfulHasFvars P] {E : List P.Ident}
    {s : Stmt P (CmdExt P)}
    {ss : List (Stmt P (CmdExt P))} (h : StmtRel E s ss) {Res : P.Ident → Prop}
    (hres : ∀ n, Res (measureIdent (P := P) n)) (hER : ∀ x ∈ E, Res x)
    (hid : ∀ x ∈ Stmt.idents s, ¬ Res x) {D df : P.Ident → Bool}
    (hDR : ∀ x, D x = true → ¬ Res x) (hdu : Stmt.defUseWellFormed D df s = true)
    {Γ Γ' : VarTyping P} (hΓR : ∀ x ty, Γ x = some ty → ¬ Res x)
    (hΓ : ∀ x, x ∉ E → Γ' x = Γ x)
    (hΓE : ∀ x ∈ E, Γ' x = some HasInt.intTy) (hf : CheckExprFacts df)
    (hw : Stmt.fvarTypesWellAnnotated Γ s) : Block.fvarTypesWellAnnotated Γ' ss := by
  -- An annotation the source's typing gives is given by `Γ'` as well.
  have hann : ∀ {occs : List (P.Ident × P.Ty)}, Γ.annotates occs → Γ'.annotates occs :=
    fun ha x ty hx => by
      rw [hΓ x fun hE => hΓR x ty (ha x ty hx) (hER x hE)]; exact ha x ty hx
  match h with
  | .cmd => exact ⟨hann hw, trivial⟩
  | .exit | .typeDecl => exact ⟨trivial, trivial⟩
  | .block hb =>
    simp only [Stmt.defUseWellFormed] at hdu
    exact ⟨hb.fvarTypesWellAnnotated hres hER (fun x hx => hid x (by simpa [Stmt.idents]))
      hDR hdu hΓR hΓ hΓE hf hw, trivial⟩
  | .ite ht he =>
    simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
    obtain ⟨hc, hwt, hwe⟩ := hw
    exact ⟨⟨hann hc,
      ht.fvarTypesWellAnnotated hres hER (fun x hx => hid x (by simp [Stmt.idents, hx])) hDR
        hdu.1.2 hΓR hΓ hΓE hf hwt,
      he.fvarTypesWellAnnotated hres hER (fun x hx => hid x (by simp [Stmt.idents, hx])) hDR
        hdu.2 hΓR hΓ hΓE hf hwe⟩, trivial⟩
  | .loopBare hb =>
    simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
    obtain ⟨hg, -, -, hbody⟩ := hw
    exact ⟨⟨hann hg, fun _ _ h => by simp at h, fun _ _ h => by simp at h,
      hb.fvarTypesWellAnnotated hres hER (fun x hx => hid x (by simp [Stmt.idents, hx])) hDR
        hdu.2 hΓR hΓ hΓE hf hbody⟩, trivial⟩
  | .loop (g := g) (m := m) (inv := inv) (body := body) (body' := body') (md := md) n hfresh
      hb =>
    have hdu' := hdu
    simp only [Stmt.defUseWellFormed, Bool.and_eq_true, List.all_eq_true] at hdu'
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hmv⟩, -⟩, hiv⟩, -⟩, hbody⟩ := hdu'
    obtain ⟨hg, hm, hi, hwb⟩ := hw
    -- The annotations of the invariants, given by any typing agreeing with `Γ'` on their
    -- variables, which are defined where the loop starts.
    have hinvA : ∀ Γ₀ : VarTyping P, (∀ x, D x = true → Γ₀ x = Γ' x) → ∀ e, InvExpr inv e →
        Γ₀.annotates (HasFvars.getTypedFvars e) := by
      rintro Γ₀ hΓ₀ e ⟨p, hp, rfl⟩ x ty hx
      have hxv : x ∈ HasFvars.getFvars p.2 := LawfulHasFvars.mem_getFvars_of_typed _ x ty hx
      rw [hΓ₀ x (hiv x (List.mem_flatMap.2 ⟨p, hp, hxv⟩))]
      exact hann hi x ty (List.mem_flatMap.2 ⟨p, hp, hx⟩)
    have hXA := (exitAssumes_passive n g inv md).fvarTypes (Γ := Γ') fun e he => by
      rcases he with he | ⟨g', rfl, rfl⟩
      · exact hinvA Γ' (fun _ _ => rfl) e he
      · intro x ty hx
        exact hann hg x ty (by simpa [ExprOrNondet.getTypedVars] using hf.notTy g' _ hx)
    -- The typing inside the checked loop, after the measure snapshot.
    let Γ₁ : VarTyping P := Γ'.extend ((measureVars n m).map (·, HasInt.intTy))
    have hΓ₁ : ∀ x, x ∉ measureVars n m → Γ₁ x = Γ' x := fun x hx =>
      VarTyping.extend_of_not_mem (by cases m <;> simp_all [measureVars])
    have hΓ₁m : ∀ x ∈ measureVars n m, Γ₁ x = some HasInt.intTy := fun x hx => by
      cases m with
      | none => cases hx
      | some _ =>
        rw [List.mem_singleton.1 hx]
        simp [Γ₁, measureVars, VarTyping.extend]
    have hresm : ∀ x ∈ measureVars n m, Res x := fun x hx => by
      cases m with
      | none => cases hx
      | some _ => rw [List.mem_singleton.1 hx]; exact hres n
    -- The variables the source's predicate marks are not redefined by the body.
    have hnd : ∀ x, D x = true → x ∉ Block.definedVars body' true := fun x hx hd => by
      have hu := Block.not_defined_of_mem_definedVars hbody
        (Block.definedVars_true_subset_false (fun _ _ => id) ((hb.defs.1 x).1 hd))
      rw [hx] at hu; cases hu
    have hBody : Block.fvarTypesWellAnnotated Γ₁ body' :=
      hb.fvarTypesWellAnnotated hres (fun x hx => by
          rcases List.mem_append.1 hx with hx | hx
          · exact hresm x hx
          · exact hER x hx)
        (fun x hx => hid x (by simp [Stmt.idents, hx])) hDR hbody hΓR (fun x hx => by
          simp only [List.mem_append, not_or] at hx
          rw [hΓ₁ x hx.1, hΓ x hx.2])
        (fun x hx => by
          by_cases hm : x ∈ measureVars n m
          · exact hΓ₁m x hm
          · rw [hΓ₁ x hm]
            exact hΓE x ((List.mem_append.1 hx).resolve_left hm)) hf hwb
    have hMP : Block.fvarTypesWellAnnotated Γ' (measurePre (C := CmdExt P) n m md) ∧
        extendBlock Γ' (measurePre (C := CmdExt P) n m md) = Γ₁ := by
      cases m with
      | none => exact ⟨trivial, rfl⟩
      | some D_m =>
        refine ⟨⟨by simpa [HasInit.init, Stmt.fvarTypesWellAnnotated,
            HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars, Cmd.getTypedVars,
            ExprOrNondet.getTypedVars] using hann (by simpa using hm), ?_, trivial⟩, ?_⟩
        · intro x ty hx
          simp only [HasPassiveCmds.assert, HasTypedVarsImp.typedReadVars,
            CmdExt.typedReadVars, Cmd.getTypedVars] at hx
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (hf.lbTy n _ hx)
          simp [HasInit.init, Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars,
            CmdExt.typedDefinedVars, Cmd.typedDefinedVars, VarTyping.extend]
        · rfl
    have hΓ₂ : ∀ x, D x = true → extendBlock Γ₁ body' x = Γ' x := fun x hx => by
      rw [extendBlock_of_not_mem (hnd x hx), hΓ₁ x fun hm => hDR x hx (hresm x hm)]
    have hNB : Block.fvarTypesWellAnnotated Γ' (loopBody n m inv body' md) := by
      simp only [loopBody, List.append_assoc, fvarTypes_append]
      rw [extendBlock_of_noDefs (midAssumes_passive n inv md).typedDefs, hMP.2,
        extendBlock_of_noDefs (maintainAsserts_passive n inv md).typedDefs]
      refine ⟨(midAssumes_passive n inv md).fvarTypes (hinvA Γ' fun _ _ => rfl), hMP.1, hBody,
        (maintainAsserts_passive n inv md).fvarTypes (hinvA _ hΓ₂),
        (measurePost_passive n m md).fvarTypes fun e ⟨m', hm', he⟩ => ?_⟩
      subst hm' he
      intro x ty hx
      rcases hf.decTy n m' _ hx with hx | hx
      · have hxv := LawfulHasFvars.mem_getFvars_of_typed _ x ty hx
        rw [hΓ₂ x (hmv x (by simpa using hxv))]
        exact hann (by simpa using hm) x ty hx
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
        rw [extendBlock_of_not_mem fun hd => hid _ (by
            simp only [Stmt.idents, List.mem_append]
            exact .inr (Block.definedVars_subset_idents body true _ ((hb.defs.1 _).1 hd)))
          (hres n)]
        exact hΓ₁m _ (List.mem_singleton_self _)
    have hEE := (entryAsserts_passive n inv md).append (entryAssumes_passive n inv md)
    have hEEL : ∀ s ∈ entryAsserts n inv md ++ entryAssumes n inv md ++
        [Stmt.loop g none [] (loopBody n m inv body' md) md], Stmt.typedDefinedVars s = [] :=
      fun s hs => by
        rcases List.mem_append.1 hs with hs | hs
        · exact hEE.typedDefs s hs
        · rw [List.mem_singleton.1 hs]; rfl
    simp only [Stmt.invChecked, fvarTypes_append]
    rw [extendBlock_of_noDefs (entryAsserts_passive n inv md).typedDefs,
      extendBlock_of_noDefs hEE.typedDefs, extendBlock_of_noDefs hEEL]
    refine ⟨⟨⟨(entryAsserts_passive n inv md).fvarTypes (hinvA Γ' fun _ _ => rfl),
      (entryAssumes_passive n inv md).fvarTypes (hinvA Γ' fun _ _ => rfl)⟩,
      ⟨hann hg, fun _ _ h => by simp at h, fun _ _ h => by simp at h, hNB⟩, trivial⟩, hXA⟩

/-- **The checks of a list's loops keep its free-variable annotations checked**, as
    `StmtRel.fvarTypesWellAnnotated`. -/
theorem BlockRel.fvarTypesWellAnnotated [LawfulHasFvars P] {E : List P.Ident}
    {ss ss' : List (Stmt P (CmdExt P))}
    (h : BlockRel E ss ss') {Res : P.Ident → Prop} (hres : ∀ n, Res (measureIdent (P := P) n))
    (hER : ∀ x ∈ E, Res x) (hid : ∀ x ∈ Block.idents ss, ¬ Res x) {D df : P.Ident → Bool}
    (hDR : ∀ x, D x = true → ¬ Res x) (hdu : Block.defUseWellFormed D df ss = true)
    {Γ Γ' : VarTyping P} (hΓR : ∀ x ty, Γ x = some ty → ¬ Res x)
    (hΓ : ∀ x, x ∉ E → Γ' x = Γ x)
    (hΓE : ∀ x ∈ E, Γ' x = some HasInt.intTy) (hf : CheckExprFacts df)
    (hw : Block.fvarTypesWellAnnotated Γ ss) : Block.fvarTypesWellAnnotated Γ' ss' := by
  match h with
  | .nil => trivial
  | .cons (s := s) hs hr =>
    simp only [Block.defUseWellFormed, Bool.and_eq_true] at hdu
    rw [fvarTypes_append, hs.extendBlock]
    have hnot : ∀ x, x ∈ (Stmt.typedDefinedVars s).map Prod.fst → ¬ Res x := fun x hx =>
      hid x (by
        simp only [Block.idents, List.mem_append]
        exact .inl (Stmt.definedVars_subset_idents s true x (typedDefinedVars_names s x hx)))
    refine ⟨hs.fvarTypesWellAnnotated hres hER (fun x hx => hid x (by simp [Block.idents, hx]))
      hDR hdu.1 hΓR hΓ hΓE hf hw.1, hr.fvarTypesWellAnnotated hres hER
        (fun x hx => hid x (by simp [Block.idents, hx])) (fun x hx => ?_) hdu.2
        (fun x ty hx => ?_)
        (fun x hx => VarTyping.extend_congr _ (hΓ x hx))
        (fun x hx => by
          rw [VarTyping.extend_of_not_mem fun h => hnot x h (hER x hx)]; exact hΓE x hx)
        hf hw.2⟩
    · simp only [Bool.or_eq_true, decide_eq_true_eq] at hx
      rcases hx with hx | hx
      · exact hDR x hx
      · exact hid x (by
          simp only [Block.idents, List.mem_append]
          exact .inl (Stmt.definedVars_subset_idents s true x hx))
    · by_cases hd : x ∈ (Stmt.typedDefinedVars s).map Prod.fst
      · exact hnot x hd
      · rw [VarTyping.extend_of_not_mem hd] at hx; exact hΓR x ty hx
end

end Annot

/-! ## Inserting the checks of some loops

Each pass of the Core pass inserts the checks of the outermost loops it has not checked yet,
leaving their bodies unchanged, and numbers them by names it draws from a generator.
`StmtRelStep N D s ss` says that `ss` is `s` with the checks of some loops carrying invariants
or a measure inserted, their bodies unchanged, each numbered by a name whose snapshot variable
does not satisfy `N` (the variables drawn before) and satisfies `D` (those drawn so far).
`StmtRelSome D E s ss` says that `ss` is `s` with the checks of some loops inserted as by
`StmtRel`, the other loops kept unchanged, body included, every snapshot variable satisfying
`D`.  A list related to `ss` by `BlockRelSome D []` and then to `ss'` by `BlockRelStep N D'`, with
`D` contained in `N` and in `D'`, is related to `ss'` by `BlockRelSome D' []`
(`BlockRelSome.trans_step`), and a list related to `ss` by `BlockRelSome D E` without loops
carrying invariants or a measure is related to it by `BlockRel E` (`BlockRelSome.blockRel`). -/

mutual
/-- The number of loops of a statement, at any depth, carrying invariants or a measure. -/
@[expose] def _root_.Imperative.Stmt.numCheckedLoops : Stmt P (CmdExt P) → Nat
  | .loop _ m inv body _ =>
    (if inv.isEmpty && m.isNone then 0 else 1) + Block.numCheckedLoops body
  | .block _ bss _ => Block.numCheckedLoops bss
  | .ite _ tss ess _ => Block.numCheckedLoops tss + Block.numCheckedLoops ess
  | .cmd _ | .exit _ _ | .typeDecl _ _ => 0

/-- The number of loops of a statement list, at any depth, carrying invariants or a measure. -/
@[expose] def _root_.Imperative.Block.numCheckedLoops : List (Stmt P (CmdExt P)) → Nat
  | [] => 0
  | s :: rest => Stmt.numCheckedLoops s + Block.numCheckedLoops rest
end

mutual
/-- `ss` is `s` with the checks of some loops carrying invariants or a measure inserted, their
    bodies unchanged, each numbered by a name whose snapshot variable does not satisfy `N` and
    satisfies `D`, and the loops of the other loops' bodies treated the same way. -/
inductive StmtRelStep (N D : P.Ident → Prop) :
    Stmt P (CmdExt P) → List (Stmt P (CmdExt P)) → Prop where
  | cmd {c : CmdExt P} : StmtRelStep N D (.cmd c) [.cmd c]
  | exit {l : String} {md : MetaData P} : StmtRelStep N D (.exit l md) [.exit l md]
  | typeDecl {tc : TypeConstructor} {md : MetaData P} :
      StmtRelStep N D (.typeDecl tc md) [.typeDecl tc md]
  | block {l : String} {bss bss' : List (Stmt P (CmdExt P))} {md : MetaData P} :
      BlockRelStep N D bss bss' → StmtRelStep N D (.block l bss md) [.block l bss' md]
  | ite {c : ExprOrNondet P} {tss tss' ess ess' : List (Stmt P (CmdExt P))}
      {md : MetaData P} :
      BlockRelStep N D tss tss' → BlockRelStep N D ess ess' →
      StmtRelStep N D (.ite c tss ess md) [.ite c tss' ess' md]
  | loopBare {g : ExprOrNondet P} {body body' : List (Stmt P (CmdExt P))} {md : MetaData P} :
      BlockRelStep N D body body' →
      StmtRelStep N D (.loop g none [] body md) [.loop g none [] body' md]
  | loop {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
      {body : List (Stmt P (CmdExt P))} {md : MetaData P} (n : String) :
      ¬ (inv = [] ∧ m = none) → (∀ x ∈ measureVars n m, ¬ N x ∧ D x) →
      StmtRelStep N D (.loop g m inv body md) (Stmt.invChecked n g m inv body md)

/-- `ss'` is `ss` with the checks of some loops inserted, statement by statement
    (`StmtRelStep`). -/
inductive BlockRelStep (N D : P.Ident → Prop) :
    List (Stmt P (CmdExt P)) → List (Stmt P (CmdExt P)) → Prop where
  | nil : BlockRelStep N D [] []
  | cons {s : Stmt P (CmdExt P)} {ss rest rest' : List (Stmt P (CmdExt P))} :
      StmtRelStep N D s ss → BlockRelStep N D rest rest' →
      BlockRelStep N D (s :: rest) (ss ++ rest')
end

mutual
/-- `ss` is `s` with the checks of some loops inserted as by `StmtRel`, every snapshot variable
    satisfying `D` and none of those of the enclosing loops `E`, and the other loops kept
    unchanged, body included. -/
inductive StmtRelSome (D : P.Ident → Prop) :
    List P.Ident → Stmt P (CmdExt P) → List (Stmt P (CmdExt P)) → Prop where
  | keep {E : List P.Ident} {s : Stmt P (CmdExt P)} : StmtRelSome D E s [s]
  | block {E : List P.Ident} {l : String} {bss bss' : List (Stmt P (CmdExt P))}
      {md : MetaData P} :
      BlockRelSome D E bss bss' → StmtRelSome D E (.block l bss md) [.block l bss' md]
  | ite {E : List P.Ident} {c : ExprOrNondet P} {tss tss' ess ess' : List (Stmt P (CmdExt P))}
      {md : MetaData P} :
      BlockRelSome D E tss tss' → BlockRelSome D E ess ess' →
      StmtRelSome D E (.ite c tss ess md) [.ite c tss' ess' md]
  | loopBare {E : List P.Ident} {g : ExprOrNondet P} {body body' : List (Stmt P (CmdExt P))}
      {md : MetaData P} :
      BlockRelSome D E body body' →
      StmtRelSome D E (.loop g none [] body md) [.loop g none [] body' md]
  | loop {E : List P.Ident} {g : ExprOrNondet P} {m : Option P.Expr}
      {inv : List (String × P.Expr)} {body body' : List (Stmt P (CmdExt P))} {md : MetaData P}
      (n : String) :
      (∀ x ∈ measureVars n m, D x ∧ x ∉ E) → BlockRelSome D (measureVars n m ++ E) body body' →
      StmtRelSome D E (.loop g m inv body md) (Stmt.invChecked n g m inv body' md)

/-- `ss'` is `ss` with the checks of some loops inserted, statement by statement
    (`StmtRelSome`). -/
inductive BlockRelSome (D : P.Ident → Prop) :
    List P.Ident → List (Stmt P (CmdExt P)) → List (Stmt P (CmdExt P)) → Prop where
  | nil {E : List P.Ident} : BlockRelSome D E [] []
  | cons {E : List P.Ident} {s : Stmt P (CmdExt P)} {ss rest rest' : List (Stmt P (CmdExt P))} :
      StmtRelSome D E s ss → BlockRelSome D E rest rest' →
      BlockRelSome D E (s :: rest) (ss ++ rest')
end

/-- Every list is itself with the checks of none of its loops inserted. -/
private theorem BlockRelSome.refl {D : P.Ident → Prop} {E : List P.Ident} :
    ∀ ss : List (Stmt P (CmdExt P)), BlockRelSome D E ss ss
  | [] => .nil
  | _ :: rest => .cons .keep (BlockRelSome.refl rest)

mutual
/-- The relation keeps holding for more allowed snapshot variables. -/
private theorem StmtRelSome.mono {D D' : P.Ident → Prop} (hD : ∀ x, D x → D' x) {E : List P.Ident}
    {s : Stmt P (CmdExt P)} {ss : List (Stmt P (CmdExt P))} (h : StmtRelSome D E s ss) :
    StmtRelSome D' E s ss := by
  match h with
  | .keep => exact .keep
  | .block hb => exact .block (hb.mono hD)
  | .ite ht he => exact .ite (ht.mono hD) (he.mono hD)
  | .loopBare hb => exact .loopBare (hb.mono hD)
  | .loop n hn hb => exact .loop n (fun x hx => ⟨hD x (hn x hx).1, (hn x hx).2⟩) (hb.mono hD)

/-- The relation keeps holding for more allowed snapshot variables. -/
private theorem BlockRelSome.mono {D D' : P.Ident → Prop} (hD : ∀ x, D x → D' x) {E : List P.Ident}
    {ss ss' : List (Stmt P (CmdExt P))} (h : BlockRelSome D E ss ss') :
    BlockRelSome D' E ss ss' := by
  match h with
  | .nil => exact .nil
  | .cons hs hr => exact .cons (hs.mono hD) (hr.mono hD)
end

mutual
/-- The relation keeps holding for fewer forbidden and more allowed snapshot variables. -/
private theorem StmtRelStep.mono {N N' D D' : P.Ident → Prop} (hN : ∀ x, N' x → N x)
    (hD : ∀ x, D x → D' x) {s : Stmt P (CmdExt P)} {ss : List (Stmt P (CmdExt P))}
    (h : StmtRelStep N D s ss) : StmtRelStep N' D' s ss := by
  match h with
  | .cmd => exact .cmd
  | .exit => exact .exit
  | .typeDecl => exact .typeDecl
  | .block hb => exact .block (hb.mono hN hD)
  | .ite ht he => exact .ite (ht.mono hN hD) (he.mono hN hD)
  | .loopBare hb => exact .loopBare (hb.mono hN hD)
  | .loop n hc hn =>
    exact .loop n hc fun x hx => ⟨fun h => (hn x hx).1 (hN x h), hD x (hn x hx).2⟩

/-- The relation keeps holding for fewer forbidden and more allowed snapshot variables. -/
private theorem BlockRelStep.mono {N N' D D' : P.Ident → Prop} (hN : ∀ x, N' x → N x)
    (hD : ∀ x, D x → D' x) {ss ss' : List (Stmt P (CmdExt P))} (h : BlockRelStep N D ss ss') :
    BlockRelStep N' D' ss ss' := by
  match h with
  | .nil => exact .nil
  | .cons hs hr => exact .cons (hs.mono hN hD) (hr.mono hN hD)
end

mutual
/-- One pass inserting checks inserts some, when the snapshot variables of the enclosing loops
    are among the forbidden ones. -/
private theorem StmtRelStep.some {N D : P.Ident → Prop} {E : List P.Ident}
    (hE : ∀ x ∈ E, N x) {s : Stmt P (CmdExt P)} {ss : List (Stmt P (CmdExt P))}
    (h : StmtRelStep N D s ss) : StmtRelSome D E s ss := by
  match h with
  | .cmd | .exit | .typeDecl => exact .keep
  | .block hb => exact .block (hb.some hE)
  | .ite ht he => exact .ite (ht.some hE) (he.some hE)
  | .loopBare hb => exact .loopBare (hb.some hE)
  | .loop n _ hn =>
    exact .loop n (fun x hx => ⟨(hn x hx).2, fun hx' => (hn x hx).1 (hE x hx')⟩)
      (BlockRelSome.refl _)

/-- One pass inserting checks inserts some, when the snapshot variables of the enclosing loops
    are among the forbidden ones. -/
private theorem BlockRelStep.some {N D : P.Ident → Prop} {E : List P.Ident}
    (hE : ∀ x ∈ E, N x) {ss ss' : List (Stmt P (CmdExt P))} (h : BlockRelStep N D ss ss') :
    BlockRelSome D E ss ss' := by
  match h with
  | .nil => exact .nil
  | .cons hs hr => exact .cons (hs.some hE) (hr.some hE)
end

/-- A list related to a concatenation is the concatenation of lists related to its parts. -/
private theorem BlockRelStep.append_inv {N D : P.Ident → Prop} :
    ∀ {a b c : List (Stmt P (CmdExt P))}, BlockRelStep N D (a ++ b) c →
      ∃ a' b', c = a' ++ b' ∧ BlockRelStep N D a a' ∧ BlockRelStep N D b b'
  | [], _, _, h => ⟨[], _, rfl, .nil, h⟩
  | _ :: _, _, _, .cons hs hr =>
    have ⟨a', b', h, ha, hb⟩ := BlockRelStep.append_inv hr
    ⟨_ ++ a', b', by rw [h, List.append_assoc], .cons hs ha, hb⟩

/-- A list of commands is related only to itself. -/
private theorem BlockRelStep.cmds_inv {N D : P.Ident → Prop} :
    ∀ {a c : List (Stmt P (CmdExt P))}, (∀ s ∈ a, ∃ c, s = .cmd c) → BlockRelStep N D a c →
      c = a
  | [], _, _, .nil => rfl
  | _ :: _, _, ha, .cons hs hr => by
    obtain ⟨c, rfl⟩ := ha _ List.mem_cons_self
    cases hs
    rw [BlockRelStep.cmds_inv (fun s hs => ha s (List.mem_cons_of_mem _ hs)) hr]
    rfl

/-- A list related to a one-statement list is a list related to the statement. -/
private theorem BlockRelStep.single_inv {N D : P.Ident → Prop} {s : Stmt P (CmdExt P)}
    {c : List (Stmt P (CmdExt P))} (h : BlockRelStep N D [s] c) : StmtRelStep N D s c := by
  cases h with
  | cons hs hr => cases hr; simpa using hs

/-- A list related to the checked form of a loop is the checked form of a list related to the
    loop's body. -/
private theorem BlockRelStep.invChecked_inv {N D : P.Ident → Prop} {n : String}
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P (CmdExt P))} {md : MetaData P} {c : List (Stmt P (CmdExt P))}
    (h : BlockRelStep N D (Stmt.invChecked n g m inv body md) c) :
    ∃ body', BlockRelStep N D body body' ∧ c = Stmt.invChecked n g m inv body' md := by
  simp only [Stmt.invChecked] at h ⊢
  obtain ⟨a₁, b₁, rfl, h₁, hX⟩ := h.append_inv
  obtain ⟨a₂, b₂, rfl, hAB, hL⟩ := h₁.append_inv
  rw [hX.cmds_inv (exitAssumes_passive n g inv md).cmds,
    hAB.cmds_inv ((entryAsserts_passive n inv md).append (entryAssumes_passive n inv md)).cmds]
  cases hL.single_inv with
  | loopBare hb =>
    simp only [loopBody] at hb
    obtain ⟨a₃, b₃, rfl, h₃, hPost⟩ := hb.append_inv
    obtain ⟨a₄, b₄, rfl, h₄, hMaint⟩ := h₃.append_inv
    obtain ⟨a₅, body', rfl, hMidPre, hBody⟩ := h₄.append_inv
    rw [hPost.cmds_inv (measurePost_passive n m md).cmds,
      hMaint.cmds_inv (maintainAsserts_passive n inv md).cmds,
      hMidPre.cmds_inv fun s hs => by
        rcases List.mem_append.1 hs with hs | hs
        · exact (midAssumes_passive n inv md).cmds s hs
        · exact measurePre_cmds n m md s hs]
    exact ⟨body', hBody, rfl⟩
  | loop _ hc _ => exact absurd ⟨rfl, rfl⟩ hc

mutual
/-- **Inserting the checks of some loops and then of some more inserts the checks of some
    loops**, when the snapshot variables allowed before are forbidden in the later pass and
    allowed after it, and those of the enclosing loops `E` are allowed before. -/
private theorem StmtRelSome.trans_step {D N D' : P.Ident → Prop} (hN : ∀ x, D x → N x)
    (hD : ∀ x, D x → D' x) {E : List P.Ident} (hE : ∀ x ∈ E, D x) {s : Stmt P (CmdExt P)}
    {c c' : List (Stmt P (CmdExt P))} (h₁ : StmtRelSome D E s c) (h₂ : BlockRelStep N D' c c') :
    StmtRelSome D' E s c' := by
  match h₁ with
  | .keep => exact h₂.single_inv.some fun x hx => hN x (hE x hx)
  | .block hb =>
    cases h₂.single_inv with
    | block hb' => exact .block (hb.trans_step hN hD hE hb')
  | .ite ht he =>
    cases h₂.single_inv with
    | ite ht' he' => exact .ite (ht.trans_step hN hD hE ht') (he.trans_step hN hD hE he')
  | .loopBare hb =>
    cases h₂.single_inv with
    | loopBare hb' => exact .loopBare (hb.trans_step hN hD hE hb')
    | loop _ hc _ => exact absurd ⟨rfl, rfl⟩ hc
  | .loop n hn hb =>
    obtain ⟨body', hb', rfl⟩ := h₂.invChecked_inv
    exact .loop n (fun x hx => ⟨hD x (hn x hx).1, (hn x hx).2⟩)
      (hb.trans_step hN hD (fun x hx => by
        rcases List.mem_append.1 hx with hx | hx
        · exact (hn x hx).1
        · exact hE x hx) hb')

/-- **Inserting the checks of some loops of a list and then of some more inserts the checks of
    some loops**, as `StmtRelSome.trans_step`. -/
theorem BlockRelSome.trans_step {D N D' : P.Ident → Prop} (hN : ∀ x, D x → N x)
    (hD : ∀ x, D x → D' x) {E : List P.Ident} (hE : ∀ x ∈ E, D x)
    {ss c c' : List (Stmt P (CmdExt P))} (h₁ : BlockRelSome D E ss c)
    (h₂ : BlockRelStep N D' c c') : BlockRelSome D' E ss c' := by
  match h₁ with
  | .nil => cases h₂; exact .nil
  | .cons hs hr =>
    obtain ⟨a', b', rfl, ha, hb⟩ := h₂.append_inv
    exact .cons (hs.trans_step hN hD hE ha) (hr.trans_step hN hD hE hb)
end

mutual
/-- A statement without loops carrying invariants or a measure is itself with the checks of its
    loops inserted. -/
private theorem StmtRel.refl_of_numCheckedLoops {E : List P.Ident} :
    ∀ s : Stmt P (CmdExt P), Stmt.numCheckedLoops s = 0 → StmtRel E s [s]
  | .cmd _, _ => .cmd
  | .exit _ _, _ => .exit
  | .typeDecl _ _, _ => .typeDecl
  | .block _ bss _, h => .block (BlockRel.refl_of_numCheckedLoops bss (by
      simpa [Stmt.numCheckedLoops] using h))
  | .ite _ tss ess _, h => by
    simp only [Stmt.numCheckedLoops] at h
    exact .ite (BlockRel.refl_of_numCheckedLoops tss (by omega))
      (BlockRel.refl_of_numCheckedLoops ess (by omega))
  | .loop g m inv body md, h => by
    simp only [Stmt.numCheckedLoops] at h
    split at h
    · rename_i hb
      simp only [Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact .loopBare (BlockRel.refl_of_numCheckedLoops body (by omega))
    · omega

/-- A list without loops carrying invariants or a measure is itself with the checks of its loops
    inserted. -/
private theorem BlockRel.refl_of_numCheckedLoops {E : List P.Ident} :
    ∀ ss : List (Stmt P (CmdExt P)), Block.numCheckedLoops ss = 0 → BlockRel E ss ss
  | [], _ => .nil
  | s :: rest, h => by
    simp only [Block.numCheckedLoops] at h
    exact .cons (StmtRel.refl_of_numCheckedLoops s (by omega))
      (BlockRel.refl_of_numCheckedLoops rest (by omega))
end

omit [HasFvar P] [HasFvars P] [HasBoolOps P] [HasInt P] [HasIntOps P] [HasIdent P] in
/-- The loops carrying invariants or a measure of a concatenation are those of its parts. -/
private theorem _root_.Imperative.Block.numCheckedLoops_append :
    ∀ a b : List (Stmt P (CmdExt P)),
      Block.numCheckedLoops (a ++ b) = Block.numCheckedLoops a + Block.numCheckedLoops b
  | [], _ => by simp [Block.numCheckedLoops]
  | s :: rest, b => by
    simp only [List.cons_append, Block.numCheckedLoops, Block.numCheckedLoops_append rest b]
    omega

omit [HasFvar P] [HasFvars P] [HasBoolOps P] [HasInt P] [HasIntOps P] [HasIdent P] in
/-- A list of commands has no loop. -/
private theorem numCheckedLoops_of_cmds {ss : List (Stmt P (CmdExt P))}
    (h : ∀ s ∈ ss, ∃ c, s = .cmd c) : Block.numCheckedLoops ss = 0 := by
  induction ss with
  | nil => rfl
  | cons s rest ih =>
    obtain ⟨c, rfl⟩ := h s List.mem_cons_self
    simp [Block.numCheckedLoops, Stmt.numCheckedLoops,
      ih fun s hs => h s (List.mem_cons_of_mem _ hs)]

/-- The loops carrying invariants or a measure of the checked form of a loop are those of the
    list in place of its body. -/
private theorem _root_.Imperative.Block.numCheckedLoops_invChecked (n : String) (g : ExprOrNondet P)
    (m : Option P.Expr) (inv : List (String × P.Expr)) (body : List (Stmt P (CmdExt P)))
    (md : MetaData P) :
    Block.numCheckedLoops (Stmt.invChecked n g m inv body md) = Block.numCheckedLoops body := by
  have h1 := numCheckedLoops_of_cmds (entryAsserts_passive n inv md).cmds
  have h2 := numCheckedLoops_of_cmds (entryAssumes_passive n inv md).cmds
  have h3 := numCheckedLoops_of_cmds (exitAssumes_passive n g inv md).cmds
  have h4 := numCheckedLoops_of_cmds (midAssumes_passive n inv md).cmds
  have h5 := numCheckedLoops_of_cmds (measurePre_cmds n m md)
  have h6 := numCheckedLoops_of_cmds (maintainAsserts_passive n inv md).cmds
  have h7 := numCheckedLoops_of_cmds (measurePost_passive n m md).cmds
  simp [Stmt.invChecked, loopBody, Block.numCheckedLoops_append, Block.numCheckedLoops,
    Stmt.numCheckedLoops, h1, h2, h3, h4, h5, h6, h7]

mutual
/-- **A statement with the checks of some loops inserted into one without loops carrying
    invariants or a measure has the checks of all its loops inserted.** -/
private theorem StmtRelSome.stmtRel {D : P.Ident → Prop} {E : List P.Ident} {s : Stmt P (CmdExt P)}
    {ss : List (Stmt P (CmdExt P))} (h : StmtRelSome D E s ss)
    (hn : Block.numCheckedLoops ss = 0) : StmtRel E s ss := by
  match h with
  | .keep => exact StmtRel.refl_of_numCheckedLoops s (by simpa [Block.numCheckedLoops] using hn)
  | .block hb =>
    exact .block (hb.blockRel (by simpa [Block.numCheckedLoops, Stmt.numCheckedLoops] using hn))
  | .ite ht he =>
    simp only [Block.numCheckedLoops, Stmt.numCheckedLoops] at hn
    exact .ite (ht.blockRel (by omega)) (he.blockRel (by omega))
  | .loopBare hb =>
    exact .loopBare (hb.blockRel (by simpa [Block.numCheckedLoops, Stmt.numCheckedLoops] using hn))
  | .loop n hn' hb =>
    rw [Block.numCheckedLoops_invChecked] at hn
    exact .loop n (fun x hx => (hn' x hx).2) (hb.blockRel hn)

/-- **A list with the checks of some loops inserted into one without loops carrying invariants
    or a measure has the checks of all its loops inserted.** -/
theorem BlockRelSome.blockRel {D : P.Ident → Prop} {E : List P.Ident}
    {ss ss' : List (Stmt P (CmdExt P))} (h : BlockRelSome D E ss ss')
    (hn : Block.numCheckedLoops ss' = 0) : BlockRel E ss ss' := by
  match h with
  | .nil => exact .nil
  | .cons hs hr =>
    rw [Block.numCheckedLoops_append] at hn
    exact .cons (hs.stmtRel (by omega)) (hr.blockRel (by omega))
end

end -- public section

end InsertLoopInvAsserts
end Imperative

namespace Core.InsertLoopInvAsserts

open Core Core.Logic Imperative Imperative.InsertLoopInvAsserts

public section

/-- The measure snapshot variables of different loop numbers differ. -/
private theorem measureIdent_inj (a b : String)
    (h : measureIdent (P := Expression) a = measureIdent b) : a = b := by
  have h' := congrArg (fun x : Expression.Ident => x.name.toList) h
  simp only [measureIdent, HasIdent.ident, String.toList_append,
    List.append_cancel_left_eq] at h'
  exact String.toList_inj.1 h'

/-- The name of a measure snapshot variable starts with the reserved prefix. -/
theorem measureIdent_reserved (n : String) :
    measurePrefix.toList.isPrefixOf
      (measureIdent (P := Expression) n).name.toList := by
  rw [List.isPrefixOf_iff_prefix]
  exact ⟨n.toList, by simp [measureIdent, HasIdent.ident, String.toList_append]⟩

/-- The conditions the checks insert read, annotate and refer to nothing new but the snapshot
    variables and the operators declared by a gate covering the factory's names. -/
private theorem checkExprFacts {df : Expression.Ident → Bool}
    (hfd : ∀ s, Core.isNameInFactory s = Bool.true → df ⟨s, ()⟩ = Bool.true) :
    CheckExprFacts (P := Expression) df := by
  have hnot : ∀ o, o = (⟨"Bool.Not", ()⟩ : Expression.Ident) → df o = Bool.true :=
    fun _ h => h ▸ hfd _ boolNot_isNameInFactory
  have hlt : ∀ o, o = (⟨"Int.Lt", ()⟩ : Expression.Ident) → df o = Bool.true :=
    fun _ h => h ▸ hfd _ intLt_isNameInFactory
  have hzFv : HasFvars.getFvars (HasInt.zero (P := Expression)) = [] := rfl
  have hzTy : HasFvars.getTypedFvars (HasInt.zero (P := Expression)) = [] := rfl
  have hzOps : HasOps.getOps (HasInt.zero (P := Expression)) = [] := rfl
  have hmFv : ∀ (n : String) x, x ∈ HasFvars.getFvars
      (HasFvar.mkTypedFvar (P := Expression) (measureIdent n) HasInt.intTy) →
      x = measureIdent n := fun n x hx =>
    List.mem_singleton.1 (LawfulHasFvars.mkTypedFvar_getFvars _ _ hx)
  have hmTy : ∀ (n : String) p, p ∈ HasFvars.getTypedFvars
      (HasFvar.mkTypedFvar (P := Expression) (measureIdent n) HasInt.intTy) →
      p = (measureIdent n, HasInt.intTy) := fun n p hp =>
    List.mem_singleton.1 (LawfulHasFvars.mkTypedFvar_getTypedFvars _ _ hp)
  have hmOps : ∀ (n : String), HasOps.getOps
      (HasFvar.mkTypedFvar (P := Expression) (measureIdent n) HasInt.intTy) = [] :=
    fun _ => LawfulHasFvar.getOps_mkTypedFvar _ _
  refine ⟨Core.not_getFvars, fun g o ho => (Core.not_getOps g o ho).imp_right (hnot o),
    Core.not_getTypedFvars, fun n x hx => ?_, fun n o ho => ?_, fun n p hp => ?_,
    fun n m x hx => ?_, fun n m o ho => ?_, fun n m p hp => ?_⟩
  · rcases Core.lt_getFvars _ _ x (Core.not_getFvars _ x hx) with h | h
    · exact hmFv n x h
    · simp [hzFv] at h
  · rcases Core.not_getOps _ o ho with h | h
    · rcases Core.lt_getOps _ _ o h with h | h | h
      · simp [hmOps] at h
      · simp [hzOps] at h
      · exact hlt o h
    · exact hnot o h
  · rcases Core.lt_getTypedFvars _ _ p (Core.not_getTypedFvars _ p hp) with h | h
    · exact hmTy n p h
    · simp [hzTy] at h
  · exact (Core.lt_getFvars _ _ x hx).imp_right (hmFv n x)
  · rcases Core.lt_getOps _ _ o ho with h | h | h
    · exact .inl h
    · simp [hmOps] at h
    · exact .inr (hlt o h)
  · exact (Core.lt_getTypedFvars _ _ p hp).imp_right (hmTy n p)

/-- No variable of a list satisfying the gate with `prefixesReserved` reserved starts with the
    reserved prefix. -/
theorem idents_not_reserved {base : InitEnvWFParams} {ss : Statements} {ρ : Env Expression}
    (hwf : BlockInitEnvWF (base.extend prefixesReserved) ss ρ) :
    ∀ x ∈ Block.idents ss,
      ¬ measurePrefix.toList.isPrefixOf x.name.toList := by
  have hp : measurePrefix ∈
      (base.extend prefixesReserved).prefixIdents := by
    simp [Imperative.Logic.InitEnvWFParams.extend, prefixesReserved]
  intro x hx
  rcases Block.idents_subset_vars ss x hx with h | h | h
  · exact hwf.getVarsNotReserved h hp
  · by_cases hd : x ∈ Block.definedVars ss false
    · exact hwf.definedVarsNotReservedCore x hd _ hp
    · exact hwf.reservedFreshCore x
        (hwf.readWritesDefined x (by simp [Block.touchedVars, h]) hd) _ hp
  · exact hwf.definedVarsNotReservedCore x h _ hp

/-! ## The Core pass

`insertInvariantAsserts` replaces a loop carrying invariants or a measure by its checked form
over its unchanged body (`Stmt.invChecked`), numbered by the name it draws from the generator,
and nothing else; the generator never draws a name twice.  So a pass of
`runStmtsRec insertInvariantAsserts` inserts the checks of some loops, numbered by names not
drawn before (`BlockRelStep`), and the iteration `insertLoopInvariantAsserts` the checks of all
loops of every procedure body (`insertLoopInvariantAsserts_blockRel`). -/

/-- The snapshot variable `x` is that of a name the generator state `γ` has drawn. -/
private def Drawn (γ : CoreGenState) (x : Expression.Ident) : Prop :=
  ∃ n, (⟨n, ()⟩ : CoreIdent) ∈ γ.generated ∧ x = measureIdent n

/-- The generator state `γ'` extends `γ`: it has drawn every name `γ` has, and is well formed
    when `γ` is. -/
private def GenLe (γ γ' : CoreGenState) : Prop :=
  (γ.WF → γ'.WF) ∧ ∀ x ∈ γ.generated, x ∈ γ'.generated

/-- Every generator state extends itself. -/
private theorem GenLe.refl (γ : CoreGenState) : GenLe γ γ := ⟨id, fun _ h => h⟩

/-- Extending generator states twice extends them. -/
private theorem GenLe.trans {γ₁ γ₂ γ₃ : CoreGenState} (h₁ : GenLe γ₁ γ₂) (h₂ : GenLe γ₂ γ₃) :
    GenLe γ₁ γ₃ := ⟨fun h => h₂.1 (h₁.1 h), fun x hx => h₂.2 x (h₁.2 x hx)⟩

/-- A snapshot variable of a drawn name stays one in an extending generator state. -/
private theorem GenLe.drawn {γ γ' : CoreGenState} (h : GenLe γ γ') {x : Expression.Ident}
    (hx : Drawn γ x) : Drawn γ' x :=
  have ⟨n, hn, he⟩ := hx; ⟨n, h.2 _ hn, he⟩

/-- Drawing a name from a well-formed generator state draws one it has not drawn before, and
    extends it. -/
private theorem gen_fresh {γ γ' : CoreGenState} {n : String}
    (h : CoreGenState.gen ("loop" : CoreIdent) γ = (⟨n, ()⟩, γ')) :
    GenLe γ γ' ∧ (⟨n, ()⟩ : CoreIdent) ∈ γ'.generated ∧
      (γ.WF → (⟨n, ()⟩ : CoreIdent) ∉ γ.generated) := by
  have hg : γ'.generated = ⟨n, ()⟩ :: γ.generated := by
    simp only [CoreGenState.gen, Prod.mk.injEq] at h
    rw [← h.2, ← h.1]
  refine ⟨⟨fun hwf => CoreGenState.WFMono' hwf h, fun x hx => by rw [hg]; exact .tail _ hx⟩,
    by rw [hg]; exact .head _, fun hwf => ?_⟩
  have hwf' := CoreGenState.WFMono' hwf h
  unfold CoreGenState.WF at hwf'
  rw [hg] at hwf'
  exact (List.nodup_cons.1 hwf'.2.2).1

/-- What `insertInvariantAsserts` returns on a statement `s`: for a loop carrying invariants or
    a measure, its checked form over its unchanged body, numbered by the name it draws; nothing
    when `s` is not such a loop, the generator state unchanged. -/
private theorem insertInvariantAsserts_post (s : Statement) (γ : CoreGenState) :
    Transform.PostGen (· = γ) (insertInvariantAsserts s) fun o γ' => match o with
      | some ss => ∃ g m inv bss md n, s = .loop g m inv bss md ∧ ¬ (inv = [] ∧ m = none) ∧
          ss = Stmt.invChecked n g m inv bss md ∧
          CoreGenState.gen ("loop" : CoreIdent) γ = (⟨n, ()⟩, γ')
      | none => (∀ g m inv bss md, s = .loop g m inv bss md → inv = [] ∧ m = none) ∧
          γ' = γ := by
  unfold insertInvariantAsserts
  split
  · rename_i g m inv bss md
    dsimp only
    split
    · rename_i hb
      simp only [Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at hb
      exact Transform.PostGen.pure fun _ h => ⟨fun _ _ _ _ _ he => by
        cases he; exact hb, h⟩
    · rename_i hb
      refine Transform.PostGen.bind (Q₁ := fun n γ' =>
        CoreGenState.gen ("loop" : CoreIdent) γ = (⟨n, ()⟩, γ'))
        (fun σ a σ' hσ hr => by
          obtain ⟨rfl, rfl⟩ := Transform.ok_pair_inj (show (Except.ok _, _) = _ from hr)
          subst hσ
          rfl) fun n => ?_
      refine Transform.PostGen.bind (Q₁ := fun _ γ' =>
          CoreGenState.gen ("loop" : CoreIdent) γ = (⟨n, ()⟩, γ'))
        (Transform.PostGen.modify (by intro; rfl) fun _ h => h) fun _ =>
        Transform.PostGen.pure fun _ h => ⟨g, m, inv, bss, md, n, rfl, fun ⟨h₁, h₂⟩ => hb (by
          simp [h₁, h₂]), rfl, h⟩
  · rename_i hne
    exact Transform.PostGen.pure fun _ h =>
      ⟨fun g m inv bss md he => absurd he (hne g m inv bss md), h⟩

/-- What one pass of `runStmtsRec insertInvariantAsserts` over `ss` from the generator state
    `γ` to `γ'` returns, `r`, when `γ` is well formed: `ss` with the checks of some loops
    inserted, numbered by names drawn in the pass (`BlockRelStep`), with fewer loops carrying
    invariants or a measure when `r` reports a change; and `ss` has none when `r` reports
    none. -/
private def PassPost (ss : List Statement) (γ : CoreGenState) (r : Bool × List Statement)
    (γ' : CoreGenState) : Prop :=
  γ.WF → BlockRelStep (Drawn γ) (Drawn γ') ss r.2 ∧
    Block.numCheckedLoops r.2 ≤ Block.numCheckedLoops ss ∧
    (r.1 = Bool.true → Block.numCheckedLoops r.2 < Block.numCheckedLoops ss) ∧
    (r.1 = Bool.false → Block.numCheckedLoops ss = 0)

/-- `PassPost` holds for any wider pair of generator states. -/
private theorem PassPost.widen {ss : List Statement} {γ₀ γ γ' γ₁ : CoreGenState}
    {r : Bool × List Statement} (h₀ : GenLe γ₀ γ) (h₁ : GenLe γ' γ₁) (h : PassPost ss γ r γ') :
    PassPost ss γ₀ r γ₁ := fun hwf =>
  have ⟨hs, h2⟩ := h (h₀.1 hwf)
  ⟨hs.mono (fun _ hx => h₀.drawn hx) fun _ hx => h₁.drawn hx, h2⟩

/-- One pass of `runStmtsRec insertInvariantAsserts` over a list of size below `fuel` inserts the
    checks of some of its loops, numbered by names it draws (`PassPost`). -/
private theorem runStmtsRec_insert_aux : ∀ (fuel : Nat) (ss : List Statement) (γ : CoreGenState),
    sizeOf ss < fuel →
    Transform.PostGen (· = γ) (Transform.runStmtsRec insertInvariantAsserts ss) fun r γ' =>
      GenLe γ γ' ∧ PassPost ss γ r γ'
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, [], γ, _ => by
    simp only [Transform.runStmtsRec]
    exact Transform.PostGen.pure fun _ h => h ▸ ⟨GenLe.refl _, fun _ =>
      ⟨.nil, Nat.le_refl _, by simp, fun _ => rfl⟩⟩
  | fuel + 1, s :: rest, γ, hsz => by
    have ih := runStmtsRec_insert_aux fuel
    simp only [List.cons.sizeOf_spec] at hsz
    rw [Transform.runStmtsRec.eq_def]
    dsimp only
    refine Transform.PostGen.bind (Q₁ := fun r γ₁ => GenLe γ γ₁ ∧ (γ.WF →
        StmtRelStep (Drawn γ) (Drawn γ₁) s r.2 ∧
        Block.numCheckedLoops r.2 ≤ Stmt.numCheckedLoops s ∧
        (r.1 = Bool.true → Block.numCheckedLoops r.2 < Stmt.numCheckedLoops s) ∧
        (r.1 = Bool.false → Stmt.numCheckedLoops s = 0))) ?_ fun r => ?_
    · refine Transform.PostGen.bind (insertInvariantAsserts_post s γ) fun o => ?_
      cases o with
      | some ss =>
        refine Transform.PostGen.pure fun γ' ⟨g, m, inv, bss, md, n, hs, hc, hss, hgen⟩ => ?_
        subst hs hss
        obtain ⟨hle, hmem, hfresh⟩ := gen_fresh hgen
        refine ⟨hle, fun hwf => ⟨.loop n hc fun x hx => ?_, ?_, fun _ => ?_, nofun⟩⟩
        · cases m with
          | none => simp [measureVars] at hx
          | some _ =>
            simp only [measureVars, List.mem_singleton] at hx
            subst hx
            exact ⟨fun ⟨k, hk, he⟩ => hfresh hwf (measureIdent_inj _ _ he ▸ hk), n, hmem, rfl⟩
        all_goals
          have hcl : ¬ (inv.isEmpty && m.isNone) = Bool.true := fun h => hc (by
            simpa [Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] using h)
          simp only [Block.numCheckedLoops_invChecked, Stmt.numCheckedLoops, hcl,
            Bool.false_eq_true, ↓reduceIte]
          omega
      | none =>
        refine Transform.PostGen.of_forall fun γ₁ ⟨hnl, hγ⟩ => ?_
        subst hγ
        cases s with
        | cmd c => exact Transform.PostGen.pure fun _ h => h ▸ ⟨GenLe.refl _, fun _ =>
            ⟨.cmd, by simp [Block.numCheckedLoops], nofun, fun _ => rfl⟩⟩
        | exit l md => exact Transform.PostGen.pure fun _ h => h ▸ ⟨GenLe.refl _, fun _ =>
            ⟨.exit, by simp [Block.numCheckedLoops], nofun, fun _ => rfl⟩⟩
        | typeDecl tc md => exact Transform.PostGen.pure fun _ h => h ▸ ⟨GenLe.refl _, fun _ =>
            ⟨.typeDecl, by simp [Block.numCheckedLoops], nofun, fun _ => rfl⟩⟩
        | loop g m inv b md =>
          obtain ⟨rfl, rfl⟩ := hnl g m inv b md rfl
          simp only [Stmt.loop.sizeOf_spec] at hsz
          refine Transform.PostGen.bind (ih b _ (by omega)) fun r => Transform.PostGen.pure
            fun γ' ⟨hle, hb⟩ => ⟨hle, fun hwf => ?_⟩
          obtain ⟨hb, h1, h2, h3⟩ := hb hwf
          exact ⟨.loopBare hb, by simpa [Block.numCheckedLoops, Stmt.numCheckedLoops] using h1,
            fun h => by simpa [Block.numCheckedLoops, Stmt.numCheckedLoops] using h2 h,
            fun h => by simpa [Stmt.numCheckedLoops] using h3 h⟩
        | block l b md =>
          simp only [Stmt.block.sizeOf_spec] at hsz
          refine Transform.PostGen.bind (ih b _ (by omega)) fun r => Transform.PostGen.pure
            fun γ' ⟨hle, hb⟩ => ⟨hle, fun hwf => ?_⟩
          obtain ⟨hb, h1, h2, h3⟩ := hb hwf
          exact ⟨.block hb, by simpa [Block.numCheckedLoops, Stmt.numCheckedLoops] using h1,
            fun h => by simpa [Block.numCheckedLoops, Stmt.numCheckedLoops] using h2 h,
            fun h => by simpa [Stmt.numCheckedLoops] using h3 h⟩
        | ite c t e md =>
          simp only [Stmt.ite.sizeOf_spec] at hsz
          refine Transform.PostGen.bind (ih t _ (by omega)) fun r => ?_
          refine Transform.PostGen.of_forall fun γ₂ ⟨hle₁, ht⟩ => ?_
          refine Transform.PostGen.bind (ih e γ₂ (by omega)) fun r' => Transform.PostGen.pure
            fun γ' ⟨hle₂, he⟩ => ⟨GenLe.refl _ |>.trans (hle₁.trans hle₂), fun hwf => ?_⟩
          obtain ⟨ht, ht1, ht2, ht3⟩ := ht hwf
          obtain ⟨he, he1, he2, he3⟩ := he (hle₁.1 hwf)
          refine ⟨.ite (ht.mono (fun _ h => h) fun _ hx => hle₂.drawn hx)
            (he.mono (fun _ hx => hle₁.drawn hx) fun _ h => h), ?_, fun h => ?_, fun h => ?_⟩
          · simp only [Block.numCheckedLoops, Stmt.numCheckedLoops]
            omega
          · simp only [Block.numCheckedLoops, Stmt.numCheckedLoops]
            cases h₁ : r.1 <;> cases h₂ : r'.1 <;> simp_all <;> omega
          · simp only [Stmt.numCheckedLoops]
            cases h₁ : r.1 <;> cases h₂ : r'.1 <;> simp_all
    · refine Transform.PostGen.of_forall fun γ₁ ⟨hle₁, hr⟩ => ?_
      refine Transform.PostGen.bind (ih rest γ₁ (by omega)) fun r' => Transform.PostGen.pure
        fun γ' ⟨hle₂, hr'⟩ => ⟨hle₁.trans hle₂, fun hwf => ?_⟩
      obtain ⟨hs, h1, h2, h3⟩ := hr hwf
      obtain ⟨hrr, h1', h2', h3'⟩ := hr' (hle₁.1 hwf)
      refine ⟨.cons (hs.mono (fun _ h => h) fun _ hx => hle₂.drawn hx)
        (hrr.mono (fun _ hx => hle₁.drawn hx) fun _ h => h), ?_, fun h => ?_, fun h => ?_⟩
      · simp only [Block.numCheckedLoops_append, Block.numCheckedLoops]
        omega
      · simp only [Block.numCheckedLoops_append, Block.numCheckedLoops]
        cases h₁ : r.1 <;> cases h₂ : r'.1 <;> simp_all <;> omega
      · simp only [Block.numCheckedLoops]
        cases h₁ : r.1 <;> cases h₂ : r'.1 <;> simp_all

/-- One pass of `runStmtsRec insertInvariantAsserts` inserts the checks of some loops of a list,
    numbered by names it draws (`PassPost`). -/
private theorem runStmtsRec_insert (ss : List Statement) (γ : CoreGenState) :
    Transform.PostGen (· = γ) (Transform.runStmtsRec insertInvariantAsserts ss) fun r γ' =>
      GenLe γ γ' ∧ PassPost ss γ r γ' :=
  runStmtsRec_insert_aux _ ss γ (Nat.lt_succ_self _)

/-- The number of loops carrying invariants or a measure in the structured procedure body of a
    declaration. -/
private def declNumChecked : Decl → Nat
  | .proc proc _ => match proc.body with
    | .structured ss => Block.numCheckedLoops ss
    | .cfg _ => 0
  | _ => 0

/-- The number of loops carrying invariants or a measure in the structured procedure bodies of a
    program. -/
private def numChecked (p : Program) : Nat := (p.decls.map declNumChecked).sum

mutual
/-- A statement has no more loops carrying invariants or a measure than loops. -/
private theorem Stmt.numCheckedLoops_le : ∀ s : Statement,
    Stmt.numCheckedLoops s ≤ Stmt.numLoops s
  | .loop _ m inv body _ => by
    have hb := Block.numCheckedLoops_le body
    simp only [Stmt.numCheckedLoops, Stmt.numLoops]
    split <;> omega
  | .block _ bss _ => by
    simpa [Stmt.numCheckedLoops, Stmt.numLoops] using Block.numCheckedLoops_le bss
  | .ite _ tss ess _ => by
    have ht := Block.numCheckedLoops_le tss
    have he := Block.numCheckedLoops_le ess
    simp only [Stmt.numCheckedLoops, Stmt.numLoops]
    omega
  | .cmd _ | .exit _ _ | .typeDecl _ _ => by simp [Stmt.numCheckedLoops]

/-- A list has no more loops carrying invariants or a measure than loops. -/
private theorem Block.numCheckedLoops_le : ∀ ss : List Statement,
    Block.numCheckedLoops ss ≤ Block.numLoops ss
  | [] => by simp [Block.numCheckedLoops]
  | s :: rest => by
    have hs := Stmt.numCheckedLoops_le s
    have hr := Block.numCheckedLoops_le rest
    simp only [Block.numCheckedLoops, Block.numLoops]
    omega
end

/-- A program has no more loops carrying invariants or a measure than loops. -/
private theorem numChecked_le (p : Program) : numChecked p ≤ numLoops p := by
  unfold numChecked numLoops
  rw [← Nat.zero_add (List.sum _)]
  generalize 0 = k
  generalize p.decls = ds
  induction ds generalizing k with
  | nil => simp
  | cons d ds ih =>
    rw [List.foldl_cons, List.map_cons, List.sum_cons]
    refine Nat.le_trans ?_ (ih _)
    cases d <;> simp only [declNumChecked] <;> try omega
    split <;> rename_i h <;> simp only [h]
    · have hb := Block.numCheckedLoops_le ‹_›
      omega
    · omega

/-- The invariant of the iteration from `p`: the generator state is well formed, and each
    procedure body of the program is that of `p` with the checks of some loops inserted,
    numbered by names drawn. -/
private def IterInv (p q : Program) (γ : CoreGenState) : Prop :=
  γ.WF ∧ List.Rel₂ (Core.LoopElim.DeclBodyRel (BlockRelSome (Drawn γ) [])) p.decls q.decls

/-- After one pass, a declaration whose procedure body is that of `d₀` with the checks of some
    loops inserted still is, with fewer loops carrying invariants or a measure when the pass
    reports a change and none when it reports none. -/
private theorem declStep_iter {γ γ' : CoreGenState} (hwf : γ.WF) (hle : GenLe γ γ')
    {d₀ d : Decl} {r : Bool × Decl}
    (h₁ : Core.LoopElim.DeclBodyRel (BlockRelSome (Drawn γ) []) d₀ d)
    (h₂ : Transform.DeclStep (fun ss r => PassPost ss γ r γ') d r) :
    Core.LoopElim.DeclBodyRel (BlockRelSome (Drawn γ') []) d₀ r.2 ∧
      declNumChecked r.2 ≤ declNumChecked d ∧
      (r.1 = Bool.true → declNumChecked r.2 < declNumChecked d) ∧
      (r.1 = Bool.false → declNumChecked r.2 = 0) := by
  cases d₀
  case proc proc₀ md₀ =>
    cases hb : proc₀.body
    · simp only [Core.LoopElim.DeclBodyRel, hb] at h₁ ⊢
      obtain ⟨ss₁, hrel, rfl⟩ := h₁
      obtain ⟨ss, ss', hss, hq, hr⟩ := h₂
      obtain rfl : ss₁ = ss := Body.structured.inj hss
      obtain ⟨hstep, hle', hlt, hz⟩ := hq hwf
      obtain ⟨c, d'⟩ := r
      cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at hr <;> subst hr
      · refine ⟨⟨ss₁, hrel.mono fun _ hx => hle.drawn hx, rfl⟩, ?_, nofun, fun _ => ?_⟩ <;>
          simp only [declNumChecked]
        · exact Nat.le_refl _
        · exact hz rfl
      · refine ⟨⟨ss', hrel.trans_step (fun _ h => h) (fun _ hx => hle.drawn hx) (by simp)
          hstep, rfl⟩, ?_, fun _ => ?_, nofun⟩ <;> simp only [declNumChecked]
        · exact Nat.le_of_lt (hlt rfl)
        · exact hlt rfl
    · -- `runProgram` rejects a CFG body.
      simp only [Core.LoopElim.DeclBodyRel, hb] at h₁
      subst h₁
      obtain ⟨ss, -, hss, -⟩ := h₂
      rw [hb] at hss
      cases hss
  all_goals
    obtain rfl := h₁
    obtain rfl := h₂
    exact ⟨rfl, Nat.le_refl _, nofun, fun _ => by simp [declNumChecked]⟩

/-- One pass keeps the procedure bodies those of `ds₀` with the checks of some loops inserted,
    removes some loops carrying invariants or a measure when it reports a change, and leaves
    none when it reports none. -/
private theorem rel₂_declStep_iter {γ γ' : CoreGenState} (hwf : γ.WF) (hle : GenLe γ γ')
    {ds₀ ds : List Decl} {rs : List (Bool × Decl)}
    (h₁ : List.Rel₂ (Core.LoopElim.DeclBodyRel (BlockRelSome (Drawn γ) [])) ds₀ ds)
    (h₂ : List.Rel₂ (Transform.DeclStep fun ss r => PassPost ss γ r γ') ds rs) :
    List.Rel₂ (Core.LoopElim.DeclBodyRel (BlockRelSome (Drawn γ') [])) ds₀ (rs.map (·.2)) ∧
      ((rs.map (·.2)).map declNumChecked).sum ≤ (ds.map declNumChecked).sum ∧
      (rs.any (·.1) = Bool.true →
        ((rs.map (·.2)).map declNumChecked).sum < (ds.map declNumChecked).sum) ∧
      (rs.any (·.1) = Bool.false → ((rs.map (·.2)).map declNumChecked).sum = 0) := by
  induction h₁ generalizing rs with
  | nil => cases h₂; exact ⟨.nil, by simp, by simp, by simp⟩
  | cons hd _ ih =>
    cases h₂ with
    | cons hd₂ hs₂ =>
      obtain ⟨hr, hle₁, hlt, hz⟩ := ih hs₂
      obtain ⟨hd', hle', hlt', hz'⟩ := declStep_iter hwf hle hd hd₂
      refine ⟨.cons hd' hr, ?_, fun h => ?_, fun h => ?_⟩
      · simp only [List.map_cons, List.sum_cons]
        omega
      · simp only [List.map_cons, List.sum_cons, List.any_cons, Bool.or_eq_true] at h ⊢
        rcases h with h | h
        · have hlt₁ := hlt' h
          omega
        · have hlt₂ := hlt h
          omega
      · simp only [List.map_cons, List.sum_cons, List.any_cons, Bool.or_eq_false_iff] at h ⊢
        have hz₁ := hz' h.1
        have hz₂ := hz h.2
        omega

/-- One pass of `runProgram insertInvariantAsserts` keeps the invariant of the iteration,
    removing some loops carrying invariants or a measure when it reports a change and leaving
    none when it reports none. -/
private theorem runProgram_insert (p q : Program) :
    Transform.PostGen (IterInv p q) (Transform.runProgram insertInvariantAsserts q)
      fun r γ' => IterInv p r.2 γ' ∧ (r.1 = Bool.true → numChecked r.2 < numChecked q) ∧
        (r.1 = Bool.false → numChecked r.2 = 0) := by
  refine Transform.PostGen.of_forall fun γ ⟨hwf, hrel⟩ => ?_
  refine (Transform.runProgram_postGen (Q := PassPost) GenLe.refl GenLe.trans PassPost.widen
    runStmtsRec_insert q γ).mono (fun _ h => h) fun r γ' ⟨hle, rs, hrs, hdecls, hc⟩ => ?_
  obtain ⟨hrel', -, hlt, hz⟩ := rel₂_declStep_iter hwf hle hrel hrs
  simp only [numChecked]
  rw [hdecls, hc]
  exact ⟨⟨hle.1 hwf, hdecls ▸ hrel'⟩, hlt, hz⟩

/-- A program whose procedure bodies are those of `p` with the checks of some loops inserted,
    and which has no loop carrying invariants or a measure, has the procedure bodies of `p` with
    the checks of all their loops inserted. -/
private theorem declBodyRel_blockRel {D : Expression.Ident → Prop} {p p' : Program}
    (h : List.Rel₂ (Core.LoopElim.DeclBodyRel (BlockRelSome D [])) p.decls p'.decls)
    (hn : numChecked p' = 0) :
    List.Rel₂ (Core.LoopElim.DeclBodyRel (BlockRel [])) p.decls p'.decls := by
  unfold numChecked at hn
  generalize p.decls = ds at h
  generalize p'.decls = ds' at h hn
  induction h with
  | nil => exact .nil
  | @cons d d' _ _ hd _ ih =>
    simp only [List.map_cons, List.sum_cons] at hn
    refine .cons ?_ (ih (by omega))
    cases d
    case proc proc md =>
      cases hb : proc.body
      · simp only [Core.LoopElim.DeclBodyRel, hb] at hd ⊢
        obtain ⟨ss', hrel, rfl⟩ := hd
        exact ⟨ss', hrel.blockRel (by simp only [declNumChecked] at hn; omega), rfl⟩
      · simp only [Core.LoopElim.DeclBodyRel, hb] at hd ⊢
        exact hd
    all_goals exact hd

/-- **The Core pass inserts the checks of loop invariants and measures.** When
    `Core.insertLoopInvariantAsserts p` succeeds with `p'` from a state whose generator state is
    well formed, `p'` has the declarations of `p` in order, except that a procedure with a
    structured body `ss` gets a body `ss'` that is `ss` with the checks of its loops inserted
    (`BlockRel [] ss ss'`). Each pass of the Core pass inserts the checks of the outermost loops not
    checked yet, numbered by names the generator has not drawn before, so the snapshot variable of a
    loop is none of those of the loops around it; after at most `Core.numLoops p + 1` passes, the
    bound the Core pass iterates to, no loop carrying invariants or a measure is left. -/
theorem insertLoopInvariantAsserts_blockRel {p p' : Program} {c : Bool}
    {σ σ' : Transform.CoreTransformState} (hwf : σ.genState.WF)
    (h : insertLoopInvariantAsserts p σ = (.ok (c, p'), σ')) :
    List.Rel₂ (fun d d' => match d with
      | .proc proc md => match proc.body with
        | .structured ss =>
          ∃ ss', BlockRel [] ss ss' ∧ d' = .proc { proc with body := .structured ss' } md
        | .cfg _ => d' = d
      | _ => d' = d) p.decls p'.decls := by
  have hinit : IterInv p p σ.genState := ⟨hwf, by
    generalize p.decls = ds
    induction ds with
    | nil => exact .nil
    | cons d ds ih =>
      refine .cons ?_ ih
      cases d
      case proc proc md =>
        cases hb : proc.body
        · simp only [Core.LoopElim.DeclBodyRel, hb]
          exact ⟨_, BlockRelSome.refl _, by rw [← hb]⟩
        · simp only [Core.LoopElim.DeclBodyRel, hb]
      all_goals rfl⟩
  obtain ⟨⟨-, hrel⟩, hn⟩ := Transform.runProgramUntil_postGen (Inv := IterInv p)
    (runProgram_insert p) (Nat.lt_succ_of_le (numChecked_le p)) σ _ σ' hinit h
  exact (declBodyRel_blockRel hrel hn).imp fun {d} _ h => by
    cases d
    case proc proc md => cases hb : proc.body <;> simpa [Core.LoopElim.DeclBodyRel, hb] using h
    all_goals exact h

/-- When `Core.insertLoopInvariantAsserts p` succeeds with `p'` from a state whose generator
    state is well formed, a procedure of `p` with a structured body `ss` has, at its position in
    `p'`, a body `ss'` that is `ss` with the checks of its loops inserted. -/
theorem insertLoopInvariantAsserts_body_blockRel {p p' : Program} {c : Bool}
    {σ σ' : Transform.CoreTransformState} (hwf : σ.genState.WF)
    (h : insertLoopInvariantAsserts p σ = (.ok (c, p'), σ'))
    {i : Nat} {proc : Procedure} {md : MetaData Expression} {ss : Statements}
    (hproc : p.decls[i]? = some (.proc proc md)) (hbody : proc.body = .structured ss) :
    ∃ ss', p'.decls[i]? = some (.proc { proc with body := .structured ss' } md) ∧
      BlockRel [] ss ss' := by
  obtain ⟨d', hd', hrel⟩ := (insertLoopInvariantAsserts_blockRel hwf h).getElem?_some hproc
  simp only [hbody] at hrel
  obtain ⟨ss', hrel, rfl⟩ := hrel
  exact ⟨ss', hd', hrel⟩

/-- A list with the checks of the loops of `ss` inserted satisfies the initial-environment gate
    `BlockInitEnvWF` at `base` wherever `ss` satisfies it at `base` with `prefixesReserved`
    reserved, when no prefix `base` reserves is a prefix of `measurePrefix` or starts with it:
    then no measure snapshot name starts with one. -/
theorem blockInitEnvWF_of_blockRel {base : InitEnvWFParams}
    (hprefixes : ∀ p ∈ base.prefixIdents,
      ¬ p.toList.isPrefixOf measurePrefix.toList ∧ ¬ measurePrefix.toList.isPrefixOf p.toList)
    {ss ss' : Statements}
    (hrel : BlockRel [] ss ss') {ρ : Env Expression}
    (hwf : BlockInitEnvWF (base.extend prefixesReserved) ss ρ) : BlockInitEnvWF base ss' ρ := by
  have hp : measurePrefix ∈
      (base.extend prefixesReserved).prefixIdents := by
    simp [Imperative.Logic.InitEnvWFParams.extend, prefixesReserved]
  have hbase : ∀ p ∈ base.prefixIdents, p ∈ (base.extend prefixesReserved).prefixIdents :=
    fun p h => List.mem_append_right _ h
  let Res : Expression.Ident → Prop := fun x =>
    measurePrefix.toList.isPrefixOf x.name.toList
  have hid := idents_not_reserved hwf
  have hDR : ∀ x, (ρ.store x).isSome = Bool.true → ¬ Res x :=
    fun x hx => hwf.reservedFreshCore x hx _ hp
  have hf := checkExprFacts (df := base.declaredFuncs) hwf.factoryDeclared
  have hdu' := hrel.defUseWellFormed (Res := Res) measureIdent_reserved (by simp) hid
    (D' := fun x => (ρ.store x).isSome) (fun x => by simp) hDR hf hwf.defUseOk
  have hdefs := hrel.defs
  exact { hwf with
    readWritesDefined := fun _ hn hnd =>
      Imperative.Block.defined_of_mem_touchedVars (fun _ _ h => h) hdu' hn hnd
    defsUndefined := fun x hx => by
      rcases hdefs.2.1 x hx with hx | ⟨n, rfl⟩
      · exact hwf.defsUndefined x hx
      · cases hs : ρ.store (measureIdent n) with
        | none => rfl
        | some _ => exact absurd (measureIdent_reserved n) (hDR _ (by simp [hs]))
    definedVarsNotReserved := fun x hx name hname p hpb => by
      rcases hdefs.2.1 x hx with hx | ⟨n, rfl⟩
      · exact hwf.definedVarsNotReserved x hx name hname p (hbase p hpb)
      · rw [← LawfulHasIdent.ident_inj hname, List.isPrefixOf_iff_prefix]
        intro hp
        have hm : measurePrefix.toList <+: (measurePrefix ++ n).toList :=
          ⟨n.toList, by rw [String.toList_append]⟩
        rcases List.prefix_or_prefix_of_prefix hp hm with h | h
        · exact (hprefixes p hpb).1 (List.isPrefixOf_iff_prefix.2 h)
        · exact (hprefixes p hpb).2 (List.isPrefixOf_iff_prefix.2 h)
    reservedFresh := fun x hx name hname p hpb =>
      hwf.reservedFresh x hx name hname p (hbase p hpb)
    exitsNotReserved := fun l hl p hpl =>
      hwf.exitsNotReserved l (hrel.labels_measures.1 ▸ hl) p hpl
    defUseOk := hdu'
    initTypesInhabited := fun ty hty => by
      rcases hdefs.2.2 ty hty with hty | rfl
      · exact hwf.initTypesInhabited ty hty
      · exact ⟨Lambda.SemValue.ofInt ρ.factory.model.tcInterp 0, rfl, rfl⟩
    fvarTypesOk := by
      obtain ⟨Γ, hσ, hw⟩ := hwf.fvarTypesOk
      refine ⟨Γ, hσ, hrel.fvarTypesWellAnnotated (Res := Res) measureIdent_reserved (by simp)
        hid hDR hwf.defUseOk (fun x ty hx => ?_) (fun _ _ => rfl) (by simp) hf hw⟩
      obtain ⟨v, hv, -⟩ := hσ x ty hx
      exact hDR x (by simp [hv])
    measuresTyped := fun m hm => by simp [hrel.labels_measures.2] at hm }

end -- public section

end Core.InsertLoopInvAsserts
