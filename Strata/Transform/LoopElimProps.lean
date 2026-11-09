/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.LoopElimPure
public import Strata.DL.Imperative.StmtProps
public import Strata.Languages.Core.Logic.LangDef
public import Strata.Transform.CoreTransformProps
import Strata.Languages.Core.ExpressionsProps
import all Strata.Languages.Core.Factory
import all Strata.Transform.LoopElim
import all Strata.Transform.CoreTransform
import all Strata.Transform.LoopElimPure
import all Strata.DL.Imperative.Cmd
import all Strata.DL.Imperative.Stmt

/-! # Properties of loop elimination

`LoopElim.StmtRel s s'` (`LoopElim.BlockRel` for lists) says that `s'` is `s` with every loop
replaced by its passive encoding (`Stmt.loopPassive`) over its loop-carried variables
(`Block.carriedVars`), when its body exits to no label starting with the prefix reserved for
the labels the encoding mints (`Core.loopElimPrefix`), with the loops of its body eliminated the
same way.  The pure pass `Block.loopElim` returns such a list for an input exiting to no such
label (`Block.loopElim_rel`), in particular for an input satisfying the gate `BlockInitEnvWF`
with that prefix reserved for block labels (`Core.LoopElim.blockRel_of_loopElim`).

`StmtRelPartial` (`BlockRelPartial`) eliminates some loops that way and keeps the others
unchanged.  It is reflexive and transitive (`BlockRelPartial.refl`, `BlockRelPartial.trans`)
and is `BlockRel` when the output has no loop (`BlockRelPartial.blockRel`).  One pass of the
Core pass, `runProgram removeLoop`, eliminates the outermost loops of every procedure body it has
not eliminated yet, with their bodies unchanged, so it relates the bodies of any program
related to `p` (`DeclBodyRel BlockRelPartial`) to those of `p` the same way, with fewer loops
when it reports a change and none when it reports none (`Core.LoopElim.runProgram_removeLoop`).
After at most `Core.numLoops p + 1` passes, as `Core.loopElim` runs them, no loop is left
(`Core.LoopElim.declBodyRel_blockRel`).

Related lists define the same variables (`BlockRel.mem_definedVars`), declare no new
`init` types (`BlockRel.initTypes`) and have the same `exit` targets (`BlockRel.labels`); the
output is def-use well formed wherever the input is
(`BlockRel.defUseWellFormed`) and has its free-variable annotations checked wherever the input
does (`BlockRel.fvarTypesWellAnnotated`), provided negation (`HasBoolOps.not`) reads no new
variable, refers to no new undeclared operator and adds no new annotated occurrence.  For Core,
the output satisfies the gate `BlockInitEnvWF` wherever the input does, at the input's
parameters without any block-label reservation (`Core.LoopElim.blockInitEnvWF_of_blockRel`).
`Core.LoopElim.single_blockRel` turns one related pair into a transformation for the trace
theorems of `LoopElimCoreCorrect`.

The properties of the pure pass of `LoopElimPure.lean` and of the Core pass of `LoopElim.lean`
are kept together here: the pure pass exists only for the correctness proof, and `BlockRel`
relates both to their inputs.  For the Core pass, `Core.LoopElim.loopElim_blockRel` states it
for a whole program and `Core.LoopElim.loopElim_body_blockRel` for one procedure body. -/

-- `CmdExt.hasHavoc_eq`, imported through `CoreTransformProps`, unfolds the havocs of the
-- encoding before the `havocs_*` lemmas below can rewrite them.
attribute [-simp] Imperative.CmdExt.hasHavoc_eq

namespace Imperative
namespace LoopElim

public section

variable {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]

mutual
/-- `s'` is `s` with its loops eliminated: each loop without invariants and measure becomes its
    passive encoding, numbered `n`, when its body exits to no label starting with the prefix
    reserved for the labels the encoding mints (`Core.loopElimPrefix`). -/
inductive StmtRel : Stmt P (CmdExt P) → Stmt P (CmdExt P) → Prop where
  | cmd (c : CmdExt P) : StmtRel (.cmd c) (.cmd c)
  | exit (l : String) (md : MetaData P) : StmtRel (.exit l md) (.exit l md)
  | typeDecl (tc : TypeConstructor) (md : MetaData P) :
      StmtRel (.typeDecl tc md) (.typeDecl tc md)
  | block {l : String} {bss bss' : List (Stmt P (CmdExt P))} {md : MetaData P} :
      BlockRel bss bss' → StmtRel (.block l bss md) (.block l bss' md)
  | ite {c : ExprOrNondet P} {tss tss' ess ess' : List (Stmt P (CmdExt P))}
      {md : MetaData P} :
      BlockRel tss tss' → BlockRel ess ess' → StmtRel (.ite c tss ess md) (.ite c tss' ess' md)
  | loop {g : ExprOrNondet P} {body body' : List (Stmt P (CmdExt P))} {md : MetaData P}
      (n : String) :
      BlockRel body body' → (∀ l ∈ Block.labels body, l.startsWith Core.loopElimPrefix = false) →
      StmtRel (.loop g none [] body md) (Stmt.loopPassive n g (Block.carriedVars body) body' md)

/-- `ss'` is `ss` with its loops eliminated, statement by statement (`StmtRel`). -/
inductive BlockRel : List (Stmt P (CmdExt P)) → List (Stmt P (CmdExt P)) → Prop where
  | nil : BlockRel [] []
  | cons {s s' : Stmt P (CmdExt P)} {ss ss' : List (Stmt P (CmdExt P))} :
      StmtRel s s' → BlockRel ss ss' → BlockRel (s :: ss) (s' :: ss')
end

/-! ## The pure pass -/

/-- A loop is related by `StmtRel` only to its passive encoding, numbered by some `n`, over its
    loop-carried variables, with in place of its body a list `body'` that is its body with its
    loops eliminated (`BlockRel`); and its body exits to no label starting with
    `Core.loopElimPrefix`. -/
theorem StmtRel.loop_inv {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P (CmdExt P))} {md : MetaData P} {s' : Stmt P (CmdExt P)}
    (h : StmtRel (.loop g m inv body md) s') :
    ∃ n body', BlockRel body body' ∧
      (∀ l ∈ Block.labels body, l.startsWith Core.loopElimPrefix = false) ∧
      s' = Stmt.loopPassive n g (Block.carriedVars body) body' md := by
  cases h with
  | loop n hb hl => exact ⟨n, _, hb, hl, rfl⟩

mutual
/-- A successful `Stmt.loopElimM` eliminates the loops of a statement that exits to no label
    starting with `Core.loopElimPrefix`. -/
private theorem _root_.Imperative.Stmt.loopElimM_rel :
    ∀ (s : Stmt P (CmdExt P)) (γ : StringGenState) {s' : Stmt P (CmdExt P)} {γ' : StringGenState},
    Stmt.loopElimM s γ = some (s', γ') →
    (∀ l ∈ Stmt.labels s, l.startsWith Core.loopElimPrefix = false) → StmtRel s s'
  | .loop g m inv body md, γ, s', γ', h, hl => by
    cases m with
    | some _ => simp [Stmt.loopElimM] at h
    | none =>
      cases inv with
      | cons _ _ => simp [Stmt.loopElimM] at h
      | nil =>
        simp only [Stmt.loopElimM] at h
        split at h
        · rename_i body' γ1 hb
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          have hl : ∀ l ∈ Block.labels body, l.startsWith Core.loopElimPrefix = false := by
            simpa [Stmt.labels] using hl
          exact .loop _ (Block.loopElimM_rel body _ hb hl) hl
        · cases h
  | .block l bss md, γ, s', γ', h, hl => by
    simp only [Stmt.loopElimM] at h
    split at h
    · rename_i bss' γ1 hb
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact .block (Block.loopElimM_rel bss _ hb (by simpa [Stmt.labels] using hl))
    · cases h
  | .ite c tss ess md, γ, s', γ', h, hl => by
    simp only [Stmt.loopElimM] at h
    split at h
    · rename_i tss' γ1 ht
      split at h
      · rename_i ess' γ2 he
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simp only [Stmt.labels, List.mem_append] at hl
        exact .ite (Block.loopElimM_rel tss _ ht fun l h => hl l (.inl h))
          (Block.loopElimM_rel ess _ he fun l h => hl l (.inr h))
      · cases h
    · cases h
  | .cmd c, γ, s', γ', h, _ => by
    simp only [Stmt.loopElimM, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact .cmd c
  | .exit l md, γ, s', γ', h, _ => by
    simp only [Stmt.loopElimM, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact .exit l md
  | .typeDecl tc md, γ, s', γ', h, _ => by
    simp only [Stmt.loopElimM, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact .typeDecl tc md

/-- A successful `Block.loopElimM` eliminates the loops of a list that exits to no label
    starting with `Core.loopElimPrefix`. -/
private theorem _root_.Imperative.Block.loopElimM_rel :
    ∀ (ss : List (Stmt P (CmdExt P))) (γ : StringGenState)
    {ss' : List (Stmt P (CmdExt P))} {γ' : StringGenState},
    Block.loopElimM ss γ = some (ss', γ') →
    (∀ l ∈ Block.labels ss, l.startsWith Core.loopElimPrefix = false) → BlockRel ss ss'
  | [], γ, ss', γ', h, _ => by
    simp only [Block.loopElimM, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact .nil
  | s :: rest, γ, ss', γ', h, hl => by
    simp only [Block.loopElimM] at h
    split at h
    · rename_i s' γ1 hs
      split at h
      · rename_i rest' γ2 hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simp only [Block.labels, List.mem_append] at hl
        exact .cons (Stmt.loopElimM_rel s _ hs fun l h => hl l (.inl h))
          (Block.loopElimM_rel rest _ hr fun l h => hl l (.inr h))
      · cases h
    · cases h
end

/-- The output of the pure pass `Block.loopElim` is its input with its loops eliminated, when
    the input exits to no label starting with `Core.loopElimPrefix`. -/
theorem _root_.Imperative.Block.loopElim_rel {ss ss' : List (Stmt P (CmdExt P))}
    (h : Block.loopElim ss = some ss')
    (hl : ∀ l ∈ Block.labels ss, l.startsWith Core.loopElimPrefix = false) :
    BlockRel ss ss' := by
  simp only [Block.loopElim, Option.map_eq_some_iff] at h
  obtain ⟨⟨_, γ⟩, h, rfl⟩ := h
  exact Block.loopElimM_rel ss _ h hl

/-! ## Variables, `init` types and well-formedness of the output -/

omit [HasBoolOps P] in
/-- A list of havocs defines no variable. -/
private theorem havocs_definedVars (M : List P.Ident) (md : MetaData P) (b : Bool) :
    Block.definedVars
      (M.map fun n => Stmt.cmd (P := P) (HasHavoc.havoc (P := P) (CmdT := CmdExt P) n md)) b =
      [] := by
  induction M with
  | nil => rfl
  | cons _ _ ih =>
    simp only [List.map_cons, Block.definedVars, ih, List.append_nil]
    rfl

/-- The variables the passive encoding of a loop defines are those its body defines, at any
    nesting depth; it defines none at top level. -/
private theorem loopPassive_definedVars (n : String) (g : ExprOrNondet P) (M : List P.Ident)
    (body' : List (Stmt P (CmdExt P))) (md : MetaData P) (b : Bool) :
    Stmt.definedVars (Stmt.loopPassive n g M body' md) b =
      if b then [] else Block.definedVars body' false := by
  cases b <;> cases g <;>
    simp [Stmt.loopPassive, LoopElim.havocBlock, LoopElim.enterAssume, LoopElim.exitAssume,
      havocs_definedVars, HasPassiveCmds.assume,
      HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars]

mutual
/-- A statement and its output define the same variables. -/
theorem StmtRel.mem_definedVars {s s' : Stmt P (CmdExt P)} (h : StmtRel s s') (b : Bool)
    (x : P.Ident) : x ∈ Stmt.definedVars s' b ↔ x ∈ Stmt.definedVars s b := by
  match h with
  | .cmd _ | .exit _ _ | .typeDecl _ _ => exact .rfl
  | .block hb =>
    cases b <;> simp [Stmt.definedVars, hb.mem_definedVars false x]
  | .ite ht he =>
    cases b <;> simp [Stmt.definedVars, ht.mem_definedVars false x, he.mem_definedVars false x]
  | .loop _ hb _ =>
    rw [loopPassive_definedVars]
    cases b <;> simp [Stmt.definedVars, hb.mem_definedVars false x]

/-- A list and its output define the same variables. -/
theorem BlockRel.mem_definedVars {ss ss' : List (Stmt P (CmdExt P))} (h : BlockRel ss ss')
    (b : Bool) (x : P.Ident) : x ∈ Block.definedVars ss' b ↔ x ∈ Block.definedVars ss b := by
  match h with
  | .nil => exact .rfl
  | .cons hs hr =>
    simp [Block.definedVars, hs.mem_definedVars b x, hr.mem_definedVars b x]
end

omit [HasFvar P] [HasFvars P] [HasBoolOps P] in
/-- A list of havocs declares no `init` type. -/
private theorem havocs_initTypes (M : List P.Ident) (md : MetaData P) :
    Block.initTypes
      (M.map fun n => Stmt.cmd (P := P) (HasHavoc.havoc (P := P) (CmdT := CmdExt P) n md)) =
      [] := by
  induction M with
  | nil => rfl
  | cons _ _ ih =>
    simp only [List.map_cons, Block.initTypes, ih, List.append_nil]
    rfl

mutual
/-- The output of a statement declares only `init` types the statement declares. -/
theorem StmtRel.initTypes {s s' : Stmt P (CmdExt P)} (h : StmtRel s s') :
    ∀ ty ∈ Stmt.initTypes s', ty ∈ Stmt.initTypes s := by
  match h with
  | .cmd _ | .exit _ _ | .typeDecl _ _ => exact fun _ h => h
  | .block hb => simpa [Stmt.initTypes] using hb.initTypes
  | .ite ht he =>
    intro ty hty
    simp only [Stmt.initTypes, List.mem_append] at hty ⊢
    exact hty.imp (ht.initTypes ty) (he.initTypes ty)
  | @StmtRel.loop _ _ _ _ g body body' md n hb _ =>
    intro ty hty
    have hb := hb.initTypes
    cases g <;>
      simp_all [Stmt.loopPassive, LoopElim.havocBlock, LoopElim.enterAssume,
        LoopElim.exitAssume, Stmt.initTypes, havocs_initTypes,
        HasPassiveCmds.assume, HasInitTypesImp.initTypes, CmdExt.initTypes, Cmd.initTypes,
        Block.initTypes]

/-- The output of a list declares only `init` types the list declares. -/
theorem BlockRel.initTypes {ss ss' : List (Stmt P (CmdExt P))} (h : BlockRel ss ss') :
    ∀ ty ∈ Block.initTypes ss', ty ∈ Block.initTypes ss := by
  match h with
  | .nil => exact fun _ h => h
  | .cons hs hr =>
    intro ty hty
    simp only [Block.initTypes, List.mem_append] at hty ⊢
    exact hty.imp (hs.initTypes ty) (hr.initTypes ty)
end

mutual
/-- A statement and its output have the same `exit` targets. -/
theorem StmtRel.labels {s s' : Stmt P (CmdExt P)} (h : StmtRel s s') :
    Stmt.labels s' = Stmt.labels s := by
  match h with
  | .cmd _ | .exit _ _ | .typeDecl _ _ => rfl
  | .block hb => simp [Stmt.labels, hb.labels]
  | .ite ht he => simp [Stmt.labels, ht.labels, he.labels]
  | @StmtRel.loop _ _ _ _ g body body' md n hb _ =>
    cases g <;>
      simp [Stmt.loopPassive, LoopElim.havocBlock, LoopElim.enterAssume, LoopElim.exitAssume,
        Stmt.labels, Block.labels, Block.labels_map_cmd, hb.labels]

/-- A list and its output have the same `exit` targets. -/
theorem BlockRel.labels {ss ss' : List (Stmt P (CmdExt P))} (h : BlockRel ss ss') :
    Block.labels ss' = Block.labels ss := by
  match h with
  | .nil => rfl
  | .cons hs hr => simp [Block.labels, hs.labels, hr.labels]
end

/-- A statement and its output define the same variables, with the same declared types, in the
    enclosing scope. -/
private theorem StmtRel.typedDefinedVars {s s' : Stmt P (CmdExt P)} (h : StmtRel s s') :
    Stmt.typedDefinedVars s' = Stmt.typedDefinedVars s := by
  cases h <;> rfl

section DefUse
variable [HasOps P]

omit [HasBoolOps P] in
/-- A list of havocs of defined variables is def-use well formed. -/
private theorem havocs_defUseWellFormed {D df : P.Ident → Bool} (M : List P.Ident) (md : MetaData P)
    (hM : ∀ x ∈ M, D x = true) :
    Block.defUseWellFormed D df
      (M.map fun n => Stmt.cmd (P := P) (HasHavoc.havoc (P := P) (CmdT := CmdExt P) n md)) =
      true := by
  induction M with
  | nil => rfl
  | cons x M ih =>
    simp only [List.map_cons, Block.defUseWellFormed, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · simp [Stmt.defUseWellFormed, HasHavoc.havoc, HasVarsImp.readVars, CmdExt.readVars,
        Cmd.getVars, ExprOrNondet.getVars, HasVarsImp.modifiedVars, CmdExt.modifiedVars,
        Cmd.modifiedVars, HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars,
        HasOpsImp.getOps, CmdExt.getOps, Cmd.getOps, hM x (by simp)]
    · have : (fun n => D n || decide (n ∈ Stmt.definedVars (P := P)
          (Stmt.cmd (HasHavoc.havoc (P := P) (CmdT := CmdExt P) x md)) true)) = D := by
        funext n
        simp [Stmt.definedVars, HasHavoc.havoc, HasVarsImp.definedVars, CmdExt.definedVars,
          Cmd.definedVars]
      rw [this]
      exact ih fun y hy => hM y (by simp [hy])

omit [HasBoolOps P] in
/-- The loop-carried variables of a def-use well-formed body are defined at its entry. -/
theorem defined_of_mem_carriedVars {D df : P.Ident → Bool} {body : List (Stmt P (CmdExt P))}
    (hdu : Block.defUseWellFormed D df body = true) {x : P.Ident}
    (hx : x ∈ Block.carriedVars body) : D x = true := by
  simp only [Block.carriedVars, List.mem_filter, decide_eq_true_eq] at hx
  exact Block.defined_of_mem_touchedVars (fun _ _ h => h) hdu
    (by simp [Block.touchedVars, Block.modifiedOrDefinedVars, hx.1]) hx.2

mutual
/-- The output of a def-use well-formed statement is def-use well formed, provided negation
    reads no new variable and refers to no new undeclared operator. -/
theorem StmtRel.defUseWellFormed {s s' : Stmt P (CmdExt P)} (h : StmtRel s s')
    {D df : P.Ident → Bool}
    (hnotFv : ∀ g : P.Expr, ∀ x ∈ HasFvars.getFvars (HasBoolOps.not g), x ∈ HasFvars.getFvars g)
    (hnotOps : ∀ g : P.Expr, ∀ o ∈ HasOps.getOps (HasBoolOps.not g),
      o ∈ HasOps.getOps g ∨ df o = true)
    (hdu : Stmt.defUseWellFormed D df s = true) : Stmt.defUseWellFormed D df s' = true := by
  match h with
  | .cmd _ | .exit _ _ | .typeDecl _ _ => exact hdu
  | .block hb =>
    simp only [Stmt.defUseWellFormed] at hdu ⊢
    exact hb.defUseWellFormed hnotFv hnotOps hdu
  | .ite ht he =>
    simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu ⊢
    exact ⟨⟨hdu.1.1, ht.defUseWellFormed hnotFv hnotOps hdu.1.2⟩,
      he.defUseWellFormed hnotFv hnotOps hdu.2⟩
  | @StmtRel.loop _ _ _ _ g body body' md n hb _ =>
    simp only [Stmt.defUseWellFormed, Bool.and_eq_true, Option.map_none, Option.getD_none,
      List.all_nil, List.flatMap_nil, and_true] at hdu
    obtain ⟨⟨hg, hgo⟩, hbody⟩ := hdu
    have hbody' := hb.defUseWellFormed hnotFv hnotOps hbody
    have hM := havocs_defUseWellFormed (df := df) (Block.carriedVars body) md
      fun _ hx => defined_of_mem_carriedVars hbody hx
    cases g with
    | det g =>
      simp only [ExprOrNondet.getVars, List.all_eq_true] at hg hgo
      simp only [Stmt.loopPassive, havocBlock, enterAssume, HasPassiveCmds.assume,
        List.cons_append, List.nil_append, exitAssume, Stmt.defUseWellFormed, ExprOrNondet.getVars,
        Block.defUseWellFormed, hM, HasVarsImp.readVars, CmdExt.readVars, Cmd.getVars,
        Stmt.definedVars, ↓reduceIte, List.not_mem_nil, decide_false, Bool.or_false,
        HasVarsImp.modifiedVars, CmdExt.modifiedVars, Cmd.modifiedVars, List.all_nil,
        Bool.and_true, HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars,
        Bool.not_eq_true, Bool.decide_eq_false, HasOpsImp.getOps, CmdExt.getOps, Cmd.getOps,
        hbody', Bool.true_and, Bool.and_eq_true, List.all_eq_true]
      have hgo' : ∀ x ∈ HasOps.getOps g, df x = true := by
        simpa [ExprOrNondet.getOps] using hgo
      exact ⟨⟨hg, hgo⟩, ⟨hg, hgo'⟩, fun x hx => hg x (hnotFv g x hx),
        fun o ho => (hnotOps g o ho).elim (hgo' o) id⟩
    | nondet =>
      simp [Stmt.loopPassive, LoopElim.havocBlock, LoopElim.enterAssume, LoopElim.exitAssume,
        Stmt.defUseWellFormed, Block.defUseWellFormed, hM, hbody', ExprOrNondet.getVars,
        Stmt.definedVars, ExprOrNondet.getOps]

/-- The output of a def-use well-formed list is def-use well formed, provided negation reads no
    new variable and refers to no new undeclared operator. -/
theorem BlockRel.defUseWellFormed {ss ss' : List (Stmt P (CmdExt P))} (h : BlockRel ss ss')
    {D df : P.Ident → Bool}
    (hnotFv : ∀ g : P.Expr, ∀ x ∈ HasFvars.getFvars (HasBoolOps.not g), x ∈ HasFvars.getFvars g)
    (hnotOps : ∀ g : P.Expr, ∀ o ∈ HasOps.getOps (HasBoolOps.not g),
      o ∈ HasOps.getOps g ∨ df o = true)
    (hdu : Block.defUseWellFormed D df ss = true) : Block.defUseWellFormed D df ss' = true := by
  match h with
  | .nil => exact hdu
  | .cons (s := s) (s' := s') hs hr =>
    simp only [Block.defUseWellFormed, Bool.and_eq_true] at hdu ⊢
    have hD : (fun n => D n || decide (n ∈ Stmt.definedVars s' true)) =
        (fun n => D n || decide (n ∈ Stmt.definedVars s true)) := by
      funext n
      simp [hs.mem_definedVars true n]
    rw [hD]
    exact ⟨hs.defUseWellFormed hnotFv hnotOps hdu.1, hr.defUseWellFormed hnotFv hnotOps hdu.2⟩
end

end DefUse

omit [HasBoolOps P] in
/-- A list of havocs has its free-variable annotations checked under any typing. -/
private theorem havocs_fvarTypesWellAnnotated (Γ : VarTyping P) (M : List P.Ident)
    (md : MetaData P) :
    Block.fvarTypesWellAnnotated Γ
      (M.map fun n => Stmt.cmd (P := P) (HasHavoc.havoc (P := P) (CmdT := CmdExt P) n md)) := by
  induction M with
  | nil => trivial
  | cons x M ih =>
    refine ⟨fun _ _ h => ?_, ?_⟩
    · simp [HasHavoc.havoc, HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars,
        Cmd.getTypedVars, ExprOrNondet.getTypedVars] at h
    · exact ih

mutual
/-- The output of a statement has its free-variable annotations checked wherever the statement
    does, provided negation adds no annotated occurrence. -/
theorem StmtRel.fvarTypesWellAnnotated {s s' : Stmt P (CmdExt P)} (h : StmtRel s s')
    (hnotTy : ∀ g : P.Expr, ∀ p ∈ HasFvars.getTypedFvars (HasBoolOps.not g),
      p ∈ HasFvars.getTypedFvars g)
    {Γ : VarTyping P} (hw : Stmt.fvarTypesWellAnnotated Γ s) :
    Stmt.fvarTypesWellAnnotated Γ s' := by
  match h with
  | .cmd _ | .exit _ _ | .typeDecl _ _ => exact hw
  | .block hb => exact hb.fvarTypesWellAnnotated hnotTy hw
  | .ite ht he =>
    exact ⟨hw.1, ht.fvarTypesWellAnnotated hnotTy hw.2.1, he.fvarTypesWellAnnotated hnotTy hw.2.2⟩
  | @StmtRel.loop _ _ _ _ g body body' md n hb _ =>
    obtain ⟨hg, -, -, hbody⟩ := hw
    have hbody' := hb.fvarTypesWellAnnotated hnotTy hbody
    have hnil : ∀ Γ : VarTyping P, Γ.extend [] = Γ := fun _ => rfl
    have hM := havocs_fvarTypesWellAnnotated Γ (Block.carriedVars body) md
    cases g with
    | det g =>
      refine ⟨hg, ⟨⟨hM, ?_⟩, ?_⟩, trivial⟩
      · refine ⟨fun x ty hx => hg x ty (by simpa [HasPassiveCmds.assume,
          HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars, Cmd.getTypedVars,
          ExprOrNondet.getTypedVars] using hx), ?_⟩
        simpa [hnil, Stmt.typedDefinedVars, LoopElim.havocBlock,
          HasPassiveCmds.assume, HasTypedVarsImp.typedDefinedVars, CmdExt.typedDefinedVars,
          Cmd.typedDefinedVars] using hbody'
      · simp only [Stmt.typedDefinedVars, hnil]
        refine ⟨hM, ?_, trivial⟩
        intro x ty hx
        simp only [HasPassiveCmds.assume, HasTypedVarsImp.typedReadVars,
          CmdExt.typedReadVars, Cmd.getTypedVars] at hx
        exact hg x ty (by simpa [ExprOrNondet.getTypedVars] using hnotTy g _ hx)
    | nondet =>
      refine ⟨hg, ⟨⟨hM, ?_⟩, ?_⟩, trivial⟩
      · simpa [hnil, Stmt.typedDefinedVars, LoopElim.havocBlock,
          LoopElim.enterAssume] using hbody'
      · simp only [Stmt.typedDefinedVars, hnil]
        exact ⟨hM, trivial⟩

/-- The output of a list has its free-variable annotations checked wherever the list does,
    provided negation adds no annotated occurrence. -/
theorem BlockRel.fvarTypesWellAnnotated {ss ss' : List (Stmt P (CmdExt P))} (h : BlockRel ss ss')
    (hnotTy : ∀ g : P.Expr, ∀ p ∈ HasFvars.getTypedFvars (HasBoolOps.not g),
      p ∈ HasFvars.getTypedFvars g)
    {Γ : VarTyping P} (hw : Block.fvarTypesWellAnnotated Γ ss) :
    Block.fvarTypesWellAnnotated Γ ss' := by
  match h with
  | .nil => exact hw
  | .cons hs hr =>
    refine ⟨hs.fvarTypesWellAnnotated hnotTy hw.1, ?_⟩
    rw [hs.typedDefinedVars]
    exact hr.fvarTypesWellAnnotated hnotTy hw.2
end

/-! ## Partial elimination

`StmtRelPartial s s'` says that `s'` is `s` with some of its loops eliminated as by `StmtRel`
and the others kept unchanged, body included.  It is reflexive and transitive
(`BlockRelPartial.trans`), so it relates a list to the output of several passes each
eliminating some loops, and it is `BlockRel` on an output without loops
(`BlockRelPartial.blockRel`). -/

mutual
/-- `s'` is `s` with some of its loops eliminated as by `StmtRel`, and the others kept
    unchanged, body included. -/
inductive StmtRelPartial : Stmt P (CmdExt P) → Stmt P (CmdExt P) → Prop where
  | cmd (c : CmdExt P) : StmtRelPartial (.cmd c) (.cmd c)
  | exit (l : String) (md : MetaData P) : StmtRelPartial (.exit l md) (.exit l md)
  | typeDecl (tc : TypeConstructor) (md : MetaData P) :
      StmtRelPartial (.typeDecl tc md) (.typeDecl tc md)
  | block {l : String} {bss bss' : List (Stmt P (CmdExt P))} {md : MetaData P} :
      BlockRelPartial bss bss' → StmtRelPartial (.block l bss md) (.block l bss' md)
  | ite {c : ExprOrNondet P} {tss tss' ess ess' : List (Stmt P (CmdExt P))}
      {md : MetaData P} :
      BlockRelPartial tss tss' → BlockRelPartial ess ess' →
      StmtRelPartial (.ite c tss ess md) (.ite c tss' ess' md)
  | keep (g : ExprOrNondet P) (m : Option P.Expr) (inv : List (String × P.Expr))
      (body : List (Stmt P (CmdExt P))) (md : MetaData P) :
      StmtRelPartial (.loop g m inv body md) (.loop g m inv body md)
  | loop {g : ExprOrNondet P} {body body' : List (Stmt P (CmdExt P))} {md : MetaData P}
      (n : String) :
      BlockRelPartial body body' →
      (∀ l ∈ Block.labels body, l.startsWith Core.loopElimPrefix = false) →
      StmtRelPartial (.loop g none [] body md)
        (Stmt.loopPassive n g (Block.carriedVars body) body' md)

/-- `ss'` is `ss` with some of its loops eliminated, statement by statement
    (`StmtRelPartial`). -/
inductive BlockRelPartial : List (Stmt P (CmdExt P)) → List (Stmt P (CmdExt P)) → Prop where
  | nil : BlockRelPartial [] []
  | cons {s s' : Stmt P (CmdExt P)} {ss ss' : List (Stmt P (CmdExt P))} :
      StmtRelPartial s s' → BlockRelPartial ss ss' → BlockRelPartial (s :: ss) (s' :: ss')
end

mutual
/-- Every statement is itself with none of its loops eliminated. -/
theorem StmtRelPartial.refl : ∀ s : Stmt P (CmdExt P), StmtRelPartial s s
  | .cmd c => .cmd c
  | .exit l md => .exit l md
  | .typeDecl tc md => .typeDecl tc md
  | .block _ bss _ => .block (BlockRelPartial.refl bss)
  | .ite _ tss ess _ => .ite (BlockRelPartial.refl tss) (BlockRelPartial.refl ess)
  | .loop g m inv body md => .keep g m inv body md

/-- Every list is itself with none of its loops eliminated. -/
theorem BlockRelPartial.refl : ∀ ss : List (Stmt P (CmdExt P)), BlockRelPartial ss ss
  | [] => .nil
  | s :: ss => .cons (StmtRelPartial.refl s) (BlockRelPartial.refl ss)
end

omit [HasFvar P] [HasFvars P] [HasBoolOps P] in
/-- A list of havocs has no loop. -/
private theorem havocs_numLoops (M : List P.Ident) (md : MetaData P) :
    Block.numLoops
      (M.map fun n => Stmt.cmd (P := P) (HasHavoc.havoc (P := P) (CmdT := CmdExt P) n md)) =
      0 := by
  induction M with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, Block.numLoops, Stmt.numLoops, ih]

omit [HasFvar P] [HasFvars P] in
/-- The loops of the passive encoding of a loop are those of the list in place of its body. -/
private theorem _root_.Imperative.Stmt.numLoops_loopPassive (n : String) (g : ExprOrNondet P)
    (M : List P.Ident) (body' : List (Stmt P (CmdExt P))) (md : MetaData P) :
    Stmt.numLoops (Stmt.loopPassive n g M body' md) = Block.numLoops body' := by
  cases g <;>
    simp [Stmt.loopPassive, LoopElim.havocBlock, LoopElim.enterAssume, LoopElim.exitAssume,
      Stmt.numLoops, Block.numLoops, havocs_numLoops]

mutual
/-- A statement without loops is related only to itself. -/
private theorem StmtRelPartial.eq_of_numLoops {s s' : Stmt P (CmdExt P)} (h : StmtRelPartial s s')
    (hn : Stmt.numLoops s = 0) : s' = s := by
  match h with
  | .cmd _ | .exit _ _ | .typeDecl _ _ | .keep .. => rfl
  | .block hb =>
    simp only [Stmt.numLoops] at hn
    rw [hb.eq_of_numLoops hn]
  | .ite ht he =>
    simp only [Stmt.numLoops] at hn
    rw [ht.eq_of_numLoops (by omega), he.eq_of_numLoops (by omega)]
  | .loop .. => simp [Stmt.numLoops] at hn

/-- A list without loops is related only to itself. -/
private theorem BlockRelPartial.eq_of_numLoops {ss ss' : List (Stmt P (CmdExt P))}
    (h : BlockRelPartial ss ss') (hn : Block.numLoops ss = 0) : ss' = ss := by
  match h with
  | .nil => rfl
  | .cons hs hr =>
    simp only [Block.numLoops] at hn
    rw [hs.eq_of_numLoops (by omega), hr.eq_of_numLoops (by omega)]
end

/-- A list related to a concatenation is the concatenation of lists related to its parts. -/
private theorem BlockRelPartial.append_inv :
    ∀ {a b c : List (Stmt P (CmdExt P))}, BlockRelPartial (a ++ b) c →
      ∃ a' b', c = a' ++ b' ∧ BlockRelPartial a a' ∧ BlockRelPartial b b'
  | [], _, _, h => ⟨[], _, rfl, .nil, h⟩
  | _ :: _, _, _, .cons hs hr =>
    have ⟨a', b', h, ha, hb⟩ := BlockRelPartial.append_inv hr
    ⟨_ :: a', b', h ▸ rfl, .cons hs ha, hb⟩

/-- A statement related to the passive encoding of a loop is the passive encoding of a list
    related to the list in place of its body. -/
private theorem StmtRelPartial.loopPassive_inv {n : String} {g : ExprOrNondet P} {M : List P.Ident}
    {body : List (Stmt P (CmdExt P))} {md : MetaData P} {s' : Stmt P (CmdExt P)}
    (h : StmtRelPartial (Stmt.loopPassive n g M body md) s') :
    ∃ body', BlockRelPartial body body' ∧ s' = Stmt.loopPassive n g M body' md := by
  simp only [Stmt.loopPassive] at h ⊢
  cases h with
  | ite ht he =>
    cases he
    cases ht with
    | cons ha hr =>
      cases ha with
      | block hb =>
        obtain ⟨a', b', rfl, ha', hb'⟩ := hb.append_inv
        have hz : ∀ l : List (Stmt P (CmdExt P)), (l = LoopElim.enterAssume n g md ∨
            l = LoopElim.exitAssume n g md) → Block.numLoops l = 0 := by
          rintro l (rfl | rfl) <;> cases g <;>
            simp [LoopElim.enterAssume, LoopElim.exitAssume, Block.numLoops, Stmt.numLoops]
        have hhv : Stmt.numLoops (P := P) (C := CmdExt P) (LoopElim.havocBlock n M md) = 0 := by
          simp [LoopElim.havocBlock, Stmt.numLoops, havocs_numLoops]
        rw [ha'.eq_of_numLoops (by
            simp [Block.numLoops, hhv, hz _ (.inl rfl)]),
          hr.eq_of_numLoops (by
            simp [Block.numLoops, hhv, hz _ (.inr rfl)])]
        exact ⟨b', hb', rfl⟩

mutual
/-- Eliminating some loops of a statement and then some loops of the result eliminates some
    loops of the statement. -/
theorem StmtRelPartial.trans {a b c : Stmt P (CmdExt P)} (h₁ : StmtRelPartial a b)
    (h₂ : StmtRelPartial b c) : StmtRelPartial a c := by
  match h₁ with
  | .cmd _ => cases h₂; exact .cmd _
  | .exit _ _ => cases h₂; exact .exit _ _
  | .typeDecl _ _ => cases h₂; exact .typeDecl _ _
  | .block hb => cases h₂ with | block hb' => exact .block (hb.trans hb')
  | .ite ht he => cases h₂ with | ite ht' he' => exact .ite (ht.trans ht') (he.trans he')
  | .keep .. => exact h₂
  | .loop n hb hl =>
    obtain ⟨_, hb', rfl⟩ := h₂.loopPassive_inv
    exact .loop n (hb.trans hb') hl

/-- Eliminating some loops of a list and then some loops of the result eliminates some loops of
    the list. -/
theorem BlockRelPartial.trans {a b c : List (Stmt P (CmdExt P))} (h₁ : BlockRelPartial a b)
    (h₂ : BlockRelPartial b c) : BlockRelPartial a c := by
  match h₁ with
  | .nil => cases h₂; exact .nil
  | .cons hs hr => cases h₂ with | cons hs' hr' => exact .cons (hs.trans hs') (hr.trans hr')
end

mutual
/-- A statement with some loops eliminated into a statement without loops has all its loops
    eliminated. -/
theorem StmtRelPartial.stmtRel {s s' : Stmt P (CmdExt P)} (h : StmtRelPartial s s')
    (hn : Stmt.numLoops s' = 0) : StmtRel s s' := by
  match h with
  | .cmd c => exact .cmd c
  | .exit l md => exact .exit l md
  | .typeDecl tc md => exact .typeDecl tc md
  | .block hb => exact .block (hb.blockRel (by simpa [Stmt.numLoops] using hn))
  | .ite ht he =>
    simp only [Stmt.numLoops] at hn
    exact .ite (ht.blockRel (by omega)) (he.blockRel (by omega))
  | .keep .. => simp [Stmt.numLoops] at hn
  | .loop n hb hl =>
    rw [Stmt.numLoops_loopPassive] at hn
    exact .loop n (hb.blockRel hn) hl

/-- A list with some loops eliminated into a list without loops has all its loops
    eliminated. -/
theorem BlockRelPartial.blockRel {ss ss' : List (Stmt P (CmdExt P))} (h : BlockRelPartial ss ss')
    (hn : Block.numLoops ss' = 0) : BlockRel ss ss' := by
  match h with
  | .nil => exact .nil
  | .cons hs hr =>
    simp only [Block.numLoops] at hn
    exact .cons (hs.stmtRel (by omega)) (hr.blockRel (by omega))
end

end -- public section

end LoopElim
end Imperative

namespace Core.LoopElim

open Core Core.Logic Imperative Imperative.LoopElim

public section

/-! ## The Core pass

`removeLoop` replaces a loop without invariants and measure by its passive encoding
(`Stmt.loopPassive`) over its unchanged body, and nothing else, so a pass of
`runStmtsRec removeLoop` eliminates some loops of a list, and a pass of `runProgram removeLoop`
some loops of every procedure body (`runProgram_removeLoop`): those it visits, which have
not been visited by an earlier pass. -/

/-- What `removeLoop` returns on a statement `s`: for a loop without invariants and measure
    whose body exits to no label starting with `Core.loopElimPrefix`, its passive encoding over
    its unchanged body, numbered by some `n`; nothing when `s` is not a loop. -/
private theorem removeLoop_post (s : Statement) :
    Transform.Post (removeLoop s) fun
      | some ss => ∃ g bss md n, s = .loop g none [] bss md ∧
          (∀ l ∈ Block.labels bss, l.startsWith loopElimPrefix = Bool.false) ∧
          ss = [Stmt.loopPassive n g (Block.carriedVars bss) bss md]
      | none => ∀ g m inv bss md, s ≠ .loop g m inv bss md := by
  unfold removeLoop
  split
  · rename_i g m inv bss md
    dsimp only
    split
    · exact Transform.Post.bind (Q₁ := fun _ => False) Transform.Post.throw fun _ h => h.elim
    · rename_i hinv
      refine Transform.Post.bind (Transform.Post.true _) fun n _ => ?_
      split
      · exact Transform.Post.bind (Q₁ := fun _ => False) Transform.Post.throw fun _ h => h.elim
      · rename_i hl
        refine Transform.Post.bind (Transform.Post.true _) fun _ _ => Transform.Post.pure ?_
        simp only [Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem,
          Option.isSome_iff_exists, not_or, not_exists] at hinv
        obtain rfl : inv = [] := List.eq_nil_iff_forall_not_mem.2 hinv.1
        obtain rfl : m = none := Option.eq_none_iff_forall_ne_some.2 fun e h => hinv.2 e h
        refine ⟨g, bss, md, n, rfl, fun l hl' => ?_, ?_⟩
        · simpa using fun h => hl (List.any_eq_true.2 ⟨l, hl', h⟩)
        · cases g <;> simp [Stmt.loopPassive, LoopElim.havocBlock, LoopElim.enterAssume,
            LoopElim.exitAssume, Block.carriedVars]
  · rename_i hne
    exact Transform.Post.pure fun g m inv bss md h => hne g m inv bss md h

/-- What one pass of `runStmtsRec removeLoop` over `ss` returns, `r`: `ss` with some loops
    eliminated (`BlockRelPartial`), with fewer loops when `r` reports a change; and `ss` has no
    loop when `r` reports none. -/
private def PassPost (ss : List Statement) (r : Bool × List Statement) : Prop :=
  BlockRelPartial ss r.2 ∧ Block.numLoops r.2 ≤ Block.numLoops ss ∧
    (r.1 = Bool.true → Block.numLoops r.2 < Block.numLoops ss) ∧
    (r.1 = Bool.false → Block.numLoops ss = 0)

/-- One pass of `runStmtsRec removeLoop` over a list of size below `fuel` eliminates some of its
    loops (`BlockRelPartial`), lowering their number when it reports a change; it reports no
    change only on a list without loops. -/
private theorem runStmtsRec_removeLoop_aux : ∀ (fuel : Nat) (ss : List Statement),
    sizeOf ss < fuel → Transform.Post (Transform.runStmtsRec removeLoop ss) (PassPost ss)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, [], _ => by
    simp only [Transform.runStmtsRec]
    exact Transform.Post.pure ⟨.nil, Nat.le_refl _, by simp, fun _ => rfl⟩
  | fuel + 1, s :: rest, hsz => by
    have ih := runStmtsRec_removeLoop_aux fuel
    simp only [List.cons.sizeOf_spec] at hsz
    rw [Transform.runStmtsRec.eq_def]
    dsimp only
    refine Transform.Post.bind (Q₁ := fun r => ∃ s', r.2 = [s'] ∧ StmtRelPartial s s' ∧
        Stmt.numLoops s' ≤ Stmt.numLoops s ∧
        (r.1 = Bool.true → Stmt.numLoops s' < Stmt.numLoops s) ∧
        (r.1 = Bool.false → Stmt.numLoops s = 0)) ?_ fun r hr => ?_
    · refine Transform.Post.bind (removeLoop_post s) fun o ho => ?_
      cases o with
      | some ss =>
        obtain ⟨g, bss, md, n, rfl, hl, rfl⟩ := ho
        refine Transform.Post.pure ⟨_, rfl, .loop n (.refl bss) hl, ?_, fun _ => ?_, nofun⟩ <;>
          simp only [Stmt.numLoops, Stmt.numLoops_loopPassive] <;> omega
      | none =>
        cases s with
        | cmd c => exact Transform.Post.pure ⟨_, rfl, .cmd c, Nat.le_refl _, nofun, fun _ => rfl⟩
        | exit l md =>
          exact Transform.Post.pure ⟨_, rfl, .exit l md, Nat.le_refl _, nofun, fun _ => rfl⟩
        | typeDecl tc md =>
          exact Transform.Post.pure ⟨_, rfl, .typeDecl tc md, Nat.le_refl _, nofun, fun _ => rfl⟩
        | loop g m inv b md => exact absurd rfl (ho g m inv b md)
        | block l b md =>
          simp only [Stmt.block.sizeOf_spec] at hsz
          refine Transform.Post.bind (ih b (by omega)) fun r hb => Transform.Post.pure ?_
          exact ⟨_, rfl, .block hb.1, hb.2.1, hb.2.2.1, hb.2.2.2⟩
        | ite c t e md =>
          simp only [Stmt.ite.sizeOf_spec] at hsz
          refine Transform.Post.bind (ih t (by omega)) fun r ht => ?_
          refine Transform.Post.bind (ih e (by omega)) fun r' he => Transform.Post.pure ?_
          obtain ⟨ht, _, _, _⟩ := ht
          obtain ⟨he, _, _, _⟩ := he
          refine ⟨_, rfl, .ite ht he, ?_, fun h => ?_, fun h => ?_⟩
          · simp only [Stmt.numLoops]
            omega
          · simp only [Stmt.numLoops]
            cases h₁ : r.1 <;> cases h₂ : r'.1 <;> simp_all <;> omega
          · simp only [Stmt.numLoops]
            cases h₁ : r.1 <;> cases h₂ : r'.1 <;> simp_all
    · obtain ⟨s', hs', hs, h1, h2, h3⟩ := hr
      refine Transform.Post.bind (ih rest (by omega)) fun r' hr' => Transform.Post.pure ?_
      obtain ⟨hr, h1', h2', h3'⟩ := hr'
      refine ⟨hs' ▸ .cons hs hr, ?_, fun h => ?_, fun h => ?_⟩
      · simp only [hs', List.singleton_append, Block.numLoops]
        omega
      · simp only [hs', List.singleton_append, Block.numLoops]
        cases h₁ : r.1 <;> cases h₂ : r'.1 <;> simp_all <;> omega
      · simp only [Block.numLoops]
        cases h₁ : r.1 <;> cases h₂ : r'.1 <;> simp_all

/-- One pass of `runStmtsRec removeLoop` eliminates some loops of a list (`BlockRelPartial`),
    lowering their number when it reports a change; it reports no change only on a list without
    loops. -/
private theorem runStmtsRec_removeLoop (ss : List Statement) :
    Transform.Post (Transform.runStmtsRec removeLoop ss) (PassPost ss) :=
  runStmtsRec_removeLoop_aux _ ss (Nat.lt_succ_self _)

/-- `d'` is `d` with its procedure body, when it is a structured body `ss`, replaced by a list
    `ss'` with `R ss ss'`; every other declaration, a procedure with a CFG body included, is
    kept. -/
@[expose] def DeclBodyRel (R : Statements → Statements → Prop) : Decl → Decl → Prop
  | .proc proc md, d' => match proc.body with
    | .structured ss => ∃ ss', R ss ss' ∧ d' = .proc { proc with body := .structured ss' } md
    | .cfg _ => d' = .proc proc md
  | d, d' => d' = d

/-- A procedure with a structured body `ss` is related to the procedures with a body `ss'` such
    that `R ss ss'`. -/
private theorem declBodyRel_structured {R : Statements → Statements → Prop} {proc : Procedure}
    {md : MetaData Expression} {ss : Statements} (hb : proc.body = .structured ss) {d' : Decl} :
    DeclBodyRel R (.proc proc md) d' ↔
      ∃ ss', R ss ss' ∧ d' = .proc { proc with body := .structured ss' } md := by
  simp only [DeclBodyRel, hb]

/-- A procedure with a CFG body is related only to itself. -/
private theorem declBodyRel_cfg {R : Statements → Statements → Prop} {proc : Procedure}
    {md : MetaData Expression} {g : Imperative.DetCFG Expression Command} (hb : proc.body = .cfg g)
    {d' : Decl} : DeclBodyRel R (.proc proc md) d' ↔ d' = .proc proc md := by
  simp only [DeclBodyRel, hb]

/-- The number of loops in the structured procedure body of a declaration. -/
private def declNumLoops : Decl → Nat
  | .proc proc _ => match proc.body with
    | .structured ss => Block.numLoops ss
    | .cfg _ => 0
  | _ => 0

/-- The number of loops of a program is the sum of those of its declarations. -/
private theorem numLoops_eq_sum (p : Program) :
    numLoops p = (p.decls.map declNumLoops).sum := by
  unfold numLoops
  rw [← Nat.zero_add (List.sum _)]
  generalize 0 = k
  generalize p.decls = ds
  induction ds generalizing k with
  | nil => simp
  | cons d ds ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, ← Nat.add_assoc]
    congr 1
    cases d <;> simp only [declNumLoops, Nat.add_zero]
    split <;> rename_i h <;> simp [h]

/-- Every list is related to itself by `DeclBodyRel BlockRelPartial`. -/
private theorem declBodyRel_refl :
    ∀ ds : List Decl, List.Rel₂ (DeclBodyRel BlockRelPartial) ds ds
  | [] => .nil
  | d :: ds => .cons (by
      cases d
      case proc proc md =>
        cases hb : proc.body
        · exact (declBodyRel_structured hb).2 ⟨_, .refl _, by rw [← hb]⟩
        · exact (declBodyRel_cfg hb).2 rfl
      all_goals rfl) (declBodyRel_refl ds)

/-- After one pass of `runProgram removeLoop`, a declaration whose procedure body is that of
    `d₀` with some loops eliminated still is. -/
private theorem declBodyRel_declStep {d₀ d : Decl} {r : Bool × Decl}
    (h₁ : DeclBodyRel BlockRelPartial d₀ d) (h₂ : Transform.DeclStep PassPost d r) :
    DeclBodyRel BlockRelPartial d₀ r.2 := by
  cases d₀
  case proc proc₀ md₀ =>
    cases hb : proc₀.body
    · rw [declBodyRel_structured hb] at h₁ ⊢
      obtain ⟨ss₁, hrel, rfl⟩ := h₁
      obtain ⟨ss, ss', hss, hq, hr⟩ := h₂
      obtain rfl : ss₁ = ss := Body.structured.inj hss
      obtain ⟨c, d'⟩ := r
      cases c
      · exact ⟨ss₁, hrel, hr⟩
      · exact ⟨ss', hrel.trans hq.1, hr⟩
    · -- `runProgram` rejects a CFG body.
      rw [declBodyRel_cfg hb] at h₁
      subst h₁
      obtain ⟨ss, -, hss, -⟩ := h₂
      rw [hb] at hss
      cases hss
  all_goals
    obtain rfl := h₁
    obtain rfl := h₂
    rfl

/-- One pass of `runProgram removeLoop` does not add loops to a declaration, removes some when
    it reports a change, and leaves a declaration without loops when it reports none. -/
private theorem declStep_numLoops {d : Decl} {r : Bool × Decl}
    (h : Transform.DeclStep PassPost d r) :
    declNumLoops r.2 ≤ declNumLoops d ∧ (r.1 = Bool.true → declNumLoops r.2 < declNumLoops d) ∧
      (r.1 = Bool.false → declNumLoops r.2 = 0) := by
  cases d
  case proc proc md =>
    obtain ⟨ss, ss', hb, hq, hr⟩ := h
    obtain ⟨c, d'⟩ := r
    cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at hr <;> subst hr <;>
      simp only [declNumLoops, hb]
    · exact ⟨Nat.le_refl _, nofun, fun _ => hq.2.2.2 rfl⟩
    · exact ⟨Nat.le_of_lt (hq.2.2.1 rfl), fun _ => hq.2.2.1 rfl, nofun⟩
  all_goals
    obtain rfl := h
    simp [declNumLoops]

/-- One pass of `runProgram removeLoop` keeps the procedure bodies those of `ds₀` with some
    loops eliminated, does not add loops, removes some when it reports a change, and leaves no
    loop when it reports none. -/
private theorem rel₂_declStep {ds₀ ds : List Decl} {rs : List (Bool × Decl)}
    (h₁ : List.Rel₂ (DeclBodyRel BlockRelPartial) ds₀ ds)
    (h₂ : List.Rel₂ (Transform.DeclStep PassPost) ds rs) :
    List.Rel₂ (DeclBodyRel BlockRelPartial) ds₀ (rs.map (·.2)) ∧
      ((rs.map (·.2)).map declNumLoops).sum ≤ (ds.map declNumLoops).sum ∧
      (rs.any (·.1) = Bool.true →
        ((rs.map (·.2)).map declNumLoops).sum < (ds.map declNumLoops).sum) ∧
      (rs.any (·.1) = Bool.false → ((rs.map (·.2)).map declNumLoops).sum = 0) := by
  induction h₁ generalizing rs with
  | nil => cases h₂; exact ⟨.nil, by simp, by simp, by simp⟩
  | cons hd _ ih =>
    cases h₂ with
    | cons hd₂ hs₂ =>
      obtain ⟨hr, hle, hlt, hz⟩ := ih hs₂
      obtain ⟨hle', hlt', hz'⟩ := declStep_numLoops hd₂
      refine ⟨.cons (declBodyRel_declStep hd hd₂) hr, ?_, fun h => ?_, fun h => ?_⟩
      · simp only [List.map_cons, List.sum_cons]
        omega
      · simp only [List.map_cons, List.sum_cons, List.any_cons, Bool.or_eq_true] at h ⊢
        rcases h with h | h
        · have := hlt' h
          omega
        · have := hlt h
          omega
      · simp only [List.map_cons, List.sum_cons, List.any_cons, Bool.or_eq_false_iff] at h ⊢
        have := hz' h.1
        have := hz h.2
        omega

/-- One pass of `runProgram removeLoop` over a program `q` whose procedure bodies are those of
    `p` with some loops eliminated returns such a program, with fewer loops than `q` when it
    reports a change and without loops when it reports none. -/
theorem runProgram_removeLoop {p q : Program}
    (hq : List.Rel₂ (DeclBodyRel BlockRelPartial) p.decls q.decls) :
    Transform.Post (Transform.runProgram removeLoop q) fun r =>
      List.Rel₂ (DeclBodyRel BlockRelPartial) p.decls r.2.decls ∧
      (r.1 = Bool.true → numLoops r.2 < numLoops q) ∧
      (r.1 = Bool.false → numLoops r.2 = 0) :=
  (Transform.runProgram_post runStmtsRec_removeLoop q).mono fun r ⟨rs, hrs, hdecls, hc⟩ => by
    obtain ⟨hrel, -, hlt, hz⟩ := rel₂_declStep hq hrs
    rw [numLoops_eq_sum, numLoops_eq_sum, hdecls, hc]
    exact ⟨hrel, hlt, hz⟩

/-- A program whose procedure bodies are those of `p` with some loops eliminated, and which has
    no loop, has the procedure bodies of `p` with all their loops eliminated. -/
theorem declBodyRel_blockRel {p p' : Program}
    (h : List.Rel₂ (DeclBodyRel BlockRelPartial) p.decls p'.decls) (hn : numLoops p' = 0) :
    List.Rel₂ (DeclBodyRel BlockRel) p.decls p'.decls := by
  rw [numLoops_eq_sum] at hn
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
      · rw [declBodyRel_structured hb] at hd ⊢
        obtain ⟨ss', hrel, rfl⟩ := hd
        exact ⟨ss', hrel.blockRel (by simp only [declNumLoops] at hn; omega), rfl⟩
      · rw [declBodyRel_cfg hb] at hd ⊢
        exact hd
    all_goals exact hd

/-- **The Core pass eliminates loops as `Block.loopElim` does, up to loop numbers.**  When
    `Core.loopElim p` succeeds with `p'`, `p'` has the declarations of `p` in order, except that
    a procedure with a structured body `ss` gets a body `ss'` that is `ss` with every loop
    replaced by its passive encoding (`BlockRel ss ss'`).  Each pass of the Core pass eliminates
    the outermost loops it has not eliminated yet, so after at most `Core.numLoops p + 1`
    passes, the bound `Core.loopElim` iterates to, no loop is left. -/
theorem loopElim_blockRel {p p' : Program} {c : Bool} {σ σ' : Transform.CoreTransformState}
    (h : loopElim p σ = (.ok (c, p'), σ')) :
    List.Rel₂ (fun d d' => match d with
      | .proc proc md => match proc.body with
        | .structured ss =>
          ∃ ss', BlockRel ss ss' ∧ d' = .proc { proc with body := .structured ss' } md
        | .cfg _ => d' = d
      | _ => d' = d) p.decls p'.decls :=
  have ⟨hrel, hn⟩ := Transform.runProgramUntil_post (fun _ hq => runProgram_removeLoop hq)
    (declBodyRel_refl p.decls) (Nat.lt_succ_self (numLoops p)) σ _ σ' h
  (declBodyRel_blockRel hrel hn).imp fun d _ h => by
    cases d
    case proc proc md => cases hb : proc.body <;> simpa [DeclBodyRel, hb] using h
    all_goals exact h

/-- When `Core.loopElim p` succeeds with `p'`, a procedure of `p` with a structured body `ss` has,
    at its position in `p'`, a body `ss'` that is `ss` with its loops eliminated. -/
theorem loopElim_body_blockRel {p p' : Program} {c : Bool}
    {σ σ' : Transform.CoreTransformState} (h : loopElim p σ = (.ok (c, p'), σ'))
    {i : Nat} {proc : Procedure} {md : MetaData Expression} {ss : Statements}
    (hproc : p.decls[i]? = some (.proc proc md)) (hbody : proc.body = .structured ss) :
    ∃ ss', p'.decls[i]? = some (.proc { proc with body := .structured ss' } md) ∧
      BlockRel ss ss' := by
  obtain ⟨d', hd', hrel⟩ := (loopElim_blockRel h).getElem?_some hproc
  simp only [hbody] at hrel
  obtain ⟨ss', hrel, rfl⟩ := hrel
  exact ⟨ss', hd', hrel⟩

/-- The `exit` targets of a list satisfying the gate at parameters reserving
    `Core.loopElimPrefix` do not start with it. -/
private theorem labels_not_startsWith_of_gate {params : InitEnvWFParams} {ss : Statements}
    {ρ : Env Expression}
    (hwf : BlockInitEnvWF (params.extendBlockLabels [Core.loopElimPrefix]) ss ρ) :
    ∀ l ∈ Block.labels ss, l.startsWith Core.loopElimPrefix = Bool.false := by
  intro l hl
  cases hs : l.startsWith Core.loopElimPrefix
  · rfl
  · exact absurd (List.isPrefixOf_iff_prefix.mpr ((String.startsWith_string_iff ..).mp hs))
      (hwf.exitsNotReserved l hl _ (List.mem_cons_self ..))

/-- The pure pass eliminates the loops of a list satisfying the gate at parameters reserving
    `Core.loopElimPrefix` for block labels. -/
theorem blockRel_of_loopElim {params : InitEnvWFParams} {ss ss' : Statements}
    {ρ : Env Expression} (ht : Imperative.Block.loopElim ss = some ss')
    (hwf : BlockInitEnvWF (params.extendBlockLabels [Core.loopElimPrefix]) ss ρ) :
    BlockRel ss ss' :=
  Imperative.Block.loopElim_rel ht (labels_not_startsWith_of_gate hwf)

/-- Sending `ss` to `ss'` and rejecting every other list eliminates the loops of its input,
    from the entries where `ss'` is `ss` with its loops eliminated. -/
theorem single_blockRel {params : InitEnvWFParams} {L : List String} {ss ss' : Statements}
    (hrel : ∀ ρ, BlockInitEnvWF (params.extendBlockLabels L) ss ρ → BlockRel ss ss') :
    ∀ s s'' ρ, (if s = ss then some ss' else none) = some s'' →
      BlockInitEnvWF (params.extendBlockLabels L) s ρ → BlockRel s s'' := by
  intro s s'' ρ h hwf
  split at h
  · rename_i hs
    subst hs
    cases h
    exact hrel ρ hwf
  · cases h

/-- A list with the loops of `ss` eliminated satisfies the initial-environment gate
    `BlockInitEnvWF` at `params` wherever `ss` satisfies it at `params` with any block-label
    prefixes `L` reserved. -/
theorem blockInitEnvWF_of_blockRel {params : InitEnvWFParams} {L : List String}
    {ss ss' : Statements} {ρ : Env Expression} (hrel : BlockRel ss ss')
    (hwf : BlockInitEnvWF (params.extendBlockLabels L) ss ρ) :
    BlockInitEnvWF params ss' ρ := by
  have hnotOps : ∀ g : Expression.Expr, ∀ o ∈ HasOps.getOps (HasBoolOps.not g),
      o ∈ HasOps.getOps g ∨ params.declaredFuncs o = Bool.true := fun g o ho =>
    (Core.not_getOps g o ho).imp_right fun h => by
      subst h
      exact hwf.factoryDeclared _ boolNot_isNameInFactory
  have hdu' := hrel.defUseWellFormed Core.not_getFvars hnotOps hwf.defUseOk
  exact { hwf with
    readWritesDefined := fun _ hn hnd =>
      Imperative.Block.defined_of_mem_touchedVars (fun _ _ h => h) hdu' hn hnd
    defsUndefined := fun n hn => hwf.defsUndefined n ((hrel.mem_definedVars false n).1 hn)
    definedVarsNotReserved := fun n hn =>
      hwf.definedVarsNotReserved n ((hrel.mem_definedVars false n).1 hn)
    exitsNotReserved := fun l hl p hp =>
      hwf.exitsNotReserved l (hrel.labels ▸ hl) p (List.mem_append_right _ hp)
    defUseOk := hdu'
    initTypesInhabited := fun ty hty => hwf.initTypesInhabited ty (hrel.initTypes ty hty)
    fvarTypesOk := by
      obtain ⟨Γ, hσ, hw⟩ := hwf.fvarTypesOk
      exact ⟨Γ, hσ, hrel.fvarTypesWellAnnotated Core.not_getTypedFvars hw⟩ }

end -- public section

end Core.LoopElim
