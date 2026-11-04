/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtExtendCallBridge
public import Strata.DL.Imperative.StmtCFGCallSemantics
public import Strata.DL.Imperative.StmtProps
public import Strata.DL.Imperative.StmtSemanticsProps
import Strata.Util.RelationsProps

/-! # Properties of the call-free bridge between extended and base Imperative syntax

Correspondence properties, generic over any expression language `P`, for
embedding and projecting between extended (`CmdExt P`) and base (`Cmd P`)
Imperative syntax (defined in `Strata.DL.Imperative.StmtExtendCallBridge`).

* The embedding is structure-determining (inversion lemmas), projection is a
  two-sided inverse on the call-free fragment (round trips), each embedding is
  injective.
* Statement and CFG analyses commute with embedding.
* The native event-trace semantics agree across the bridge, step-for-step and
  trace-for-trace (`stepStarE_embed_iff`, the projection corollary
  `noCalls_stmts_stepStarE_iff`).

## Why these facts live in a dedicated Props module

Every theorem below mentions a bridge definition (`embedStmt`, `embedConfig`,
`projectStmts`, …), so none of them is a statement about `Stmt`/`Config`/`CFG`
alone.  Pushing a bridge-dependent fact down into `StmtProps` or
`StmtSemanticsProps` would force those modules to import the bridge and thereby
invert the dependency (the bridge is built *on top of* the statement layer).  A
genuinely bridge-independent generic fact belongs in those modules instead; none
is introduced here.  The dialect-specific residue that additionally mentions a
concrete call predicate (`isNotCall` / `noCalls`) or a dialect's init-environment
well-formedness lives in the dialect's own bridge-props module, importing and
reusing the generic facts below. -/

public section

namespace Imperative

variable {P : PureExpr}

/-! ## Inversion of the embedding

The embedding is structure-determining: the shape of an embedded statement or
configuration forces the shape of its base preimage.  These lemmas invert a
single layer of `embedStmt` / `embedConfig`. -/

/-- An embedded statement that is a `.cmd` comes from a base `.cmd`, whose
command the extended command wraps with `CmdExt.cmd`. -/
theorem embedStmt_eq_cmd {s : Stmt P (Cmd P)} {c : CmdExt P}
    (h : embedStmt s = .cmd c) : ∃ b, s = .cmd b ∧ c = CmdExt.cmd b := by
  cases s <;> simp only [embedStmt, Stmt.cmd.injEq, reduceCtorEq] at h
  exact ⟨_, rfl, h.symm⟩

/-- An embedded statement that is a `.block` comes from a base `.block` with the
same label and metadata whose body embeds to the given statements. -/
theorem embedStmt_eq_block {s : Stmt P (Cmd P)} {label ss md}
    (h : embedStmt s = .block label ss md) :
    ∃ ssb, s = .block label ssb md ∧ embedStmts ssb = ss := by
  cases s <;> simp only [embedStmt, Stmt.block.injEq, reduceCtorEq] at h
  obtain ⟨rfl, hss, rfl⟩ := h
  exact ⟨_, rfl, hss⟩

/-- An embedded statement that is an `.ite` comes from a base `.ite` with the
same condition and metadata whose branches embed to the given statements. -/
theorem embedStmt_eq_ite {s : Stmt P (Cmd P)} {cond tss ess md}
    (h : embedStmt s = .ite cond tss ess md) :
    ∃ tssb essb, s = .ite cond tssb essb md ∧
      embedStmts tssb = tss ∧ embedStmts essb = ess := by
  cases s <;> simp only [embedStmt, Stmt.ite.injEq, reduceCtorEq] at h
  obtain ⟨rfl, htss, hess, rfl⟩ := h
  exact ⟨_, _, rfl, htss, hess⟩

/-- An embedded statement that is a `.loop` comes from a base `.loop` with the
same guard, measure, invariant, and metadata whose body embeds to the given
statements. -/
theorem embedStmt_eq_loop {s : Stmt P (Cmd P)} {guard measure invariant body md}
    (h : embedStmt s = .loop guard measure invariant body md) :
    ∃ bodyb, s = .loop guard measure invariant bodyb md ∧ embedStmts bodyb = body := by
  cases s <;> simp only [embedStmt, Stmt.loop.injEq, reduceCtorEq] at h
  obtain ⟨rfl, rfl, rfl, hbody, rfl⟩ := h
  exact ⟨_, rfl, hbody⟩

/-- An embedded statement that is an `.exit` comes from the identical base
`.exit`. -/
theorem embedStmt_eq_exit {s : Stmt P (Cmd P)} {label md}
    (h : embedStmt s = .exit label md) : s = .exit label md := by
  cases s <;> simp_all only [embedStmt, Stmt.exit.injEq, reduceCtorEq]

/-- An embedded statement that is a `.typeDecl` comes from the identical base
`.typeDecl`. -/
theorem embedStmt_eq_typeDecl {s : Stmt P (Cmd P)} {tc md}
    (h : embedStmt s = .typeDecl tc md) : s = .typeDecl tc md := by
  cases s <;> simp_all only [embedStmt, Stmt.typeDecl.injEq, reduceCtorEq]

/-- A base statement list whose embedding is empty is itself empty. -/
theorem embedStmts_eq_nil {ss : List (Stmt P (Cmd P))}
    (h : embedStmts ss = []) : ss = [] := by
  cases ss <;> simp_all only [embedStmts, reduceCtorEq]

/-- A base statement list whose embedding is a cons comes from a cons whose head
embeds to the head statement and whose tail embeds to the remaining statements. -/
theorem embedStmts_eq_cons {ss : List (Stmt P (Cmd P))} {t : Stmt P (CmdExt P)}
    {rest : List (Stmt P (CmdExt P))}
    (h : embedStmts ss = t :: rest) :
    ∃ sb ssb, ss = sb :: ssb ∧ embedStmt sb = t ∧ embedStmts ssb = rest := by
  cases ss <;> simp only [embedStmts, List.cons.injEq, reduceCtorEq] at h
  obtain ⟨ht, hrest⟩ := h
  exact ⟨_, _, rfl, ht, hrest⟩

/-- An embedded configuration that is a `.stmt` comes from a base `.stmt` at the
same environment whose statement embeds to the given one. -/
theorem embedConfig_eq_stmt {c : Config P (Cmd P)} {s ρ}
    (h : embedConfig c = .stmt s ρ) : ∃ sb, c = .stmt sb ρ ∧ embedStmt sb = s := by
  cases c <;> simp only [embedConfig, Config.stmt.injEq, reduceCtorEq] at h
  obtain ⟨hs, rfl⟩ := h
  exact ⟨_, rfl, hs⟩

/-- An embedded configuration that is a `.stmts` comes from a base `.stmts` at
the same environment whose statements embed to the given ones. -/
theorem embedConfig_eq_stmts {c : Config P (Cmd P)} {ss ρ}
    (h : embedConfig c = .stmts ss ρ) :
    ∃ ssb, c = .stmts ssb ρ ∧ embedStmts ssb = ss := by
  cases c <;> simp only [embedConfig, Config.stmts.injEq, reduceCtorEq] at h
  obtain ⟨hss, rfl⟩ := h
  exact ⟨_, rfl, hss⟩

/-- An embedded configuration that is `.terminal` comes from the identical base
`.terminal`. -/
theorem embedConfig_eq_terminal {c : Config P (Cmd P)} {ρ}
    (h : embedConfig c = .terminal ρ) : c = .terminal ρ := by
  cases c <;> simp_all only [embedConfig, Config.terminal.injEq, reduceCtorEq]

/-- An embedded configuration that is `.exiting` comes from the identical base
`.exiting`. -/
theorem embedConfig_eq_exiting {c : Config P (Cmd P)} {label ρ}
    (h : embedConfig c = .exiting label ρ) : c = .exiting label ρ := by
  cases c <;> simp_all only [embedConfig, Config.exiting.injEq, reduceCtorEq]

/-- An embedded configuration that is a `.block` comes from a base `.block` with
the same label and store whose inner configuration embeds to the given one. -/
theorem embedConfig_eq_block {c : Config P (Cmd P)} {label σ inner}
    (h : embedConfig c = .block label σ inner) :
    ∃ cinner, c = .block label σ cinner ∧ embedConfig cinner = inner := by
  cases c <;> simp only [embedConfig, Config.block.injEq, reduceCtorEq] at h
  obtain ⟨rfl, rfl, hinner⟩ := h
  exact ⟨_, rfl, hinner⟩

/-- An embedded configuration that is a `.seq` comes from a base `.seq` whose
inner configuration and continuation embed to the given ones. -/
theorem embedConfig_eq_seq {c : Config P (Cmd P)} {inner ss}
    (h : embedConfig c = .seq inner ss) :
    ∃ cinner ssb, c = .seq cinner ssb ∧ embedConfig cinner = inner ∧ embedStmts ssb = ss := by
  cases c <;> simp only [embedConfig, Config.seq.injEq, reduceCtorEq] at h
  obtain ⟨hinner, hss⟩ := h
  exact ⟨_, _, rfl, hinner, hss⟩

/-! ## Round trips: projecting an embedding -/

mutual
/-- Projecting an embedded base statement recovers it. -/
theorem projectStmt_embedStmt (s : Stmt P (Cmd P)) : projectStmt (embedStmt s) = some s := by
  cases s with
  | cmd c => simp [embedStmt, projectStmt, projectCommand]
  | block label ss md => simp [embedStmt, projectStmt, projectStmts_embedStmts ss]
  | ite cond tss ess md =>
      simp [embedStmt, projectStmt, projectStmts_embedStmts tss, projectStmts_embedStmts ess]
  | loop guard measure invariant body md =>
      simp [embedStmt, projectStmt, projectStmts_embedStmts body]
  | exit label md => simp [embedStmt, projectStmt]
  | typeDecl tc md => simp [embedStmt, projectStmt]

/-- Projecting an embedded base statement list recovers it. -/
theorem projectStmts_embedStmts (ss : List (Stmt P (Cmd P))) :
    projectStmts (embedStmts ss) = some ss := by
  cases ss with
  | nil => simp [embedStmts, projectStmts]
  | cons s rest =>
      simp [embedStmts, projectStmts, projectStmt_embedStmt s, projectStmts_embedStmts rest]
end

/-! ## Injectivity of the embedding

Each embedding has its projection as a left inverse, so it is injective. -/

/-- `embedStmt` is injective. -/
theorem embedStmt_injective {s t : Stmt P (Cmd P)} (h : embedStmt s = embedStmt t) : s = t := by
  have hproject := projectStmt_embedStmt s
  rw [h, projectStmt_embedStmt t] at hproject
  exact (Option.some.inj hproject).symm

/-- `embedStmts` is injective. -/
theorem embedStmts_injective {ss ts : List (Stmt P (Cmd P))}
    (h : embedStmts ss = embedStmts ts) : ss = ts := by
  have hproject := projectStmts_embedStmts ss
  rw [h, projectStmts_embedStmts ts] at hproject
  exact (Option.some.inj hproject).symm

/-- `embedConfig` is injective. -/
theorem embedConfig_injective {c d : Config P (Cmd P)}
    (h : embedConfig c = embedConfig d) : c = d := by
  induction c generalizing d with
  | stmt s ρ =>
      obtain ⟨sb, hd, hs⟩ := embedConfig_eq_stmt h.symm
      subst hd; simp [embedStmt_injective hs.symm]
  | stmts ss ρ =>
      obtain ⟨ssb, hd, hs⟩ := embedConfig_eq_stmts h.symm
      subst hd; simp [embedStmts_injective hs.symm]
  | terminal ρ => simp [embedConfig_eq_terminal h.symm]
  | exiting label ρ => simp [embedConfig_eq_exiting h.symm]
  | block label σ inner ih =>
      obtain ⟨cinner, hd, hc⟩ := embedConfig_eq_block h.symm
      subst hd; simp [ih hc.symm]
  | seq inner ss ih =>
      obtain ⟨cinner, ssb, hd, hc, hss⟩ := embedConfig_eq_seq h.symm
      subst hd; simp [ih hc.symm, embedStmts_injective hss.symm]

/-! ## Re-embedding successful projections -/
mutual
/-- If an extended statement projects successfully, embedding the result recovers
the extended statement: embedding is a left inverse of projection on its domain. -/
theorem embedStmt_projectStmt {s : Stmt P (CmdExt P)} {b : Stmt P (Cmd P)}
    (h : projectStmt s = some b) : embedStmt b = s := by
  cases s with
  | cmd c =>
      cases c with
      | cmd cc =>
          simp only [projectStmt, projectCommand, Option.map_some, Option.some.injEq] at h
          subst h; simp [embedStmt]
      | call procName args md => simp [projectStmt, projectCommand] at h
  | block label ss md =>
      simp only [projectStmt, Option.map_eq_some_iff] at h
      obtain ⟨ss', hss, hb⟩ := h
      subst hb; simp [embedStmt, embedStmts_projectStmts hss]
  | ite cond tss ess md =>
      simp only [projectStmt] at h
      cases htss : projectStmts tss with
      | none => simp only [htss, reduceCtorEq] at h
      | some tss' =>
          cases hess : projectStmts ess with
          | none => simp only [htss, hess, reduceCtorEq] at h
          | some ess' =>
              simp only [htss, hess, Option.some.injEq] at h
              subst h
              simp [embedStmt, embedStmts_projectStmts htss, embedStmts_projectStmts hess]
  | loop guard measure invariant body md =>
      simp only [projectStmt, Option.map_eq_some_iff] at h
      obtain ⟨body', hbody, hb⟩ := h
      subst hb; simp [embedStmt, embedStmts_projectStmts hbody]
  | exit label md =>
      simp only [projectStmt, Option.some.injEq] at h; subst h; rfl
  | typeDecl tc md =>
      simp only [projectStmt, Option.some.injEq] at h; subst h; rfl

/-- If an extended statement list projects successfully, embedding the result
recovers the extended list. -/
theorem embedStmts_projectStmts {ss : List (Stmt P (CmdExt P))} {bs : List (Stmt P (Cmd P))}
    (h : projectStmts ss = some bs) : embedStmts bs = ss := by
  cases ss with
  | nil => simp only [projectStmts, Option.some.injEq] at h; subst h; rfl
  | cons s rest =>
      simp only [projectStmts] at h
      cases hs : projectStmt s with
      | none => simp only [hs, reduceCtorEq] at h
      | some s' =>
          cases hrest : projectStmts rest with
          | none => simp only [hs, hrest, reduceCtorEq] at h
          | some rest' =>
              simp only [hs, hrest, Option.some.injEq] at h
              subst h
              simp [embedStmts, embedStmt_projectStmt hs, embedStmts_projectStmts hrest]
end

/-! ## Command-level agreement of the embedding

Each command analysis reduces, on an embedded command `embedCommand c =
CmdExt.cmd c`, to the corresponding base-command analysis.  The `HasVarsImp` /
`HasOpsImp` / `HasInitTypesImp` instances of `CmdExt` all dispatch on the `.cmd`
constructor, so each of these holds definitionally. -/

/-- `definedVars` of an embedded command rewrites to `definedVars` of the base
command. -/
@[simp] theorem embedCommand_definedVars (c : Cmd P) :
    CmdExt.definedVars (embedCommand c) = Cmd.definedVars c := rfl

/-- `modifiedVars` of an embedded command rewrites to `modifiedVars` of the base
command. -/
@[simp] theorem embedCommand_modifiedVars (c : Cmd P) :
    CmdExt.modifiedVars (embedCommand c) = Cmd.modifiedVars c := rfl

/-- `initTypes` of an embedded command rewrites to `initTypes` of the base
command. -/
@[simp] theorem embedCommand_initTypes (c : Cmd P) :
    CmdExt.initTypes (embedCommand c) = Cmd.initTypes c := rfl

section AnalysisVars

variable [HasFvar P] [HasFvars P]

/-- `readVars` of an embedded command rewrites to `getVars` of the base command. -/
@[simp] theorem embedCommand_readVars (c : Cmd P) :
    CmdExt.readVars (embedCommand c) = Cmd.getVars c := rfl

/-! ## Analysis commutation with `embedStmts`

Each lemma states that running a base analysis on `embedStmts bs` (at the
extended command type) yields the same result as running it on `bs` (at the base
command type).  Each is proved by the obvious mutual structural recursion
mirroring `embedStmt` / `embedStmts`; the `.cmd` leaf closes by the command-level
agreement above, and the remaining constructors recurse on their sub-blocks
(the guard/measure/invariant expressions are command-independent and carried
verbatim by the embedding). -/

mutual
/-- `definedVars` commutes with the embedding on a statement: the embedded
statement has the same defined variables as the base statement. -/
theorem embedStmt_definedVars (s : Stmt P (Cmd P)) (flag : Bool) :
    Stmt.definedVars (C := CmdExt P) (embedStmt s) flag
      = Stmt.definedVars (C := Cmd P) s flag := by
  match s with
  | .cmd c => rfl
  | .block lbl ss md =>
      simp only [embedStmt, Stmt.definedVars]
      split
      · rfl
      · exact embedStmts_definedVars ss flag
  | .ite cond tss ess md =>
      simp only [embedStmt, Stmt.definedVars]
      split
      · rfl
      · rw [embedStmts_definedVars tss flag, embedStmts_definedVars ess flag]
  | .loop g m inv body md =>
      simp only [embedStmt, Stmt.definedVars]
      split
      · rfl
      · exact embedStmts_definedVars body flag
  | .exit lbl md => rfl
  | .typeDecl t md => rfl
  termination_by sizeOf s

/-- `definedVars` commutes with the embedding on a statement list. -/
theorem embedStmts_definedVars (ss : List (Stmt P (Cmd P))) (flag : Bool) :
    Block.definedVars (C := CmdExt P) (embedStmts ss) flag
      = Block.definedVars (C := Cmd P) ss flag := by
  match ss with
  | [] => rfl
  | s :: rest =>
      simp only [embedStmts, Block.definedVars]
      rw [embedStmt_definedVars s flag, embedStmts_definedVars rest flag]
  termination_by sizeOf ss
end

mutual
/-- `modifiedVars` commutes with the embedding on a statement. -/
theorem embedStmt_modifiedVars (s : Stmt P (Cmd P)) :
    Stmt.modifiedVars (C := CmdExt P) (embedStmt s)
      = Stmt.modifiedVars (C := Cmd P) s := by
  match s with
  | .cmd c => rfl
  | .block lbl ss md =>
      simp only [embedStmt, Stmt.modifiedVars]; exact embedStmts_modifiedVars ss
  | .ite cond tss ess md =>
      simp only [embedStmt, Stmt.modifiedVars]
      rw [embedStmts_modifiedVars tss, embedStmts_modifiedVars ess]
  | .loop g m inv body md =>
      simp only [embedStmt, Stmt.modifiedVars]; exact embedStmts_modifiedVars body
  | .exit lbl md => rfl
  | .typeDecl t md => rfl
  termination_by sizeOf s

/-- `modifiedVars` commutes with the embedding on a statement list. -/
theorem embedStmts_modifiedVars (ss : List (Stmt P (Cmd P))) :
    Block.modifiedVars (C := CmdExt P) (embedStmts ss)
      = Block.modifiedVars (C := Cmd P) ss := by
  match ss with
  | [] => rfl
  | s :: rest =>
      simp only [embedStmts, Block.modifiedVars]
      rw [embedStmt_modifiedVars s, embedStmts_modifiedVars rest]
  termination_by sizeOf ss
end

mutual
/-- `getVars` commutes with the embedding on a statement. -/
theorem embedStmt_getVars (s : Stmt P (Cmd P)) :
    Stmt.getVars (C := CmdExt P) (embedStmt s)
      = Stmt.getVars (C := Cmd P) s := by
  match s with
  | .cmd c => rfl
  | .block lbl ss md =>
      simp only [embedStmt, Stmt.getVars]; exact embedStmts_getVars ss
  | .ite cond tss ess md =>
      simp only [embedStmt, Stmt.getVars]
      rw [embedStmts_getVars tss, embedStmts_getVars ess]
  | .loop g m inv body md =>
      simp only [embedStmt, Stmt.getVars]
      rw [embedStmts_getVars body]
  | .exit lbl md => rfl
  | .typeDecl t md => rfl
  termination_by sizeOf s

/-- `getVars` commutes with the embedding on a statement list. -/
theorem embedStmts_getVars (ss : List (Stmt P (Cmd P))) :
    Block.getVars (C := CmdExt P) (embedStmts ss)
      = Block.getVars (C := Cmd P) ss := by
  match ss with
  | [] => rfl
  | s :: rest =>
      simp only [embedStmts, Block.getVars]
      rw [embedStmt_getVars s, embedStmts_getVars rest]
  termination_by sizeOf ss
end

omit [HasFvar P] [HasFvars P] in
mutual
/-- `initTypes` commutes with the embedding on a statement. -/
theorem embedStmt_initTypes (s : Stmt P (Cmd P)) :
    Stmt.initTypes (C := CmdExt P) (embedStmt s)
      = Stmt.initTypes (C := Cmd P) s := by
  match s with
  | .cmd c => rfl
  | .block lbl ss md =>
      simp only [embedStmt, Stmt.initTypes]; exact embedStmts_initTypes ss
  | .ite cond tss ess md =>
      simp only [embedStmt, Stmt.initTypes]
      rw [embedStmts_initTypes tss, embedStmts_initTypes ess]
  | .loop g m inv body md =>
      simp only [embedStmt, Stmt.initTypes]; exact embedStmts_initTypes body
  | .exit lbl md => rfl
  | .typeDecl t md => rfl
  termination_by sizeOf s

/-- `initTypes` commutes with the embedding on a statement list. -/
theorem embedStmts_initTypes (ss : List (Stmt P (Cmd P))) :
    Block.initTypes (C := CmdExt P) (embedStmts ss)
      = Block.initTypes (C := Cmd P) ss := by
  match ss with
  | [] => rfl
  | s :: rest =>
      simp only [embedStmts, Block.initTypes]
      rw [embedStmt_initTypes s, embedStmts_initTypes rest]
  termination_by sizeOf ss
end

/-! ## Structural analysis commutation with `embedStmts`

The pass-facing shape analyses below inspect statement structure and, for init
analyses, the command type's `HasVarsImp` instance.  Therefore they commute with
the generic call-free embedding just like the variable analyses above. -/

mutual
/-- Loop-body-init analysis is unchanged by command embedding. -/
theorem embedStmt_loopBodyNoInits (s : Stmt P (Cmd P)) :
    Stmt.loopBodyNoInits (embedStmt s) = Stmt.loopBodyNoInits s := by
  match s with
  | .cmd c => simp [embedStmt, Stmt.loopBodyNoInits]
  | .block label ss md =>
      simp only [embedStmt, Stmt.loopBodyNoInits]
      exact embedStmts_loopBodyNoInits ss
  | .ite cond tss ess md =>
      simp only [embedStmt, Stmt.loopBodyNoInits]
      rw [embedStmts_loopBodyNoInits tss, embedStmts_loopBodyNoInits ess]
  | .loop guard measure invariant body md =>
      simp only [embedStmt, Stmt.loopBodyNoInits, Block.initVars]
      rw [embedStmts_definedVars body false, embedStmts_loopBodyNoInits body]
  | .exit label md => simp [embedStmt, Stmt.loopBodyNoInits]
  | .typeDecl tc md => simp [embedStmt, Stmt.loopBodyNoInits]
  termination_by sizeOf s

/-- Loop-body-init analysis of a statement list is unchanged by command
embedding. -/
theorem embedStmts_loopBodyNoInits (ss : List (Stmt P (Cmd P))) :
    Block.loopBodyNoInits (embedStmts ss) = Block.loopBodyNoInits ss := by
  match ss with
  | [] => simp [embedStmts, Block.loopBodyNoInits]
  | s :: rest =>
      simp only [embedStmts, Block.loopBodyNoInits]
      rw [embedStmt_loopBodyNoInits s, embedStmts_loopBodyNoInits rest]
  termination_by sizeOf ss
end

/-- Init-name uniqueness is unchanged by command embedding. -/
theorem embedStmts_uniqueInits (ss : List (Stmt P (Cmd P))) :
    Block.uniqueInits (C := CmdExt P) (embedStmts ss) ↔
      Block.uniqueInits (C := Cmd P) ss := by
  unfold Block.uniqueInits Block.initVars
  rw [embedStmts_definedVars]

/-- `touchedVars` commutes with the embedding: it is a fixed combination of
    `modifiedVars`, `definedVars true`, and `getVars`, each of which commutes. -/
theorem embedStmts_touchedVars (ss : List (Stmt P (Cmd P))) :
    Block.touchedVars (C := CmdExt P) (embedStmts ss)
      = Block.touchedVars (C := Cmd P) ss := by
  simp only [Block.touchedVars, Block.modifiedOrDefinedVars,
    embedStmts_modifiedVars, embedStmts_definedVars, embedStmts_getVars]

omit [HasFvar P] [HasFvars P] in
/-- `InitTypesInhabited` commutes with the embedding (it quantifies over
    `initTypes`, which commutes). -/
theorem embedStmts_InitTypesInhabited [HasVal P] (f : P.Factory) (ss : List (Stmt P (Cmd P))) :
    Block.InitTypesInhabited (P := P) (C := CmdExt P) f (embedStmts ss)
      ↔ Block.InitTypesInhabited (P := P) (C := Cmd P) f ss := by
  unfold Block.InitTypesInhabited
  rw [embedStmts_initTypes]

/-- A successful projection preserves the generic property that no identifier of
    a given string kind is defined or modified.  This is the command-generic
    bridge used to recover base-only predicates such as a pass's no-generated-write
    obligation. -/
theorem projectStmts_noDefinedOrModifiedKind_iff [HasIdent P]
    (Q : String → Prop) {ss : List (Stmt P (CmdExt P))} {bs : List (Stmt P (Cmd P))}
    (hp : projectStmts ss = some bs) :
    (∀ name : String, Q name →
      HasIdent.ident (P := P) name ∉
        (Block.definedVars (C := CmdExt P) ss false ++
          Block.modifiedVars (C := CmdExt P) ss)) ↔
    (∀ name : String, Q name →
      HasIdent.ident (P := P) name ∉
        (Block.definedVars (C := Cmd P) bs false ++
          Block.modifiedVars (C := Cmd P) bs)) := by
  have hemb : embedStmts bs = ss := embedStmts_projectStmts hp
  rw [← hemb, embedStmts_definedVars, embedStmts_modifiedVars]

/-! `defUseWellFormed` commutes with the embedding.  The `definedVars` and
    `declaredFuncs` predicate arguments are command-independent, so the theorem is
    universally quantified over them, which lets the cons case apply it at the
    extended predicate it threads through the tail. -/
mutual
/-- `defUseWellFormed` commutes with the embedding on a statement, at any
defined-variable and declared-function predicates. -/
theorem embedStmt_defUseWellFormed [HasOps P] [DecidableEq P.Ident]
    (dv df : P.Ident → Bool) (s : Stmt P (Cmd P)) :
    Stmt.defUseWellFormed (C := CmdExt P) dv df (embedStmt s)
      = Stmt.defUseWellFormed (C := Cmd P) dv df s := by
  match s with
  | .cmd c => rfl
  | .block lbl ss md =>
      simp only [embedStmt, Stmt.defUseWellFormed]
      exact embedStmts_defUseWellFormed dv df ss
  | .ite cond tss ess md =>
      simp only [embedStmt, Stmt.defUseWellFormed]
      rw [embedStmts_defUseWellFormed dv df tss, embedStmts_defUseWellFormed dv df ess]
  | .loop g m inv body md =>
      simp only [embedStmt, Stmt.defUseWellFormed]
      rw [embedStmts_defUseWellFormed dv df body]
  | .exit lbl md => rfl
  | .typeDecl t md => rfl
  termination_by sizeOf s

/-- `defUseWellFormed` commutes with the embedding on a statement list. -/
theorem embedStmts_defUseWellFormed [HasOps P] [DecidableEq P.Ident]
    (dv df : P.Ident → Bool) (ss : List (Stmt P (Cmd P))) :
    Block.defUseWellFormed (C := CmdExt P) dv df (embedStmts ss)
      = Block.defUseWellFormed (C := Cmd P) dv df ss := by
  match ss with
  | [] => rfl
  | s :: rest =>
      simp only [embedStmts, Block.defUseWellFormed]
      rw [embedStmt_defUseWellFormed dv df s,
          embedStmt_definedVars s true,
          embedStmts_defUseWellFormed
            (fun n => dv n || decide (n ∈ Stmt.definedVars (C := Cmd P) s true)) df rest]
  termination_by sizeOf ss
end

omit [HasFvar P] [HasFvars P] in
/-- `embedStmts` is the pointwise map of `embedStmt`. -/
theorem embedStmts_eq_map (ss : List (Stmt P (Cmd P))) : embedStmts ss = ss.map embedStmt := by
  induction ss with
  | nil => rfl
  | cons s rest ih => simp [embedStmts, ih]

omit [HasFvar P] [HasFvars P] in
/-- `embedStmts` distributes over list append. -/
theorem embedStmts_append (xs ys : List (Stmt P (Cmd P))) :
    embedStmts (xs ++ ys) = embedStmts xs ++ embedStmts ys := by
  simp [embedStmts_eq_map, List.map_append]

omit [HasFvar P] [HasFvars P] in
/-- Flat-mapping `definedVars` over embedded commands equals flat-mapping
`definedVars` over the base commands. -/
@[simp] private theorem map_embedCommand_definedVars (cmds : List (Cmd P)) :
    (cmds.map embedCommand).flatMap CmdExt.definedVars = cmds.flatMap Cmd.definedVars := by
  induction cmds with
  | nil => rfl
  | cons c rest ih => simp [ih]

omit [HasFvar P] [HasFvars P] in
/-- Flat-mapping `modifiedVars` over embedded commands equals flat-mapping
`modifiedVars` over the base commands. -/
@[simp] private theorem map_embedCommand_modifiedVars (cmds : List (Cmd P)) :
    (cmds.map embedCommand).flatMap CmdExt.modifiedVars = cmds.flatMap Cmd.modifiedVars := by
  induction cmds with
  | nil => rfl
  | cons c rest ih => simp [ih]

/-- Flat-mapping `getVars` over embedded commands equals flat-mapping `getVars`
over the base commands. -/
@[simp] private theorem map_embedCommand_readVars (cmds : List (Cmd P)) :
    (cmds.map embedCommand).flatMap CmdExt.readVars = cmds.flatMap Cmd.getVars := by
  induction cmds with
  | nil => rfl
  | cons c rest ih => simp [ih]

omit [HasFvar P] [HasFvars P] in
/-- Flat-mapping `initTypes` over embedded commands equals flat-mapping
`initTypes` over the base commands. -/
@[simp] private theorem map_embedCommand_initTypes (cmds : List (Cmd P)) :
    (cmds.map embedCommand).flatMap (HasInitTypesImp.initTypes (P := P)) =
      cmds.flatMap (HasInitTypesImp.initTypes (P := P)) := by
  induction cmds with
  | nil => rfl
  | cons c rest ih =>
      rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, ih]
      cases c <;> rfl

/-- `definedVars` of an embedded CFG equals `definedVars` of the base CFG. -/
@[simp] theorem embedCFG_definedVars
    (cfg : CFG String (DetBlock String (Cmd P) P)) (flag : Bool) :
    HasVarsImp.definedVars (P := P) (embedCFG cfg) flag =
      HasVarsImp.definedVars (P := P) cfg flag := by
  cases cfg with
  | mk entry blocks =>
    change (blocks.map (fun lb => (lb.1, embedDetBlock lb.2))).flatMap
      (fun lb => lb.2.cmds.flatMap CmdExt.definedVars) =
      blocks.flatMap (fun lb => lb.2.cmds.flatMap Cmd.definedVars)
    induction blocks with
    | nil => rfl
    | cons lb rest ih =>
      rcases lb with ⟨label, block⟩
      simp only [List.map_cons, List.flatMap_cons]
      rw [ih]
      simp [embedDetBlock]

/-- `modifiedVars` of an embedded CFG equals `modifiedVars` of the base CFG. -/
@[simp] theorem embedCFG_modifiedVars
    (cfg : CFG String (DetBlock String (Cmd P) P)) :
    HasVarsImp.modifiedVars (P := P) (embedCFG cfg) =
      HasVarsImp.modifiedVars (P := P) cfg := by
  cases cfg with
  | mk entry blocks =>
    change (blocks.map (fun lb => (lb.1, embedDetBlock lb.2))).flatMap
      (fun lb => lb.2.cmds.flatMap CmdExt.modifiedVars) =
      blocks.flatMap (fun lb => lb.2.cmds.flatMap Cmd.modifiedVars)
    induction blocks with
    | nil => rfl
    | cons lb rest ih =>
      rcases lb with ⟨label, block⟩
      simp only [List.map_cons, List.flatMap_cons]
      rw [ih]
      simp [embedDetBlock]

/-- `readVars` of an embedded CFG equals `readVars` of the base CFG. -/
@[simp] theorem embedCFG_readVars
    (cfg : CFG String (DetBlock String (Cmd P) P)) :
    HasVarsImp.readVars (P := P) (embedCFG cfg) =
      HasVarsImp.readVars (P := P) cfg := by
  simp only [embedCFG, HasVarsImp.readVars]
  induction cfg.blocks with
  | nil => rfl
  | cons lb rest ih =>
    rcases lb with ⟨label, block⟩
    simp only [List.map_cons, List.flatMap_cons]
    rw [ih]
    simp [embedDetBlock]

omit [HasFvar P] [HasFvars P] in
/-- `initTypes` of an embedded CFG equals `initTypes` of the base CFG. -/
@[simp] theorem embedCFG_initTypes
    (cfg : CFG String (DetBlock String (Cmd P) P)) :
    Imperative.DetCFG.initTypes (embedCFG cfg) = Imperative.DetCFG.initTypes cfg := by
  cases cfg with
  | mk entry blocks =>
    change (blocks.map (fun lb => (lb.1, embedDetBlock lb.2))).flatMap
      (fun lb => lb.2.cmds.flatMap (HasInitTypesImp.initTypes (P := P))) =
      blocks.flatMap (fun lb => lb.2.cmds.flatMap
        (HasInitTypesImp.initTypes (P := P)))
    induction blocks with
    | nil => rfl
    | cons lb rest ih =>
      rcases lb with ⟨label, block⟩
      simp only [List.map_cons, List.flatMap_cons]
      rw [ih]
      simp [embedDetBlock]

end AnalysisVars

/-! ## Command-independent shape analyses

These analyses never inspect a command, so they commute with the embedding with
no expression type classes at all. -/

mutual
/-- Deterministic-guard analysis is unchanged by command embedding. -/
theorem embedStmt_noNondetGuards (s : Stmt P (Cmd P)) :
    Stmt.noNondetGuards (embedStmt s) = Stmt.noNondetGuards s := by
  match s with
  | .cmd c => simp [embedStmt, Stmt.noNondetGuards]
  | .block label ss md =>
      simp only [embedStmt, Stmt.noNondetGuards]
      exact embedStmts_noNondetGuards ss
  | .ite cond tss ess md =>
      have ht := embedStmts_noNondetGuards tss
      have he := embedStmts_noNondetGuards ess
      cases cond <;> simp [embedStmt, Stmt.noNondetGuards, ht, he]
  | .loop guard measure invariant body md =>
      have hb := embedStmts_noNondetGuards body
      cases guard <;> simp [embedStmt, Stmt.noNondetGuards, hb]
  | .exit label md => simp [embedStmt, Stmt.noNondetGuards]
  | .typeDecl tc md => simp [embedStmt, Stmt.noNondetGuards]
  termination_by sizeOf s

/-- Deterministic-guard analysis of a statement list is unchanged by command
embedding. -/
theorem embedStmts_noNondetGuards (ss : List (Stmt P (Cmd P))) :
    Block.noNondetGuards (embedStmts ss) = Block.noNondetGuards ss := by
  match ss with
  | [] => simp [embedStmts, Block.noNondetGuards]
  | s :: rest =>
      simp only [embedStmts, Block.noNondetGuards]
      rw [embedStmt_noNondetGuards s, embedStmts_noNondetGuards rest]
  termination_by sizeOf ss
end

mutual
/-- Loop-invariant shape analysis is unchanged by command embedding. -/
theorem embedStmt_loopHasNoInvariants (s : Stmt P (Cmd P)) :
    Stmt.loopHasNoInvariants (embedStmt s) = Stmt.loopHasNoInvariants s := by
  match s with
  | .cmd c => simp [embedStmt, Stmt.loopHasNoInvariants]
  | .block label ss md =>
      simp only [embedStmt, Stmt.loopHasNoInvariants]
      exact embedStmts_loopHasNoInvariants ss
  | .ite cond tss ess md =>
      simp only [embedStmt, Stmt.loopHasNoInvariants]
      rw [embedStmts_loopHasNoInvariants tss, embedStmts_loopHasNoInvariants ess]
  | .loop guard measure invariant body md =>
      simp only [embedStmt, Stmt.loopHasNoInvariants]
      rw [embedStmts_loopHasNoInvariants body]
  | .exit label md => simp [embedStmt, Stmt.loopHasNoInvariants]
  | .typeDecl tc md => simp [embedStmt, Stmt.loopHasNoInvariants]
  termination_by sizeOf s

/-- Loop-invariant shape analysis of a statement list is unchanged by command
embedding. -/
theorem embedStmts_loopHasNoInvariants (ss : List (Stmt P (Cmd P))) :
    Block.loopHasNoInvariants (embedStmts ss) = Block.loopHasNoInvariants ss := by
  match ss with
  | [] => simp [embedStmts, Block.loopHasNoInvariants]
  | s :: rest =>
      simp only [embedStmts, Block.loopHasNoInvariants]
      rw [embedStmt_loopHasNoInvariants s, embedStmts_loopHasNoInvariants rest]
  termination_by sizeOf ss
end

mutual
/-- Loop-measure shape analysis is unchanged by command embedding. -/
theorem embedStmt_noMeasureLoops (s : Stmt P (Cmd P)) :
    Stmt.noMeasureLoops (embedStmt s) = Stmt.noMeasureLoops s := by
  match s with
  | .cmd c => simp [embedStmt, Stmt.noMeasureLoops]
  | .block label ss md =>
      simp only [embedStmt, Stmt.noMeasureLoops]
      exact embedStmts_noMeasureLoops ss
  | .ite cond tss ess md =>
      simp only [embedStmt, Stmt.noMeasureLoops]
      rw [embedStmts_noMeasureLoops tss, embedStmts_noMeasureLoops ess]
  | .loop guard measure invariant body md =>
      simp only [embedStmt, Stmt.noMeasureLoops]
      rw [embedStmts_noMeasureLoops body]
  | .exit label md => simp [embedStmt, Stmt.noMeasureLoops]
  | .typeDecl tc md => simp [embedStmt, Stmt.noMeasureLoops]
  termination_by sizeOf s

/-- Loop-measure shape analysis of a statement list is unchanged by command
embedding. -/
theorem embedStmts_noMeasureLoops (ss : List (Stmt P (Cmd P))) :
    Block.noMeasureLoops (embedStmts ss) = Block.noMeasureLoops ss := by
  match ss with
  | [] => simp [embedStmts, Block.noMeasureLoops]
  | s :: rest =>
      simp only [embedStmts, Block.noMeasureLoops]
      rw [embedStmt_noMeasureLoops s, embedStmts_noMeasureLoops rest]
  termination_by sizeOf ss
end

mutual
/-- Exit coverage is unchanged by command embedding. -/
theorem embedStmt_exitsCoveredByBlocks (labels : List String) (s : Stmt P (Cmd P)) :
    Stmt.exitsCoveredByBlocks labels (embedStmt s) ↔
      Stmt.exitsCoveredByBlocks labels s := by
  match s with
  | .cmd c => simp [embedStmt, Stmt.exitsCoveredByBlocks]
  | .block label ss md =>
      simp only [embedStmt, Stmt.exitsCoveredByBlocks]
      exact embedStmts_exitsCoveredByBlocks (label :: labels) ss
  | .ite cond tss ess md =>
      simp only [embedStmt, Stmt.exitsCoveredByBlocks]
      rw [embedStmts_exitsCoveredByBlocks labels tss,
        embedStmts_exitsCoveredByBlocks labels ess]
  | .loop guard measure invariant body md =>
      simp only [embedStmt, Stmt.exitsCoveredByBlocks]
      exact embedStmts_exitsCoveredByBlocks labels body
  | .exit label md => simp [embedStmt, Stmt.exitsCoveredByBlocks]
  | .typeDecl tc md => simp [embedStmt, Stmt.exitsCoveredByBlocks]
  termination_by sizeOf s

/-- Exit coverage of a statement list is unchanged by command embedding. -/
theorem embedStmts_exitsCoveredByBlocks (labels : List String) (ss : List (Stmt P (Cmd P))) :
    Block.exitsCoveredByBlocks labels (embedStmts ss) ↔
      Block.exitsCoveredByBlocks labels ss := by
  match ss with
  | [] => simp [embedStmts, Block.exitsCoveredByBlocks]
  | s :: rest =>
      simp only [embedStmts, Block.exitsCoveredByBlocks]
      rw [embedStmt_exitsCoveredByBlocks labels s,
        embedStmts_exitsCoveredByBlocks labels rest]
  termination_by sizeOf ss
end

mutual
/-- User block labels are unchanged by command embedding. -/
theorem embedStmt_getBlockLabels (s : Stmt P (Cmd P)) :
    Block.getBlockLabels.stmtGetBlockLabels (embedStmt s) =
      Block.getBlockLabels.stmtGetBlockLabels s := by
  match s with
  | .cmd c => simp [embedStmt, Block.getBlockLabels.stmtGetBlockLabels]
  | .block label ss md =>
      simp only [embedStmt, Block.getBlockLabels.stmtGetBlockLabels]
      rw [embedStmts_getBlockLabels ss]
  | .ite cond tss ess md =>
      simp only [embedStmt, Block.getBlockLabels.stmtGetBlockLabels]
      rw [embedStmts_getBlockLabels tss, embedStmts_getBlockLabels ess]
  | .loop guard measure invariant body md =>
      simp only [embedStmt, Block.getBlockLabels.stmtGetBlockLabels]
      rw [embedStmts_getBlockLabels body]
  | .exit label md => simp [embedStmt, Block.getBlockLabels.stmtGetBlockLabels]
  | .typeDecl tc md => simp [embedStmt, Block.getBlockLabels.stmtGetBlockLabels]
  termination_by sizeOf s

/-- User block labels of a statement list are unchanged by command embedding. -/
theorem embedStmts_getBlockLabels (ss : List (Stmt P (Cmd P))) :
    Block.getBlockLabels (embedStmts ss) = Block.getBlockLabels ss := by
  match ss with
  | [] => simp [embedStmts, Block.getBlockLabels]
  | s :: rest =>
      simp only [embedStmts, Block.getBlockLabels]
      rw [embedStmt_getBlockLabels s, embedStmts_getBlockLabels rest]
  termination_by sizeOf ss
end

/-- User-label shape and uniqueness are unchanged by command embedding. -/
theorem embedStmts_userLabelsShapeNodup (ss : List (Stmt P (Cmd P))) :
    Block.userLabelsShapeNodup (C := CmdExt P) (embedStmts ss) ↔
      Block.userLabelsShapeNodup (C := Cmd P) ss := by
  unfold Block.userLabelsShapeNodup
  rw [embedStmts_getBlockLabels]

/-! ## Native semantics correspondence

The base event-trace semantics `StepStmtE P (EvalCmdE P)` and the call-aware
event-trace semantics `StepStmtExtE π` (= `StepStmtE P (EvalCmdExtE π)`) agree
across the embedding, step for step and trace for trace.  The traces coincide
exactly; no event is added or dropped. -/

section Semantics

variable [DecidableEq P.Ident] [HasOldIdent P]
  [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P] [HasVal P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
  (π : String → Option (Procedure P (CmdExt P) Hdr))

/-! ### Administrative (command-free) steps -/

omit [DecidableEq P.Ident] [HasOldIdent P] [HasBoolOps P] [HasFvar P] [HasFvars P] [HasVal P] in
/-- Embedding carries a command-free `StepStmt` forward: every administrative
    control-flow step on base configurations is the same step on the embedded
    extended configurations. -/
theorem embedConfig_stepAdmin {c c' : Config P (Cmd P)}
    (h : StepStmt P (noCommandEvalE P (Cmd P)) c c') :
    StepStmt P (noCommandEvalE P (CmdExt P)) (embedConfig c) (embedConfig c') := by
  induction h with
  | step_cmd hc => exact hc.elim
  | step_block => exact .step_block
  | step_ite_true hcond => exact .step_ite_true hcond
  | step_ite_false hcond => exact .step_ite_false hcond
  | step_ite_nondet_true => exact .step_ite_nondet_true
  | step_ite_nondet_false => exact .step_ite_nondet_false
  | step_loop_enter hg => exact .step_loop_enter hg
  | step_loop_exit hg => exact .step_loop_exit hg
  | step_loop_nondet_enter => exact .step_loop_nondet_enter
  | step_loop_nondet_exit => exact .step_loop_nondet_exit
  | step_exit => exact .step_exit
  | step_typeDecl => exact .step_typeDecl
  | step_stmts_nil => exact .step_stmts_nil
  | step_stmts_cons => exact .step_stmts_cons
  | step_seq_inner _ ih => exact .step_seq_inner ih
  | step_seq_done => exact .step_seq_done
  | step_seq_exit => exact .step_seq_exit
  | step_block_body _ ih => exact .step_block_body ih
  | step_block_done => exact .step_block_done
  | step_block_exit_match hlabel => exact .step_block_exit_match hlabel
  | step_block_exit_mismatch hlabel => exact .step_block_exit_mismatch hlabel

omit [DecidableEq P.Ident] [HasOldIdent P] [HasBoolOps P] [HasFvar P] [HasFvars P] [HasVal P] in
/-- Embedding reflects a command-free `StepStmt`: an administrative step out
    of an embedded configuration comes from a base step, and lands in the image
    of the embedding. -/
theorem embedConfig_stepAdmin_rev {c : Config P (Cmd P)} {d : Config P (CmdExt P)}
    (h : StepStmt P (noCommandEvalE P (CmdExt P)) (embedConfig c) d) :
    ∃ c', d = embedConfig c' ∧
      StepStmt P (noCommandEvalE P (Cmd P)) c c' := by
  generalize he : embedConfig c = e at h
  induction h generalizing c with
  | step_cmd hc => exact hc.elim
  | step_block =>
      obtain ⟨sb, rfl, hs⟩ := embedConfig_eq_stmt he
      obtain ⟨ssb, rfl, hss⟩ := embedStmt_eq_block hs
      refine ⟨_, ?_, .step_block⟩; subst hss; rfl
  | step_ite_true hcond =>
      obtain ⟨sb, rfl, hs⟩ := embedConfig_eq_stmt he
      obtain ⟨tssb, essb, rfl, ht, _⟩ := embedStmt_eq_ite hs
      refine ⟨_, ?_, .step_ite_true hcond⟩; subst ht; rfl
  | step_ite_false hcond =>
      obtain ⟨sb, rfl, hs⟩ := embedConfig_eq_stmt he
      obtain ⟨tssb, essb, rfl, _, hee⟩ := embedStmt_eq_ite hs
      refine ⟨_, ?_, .step_ite_false hcond⟩; subst hee; rfl
  | step_ite_nondet_true =>
      obtain ⟨sb, rfl, hs⟩ := embedConfig_eq_stmt he
      obtain ⟨tssb, essb, rfl, ht, _⟩ := embedStmt_eq_ite hs
      refine ⟨_, ?_, .step_ite_nondet_true⟩; subst ht; rfl
  | step_ite_nondet_false =>
      obtain ⟨sb, rfl, hs⟩ := embedConfig_eq_stmt he
      obtain ⟨tssb, essb, rfl, _, hee⟩ := embedStmt_eq_ite hs
      refine ⟨_, ?_, .step_ite_nondet_false⟩; subst hee; rfl
  | step_loop_enter hg =>
      obtain ⟨sb, rfl, hs⟩ := embedConfig_eq_stmt he
      obtain ⟨bodyb, rfl, hb⟩ := embedStmt_eq_loop hs
      refine ⟨_, ?_, .step_loop_enter hg⟩; subst hb; rfl
  | step_loop_exit hg =>
      obtain ⟨sb, rfl, hs⟩ := embedConfig_eq_stmt he
      obtain ⟨bodyb, rfl, _⟩ := embedStmt_eq_loop hs
      refine ⟨_, ?_, .step_loop_exit hg⟩; rfl
  | step_loop_nondet_enter =>
      obtain ⟨sb, rfl, hs⟩ := embedConfig_eq_stmt he
      obtain ⟨bodyb, rfl, hb⟩ := embedStmt_eq_loop hs
      refine ⟨_, ?_, .step_loop_nondet_enter⟩; subst hb; rfl
  | step_loop_nondet_exit =>
      obtain ⟨sb, rfl, hs⟩ := embedConfig_eq_stmt he
      obtain ⟨bodyb, rfl, _⟩ := embedStmt_eq_loop hs
      refine ⟨_, ?_, .step_loop_nondet_exit⟩; rfl
  | step_exit =>
      obtain ⟨sb, rfl, hs⟩ := embedConfig_eq_stmt he
      obtain rfl := embedStmt_eq_exit hs
      refine ⟨_, ?_, .step_exit⟩; rfl
  | step_typeDecl =>
      obtain ⟨sb, rfl, hs⟩ := embedConfig_eq_stmt he
      obtain rfl := embedStmt_eq_typeDecl hs
      refine ⟨_, ?_, .step_typeDecl⟩; rfl
  | step_stmts_nil =>
      obtain ⟨ssb, rfl, hss⟩ := embedConfig_eq_stmts he
      obtain rfl := embedStmts_eq_nil hss
      refine ⟨_, ?_, .step_stmts_nil⟩; rfl
  | step_stmts_cons =>
      obtain ⟨ssb, rfl, hss⟩ := embedConfig_eq_stmts he
      obtain ⟨sb, ssb', rfl, hsb, hssb⟩ := embedStmts_eq_cons hss
      refine ⟨_, ?_, .step_stmts_cons⟩; subst hsb; subst hssb; rfl
  | step_seq_inner _ ih =>
      obtain ⟨cinner, ssb, rfl, hce, hss⟩ := embedConfig_eq_seq he
      obtain ⟨cinner', rfl, hstep⟩ := ih hce
      refine ⟨_, ?_, .step_seq_inner hstep⟩; subst hss; rfl
  | step_seq_done =>
      obtain ⟨cinner, ssb, rfl, hce, hss⟩ := embedConfig_eq_seq he
      obtain rfl := embedConfig_eq_terminal hce
      refine ⟨_, ?_, .step_seq_done⟩; subst hss; rfl
  | step_seq_exit =>
      obtain ⟨cinner, ssb, rfl, hce, _⟩ := embedConfig_eq_seq he
      obtain rfl := embedConfig_eq_exiting hce
      refine ⟨_, ?_, .step_seq_exit⟩; rfl
  | step_block_body _ ih =>
      obtain ⟨cinner, rfl, hce⟩ := embedConfig_eq_block he
      obtain ⟨cinner', rfl, hstep⟩ := ih hce
      refine ⟨_, ?_, .step_block_body hstep⟩; rfl
  | step_block_done =>
      obtain ⟨cinner, rfl, hce⟩ := embedConfig_eq_block he
      obtain rfl := embedConfig_eq_terminal hce
      refine ⟨_, ?_, .step_block_done⟩; rfl
  | step_block_exit_match hlabel =>
      obtain ⟨cinner, rfl, hce⟩ := embedConfig_eq_block he
      obtain rfl := embedConfig_eq_exiting hce
      refine ⟨_, ?_, .step_block_exit_match hlabel⟩; rfl
  | step_block_exit_mismatch hlabel =>
      obtain ⟨cinner, rfl, hce⟩ := embedConfig_eq_block he
      obtain rfl := embedConfig_eq_exiting hce
      refine ⟨_, ?_, .step_block_exit_mismatch hlabel⟩; rfl

/-! ### Single event-trace steps -/

omit [HasVal P] in
/-- Embedding carries one base event-trace step forward, with the same trace. -/
theorem embedConfig_stepE {c c' : Config P (Cmd P)}
    {tr : Trace P} (h : StepStmtE P (EvalCmdE P) c tr c') :
    StepStmtE P (EvalCmdExtE π) (embedConfig c) tr (embedConfig c') := by
  induction h with
  | step_cmd hcmd =>
      exact StepStmtE.step_cmd (EvalCmdExtE.cmd_sem hcmd)
  | step_admin hadmin =>
      exact StepStmtE.step_admin (embedConfig_stepAdmin hadmin)
  | step_seq_inner _ ih => exact StepStmtE.step_seq_inner ih
  | step_block_body _ ih => exact StepStmtE.step_block_body ih

omit [HasVal P] in
/-- Embedding reflects one call-aware event-trace step out of an embedded
    configuration: it comes from a base step with the identical trace and a
    target again in the image of the embedding. -/
theorem embedConfig_stepE_rev {c : Config P (Cmd P)}
    {d : Config P (CmdExt P)} {tr : Trace P}
    (h : StepStmtE P (EvalCmdExtE π) (embedConfig c) tr d) :
    ∃ c', d = embedConfig c' ∧ StepStmtE P (EvalCmdE P) c tr c' := by
  generalize he : embedConfig c = e at h
  induction h generalizing c with
  | step_cmd hcmd =>
      obtain ⟨sb, rfl, hs⟩ := embedConfig_eq_stmt he
      obtain ⟨b, rfl, rfl⟩ := embedStmt_eq_cmd hs
      cases hcmd with
      | cmd_sem hbase =>
          exact ⟨_, by simp [embedConfig], StepStmtE.step_cmd hbase⟩
  | step_admin hadmin =>
      subst he
      obtain ⟨c', hd, hstep⟩ := embedConfig_stepAdmin_rev hadmin
      exact ⟨c', hd, StepStmtE.step_admin hstep⟩
  | step_seq_inner _ ih =>
      obtain ⟨cinner, ssb, rfl, hce, hss⟩ := embedConfig_eq_seq he
      obtain ⟨cinner', rfl, hstep⟩ := ih hce
      exact ⟨_, by simp [embedConfig, ← hss], StepStmtE.step_seq_inner hstep⟩
  | step_block_body _ ih =>
      obtain ⟨cinner, rfl, hce⟩ := embedConfig_eq_block he
      obtain ⟨cinner', rfl, hstep⟩ := ih hce
      exact ⟨_, by simp [embedConfig], StepStmtE.step_block_body hstep⟩

/-! ### Multi-step event-trace runs -/

omit [HasVal P] in
/-- Embedding carries a whole base run forward, preserving its trace. -/
theorem embedConfig_stepStarE {c c' : Config P (Cmd P)}
    {tr : Trace P} (h : StepStmtStarE P (EvalCmdE P) c tr c') :
    StepStmtStarE P (EvalCmdExtE π) (embedConfig c) tr (embedConfig c') := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ _ _ hstep _ ih => exact .step _ _ _ _ _ (embedConfig_stepE π hstep) ih

omit [HasVal P] in
/-- Embedding reflects a whole call-aware run out of an embedded configuration:
    it comes from a base run with the identical trace and an embedded target. -/
theorem embedConfig_stepStarE_rev {c : Config P (Cmd P)}
    {d : Config P (CmdExt P)} {tr : Trace P}
    (h : StepStmtStarE P (EvalCmdExtE π) (embedConfig c) tr d) :
    ∃ c', d = embedConfig c' ∧ StepStmtStarE P (EvalCmdE P) c tr c' := by
  generalize he : embedConfig c = e at h
  induction h generalizing c with
  | refl => exact ⟨c, he.symm, .refl _⟩
  | step _ _ _ _ _ hstep _ ih =>
      subst he
      obtain ⟨cmid, rfl, hbasestep⟩ := embedConfig_stepE_rev π hstep
      obtain ⟨c', hd, hbaserest⟩ := ih rfl
      exact ⟨c', hd, .step _ _ _ _ _ hbasestep hbaserest⟩

/-! ### The correspondence -/

omit [HasVal P] in
/-- Native event-trace correspondence between the base semantics
    `StepStmtE P (EvalCmdE P)` and the call-aware semantics
    `StepStmtE P (EvalCmdExtE π)`, for an arbitrary base configuration and an
    arbitrary finite trace.  The traces coincide exactly; no event is added or
    dropped. -/
theorem stepStarE_embed_iff
    (c c' : Config P (Cmd P)) (tr : Trace P) :
    StepStmtStarE P (EvalCmdE P) c tr c' ↔
    StepStmtStarE P (EvalCmdExtE π) (embedConfig c) tr (embedConfig c') := by
  constructor
  · exact embedConfig_stepStarE π
  · intro h
    obtain ⟨c'', hd, hb⟩ := embedConfig_stepStarE_rev π h
    rwa [embedConfig_injective hd]

omit [HasVal P] in
/-- Call-free specialisation: a call-free extended block runs, under
    `StepStmtE P (EvalCmdExtE π)`, exactly as its base projection runs under
    `StepStmtE P (EvalCmdE P)`, for an arbitrary configuration and finite trace. -/
theorem noCalls_stmts_stepStarE_iff
    {ss : List (Stmt P (CmdExt P))} {bs : List (Stmt P (Cmd P))} {ρ : Env P}
    {tr : Trace P} {c' : Config P (Cmd P)}
    (hproj : projectStmts ss = some bs) :
    StepStmtStarE P (EvalCmdE P) (.stmts bs ρ) tr c' ↔
    StepStmtStarE P (EvalCmdExtE π) (.stmts ss ρ) tr (embedConfig c') := by
  have hss : embedStmts bs = ss := embedStmts_projectStmts hproj
  have hcfg : (Config.stmts ss ρ : Config P (CmdExt P)) = embedConfig (.stmts bs ρ) := by
    simp [embedConfig, hss]
  rw [hcfg]
  exact stepStarE_embed_iff π (.stmts bs ρ) c' tr

/-! ## CFG forward bridge

Base deterministic CFG configurations embed into extended CFG configurations by
wrapping body commands while leaving labels, transfers, and environments
unchanged. The bridge carries base steps and finite event traces forward. -/

omit [DecidableEq P.Ident] [HasOldIdent P] [HasBool P] [HasBoolOps P]
    [HasFvar P] [HasFvars P] [HasVal P] in
/-- Looking a label up in an embedded CFG's block list yields the embedding of
the base lookup. -/
theorem lookup_embedCFG_blocks (cfg : CFG String (DetBlock String (Cmd P) P))
    (t : String) :
    List.lookup t (embedCFG cfg).blocks
      = (List.lookup t cfg.blocks).map embedDetBlock := by
  simp only [embedCFG]
  induction cfg.blocks with
  | nil => simp [List.lookup]
  | cons hd tl ih =>
      simp only [List.map_cons, List.lookup]
      by_cases h : t == hd.1
      · simp [h]
      · simp [h, ih]

omit [DecidableEq P.Ident] [HasOldIdent P] [HasFvar P] in
/-- The CFG forward bridge carries a command-free `StepCFG` step forward. -/
theorem embedCFGConfig_stepCFG {c c' : CFGConfig String (Cmd P) P}
    (h : StepCFG P (noCommandEvalE P (Cmd P)) c c') :
    StepCFG P (noCommandEvalE P (CmdExt P))
      (embedCFGConfig c) (embedCFGConfig c') := by
  induction h with
  | fetch hlookup =>
      refine StepCFG.fetch (b := embedDetBlock _) ?_
      rw [lookup_embedCFG_blocks, hlookup]; rfl
  | step_cmd hc => exact hc.elim
  | goto_true hcond => exact StepCFG.goto_true hcond
  | goto_false hcond => exact StepCFG.goto_false hcond
  | finish => exact StepCFG.finish

/-- The CFG forward bridge carries one base event-trace CFG step forward, with
the same emitted trace. -/
theorem embedCFGConfig_stepCFGE
    {c c' : CFGConfig String (Cmd P) P} {tr : List (Event P)}
    (h : StepCFGE P (EvalCmdE P) c tr c') :
    StepCFGE P (EvalCmdExtE π) (embedCFGConfig c) tr (embedCFGConfig c') := by
  cases h with
  | step_cmd hcmd =>
      exact StepCFGE.step_cmd (EvalCmdExtE.cmd_sem hcmd)
  | step_admin hadmin =>
      exact StepCFGE.step_admin (embedCFGConfig_stepCFG hadmin)

/-- The CFG forward bridge carries a whole base CFG run forward, preserving its
trace. -/
theorem embedCFGConfig_stepCFGStarE
    {c c' : CFGConfig String (Cmd P) P} {tr : List (Event P)}
    (h : StepCFGStarE P (EvalCmdE P) c tr c') :
    StepCFGStarE P (EvalCmdExtE π) (embedCFGConfig c) tr (embedCFGConfig c') := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ _ _ hstep _ ih => exact .step _ _ _ _ _ (embedCFGConfig_stepCFGE π hstep) ih

end Semantics

end Imperative

end -- public section
