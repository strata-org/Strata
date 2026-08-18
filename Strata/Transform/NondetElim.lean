/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.StmtProps
public import Strata.DL.Imperative.Cmd
public import Strata.DL.Util.LabelGen
public import Strata.Languages.Core.PipelinePhase
public import Strata.Transform.CoreTransform

public section

namespace Imperative

open LabelGen (StringGenM)

/-! # `nondetElim` — structured-to-structured nondeterministic-control elimination

Replaces every nondeterministic `.ite`/`.loop` guard with a deterministic read
of a freshly-generated boolean variable that is havoc'd at the construct's site.
After the pass, no `.ite`/`.loop` carries a `.nondet` guard; nondeterminism
survives only as havoc commands.

The fresh-name prefixes are distinct from the str2unstr translator's
`$__nondet_*` prefixes so the two passes' generated names are unmistakable in
origin; disjointness in the proofs is suffix-based, not prefix-based. -/

/-- Fresh-name prefix for nondet `.ite` guard variables. -/
@[expose] def ndelimItePrefix : String := "$__ndelim_ite$"

/-- Fresh-name prefix for nondet `.loop` guard variables. -/
@[expose] def ndelimLoopPrefix : String := "$__ndelim_loop$"

/-! Although this pass is generic over the command type, its correctness proofs
(`NondetElimCorrect.lean`) are specialized to the base command `Cmd P`. -/

mutual
/-- Rewrite a single statement, eliminating nondeterministic control. Threads a
`StringGenState`. For `.ite .nondet`, allocates a fresh boolean `$g`, emits a
local `init $g := *` before the rewritten ite, and makes the guard `.det $g`.
For `.loop .nondet`, emits a before-loop `init $g := *`, makes the guard
`.det $g`, and appends a body-tail `set $g := *` (re-havoc each iteration). Det
constructs and atomic commands pass through, recursing into sub-bodies. -/
@[expose] def Stmt.nondetElimM {P : PureExpr} {CmdT : Type}
    [HasIdent P] [HasFvar P] [HasBool P] [HasInit P CmdT] [HasHavoc P CmdT]
    (s : Stmt P CmdT) : StringGenM (List (Stmt P CmdT)) :=
  match s with
  | .cmd c => fun σ => ([.cmd c], σ)
  | .block lbl bss md => fun σ =>
      let (bss', σ') := Block.nondetElimM bss σ
      ([.block lbl bss' md], σ')
  | .ite (.det e) tss ess md => fun σ =>
      let (tss', σ₁) := Block.nondetElimM tss σ
      let (ess', σ₂) := Block.nondetElimM ess σ₁
      ([.ite (.det e) tss' ess' md], σ₂)
  | .ite .nondet tss ess md => fun σ =>
      let (g, σ₁) := StringGenState.gen ndelimItePrefix σ
      let ident := HasIdent.ident (P := P) g
      let (tss', σ₂) := Block.nondetElimM tss σ₁
      let (ess', σ₃) := Block.nondetElimM ess σ₂
      ([.cmd (HasInit.init ident HasBool.boolTy .nondet md),
        .ite (.det (HasFvar.mkFvar ident)) tss' ess' md], σ₃)
  | .loop (.det e) m inv body md => fun σ =>
      let (body', σ') := Block.nondetElimM body σ
      ([.loop (.det e) m inv body' md], σ')
  | .loop .nondet m inv body md => fun σ =>
      let (g, σ₁) := StringGenState.gen ndelimLoopPrefix σ
      let ident := HasIdent.ident (P := P) g
      let (body', σ₂) := Block.nondetElimM body σ₁
      ([.cmd (HasInit.init ident HasBool.boolTy .nondet md),
        .loop (.det (HasFvar.mkFvar ident)) m inv
          (body' ++ [.cmd (HasHavoc.havoc ident md)]) md], σ₂)
  | .exit lbl md => fun σ => ([.exit lbl md], σ)
  | .funcDecl d md => fun σ => ([.funcDecl d md], σ)
  | .typeDecl t md => fun σ => ([.typeDecl t md], σ)
  termination_by sizeOf s

/-- Apply `Stmt.nondetElimM` to each statement of the block, threading the state
and concatenating the resulting lists. -/
@[expose] def Block.nondetElimM {P : PureExpr} {CmdT : Type}
    [HasIdent P] [HasFvar P] [HasBool P] [HasInit P CmdT] [HasHavoc P CmdT]
    (ss : List (Stmt P CmdT)) : StringGenM (List (Stmt P CmdT)) :=
  match ss with
  | [] => fun σ => ([], σ)
  | s :: rest => fun σ =>
      let (ss_s, σ₁) := Stmt.nondetElimM s σ
      let (ss_r, σ₂) := Block.nondetElimM rest σ₁
      (ss_s ++ ss_r, σ₂)
  termination_by sizeOf ss
end

/-- Pure top-level wrapper: run the monadic pass from the empty `StringGenState`
and discard the final state. -/
@[expose] def Block.nondetElim {P : PureExpr} {CmdT : Type}
    [HasIdent P] [HasFvar P] [HasBool P] [HasInit P CmdT] [HasHavoc P CmdT]
    (ss : List (Stmt P CmdT)) : List (Stmt P CmdT) :=
  (Block.nondetElimM ss StringGenState.emp).1

end Imperative

/-! ## Core pipeline phase

Per-body name reuse across procedures is harmless: each procedure's scope (and
its guard bindings) is popped before the next runs. -/

namespace Core
open Imperative Lambda

/-- Nondet-elimination pass for Core: run `Imperative.Block.nondetElim` on every
structured procedure body. Raises a failure on a CFG procedure body, since this
statement-level rewrite cannot express CFGs and silently skipping one would let
a nondeterministic guard survive into symbolic evaluation. -/
def nondetElim (p : Program) : Transform.CoreTransformM (Bool × Program) := do
  let decls ← p.decls.mapM fun d =>
    match d with
    | .proc proc md =>
      match proc.body with
      | .structured ss =>
        pure (Decl.proc { proc with body := .structured (Block.nondetElim ss) } md)
      | .cfg _ =>
        throw (Strata.Message.fromString
          s!"nondetElim: CFG procedure bodies are not supported \
             (procedure '{proc.header.name.1}'); nondetElim expects structured bodies.")
    | _ => pure d
  return (true, { decls := decls })

/-- Nondet-elimination pipeline phase. Model-preserving: havoc'ing a fresh
    boolean and branching on it realizes exactly the nondeterministic choice it
    replaces, introducing no over-approximation. -/
def nondetElimPipelinePhase : PipelinePhase :=
  modelPreservingPipelinePhase "nondetElim" nondetElim

end Core
