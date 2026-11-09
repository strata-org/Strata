/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.ListUtilsProps
import all Strata.Util.ListUtils
import all Strata.Util.ListUtilsProps
public import Strata.DL.Imperative.CFGDominators
public import Strata.Languages.Core.Program
public import Strata.Languages.Core.CallWF

public section

/-! # Well-Formedness of Strata Core Programs
 This file contains well-formedness definitions of Strata Core `Program`s Note that
 the substructures such as `WFStatementProp` also carry a `Program` instance, and
 this allows us to state more expressive well-formedness conditions than a
 typical inductive relation.

 Although arguably these well-formedness properties can also be formulated using
 an inductive relation, this design choice provides more structure in
 formulating the properties in that it quite strictly mirrors the actual program
 structures themselves and can be extended in a straight-forward manner to suit
 specific needs.

 For example, one can easily add a new Prop to `WFProgramProp` stating that the
 set of all variable names, procedure names, and function names do not contain
 duplicates.  (Currently we only assert that the individual sets themselves do
 not contain duplicates)

 Theorems producing the well-formedness 'proofs' are located in files *WF.lean.
 These theorems typically state that if the type checker returns no error, then
 the structure is well-formed.

 A main theorem is `Program.typeCheckWF`, which states that if a program
 successfully type checks, then it is also well-formed. These properties are
 can serve as a baseline for proving semantic preservations.
 -/


namespace Core
namespace WF

open Imperative

/- Statement Wellformedness -/

structure WFcmdProp (p : Program) (c : Imperative.Cmd Expression) : Prop where

structure WFargProp (p : Program) (arg : Expression.Expr) : Prop where

/-- A call to `procName` with arguments `callArgs` is well-formed in `p`: the callee
    is a declared procedure, the arguments match its signature, and the result
    variables are distinct. -/
structure WFcallProp (p : Program) (procName : String) (callArgs : List (CallArg Expression)) : Prop where
  defined : (Program.Procedure.find? p procName).isSome
  argsMatch : (Program.Procedure.find? p procName = some proc) →
          ArgsMatchSignature proc callArgs
  lhsWF : (CallArg.getLhs callArgs).Nodup
  wfargs : Forall (WFargProp p) (CallArg.getInputExprs callArgs)

@[expose] def WFCmdExtProp (p : Program) (c : CmdExt Expression) : Prop := match c with
  | .cmd c => WFcmdProp p c
  | .call procName callArgs _ => WFcallProp p procName callArgs

structure WFblockProp (Cmd : Type) (p : Program) (label : String) (b : Block) : Prop where

structure WFifProp    (Cmd : Type) (p : Program) (cond : ExprOrNondet Expression)  (thenb : Block) (elseb : Block) : Prop where

structure WFloopProp    (Cmd : Type) (p : Program) (guard : ExprOrNondet Expression) (measure : Option Expression.Expr) (invariant : List (String × Expression.Expr)) (b : Block) : Prop where

structure WFexitProp  (p : Program) (label : String) : Prop where

@[simp, expose]
def WFStatementProp (p : Program) (stmt : Statement) : Prop := match stmt with
  | .cmd   cmd => WFCmdExtProp p cmd
  | .block (label : String) (b : Block) _ => WFblockProp (CmdExt Expression) p label b
  | .ite   (cond : ExprOrNondet Expression) (thenb : Block) (elseb : Block) _ =>
     WFifProp (CmdExt Expression) p cond thenb elseb
  | .loop  (guard : ExprOrNondet Expression) (measure : Option Expression.Expr)
           (invariant : List (String × Expression.Expr)) (body : Block) _ =>
     WFloopProp (CmdExt Expression) p guard measure invariant body
  | .exit (label : String) _ => WFexitProp p label
  | .typeDecl _ _ => True  -- Type declarations are always well-formed

abbrev WFStatementsProp (p : Program) := Forall (WFStatementProp p)

instance (p : Program) : ListP (WFStatementProp p) (WFStatementsProp p) where
  split := by intros as a wfs
              have H := ((List.Forall_cons (WFStatementProp p) a as).mp wfs)
              exact ⟨H.1, H.2⟩

/- Spec Wellformedness -/

structure WFPrePostProp (p : Program) (d : Procedure) (pp : CoreLabel × Procedure.Check)
  : Prop where

structure WFPreProp (p : Program) (d : Procedure) (pp : CoreLabel × Procedure.Check)
  : Prop extends WFPrePostProp p d pp where
  /-- A precondition carries no `old `-prefixed free variable. Unlike a
      postcondition, a precondition is evaluated in the pre-state, where an
      `old p` reference has no meaning; type checking rejects it because the
      `old` bindings for inout parameters are only introduced when checking
      postconditions and the body, not preconditions. This is the pre-state
      counterpart of `WFPostProp.oldOnlyInout`. -/
  noOldFvars : ∀ id ∈ Imperative.HasFvars.getFvars (P := Expression) pp.2.expr,
    ¬ CoreIdent.isOldIdent id

structure WFPostProp (p : Program) (d : Procedure) (pp : CoreLabel × Procedure.Check)
  : Prop extends WFPrePostProp p d pp where
  oldOnlyInout : ∀ id ∈ Imperative.HasFvars.getFvars (P := Expression) pp.2.expr,
    CoreIdent.isOldIdent id → id ∈ ListMap.keys (d.header.getInoutParams.map
      (fun (x, ty) => (CoreIdent.mkOld x.name, ty)))

@[simp]
abbrev WFPresProp (p : Program) (d : Procedure) := Forall (WFPreProp p d)

@[simp]
abbrev WFPostsProp (p : Program) (d : Procedure) := Forall (WFPostProp p d)

structure WFSpecProp (p : Program) (spec : Procedure.Spec) (d : Procedure): Prop where
  wfpre : WFPresProp p d spec.preconditions
  wfpost : WFPostsProp p d spec.postconditions

/- Procedure Wellformedness -/

structure WFTypeDeclarationProp (p : Program) (f : TypeDecl) : Prop where

structure WFAxiomDeclarationProp (p : Program) (f : Axiom) : Prop where

structure WFLemmaDeclarationProp (p : Program) (l : Lemma) : Prop where

structure WFDistinctDeclarationProp (p : Program) (l : Expression.Ident) (es : List (Expression.Expr)) : Prop where

/-! ## CFG-body well-formedness

`WFCFGProp` characterizes a well-formed `DetCFG` procedure body. Its conjuncts
mirror what the dominance-scoped CFG type checker (`CFG.typeCheck`) verifies:
structural validity (unique labels, existing entry, in-range branch targets) and
the scoping discipline on block-level `init`s (detailed per field below).

Dominance, cycles and reachability are stated over the computed graph analyses
(`computeDominators`, `cycleLabelsWith`, `reachableLabels`), not over paths of
the CFG. Nothing yet proves that these analyses agree with the path-based
definitions (see the `Strata.DL.Imperative.CFGDominators` module header), so
the conjuncts below mean "with respect to these analyses".

`WFCFGProp` does not by itself imply that a CFG-local is never read before it is
initialized: `domScoped` accepts a read that comes before the declaring `init` in
the same block, since a block dominates itself. The per-block type check rejects
such a read (the local is not yet in scope), but that is not part of this
structure. Nor does it rule out two `init`s of one local on a single path through
dominance-incomparable blocks (`entry → D → E` plus `entry → E`): `CFG.typeCheck`
rejects that with `checkInitsNotReachable`, whose result is not yet proved to
match a reachability property and so is not a conjunct here. The header-collision
and type-agreement checks (`checkInitsNotHeader`, `checkInitTypesAgree`) are not
part of it either, nor is a collision with a global name (rejected by the
per-block check). `WFCFGProp` is about scoping and shape only; it makes no
typing claim. -/

/-- The `init` targets declared by a basic block, in order. `Command.definedVars`
yields `[x]` for `init x` and `[]` for every other command. -/
@[expose] def blockInitVars (blk : DetBlock String Command Expression) : List Expression.Ident :=
  blk.cmds.flatMap Command.definedVars

/-- Every `init` target declared anywhere in a CFG. -/
@[expose] def cfgInitVars (cfg : DetCFG) : List Expression.Ident :=
  cfg.blocks.flatMap (fun lb => blockInitVars lb.2)

/-- Every variable a block *reads*: the fvars of its commands (`Command.readVars`
covers init/set right-hand sides, assert/assume/cover expressions, and call
`inArg`/`inoutArg` reads) plus its transfer guard's fvars. -/
@[expose] def blockReadVars (blk : DetBlock String Command Expression) : List Expression.Ident :=
  (blk.cmds.flatMap Command.readVars) ++ blk.transfer.guardFvars

/-- Every variable a block *assigns*. `Command.modifiedVars` covers `set` targets
and call `outArg`/`inoutArg` write targets. -/
@[expose] def blockSetTargets (blk : DetBlock String Command Expression) : List Expression.Ident :=
  blk.cmds.flatMap Command.modifiedVars

/-- Well-formedness of a `DetCFG` procedure body. -/
structure WFCFGProp (p : Program) (d : Procedure) (cfg : DetCFG) : Prop where
  /-- Block labels are unique. -/
  uniqueLabels : cfg.labels.Nodup
  /-- The entry label names an existing block. -/
  entryExists : cfg.entry ∈ cfg.labels
  /-- Every transfer target names an existing block. -/
  targetsInRange : ∀ lbl blk, (lbl, blk) ∈ cfg.blocks →
      ∀ t ∈ blk.transfer.targets, t ∈ cfg.labels
  /-- No block declares the same `init` target twice. -/
  blockInitsNodup : ∀ lbl blk, (lbl, blk) ∈ cfg.blocks → (blockInitVars blk).Nodup
  /-- Every CFG-local a *reachable* block reads or assigns has a declarer that
  dominates it with respect to `computeDominators`. Rules out a use of a local
  declared on only one arm of a branch. Unreachable blocks are excluded (their
  dominator set is `⊤`). -/
  domScoped : ∀ Blbl Bblk, (Blbl, Bblk) ∈ cfg.blocks →
      cfg.isReachable Blbl = true →
      ∀ x ∈ blockReadVars Bblk ++ blockSetTargets Bblk,
        x ∈ cfgInitVars cfg →
          ∃ Dlbl Dblk, (Dlbl, Dblk) ∈ cfg.blocks ∧ x ∈ blockInitVars Dblk ∧
            CFG.Dom.dominates cfg.computeDominators Dlbl Blbl = true
  /-- Two distinct *reachable* blocks declaring the same local are
  dominance-incomparable (so a use of that local resolves to a unique dominating
  declarer). Unreachable dead-code declarers are excluded. -/
  initsIncomparable : ∀ D1 D2 B1 B2, (D1, B1) ∈ cfg.blocks → (D2, B2) ∈ cfg.blocks →
      cfg.isReachable D1 = true → cfg.isReachable D2 = true →
      D1 ≠ D2 → ∀ x, x ∈ blockInitVars B1 → x ∈ blockInitVars B2 →
        CFG.Dom.dominates cfg.computeDominators D1 D2 = false ∧
        CFG.Dom.dominates cfg.computeDominators D2 D1 = false
  /-- No *reachable* block that declares a local lies on a cycle, as computed by
  `cycleLabelsWith`, so no `init` can run twice by looping back to it. -/
  noLoopInits : ∀ lbl blk, (lbl, blk) ∈ cfg.blocks → cfg.isReachable lbl = true →
      blockInitVars blk ≠ [] →
        (CFG.cycleLabelsWith cfg.succMap cfg.labels).contains lbl = false

structure WFProcedureProp (p : Program) (d : Procedure) : Prop where
  wfstmts : ∀ ss, d.body = .structured ss → WFStatementsProp p ss
  wfloclnd : ∀ ss, d.body = .structured ss → (HasVarsImp.definedVars (P:=Expression) ss false).Nodup
  inputsNodup : (ListMap.keys d.header.inputs).Nodup
  outputsNodup : (ListMap.keys d.header.outputs).Nodup
  ioNotOld : ∀ id ∈ ListMap.keys d.header.inputs ++ ListMap.keys d.header.outputs,
      ∀ x, id ≠ CoreIdent.mkOld x
  wfspec : WFSpecProp p d.spec d
  bodyExitsCovered : ∀ ss, d.body = .structured ss →
    Block.exitsCoveredByBlocks [] ss
  wfcfg : ∀ cfg, d.body = .cfg cfg → WFCFGProp p d cfg
structure WFFunctionProp (p : Program) (f : Function) : Prop where

structure WFRecFuncBlockProp (p : Program) (fs : List Function) : Prop where
  nonempty : fs ≠ []
  namesDistinct : (fs.map (·.name)).Nodup
  noInline : ∀ f ∈ fs, ¬ f.attr.any (· == .inline)
  wfFuncs : ∀ f ∈ fs, WFFunctionProp p f

@[simp, expose, grind]
def WFDeclProp (p : Program) (decl : Decl) : Prop := match decl with
  | .type t _ => WFTypeDeclarationProp p t
  | .ax a _ => WFAxiomDeclarationProp p a
  | .lemma l _ => WFLemmaDeclarationProp p l
  | .distinct l es _ => WFDistinctDeclarationProp p l es
  | .proc d _ => WFProcedureProp p d
  | .func f _ => WFFunctionProp p f
  | .recFuncBlock fs _ => WFRecFuncBlockProp p fs

@[simp] abbrev WFDeclsProp (p : Program) := Forall (WFDeclProp p)

instance (p : Program) : ListP (WFDeclProp p) (WFDeclsProp p) where
  split := by intros as a wfs
              have H := ((List.Forall_cons (WFDeclProp p) a as).mp wfs)
              exact ⟨H.1, H.2⟩

structure WFProgramProp (p : Program) where
  namesNodup : (p.getNames).Nodup
  wfdecls : WFDeclsProp p p.decls

structure WFProcedure (p : Program) extends (Wrapper Procedure) where
  prop: WFProcedureProp p self

structure WFProgram extends (Wrapper Program) where
  prop: WFProgramProp self

end WF

end Core

end -- public section
