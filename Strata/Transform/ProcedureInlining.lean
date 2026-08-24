/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.Languages.Core.PipelinePhase
public import Strata.Languages.Core.StatementType

/-! # Procedure Inlining Transformation -/

public section

namespace Core
namespace ProcedureInlining

open Transform
open Strata.Util (HMap)

/-- Statistics keys tracked by the procedure inlining transformation. -/
inductive Stats where
  | visitedCalls
  | inlinedCalls

#derive_prefixed_toString Stats "ProcedureInlining"

-- Gathers all labels including those in assert and assume.
mutual
def Block.labelsOfBlocksAndAssertAssumes (b : Block): List String :=
  List.flatMap (fun s => Statement.labelsOfBlocksAndAssertAssumes s) b

def Statement.labelsOfBlocksAndAssertAssumes (s : Core.Statement) : List String :=
  match s with
  | .block lbl b _ => lbl :: (Block.labelsOfBlocksAndAssertAssumes b)
  | .ite _ thenb elseb _ =>
    (Block.labelsOfBlocksAndAssertAssumes thenb) ++ (Block.labelsOfBlocksAndAssertAssumes elseb)
  | .loop _ _ _ body _ => Block.labelsOfBlocksAndAssertAssumes body
  | .assume lbl _ _ => [lbl]
  | .assert lbl _ _ => [lbl]
  | .cover lbl _ _ => [lbl]
  | .exit _ _ => []
  -- No other labeled commands.
  | .cmd _ => []
  | .funcDecl _ _ => []
  | .typeDecl _ _ => []
end

mutual
def Block.replaceLabelsOfBlocksAndAssertAssumes (b : Block) (map : HMap String String)
    : Block :=
  b.map (fun s => Statement.replaceLabelsOfBlocksAndAssertAssumes s map)

def Statement.replaceLabelsOfBlocksAndAssertAssumes
    (s : Core.Statement) (map : HMap String String) : Core.Statement :=
  let app (s:String) :=
    match map.find? s with
    | .none => s
    | .some s' => s'
  match s with
  | .block lbl b m => .block (app lbl) (Block.replaceLabelsOfBlocksAndAssertAssumes b map) m
  | .exit lbl m => .exit (app lbl) m
  | .ite cond thenb elseb m =>
    .ite cond (Block.replaceLabelsOfBlocksAndAssertAssumes thenb map) (Block.replaceLabelsOfBlocksAndAssertAssumes elseb map) m
  | .loop g measure inv body m =>
    .loop g measure inv (Block.replaceLabelsOfBlocksAndAssertAssumes body map) m
  | .assume lbl e m => .assume (app lbl) e m
  | .assert lbl e m => .assert (app lbl) e m
  | .cover lbl e m => .cover (app lbl) e m
  | .cmd _ => s
  | .funcDecl _ _ => s
  | .typeDecl _ _ => s
end


/-- Fresh-name prefix (`$__inline<N>`) for variables and labels introduced by
    one inlining. The `$__` namespace is reserved for internal use, and each
    inlining site gets a distinct `N`. -/
def inlinePrefix (n : Nat) : String := s!"$__inline{n}"

def inlineCounterKey : String := "inlineProcedures"

/-- Fresh-name prefix for the type variables introduced when freshening a
    polymorphic callee's type parameters at an inlining site. -/
def inlineTyVarPrefix : String := "$__inlinety"

/-- Rename every variable and label occurrence in the callee's `inputs`,
    `outputs`, and `bodyStmts` according to the explicit `var_map` (variables) and
    `label_map` (block/assert/assume/cover labels). `var_map` also carries the
    inout `old x` → snapshot rewrites, so all `Statement.substFvar` happens here in
    one pass. -/
private def renameAllLocalNames
    (inputs outputs : @Lambda.LMonoTySignature Unit) (bodyStmts : List Statement)
    (var_map : HMap Expression.Ident Expression.Ident)
    (label_map : HMap String String)
    : @Lambda.LMonoTySignature Unit × @Lambda.LMonoTySignature Unit × List Statement :=
  let new_body := bodyStmts.map (fun (s0 : Statement) =>
    let s := var_map.toList.foldl (fun (s : Statement) (old_id, new_id) =>
        let s := Statement.substFvar s old_id (.fvar () new_id .none)
        Statement.renameLhs s old_id new_id)
      s0
    Statement.replaceLabelsOfBlocksAndAssertAssumes s label_map)
  let renameId (id : Expression.Ident) : Expression.Ident :=
    (var_map.find? id).getD id
  let new_inputs := inputs.map (fun (id, ty) => (renameId id, ty))
  let new_outputs := outputs.map (fun (id, ty) => (renameId id, ty))
  (new_inputs, new_outputs, new_body)

/-- Build the pre-state snapshots for a callee's inout parameters. Returns the
    snapshot `init` statements together with the `old x → snapshot` variable
    rewrites (this helper performs no `Statement.substFvar` itself).

    In each `inoutParams` entry `(origName, renamedId, ty)`, `origName` is what
    `old origName` in the body matches against.

    Snapshot names use a `$` separator (`<pfx>$old_<name>`) so they stay disjoint
    from the `_`-separated renames regardless of the callee's own local names.
    `CoreIdent.mkOld` is deliberately not reused: the `old ` prefix is reserved
    for the *enclosing* procedure's own inout pre-state. -/
def snapshotOldInout (pfx : String)
    (inoutParams : List (Expression.Ident × Expression.Ident × Expression.Ty))
    (md : Imperative.MetaData Expression)
    : List Statement × List (Expression.Ident × Expression.Ident) :=
  let snapshotIds : List Expression.Ident :=
    inoutParams.map (fun (orig, _, _) => ⟨s!"{pfx}$old_{orig.name}", ()⟩)
  let oldInoutInits := createInitVars
    ((snapshotIds.zip (inoutParams.map (fun (_, _, ty) => ty))).zip
      (inoutParams.map (fun (_, rid, _) => rid))) md
  let oldSubst : List (Expression.Ident × Expression.Ident) :=
    (inoutParams.zip snapshotIds).map (fun ((orig, _, _), s) => (CoreIdent.mkOld orig.name, s))
  (oldInoutInits, oldSubst)


/-- Update the call graph after inlining one f(caller) -> g(callee) invocation. -/
def updateCallGraph (cg:CallGraph) (f: String) (g: String):
    Except Err CallGraph := do
  -- For each edge 'g -> x', add f -> x'
  let edges_from_g ← match cg.callees.get? g with
    | .some r => .ok r
    | .none => throw (Strata.Message.fromFormat f!"Invalid CallGraph: can't find {g} from callees domain")
  let edges_from_f ← match cg.callees.get? f with
    | .some r => .ok r
    | .none => throw (Strata.Message.fromFormat f!"Invalid CallGraph: can't find {f} from callees domain")
  let edges_from_f := edges_from_g.fold
    (fun (edges_from_f:Std.HashMap String Nat) fn_x cnt =>
      edges_from_f.alter fn_x (fun v =>
        .some (match v with | .none => cnt | .some v' => cnt + v')))
    edges_from_f
  let callees_new := cg.callees.insert f edges_from_f

  -- Now the callers. For every 'g -> x' edge, add f -> x'.
  let callers_new ← edges_from_g.foldM
    (fun (m:Std.HashMap String (Std.HashMap String Nat)) fn_x cnt => do
      match m.get? fn_x with
      | .none => throw (Strata.Message.fromFormat f!"Invalid CallGraph: can't find {fn_x} from callers domain")
      | .some edges_to_x =>
        .ok (m.insert fn_x (edges_to_x.alter f (fun v =>
          .some (match v with | .none => cnt | .some v' => cnt + v')))))
    cg.callers

  let cg_new : CallGraph := { callees := callees_new, callers := callers_new }

  -- .. and decrement the 'f -> g' edge by 1.
  let cg_final ← (cg_new.decrementEdge f g).mapError Strata.Message.fromString
  return cg_final

/-! ### Update assertion metadata with call site information -/

-- Update assertions and assumes in inlined body to carry the call site metadata
-- as the primary file range, moving the original assertion's file range to
-- relatedFileRange.
mutual
def Block.setCallSiteMetadata (b : Block) (callMd : Imperative.MetaData Expression)
    : Block :=
  b.map (fun s => Statement.setCallSiteMetadata s callMd)

def Statement.setCallSiteMetadata (s : Statement) (callMd : Imperative.MetaData Expression)
    : Statement :=
  match s with
  | .cmd (.cmd (.assert lbl e md)) =>
    .assert lbl e (md.setCallSiteFileRange callMd)
  | .cmd (.cmd (.assume lbl e md)) =>
    .assume lbl e (md.setCallSiteFileRange callMd)
  | .cmd (.cmd (.cover lbl e md)) =>
    .cover lbl e (md.setCallSiteFileRange callMd)
  | .block lbl b md =>
    .block lbl (Block.setCallSiteMetadata b callMd) md
  | .ite cond thenb elseb md =>
    .ite cond (Block.setCallSiteMetadata thenb callMd)
              (Block.setCallSiteMetadata elseb callMd) md
  | .loop g measure inv body md =>
    .loop g measure inv (Block.setCallSiteMetadata body callMd) md
  | _ => s
end

/-
Procedure Inlining.

If st is a call statement, inline the contents of the callee procedure.
To avoid conflicts between duplicated variable names in caller and callee,
every variables in callee are renamed.
This function does not update the specification because inlineCallStmt will not
use the specification. This will have to change if Strata also wants to support
the reachability query.
-/
def inlineCallCmd
    (doInline: Option String -> String -> CachedAnalyses -> Bool := λ _caller _callee _analyses => true)
    (s: Statement)
  : CoreTransformM (Option (List Statement)) :=
    open Lambda in do
    match s with
      | .cmd (.call procName callArgs md) =>
        let lhs := CallArg.getLhs callArgs
        let args := CallArg.getInputExprs callArgs
        incrementStat s!"{Stats.visitedCalls}"

        let st ← get
        if ¬ doInline st.currentProcedureName procName st.cachedAnalyses then return .none else
        incrementStat s!"{Stats.inlinedCalls}"

        let some p := (← get).currentProgram
          | throw (Strata.Message.fromString "currentProgram not set")
        let some currProcName := (← get).currentProcedureName
          | throw (Strata.Message.fromString "currentProcedure not set")
        let some proc := Program.Procedure.find? p procName
          | throw (Strata.Message.fromFormat f!"Procedure {procName} not found in program")

        let n ← bumpCounter inlineCounterKey
        let pfx := inlinePrefix n
        let freshen (name : String) : Expression.Ident := ⟨s!"{pfx}_{name}", ()⟩

        -- Freshen the callee's type parameters per inlining site. Keep only the
        -- signature (inputs/outputs), not a full `Procedure.Header`.
        let tySubst ← freshenTypeArgsSubst inlineTyVarPrefix proc.header.typeArgs
        let inputs : @Lambda.LMonoTySignature Unit :=
          proc.header.inputs.map (fun (id, ty) => (id, Lambda.LMonoTy.subst tySubst ty))
        let outputs : @Lambda.LMonoTySignature Unit :=
          proc.header.outputs.map (fun (id, ty) => (id, Lambda.LMonoTy.subst tySubst ty))

        let bodyStmts : List Statement ← match proc.body with
          | .structured ss => pure (ss.map (Core.Statement.Statement.subst tySubst))
          | .cfg _ => throw (Strata.Message.fromString
              "cannot inline procedure with CFG body into structured code")

        let inoutParams : List (Expression.Ident × Expression.Ident × Expression.Ty) :=
          (LMonoTySignature.toTrivialLTy (getInoutParams inputs outputs)).map
            (fun (orig, ty) => (orig, freshen orig.name, ty))
        let (oldInoutInits, oldSubst) := snapshotOldInout pfx inoutParams md

        let renameIds : List Expression.Ident :=
          bodyStmts.flatMap (fun s => s.definedVars false)
          ++ inputs.unzip.fst ++ outputs.unzip.fst
        let var_map : HMap Expression.Ident Expression.Ident :=
          renameIds.foldl (fun m id => m.insert id (freshen id.name)) {}
        let var_map := oldSubst.foldl (fun m (oldId, snapId) => m.insert oldId snapId) var_map
        let label_map : HMap String String :=
          (bodyStmts.flatMap (fun s => Statement.labelsOfBlocksAndAssertAssumes s)).foldl
            (fun m l => m.insert l s!"{pfx}_{l}") {}

        let (renamedInputs, renamedOutputs, procBodyStmts) :=
          renameAllLocalNames inputs outputs bodyStmts var_map label_map

        let sigOutputs := LMonoTySignature.toTrivialLTy renamedOutputs
        let sigInputs := LMonoTySignature.toTrivialLTy renamedInputs

        --   call x1,x2, .. = f(v1,v2,...)
        --   where 'procedure f(in1,in2,..) outputs(out1,out2,..)'
        -- Insert
        --   init in1 : ty := v1     --- inputInit
        --   init in2 : ty := v2
        --   init s1 : ty := j1  --- oldInoutInit (fresh pre-state snapshot,
        --   init s2 : ty := j2      one per inout param j1,j2,..)
        --   init out1 : ty := nondet --- outputInit
        --   init out2 : ty := nondet
        --   ... (f body, with `old jK` rewritten to sK)
        --   set x1 := out1    --- outputSetStmts
        --   set x2 := out2
        -- `init outN` is not necessary because calls are only allowed to use
        -- already declared variables (per Core.typeCheck)

        let inputInits := createInits (sigInputs.zip args) md
        -- Output-only parameters get a nondet init (already unconstrained, so no
        -- havoc); inout parameters are excluded to avoid a double init.
        let inputNames := sigInputs.unzip.fst.map (·.name)
        let sigOutputOnly := sigOutputs.filter fun (id, _) => !inputNames.contains id.name
        let outputInits := sigOutputOnly.map (fun (id, ty) => Statement.init id ty .nondet md)

        let outputSetStmts :=
          let out_vars := sigOutputs.unzip.fst
          let outs_lhs_and_sig := List.zip lhs out_vars
          List.map
            (fun (lhs_var,out_var) =>
              Statement.set lhs_var (.fvar () out_var (.none)) md)
            outs_lhs_and_sig

        let stmts:List (Imperative.Stmt Core.Expression Core.Command)
          := inputInits ++ oldInoutInits ++ outputInits
             ++ Block.setCallSiteMetadata procBodyStmts md
             ++ outputSetStmts

        -- Update CallGraph if available
        let σ ← get
        match σ.cachedAnalyses.callGraph with
        | .none => modify id -- do nothing
        | .some callGraph =>
          let callGraph' ← updateCallGraph callGraph currProcName procName
          set ({ σ with
            cachedAnalyses := {
              callGraph := .some callGraph'
            }
          }:CoreTransformState)

        -- Prefix the wrapper block label with the same unique `$__inline<N>` so
        -- that inlining the same callee at several sites yields distinct block
        -- labels rather than duplicates.
        return .some [.block s!"{pfx}_{procName}$inlined" stmts md]

      | _ => return .none

end ProcedureInlining

/-- A `doInline` predicate that refuses to inline procedures involved in
    recursion (i.e., part of a cycle in the call graph).  Falls back to
    `true` when no call graph is available. -/
def doInlineNonRecursive (callee : String) (analyses : Transform.CachedAnalyses) : Bool :=
  match analyses.callGraph with
  | none => true
  | some cg => !cg.isRecursive callee

/--
Options to control the behavior of inlining procedure calls in a Core program.
-/
structure InlineTransformOptions where
  -- 'doInline caller callee cachedAnalysis' returns true if the call command
  -- from caller to callee should be inlined. The caller can be none if the
  -- command is an orphaned one (rare, but can happen if inlineCallCmd is run
  -- directly on Command).
  doInline : Option String → String → Transform.CachedAnalyses → Bool :=
      fun _ callee analyses => doInlineNonRecursive callee analyses
  maxIters : Option Nat := none

/-- Procedure-inlining pipeline phase: the transform inlines procedure bodies
    at call sites. Inlining is semantics-preserving, so models are always
    sound (model-preserving).
    - `maxIters = none`: repeat until a fixed point (no changes).
    - `maxIters = some n`: run up to `n` iterations, stopping early if no change. -/
def procedureInliningPipelinePhase
    (opts : InlineTransformOptions := {})
    : PipelinePhase :=
  open Transform in
  -- `runProgramUntil` throws on a CFG body, and a callee with a CFG body
  -- cannot be inlined into structured code. Which calls are inlined is up to
  -- `doInline`, so the phase cannot claim `noCalls`, and the callee's `init`s
  -- are why it cannot claim `staticSingleAssignment` either.
  modelPreservingPipelinePhase "inlineProcedures"
    (requires := factSet![.noCFGBodies])
    (preserves := factSet![.noCFGBodies, .noCalls, .noLoops, .noLoopInvariants,
                         .noLoopMeasures, .noPrecondsFromFuncs, .noNondetGuards,
                         .noInternalFuncDecl, .noPolymorphicProcedures,
                         .noPolymorphicFunctions])
    fun prog =>
      runProgramUntil (ProcedureInlining.inlineCallCmd (doInline := opts.doInline)) prog opts.maxIters

end Core

end -- public section
