/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.FilterProcedures
public import Strata.Transform.PrecondElim
public import Strata.Transform.CoreSpecification

/-! # Pass-Specific Correctness Specifications

This file defines pass-specific correctness properties that go beyond the
generic `Overapproximates` (semantic preservation) predicate. These capture
structural invariants particular to each transformation pass.

## FilterProcedures

FilterProcedures removes unreachable procedures from a program given a set of
target entry points. Its correctness involves:
1. Declaration-level properties (what is kept/removed)
2. CallGraph consistency (the cached CG faithfully represents the output)
3. Semantic irrelevance of removed procedures (the removed procedures do not
   affect the verification of the retained ones)

## CallGraph Preservation

Several passes depend on a correct CallGraph. We define what it means for a
CallGraph to be consistent with a program, enabling compositional reasoning
about passes that consume or produce call graphs.
-/

public section

namespace Core

open Core Imperative

/-! ## Well-formedness of CallGraph -/

def CalleesCountEqual (calleeMap : Std.HashMap String Nat) (proc : Procedure) :=
  ∀ callee : String,
    calleeMap[callee]?.getD 0 = (extractCallsFromProcedure proc).count callee

structure CallGraphWF (cg : CallGraph) (prog : Program) : Prop where
  sound : ∀ (caller : String) (k : Std.HashMap String Nat),
    cg.callees[caller]? = .some k →
    ∃ (p : Procedure) (_md : MetaData Expression),
      (.proc p _md) ∈ prog.decls ∧
      CoreIdent.toPretty p.header.name = caller ∧
      CalleesCountEqual k p

  complete : ∀ (p : Procedure) (_md : MetaData Expression),
    (.proc p _md) ∈ prog.decls →
    ∃ (k : Std.HashMap String Nat),
      cg.callees[CoreIdent.toPretty p.header.name]? = .some k ∧
      CalleesCountEqual k p

  /-- No entry in the maps has a zero count. -/
  noZeroCount :
    (∀ (a b : String) (k : Std.HashMap String Nat) (n : Nat),
      cg.callees[a]? = .some k → k[b]? = some n → n ≠ 0)

  /-- callers is the transpose of callees. -/
  callersTranspose : ∀ (a b : String) (n : Nat),
    (∃ (k : Std.HashMap String Nat), cg.callees[a]? = .some k ∧ k[b]? = .some n) ↔
    (∃ (k : Std.HashMap String Nat), cg.callers[b]? = .some k ∧ k[a]? = .some n)

theorem CallGraphWF.noZeroCountCallers {cg : CallGraph} {prog : Program}
    (wf : CallGraphWF cg prog)
    (a b : String) (k : Std.HashMap String Nat) (n : Nat)
    (hk : cg.callers[b]? = .some k) (hn : k[a]? = some n) : n ≠ 0 := by
  have ⟨k', hk', hn'⟩ := wf.callersTranspose a b n |>.mpr ⟨k, hk, hn⟩
  exact wf.noZeroCount a b k' n hk' hn'


/-- A pass is *analysis-preserving* for the call graph: for any successful
    execution, if the input cached call graph is well-formed w.r.t. the input
    program, then the output cached call graph is well-formed w.r.t. the
    output program. -/
def PreservesCachedAnalysesWF
    (pass : Program → Transform.CoreTransformM (Bool × Program)) : Prop :=
  ∀ (progIn : Program) (st : Transform.CoreTransformState)
    (changed : Bool) (progOut : Program) (st' : Transform.CoreTransformState),
    (pass progIn).run st = (.ok (changed, progOut), st') →
    ∀ (cgIn : CallGraph),
      st.cachedAnalyses.callGraph = .some cgIn →
      CallGraphWF cgIn progIn →
      ∀ (cgOut : CallGraph),
        st'.cachedAnalyses.callGraph = .some cgOut →
        CallGraphWF cgOut progOut

/-- The `changed` flag returned by a pass is faithful: true iff the output
    program differs from the input. -/
def ChangedFlagValid
    (pass : Program → Transform.CoreTransformM (Bool × Program)) : Prop :=
  ∀ (progIn : Program) (st : Transform.CoreTransformState)
    (changed : Bool) (progOut : Program) (st' : Transform.CoreTransformState),
    (pass progIn).run st = (.ok (changed, progOut), st') →
    (changed = Bool.true ↔ progOut ≠ progIn)


/-! ## FilterProcedures — Structural Properties -/

namespace FilterProcedures

/-- The set of procedure names in a program. -/
def programProcNames (prog : Program) : List String :=
  prog.decls.filterMap fun
    | .proc p _ => some (CoreIdent.toPretty p.header.name)
    | _ => none

structure FilterCorrect
    (progIn progOut : Program)
    (targets : List String)
    (cgIn : CallGraph)
    (respectNoFilter : Bool) : Prop where
  /-- The output declarations are a sublist of the input declarations:
      same elements in the same relative order, with only some procedures
      removed. This subsumes subset, nonProcsPreserved, bodiesPreserved,
      and ordering preservation in a single statement. -/
  declsSublist : progOut.decls.Sublist progIn.decls

  /-- Every target procedure that exists in the input appears in the output. -/
  targetsRetained : ∀ name ∈ targets,
    name ∈ programProcNames progIn →
    name ∈ programProcNames progOut

  /-- The output is closed under the call graph: if a procedure is retained,
      all its transitive callees are also retained. -/
  calleeClosureRetained : ∀ name ∈ programProcNames progOut,
    ∀ callee ∈ cgIn.getCalleesClosure name,
      callee ∈ programProcNames progOut

  /-- Only procedures are removed (non-procedure declarations are never dropped). -/
  onlyProcsRemoved : ∀ (d : Decl),
    d ∈ progIn.decls → d.kind ≠ .proc → d ∈ progOut.decls

  /-- Procedures unreachable from the target closure are removed, unless they
      have `noFilter = true` and `respectNoFilter` is set. -/
  unreachableRemoved : ∀ (proc : Procedure) (md md' : MetaData Expression),
    (Decl.proc proc md) ∈ progIn.decls →
    CoreIdent.toPretty proc.header.name ∉
      (targets ++ cgIn.getAllCalleesClosure targets) →
    (Decl.proc proc md' ∉ progOut.decls ∨
      (respectNoFilter = Bool.true ∧ proc.header.noFilter = Bool.true))

/-- Phase-level correctness for FilterProcedures: structural correctness
    for every successful execution, plus call graph preservation. -/
structure FilterProcedurePhaseCorrect
    (targets : List String)
    (respectNoFilter : Bool) : Prop where
  filterCorrect :
    ∀ (progIn : Program) (st : Transform.CoreTransformState)
      (changed : Bool) (progOut : Program) (st' : Transform.CoreTransformState)
      (cgIn : CallGraph),
      st.cachedAnalyses.callGraph = .some cgIn →
      ((filterProceduresPipelinePhase targets respectNoFilter).transform progIn).run st =
        (.ok (changed, progOut), st') →
      FilterCorrect progIn progOut targets cgIn respectNoFilter

  changedFlagValid :
    ChangedFlagValid
      (filterProceduresPipelinePhase targets respectNoFilter).transform

  analysisPreserving :
    PreservesCachedAnalysesWF
      (filterProceduresPipelinePhase targets respectNoFilter).transform

end FilterProcedures


/-! ## PrecondElim — Structural Properties -/

namespace PrecondElim

/-- Program-level structural correctness of PrecondElim. -/
structure PrecondElimCorrect (progIn progOut : Program) : Prop where
  /-- Generated `$$wf` procedures have `noFilter := true` and empty specs. -/
  generatedWF : ∀ (proc : Procedure) (md : MetaData Expression),
    (Decl.proc proc md) ∈ progOut.decls →
    (CoreIdent.toPretty proc.header.name).endsWith wfSuffix →
    proc.header.noFilter = Bool.true ∧
    proc.spec.preconditions = [] ∧
    proc.spec.postconditions = []

  /-- All functions in the output have empty preconditions. -/
  preconditionsStripped :
    (∀ (func : Function) (md : MetaData Expression),
      (Decl.func func md) ∈ progOut.decls →
      func.preconditions = []) ∧
    (∀ (fs : List Function) (md : MetaData Expression),
      (Decl.recFuncBlock fs md) ∈ progOut.decls →
      ∀ f ∈ fs, f.preconditions = [])

  /-- Non-procedure/function declarations pass through (types, axioms, distincts). -/
  nonProcDeclsPreserved : ∀ (d : Decl),
    d ∈ progIn.decls → d.kind = .type ∨ d.kind = .ax ∨ d.kind = .distinct →
    d ∈ progOut.decls

  /-- Original procedures are preserved (same name and spec, body may grow). -/
  proceduresPreserved : ∀ (proc : Procedure) (md : MetaData Expression),
    (Decl.proc proc md) ∈ progIn.decls →
    ∃ (proc' : Procedure) (md' : MetaData Expression),
      (Decl.proc proc' md') ∈ progOut.decls ∧
      proc'.header.name = proc.header.name ∧
      proc'.spec = proc.spec

  /-- Original functions are preserved (same name/body/signature, preconditions stripped). -/
  functionsPreserved : ∀ (func : Function) (md : MetaData Expression),
    (Decl.func func md) ∈ progIn.decls →
    ∃ (func' : Function) (md' : MetaData Expression),
      (Decl.func func' md') ∈ progOut.decls ∧
      func'.name = func.name ∧
      func'.preconditions = [] ∧
      func'.body = func.body ∧
      func'.inputs = func.inputs ∧
      func'.output = func.output

  /-- No declarations are removed from the input. -/
  noDeclsRemoved : ∀ (d : Decl),
    d ∈ progIn.decls →
    ∃ (d' : Decl), d' ∈ progOut.decls ∧ d'.name = d.name

  /-- The relative order of input declarations is preserved in the output.
      (New `$$wf` procedures may be interleaved.) -/
  orderPreserved :
    (progIn.decls.map Decl.name).Sublist (progOut.decls.map Decl.name)

/-- Factory-level correctness of PrecondElim. -/
structure PrecondElimFactoryCorrect
    (progOut : Program)
    (stIn stOut : Transform.CoreTransformState) : Prop where
  /-- The output Factory grows from the input Factory. -/
  factoryGrows : ∀ (fIn : @Lambda.Factory CoreLParams) (fOut : @Lambda.Factory CoreLParams),
    stIn.factory = .some fIn →
    stOut.factory = .some fOut →
    ∀ (name : String), name ∈ fIn → name ∈ fOut

  /-- The output Factory contains all declared functions. -/
  factoryComplete : ∀ (fOut : @Lambda.Factory CoreLParams),
    stOut.factory = .some fOut →
    (∀ (func : Function) (md : MetaData Expression),
      (Decl.func func md) ∈ progOut.decls →
      func.name.name ∈ fOut) ∧
    (∀ (fs : List Function) (md : MetaData Expression),
      (Decl.recFuncBlock fs md) ∈ progOut.decls →
      ∀ f ∈ fs, f.name.name ∈ fOut)

  /-- Preconditions are empty in the output Factory. -/
  factoryStripped : ∀ (fOut : @Lambda.Factory CoreLParams),
    stOut.factory = .some fOut →
    ∀ (name : String) (h : name ∈ fOut), (fOut[name]).preconditions = []

/-- Phase-level correctness for PrecondElim: program correctness and
    factory correctness for every successful execution, plus call graph
    preservation. -/
structure PrecondElimPhaseCorrect : Prop where
  precondElimCorrect :
    ∀ (progIn : Program) (st : Transform.CoreTransformState)
      (changed : Bool) (progOut : Program) (st' : Transform.CoreTransformState),
      (precondElimPipelinePhase.transform progIn).run st =
        (.ok (changed, progOut), st') →
      PrecondElimCorrect progIn progOut

  factoryCorrect :
    ∀ (progIn : Program) (st : Transform.CoreTransformState)
      (changed : Bool) (progOut : Program) (st' : Transform.CoreTransformState),
      (precondElimPipelinePhase.transform progIn).run st =
        (.ok (changed, progOut), st') →
      PrecondElimFactoryCorrect progOut st st'

  changedFlagValid :
    ChangedFlagValid precondElimPipelinePhase.transform

  analysisPreserving :
    PreservesCachedAnalysesWF precondElimPipelinePhase.transform

end PrecondElim

end Core

end -- public section
