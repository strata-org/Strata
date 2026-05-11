/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.FilterProcedures
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


/-- A pass is *analysis-preserving* for the call graph if, when the input
    state has a well-formed cached call graph, the output state's cached call
    graph (if present) is well-formed w.r.t. the output program.

    The pass takes a program and runs in `CoreTransformM`, which threads
    `CoreTransformState` containing `cachedAnalyses.callGraph`. -/
def AnalysisPreserving (pass : Program → Transform.CoreTransformM Program) : Prop :=
  ∀ (prog : Program) (st : Transform.CoreTransformState) (prog' : Program)
    (st' : Transform.CoreTransformState) (cg : CallGraph) (cg' : CallGraph),
    st.cachedAnalyses.callGraph = .some cg →
    CallGraphWF cg prog →
    (pass prog).run st = (.ok prog', st') →
    st'.cachedAnalyses.callGraph = .some cg' →
    CallGraphWF cg' prog'


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

end FilterProcedures

end Core

end -- public section
