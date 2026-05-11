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

/-! ## FilterProcedures — Structural Properties -/

namespace FilterProcedures

/-- The set of procedure names in a program. -/
def programProcNames (prog : Program) : List String :=
  prog.decls.filterMap fun
    | .proc p _ => some (CoreIdent.toPretty p.header.name)
    | _ => none

/-- The set of non-procedure declarations in a program. -/
def nonProcDecls (prog : Program) : List Decl :=
  prog.decls.filter fun d => d.kind ≠ .proc

/-- **Subset property**: Every procedure in the output was in the input. -/
def ProcedureSubset (progIn progOut : Program) : Prop :=
  ∀ (d : Decl), d ∈ progOut.decls → d.kind = .proc → d ∈ progIn.decls

/-- **Non-procedure preservation**: All non-procedure declarations are
    preserved verbatim and in the same relative order. -/
def NonProcDeclsPreserved (progIn progOut : Program) : Prop :=
  nonProcDecls progOut = nonProcDecls progIn

/-- **Target inclusion**: Every target procedure that exists in the input
    appears in the output. -/
def TargetsRetained (progIn progOut : Program) (targets : List String) : Prop :=
  ∀ name ∈ targets,
    name ∈ programProcNames progIn →
    name ∈ programProcNames progOut

/-- **Transitive closure completeness**: If a procedure is in the output,
    all procedures it calls (transitively) that exist in the input are
    also in the output. -/
def CalleesClosed (progOut : Program) (cg : CallGraph) : Prop :=
  ∀ name ∈ programProcNames progOut,
    ∀ callee ∈ cg.getCalleesClosure name,
      callee ∈ programProcNames progOut

/-- **noFilter respect**: When `respectNoFilter = Bool.true`, procedures marked
    with `noFilter := Bool.true` in the input are always retained. -/
def NoFilterRespected (progIn progOut : Program) : Prop :=
  ∀ (proc : Procedure) (md : MetaData Expression),
    (Decl.proc proc md) ∈ progIn.decls →
    proc.header.noFilter = Bool.true →
    (Decl.proc proc md) ∈ progOut.decls

/-- **Body preservation**: Retained procedures have their bodies unchanged. -/
def BodiesPreserved (progIn progOut : Program) : Prop :=
  ∀ (proc : Procedure) (md : MetaData Expression),
    (Decl.proc proc md) ∈ progOut.decls →
    (Decl.proc proc md) ∈ progIn.decls

/-- **Idempotence of the target set w.r.t. the output**: Running
    FilterProcedures on the output with the same targets produces an
    identical program (since nothing further can be removed). -/
def FilterIdempotent (progOut : Program) (targets : List String) (cg : CallGraph) : Prop :=
  let neededNames := (targets ++ cg.getAllCalleesClosure targets).dedup
  ∀ name ∈ programProcNames progOut,
    name ∈ neededNames

/-! ## FilterProcedures — Composite Correctness -/

/-- The full structural correctness of a single FilterProcedures invocation.
    This bundles all the individual properties into one record. -/
structure FilterCorrect
    (progIn progOut : Program)
    (targets : List String)
    (cgIn : CallGraph)
    (respectNoFilter : Bool) : Prop where
  /-- Output procedures are a subset of input procedures. -/
  subset : ProcedureSubset progIn progOut
  /-- Non-procedure declarations are unchanged. -/
  nonProcsPreserved : NonProcDeclsPreserved progIn progOut
  /-- Targets (that exist) are retained. -/
  targetsRetained : TargetsRetained progIn progOut targets
  /-- The output is closed under the call graph. -/
  calleesClosed : CalleesClosed progOut cgIn
  /-- Procedure bodies are not modified. -/
  bodiesPreserved : BodiesPreserved progIn progOut
  /-- When respectNoFilter, noFilter procedures survive. -/
  noFilterRespected : respectNoFilter = Bool.true → NoFilterRespected progIn progOut

/-! ## FilterProcedures — Semantic Correctness

The key semantic insight: FilterProcedures is correct because the procedures
it removes are *unreachable* from the targets. Since Strata's verification is
per-procedure (each procedure is verified independently against its own spec),
removing unreachable procedures cannot affect the correctness of remaining ones.

More precisely: `ProcedureCorrect π φ proc p` depends on `π` (the procedure
environment used for call resolution). FilterProcedures preserves correctness
because for any retained procedure, all procedures it can call are also
retained — so the relevant fragment of `π` is unchanged.
-/

/-- The procedure-lookup function restricted to a program's declarations. -/
def procLookup (prog : Program) (name : String) : Option Procedure :=
  prog.decls.findSome? fun
    | .proc p _ => if CoreIdent.toPretty p.header.name = name then some p else none
    | _ => none

/-- **Semantic preservation for retained procedures**: For any procedure
    retained in the output, its lookup environment (for resolving calls)
    is identical when restricted to reachable callees.

    This is the key lemma: if `proc` is in `progOut` and `progOut` is
    callee-closed, then for any callee `c` reachable from `proc`:
      `procLookup progOut c = procLookup progIn c`

    Since `ProcedureCorrect` only depends on the procedure environment for
    resolving calls that can actually be reached, this gives us semantic
    preservation. -/
def CalleeEnvPreserved (progIn progOut : Program) (cg : CallGraph) : Prop :=
  ∀ name ∈ programProcNames progOut,
    ∀ callee ∈ name :: cg.getCalleesClosure name,
      procLookup progOut callee = procLookup progIn callee

/-- **Full correctness**: structural properties + semantic preservation. -/
structure FilterFullCorrect
    (progIn progOut : Program)
    (targets : List String)
    (cgIn : CallGraph)
    (respectNoFilter : Bool) : Prop where
  /-- Structural correctness. -/
  structural : FilterCorrect progIn progOut targets cgIn respectNoFilter
  /-- The callee lookup environment is preserved for retained procedures. -/
  envPreserved : CalleeEnvPreserved progIn progOut cgIn

/-! ## CallGraph — Properties Under FilterProcedures

These characterize how the call graph produced by FilterProcedures relates to
the input call graph. -/

/-- The filtered call graph is a subgraph of the input call graph restricted
    to the retained procedure names. -/
def FilteredCGIsSubgraph (cgIn cgOut : CallGraph) (retained : List String) : Prop :=
  (∀ name, cgOut.callees.contains name → name ∈ retained) ∧
  (∀ name, name ∈ retained → cgIn.callees.contains name → cgOut.callees.contains name) ∧
  (∀ (a b : String), ((cgOut.getCalleesWithCount a)[b]?).getD 0 ≤
                     ((cgIn.getCalleesWithCount a)[b]?).getD 0)

/-- If the input call graph is consistent with the input program, then
    the filtered call graph is consistent with the output program. -/
def FilterPreservesCGConsistency
    (cgIn : CallGraph) (progIn progOut : Program) (cgOut : CallGraph) : Prop :=
  CallGraphWF cgIn progIn → CallGraphWF cgOut progOut

end FilterProcedures

/-! ## Generic Pass Specification Template

This section provides a template structure for specifying future passes.
Each pass should define:
1. What structural properties it maintains
2. What semantic property it establishes or preserves
3. What analyses it depends on (and thus requires consistency of)
-/

/-- A pass is *analysis-preserving* for the call graph if, when given a
    consistent call graph, it produces a consistent call graph for the
    output program. -/
def AnalysisPreserving (pass : Program → CallGraph → Program × CallGraph) : Prop :=
  ∀ (prog : Program) (cg : CallGraph),
    CallGraphWF cg prog →
    let (prog', cg') := pass prog cg
    CallGraphWF cg' prog'

end Core

end -- public section
