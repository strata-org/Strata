/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Options
public import Strata.Languages.Core.ProgramEval
public import Strata.Languages.Core.ProgramType
public import Strata.Languages.Core.DDMTransform.ASTtoCST
public import Strata.Languages.Core.Statistics

---------------------------------------------------------------------

namespace Core
open Strata

public section

/-!
## Differences between Boogie and Strata.Core

1. Strata.Core does not have global variables.

2. Unlike Boogie, Strata.Core is sensitive to global declaration order. E.g.,
   a function must be declared before it can be used in a procedure.

3. Strata.Core does not (yet) support polymorphism.

4. Strata.Core supports `exit` statements that exit the nearest enclosing
   block with a matching label (or the nearest block if no label is given).
   Strata does not support arbitrary `goto` statements.

5. Strata.Core does not support `where` clauses and `unique` constants,
   requiring a tool like `BoogieToStrata` to desugar them.
-/

def typeCheck (options : VerifyOptions) (program : Program)
    (moreFns : Lambda.Factory CoreLParams := Lambda.Factory.default) :
    Except DiagnosticModel Program := do
  let T := Lambda.TEnv.default
  let factory ← Core.Factory.addFactory moreFns
  let C := { Lambda.LContext.default with
                functions := factory,
                knownTypes := Core.KnownTypes }
  match Factory.typeCheck C T with
  | .error k =>
    -- TODO: DiagnosticModel for functions defined in Factory?
    throw (DiagnosticModel.fromFormat k)
  | .ok T =>
    let (program, _T) ← Program.typeCheck C T program
    -- dbg_trace f!"[Strata.Core] Annotated program:\n{program}"
    if options.verbose >= .normal then dbg_trace f!"[Strata.Core] Type checking succeeded.\n"
    return program

def formatProofObligation (ob : Imperative.ProofObligation Expression) :
    Std.Format :=
  let assumptionPairs := ob.assumptions.flatMap (·.toList)
  let assumptionFmt := assumptionPairs.map fun (label, expr) =>
    f!"{label}: {Core.formatExprs [expr]}"
  let assumptionLine := if assumptionPairs.isEmpty then f!""
                        else f!"\nAssumptions:\n{Std.Format.joinSep assumptionFmt "\n"}"
  f!"Label: {ob.label}\n\
     Property: {ob.property}{assumptionLine}\n\
     Obligation:\n{Core.formatExprs [ob.obligation]}\n"

def formatProofObligations (obs : Array (Imperative.ProofObligation Expression)) :
    Std.Format :=
  Std.Format.joinSep (obs.toList.map formatProofObligation) "\n"

def typeCheckAndEval (options : VerifyOptions) (program : Program)
    (moreFns : Lambda.Factory CoreLParams := Lambda.Factory.default) :
    Except DiagnosticModel ((List Env) × Statistics) := do
  let factory ← Core.Factory.addFactory moreFns
  let program ← typeCheck options program moreFns
  let datatypes := program.decls.filterMap fun decl =>
    match decl with
    | .type (.data d) _ => some d
    | _ => none
  let σ ← (Lambda.LState.init).addFactory factory
  let E := { Env.init with exprEnv := σ, program := program, pathCap := options.pathCap }
  let E ← E.addDatatypes datatypes

  -- Collect declaration statistics
  let stats := program.decls.foldl (fun s d =>
    match d with
    | .type _ _          => s.increment s!"{Evaluator.Stats.typeDecls}"
    | .ax _ _            => s.increment s!"{Evaluator.Stats.axioms}"
    | .distinct _ _ _    => s.increment s!"{Evaluator.Stats.distincts}"
    | .proc _ _          => s.increment s!"{Evaluator.Stats.procedures}"
    | .func _ _          => s.increment s!"{Evaluator.Stats.functions}"
    | .recFuncBlock fs _ => s.increment s!"{Evaluator.Stats.recursiveFunctions}" fs.length)
    ({} : Statistics)

  let stats := stats.increment s!"{Evaluator.Stats.factoryOps}" factory.toArray.size
  let (pEs, evalStats) ← Program.eval E
  -- Note: all .program fields in pEs will have identical values, because
  -- Program.eval does not modify the program. The Program field is
  -- kept for convenience.
  let stats := stats.merge evalStats
  let stats := stats.increment s!"{Evaluator.Stats.verificationEnvironments}" pEs.length

  if options.verbose >= .normal then do
    dbg_trace f!"{Std.Format.line}VCs:"
    for E in pEs do
      dbg_trace f!"{formatProofObligations E.deferred}"
  return (pEs, stats)

end -- public section

end Core

---------------------------------------------------------------------
