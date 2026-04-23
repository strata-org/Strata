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

/-- Build an evaluation environment from a program.
    Loads the factory, datatypes, and processes all declarations.
    When `registerCustomFunctions` is true, also loads function declarations,
    distinct constraints, and local function declarations from procedure
    bodies into the factory (needed for SMT encoding). -/
def buildEnv (options : VerifyOptions) (program : Program)
    (moreFns : Lambda.Factory CoreLParams := Lambda.Factory.default)
    (registerCustomFunctions : Bool := false) :
    Except DiagnosticModel (Env × Statistics) := do
  let factory ← Core.Factory.addFactory moreFns
  let σ ← (Lambda.LState.init).addFactory factory
  let datatypes := program.decls.filterMap fun decl =>
    match decl with | .type (.data d) _ => some d | _ => none
  let mut E : Env := { Env.init with exprEnv := σ, program := program, pathCap := options.pathCap }
  E ← E.addDatatypes datatypes

  if registerCustomFunctions then
    for decl in program.decls do
      match decl with
      | .func func _ => E ← E.addFactoryFunc func
      | .recFuncBlock funcs _ =>
        validateCasesTypes funcs E.datatypes
        for func in funcs do E ← E.addFactoryFunc func
      | .distinct _ es _ => E := { E with distinct := es :: E.distinct }
      | .proc proc _ =>
        for stmt in proc.body.flatMap collectFuncDecls do
          match E.exprEnv.addFactoryFunc stmt with
          | .ok σ' => E := { E with exprEnv := σ' }
          | .error _ => pure ()
      | _ => pure ()

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
  return (E, stats)
where
  collectFuncDecls : Statement → List (@Lambda.LFunc CoreLParams)
    | .funcDecl decl _ => [{
        name := decl.name, typeArgs := decl.typeArgs, isConstr := decl.isConstr,
        inputs := decl.inputs.map (fun (id, ty) => (id, Lambda.LTy.toMonoTypeUnsafe ty)),
        output := Lambda.LTy.toMonoTypeUnsafe decl.output,
        body := decl.body, attr := decl.attr,
        concreteEval := decl.concreteEval, axioms := decl.axioms }]
    | .block _ ss _ => ss.flatMap collectFuncDecls
    | .ite _ tss ess _ => tss.flatMap collectFuncDecls ++ ess.flatMap collectFuncDecls
    | .loop _ _ _ body _ => body.flatMap collectFuncDecls
    | _ => []

/-- Proof obligation program construction: Program → Program.
    Runs symbolic execution and converts obligations to a program
    suitable for downstream phases (ANF encoding, SMT encoding). -/
def toCoreProofObligationProgram (options : VerifyOptions) (program : Program)
    (moreFns : Lambda.Factory CoreLParams := Lambda.Factory.default) :
    Except DiagnosticModel (Program × Statistics) := do
  let (E, declStats) ← buildEnv options program moreFns
  let (pEs, evalStats) ← Program.eval E
  -- Note: all .program fields in pEs will have identical values, because
  -- Program.eval does not modify the program. The Program field is
  -- kept for convenience.
  let stats := declStats.merge evalStats
  let stats := stats.increment s!"{Evaluator.Stats.verificationEnvironments}" pEs.length

  -- Convert each Env's deferred obligations into a procedure body.
  -- The resulting program has type/datatype declarations preserved,
  -- but each procedure's body is replaced with the obligations tree
  -- (assume/assert blocks combined with if *). Axioms are inlined
  -- into each procedure's obligations (from E.deferred path conditions).
  -- Type/datatype declarations come from the original program.
  let typeDecls := program.decls.filter fun d =>
    match d with | .type _ _ => true | _ => false
  let procNames := program.decls.filterMap fun d =>
    match d with | .proc p _ => some p.header.name | _ => none
  let oblProcs := (pEs.zip procNames).map fun (E, procName) =>
    let blocks := E.deferred.toList.map fun ob =>
      let assumes := ob.assumptions.flatten.map fun (label, e) =>
        Imperative.Stmt.cmd (CmdExt.cmd (Imperative.Cmd.assume label e ob.metadata))
      let assertStmt := Imperative.Stmt.cmd (CmdExt.cmd (
        if ob.property == .cover
        then Imperative.Cmd.cover ob.label ob.obligation ob.metadata
        else Imperative.Cmd.assert ob.label ob.obligation ob.metadata))
      assumes ++ [assertStmt]
    let body := match blocks with
      | [] => []
      | [b] => b
      | b :: rest => rest.foldl (fun acc block =>
          [Imperative.Stmt.ite .nondet acc block .empty]) b
    let proc : Procedure := {
      header := { name := procName, typeArgs := [], inputs := [], outputs := [] },
      spec := { preconditions := [], postconditions := [] },
      body := body
    }
    Decl.proc proc .empty

  -- Include function declarations and distinct constraints from the
  -- evaluation environment so the obligations program is self-contained
  -- for downstream phases (ANF encoding, SMT encoding).
  let postEvalEnv := pEs.head?.getD E
  -- Get functions added during evaluation (not in the initial factory)
  let initialFactorySize := E.exprEnv.config.factory.toArray.size
  let evalFuncs := postEvalEnv.exprEnv.config.factory.toArray.toList.drop initialFactorySize
  let funcDecls := evalFuncs.map fun func => Decl.func func .empty
  let distinctDecls := postEvalEnv.distinct.mapIdx fun i es =>
    Decl.distinct s!"distinct_{i}" es .empty
  let oblProgram : Program := { decls := typeDecls ++ funcDecls ++ distinctDecls ++ oblProcs }

  if options.verbose >= .normal then do
    dbg_trace f!"{Std.Format.line}VCs:"
    for E in pEs do
      dbg_trace f!"{formatProofObligations E.deferred}"
  return (oblProgram, stats)


/-- Convenience: type check then symbolic eval. -/
def typeCheckAndEval (options : VerifyOptions) (program : Program)
    (moreFns : Lambda.Factory CoreLParams := Lambda.Factory.default) :
    Except DiagnosticModel (Program × Statistics) := do
  let program ← typeCheck options program moreFns
  toCoreProofObligationProgram options program moreFns

end -- public section

end Core

---------------------------------------------------------------------
