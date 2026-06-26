/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Backends.CBMC.CollectSymbols
import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOPipeline
import Strata.Backends.CBMC.GOTO.CoreToGOTOPipeline
import StrataDDM.Integration.Lean.HashCommands
import Strata.Languages.Core.DDMTransform.Translate
import Lean.Server.Utils

/-! ## Equivalence tests: direct path vs. CFG path

Run both `procedureToGotoCtx` (direct) and `procedureToGotoCtxViaCFG` (CFG)
on the same programs and compare outputs.

The CFG path produces additional GOTO instructions for explicit block-to-block
transfers that the direct path handles implicitly via fall-through. Comparisons
therefore focus on **semantic** instructions (DECL, ASSIGN, ASSERT, ASSUME,
FUNCTION_CALL, END_FUNCTION) and contract annotations, ignoring cosmetic GOTO
and LOCATION differences.
-/

open Strata

private def translateCore (p : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-! ### Instruction-level comparison helpers -/

private def isSemanticInst (inst : CProverGOTO.Instruction) : Bool :=
  match inst.type with
  | .DECL | .ASSIGN | .ASSERT | .ASSUME | .FUNCTION_CALL
  | .SET_RETURN_VALUE | .END_FUNCTION => true
  | _ => false

private def compareSemanticInstructions
    (directInsts cfgInsts : Array CProverGOTO.Instruction)
    : Except String Unit := do
  let dSemantic := directInsts.filter isSemanticInst
  let cSemantic := cfgInsts.filter isSemanticInst
  if dSemantic.size != cSemantic.size then
    throw s!"Semantic instruction count mismatch: direct={dSemantic.size} cfg={cSemantic.size}"
  for i in List.range dSemantic.size do
    if dSemantic[i]!.type != cSemantic[i]!.type then
      throw s!"Semantic instruction type mismatch at index {i}: \
               direct={dSemantic[i]!.type} cfg={cSemantic[i]!.type}"
  return ()

/-! ### Pipeline runners -/

private def runDirectPipeline (cprog : Core.Program) (procName : String := "main")
    : Except Std.Format (CoreToGOTO.CProverGOTO.Context × List Core.Function) := do
  let Env := Lambda.TEnv.default
  let procs := cprog.decls.filterMap fun d => d.getProc?
  let axioms := cprog.decls.filterMap fun d => d.getAxiom?
  let distincts := cprog.decls.filterMap fun d => match d with
    | .distinct name es _ => some (name, es) | _ => none
  let some proc := procs.find? (fun p => Core.CoreIdent.toPretty p.header.name == procName)
    | .error f!"procedure {procName} not found"
  procedureToGotoCtx Env proc (axioms := axioms) (distincts := distincts)

private def runCFGPipeline (cprog : Core.Program) (procName : String := "main")
    : Except Std.Format (CoreToGOTO.CProverGOTO.Context × List Core.Function) := do
  let Env := Lambda.TEnv.default
  let procs := cprog.decls.filterMap fun d => d.getProc?
  let axioms := cprog.decls.filterMap fun d => d.getAxiom?
  let distincts := cprog.decls.filterMap fun d => match d with
    | .distinct name es _ => some (name, es) | _ => none
  let some proc := procs.find? (fun p => Core.CoreIdent.toPretty p.header.name == procName)
    | .error f!"procedure {procName} not found"
  procedureToGotoCtxViaCFG Env proc (axioms := axioms) (distincts := distincts)

private def toJson (ctx : CoreToGOTO.CProverGOTO.Context) (pname : String)
    : Except Std.Format (Lean.Json × Lean.Json) := do
  let json ← (CoreToGOTO.CProverGOTO.Context.toJson pname ctx).mapError (fun e => f!"{e}")
  return (json.symtab, json.goto)

/-- Run both pipelines and compare semantic instructions + contracts + JSON validity. -/
private def testEquivalence (prog : StrataDDM.Program) (procName : String := "main")
    : IO Unit := do
  let cprog := translateCore prog
  let directResult := runDirectPipeline cprog procName
  let cfgResult := runCFGPipeline cprog procName
  match directResult, cfgResult with
  | .error e, _ => IO.throwServerError s!"Direct pipeline failed: {e}"
  | _, .error e => IO.throwServerError s!"CFG pipeline failed: {e}"
  | .ok (dctx, _), .ok (cctx, _) =>
    -- Instruction-level: compare semantic instructions (ignoring GOTO/LOCATION)
    match compareSemanticInstructions dctx.program.instructions cctx.program.instructions with
    | .error e => IO.throwServerError s!"Instruction mismatch: {e}"
    | .ok () => pure ()
    -- Contract annotations must match
    if dctx.contracts.length != cctx.contracts.length then
      IO.throwServerError s!"Contract count mismatch: direct={dctx.contracts.length} cfg={cctx.contracts.length}"
    for (dk, dv) in dctx.contracts do
      match cctx.contracts.find? (·.1 == dk) with
      | some (_, cv) =>
        if dv != cv then
          IO.throwServerError s!"Contract value mismatch for {dk}"
      | none =>
        IO.throwServerError s!"Contract key {dk} missing from CFG path"
    -- JSON-level: both produce valid, non-null output
    let pname := "main"
    match toJson dctx pname, toJson cctx pname with
    | .error e, _ => IO.throwServerError s!"Direct JSON failed: {e}"
    | _, .error e => IO.throwServerError s!"CFG JSON failed: {e}"
    | .ok (dSym, dGoto), .ok (cSym, cGoto) =>
      assert! dSym != Lean.Json.null
      assert! cSym != Lean.Json.null
      assert! dGoto != Lean.Json.null
      assert! cGoto != Lean.Json.null

-------------------------------------------------------------------------------

-- Test 1: Simple assert
def CFGEq_SimpleAssert :=
#strata
program Core;
procedure main(x : int) {
  assert (x > 0);
};
#end

#eval testEquivalence CFGEq_SimpleAssert

-------------------------------------------------------------------------------

-- Test 2: Variable declaration and assignment
def CFGEq_VarDeclAssign :=
#strata
program Core;
procedure main(x : int) {
  var z : int := x + 1;
  assert (z > 0);
};
#end

#eval testEquivalence CFGEq_VarDeclAssign

-------------------------------------------------------------------------------

-- Test 3: If-then-else
def CFGEq_IfThenElse :=
#strata
program Core;
procedure main(x : int) {
  var r : int;
  if (x > 0) {
    r := 1;
  } else {
    r := 0;
  }
  assert (r >= 0);
};
#end

#eval testEquivalence CFGEq_IfThenElse

-------------------------------------------------------------------------------

-- Test 4: Preconditions and postconditions
def CFGEq_Contracts :=
#strata
program Core;
procedure main(x : int)
spec {
  requires (x > 0);
  ensures (x >= 0);
} {
  assert (x > 0);
};
#end

#eval testEquivalence CFGEq_Contracts

-------------------------------------------------------------------------------

-- Test 5: Axioms and distinct declarations
def CFGEq_AxiomDistinct :=
#strata
program Core;
const a : int;
const b : int;
axiom [ax1]: (a > 0);
distinct [ab]: [a, b];
procedure main() {
  assert (a != b);
};
#end

#eval testEquivalence CFGEq_AxiomDistinct

-------------------------------------------------------------------------------

-- Test 6: Free specs are skipped (same in both paths)
def CFGEq_FreeSpecs :=
#strata
program Core;
procedure main(x : int)
spec {
  free requires (x > 10);
  requires (x >= 0);
  free ensures (x > 5);
  ensures (x >= 0);
} {
  assert (x >= 0);
};
#end

#eval testEquivalence CFGEq_FreeSpecs

-------------------------------------------------------------------------------

-- Test 7: Cover command
def CFGEq_Cover :=
#strata
program Core;
procedure main(x : int) {
  cover (x > 0);
};
#end

#eval testEquivalence CFGEq_Cover

-------------------------------------------------------------------------------

-- Test 8: Bitvector operations
def CFGEq_BVOps :=
#strata
program Core;
procedure main(x : bv32, y : bv32) {
  var z : bv32 := x + y;
  assert (z > bv{32}(0));
};
#end

#eval testEquivalence CFGEq_BVOps

-------------------------------------------------------------------------------

-- Test 9: Assume command
def CFGEq_Assume :=
#strata
program Core;
procedure main(x : int) {
  assume (x > 0);
  assert (x > 0);
};
#end

#eval testEquivalence CFGEq_Assume

-------------------------------------------------------------------------------

-- Test 10: Multiple sequential commands
def CFGEq_MultipleCommands :=
#strata
program Core;
procedure main(x : int) {
  var a : int := x + 1;
  var b : int := a + 2;
  assert (b > x);
};
#end

#eval testEquivalence CFGEq_MultipleCommands

-------------------------------------------------------------------------------

-- Test 11: CFG path only — verify the CFG-only pipeline produces valid output
-- (no direct path comparison since .cfg bodies aren't supported by the direct path)
#eval do
  let prog :=
    #strata
    program Core;
    procedure main(x : int) {
      var r : int;
      if (x > 0) {
        r := 1;
      } else {
        r := 0;
      }
      assert (r >= 0);
    };
    #end
  let cprog := translateCore prog
  match runCFGPipeline cprog with
  | .error e => IO.throwServerError s!"CFG pipeline failed: {e}"
  | .ok (ctx, _) =>
    match toJson ctx "main" with
    | .error e => IO.throwServerError s!"JSON failed: {e}"
    | .ok (symtab, goto) =>
      assert! symtab != Lean.Json.null
      assert! goto != Lean.Json.null
      let gotoStr := goto.pretty
      assert! (gotoStr.splitOn "GOTO").length > 1
      assert! (gotoStr.splitOn "ASSERT").length > 1
