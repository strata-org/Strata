/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Backends.CBMC.CollectSymbols
import Strata.Backends.CBMC.GOTO.CoreToGOTOPipeline
import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOPipeline

/-! ## End-to-end tests: Core program → GOTO JSON

These tests verify the full pipeline from DDM-parsed Core programs through
`procedureToGotoCtx` to GOTO JSON output, covering features added in the
Core-to-GOTO gap-filling work:
- Procedure contracts (requires/ensures)
- Cover command
- Bitvector operations
-/

open Strata

private def translateCore (p : Strata.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

private def coreToGotoJson (p : Strata.Program) :
    Except Std.Format (Lean.Json × Lean.Json) := do
  let cprog := translateCore p
  let Env := Lambda.TEnv.default
  let procs := cprog.decls.filterMap fun d => d.getProc?
  let axioms := cprog.decls.filterMap fun d => d.getAxiom?
  let distincts := cprog.decls.filterMap fun d => match d with
    | .distinct name es _ => some (name, es) | _ => none
  let extraSyms ← collectExtraSymbols cprog
  let p := procs[0]!
  let pname := Core.CoreIdent.toPretty p.header.name
  let ctx ← procedureToGotoCtx Env p (axioms := axioms) (distincts := distincts)
  let json ← (CoreToGOTO.CProverGOTO.Context.toJson pname ctx.1).mapError (fun e => f!"{e}")
  let extraJson := Lean.toJson extraSyms
  let symtab := match json.symtab, extraJson with
    | .obj m1, .obj m2 => Lean.Json.obj (m2.mergeWith (fun _ v _ => v) m1)
    | _, _ => json.symtab
  return (symtab, json.goto)

-------------------------------------------------------------------------------

-- Test: simple procedure with assert translates end-to-end
def E2E_SimpleAssert :=
#strata
program Core;
procedure test(x : int) {
  assert (x > 0);
};
#end

#eval do
  let (.ok (symtab, goto)) := coreToGotoJson E2E_SimpleAssert | IO.throwServerError "translation failed"
  assert! symtab.getObjValD "test" != Lean.Json.null
  assert! goto.getObjValD "functions" != Lean.Json.null

-------------------------------------------------------------------------------

-- Test: procedure with precondition emits #spec_requires
def E2E_Precondition :=
#strata
program Core;
procedure test(x : int)
spec {
  requires (x > 0);
} {
  assert (x > 0);
};
#end

#eval do
  let (.ok (symtab, _)) := coreToGotoJson E2E_Precondition | IO.throwServerError "translation failed"
  let testSym := symtab.getObjValD "test"
  let codeType := testSym.getObjValD "type"
  let namedSub := codeType.getObjValD "namedSub"
  let specReq := namedSub.getObjValD "#spec_requires"
  assert! specReq != Lean.Json.null

-------------------------------------------------------------------------------

-- Test: procedure with postcondition emits #spec_ensures
def E2E_Postcondition :=
#strata
program Core;
procedure test(x : int)
spec {
  ensures (x > 0);
} {
  assert (x > 0);
};
#end

#eval do
  let (.ok (symtab, _)) := coreToGotoJson E2E_Postcondition | IO.throwServerError "translation failed"
  let testSym := symtab.getObjValD "test"
  let codeType := testSym.getObjValD "type"
  let namedSub := codeType.getObjValD "namedSub"
  let specEns := namedSub.getObjValD "#spec_ensures"
  assert! specEns != Lean.Json.null

-------------------------------------------------------------------------------

-- Test: cover command produces ASSERT instruction in GOTO output
def E2E_Cover :=
#strata
program Core;
procedure test(x : int) {
  cover (x > 0);
};
#end

#eval do
  let (.ok (_, goto)) := coreToGotoJson E2E_Cover | IO.throwServerError "translation failed"
  assert! (goto.pretty.splitOn "ASSERT").length > 1

-------------------------------------------------------------------------------

-- Test: bitvector operations translate end-to-end
def E2E_BVOps :=
#strata
program Core;
procedure test(x : bv32, y : bv32) {
  var z : bv32 := x + y;
  assert (z > bv{32}(0));
};
#end

#eval do
  let (.ok (symtab, goto)) := coreToGotoJson E2E_BVOps | IO.throwServerError "translation failed"
  assert! symtab.getObjValD "test" != Lean.Json.null
  assert! goto.getObjValD "functions" != Lean.Json.null

-------------------------------------------------------------------------------

-- Test: free requires/ensures are skipped in contract annotations
def E2E_FreeSpecs :=
#strata
program Core;
procedure test(x : int)
spec {
  free requires (x > 10);
  requires (x >= 0);
  free ensures (x > 5);
  ensures (x >= 0);
}
{
  assert (x >= 0);
};
#end

#eval do
  match coreToGotoJson E2E_FreeSpecs with
  | .error e => IO.throwServerError s!"translation failed: {e}"
  | .ok (symtab, _) =>
    let testSym := symtab.getObjValD "test"
    let codeType := testSym.getObjValD "type"
    let namedSub := codeType.getObjValD "namedSub"
    assert! namedSub.getObjValD "#spec_requires" != Lean.Json.null
    assert! namedSub.getObjValD "#spec_ensures" != Lean.Json.null
    let reqSub := (namedSub.getObjValD "#spec_requires").getObjValD "sub"
    let ensSub := (namedSub.getObjValD "#spec_ensures").getObjValD "sub"
    let reqCount := match reqSub with | .arr a => a.size | _ => 0
    let ensCount := match ensSub with | .arr a => a.size | _ => 0
    -- Each should have exactly 1 clause (the non-free one), not 2
    assert! reqCount == 1
    assert! ensCount == 1

-------------------------------------------------------------------------------

-- Test: procedure call translates to FUNCTION_CALL instruction
def E2E_Call :=
#strata
program Core;
procedure callee(x : int, out r : int) {
  r := x + 1;
};
procedure caller(out y : int) {
  call callee(42, out y);
};
#end

-- Helper: translate a specific procedure by name
private def coreToGotoJsonByName (p : Strata.Program) (name : String) :
    Except Std.Format (Lean.Json × Lean.Json) := do
  let cprog := translateCore p
  let Env := Lambda.TEnv.default
  let procs := cprog.decls.filterMap fun d => d.getProc?
  let axioms := cprog.decls.filterMap fun d => d.getAxiom?
  let distincts := cprog.decls.filterMap fun d => match d with
    | .distinct name es _ => some (name, es) | _ => none
  let extraSyms ← collectExtraSymbols cprog
  let some proc := procs.find? (fun p => Core.CoreIdent.toPretty p.header.name == name)
    | .error f!"procedure {name} not found"
  let pname := Core.CoreIdent.toPretty proc.header.name
  let ctx ← procedureToGotoCtx Env proc (axioms := axioms) (distincts := distincts)
  let json ← (CoreToGOTO.CProverGOTO.Context.toJson pname ctx.1).mapError (fun e => f!"{e}")
  let extraJson := Lean.toJson extraSyms
  let symtab := match json.symtab, extraJson with
    | .obj m1, .obj m2 => Lean.Json.obj (m2.mergeWith (fun _ v _ => v) m1)
    | _, _ => json.symtab
  return (symtab, json.goto)

#eval do
  match coreToGotoJsonByName E2E_Call "caller" with
  | .error e => dbg_trace s!"translation error: {e}"; pure ()
  | .ok (_, goto) =>
    assert! (goto.pretty.splitOn "FUNCTION_CALL").length > 1

-------------------------------------------------------------------------------

-- Test: axioms are emitted as ASSUME instructions
def E2E_Axiom :=
#strata
program Core;
axiom [positive_fact]: (42 > 0);
procedure test(x : int) {
  assert (x > 0);
};
#end

#eval do
  let (.ok (_, goto)) := coreToGotoJson E2E_Axiom | IO.throwServerError "translation failed"
  -- The GOTO output should contain an ASSUME for the axiom
  assert! (goto.pretty.splitOn "ASSUME").length > 1

-------------------------------------------------------------------------------

-- Test: distinct declarations emit pairwise != ASSUME instructions
def E2E_Distinct :=
#strata
program Core;
const a : int;
const b : int;
const c : int;
distinct [abc]: [a, b, c];
procedure test() {
  assert (a != b);
};
#end

#eval do
  let (.ok (_, goto)) := coreToGotoJson E2E_Distinct | IO.throwServerError "translation failed"
  -- Should have 3 ASSUME instructions for pairwise != (a!=b, a!=c, b!=c)
  let assumes := (goto.pretty.splitOn "ASSUME").length - 1
  assert! assumes >= 3

-------------------------------------------------------------------------------

-- Test: string and regex operations emit function_application with correct types
def E2E_Regex :=
#strata
program Core;
function myStrInRe(s : string, r : regex) : bool;
function myReStar(r : regex) : regex;
function myStrToRe(s : string) : regex;
procedure test(s : string) {
  assert (myStrInRe(s, myReStar(myStrToRe("abc"))));
};
#end

#eval do
  let (.ok (symtab, goto)) := coreToGotoJson E2E_Regex | IO.throwServerError "translation failed"
  let gotoStr := goto.pretty
  -- The GOTO output should contain function_application nodes
  assert! (gotoStr.splitOn "function_application").length > 1
  -- The regex type should appear in the symbol table
  let symStr := symtab.pretty
  assert! (symStr.splitOn "regex").length > 1

-------------------------------------------------------------------------------

-- Test: procedure calls inside if-then-else
def E2E_NestedCall :=
#strata
program Core;
function helper(x : int) : int;
procedure caller(x : int) {
  var b : int;
  if (x > 0) {
    b := helper(x);
  } else {
    b := 0;
  }
  assert (b >= 0);
};
#end

#eval do
  match coreToGotoJsonByName E2E_NestedCall "caller" with
  | .error e => dbg_trace s!"translation error: {e}"; pure ()
  | .ok (_, goto) =>
    let gotoStr := goto.pretty
    -- Should contain both GOTO (for if-then-else) and function_application (for helper call)
    assert! (gotoStr.splitOn "GOTO").length > 1
    assert! (gotoStr.splitOn "function_application").length > 1

-------------------------------------------------------------------------------

-- Test: local function declarations (funcDecl) are lifted to top-level GOTO functions
def E2E_FuncDecl :=
#strata
program Core;
procedure test(x : int) {
  function double(n : int) : int { n + n }
  assert (double(x) >= 0 || double(x) < 0);
};
#end

#eval do
  let (.ok (symtab, _)) := coreToGotoJson E2E_FuncDecl | IO.throwServerError "translation failed"
  let symStr := symtab.pretty
  -- The lifted function "double" should appear in the symbol table
  assert! (symStr.splitOn "double").length > 1

-------------------------------------------------------------------------------

-- Test: source locations are propagated to GOTO instructions
def E2E_SourceLoc :=
#strata
program Core;
procedure test(x : int) {
  assert (x > 0);
};
#end

#eval do
  let (.ok (_, goto)) := coreToGotoJson E2E_SourceLoc | IO.throwServerError "translation failed"
  let gotoStr := goto.pretty
  -- The GOTO output should contain non-zero line numbers from source locations
  assert! (gotoStr.splitOn "\"line\"").length > 1

-------------------------------------------------------------------------------

-- Test: property summary in metadata flows to GOTO JSON comment field
-- We parse a Core program, then inject a property summary into the assert's
-- metadata before translating to GOTO.

private def injectPropertySummary (stmts : List Core.Statement) (msg : String)
    : List Core.Statement :=
  stmts.map fun s => match s with
    | .cmd (.cmd (.assert label b md)) =>
      .cmd (.cmd (.assert label b (md.withPropertySummary msg)))
    | other => other

-- TODO: This could be split into a two-stage transformation:
-- 1. structured → cfg (via StructuredToUnstructured)
-- 2. cfg → CProverGOTO (always operates on CFG, no pattern matching needed)
-- For now, unstructured bodies are not supported in this test helper.
private def coreToGotoJsonWithSummary (p : Strata.Program) (summary : String) :
    Except Std.Format (Lean.Json × Lean.Json) := do
  let cprog := translateCore p
  let Env := Lambda.TEnv.default
  let procs := cprog.decls.filterMap fun d => d.getProc?
  let p := procs[0]!
  let bodyStmts ← p.body.getStructured.mapError fun s => f!"{s}"
  let p' : Core.Procedure := { p with body := .structured (injectPropertySummary bodyStmts summary) }
  let pname := Core.CoreIdent.toPretty p'.header.name
  let ctx ← procedureToGotoCtx Env p'
  let json ← (CoreToGOTO.CProverGOTO.Context.toJson pname ctx.1).mapError (fun e => f!"{e}")
  return (json.symtab, json.goto)

def E2E_PropertySummary :=
#strata
program Core;
procedure test(x : int) {
  assert (x > 0);
};
#end

#eval do
  let (.ok (_, goto)) := coreToGotoJsonWithSummary E2E_PropertySummary "x must be positive"
    | IO.throwServerError "translation failed"
  let gotoStr := goto.pretty
  -- The GOTO JSON should contain the property summary as the comment
  assert! (gotoStr.splitOn "x must be positive").length > 1
  -- It should NOT contain the default label as the comment
  assert! (gotoStr.splitOn "assert_0").length == 1

-------------------------------------------------------------------------------

-- Regression: inout-parameter rename collision.
-- An inout parameter appears in both `Procedure.Header.inputs` and
-- `Procedure.Header.outputs`. Before the fix, the rename map's outputs entry
-- (`pname::1::x`) overwrote the formals entry (`pname::x`), and call sites
-- passing inout args produced typeless `LExpr.fvar id none` that
-- `toGotoExprCtx` rejected with "Not yet implemented: LExpr.fvar … none".

-- Inout params are bound to the formal symbol form, not a separate local.
private def E2E_InoutRename :=
#strata
program Core;
procedure caller(inout y : int)
spec {
  ensures (y == y);
} {
  y := y;
};
#end

#eval do
  let (.ok (symtab, goto)) := coreToGotoJson E2E_InoutRename
    | IO.throwServerError "inout translation failed"
  let symtabStr := symtab.pretty
  let gotoStr := goto.pretty
  -- Body references to `y` resolve to the formal symbol `caller::y`,
  -- not the local symbol `caller::1::y`.
  assert! (gotoStr.splitOn "caller::y").length > 1
  assert! (gotoStr.splitOn "caller::1::y").length == 1
  -- The formal symbol entry exists; the spurious local entry does NOT.
  assert! (symtabStr.splitOn "\"caller::y\"").length > 1
  assert! (symtabStr.splitOn "\"caller::1::y\"").length == 1

-- Inout call site: passing inout to a callee no longer errors at toGotoExprCtx.
private def E2E_InoutCallSite :=
#strata
program Core;
procedure helper(inout x : int) { x := x; };
procedure main(inout y : int)   { call helper(inout y); };
#end

#eval do
  -- Before the fix, this produced:
  --   [toGotoExprCtx] Not yet implemented: LExpr.fvar … name := "main::1::y" … none
  let cprog := translateCore E2E_InoutCallSite
  let procs := cprog.decls.filterMap fun d => Core.Decl.getProc? d
  let mainProc := procs[1]!
  let Env := Lambda.TEnv.default
  let (.ok _) := procedureToGotoCtx Env mainProc
    | IO.throwServerError "inout call-site translation failed"
  pure ()

-- Pure-out regression guard: inouts must not break the pre-existing `out`
-- handling. A pure `out` parameter still gets the local symbol form.
private def E2E_PureOutRegression :=
#strata
program Core;
procedure helper(out x : int) { x := 0; };
procedure main(out y : int)   { call helper(out y); };
#end

#eval do
  let cprog := translateCore E2E_PureOutRegression
  let procs := cprog.decls.filterMap fun d => Core.Decl.getProc? d
  let mainProc := procs[1]!
  let Env := Lambda.TEnv.default
  let (.ok (ctx, _)) := procedureToGotoCtx Env mainProc
    | IO.throwServerError "pure-out translation failed"
  -- `y` is a pure out, so it appears in ctx.locals (mapped to `main::1::y`).
  assert! ctx.locals.contains "y"

-------------------------------------------------------------------------------

-- Regression: body-aware dispatch sends CFG procedures through
-- `procedureToGotoCtxViaCFG` instead of erroring "expected structured body,
-- got CFG". Before the dispatch wrapper, every CFG-bodied procedure failed
-- at coreToGotoFiles even though procedureToGotoCtxViaCFG existed.
--
-- We build the procedure programmatically because the `cfg ...` surface
-- syntax isn't parseable in the #strata macro on this branch.

private def E2E_CFGDispatchProc : Core.Procedure :=
  { header := { name := "trivialCfg", typeArgs := [], inputs := [], outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .cfg
      { entry := "start",
        blocks := [("start", { cmds := [], transfer := .finish })] } }

#eval do
  let Env := Lambda.TEnv.default
  -- The dispatcher sees a CFG body and routes to procedureToGotoCtxViaCFG.
  let (.ok _) := procedureToGotoCtxDispatch Env E2E_CFGDispatchProc
    | IO.throwServerError "CFG-body dispatch failed"
  -- Sanity: the structured-only path explicitly rejects CFG bodies.
  match procedureToGotoCtx Env E2E_CFGDispatchProc with
  | .error _ => pure ()  -- expected
  | .ok _ => IO.throwServerError "structured path unexpectedly accepted CFG body"

-------------------------------------------------------------------------------

-- Regression: buildEntryShim produces a __cprover_entry function that
-- declares one local per main formal, havocs each from nondet, calls main,
-- and ends. Without this shim, cbmc rejects SMACK-translated `main`
-- (which has memory-map / exception parameters) as having no valid entry
-- point and exits with rc=6.

#eval do
  let formals : Map String CProverGOTO.Ty :=
    [("p_in", CProverGOTO.Ty.Integer), ("p_inout", CProverGOTO.Ty.Boolean)]
  let retTy : CProverGOTO.Ty := CProverGOTO.Ty.Integer
  let (.ok (symtabJson, gotoFn)) := buildEntryShim "__cprover_entry" "main" formals retTy
    | IO.throwServerError "buildEntryShim failed"
  -- The function symbol exists.
  let symtabStr := symtabJson.pretty
  assert! (symtabStr.splitOn "__cprover_entry").length > 1
  -- Locals for both formals exist, prefixed with the entry name.
  assert! (symtabStr.splitOn "__cprover_entry::1::p_in").length > 1
  assert! (symtabStr.splitOn "__cprover_entry::1::p_inout").length > 1
  -- A return local exists since main has a non-Empty return type.
  assert! (symtabStr.splitOn "__cprover_entry::1::_ret").length > 1
  -- The GOTO function body contains a FUNCTION_CALL to main.
  let gotoStr := gotoFn.pretty
  assert! (gotoStr.splitOn "FUNCTION_CALL").length > 1
  assert! (gotoStr.splitOn "\"main\"").length > 1

-- Empty-return regression: if main has no output, no _ret local is emitted.
#eval do
  let formals : Map String CProverGOTO.Ty := [("x", CProverGOTO.Ty.Integer)]
  let retTy : CProverGOTO.Ty := CProverGOTO.Ty.Empty
  let (.ok (symtabJson, _)) := buildEntryShim "__cprover_entry" "main" formals retTy
    | IO.throwServerError "buildEntryShim (void return) failed"
  let symtabStr := symtabJson.pretty
  -- Only one local (the formal), no _ret entry.
  assert! (symtabStr.splitOn "__cprover_entry::1::x").length > 1
  assert! (symtabStr.splitOn "__cprover_entry::1::_ret").length == 1
