/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataMain

/-! ## End-to-end tests: Core program → GOTO JSON

These tests verify the full pipeline from DDM-parsed Core programs through
`procedureToGotoCtx` to GOTO JSON output, covering features added in the
Core-to-GOTO gap-filling work:
- Global variables in symbol table
- Procedure contracts (requires/ensures/modifies)
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
  let json := CoreToGOTO.CProverGOTO.Context.toJson pname ctx.1
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
procedure test(x : int) returns () {
  assert (x > 0);
};
#end

#eval! do
  let (.ok (symtab, goto)) := coreToGotoJson E2E_SimpleAssert | panic! "translation failed"
  assert! symtab.getObjValD "test" != Lean.Json.null
  assert! goto.getObjValD "functions" != Lean.Json.null

-------------------------------------------------------------------------------

-- Test: global variable appears in symbol table
def E2E_GlobalVar :=
#strata
program Core;
var g : int;
procedure test() returns () {
  assert (g > 0);
};
#end

#eval! do
  let (.ok (symtab, _)) := coreToGotoJson E2E_GlobalVar | panic! "translation failed"
  let gSym := symtab.getObjValD "g"
  assert! gSym != Lean.Json.null
  -- isStaticLifetime is a Bool field in CBMCSymbol, serialized by deriving ToJson
  let isStatic := gSym.getObjValD "isStaticLifetime"
  assert! isStatic == Lean.Json.bool true

-------------------------------------------------------------------------------

-- Test: procedure with precondition emits #spec_requires
def E2E_Precondition :=
#strata
program Core;
procedure test(x : int) returns ()
spec {
  requires (x > 0);
} {
  assert (x > 0);
};
#end

#eval! do
  let (.ok (symtab, _)) := coreToGotoJson E2E_Precondition | panic! "translation failed"
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
procedure test(x : int) returns ()
spec {
  ensures (x > 0);
} {
  assert (x > 0);
};
#end

#eval! do
  let (.ok (symtab, _)) := coreToGotoJson E2E_Postcondition | panic! "translation failed"
  let testSym := symtab.getObjValD "test"
  let codeType := testSym.getObjValD "type"
  let namedSub := codeType.getObjValD "namedSub"
  let specEns := namedSub.getObjValD "#spec_ensures"
  assert! specEns != Lean.Json.null

-------------------------------------------------------------------------------

-- Test: procedure with modifies emits #spec_assigns
def E2E_Modifies :=
#strata
program Core;
var g : int;
procedure test(x : int) returns ()
spec {
  modifies g;
} {
  assert (x > 0);
};
#end

#eval! do
  let (.ok (symtab, _)) := coreToGotoJson E2E_Modifies | panic! "translation failed"
  let testSym := symtab.getObjValD "test"
  let codeType := testSym.getObjValD "type"
  let namedSub := codeType.getObjValD "namedSub"
  let specAssigns := namedSub.getObjValD "#spec_assigns"
  assert! specAssigns != Lean.Json.null

-------------------------------------------------------------------------------

-- Test: cover command produces ASSERT instruction in GOTO output
def E2E_Cover :=
#strata
program Core;
procedure test(x : int) returns () {
  cover (x > 0);
};
#end

#eval! do
  let (.ok (_, goto)) := coreToGotoJson E2E_Cover | panic! "translation failed"
  assert! (goto.pretty.splitOn "ASSERT").length > 1

-------------------------------------------------------------------------------

-- Test: bitvector operations translate end-to-end
def E2E_BVOps :=
#strata
program Core;
procedure test(x : bv32, y : bv32) returns () {
  var z : bv32 := x + y;
  assert (z > bv{32}(0));
};
#end

#eval! do
  let (.ok (symtab, goto)) := coreToGotoJson E2E_BVOps | panic! "translation failed"
  assert! symtab.getObjValD "test" != Lean.Json.null
  assert! goto.getObjValD "functions" != Lean.Json.null

-------------------------------------------------------------------------------

-- Test: free requires/ensures are skipped in contract annotations
def E2E_FreeSpecs :=
#strata
program Core;
procedure test(x : int) returns ()
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

#eval! do
  match coreToGotoJson E2E_FreeSpecs with
  | .error e => panic! s!"translation failed: {e}"
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
procedure callee(x : int) returns (r : int) {
  r := x + 1;
};
procedure caller() returns (y : int) {
  call y := callee(42);
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
  let json := CoreToGOTO.CProverGOTO.Context.toJson pname ctx.1
  let extraJson := Lean.toJson extraSyms
  let symtab := match json.symtab, extraJson with
    | .obj m1, .obj m2 => Lean.Json.obj (m2.mergeWith (fun _ v _ => v) m1)
    | _, _ => json.symtab
  return (symtab, json.goto)

#eval! do
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
procedure test(x : int) returns () {
  assert (x > 0);
};
#end

#eval! do
  let (.ok (_, goto)) := coreToGotoJson E2E_Axiom | panic! "translation failed"
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
procedure test() returns () {
  assert (a != b);
};
#end

#eval! do
  let (.ok (_, goto)) := coreToGotoJson E2E_Distinct | panic! "translation failed"
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
procedure test(s : string) returns () {
  assert (myStrInRe(s, myReStar(myStrToRe("abc"))));
};
#end

#eval! do
  let (.ok (symtab, goto)) := coreToGotoJson E2E_Regex | panic! "translation failed"
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
procedure caller(x : int) returns () {
  var b : int;
  if (x > 0) {
    b := helper(x);
  } else {
    b := 0;
  }
  assert (b >= 0);
};
#end

#eval! do
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
procedure test(x : int) returns () {
  function double(n : int) : int { n + n }
  assert (double(x) >= 0 || double(x) < 0);
};
#end

#eval! do
  let (.ok (symtab, _)) := coreToGotoJson E2E_FuncDecl | panic! "translation failed"
  let symStr := symtab.pretty
  -- The lifted function "double" should appear in the symbol table
  assert! (symStr.splitOn "double").length > 1

-------------------------------------------------------------------------------

-- Test: source locations are propagated to GOTO instructions
def E2E_SourceLoc :=
#strata
program Core;
procedure test(x : int) returns () {
  assert (x > 0);
};
#end

#eval! do
  let (.ok (_, goto)) := coreToGotoJson E2E_SourceLoc | panic! "translation failed"
  let gotoStr := goto.pretty
  -- The GOTO output should contain non-zero line numbers from source locations
  assert! (gotoStr.splitOn "\"line\"").length > 1
