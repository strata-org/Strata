/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
meta import Strata.Languages.Core
meta import Strata.Languages.Core.SMTEncoder
meta import Strata.Languages.Core.Verifier
import all Strata.Languages.Core.VerifiedSMTGen.SMTEncoder
import Strata.Languages.Core.ObligationExtraction
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core.ProgramType

meta section

/-!
# Full-pipeline differential harness for the refactored SMT encoder

Runs whole `#strata` programs through the FULL production transform pipeline, extracts their real proof
obligations, and validates the refactored encoder against production on each:
  * `checkProgram`  — renders each obligation via both encoders and asserts the normalized SMT-LIB text
    agrees (throws on divergence).
  * `checkVerdicts` — runs the real `Core.verify` pipeline with `useRefactoredEncoder` off vs on and
    compares the per-obligation solver verdict (the actual Approach-A integration path).

Both are fed the SAME post-pipeline monomorphized factory + datatypes. No production code is modified. -/

namespace Core
open Strata Lambda Imperative Strata.SMT
open Strata.SMT.DenoteTyped

/-- Reassemble a string into its top-level parenthesized S-expressions (one per SMT command), so
    MULTI-LINE commands (e.g. `declare-datatype` bodies) stay whole. Chars outside any command
    (whitespace between commands) are dropped. -/
private def splitTopLevel (s : String) : List String := Id.run do
  let mut out : List String := []
  let mut depth : Nat := 0
  let mut cur : String := ""
  for c in s.toList do
    if c == '(' then
      depth := depth + 1; cur := cur.push c
    else if c == ')' then
      cur := cur.push c; depth := depth - 1
      if depth == 0 then out := out ++ [cur]; cur := ""
    else if depth > 0 then
      cur := cur.push c
  return out

-- `f.N` interpreted-function names differ COSMETICALLY between the encoders: production and the
-- refactored encoder emit the same define-funs in different (both valid) topological orders, so the
-- positional `f.{n}` numbers differ. The helpers below canonicalize each `f.N` to a CONTENT-derived
-- token (its definition with callees recursively canonicalized) so equivalent queries compare equal.

/-- All maximal digit-runs immediately following `f.` in `s` (the `N` of each `f.N` occurrence). -/
private partial def fnNumsIn (s : String) : List String :=
  ((s.splitOn "f.").drop 1).filterMap (fun part =>
    let ds := String.ofList (part.toList.takeWhile Char.isDigit)
    if ds.isEmpty then none else some ds)

/-- The `N` of a `(define-fun f.N …)` command, if it is one. -/
private def defFnNum (c : String) : Option String :=
  if c.startsWith "(define-fun f." then
    some (String.ofList ((c.toList.drop "(define-fun f.".length).takeWhile Char.isDigit))
  else none

/-- Replace each `f.N` (N a number) with its canonical token; longest numbers first so `f.3` never
    clobbers `f.31`. Canonical tokens contain no `f.<digit>`, so replacements don't cascade. -/
private def substFN (canon : List (String × String)) (s : String) : String :=
  ((canon.toArray.qsort (fun a b => a.1.length > b.1.length)).toList).foldl
    (fun s (num, tok) => s.replace ("f." ++ num) tok) s

/-- Assign each define-fun `f.N` a content-derived canonical token, in dependency order (a callee's
    token is substituted into its callers'); fuel-bounded, cycles broken by forcing progress. -/
private partial def assignCanonFN (defs : List (String × String)) : List (String × String) :=
  let rec go (canon : List (String × String)) (fuel : Nat) : List (String × String) :=
    match fuel with
    | 0 => canon
    | fuel + 1 =>
      let assigned := canon.map (·.1)
      let remaining := defs.filter (fun p => !assigned.contains p.1)
      if remaining.isEmpty then canon else
        let ready := remaining.filter (fun (n, d) => (fnNumsIn d).all (fun m => m == n || assigned.contains m))
        let batch := if ready.isEmpty then remaining else ready
        let canon := batch.foldl (fun canon (n, d) =>
          canon ++ [(n, "F<" ++ substFN (canon ++ [(n, "SELF")]) d ++ ">")]) canon
        go canon fuel
  go [] (defs.length + 1)

private def canonicalizeFN (cmds : List String) : List String :=
  let defs := cmds.filterMap (fun c => (defFnNum c).map (fun n => (n, c)))
  let canon := assignCanonFN defs
  cmds.map (substFN canon)

def normalizeSMT (s : String) : List String :=
  let noComments := (s.splitOn "\n").filter (fun l => !l.startsWith ";")
  let joined := String.intercalate "\n" noComments
  let collapse (c : String) : String :=
    String.intercalate " " ((((c.replace "\n" " ").replace "\t" " ").splitOn " ").filter (· ≠ ""))
  let drop (c : String) : Bool :=
    c.isEmpty || c.startsWith "(set-logic" || c.startsWith "(set-option" || c.startsWith "(set-info"
      || c.startsWith "(check-sat" || c.startsWith "(get-value" || c.startsWith "(push" || c.startsWith "(pop"
  let core := ((splitTopLevel joined).map collapse).filter (fun c => !drop c)
  -- Canonicalize cosmetic `f.N` naming, then (re)sort into an order-independent multiset.
  (((canonicalizeFN core)).toArray.qsort (fun a b => compare a b == Ordering.lt)).toList

private def translate (t : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

/-- A polymorphic map-`select` program (↔ `MonomorphizeFunctions` Example 15): `get0<v>(m)` reads
    `m[0]` (the Factory `select`), forcing a ground `$__mono#select#int#int` instance in the
    monomorphized factory. -/
def mapGetPgm : StrataDDM.Program :=
#strata
program Core;
function get0<v>(m : Map int v) : v { m[0] }
procedure P(m : Map int int, out r : int)
spec {
  requires m[0] == 42;
  ensures r == 42;
}
{
  r := get0(m);
};
#end

/-! ## Differential over REAL obligations from whole programs

Run a `#strata` program through the FULL production transform pipeline (`runTransforms ∘
corePipelinePhases`: precondElim → termCheck → monomorphizeProcedures → typeCheck → monomorphizeFunctions
→ symbolicEval → …), then extract its real proof obligations (`ObligationExtraction.extractObligations`
on the post-eval program) and diff BOTH encoders on each, against the SAME post-pipeline monomorphized
factory + datatypes. This exercises the breadth production sees — datatype ops, `define-fun` bodies,
axioms, distinct.

`karities` (opaque-sort arities the refactored encoder needs) is read off production's collected
`ctx.sorts` — objective program metadata, not encoder-behavior. `checkProgram` asserts the normalized
SMT text agrees and THROWS on divergence. -/

/-- Run the full pipeline on `t`; return `(monomorphized factory, datatypes, real obligations)`. -/
def runProgramObligations (t : StrataDDM.Program) (useArrayTheory : Bool) :
    IO (Except String (Lambda.Factory CoreLParams
        × (@Lambda.TypeFactory CoreLParams.IDMeta)
        × Array (ProofObligation Expression))) := do
  let prog := translate t
  let options : Core.VerifyOptions :=
    { Core.VerifyOptions.default with useArrayTheory := useArrayTheory, verbose := .quiet }
  let phases := Core.corePipelinePhases none options
  let seed : Core.Transform.CoreTransformState :=
    { Core.Transform.CoreTransformState.emp with factory := Core.Factory }
  match ← EIO.toIO' (Core.runTransforms prog phases seed) with
  | .error e => return .error s!"transform: {toString e}"
  | .ok (oblProgram, state) =>
    match Core.buildEnv options oblProgram state.factory (registerCustomFunctions := true) with
    | .error e => return .error s!"buildEnv: {toString e}"
    | .ok (E, _) =>
      match Core.ObligationExtraction.extractObligations oblProgram with
      | .error e => return .error s!"extract: {e}"
      | .ok obs => return .ok (E.factory, E.datatypes, obs)

/-! ## Rendering the refactored `SMTQuery` to SMT-LIB (test-only)

The refactored encoder produces an `SMTQuery` (data) and stops there; the production CR integration renders
it by converting to an `EncodeResult` and reusing production's `encodeCore`. These `emit`/`render` adapters
exist ONLY so this differential harness can dump a query to text and diff it against production — so they
live here, not in the encoder (which stays free of any `Solver`/`Encoder` dependency). Accesses `SMTQuery`'s
projections via the file's `import all` of the encoder. -/

/-- Emit an `SMTQuery` via `SolverM`, in command order: sorts → datatypes → uninterpreted decls (free
    vars, fn decls, var decls) → interpreted defs (fn defs, var defs) → assertions (fn axioms,
    assumptions) → the obligation (asserted as-is). -/
def _root_.Strata.SMT.DenoteTyped.SMTQuery.emit (q : SMTQuery) : SolverM Unit := do
  for s in q.sorts do
    Solver.declareSort s.name s.arity
  -- Emit datatypes per mutual-recursion block: a singleton block as `declare-datatype` (singular), a
  -- multi-member block as `declare-datatypes` (grouped, for mutual recursion).
  for block in q.datatypes do
    let toSMTC (c : RConstructor) : SMTConstructor := { name := c.name, args := c.args }
    match block with
    | [] => pure ()
    | [(n, ps, cs)] => Solver.declareDatatype n ps (cs.map toSMTC)
    | ds => Solver.declareDatatypes (ds.map fun (n, ps, cs) => (n, ps, cs.map toSMTC))
  -- Route declarations/definitions/assertions through the shared `Encoder` layer: interpreted factory
  -- functions get abbreviated `f.N` names (`encodeFunctionDef`), UF names are uniquified (`encodeUF`),
  -- and quantifier triggers are wrapped into the `.app .triggers` form printed as `:pattern`
  -- (`encodeTerm`). Managed vars (`varDecls`/`varDefs`) keep their own names, pre-registered so term
  -- references resolve to the real name without re-declaration.
  let enc : Strata.SMT.EncoderM Unit := do
    for uf in q.fnDecls ++ q.varDecls do
      let _ ← Strata.SMT.Encoder.encodeUF uf
    for f in q.varDefs do
      modify fun (s : Strata.SMT.EncoderState) => { s with
        functions := s.functions.insert f.toUF f.id
        isFunUninterp := s.isFunUninterp.insert f.toUF false
        usedNames := s.usedNames.insert f.id }
    for f in q.fnDefs do
      let _ ← Strata.SMT.Encoder.encodeFunctionDef f
    for f in q.varDefs do
      let bodyEnc ← Strata.SMT.Encoder.encodeTerm f.body
      Solver.defineFunTerm f.id (f.args.map fun v => (v.id, v.ty)) f.out bodyEnc
    for t in q.fnAxioms ++ q.assumptions do
      Solver.assert (← Strata.SMT.Encoder.encodeTerm t)
    Solver.assert (← Strata.SMT.Encoder.encodeTerm q.obl)
  let _ ← enc.run Strata.SMT.EncoderState.init
  pure ()

/-- Render an `SMTQuery` to SMT-LIB text via an in-memory buffer. For inspection and differential
    testing. -/
def _root_.Strata.SMT.DenoteTyped.SMTQuery.render (q : SMTQuery) : IO String := do
  let b ← IO.mkRef { : IO.FS.Stream.Buffer }
  let solver ← Solver.bufferWriter b
  let _ ← SolverM.run solver q.emit
  let contents ← b.get
  if h : contents.data.IsValidUTF8 then
    return String.fromUTF8 contents.data h
  else
    return "<invalid UTF-8 in rendered SMTQuery>"

/-- Render obligation `ob` to SMT-LIB text on BOTH paths, through the same full-pipeline factory:
    PRODUCTION via `encodeObligationToSMT` → `encodeCore` (fresh per-obligation state, no pruning), and
    REFACTORED via `encodeObligationRun` → `SMTQuery.render`. Returns `(pstr, rstr)` — the raw streams,
    before any normalization. `none` if production's collect errors on this obligation. -/
def renderBoth (F : Lambda.Factory CoreLParams) (tf : @Lambda.TypeFactory CoreLParams.IDMeta)
    (ob : ProofObligation Expression) (useArrayTheory : Bool) : IO (Option (String × String)) := do
  let baseCtx : SMT.Context :=
    { SMT.Context.default with datatypes := SMT.Datatypes.ofFactory tf, useArrayTheory }
  match encodeObligationToSMT F (.init { ctx := baseCtx }) ob [] with
  | .error _ => return none
  | .ok (r, _) => do
    let karities := r.ctx.sorts.toArray.toList.map (fun s => (s.name, s.arity))
    let pctx ← Strata.Pipeline.PipelineContext.create
    let b ← IO.mkRef { : IO.FS.Stream.Buffer }
    let solver ← Solver.bufferWriter b
    let _ ← SolverM.run solver
      (Strata.SMT.Encoder.encodeCore r.ctx (pure ()) r.assumptions r.goal ob.metadata
        (satisfiabilityCheck := true) (validityCheck := false) (label := ob.label)
        (varDefinitions := r.varDefs) (varDeclarations := r.varDecls) (pctx := pctx))
    let contents ← b.get
    let pstr := if hh : contents.data.IsValidUTF8 then String.fromUTF8 contents.data hh else ""
    let rstr ← match Refactor.encodeObligationRun useArrayTheory F tf karities ob with
      | .ok q => q.render
      | .error err => pure s!"<refactored error> {err.pretty}"
    return some (pstr, rstr)

def checkProgram (name : String) (t : StrataDDM.Program) (useArrayTheory : Bool := false) : IO Unit := do
  IO.println s!"════════ {name} ════════"
  match ← runProgramObligations t useArrayTheory with
  | .error e => throw (IO.userError s!"{name}: pipeline error: {e}")
  | .ok (F, tf, obs) => do
    let mut nMatch := 0
    let mut nDiff := 0
    for h : idx in [0:obs.size] do
      let ob := obs[idx]
      match ← renderBoth F tf ob useArrayTheory with
      | none => IO.println s!"  [{idx}] ⚠️ production collect error"; nDiff := nDiff + 1
      | some (pstr, rstr) =>
        if normalizeSMT pstr == normalizeSMT rstr then nMatch := nMatch + 1
        else
          nDiff := nDiff + 1
          IO.println s!"  [{idx}] ❌ {ob.label}"
          IO.println s!"    prod: {normalizeSMT pstr}"
          IO.println s!"    ref:  {normalizeSMT rstr}"
    IO.println s!"  → {nMatch} match / {nDiff} diff (of {obs.size} obligations)"
    if nDiff > 0 then
      throw (IO.userError s!"{name}: {nDiff} of {obs.size} obligation(s) diverged from production")

-- First real-obligation program: `mapGetPgm`'s `ensures r == 42` after `r := get0(m)` — exercises a
-- monomorphized `define-fun` (`$__mono#get0#int`) body + `select`, which the hand-built cases never did.
#eval checkProgram "mapGetPgm (real obligations)" mapGetPgm

/-! ### Corpus: representative example programs (datatypes, define-funs, axioms/triggers, distinct) -/

-- Datatype + testers/selectors (`Option..isNone/isSome`).
def optionTesterPgm : StrataDDM.Program :=
#strata
program Core;
datatype Option () { None(), Some(val: int) };
procedure TestOptionTesters()
spec {
  ensures true;
}
{
  var x : Option;
  var y : Option;
  x := None();
  assert [isNone]: Option..isNone(x);
  assert [notSome]: !Option..isSome(x);
  y := Some(42);
  assert [isSome]: Option..isSome(y);
  assert [notNone]: !Option..isNone(y);
};
#end

-- Interpreted + inline functions (exercises the `define-fun` f.N naming across several fns).
def funcPgm : StrataDDM.Program :=
#strata
program Core;
const fooConst : int;
inline function fooTest() : int { fooConst }
function barTest1(x : int) : int { x }
inline function barTest2(y : int) : int { y }
function barTest3(y : int) : int { barTest1(y) }
function barTest4(y : int) : int { barTest3(y) }
procedure fooProc(a : int) {
  assert [barEq]: (barTest1(a) == barTest2(a));
  assert [fooEq]: (fooConst == fooTest);
};
#end

-- Uninterpreted functions + quantified axioms WITH triggers.
def axiomPgm2 : StrataDDM.Program :=
#strata
program Core;
function f(x : int) : int;
function g(x : int) : int;
axiom [f_g_ax]: (forall x : int :: { f(x) } f(x) == int.add(g(x), 1));
axiom [g_ax]:   (forall x : int :: { g(x), f(x) } g(x) == int.mul(x, 2));
procedure main (x : int) {
assert [axiomPgm2_main_assert]: (int.ge(x, 0) ==> int.gt(f(x), x));
};
#end

-- Enum-style datatype (exercises the distinct-constructors path).
def enumPgm : StrataDDM.Program :=
#strata
program Core;
datatype Color () { Red(), Green(), Blue() };
procedure TestEnumTesters()
spec {
  ensures true;
}
{
  var c : Color;
  c := Red();
  assert [isRed]: Color..isRed(c);
  assert [notGreen]: !Color..isGreen(c);
  assert [notBlue]: !Color..isBlue(c);
};
#end

-- Richest: recursive datatypes + four `rec function`s (define-fun + generated recursive axioms).
def sizeIsLenPgm : StrataDDM.Program :=
#strata
program Core;
datatype IntList { Nil(), Cons(hd: int, tl: IntList) };
datatype IntTree { Leaf(), Node(left: IntTree, val: int, right: IntTree) };
rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else int.add(1, listLen(IntList..tl(xs)))
};
rec function append (@[cases] xs : IntList, ys : IntList) : IntList
{
  if IntList..isNil(xs) then ys
  else Cons(IntList..hd(xs), append(IntList..tl(xs), ys))
};
rec function size (@[cases] t : IntTree) : int
{
  if IntTree..isLeaf(t) then 0
  else int.add(int.add(1, size(IntTree..left(t))), size(IntTree..right(t)))
};
rec function toList (@[cases] t : IntTree) : IntList
{
  if IntTree..isLeaf(t) then Nil()
  else append(toList(IntTree..left(t)), Cons(IntTree..val(t), toList(IntTree..right(t))))
};
procedure LenAppend(xs : IntList, ys : IntList)
spec {
  ensures [len_append]: listLen(append(xs, ys)) == int.add(listLen(xs), listLen(ys));
}
{
  if (IntList..isCons(xs))
  {
    call LenAppend(IntList..tl(xs), ys);
  }
};
procedure SizeIsLen(t : IntTree)
spec {
  ensures [size_is_len]: size(t) == listLen(toList(t));
}
{
  if (IntTree..isNode(t))
  {
    call SizeIsLen(IntTree..left(t));
    call SizeIsLen(IntTree..right(t));
    call LenAppend(toList(IntTree..left(t)), Cons(IntTree..val(t), toList(IntTree..right(t))));
  }
};
#end

#eval checkProgram "optionTesterPgm (datatype + testers)" optionTesterPgm
#eval checkProgram "funcPgm (interpreted/inline functions)" funcPgm

#eval checkProgram "axiomPgm2 (axioms + triggers)" axiomPgm2
#eval checkProgram "enumPgm (enum → distinct)" enumPgm
#eval checkProgram "sizeIsLenPgm (recursive datatypes + rec functions)" sizeIsLenPgm

/-! ### Wider corpus: mutually-recursive datatypes, regex, quantifiers-over-maps, bitvectors -/

-- MUTUALLY-recursive datatypes (Forest ↔ RoseTree): a genuine multi-member block → exercises the
-- GROUPED `declare-datatypes` path (D3 fix), unlike the independent datatypes in sizeIsLenPgm.
def roseTreeTesterPgm : StrataDDM.Program :=
#strata
program Core;
  datatype Forest { FNil(), FCons(head: RoseTree, tail: Forest) }
  datatype RoseTree { Node(val: int, children: Forest) };
procedure TestRoseTreeTesters()
spec {
  ensures true;
}
{
  var t : RoseTree;
  var f : Forest;
  f := FNil();
  assert [isFNil]: Forest..isFNil(f);
  assert [notFCons]: !Forest..isFCons(f);
  t := Node(42, FNil());
  assert [isNode]: RoseTree..isNode(t);
  f := FCons(Node(1, FNil()), FNil());
  assert [isFCons]: Forest..isFCons(f);
  assert [notFNil]: !Forest..isFNil(f);
};
#end

-- Regex: `regex`-typed interpreted functions + `str.in.re` / `re.*` ops.
def regexPgm1 : StrataDDM.Program :=
#strata
program Core;
function cannot_end_with_period () : regex {
  re.comp(re.concat (re.* (re.all()), str.to.re(".")))
}
function optionally_a () : regex {
    re.loop(str.to.re("a"), 0, 1)
}
function ok_chars_regex () : regex {
    re.loop(
        re.union(re.range("a", "z"),
            re.union(re.range("0", "9"),
                     re.union(str.to.re("."),
                              str.to.re("-")))),
        1, 10)
}
procedure main() {
    assert [hello_dot_ends_with_period]:    (!(str.in.re("hello.", cannot_end_with_period())));
    assert [dot_ends_with_period]:          (!(str.in.re(".",      cannot_end_with_period())));
    assert [bye_exclaim_no_end_with_period]:  (str.in.re("bye!",   cannot_end_with_period()));
    assert [ok_chars_str]:                    (str.in.re("test-str-1", ok_chars_regex()));
    assert [cannot_contain_exclaim]:        (!(str.in.re("test-str!", ok_chars_regex())));
    assert [has_to_be_at_least_1_char]:     (!(str.in.re("", ok_chars_regex())));
    assert [cannot_exceed_10_chars]:        (!(str.in.re("0123456789a", ok_chars_regex())));
    assert [optionally_a_check1]:             (str.in.re("a", optionally_a()));
    assert [optionally_a_check2]:           (!(str.in.re("b", optionally_a())));
};
#end

-- Quantifier over maps: an axiom `forall m, k :: m[k] == 0` (select under a binder).
def advQuantPgm : StrataDDM.Program :=
#strata
program Core;
axiom [mapAllValues0]: forall m: (Map int int), k: int :: m[k] == 0;
procedure Update(mArg: Map int int, kArg: int, out res: int)
spec {
  ensures mArg[kArg] == 0;
}
{
  assert [a]: mArg[kArg] == 0;
  res := mArg[kArg];
};
#end

-- Bitvectors: `bv W8`/`bv W1` consts, bv-op axioms (bv8.uLe), and bv8.add/bv1.add/bv1.sub asserts.
def bvPgm : StrataDDM.Program :=
#strata
program Core;
const x : bv W8;
const y : bv W8;
axiom [bv_x_ge_1]: bv8.uLe(bv{8}(1), x);
axiom [bv_y_ge_2]: bv8.uLe(bv{8}(2), y);
procedure P()
{
  assert [bv_add_ge]: bv8.add(x, y) == bv8.add(y, x);
};
procedure Q(x: bv W1, out r: bv W1)
spec {
  ensures r == bv1.sub(x, x);
} {
  r := bv1.add(x, x);
};
#end

#eval checkProgram "roseTreeTesterPgm (MUTUAL datatypes → grouped declare-datatypes)" roseTreeTesterPgm
#eval checkProgram "regexPgm1 (regex functions + str.in.re)" regexPgm1
#eval checkProgram "advQuantPgm (quantifier over maps)" advQuantPgm
#eval checkProgram "bvPgm (bitvector ops + axioms)" bvPgm

/-! ### More obligation kinds: div/mod (WF checks), cover, distinct, havoc'd (nondet) vars -/

-- Integer div/mod: `int.div`/`int.mod` generate divisor-well-formedness obligations (the previously
-- unconfirmed div/mod theory). Non-trivial assert forces the SafeDiv/SafeMod terms to be encoded.
def divModPgm : StrataDDM.Program :=
#strata
program Core;
procedure P(x : int, y : int)
{
  assert [d]: int.div(x, y) == 0;
  assert [m]: int.mod(x, y) == 0;
  assert [dt]: int.divT(x, y) == 0;
  assert [mt]: int.modT(x, y) == 0;
};
#end

-- Cover obligation + havoc'd (nondet) var + explicit distinct decl.
def coverDistinctPgm : StrataDDM.Program :=
#strata
program Core;
const c : int;
distinct [dd]: [c];
procedure P(a : int, b : int)
{
  var z : int;
  cover [cvr]: int.lt(a, b);
  assert [zt]: int.le(z, z);
};
#end

#eval checkProgram "divModPgm (int.div/mod/divT/modT + WF)" divModPgm
#eval checkProgram "coverDistinctPgm (cover + nondet var + distinct)" coverDistinctPgm

/-! ### Rich real program: heap `stress` (many mutually-referencing define-funs) — f.N ordering stress -/

def heapStressPgm : StrataDDM.Program :=
#strata
program Core;

datatype TypeTag {
  Container_TypeTag()
};
datatype Field {
  Container.value()
};
datatype Box {
  BoxInt(intVal : int)
};
datatype Composite {
  MkComposite(ref : int, typeTag : TypeTag)
};
datatype NotSupportedYet {
  MkNotSupportedYet()
};
datatype Heap {
  MkHeap(data : Map Composite (Map Field Box), nextReference : int)
};
datatype LaurelResolutionErrorPlaceholder {
  MkLaurelResolutionErrorPlaceholder()
};
datatype Float64IsNotSupportedYet {
  MkFloat64IsNotSupportedYet()
};
datatype LaurelUnit {
  MkLaurelUnit()
};
function ancestorsForContainer () : Map TypeTag bool {
  (mapConst<TypeTag>(false))[Container_TypeTag:=true]
}
function ancestorsPerType () : Map TypeTag (Map TypeTag bool) {
  (mapConst<TypeTag>(mapConst<TypeTag>(false)))[Container_TypeTag:=ancestorsForContainer]
}
function modifyOne$post0 ($heap : Heap, c : Composite, $heap$out : Heap) : bool {
  Heap..data!($heap$out) == (Heap..data!($heap))[c:=(Heap..data!($heap$out))[c]] && int.le(Heap..nextReference!($heap), Heap..nextReference!($heap$out))
}
function readField (heap : Heap, obj : Composite, field : Field) : Box {
  ((Heap..data!(heap))[obj])[field]
}
function modifyOne$post1 ($heap : Heap, c : Composite, $heap$out : Heap) : bool {
  forall $modifies_obj : Composite :: forall $modifies_fld : Field :: (if int.lt(Composite..ref!($modifies_obj), Heap..nextReference!($heap)) && !($modifies_obj == c) then readField($heap, $modifies_obj, $modifies_fld) == readField($heap$out, $modifies_obj, $modifies_fld) else true)
}
function updateField (heap : Heap, obj : Composite, field : Field, val : Box) : Heap {
  MkHeap((Heap..data!(heap))[obj:=((Heap..data!(heap))[obj])[field:=val]], Heap..nextReference!(heap))
}
function increment (heap : Heap) : Heap {
  MkHeap(Heap..data!(heap), int.add(Heap..nextReference!(heap), 1))
}
function modifyOne$asFunction ($heap : Heap, c : Composite) : Heap;
function stress$asFunction ($heap : Heap) : Heap;
procedure modifyOne (inout $heap : Heap, c : Composite)
{
  assume [assume_true]: true;
};
procedure stress (inout $heap : Heap)
{
  $return: {
    var $th_tmp0 : int := Heap..nextReference!($heap);
    var $$heap_0 : Heap := $heap;
    $heap := increment($heap);
    var target : Composite := MkComposite($th_tmp0, Container_TypeTag);
    var x : int := Box..intVal!(readField($heap, target, Container.value));
    var $th_tmp1 : int := Heap..nextReference!($heap);
    var $$heap_1 : Heap := $heap;
    $heap := increment($heap);
    var c0 : Composite := MkComposite($th_tmp1, Container_TypeTag);
    var $cp_2 : Heap := $heap;
    var $cp_3 : Composite := c0;
    $heap := modifyOne$asFunction($heap, $cp_3);
    assume [|assume(1075)|]: modifyOne$post0($cp_2, $cp_3, $heap);
    var $th_tmp2 : int := Heap..nextReference!($heap);
    var $$heap_2 : Heap := $heap;
    $heap := increment($heap);
    var c1 : Composite := MkComposite($th_tmp2, Container_TypeTag);
    var $cp_4 : Heap := $heap;
    var $cp_5 : Composite := c1;
    $heap := modifyOne$asFunction($heap, $cp_5);
    assume [|assume(1128)|]: modifyOne$post0($cp_4, $cp_5, $heap);
    var $th_tmp3 : int := Heap..nextReference!($heap);
    var $$heap_3 : Heap := $heap;
    $heap := increment($heap);
    var c2 : Composite := MkComposite($th_tmp3, Container_TypeTag);
    var $cp_6 : Heap := $heap;
    var $cp_7 : Composite := c2;
    $heap := modifyOne$asFunction($heap, $cp_7);
    assume [|assume(1181)|]: modifyOne$post0($cp_6, $cp_7, $heap);
    var $th_tmp4 : int := Heap..nextReference!($heap);
    var $$heap_4 : Heap := $heap;
    $heap := increment($heap);
    var c3 : Composite := MkComposite($th_tmp4, Container_TypeTag);
    var $cp_8 : Heap := $heap;
    var $cp_9 : Composite := c3;
    $heap := modifyOne$asFunction($heap, $cp_9);
    assume [|assume(1234)|]: modifyOne$post0($cp_8, $cp_9, $heap);
    var $th_tmp5 : int := Heap..nextReference!($heap);
    var $$heap_5 : Heap := $heap;
    $heap := increment($heap);
    var c4 : Composite := MkComposite($th_tmp5, Container_TypeTag);
    var $cp_10 : Heap := $heap;
    var $cp_11 : Composite := c4;
    $heap := modifyOne$asFunction($heap, $cp_11);
    assume [|assume(1287)|]: modifyOne$post0($cp_10, $cp_11, $heap);
    var $th_tmp6 : int := Heap..nextReference!($heap);
    var $$heap_6 : Heap := $heap;
    $heap := increment($heap);
    var c5 : Composite := MkComposite($th_tmp6, Container_TypeTag);
    var $cp_12 : Heap := $heap;
    var $cp_13 : Composite := c5;
    $heap := modifyOne$asFunction($heap, $cp_13);
    assume [|assume(1340)|]: modifyOne$post0($cp_12, $cp_13, $heap);
    var $th_tmp7 : int := Heap..nextReference!($heap);
    var $$heap_7 : Heap := $heap;
    $heap := increment($heap);
    var c6 : Composite := MkComposite($th_tmp7, Container_TypeTag);
    var $cp_14 : Heap := $heap;
    var $cp_15 : Composite := c6;
    $heap := modifyOne$asFunction($heap, $cp_15);
    assume [|assume(1393)|]: modifyOne$post0($cp_14, $cp_15, $heap);
    var $th_tmp8 : int := Heap..nextReference!($heap);
    var $$heap_8 : Heap := $heap;
    $heap := increment($heap);
    var c7 : Composite := MkComposite($th_tmp8, Container_TypeTag);
    var $cp_16 : Heap := $heap;
    var $cp_17 : Composite := c7;
    $heap := modifyOne$asFunction($heap, $cp_17);
    assume [|assume(1446)|]: modifyOne$post0($cp_16, $cp_17, $heap);
    var $th_tmp9 : int := Heap..nextReference!($heap);
    var $$heap_9 : Heap := $heap;
    $heap := increment($heap);
    var c8 : Composite := MkComposite($th_tmp9, Container_TypeTag);
    var $cp_18 : Heap := $heap;
    var $cp_19 : Composite := c8;
    $heap := modifyOne$asFunction($heap, $cp_19);
    assume [|assume(1499)|]: modifyOne$post0($cp_18, $cp_19, $heap);
    var $th_tmp10 : int := Heap..nextReference!($heap);
    var $$heap_10 : Heap := $heap;
    $heap := increment($heap);
    var c9 : Composite := MkComposite($th_tmp10, Container_TypeTag);
    var $cp_20 : Heap := $heap;
    var $cp_21 : Composite := c9;
    $heap := modifyOne$asFunction($heap, $cp_21);
    assume [|assume(1552)|]: modifyOne$post0($cp_20, $cp_21, $heap);
    var $th_tmp11 : int := Heap..nextReference!($heap);
    var $$heap_11 : Heap := $heap;
    $heap := increment($heap);
    var c10 : Composite := MkComposite($th_tmp11, Container_TypeTag);
    var $cp_22 : Heap := $heap;
    var $cp_23 : Composite := c10;
    $heap := modifyOne$asFunction($heap, $cp_23);
    assume [|assume(1605)|]: modifyOne$post0($cp_22, $cp_23, $heap);
    var $th_tmp12 : int := Heap..nextReference!($heap);
    var $$heap_12 : Heap := $heap;
    $heap := increment($heap);
    var c11 : Composite := MkComposite($th_tmp12, Container_TypeTag);
    var $cp_24 : Heap := $heap;
    var $cp_25 : Composite := c11;
    $heap := modifyOne$asFunction($heap, $cp_25);
    assume [|assume(1658)|]: modifyOne$post0($cp_24, $cp_25, $heap);
    assert [|assert(2119)|]: x == Box..intVal!(readField($heap, target, Container.value));
  }
};
#end

#eval checkProgram "heapStressPgm (heap stress: many define-funs)" heapStressPgm


/-! ## Verdict-parity validation of the `useRefactoredEncoder` flag (end-to-end `Core.verify`)

Directive: for each corpus program, run the FULL `Core.verify` pipeline TWICE — options differing ONLY
in `useRefactoredEncoder := false` (production encoder) vs `true` (refactored encoder, Approach A:
builds an `EncodeResult`, reuses production's `encodeCore`) — and compare the per-obligation **verdict**
(`label` + `formatOutcome`, i.e. the sat/valid/invalid + path disposition), NOT the full solver output /
counterexample text (those differ only cosmetically). Mechanism copied verbatim from the one-program
smoke test in `SMTEncoderTests.lean` (`Core.verify … (options := { … with useRefactoredEncoder := b })`,
then `rs.toList.map fun (r : Core.VCResult) => (r.obligation.label, r.formatOutcome)`).

Unlike `checkProgram` above (which diffs the SMT-LIB *text* and THROWS on divergence), this diffs only the
solver VERDICTS and NEVER throws: a real divergence / flag-on error is a FINDING to print, not a build
break. Each program gets its own `#eval` so one program's error can't abort the others. -/

/-- Per-obligation `(label, formatOutcome)` list from `Core.verify` under `useRefactoredEncoder := b`,
    or an `.error` capturing any thrown pipeline/solver failure (so callers stay total & keep going). -/
def verdictsOf (t : StrataDDM.Program) (useRefactored : Bool) :
    IO (Except String (List (String × String))) := do
  try
    -- `Strata.Core.verify` is the `StrataDDM.Program → IO Core.VCResults` wrapper the smoke test uses
    -- (translates DDM→Core + manages a temp dir internally). Qualified to avoid resolving to the
    -- lower-level `_root_.Core.verify` (which takes a `Core.Program` + explicit `tempDir`).
    let rs ← Strata.Core.verify t
      (options := { Core.VerifyOptions.quiet with useRefactoredEncoder := useRefactored })
    pure (.ok (rs.toList.map fun (r : Core.VCResult) => (r.obligation.label, r.formatOutcome)))
  catch e =>
    pure (.error (toString e))

/-- `true` if `s` is an obligation-level error verdict (encode error / solver error), which
    `VCResult.formatOutcome` renders with a leading 🚨. -/
private def isErrVerdict (s : String) : Bool := s.startsWith "🚨"

/-- Canonicalize a verdict for COMPARISON by stripping volatile detail that isn't part of the
    disposition. Pass/fail/unknown labels are already stable; error verdicts (🚨) embed the SMT
    solver's per-run temp-file path (`/tmp/tmp.XXXX/label_N.smt2:L.C:`), so two byte-identical
    crashes would otherwise spuriously differ. We drop any whitespace-delimited token that names an
    `.smt2` file or a `/tmp/` path, leaving the stable error kind/message. -/
private def canonVerdict (s : String) : String :=
  if isErrVerdict s then
    String.intercalate " "
      ((s.splitOn " ").filter
        (fun tok => (tok.splitOn ".smt2").length == 1 && (tok.splitOn "/tmp/").length == 1))
  else s

/-- Run `Core.verify` flag-OFF vs flag-ON on `t` and compare per-obligation verdicts only.
    Prints `[name] N obligations, all verdicts match` on agreement (flagging any 🚨 error verdicts
    that appear on BOTH sides), or the specific mismatching labels with both verdicts. A thrown
    failure on either path is surfaced distinctly. Never throws — divergence is a finding, not a
    build break. -/
def checkVerdicts (name : String) (t : StrataDDM.Program) : IO Unit := do
  let off ← verdictsOf t false
  let on  ← verdictsOf t true
  match off, on with
  | .error e, .error e2 =>
    IO.println s!"[{name}] ⚠️ BOTH paths errored — off: {e} | on: {e2}"
  | .error e, .ok _ =>
    IO.println s!"[{name}] ⚠️ flag-OFF (production) errored (flag-on ran): {e}"
  | .ok _, .error e =>
    IO.println s!"[{name}] ⚠️ flag-ON (refactored) errored (flag-off ran): {e}"
  | .ok offR, .ok onR =>
    -- Compare on the CANONICAL verdict (disposition), not the raw text (volatile temp paths).
    let offC := offR.map (fun (l, v) => (l, canonVerdict v))
    let onC  := onR.map (fun (l, v) => (l, canonVerdict v))
    if offC == onC then
      let errs := offR.filter (fun p => isErrVerdict p.2)
      if errs.isEmpty then
        IO.println s!"[{name}] {offR.length} obligations, all verdicts match"
      else
        IO.println s!"[{name}] {offR.length} obligations, all verdicts match \
          (⚠️ {errs.length} obligation(s) are the SAME ERROR verdict on BOTH paths — pre-existing, \
          not a flag-on regression):"
        for (lbl, v) in errs do
          IO.println s!"    {lbl}: {v}"
    else
      IO.println s!"[{name}] ❌ VERDICT MISMATCH ({offR.length} off-obligations vs {onR.length} on-obligations)"
      -- Report every label whose canonical off/on verdict differs (present on only one side counts).
      let labels := (offR.map (·.1) ++ onR.map (·.1)).foldl
        (fun acc l => if acc.contains l then acc else acc ++ [l]) ([] : List String)
      for lbl in labels do
        let o := (offR.find? (·.1 == lbl)).map (·.2) |>.getD "<absent>"
        let n := (onR.find? (·.1 == lbl)).map (·.2) |>.getD "<absent>"
        if canonVerdict o != canonVerdict n then
          IO.println s!"    {lbl}: off={o} | on={n}"

-- Feature-spanning corpus (datatypes / maps / quantifiers / bitvectors / regex / recursive functions /
-- div-mod / cover+distinct / heap stress). Each is its own `#eval` for error isolation.
#eval checkVerdicts "mapGetPgm" mapGetPgm
#eval checkVerdicts "optionTesterPgm" optionTesterPgm
#eval checkVerdicts "funcPgm" funcPgm
#eval checkVerdicts "sizeIsLenPgm" sizeIsLenPgm
#eval checkVerdicts "enumPgm" enumPgm
#eval checkVerdicts "axiomPgm2" axiomPgm2
#eval checkVerdicts "roseTreeTesterPgm" roseTreeTesterPgm
#eval checkVerdicts "regexPgm1" regexPgm1
#eval checkVerdicts "advQuantPgm" advQuantPgm
#eval checkVerdicts "bvPgm" bvPgm
#eval checkVerdicts "divModPgm" divModPgm
#eval checkVerdicts "coverDistinctPgm" coverDistinctPgm
#eval checkVerdicts "heapStressPgm" heapStressPgm

end Core
