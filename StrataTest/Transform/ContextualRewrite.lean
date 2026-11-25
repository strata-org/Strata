/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Transform.ContextualRewrite
import StrataDDM.Integration.Lean.HashCommands

meta section

/-! # Contextual rewriting

The `contextualRewrite` phase rewrites each `assert` goal under the facts on its path, replaces
it by `true` when it rewrites to `true`, and leaves every other goal, every `cover`, every label
and all metadata alone.

Most tests run the default order of `--vcgen symexec` up to `betaReduce`, then
the phase, so the obligation program is the one symbolic execution writes, with its join
definitions. A test prints, for each check, whether the phase replaced its goal by `true`
(`proved`) or not (`kept`); a label ending in `_proved` or `_kept` says which is expected. Each
test also checks that the output is the input with only some `assert` goals replaced by `true`
(`shape: ok`). -/

namespace Strata.ContextualRewriteTest

private def parse (p : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-- The options of a `--vcgen symexec` run under merge mode `mode`. -/
private def opts (mode : Core.MergeMode := .always) : Core.VerifyOptions :=
  { Core.VerifyOptions.quiet with symExec := some mode }

/-- The default order of `o` with the phase after `betaReduce`, as `--phases` names it, checked
    to compose. -/
private def withPhase (o : Core.VerifyOptions) :
    Except String (Core.ValidatedPipeline Core.ProgramFactSet.empty) :=
  Core.splicePhasesAfter "betaReduce" [Core.passContextualRewrite] (Core.corePipelinePhases o)
    >>= Core.validatePipeline

/-- Run `phases` on `prog` from the state `σ0` (by default, one whose factory is Core's): the
    output program, the statistics the phases recorded, and the final state, or the error. -/
private def runPhases (prog : Core.Program) (phases : List Core.PipelinePhase)
    (σ0 : Core.Transform.CoreTransformState :=
      { Core.Transform.CoreTransformState.emp with factory := Core.Factory }) :
    Except String (Core.Program × _root_.Statistics × Core.Transform.CoreTransformState) :=
  let step (p : Core.Program) (ph : Core.PipelinePhase) :
      Core.Transform.CoreTransformM Core.Program := do
    let (_, out) ← ph.transform p
    return out
  match (phases.foldlM step prog).run σ0 with
  | (.ok out, σ) => .ok (out, σ.statistics, σ)
  | (.error e, _) => .error e.message

/-- The phases of the default order of `o` up to and including `betaReduce`. -/
private def upToBetaReduce (o : Core.VerifyOptions) : List Core.PipelinePhase :=
  let ps := Core.corePipelinePhases o
  ps.take ((ps.findIdx? (Core.phaseName · == "betaReduce")).getD ps.length + 1)

/-- The check of the command `c`, if it is an `assert` or a `cover`: its label, whether it is
    an `assert`, and its goal. -/
private def cmdCheck : Core.Command → Option (String × Bool × Core.Expression.Expr)
  | .cmd (.assert l e _) => some (l, true, e)
  | .cmd (.cover l e _) => some (l, false, e)
  | _ => none

mutual
/-- The checks of `s`: each `assert` and `cover`, with its label and goal. -/
private partial def stmtChecks : Core.Statement → List (String × Bool × Core.Expression.Expr)
  | .cmd c => (cmdCheck c).toList
  | .block _ ss _ => stmtsChecks ss
  | .ite _ ts es _ => stmtsChecks ts ++ stmtsChecks es
  | .loop _ _ _ body _ => stmtsChecks body
  | _ => []
/-- The checks of `ss`, in order. -/
private partial def stmtsChecks (ss : List Core.Statement) :
    List (String × Bool × Core.Expression.Expr) :=
  ss.flatMap stmtChecks
end

/-- The checks of the procedure bodies of `p`, in order; those of a control-flow graph block by
    block. -/
private def programChecks (p : Core.Program) : List (String × Bool × Core.Expression.Expr) :=
  p.decls.flatMap fun
    | .proc q _ => match q.body with
      | .structured ss _ => stmtsChecks ss
      | .cfg g _ => g.blocks.flatMap fun (_, b) => b.cmds.filterMap cmdCheck
      | .abstract => []
    | _ => []

mutual
/-- Whether `s'` is `s` with, at most, the goals of some `assert`s replaced by `true`: every
    label, every piece of metadata, every `cover` and every other statement unchanged. -/
private partial def sameShape : Core.Statement → Core.Statement → Bool
  | .cmd (.cmd (.assert l e md)), .cmd (.cmd (.assert l' e' md')) =>
    l == l' && decide (md = md') && (decide (e = e') || e'.isTrue)
  | .block l ss md, .block l' ss' md' => l == l' && decide (md = md') && sameShapes ss ss'
  | .ite c ts es md, .ite c' ts' es' md' =>
    decide (c = c') && decide (md = md') && sameShapes ts ts' && sameShapes es es'
  | .loop g m invs body md, .loop g' m' invs' body' md' =>
    decide (g = g') && decide (m = m') && decide (invs = invs') && decide (md = md') &&
      sameShapes body body'
  | s, s' => decide (s = s')
/-- `sameShape` on each pair of statements, for lists of the same length. -/
private partial def sameShapes (ss ss' : List Core.Statement) : Bool :=
  ss.length == ss'.length && (ss.zip ss').all fun (a, b) => sameShape a b
end

/-- Whether `g'` is the control-flow graph `g` with, at most, the goals of some `assert`s
    replaced by `true`. -/
private def sameCFG (g g' : Core.DetCFG) : Bool :=
  g.entry == g'.entry && g.blocks.length == g'.blocks.length &&
    (g.blocks.zip g'.blocks).all fun ((l, b), (l', b')) =>
      l == l' && decide (b.transfer = b'.transfer) && decide (b.md = b'.md) &&
        sameShapes (b.cmds.map .cmd) (b'.cmds.map .cmd)

/-- What happened to each check of `before` in `after`, and whether only `assert` goals
    changed. -/
private def report (before after : Core.Program) : IO Unit := do
  let cs := programChecks before
  let cs' := programChecks after
  for ((l, isAssert, e), (_, _, e')) in cs.zip cs' do
    let got := if !isAssert then (if decide (e = e') then "kept" else "changed")
      else if e.isTrue then "true already"
      else if e'.isTrue then "proved" else "kept"
    IO.println s!"{if isAssert then "" else "cover "}{l}: {got}"
  let sameDecls := before.decls.length == after.decls.length &&
    (before.decls.zip after.decls).all fun
      | (.proc q _, .proc q' _) => decide (q.header = q'.header) &&
          (match q.body, q'.body with
           | .structured ss o, .structured ss' o' => o == o' && sameShapes ss ss'
           | .cfg g o, .cfg g' o' => o == o' && sameCFG g g'
           | .abstract, .abstract => true
           | _, _ => false)
      | (.lemma l md, .lemma l' md') => l.name == l'.name && decide (md = md') &&
          (decide (l.e = l'.e) || l'.e.isTrue)
      | (d, d') => decide (d = d')
  IO.println s!"shape: {if sameDecls then "ok" else "CHANGED"}"

/-- The phase's statistics in `st`. -/
private def printStats (st : _root_.Statistics) : IO Unit :=
  for k in ["proved", "deadPaths", "budgetExhausted", "skippedLarge"] do
    IO.println s!"ContextualRewrite.{k}: {st.get s!"ContextualRewrite.{k}"}"

/-- Run the default order of `opts mode` on `p` up to `betaReduce`, then the phase, and
    `report`. With `stats`, also print the phase's statistics. -/
private def check (p : StrataDDM.Program) (mode : Core.MergeMode := .always)
    (stats : Bool := false) : IO Unit := do
  match runPhases (parse p) (upToBetaReduce (opts mode)) with
  | .error e => IO.println s!"error: {e}"
  | .ok (before, _, σ) =>
    -- The phase runs in the state the earlier phases leave, whose factory has the functions
    -- monomorphization added, with the statistics cleared.
    match runPhases before [Core.contextualRewritePhase] { σ with statistics := {} } with
    | .error e => IO.println s!"error: {e}"
    | .ok (after, st, _) =>
      report before after
      if stats then printStats st

/-- Type check `p`, run the phase alone on it, and `report`; with `stats`, also print the
    phase's statistics. -/
private def checkDirectCore (p : Core.Program) (stats : Bool := true) : IO Unit := do
  match Core.typeCheck .quiet p with
  | .error e => IO.println s!"error: {e}"
  | .ok typed =>
    match runPhases typed [Core.contextualRewritePhase] with
    | .error e => IO.println s!"error: {e}"
    | .ok (after, st, _) =>
      for (d, d') in typed.decls.zip after.decls do
        if let (.lemma l _, .lemma l' _) := (d, d') then
          IO.println s!"lemma {l.name}: {if l'.e.isTrue && !l.e.isTrue then "proved" else "kept"}"
      report typed after
      if stats then printStats st

/-- `checkDirectCore` on the program `p` parses to. -/
private def checkDirect (p : StrataDDM.Program) (stats : Bool := true) : IO Unit :=
  checkDirectCore (parse p) stats

/-! ## Facts from `assume`s, with connectives and the context they give -/

private def factPgm :=
#strata
program Core;
procedure P(x : int, y : int, b : bool, c : bool)
{
  assume [h]: int.gt(x, 0);
  assert [fact_proved]: int.gt(x, 0);
  assert [fact_kept]: int.gt(x, 1);
  assert [or_proved]: int.gt(x, 0) || int.lt(y, 5);
  assert [or_kept]: int.lt(y, 5) || int.lt(y, 6);
  assert [imp_proved]: int.gt(y, 0) ==> int.gt(y, 0);
  assert [imp_kept]: int.gt(y, 0) ==> int.gt(y, 1);
  assert [ite_proved]: if int.gt(y, 0) then int.gt(y, 0) else true;
  assert [ite_kept]: if int.gt(y, 0) then int.gt(y, 1) else true;
  assume [hbc]: b && c;
  assert [conj_proved]: c;
  assert [or_ctx_proved]: !b || b;
};
#end

-- `imp_proved` and `ite_proved` are proved by the context their conditions give, without a
-- fact of the path.
/--
info: fact_proved: proved
fact_kept: kept
or_proved: proved
or_kept: kept
imp_proved: proved
imp_kept: kept
ite_proved: proved
ite_kept: kept
conj_proved: proved
or_ctx_proved: proved
shape: ok
ContextualRewrite.proved: 6
ContextualRewrite.deadPaths: 0
ContextualRewrite.budgetExhausted: 0
ContextualRewrite.skippedLarge: 0
-/
#guard_msgs in
#eval check factPgm (stats := true)

/-- Verify `p` under `opts`, running the phase after `betaReduce` (`withPhase`), with a
    discharge that proves every query it receives, and print how many queries reached it. -/
private def dischargeCalls (p : StrataDDM.Program) : IO Unit := do
  let calls ← IO.mkRef (0 : Nat)
  let mk : Core.MkDischargeFn := fun _ _ _ _ _ _ _ _ _ =>
    fun _ _ _ _ _ _ _ => do
      calls.modify (· + 1)
      pure (.ok (.unsat, .unsat, Strata.SMT.EncoderState.init))
  let .ok vp := withPhase opts | IO.println "error: the order does not compose"
  match ← (Strata.Core.verifyProgram (parse p) (opts) (pipeline := some vp)
      (mkDischarge := mk)).toBaseIO with
  | .ok results => IO.println s!"results: {results.size}, discharge calls: {← calls.get}"
  | .error e => IO.println s!"error: {e}"

-- End to end, a goal the phase proves never reaches the discharge: only the four `_kept`
-- goals do.
/-- info: results: 10, discharge calls: 4 -/
#guard_msgs in
#eval dischargeCalls factPgm

/-! ## Testers and constructor equality -/

private def testerPgm :=
#strata
program Core;
datatype Option () { None(), Some(val: int) };
datatype Three () { A(), B(), C() };
procedure P(o : Option, p : Option, t : Three, u : Three, x : int, y : int)
{
  assume [isSomeO]: Option..isSome(o);
  assert [tester_true_proved]: !Option..isNone(o);
  assert [tester_true_kept]: Option..isNone(p);
  assume [notSome]: !Option..isSome(p);
  assert [tester_two_ctors_proved]: Option..isNone(p);
  assume [notA]: !Three..isA(t);
  assume [notB]: !Three..isB(t);
  assert [tester_others_false_proved]: Three..isC(t);
  assume [notAu]: !Three..isA(u);
  assert [tester_some_false_kept]: Three..isC(u);
  assert [ctor_injective_proved]: Some(x) == Some(y) ==> x == y;
  assert [ctor_eq_kept]: Some(x) == Some(y);
};
#end

/--
info: tester_true_proved: proved
tester_true_kept: kept
tester_two_ctors_proved: proved
tester_others_false_proved: proved
tester_some_false_kept: kept
ctor_injective_proved: proved
ctor_eq_kept: kept
shape: ok
-/
#guard_msgs in
#eval check testerPgm

/-! ### A function named like a copy

A program can declare a function named like the copy monomorphization makes of a tester
(monomorphization then names its copies with another prefix). The theories read a name as a
copy's only for a
function marked as one (`FuncAttr.monoCopyOf`), which monomorphization alone does, so such a
function is read by its own declaration, here `false`. A mark on a function the program
declares is dropped. -/

private def copyNamePgm :=
#strata
program Core;
datatype IntList { Nil(), Cons(hd : int, tl : IntList) };
function |$__mono#IntList..isCons#int|(l : IntList) : bool { false }
procedure P(x : int)
{
  assert [copyName_kept]: |$__mono#IntList..isCons#int|(Cons(x, Nil()));
  assert [tester_proved]: IntList..isCons(Cons(x, Nil()));
};
#end

/-- `p` with the functions it declares marked as copies of `IntList..isCons`. -/
private def markAsTesterCopy (p : Core.Program) : Core.Program :=
  { decls := p.decls.map fun
      | .func f md => .func { f with attr := f.attr.push (.monoCopyOf "IntList..isCons") } md
      | d => d }

/--
info: copyName_kept: kept
tester_proved: proved
shape: ok
-/
#guard_msgs in
#eval checkDirect copyNamePgm (stats := false)

/--
info: copyName_kept: kept
tester_proved: proved
shape: ok
-/
#guard_msgs in
#eval checkDirectCore (markAsTesterCopy (parse copyNamePgm)) (stats := false)

/-! ## Definitions of join variables

Each diamond merges `r` at the join: symbolic execution binds a fresh symbol to the merged
value and assumes their equality, and the goal mentions the symbol. -/

private def joinPgm :=
#strata
program Core;
datatype Option () { None(), Some(val: int) };
procedure Same(b : bool, out r : Option)
{
  if (b) { r := Some(1); } else { r := Some(2); }
  assert [join_same_ctor_proved]: Option..isSome(r);
};
procedure Guarded(b : bool, c : bool, out r : Option)
{
  assume [bc]: b && c;
  if (b) { r := Some(1); } else { r := None(); }
  assert [join_guarded_proved]: Option..isSome(r);
};
procedure Unguarded(b : bool, out r : Option)
{
  if (b) { r := Some(1); } else { r := None(); }
  assert [join_unguarded_kept]: Option..isSome(r);
};
procedure Nested(b : bool, c : bool, out r : Option, out s : Option)
{
  if (b) { r := Some(1); } else { r := Some(2); }
  if (c) { s := r; } else { s := Some(3); }
  assert [join_nested_proved]: Option..isSome(s);
};
#end

/--
info: join_same_ctor_proved: proved
join_guarded_proved: proved
join_unguarded_kept: kept
join_nested_proved: proved
shape: ok
-/
#guard_msgs in
#eval check joinPgm

/-! ## Map reads, sequence lengths and integer constants -/

private def mapPgm :=
#strata
program Core;
procedure P(m : Map int int, k : int, j : int, v : int, w : int, s : Sequence int, x : int)
{
  assert [map_same_key_proved]: m[k := v][k] == v;
  assert [map_same_key_kept]: m[k := v][j] == v;
  assert [map_other_key_proved]: m[1 := v][2] == m[2];
  assert [map_other_key_kept]: m[k := v][j] == m[j];
  assert [map_const_proved]: mapConst<int>(v)[k] == v;
  assert [map_const_kept]: mapConst<int>(v)[k] == w;
  assert [seq_length_proved]: Sequence.length(Sequence.build(Sequence.empty<int>(), x)) == 1;
  assert [seq_length_sym_proved]:
    Sequence.length(Sequence.build(s, x)) == int.add(Sequence.length(s), 1);
  assert [seq_length_kept]: Sequence.length(Sequence.build(s, x)) == 1;
  assert [int_le_proved]: int.le(x, x);
  assert [int_offset_proved]: int.lt(int.add(x, 1), int.add(x, 2));
  assert [int_kept]: int.le(x, j) ==> int.le(x, int.add(j, 1));
};
#end

/--
info: map_same_key_proved: proved
map_same_key_kept: kept
map_other_key_proved: proved
map_other_key_kept: kept
map_const_proved: proved
map_const_kept: kept
seq_length_proved: proved
seq_length_sym_proved: proved
seq_length_kept: kept
int_le_proved: proved
int_offset_proved: proved
int_kept: kept
shape: ok
-/
#guard_msgs in
#eval check mapPgm

/-! ## Negative cases

A fact learned in one branch does not hold in the other, nor after the branches merge. A goal whose
only proof needs arithmetic over variables is left for the solver. A `cover` is never
rewritten, even when its condition is a fact. -/

private def negativePgm :=
#strata
program Core;
procedure P(b : bool, x : int, y : int)
{
  if (b) {
    assume [pos]: int.gt(x, 0);
    assert [inThen_proved]: int.gt(x, 0);
  } else {
    assert [inElse_kept]: int.gt(x, 0);
  }
  assert [afterIf]: int.gt(x, 0);
  assume [big]: int.gt(y, 5);
  assert [arith_kept]: int.gt(y, 0);
  cover [cov_kept]: int.gt(y, 5);
};
#end

/--
info: inThen_proved: proved
inElse_kept: kept
afterIf: kept
arith_kept: kept
cover cov_kept: kept
shape: ok
-/
#guard_msgs in
#eval check negativePgm

-- The same program explored path by path: the checks after the `if` appear once per path, and
-- on the path through the `then` branch `pos` is still assumed, so `afterIf` is proved there.
/--
info: inThen_proved: proved
afterIf: proved
arith_kept: kept
cover cov_kept: kept
inElse_kept: kept
afterIf: kept
arith_kept: kept
cover cov_kept: kept
shape: ok
-/
#guard_msgs in
#eval check negativePgm (mode := .never)

/-! ## A contradiction only the engine sees

Symbolic execution ends a path at an assumption that is literally `false` or whose negation
is already assumed word for word; here the contradiction needs splitting `b && c`. -/

private def deadPgm :=
#strata
program Core;
procedure P(b : bool, c : bool, x : int)
{
  assume [bc]: b && c;
  assume [notB]: !b;
  assert [dead_proved]: int.gt(x, 100);
};
#end

/--
info: dead_proved: proved
shape: ok
ContextualRewrite.proved: 1
ContextualRewrite.deadPaths: 1
ContextualRewrite.budgetExhausted: 0
ContextualRewrite.skippedLarge: 0
-/
#guard_msgs in
#eval check deadPgm (stats := true)

/-! ## Well-formedness lemmas

Precondition elimination states that a function body uses `Option..val` only where its
precondition holds. Symbolic execution writes such lemmas, like every lemma, as checks under
the ground axioms, in a branch of the obligation procedure. -/

private def wfPgm :=
#strata
program Core;
datatype Option () { None(), Some(val: int) };
function g(o : Option) : int
  requires Option..isSome(o);
{ Option..val(o) }
#end

-- The lemma is `Option..isSome(o) ==> Option..isSome(o)`, proved by the context its antecedent
-- gives.
/--
info: g_body_calls_Option..val_0: proved
shape: ok
ContextualRewrite.proved: 1
ContextualRewrite.deadPaths: 0
ContextualRewrite.budgetExhausted: 0
ContextualRewrite.skippedLarge: 0
-/
#guard_msgs in
#eval check wfPgm (stats := true)

/-! ## The phase on lemma declarations

Run alone on a type-checked program, the phase rewrites the goal of each lemma under the
ground axioms declared before it. An axiom that is literally `false` ends every path. -/

private def lemmaPgm :=
#strata
program Core;
datatype Option () { None(), Some(val: int) };
function f(n : int) : Option;
axiom [fZero]: f(0) == Some(3);
lemma [lemma_proved]: Option..isSome(f(0));
lemma [lemma_kept]: Option..isSome(f(1));
axiom [contra]: false;
lemma [afterFalse_proved]: Option..isSome(f(1));
procedure P(x : int)
{
  assert [inProc_proved]: int.gt(x, 0);
};
#end

/--
info: lemma lemma_proved: proved
lemma lemma_kept: kept
lemma afterFalse_proved: proved
inProc_proved: proved
shape: ok
ContextualRewrite.proved: 3
ContextualRewrite.deadPaths: 1
ContextualRewrite.budgetExhausted: 0
ContextualRewrite.skippedLarge: 0
-/
#guard_msgs in
#eval checkDirect lemmaPgm

/-! ## Axioms about a name a body declares

Type checking rejects an axiom with a free variable, but a program built through the API can
have one, such as `x == 3` below, about a variable named like a local of a procedure. The
axiom says nothing about the local, so a body starts without the facts that mention a variable
it declares, at any depth. Each goal below is false in some run, and stays as it is. -/

private def axiomLocalPgm :=
#strata
program Core;
procedure Init()
{
  var x : int := 5;
  assert [init_kept]: x == 3;
};
procedure Nondet()
{
  var x : int;
  assert [nondet_kept]: x == 3;
};
procedure Branch(c : bool)
{
  if (c) {
    var x : int := 5;
    assert [branch_kept]: x == 3;
  }
};
procedure Loop(c : bool)
{
  while (c) {
    var x : int;
    assert [loop_kept]: x == 3;
  }
};
procedure Block()
{
  b: {
    var x : int := 5;
    assert [block_kept]: x == 3;
  }
};
#end

/-- `p` with the axiom `x == 3` on the free variable `x` declared first. -/
private def withAxiomOnX (p : Core.Program) : Core.Program :=
  let x : Core.Expression.Expr := .fvar Core.valueLoc ⟨"x", ()⟩ (some .int)
  let ax : Core.Axiom := { name := "ax", e := .eq Core.valueLoc x (.intConst Core.valueLoc 3) }
  { p with decls := .ax ax .empty :: p.decls }

/-- Type check `p`, add the axiom `x == 3` on the free variable `x`, which type checking
    rejects, run the phase alone, and `report`. -/
private def checkWithAxiomOnX (p : StrataDDM.Program) : IO Unit := do
  match Core.typeCheck .quiet (parse p) with
  | .error e => IO.println s!"error: {e}"
  | .ok typed =>
    let typed := withAxiomOnX typed
    match runPhases typed [Core.contextualRewritePhase] with
    | .error e => IO.println s!"error: {e}"
    | .ok (after, _, _) => report typed after

/--
info: init_kept: kept
nondet_kept: kept
branch_kept: kept
loop_kept: kept
block_kept: kept
shape: ok
-/
#guard_msgs in
#eval checkWithAxiomOnX axiomLocalPgm

/-! ## Terms larger than the size bound

A goal or assumption whose tree has more nodes than `maxTreeSize` is left alone: the goal is
kept and the assumption gives no fact. Each `r := int.add(r, r)` doubles the tree of `r`, whose
subterms symbolic execution shares. After 12 copies the assumption `large` and the goal
`largeGoal` are under the bound; after 15 copies both are over it, and each counts once. -/

private def smallPgm :=
#strata
program Core;
procedure P(x : int, b : bool, out r : int)
{
  assume [small]: int.gt(x, 0);
  r := x;
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  assume [large]: b && int.ge(int.add(r, r), 0);
  assert [small_proved]: int.gt(x, 0);
  assert [fromLarge]: b;
  assert [largeGoal]: int.ge(int.add(r, r), int.add(r, r));
};
#end

/--
info: small_proved: proved
fromLarge: proved
largeGoal: proved
shape: ok
ContextualRewrite.proved: 3
ContextualRewrite.deadPaths: 0
ContextualRewrite.budgetExhausted: 0
ContextualRewrite.skippedLarge: 0
-/
#guard_msgs in
#eval check smallPgm (stats := true)

private def largePgm :=
#strata
program Core;
procedure P(x : int, b : bool, out r : int)
{
  assume [small]: int.gt(x, 0);
  r := x;
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  r := int.add(r, r);
  assume [large]: b && int.ge(int.add(r, r), 0);
  assert [small_proved]: int.gt(x, 0);
  assert [fromLarge]: b;
  assert [largeGoal]: int.ge(int.add(r, r), int.add(r, r));
};
#end

/--
info: small_proved: proved
fromLarge: kept
largeGoal: kept
shape: ok
ContextualRewrite.proved: 1
ContextualRewrite.deadPaths: 0
ContextualRewrite.budgetExhausted: 0
ContextualRewrite.skippedLarge: 2
-/
#guard_msgs in
#eval check largePgm (stats := true)

/-! ## Calls, conditions, loops, definitions and exits

The tests below run the phase alone on a type-checked program, so the program keeps its calls,
its `if` conditions, its loops and its `exit`s. -/

/-! ### Calls

A call writes only its output and in-out arguments: the facts about them are forgotten, the
others kept. The callee's postcondition is not assumed. -/

private def callPgm :=
#strata
program Core;
procedure Q(a : int, inout c : int, out b : int)
spec { ensures [post]: int.gt(b, 0); }
{ b := 1; };
procedure P(x : int, inout y : int, out z : int)
{
  assume [hx]: int.gt(x, 0);
  assume [hy]: int.gt(y, 0);
  assume [hz]: int.gt(z, 0);
  call Q(x, inout y, out z);
  assert [call_notWritten_proved]: int.gt(x, 0);
  assert [call_inout_kept]: int.gt(y, 0);
  assert [call_out_kept]: int.gt(z, 0);
};
#end

/--
info: call_notWritten_proved: proved
call_inout_kept: kept
call_out_kept: kept
shape: ok
-/
#guard_msgs in
#eval checkDirect callPgm (stats := false)

/-! ### Conditions of `if`

The then branch has the condition, the else branch its negation. After the `if`, a fact both
branches establish holds; one only one branch establishes does not. -/

private def condPgm :=
#strata
program Core;
procedure P(x : int, y : int, w : int, b : bool)
{
  if (int.gt(x, 0)) {
    assert [cond_then_proved]: int.gt(x, 0);
  } else {
    assert [cond_else_proved]: !int.gt(x, 0);
  }
  assert [cond_after_kept]: int.gt(x, 0);
  if (b) {
    assume [y1]: int.gt(y, 0);
    assume [w1]: int.gt(w, 0);
  } else {
    assume [y2]: int.gt(y, 0);
  }
  assert [join_both_proved]: int.gt(y, 0);
  assert [join_one_kept]: int.gt(w, 0);
};
#end

/--
info: cond_then_proved: proved
cond_else_proved: proved
cond_after_kept: kept
join_both_proved: proved
join_one_kept: kept
shape: ok
-/
#guard_msgs in
#eval checkDirect condPgm (stats := false)

/-! ### Loops

The body has the guard, and the code after the loop its negation. A fact about a variable the
body writes holds before the first iteration only, so it is not kept; one about a variable
the body does not write is. The invariant is not assumed. -/

private def loopPgm :=
#strata
program Core;
procedure P(n : int, k : int, out i : int)
{
  assume [hk]: int.gt(k, 0);
  i := 0;
  assume [hi]: int.ge(i, 0);
  while (int.lt(i, n))
    invariant int.ge(i, 0)
  {
    assert [loop_guard_proved]: int.lt(i, n);
    assert [loop_unwritten_proved]: int.gt(k, 0);
    assert [loop_written_kept]: int.ge(i, 0);
    i := int.add(i, 1);
  }
  assert [loop_negGuard_proved]: !int.lt(i, n);
  assert [loop_invariant_kept]: int.ge(i, 0);
};
#end

/--
info: loop_guard_proved: proved
loop_unwritten_proved: proved
loop_written_kept: kept
loop_negGuard_proved: proved
loop_invariant_kept: kept
shape: ok
-/
#guard_msgs in
#eval checkDirect loopPgm (stats := false)

/-! ### Definitions from `init`

`var x : T := e` records `x == e`; a later write to `x` forgets it. -/

private def initPgm :=
#strata
program Core;
datatype Option () { None(), Some(val: int) };
procedure P(x : int, out r : Option)
{
  var o : Option := Some(x);
  assert [init_ctor_proved]: Option..isSome(o);
  var b : bool := int.gt(x, 0);
  assume [hb]: b;
  assert [init_def_proved]: int.gt(x, 0);
  var c : bool := int.gt(x, 1);
  assert [init_def_kept]: c;
  o := None();
  assert [init_written_kept]: Option..isSome(o);
};
#end

/--
info: init_ctor_proved: proved
init_def_proved: proved
init_def_kept: kept
init_written_kept: kept
shape: ok
-/
#guard_msgs in
#eval checkDirect initPgm (stats := false)

/-! ### `exit` out of a block

The facts after a block are those that hold at its end and at each `exit` that leaves it. No
state reaches a statement after an `exit`, so its goal becomes `true`. -/

private def exitPgm :=
#strata
program Core;
procedure P(x : int, y : int, w : int, b : bool)
{
  l: {
    if (int.gt(x, 0)) {
      assume [y1]: int.gt(y, 0);
      exit l;
    }
    assume [y2]: int.gt(y, 0);
  }
  assert [exit_join_proved]: int.gt(y, 0);
  m: {
    if (b) {
      exit m;
      assert [exit_after_proved]: false;
    }
    assume [w1]: int.gt(w, 0);
  }
  assert [exit_skips_kept]: int.gt(w, 0);
};
#end

/--
info: exit_join_proved: proved
exit_after_proved: proved
exit_skips_kept: kept
shape: ok
-/
#guard_msgs in
#eval checkDirect exitPgm (stats := false)

/-! ## A dead path under `deductiveAssumingSatisfiablePaths`

The assumptions contradict each other once `b && c` is split. That mode reports a goal that
reduces to `false` failing, on its premise that every path can be taken; the phase finds the
path dead and replaces the goal by `true`, which passes. -/

private def deadModePgm :=
#strata
program Core;
procedure P(b : bool, c : bool) { assume b && c; assume !b; assert [f]: false; };
#end

/-- Verify `p` under `--vcgen symexec` and `deductiveAssumingSatisfiablePaths` at the check
    level `level`, in the default order or, with `phase`, in that order with the phase
    (`withPhase`), and print each result. -/
private def verifyDeadMode (p : StrataDDM.Program) (phase : Bool)
    (level : Core.CheckLevel := .minimal) : IO Unit := do
  let o := { opts with checkMode := .deductiveAssumingSatisfiablePaths, checkLevel := level }
  let .ok vp := withPhase o | IO.println "error: the order does not compose"
  let pipeline := if phase then some vp else none
  match ← (Strata.Core.verifyProgram (parse p) o (pipeline := pipeline)).toBaseIO with
  | .ok results =>
    for r in results do
      IO.println s!"{r.obligation.label}: {r.formatOutcome}"
  | .error e => IO.println s!"error: {e}"

/--
info:

Obligation f: failed!

Result obtained during evaluation.
f: ❌ fail
-/
#guard_msgs in
#eval verifyDeadMode deadModePgm (phase := false)

/-- info: f: ✅ pass -/
#guard_msgs in
#eval verifyDeadMode deadModePgm (phase := true)

-- At the `full` check level, which also asks whether the goal can be reached, the mode reports
-- the goal reachable on its premise; with the phase, the solver finds it unreachable.
/--
info:

Obligation f: failed!

Result obtained during evaluation.
f: ❌ always false and is reachable from declaration entry
-/
#guard_msgs in
#eval verifyDeadMode deadModePgm (phase := false) (level := .full)

/-- info: f: ✅ pass (❗unreachable in this context) -/
#guard_msgs in
#eval verifyDeadMode deadModePgm (phase := true) (level := .full)

end Strata.ContextualRewriteTest
