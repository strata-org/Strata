/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core.IncrementalSolve
public import StrataDDM.Integration.Lean.HashCommands
meta import StrataTest.Languages.Core.Examples.DatatypePruningTestUtils

meta section

/-! # Removing irrelevant datatypes

With `removeIrrelevantDatatypes`, each query declares only the datatypes its
text mentions and the datatypes their constructor fields use. In each program
below, only the axiom `o_def` uses `o : Other`, and directed axiom pruning
drops it from the query for the goal, which does not mention `Other`. -/

namespace Core.RemoveIrrelevantDatatypes.Tests

/-- Print the datatype declarations in the query written for obligation
    `label` of `pgm`, one per line. -/
private def datatypeDecls (pgm : StrataDDM.Program)
    (options : Core.VerifyOptions) (label : String) : IO Unit := do
  let vcDir : System.FilePath := "_test_vcs_irrelevant_datatypes"
  if ← vcDir.pathExists then
    IO.FS.removeDirAll vcDir
  IO.FS.createDirAll vcDir
  let _ ← Strata.Core.verify pgm (options := { options with
    skipSolver := true, vcDirectory := vcDir,
    obligationsToVerify := some [label] })
  let mut decls := []
  for e in ← vcDir.readDir do
    if e.fileName.endsWith ".smt2" then
      let mut current : Option String := none
      for line in (← IO.FS.readFile e.path).splitOn "\n" do
        if line.startsWith "(declare-datatype" then
          if let some d := current then decls := decls ++ [d]
          current := some line
        else if line.startsWith " " then
          current := current.map (· ++ line)
        else
          if let some d := current then decls := decls ++ [d]
          current := none
      if let some d := current then decls := decls ++ [d]
  IO.FS.removeDirAll vcDir
  for d in decls do
    IO.println d

private def directed : Core.VerifyOptions :=
  { Core.VerifyOptions.quiet with removeIrrelevantAxioms := .Directed }

private def directedPruned : Core.VerifyOptions :=
  { directed with removeIrrelevantDatatypes := true }

def bucketPgm : StrataDDM.Program :=
#strata
program Core;
datatype Tag { T(on: bool) };
datatype Bucket { B(tag: Tag) };
datatype Other { O() };

const b : Bucket;
const o : Other;

axiom [o_def]: Other..isO(o);

procedure P()
{
  assert [uses_bucket]: Bucket..isB(b);
};
#end

-- Without the flag, the query declares `Other`, which only the dropped axiom
-- uses.
/--
info: (declare-datatype Tag (  (T (Tag..on Bool))))
(declare-datatype Bucket (  (B (Bucket..tag Tag))))
(declare-datatype Other (  (O)))
-/
#guard_msgs in
#eval datatypeDecls bucketPgm directed "uses_bucket"
-- With the flag, `Other` is gone, and `Tag` stays as the type of the field of
-- `Bucket`.
/--
info: (declare-datatype Tag (  (T (Tag..on Bool))))
(declare-datatype Bucket (  (B (Bucket..tag Tag))))
-/
#guard_msgs in
#eval datatypeDecls bucketPgm directedPruned "uses_bucket"

def varDeclPgm : StrataDDM.Program :=
#strata
program Core;
datatype Declared { D(k: int) };
datatype Other { O() };

const c : bool;
const o : Other;

axiom [o_def]: Other..isO(o);

procedure P()
{
  var d : Declared;
  havoc d;
  assert [goal]: c;
};
#end

-- `Declared` is left out: the query does not declare `d`, which nothing uses.
#guard_msgs in
#eval datatypeDecls varDeclPgm directedPruned "goal"

def varDefPgm : StrataDDM.Program :=
#strata
program Core;
datatype Defined { D(k: int) };
datatype Other { O() };

const c : bool;
const o : Other;

axiom [o_def]: Other..isO(o);

procedure P()
{
  var n : bool := forall x : Defined :: Defined..isD(x);
  assert [goal]: n || c;
};
#end

-- `Defined` stays because the definition of `n` mentions it.
/--
info: (declare-datatype Defined (  (D (Defined..k Int))))
-/
#guard_msgs in
#eval datatypeDecls varDefPgm directedPruned "goal"

def keptAxiomPgm : StrataDDM.Program :=
#strata
program Core;
datatype AxOnly { A(), B() };
datatype Other { O() };

const o : Other;

function p(x : int) : bool;

axiom [p_def]: p(1) ==
  (forall x : AxOnly :: AxOnly..isA(x) || AxOnly..isB(x));
axiom [o_def]: Other..isO(o);

procedure P()
{
  assert [uses_p]: p(1);
};
#end

-- `AxOnly` stays because the kept axiom `p_def` mentions it.
/--
info: (declare-datatype AxOnly (  (A)  (B)))
-/
#guard_msgs in
#eval datatypeDecls keptAxiomPgm directedPruned "uses_p"

def bodyPgm : StrataDDM.Program :=
#strata
program Core;
datatype Hidden { H(n: int) };
datatype Other { O() };

const m : int;
const o : Other;

function g(x : int) : int {
  Hidden..n(H(x))
}

axiom [o_def]: Other..isO(o);

procedure P()
{
  assert [uses_g]: g(m) == m;
};
#end

-- `Hidden` stays because the body of `g`, which the goal calls, uses it.
/--
info: (declare-datatype Hidden (  (H (Hidden..n Int))))
-/
#guard_msgs in
#eval datatypeDecls bodyPgm directedPruned "uses_g"

def mutualPgm : StrataDDM.Program :=
#strata
program Core;
datatype Forest { FNil(), FCons(head: RoseTree, tail: Forest) }
datatype RoseTree { Node(val: int, children: Forest) };
datatype Even { Zero(), ESucc(pred: Odd) }
datatype Odd { OSucc(pred: Even) };
datatype Other { O() };

const t : RoseTree;
const e : Even;
const o : Other;

axiom [o_def]: Other..isO(o) && Even..isZero(e);

procedure P()
{
  assert [uses_tree]: RoseTree..isNode(t);
};
#end

/--
info: (declare-datatypes ((Forest 0) (RoseTree 0))
  (((FNil) (FCons (Forest..head RoseTree) (Forest..tail Forest)))
  ((Node (RoseTree..val Int) (RoseTree..children Forest)))))
(declare-datatypes ((Even 0) (Odd 0))
  (((Zero) (ESucc (Even..pred Odd))) ((OSucc (Odd..pred Even)))))
(declare-datatype Other (  (O)))
-/
#guard_msgs (whitespace := lax) in
#eval datatypeDecls mutualPgm directed "uses_tree"
-- With the flag, `Forest` stays as a field type of `RoseTree`, and the
-- unused block of `Even` and `Odd` is gone.
/--
info: (declare-datatypes ((Forest 0) (RoseTree 0))
  (((FNil) (FCons (Forest..head RoseTree) (Forest..tail Forest)))
  ((Node (RoseTree..val Int) (RoseTree..children Forest)))))
-/
#guard_msgs (whitespace := lax) in
#eval datatypeDecls mutualPgm directedPruned "uses_tree"

def partialBlockPgm : StrataDDM.Program :=
#strata
program Core;
datatype Wrap { W(x: Inner) }
datatype Inner { I(n: int) };
datatype Other { O() };

const i : Inner;
const w : Wrap;
const o : Other;

axiom [o_def]: Other..isO(o) && Wrap..isW(w);

procedure P()
{
  assert [uses_inner]: Inner..isI(i);
};
#end

/--
info: (declare-datatypes ((Wrap 0) (Inner 0))
  (((W (Wrap..x Inner))) ((I (Inner..n Int)))))
(declare-datatype Other (  (O)))
-/
#guard_msgs (whitespace := lax) in
#eval datatypeDecls partialBlockPgm directed "uses_inner"
-- With the flag, `Inner` is declared alone, without the unused `Wrap` of its
-- block.
/--
info: (declare-datatype Inner (  (I (Inner..n Int))))
-/
#guard_msgs in
#eval datatypeDecls partialBlockPgm directedPruned "uses_inner"

def aliasPgm : StrataDDM.Program :=
#strata
program Core;
datatype Leaf { L(v: int) };
type A := Leaf;
datatype Holder { MkH(x: A) };
datatype Other { O() };

const h : Holder;
const o : Other;

axiom [o_def]: Other..isO(o);

procedure P()
{
  assert [uses_holder]: Holder..isMkH(h);
};
#end

-- `Leaf` stays: the field of `Holder` has type `A`, an alias of `Leaf`.
/--
info: (declare-datatype Leaf (  (L (Leaf..v Int))))
(declare-datatype Holder (  (MkH (Holder..x Leaf))))
-/
#guard_msgs in
#eval datatypeDecls aliasPgm directedPruned "uses_holder"

def typeArgPgm : StrataDDM.Program :=
#strata
program Core;
datatype Leaf { L(v: int) };
datatype Box (a : Type) { MkBox(item: a) };
datatype Other { O() };

const bx : Box Leaf;
const o : Other;

axiom [o_def]: Other..isO(o);

procedure P()
{
  assert [uses_box]: Box..isMkBox(bx);
};
#end

-- `Leaf` stays: it appears only as the type argument of `Box Leaf`.
/--
info: (declare-datatype Leaf (  (L (Leaf..v Int))))
(declare-datatype Box (par (a) (  (MkBox (Box..item a)))))
-/
#guard_msgs in
#eval datatypeDecls typeArgPgm directedPruned "uses_box"

/-- Print the datatypes declared to the solver and a line per check, in order,
    as the incremental back end walks `pgm` with one solver, then whether each
    goal passed. -/
private def incrementalDecls (pgm : StrataDDM.Program)
    (options : Core.VerifyOptions) : IO Unit := do
  let log ← IO.mkRef (#[] : Array String)
  let wrap
      (s : Strata.SMT.AbstractSolver Strata.SMT.Term Strata.SMT.TermType IO) :=
    { s with
      declareDatatype := fun n ps k => do
        log.modify (·.push s!"declare {n}")
        s.declareDatatype n ps k
      declareDatatypes := fun ds k => do
        log.modify (·.push s!"declare {ds.map (·.1)}")
        s.declareDatatypes ds k
      checkSatAssuming := fun ts => do
        log.modify (·.push "check")
        s.checkSatAssuming ts }
  let program := (Strata.TransM.run Inhabited.default
    (Strata.translateProgram pgm)).fst
  match ← Core.IncrementalSolve.verifyProgram program 1 options
      (wrapSolver := wrap) with
  | .ok (results, _) =>
    for l in ← log.get do
      IO.println l
    for r in results do
      let outcome := if r.isSuccess then "pass" else "fail"
      IO.println s!"{r.obligation.label}: {outcome}"
  | .error e => IO.println s!"error: {e}"

def twoGoalsPgm : StrataDDM.Program :=
#strata
program Core;
datatype Tag { T(on: bool) };
datatype Bucket { B(tag: Tag) };
datatype Hidden { H(n: int) };
datatype Other { O() };

const b : Bucket;
const m : int;
const o : Other;

function g(x : int) : int {
  Hidden..n(H(x))
}

axiom [o_def]: Other..isO(o);

procedure P()
{
  assert [uses_bucket]: Bucket..isB(b);
  assert [uses_g]: g(m) == m;
};
#end

-- The incremental back end declares `Other` only without the flag.
/--
info: declare Tag
declare Bucket
declare Other
check
declare Hidden
check
uses_bucket: pass
uses_g: pass
-/
#guard_msgs in
#eval incrementalDecls twoGoalsPgm directed
/--
info: declare Tag
declare Bucket
check
declare Hidden
check
uses_bucket: pass
uses_g: pass
-/
#guard_msgs in
#eval incrementalDecls twoGoalsPgm directedPruned

-- The solver accepts the pruned queries.
/--
info:
Obligation: uses_bucket
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify bucketPgm (options := directedPruned)
/--
info:
Obligation: uses_tree
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify mutualPgm (options := directedPruned)
/--
info:
Obligation: uses_bucket
Property: assert
Result: ✅ pass

Obligation: uses_g
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify twoGoalsPgm (options := directedPruned)

-- Every program above verifies identically with and without the flag.
/--
info: 10 of 10 the same
-/
#guard_msgs in
#eval TestUtils.sameWithFlag
  [bucketPgm, varDeclPgm, varDefPgm, keptAxiomPgm, bodyPgm, mutualPgm,
   partialBlockPgm, aliasPgm, typeArgPgm, twoGoalsPgm]

end Core.RemoveIrrelevantDatatypes.Tests
end
