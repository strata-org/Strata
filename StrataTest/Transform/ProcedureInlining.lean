/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
meta import StrataDDM.Util.Format
meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core.StatementSemantics
meta import Strata.Languages.Core.ProgramType
meta import Strata.Languages.Core.ProgramWF
meta import Strata.Transform.CoreTransform
meta import Strata.Transform.ProcedureInlining
meta import Strata.Util.Tactics
meta import StrataTest.Transform.CallFixtures
meta import StrataTest.Languages.Core.Tests.TestUtil

meta section

open Core
private abbrev testLoc : ExprSourceLoc := ExprSourceLoc.synthesized "test"
open Core.Transform
open ProcedureInlining
open Strata
open Std
open Core.CallFixtures (runInlineCall tryInlineCall)

/-! ## Procedure Inlining Examples -/

section ProcedureInliningExamples


-- Alpha equivalence of procedures for testing!


structure IdMap where
  vars: (Map String String × Map String String)
  labels: Map String String

private def IdMap.updateVars (map:IdMap) (newmap: List (String × String))
  : Except Format IdMap := do
  let newvars ← newmap.foldlM (fun (m1, m2) ((oldid,newid):String × String) =>
    match Map.find? m1 oldid, Map.find? m2 newid with
    | .some x, _ => .error  (f!"Has duplicated definition of var " ++ oldid ++
        "(previously mapped to " ++ x ++ ")")
    | _, .some y => .error  (f!"Has duplicated definition of var " ++ newid ++
        "(previously mapped to " ++ y ++ ")")
    | .none, .none => return (m1.insert oldid newid, m2.insert newid oldid))
    map.vars
  return { map with vars := newvars }

private def IdMap.updateLabel (map:IdMap) (frlbl:String) (tolbl:String)
  : Except Format IdMap := do
  match Map.find? map.labels frlbl with
  | .none =>
    return { map with labels := Map.insert map.labels frlbl tolbl }
  | .some x =>
    if x == tolbl then return map
    else .error ("Label " ++ frlbl ++ " is already mapped to " ++ x ++
      " but tried to map to " ++ tolbl)

private def IdMap.lblMapsTo (map:IdMap) (fr:String) (to:String): Bool :=
  match Map.find? map.labels fr with
  | .none => false
  | .some x => x == to


private def substExpr (e1:Expression.Expr) (map:Map String String) :=
  map.foldl
    (fun (e:Expression.Expr) ((i1,i2):String × String) =>
      -- old_id has visibility of temp because the new local variables were
      -- created by CoreGenM.
      -- All variables now have Unit metadata; we substitute by name.
      let old_id : Expression.Ident := { name := i1, metadata := () }
      let new_expr : Expression.Expr := .fvar testLoc { name := i2, metadata := () } .none
      e.substFvar old_id new_expr)
    e1

/-- Alpha-equivalence of expressions, ignoring types and source locations
    (the expected program is parsed from different text). -/
private def alphaEquivExprs (e1 e2: Expression.Expr) (map:IdMap)
    : Bool :=
  (substExpr e1 (map.vars.fst)).eraseTypes.eqModuloMeta e2.eraseTypes &&
  (substExpr e2 (map.vars.snd)).eraseTypes.eqModuloMeta e1.eraseTypes

private def alphaEquivExprsOpt (e1 e2: Option Expression.Expr) (map:IdMap)
    : Except Format Bool :=
  match e1,e2 with
  | .some e1, .some e2 =>
    return alphaEquivExprs e1 e2 map
  | .none, .none =>
    return .true
  | _, _ =>
    .error ".some and .none mismatch"

private def alphaEquivLoopInvs (l1 l2 : List (String × Expression.Expr)) (map : IdMap)
    : Except Format Bool :=
  if l1.length != l2.length then
    .error "invariant lists have different lengths"
  else
    return (l1.zip l2).all (fun ((lbl1, a), (lbl2, b)) =>
      lbl1 == lbl2 && alphaEquivExprs a b map)

private def alphaEquivIdents (e1 e2: Expression.Ident) (map:IdMap)
    : Bool :=
  (match Map.find? map.vars.fst e1.name, Map.find? map.vars.snd e2.name with
    | .some n', .some m' => n' == e2.name && m' == e1.name
    | .none, .none => e1.name == e2.name
    | _, _ => false )


mutual

def alphaEquivBlock (b1 b2: Core.Block) (map:IdMap)
    : Except Format IdMap := do
  match b1, b2 with
  | [], [] => .ok map
  | bs1 :: bss1, bs2 :: bss2 =>
    let newmap ← alphaEquivStatement bs1 bs2 map
    alphaEquivBlock bss1 bss2 newmap
  | _, _ => .error "Block lengths do not match"

def alphaEquivStatement (s1 s2: Core.Statement) (map:IdMap)
    : Except Format IdMap := do
  let mk_err (s:Format): Except Format IdMap :=
    .error (f!"{s}\ns1:{s1}\ns2:{s2}\nmap:{map.vars}")

  match s1, s2 with
  | .block lbl1 b1 _, .block lbl2 b2 _ =>
    -- Since 'exit lbl' can reference an enclosing block, update the label
    -- map here
    let map ← IdMap.updateLabel map lbl1 lbl2
    alphaEquivBlock b1 b2 map

  | .ite cond1 thenb1 elseb1 _, .ite cond2 thenb2 elseb2 _ => do
    let condsMatch := match cond1, cond2 with
      | .det e1, .det e2 => alphaEquivExprs e1 e2 map
      | .nondet, .nondet => true
      | _, _ => false
    if condsMatch then
      let map' <- alphaEquivBlock thenb1 thenb2 map
      let map'' <- alphaEquivBlock elseb1 elseb2 map'
      return map''
    else
      .error "if conditions do not match"

  | .loop g1 m1 i1 b1 _, .loop g2 m2 i2 b2 _ =>
    let guardsMatch := match g1, g2 with
      | .det e1, .det e2 => alphaEquivExprs e1 e2 map
      | .nondet, .nondet => true
      | _, _ => false
    if !guardsMatch then
      .error "guard does not match"
    else if ¬ (← alphaEquivExprsOpt m1 m2 map) then
      .error "measure does not match"
    else if ¬ (← alphaEquivLoopInvs i1 i2 map) then
      .error "invariant does not match"
    else alphaEquivBlock b1 b2 map

  | .exit l1 _, .exit l2 _ =>
    IdMap.updateLabel map l1 l2

  | .cmd c1, .cmd c2 =>
    match c1, c2 with
    | .call procName1 _ callArgs1 _, .call procName2 _ callArgs2 _ =>
      let lhs1 := Imperative.CallArg.getLhs callArgs1
      let lhs2 := Imperative.CallArg.getLhs callArgs2
      let args1 := Imperative.CallArg.getInArgs callArgs1
      let args2 := Imperative.CallArg.getInArgs callArgs2
      if procName1 ≠ procName2 then
        .error "Procedure name does not match"
      else if lhs1.length ≠ lhs2.length then
        .error "Call LHS length does not match"
      else if ¬ (lhs1.zip lhs2).all
          (fun (lhs1,lhs2) => alphaEquivIdents lhs1 lhs2 map) then
        .error "Call LHS name does not map"
      else if (args1.length ≠ args2.length) then
        .error "Call args length does not match"
      else if ¬ (args1.zip args2).all (fun (arg1,arg2) =>
          ¬ alphaEquivExprs arg1 arg2 map) then
        .error "Call args do not map"
      else
        return map
    | .cmd (.init n1 _ _e1 _), .cmd (.init n2 _ _e2 _) =>
      -- Omit e1 and e2 check because init may use undeclared free vars
      -- The updateVars below must be the only place that updates the
      -- variable name mapping.
      IdMap.updateVars map [(n1.name,n2.name)]
    | .cmd (.set n1 (.det e1) _), .cmd (.set n2 (.det e2) _) =>
      if ¬ alphaEquivExprs e1 e2 map then
        mk_err f!"RHS of sets do not match \
        \n(subst of e1: {repr (substExpr e1 map.vars.fst)})\n(e2: {repr e2})
        \n(subst of e2: {repr (substExpr e2 map.vars.snd)})\n(e1: {repr e1})"
      else if ¬ alphaEquivIdents n1 n2 map then
        mk_err "LHS of sets do not match"
      else
        return map
    | .cmd (.set n1 .nondet _), .cmd (.set n2 .nondet _) =>
      if ¬ alphaEquivIdents n1 n2 map then
        mk_err "LHS of sets do not match"
      else
        return map
    | .cmd (.assert _ e1 _), .cmd (.assert _ e2 _) =>
      if ¬ alphaEquivExprs e1 e2 map then
        mk_err "Expressions of asserts do not match"
      else
        return map
    | .cmd (.assume _ e1 _), .cmd (.assume _ e2 _) =>
      if ¬ alphaEquivExprs e1 e2 map then
        mk_err "Expressions of assumes do not match"
      else
        return map
    | _, _ =>
      mk_err "Commands do not match"

  | _, _ => mk_err "Statements do not match"

end

private def alphaEquiv (p1 p2:Core.Procedure):Except Format Bool := do
  match p1.body, p2.body with
  | .structured ss1 _, .structured ss2 _ =>
    if ss1.length ≠ ss2.length then
      .error (s!"# statements do not match: in {p1.header.name}, "
          ++ s!"inlined fn one has {ss1.length}"
          ++ s!" whereas the answer has {ss2.length}")
    else
      let newmap:IdMap := IdMap.mk ([], []) []
      let m ← List.foldlM (fun (map:IdMap) (s1,s2) =>
          alphaEquivStatement s1 s2 map)
        newmap (ss1.zip ss2)
      return ((p1.header.outputs.zip p2.header.outputs).map (fun ((x, _), (y, _)) => alphaEquivIdents x y m)).all id
  | _, _ => .error f!"alphaEquiv: CFG procedure bodies are not supported in the inlining test harness"



def translate (t : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

def checkInlining (prog : Core.Program) (progAns : Core.Program)
    : Except Format Bool := do
  let prog' := runInlineCall prog
  let pp' := prog'.decls.zip progAns.decls
  pp'.allM (fun (p,p') => do
    match p,p' with
    | .proc p _, .proc p' _ =>
      match alphaEquiv p p' with
      | .ok _ => return .true
      | .error msg =>
        dbg_trace s!"----- Inlined program ----"
        dbg_trace s!"{toString prog'}"
        dbg_trace s!"----- Answer ----"
        dbg_trace s!"{toString progAns}"
        .error msg
    | _, _ => .error "?")



def Test1 :=
#strata
program Core;
procedure f(x : bool, out y : bool) {
  y := !x;
};

procedure h() {
  var b_in : bool;
  var b_out : bool;
  call f(b_in, out b_out);
};
#end

def Test1Ans :=
#strata
program Core;
procedure f(x : bool, out y : bool) {
  y := !x;
};

procedure h() {
  var b_in : bool;
  var b_out : bool;
  inlined: {
    var tmp_arg_0 : bool := b_in;
    var tmp_arg_1 : bool;
    tmp_arg_1 := !tmp_arg_0;
    b_out := tmp_arg_1;
  }
};

#end

/--
info: ok: true
-/
#guard_msgs in
#eval checkInlining (translate Test1) (translate Test1Ans)

def Test2 :=
#strata
program Core;
procedure f(x : bool, out y : bool) {
  body: {
    if (x) {
      exit body;
    } else { y := false;
    }
  }
};

procedure h() {
  var b_in : bool;
  var b_out : bool;
  call f(b_in, out b_out);
  _exit: {}
};
#end

def Test2Ans :=
#strata
program Core;
procedure f(x : bool, out y : bool) {
  body: {
    if (x) {
      exit body;
    } else { y := false;
    }
  }
};

procedure h() {
  var b_in : bool;
  var b_out : bool;
  inlined: {
    var f_x : bool := b_in;
    var f_y : bool;
    f_body: {
      if (f_x) {
        exit f_body;
      } else {
        f_y := false;
      }
    }
    b_out := f_y;
  }
  _exit: {}
};

#end

/--
info: ok: true
-/
#guard_msgs in
#eval checkInlining (translate Test2) (translate Test2Ans)


--- Test procedure calls inside subblocks

def Test3 :=
#strata
program Core;
procedure f(x : int, out y : int) {
  y := x;
};

procedure g() {
  var f_out : int;
  if (true) {
    call f(1, out f_out);
  } else {
    call f(2, out f_out);
  }
};
#end

def Test3Ans :=
#strata
program Core;
procedure f(x : int, out y : int) {
  y := x;
};

procedure g() {
  var f_out : int;
  if (true) {
    inlined1: {
      var f_x : int := 1;
      var f_y : int;
      f_y := f_x;
      f_out := f_y;
    }
  } else {
    inlined1: {
      var f_x2 : int := 2;
      var f_y2 : int;
      f_y2 := f_x2;
      f_out := f_y2;
    }
  }
};
#end

/--
info: ok: true
-/
#guard_msgs in
#eval checkInlining (translate Test3) (translate Test3Ans)


def TestRecursiveCall :=
#strata
program Core;
procedure a1() {
};
procedure a2() {
};

procedure f() {
  call a1();
  call a2();
  call f();
};
#end

def setCallGraph (p : Core.Program) : CoreTransformM Unit :=
  modify (fun σ => { σ with cachedAnalyses :=
    { callGraph := Program.toProcedureCG p } })

def test := do
  let p := translate TestRecursiveCall
  let _ ← setCallGraph p
  let (changed, _p) ← runProgramTyped (targetProcList := .some ["f"])
    (inlineCallCmd (p.typeNamesWithPrefix inlineTyPrefix)
      (doInline := fun _caller callee _ => callee = "f")) p
  let cg := (← get).cachedAnalyses.callGraph
  return (changed, cg)

/--
info: true, some CallGraph(callees: [("a1", []),
("a2", []),
("f", [("a1", 2), ("a2", 2), ("f", 1)])],
         callers: [("a1", [("f", 2)]),
("a2", [("f", 2)]),
("f", [("f", 1)])])
-/
#guard_msgs in
#eval ((match test .emp with
  | ⟨.ok (changed, cg), _⟩ => f!"{repr changed}, {repr cg}"
  | ⟨.error m, _⟩ => panic! s!"{m}"))



/- Check CallGraph cache of CoreTransformState -/

def TestThreeChain :=
#strata
program Core;
procedure leaf(x : int, out y : int) {
  y := int.add(x, 1);
};
procedure mid(a : int, out b : int) {
  call leaf(a, out b);
};
procedure top(n : int, out r : int) {
  call mid(n, out r);
};
#end

/-- After fully inlining the 3-procedure chain, the cached call graph must
    equal the call graph freshly computed from the output program. -/
def testThreeChainCG := do
  let p := translate TestThreeChain
  let _ ← setCallGraph p
  let (_, p') ← runProgramUntilTyped
    (inlineCallCmd (p.typeNamesWithPrefix inlineTyPrefix)) p
  let cachedCG := (← get).cachedAnalyses.callGraph
  let freshCG := p'.toProcedureCG
  return (cachedCG.map (· == freshCG))

/-- info: some true -/
#guard_msgs in
#eval ((match testThreeChainCG .emp with
  | ⟨.ok result, _⟩ => f!"{repr result}"
  | ⟨.error m, _⟩ => s!"ERROR: {m}"))


/- A polymorphic callee inlined at two different concrete types. Each inlining
   site instantiates the callee's type parameter at its own argument type, so
   one block uses `int` and the other `bool`. -/
def TestPolyTwoTypes :=
#strata
program Core;
procedure PolyId<a>(inout T : a) {
  assert [inner]: old T == T;
};
procedure Caller() {
  var I : int := 0;
  var B : bool := true;
  call PolyId(inout I);
  call PolyId(inout B);
};
#end

-- Type-checking the inlined program prints `ok: <program>`, confirming both
-- sites are well-typed.
/--
info: ok: program Core;

procedure PolyId<a> (inout T : a)
{
  assert [inner]: old T == T;
};
procedure Caller ()
{
  var I : int := 0;
  var B : bool := true;
  $__inline1_PolyId$inlined: {
    var $__inline1_T : int := I;
    var $__inline1$old_T : int := $__inline1_T;
    assert [$__inline1_inner]: $__inline1$old_T == $__inline1_T;
    I := $__inline1_T;
  }
  $__inline2_PolyId$inlined: {
    var $__inline2_T : bool := B;
    var $__inline2$old_T : bool := $__inline2_T;
    assert [$__inline2_inner]: $__inline2$old_T == $__inline2_T;
    B := $__inline2_T;
  }
};
-/
#guard_msgs in
#eval Core.typeCheck .quiet (runInlineCall (translate TestPolyTwoTypes))

/-- Inline the calls of the procedures `procs` of `p`, formatting the result or the error. -/
private def inlineShown (p : Core.Program) (procs : List String) : String :=
  match (runProgramTyped (targetProcList := some procs)
      (inlineCallCmd (p.typeNamesWithPrefix inlineTyPrefix)) p) .emp with
  | ⟨.ok (_, res), _⟩ => toString res.eraseTypes
  | ⟨.error e, _⟩ => s!"error: {e}"

/-- A structured caller of a CFG callee. -/
private def TestCFGCallee :=
#strata
program Core;
procedure leaf(x : int, out y : int)
cfg entry {
  entry: { y := int.add(x, 1); return; }
};
procedure top(n : int, out r : int) {
  call leaf(n, out r);
};
#end

-- A CFG callee is not inlined into structured code.
/-- info: error: cannot inline procedure with CFG body into structured code -/
#guard_msgs in
#eval IO.println (inlineShown (translate TestCFGCallee) ["top"])

/-- A CFG caller of a structured callee. -/
private def TestCFGCaller :=
#strata
program Core;
procedure leaf(x : int, out y : int) {
  y := int.add(x, 1);
};
procedure top(n : int, out r : int)
cfg entry {
  entry: { call leaf(n, out r); return; }
};
#end

-- A CFG caller is not walked.
/--
info: error: runProgram: cannot apply statement-level transform to CFG body
  (procedure 'top')
-/
#guard_msgs (whitespace := lax) in
#eval IO.println (inlineShown (translate TestCFGCaller) ["top"])

/-- `p` with the body of its procedure `name` marked opaque (`Body.isOpaque`). -/
private def markOpaque (name : String) (p : Core.Program) : Core.Program :=
  { p with decls := p.decls.map fun
    | .proc q md =>
      if q.header.name.name == name then
        .proc { q with body := match q.body with
          | .structured ss _ => .structured ss true
          | b => b } md
      else .proc q md
    | d => d }

/-- A caller of a callee with a body and a postcondition. -/
private def TestOpaqueCallee :=
#strata
program Core;
procedure leaf(x : int, out y : int)
spec { ensures int.gt(y, x); }
{
  y := int.add(x, 1);
};
procedure top(n : int, out r : int) {
  call leaf(n, out r);
};
#end

-- An opaque callee is inlined as its contract: its postcondition is assumed after the havoc of
-- its output, and its body is not inlined.
/--
info: program Core;

procedure leaf (x : int, out y : int)
spec {
  ensures [leaf_ensures_0]: int.gt(y, x);
  } opaque {
  y := int.add(x, 1);
};
procedure top (n : int, out r : int)
{
  $__inline1_leaf$inlined: {
    var $__inline1_x : int := n;
    var $__inline1_y : int;
    assume [$__inline1_leaf_ensures_0]: int.gt($__inline1_y, $__inline1_x);
    r := $__inline1_y;
  }
};
-/
#guard_msgs in
#eval IO.println (inlineShown (markOpaque "leaf" (translate TestOpaqueCallee)) ["top"])

end ProcedureInliningExamples

/-! ## Inlining at the call's type instance

Each program below except `unknownProg` and `conflictProg` is a fully annotated Core AST.
The printed result shows the types inlining gives the callee's variables; the `#guard` checks
that every expression of the result carries its type annotations. -/
section CallInstanceTests
open Lambda
open Core.CallFixtures Core.TestUtil

private def idpP : Decl :=
  mkProc "idp" ["a"] [("x", tv "a")] [("r", tv "a")] (body := [setS "r" (v "x" (tv "a"))])
private def swapP : Decl :=
  mkProc "swap" ["a"] [("x", tv "a"), ("y", tv "a")] [("x", tv "a"), ("y", tv "a")] (body :=
    [Statement.init "t" (.forAll [] (tv "a")) (.det (v "x" (tv "a"))) .empty,
     setS "x" (v "y" (tv "a")), setS "y" (v "t" (tv "a")),
     Statement.assert "swapped" (eqE (v "x" (tv "a")) (v (CoreIdent.mkOld "y").name (tv "a"))) #[]])
private def seqP : Decl :=
  mkProc "p" ["a"] [("s", seqTy (seqTy (tv "a")))] [] (body :=
    [Statement.assert "refl" (eqE (v "s" (seqTy (seqTy (tv "a")))) (v "s" (seqTy (seqTy (tv "a")))))
      #[]])
private def pairP : Decl :=
  mkProc "pair" ["a", "b"] [("x", tv "a"), ("y", tv "b")] [("r", tv "a")]
    (body := [setS "r" (v "x" (tv "a"))])
/-- `q<a>()` assumes `forall y : a :: y == y`. -/
private def qP : Decl :=
  mkProc "q" ["a"] [] [] (body := [Statement.assume "refl" (reflAll (tv "a")) #[]])
/-- `r<a, b>(x : a)` with `b` only in an assumption of its body. -/
private def rP : Decl :=
  mkProc "r" ["a", "b"] [("x", tv "a")] [] (body :=
    [Statement.assert "refl" (eqE (v "x" (tv "a")) (v "x" (tv "a"))) #[],
     Statement.assume "reflB" (reflAll (tv "b")) #[]])

/--
info: program Core;

procedure idp<a> (x : a, out r : a)
{
  r := x;
};
procedure Caller ()
{
  var ai : int;
  $__inline1_idp$inlined: {
    var $__inline1_x : int := 7;
    var $__inline1_r : int;
    $__inline1_r := $__inline1_x;
    ai := $__inline1_r;
  }
};
-/
#guard_msgs in
#eval IO.println (toString (runInlineCall (idpProg idpP)))
#guard (runInlineCall (idpProg idpP)).allExprs LExpr.fullyAnnotated

/--
info: program Core;

procedure swap<a> (inout x : a, inout y : a)
{
  var t : a := x;
  x := y;
  y := t;
  assert [swapped]: x == old y;
};
procedure Caller ()
{
  var i : int;
  var j : int;
  $__inline1_swap$inlined: {
    var $__inline1_x : int := i;
    var $__inline1_y : int := j;
    var $__inline1$old_x : int := $__inline1_x;
    var $__inline1$old_y : int := $__inline1_y;
    var $__inline1_t : int := $__inline1_x;
    $__inline1_x := $__inline1_y;
    $__inline1_y := $__inline1_t;
    assert [$__inline1_swapped]: $__inline1_x == $__inline1$old_y;
    i := $__inline1_x;
    j := $__inline1_y;
  }
};
-/
#guard_msgs in
#eval IO.println (toString (runInlineCall (swapProg swapP)))
#guard (runInlineCall (swapProg swapP)).allExprs LExpr.fullyAnnotated

/--
info: program Core;

procedure p<a> (s : Sequence (Sequence a))
{
  assert [refl]: s == s;
};
procedure Caller (t : Sequence (Sequence int))
{
  $__inline1_p$inlined: {
    var $__inline1_s : Sequence (Sequence int) := t;
    assert [$__inline1_refl]: $__inline1_s == $__inline1_s;
  }
};
-/
#guard_msgs in
#eval IO.println (toString (runInlineCall (seqProg seqP)))
#guard (runInlineCall (seqProg seqP)).allExprs LExpr.fullyAnnotated

/--
info: program Core;

procedure idp<a> (x : a, out r : a)
{
  r := x;
};
procedure Caller<a> (z : a)
{
  var w : a;
  $__inline1_idp$inlined: {
    var $__inline1_x : a := z;
    var $__inline1_r : a;
    $__inline1_r := $__inline1_x;
    w := $__inline1_r;
  }
};
-/
#guard_msgs in
#eval IO.println (toString (runInlineCall (sameNameProg idpP)))
#guard (runInlineCall (sameNameProg idpP)).allExprs LExpr.fullyAnnotated

/--
info: program Core;

procedure pair<a, b> (x : a, y : b, out r : a)
{
  r := x;
};
procedure Caller<a, b> (x : a, y : b)
{
  var w : b;
  $__inline1_pair$inlined: {
    var $__inline1_x : b := y;
    var $__inline1_y : a := x;
    var $__inline1_r : b;
    $__inline1_r := $__inline1_x;
    w := $__inline1_r;
  }
};
-/
#guard_msgs in
#eval IO.println (toString (runInlineCall (pairProg pairP)))
#guard (runInlineCall (pairProg pairP)).allExprs LExpr.fullyAnnotated

/--
info: program Core;

type $__inlinety_0;
procedure q<a> ()
{
  assume [refl]: forall y : a :: y == y;
};
procedure Caller ()
{
  $__inline1_q$inlined: {
    assume [$__inline1_refl]: forall y : $__inlinety_0 :: y == y;
  }
};
-/
#guard_msgs in
#eval IO.println (toString (runInlineCall (qProg qP)))
#guard (runInlineCall (qProg qP)).allExprs LExpr.fullyAnnotated

/--
info: program Core;

type $__inlinety_0;
procedure r<a, b> (x : a)
{
  assert [refl]: x == x;
  assume [reflB]: forall y : b :: y == y;
};
procedure Caller ()
{
  $__inline1_r$inlined: {
    var $__inline1_x : int := 7;
    assert [$__inline1_refl]: $__inline1_x == $__inline1_x;
    assume [$__inline1_reflB]: forall y : $__inlinety_0 :: y == y;
  }
};
-/
#guard_msgs in
#eval IO.println (toString (runInlineCall (rProg rP)))
#guard (runInlineCall (rProg rP)).allExprs LExpr.fullyAnnotated

-- Stored type arguments give the type of a parameter that the call's arguments do not determine,
-- so no opaque type is declared.
/--
info: program Core;

procedure q<a> ()
{
  assume [refl]: forall y : a :: y == y;
};
procedure Caller ()
{
  $__inline1_q$inlined: {
    assume [$__inline1_refl]: forall y : int :: y == y;
  }
};
-/
#guard_msgs in
#eval IO.println (toString (runInlineCall (qTyArgsProg qP (some [.forAll [] .int]))))
#guard (runInlineCall (qTyArgsProg qP (some [.forAll [] .int]))).allExprs LExpr.fullyAnnotated

-- A stored type that still contains a generated type variable is not used: `b` gets an opaque
-- type, while `a` is read from the stored type arguments.
/--
info: program Core;

type $__inlinety_0;
procedure r<a, b> (x : a)
{
  assert [refl]: x == x;
  assume [reflB]: forall y : b :: y == y;
};
procedure Caller ()
{
  $__inline1_r$inlined: {
    var $__inline1_x : int := 7;
    assert [$__inline1_refl]: $__inline1_x == $__inline1_x;
    assume [$__inline1_reflB]: forall y : $__inlinety_0 :: y == y;
  }
};
-/
#guard_msgs in
#eval IO.println (toString (runInlineCall
  (rTyArgsProg rP (some [.forAll [] .int, .forAll [] (.ftvar "$__ty3")]))))
#guard (runInlineCall
  (rTyArgsProg rP (some [.forAll [] .int, .forAll [] (.ftvar "$__ty3")]))).allExprs
  LExpr.fullyAnnotated

-- Stored type arguments that are not one entry per type parameter are ignored, and the call's
-- arguments determine the types as for a program that was not type-checked.
/--
info: program Core;

type $__inlinety_0;
procedure r<a, b> (x : a)
{
  assert [refl]: x == x;
  assume [reflB]: forall y : b :: y == y;
};
procedure Caller ()
{
  $__inline1_r$inlined: {
    var $__inline1_x : int := 7;
    assert [$__inline1_refl]: $__inline1_x == $__inline1_x;
    assume [$__inline1_reflB]: forall y : $__inlinety_0 :: y == y;
  }
};
-/
#guard_msgs in
#eval IO.println (toString (runInlineCall (rTyArgsProg rP (some [.forAll [] .bool]))))
#guard (runInlineCall (rTyArgsProg rP (some [.forAll [] .bool]))).allExprs LExpr.fullyAnnotated

-- A stored type that disagrees with the type the call's argument gives is an error: `a` is
-- stored as `bool`, but the argument `7` is an `int`.
/--
info: Procedure inlining requires every call to be well-formed: the call to r stores a = bool,
but its arguments give a = int
-/
#guard_msgs in
#eval match tryInlineCall (rTyArgsProg rP (some [.forAll [] .bool, .forAll [] .int])) with
  | .ok _ => IO.println "no error"
  | .error e => IO.println e.message

-- Stored type arguments with more entries than type parameters are ignored likewise.
/--
info: program Core;

type $__inlinety_0;
procedure r<a, b> (x : a)
{
  assert [refl]: x == x;
  assume [reflB]: forall y : b :: y == y;
};
procedure Caller ()
{
  $__inline1_r$inlined: {
    var $__inline1_x : int := 7;
    assert [$__inline1_refl]: $__inline1_x == $__inline1_x;
    assume [$__inline1_reflB]: forall y : $__inlinety_0 :: y == y;
  }
};
-/
#guard_msgs in
#eval IO.println (toString (runInlineCall
  (rTyArgsProg rP (some [.forAll [] .int, .forAll [] .bool, .forAll [] .int]))))
#guard (runInlineCall
  (rTyArgsProg rP (some [.forAll [] .int, .forAll [] .bool, .forAll [] .int]))).allExprs
  LExpr.fullyAnnotated

/--
info: program Core;

type $__inlinety_0;
type $__inlinety_1;
procedure r<a, b> (x : a)
{
  assert [refl]: x == x;
  assume [reflB]: forall y : b :: y == y;
};
procedure Caller ()
{
  $__inline1_r$inlined: {
    var $__inline1_x : $__inlinety_0 := int.neg(7);
    assert [$__inline1_refl]: $__inline1_x == $__inline1_x;
    assume [$__inline1_reflB]: forall y : $__inlinety_1 :: y == y;
  }
};
-/
#guard_msgs in
#eval IO.println (toString (runInlineCall (unknownProg rP)))

-- The type checker rejects this program: the call needs `a` at both `int` and
-- `bool`. Inlining still runs on it and keeps the result annotated.
/--
info: program Core;

type $__inlinety_0;
procedure idp<a> (x : a, out r : a)
{
  r := x;
};
procedure Caller ()
{
  var bb : bool;
  $__inline1_idp$inlined: {
    var $__inline1_x : $__inlinety_0 := 7;
    var $__inline1_r : $__inlinety_0;
    $__inline1_r := $__inline1_x;
    bb := $__inline1_r;
  }
};
-/
#guard_msgs in
#eval IO.println (toString (runInlineCall (conflictProg idpP)))
#guard (runInlineCall (conflictProg idpP)).allExprs LExpr.fullyAnnotated

end CallInstanceTests

/-! ## The opaque types of an inlined call avoid the program's type names

A program may declare a type named like the opaque type inlining gives a callee type parameter
that the call does not determine. Here the axiom makes `$__inlinety_0` a singleton, under which
the assertion of `Q` holds, so the inlined assertion must be at another type. The checker rejects
such a call, so the pass is run directly on the unchecked program. -/
section InlineAvoidsTypeNames
open Core.CallFixtures Core.TestUtil

def capturedInlineTypePgm : Program :=
  capturedTypeProg "$__inlinety_0" []
    [Statement.assert "qa" (singletonAll (tv "a")) .empty]

/--
info: program Core;

type $__inlinety_1;
type $__inlinety_0;
axiom [one]: forall x : $__inlinety_0 :: forall y : $__inlinety_0 :: x == y;
procedure Q<a> ()
{
  assert [qa]: forall x : a :: forall y : a :: x == y;
};
procedure P ()
{
  $__inline1_Q$inlined: {
    assert [$__inline1_qa]: forall x : $__inlinety_1 :: forall y : $__inlinety_1 :: x == y;
  }
};
-/
#guard_msgs in
#eval IO.println (toString (runInlineCall capturedInlineTypePgm).stripMetaData)

/--
info: Procedure 'P': the call to 'Q' does not determine one of its type
parameters
-/
#guard_msgs (whitespace := lax) in
#eval match Core.typeCheck .quiet capturedInlineTypePgm with
  | .ok p => IO.println (toString (runInlineCall p).stripMetaData)
  | .error e => IO.println e.message

/-- A type declared inside a procedure body is avoided as well. Here the assumption makes the
    local `$__inlinety_0` a singleton, so the inlined assertion must be at another type. -/
def capturedLocalInlineTypePgm : Program :=
  capturedLocalTypeProg "$__inlinety_0" []
    [Statement.assert "qa" (singletonAll (tv "a")) .empty]

-- As in CallElim.lean, the printed program cannot be shown, so the output is checked directly.
#guard ((toString (runInlineCall capturedLocalInlineTypePgm).stripMetaData).splitOn
  "forall x : $__inlinety_1 ::").length > 1

/--
info: Procedure 'P': the call to 'Q' does not determine one of its type
parameters
-/
#guard_msgs (whitespace := lax) in
#eval match Core.typeCheck .quiet capturedLocalInlineTypePgm with
  | .ok p => IO.println (toString (runInlineCall p).stripMetaData)
  | .error e => IO.println e.message

end InlineAvoidsTypeNames
end
