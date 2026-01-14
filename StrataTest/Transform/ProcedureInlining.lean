/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.DDM.Util.Format
import Strata.Languages.Boogie.Boogie
import Strata.Languages.Boogie.DDMTransform.Translate
import Strata.Languages.Boogie.StatementSemantics
import Strata.Languages.Boogie.ProgramType
import Strata.Languages.Boogie.ProgramWF
import Strata.Transform.BoogieTransform
import Strata.Transform.ProcedureInlining

open Boogie
open Boogie.Transform
open ProcedureInlining
open Strata
open Std

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


private def substExpr (e1:Expression.Expr) (map:Map String String) (isReverse: Bool) :=
  map.foldl
    (fun (e:Expression.Expr) ((i1,i2):String × String) =>
      -- old_id has visibility of temp because the new local variables were
      -- created by BoogieGenM.
      -- new_expr has visibility of unres because that is the default setting
      -- from DDM parsed program, and the substituted program is supposed to be
      -- equivalent to the answer program translated from DDM
      -- These must be reversed when checking e2 -> e1
      let old_vis := if not isReverse then Visibility.temp else  Visibility.unres
      let new_vis := if not isReverse then Visibility.unres else Visibility.temp
      let old_id:Expression.Ident := { name := i1, metadata := old_vis }

      let new_expr:Expression.Expr := .fvar ()
          { name := i2, metadata := new_vis } .none
      e.substFvar old_id new_expr)
    e1

private def alphaEquivExprs (e1 e2: Expression.Expr) (map:IdMap)
    : Bool :=
  (substExpr e1 (map.vars.fst) false).eraseTypes == e2.eraseTypes &&
  (substExpr e2 (map.vars.snd) true).eraseTypes == e1.eraseTypes

private def alphaEquivExprsOpt (e1 e2: Option Expression.Expr) (map:IdMap)
    : Except Format Bool :=
  match e1,e2 with
  | .some e1, .some e2 =>
    return alphaEquivExprs e1 e2 map
  | .none, .none =>
    return .true
  | _, _ =>
    .error ".some and .none mismatch"

private def alphaEquivIdents (e1 e2: Expression.Ident) (map:IdMap)
    : Bool :=
  (-- Case 1: e1 is created from inliner, e2 was from DDM
   (e1.metadata == Visibility.temp && e2.metadata == Visibility.unres) ||
   -- Caes 2: both e1 and e2 are from DDM
   (e1.metadata == e2.metadata)) &&
  (match Map.find? map.vars.fst e1.name, Map.find? map.vars.snd e2.name with
    | .some n', .some m' => n' == e2.name && m' == e1.name
    | .none, .none => e1.name == e2.name
    | _, _ => false )


mutual

def alphaEquivBlock (b1 b2: Boogie.Block) (map:IdMap)
    : Except Format IdMap := do
  if b1.length ≠ b2.length then
    .error "Block lengths do not match"
  else
    (b1.attach.zip b2).foldlM
      (fun (map:IdMap) (st1,st2) => do
        let newmap ← alphaEquivStatement st1.1 st2 map
        return newmap)
      map
  termination_by b1.sizeOf
  decreasing_by cases st1; apply Imperative.sizeOf_stmt_in_block; assumption

def alphaEquivStatement (s1 s2: Boogie.Statement) (map:IdMap)
    : Except Format IdMap := do
  let mk_err (s:Format): Except Format IdMap :=
    .error (f!"{s}\ns1:{s1}\ns2:{s2}\nmap:{map.vars}")

  match hs: (s1,s2) with
  | (.block lbl1 b1 _, .block lbl2 b2 _) =>
    -- Since 'goto lbl' can appear before 'lbl' is defined, update the label
    -- map here
    let map ← IdMap.updateLabel map lbl1 lbl2
    alphaEquivBlock b1 b2 map

  | (.ite cond1 thenb1 elseb1 _, .ite cond2 thenb2 elseb2 _) => do
    if alphaEquivExprs cond1 cond2 map then
      let map' <- alphaEquivBlock thenb1 thenb2 map
      let map'' <- alphaEquivBlock elseb1 elseb2 map'
      return map''
    else
      .error "if conditions do not match"

  | (.loop g1 m1 i1 b1 _, .loop g2 m2 i2 b2 _) =>
    if ¬ alphaEquivExprs g1 g2 map then
      .error "guard does not match"
    else if ¬ (← alphaEquivExprsOpt m1 m2 map) then
      .error "measure does not match"
    else if ¬ (← alphaEquivExprsOpt i1 i2 map) then
      .error "invariant does not match"
    else alphaEquivBlock b1 b2 map

  | (.goto lbl1 _, .goto lbl2 _) =>
    IdMap.updateLabel map lbl1 lbl2

  | (.cmd c1, .cmd c2) =>
    match (c1, c2) with
    | (.call lhs1 procName1 args1 _, .call lhs2 procName2 args2 _) =>
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
    | (.cmd (.init n1 _ _e1 _), .cmd (.init n2 _ _e2 _)) =>
      -- Omit e1 and e2 check because init may use undeclared free vars
      -- The updateVars below must be the only place that updates the
      -- variable name mapping.
      IdMap.updateVars map [(n1.name,n2.name)]
    | (.cmd (.set n1 e1 _), .cmd (.set n2 e2 _)) =>
      if ¬ alphaEquivExprs e1 e2 map then
        mk_err f!"RHS of sets do not match \
        \n(subst of e1: {repr (substExpr e1 map.vars.fst false)})\n(e2: {repr e2})
        \n(subst of e2: {repr (substExpr e2 map.vars.snd true)})\n(e1: {repr e1})"
      else if ¬ alphaEquivIdents n1 n2 map then
        mk_err "LHS of sets do not match"
      else
        return map
    | (.cmd (.havoc n1 _), .cmd (.havoc n2 _)) =>
      if ¬ alphaEquivIdents n1 n2 map then
        mk_err "LHS of havocs do not match"
      else
        return map
    | (.cmd (.assert _ e1 _), .cmd (.assert _ e2 _)) =>
      if ¬ alphaEquivExprs e1 e2 map then
        mk_err "Expressions of asserts do not match"
      else
        return map
    | (.cmd (.assume _ e1 _), .cmd (.assume _ e2 _)) =>
      if ¬ alphaEquivExprs e1 e2 map then
        mk_err "Expressions of assumes do not match"
      else
        return map
    | (_,_) =>
      mk_err "Commands do not match"

  | (_,_) => mk_err "Statements do not match"
  termination_by s1.sizeOf
  decreasing_by all_goals(cases hs; simp_all; try omega)

end

private def alphaEquiv (p1 p2:Boogie.Procedure):Except Format Bool := do
  if p1.body.length ≠ p2.body.length then
    .error (s!"# statements do not match: in {p1.header.name}, "
        ++ s!"inlined fn one has {p1.body.length}"
        ++ s!" whereas the answer has {p2.body.length}")
  else
    let newmap:IdMap := IdMap.mk ([], []) []
    let stmts := (p1.body.zip p2.body)
    let m ← List.foldlM (fun (map:IdMap) (s1,s2) =>
        alphaEquivStatement s1 s2 map)
      newmap stmts
    -- The corresponding outputs should be pairwise α-equivalent
    return ((p1.header.outputs.zip p2.header.outputs).map (fun ((x, _), (y, _)) => alphaEquivIdents x y m)).all id



def translate (t : Strata.Program) : Boogie.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

def runInlineCall (p : Boogie.Program) : Boogie.Program :=
  match (runProgram inlineCallCmd p .emp) with
  | ⟨.ok res, _⟩ => res
  | ⟨.error e, _⟩ => panic! e

def checkInlining (prog : Boogie.Program) (progAns : Boogie.Program)
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
program Boogie;
procedure f(x : bool) returns (y : bool) {
  y := !x;
};

procedure h() returns () {
  var b_in : bool;
  var b_out : bool;
  call b_out := f(b_in);
};
#end

def Test1Ans :=
#strata
program Boogie;
procedure f(x : bool) returns (y : bool) {
  y := !x;
};

procedure h() returns () {
  var b_in : bool;
  var b_out : bool;
  inlined: {
    var tmp_arg_0 : bool := b_in;
    var tmp_arg_1 : bool;
    havoc tmp_arg_1;
    tmp_arg_1 := !tmp_arg_0;
    b_out := tmp_arg_1;
  }
};

#end

/-- info: ok: true -/
#guard_msgs in
#eval checkInlining (translate Test1) (translate Test1Ans)

def Test2 :=
#strata
program Boogie;
procedure f(x : bool) returns (y : bool) {
  if (x) {
    goto end;
  } else { y := false;
  }
  end: {}
};

procedure h() returns () {
  var b_in : bool;
  var b_out : bool;
  call b_out := f(b_in);
  end: {}
};
#end

def Test2Ans :=
#strata
program Boogie;
procedure f(x : bool) returns (y : bool) {
  if (x) {
    goto end;
  } else { y := false;
  }
  end: {}
};

procedure h() returns () {
  var b_in : bool;
  var b_out : bool;
  inlined: {
    var f_x : bool := b_in;
    var f_y : bool;
    havoc f_y;
    if (f_x) {
      goto f_end;
    } else {
      f_y := false;
    }
    f_end: {}
    b_out := f_y;
  }
  end: {}
};

#end

/-- info: ok: true -/
#guard_msgs in
#eval checkInlining (translate Test2) (translate Test2Ans)


--- Test procedure calls inside subblocks

def Test3 :=
#strata
program Boogie;
procedure f(x : int) returns (y : int) {
  y := x;
};

procedure g() returns () {
  var f_out : int;
  if (true) {
    call f_out := f(1);
  } else {
    call f_out := f(2);
  }
};
#end

def Test3Ans :=
#strata
program Boogie;
procedure f(x : int) returns (y : int) {
  y := x;
};

procedure g() returns () {
  var f_out : int;
  if (true) {
    inlined1: {
      var f_x : int := 1;
      var f_y : int;
      havoc f_y;
      f_y := f_x;
      f_out := f_y;
    }
  } else {
    inlined1: {
      var f_x2 : int := 2;
      var f_y2 : int;
      havoc f_y2;
      f_y2 := f_x2;
      f_out := f_y2;
    }
  }
};
#end

/-- info: ok: true -/
#guard_msgs in
#eval checkInlining (translate Test3) (translate Test3Ans)


end ProcedureInliningExamples
