/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.CallElim
import Strata.Languages.Boogie.Boogie
import Strata.Languages.Boogie.StatementSemantics
import Strata.Languages.Boogie.ProgramType
import Strata.Languages.Boogie.ProgramWF
import Strata.DL.Lambda.IntBoolFactory

open Boogie
open CallElim
open Strata

/-! ## Procedure Inlining Examples -/
section ProcedureInliningExamples

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
    tmp_arg_1 := !tmp_arg_0;
    b_out := tmp_arg_1;
  }
};

#end


structure VarMap where
  vars: Map String String
  labels: Map String String

mutual
partial def alphaEquivBlock (b1 b2: Boogie.Block) (map:VarMap)
    : Except String VarMap := do
  let st1 := b1.ss
  let st2 := b2.ss
  if st1.length ≠ st2.length then
    .error "Block lengths do not match"
  else
    (st1.zip st2).allM
      (fun (st1,st2) => alphaEquivStatement st1 st2 varmap lblmap)

partial def alphaEquivStatement (s1 s2: Boogie.Statement)
    (varmap:Map String String) (lblmap:Map String String)
    : Except String Bool :=
  match s1,s2 with
  | (.block lbl1 b1 _, .block lbl2 b2 _) =>
    match lblmap.find? lbl1 with
    | None =>
      alphaEquivBlock b1 b2 varmap (lblmap.insert lbl1 lbl2)
    | Some lbl2' =>
      .error ("Has duplicated definition of block label " ++ lbl1 ++
          "(previously mapped to " ++ lbl2' ++ ")")
  | (.ite _ thenb1 elseb1 _, .ite _ thenb2 elseb2) => do
    let res1 <- alphaEquivBlock thenb1 thenb2 varmap lblmap

end

def alphaEquiv (p1 p2:Boogie.Procedure) :=
  p1.body



def translate (t : Strata.Program) : Boogie.Program :=
  (TransM.run (translateProgram t)).fst

def env := (Lambda.LContext.default.addFactoryFunctions Boogie.Factory)

def translateWF (t : Strata.Program) : WF.WFProgram :=
  let p := translate t
  match H: Program.typeCheck env Lambda.TEnv.default p with
  | .error e => panic! "Well, " ++ Std.format e |> toString
  | .ok res => { self := p, prop := by exact WF.Program.typeCheckWF H }

def inlineCall (p : Boogie.Program)
  : Boogie.Program :=
  match (Boogie.CallElim.run p inlineCall') with
  | .ok res => res
  | .error e => panic! e

#eval Boogie.typeCheck Options.default (translate Test1)
#eval Boogie.typeCheck Options.default (translate Test1Ans)
#eval toString (inlineCall (translate Test1)).eraseTypes
#eval toString (translate Test1Ans).eraseTypes

-- TODO: compare Test1 and Test1Ans. This needs postprocessing because
-- the "init" statements' RHSes have different placeholder variable names.

end ProcedureInliningExamples
