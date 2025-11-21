/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.CallElim
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
    var y : bool;
    y := !b_in;
    b_out := y;
  }
};

#end



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

/--
info: "(procedure f :  ((x : bool)) → ((y : bool)))\nmodifies: []\npreconditions: \npostconditions: \nbody: y := (~Bool.Not x)\n\n(procedure h :  () → ())\nmodifies: []\npreconditions: \npostconditions: \nbody: init (b_in : bool) := init_b_in_0\ninit (b_out : bool) := tmp_b_out_0\nf$inlined : {init (tmp_arg_1 : bool) := b_in\n init (y : bool) := tmp_y_2\n y := (~Bool.Not tmp_arg_1)\n b_out := y}\n"
-/
#guard_msgs in
#eval toString (inlineCall (translate Test1)).eraseTypes

/--
info: "(procedure f :  ((x : bool)) → ((y : bool)))\nmodifies: []\npreconditions: \npostconditions: \nbody: y := (~Bool.Not x)\n\n(procedure h :  () → ())\nmodifies: []\npreconditions: \npostconditions: \nbody: init (b_in : bool) := init_b_in_0\ninit (b_out : bool) := init_b_out_1\ninlined : {init (tmp_arg_0 : bool) := b_in\n init (y : bool) := init_y_2\n y := (~Bool.Not b_in)\n b_out := y}\n"
-/
#guard_msgs in
#eval toString (translate Test1Ans).eraseTypes

-- TODO: compare Test1 and Test1Ans. This needs postprocessing because
-- the "init" statements' RHSes have different placeholder variable names.

end ProcedureInliningExamples
