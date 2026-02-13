/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.Languages.Core.Core
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.ProgramType
import Strata.Transform.PrecondElim

open Core
open Core.PrecondElim
open Strata

/-! ## PrecondElim Tests -/
section PrecondElimTests

def translate (t : Strata.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

def typeCheckProgram (p : Core.Program) : Core.Program × @Lambda.Factory CoreLParams :=
  let env := (Lambda.LContext.default.addFactoryFunctions Core.Factory)
  match Program.typeCheck env Lambda.TEnv.default p with
  | .error e => panic! s!"Type check failed: {Std.format e}"
  | .ok (p', _) =>
    -- Build factory the same way typeCheckAndPartialEval does
    let datatypes := p'.decls.filterMap fun decl =>
      match decl with
      | .type (.data d) _ => some d
      | _ => none
    let σ := (Lambda.LState.init).setFactory Core.Factory
    let E := { Env.init with exprEnv := σ, program := p' }
    match E.addDatatypes datatypes with
    | .error e => panic! s!"addDatatypes failed: {Std.format e}"
    | .ok E =>
      -- Also add explicit function declarations
      let E := p'.decls.foldl (fun E d =>
        match d with
        | .func f _ => match E.addFactoryFunc f with
          | .ok E' => E'
          | .error _ => E
        | _ => E) E
      (p', E.factory)

def runPrecondElim (p : Core.Program) (F : @Lambda.Factory CoreLParams)
    : Core.Program :=
  (precondElim p F).fst

def transformProgram (t : Strata.Program) : Core.Program :=
  let p := translate t
  let (p', F) := typeCheckProgram p
  (runPrecondElim p' F).eraseTypes

/-! ### Test 1: Procedure body with div call gets assert for y != 0 -/

def divInBodyPgm :=
#strata
program Core;

procedure test(a : int) returns ()
{
  var z : int := 10 div a;
};

#end

/--
info: procedure test :  ((a : int)) → ()
  modifies: []
  preconditions: 
  postconditions: 
{
  assert [init_calls_Int.Div_0] (~Bool.Not (a == #0))
  init (z : int) := ((~Int.Div #10) a)
}
-/
#guard_msgs in
#eval (Std.format (transformProgram divInBodyPgm))

/-! ### Test 2: Function whose precondition calls a partial function -/

def funcWithPrecondPgm :=
#strata
program Core;

function safeMod(x : int, y : int) : int
  requires y != 0;
{ x mod y }

function foo(x : int, y : int) : int
  requires safeMod(x, y) > 0;
{ x + y }

#end

/--
info: procedure safeMod$$wf :  ((x : int) (y : int)) → ()
  modifies: []
  preconditions: 
  postconditions: 
{
  assume [precond_safeMod_0] (~Bool.Not (y == #0))
  assert [safeMod_body_calls_Int.Mod_0] (~Bool.Not (y == #0))
}
func safeMod :  ((x : int) (y : int)) → int :=
  (((~Int.Mod x) y))
procedure foo$$wf :  ((x : int) (y : int)) → ()
  modifies: []
  preconditions: 
  postconditions: 
{
  assert [foo_precond_calls_safeMod_0] (~Bool.Not (y == #0))
  assume [precond_foo_0] ((~Int.Gt ((~safeMod x) y)) #0)
}
func foo :  ((x : int) (y : int)) → int :=
  (((~Int.Add x) y))
-/
#guard_msgs in
#eval (Std.format (transformProgram funcWithPrecondPgm))

/-! ### Test 3: Procedure with ADT destructor (has implicit precondition) in requires -/

def procContractADTPgm :=
#strata
program Core;

datatype List { Nil(), Cons(head : int, tail : List) };

procedure test(xs : List) returns ()
spec {
  requires List..isCons(xs);
  requires List..head(xs) > 0;
}
{
};

#end

/--
info: type:
List
Type Arguments:
[]
Constructors:
[Name: Nil Args: [] Tester: List..isNil , Name: Cons Args: [(head, int), (tail, List)] Tester: List..isCons ]

procedure test$$wf :  ((xs : List)) → ()
  modifies: []
  preconditions: 
  postconditions: 
{
  assume [test_requires_0] (~List..isCons xs)
  assert [test_pre_test_requires_1_calls_List..head_0] (~List..isCons xs)
  assume [test_requires_1] ((~Int.Gt (~List..head xs)) #0)
}
procedure test :  ((xs : List)) → ()
  modifies: []
  preconditions: (test_requires_0, ((~List..isCons : (arrow List bool)) (xs : List))) (test_requires_1, (((~Int.Gt : (arrow int (arrow int bool))) ((~List..head : (arrow List int)) (xs : List))) #0))
  postconditions: 
{
  
}
-/
#guard_msgs in
#eval (Std.format (transformProgram procContractADTPgm))

/-! ### Test 4: Multiple requires, second depends on first for well-formedness -/

def dependentRequiresPgm :=
#strata
program Core;

datatype List { Nil(), Cons(head : int, tail : List) };

procedure test(xs : List) returns ()
spec {
  requires List..isCons(xs);
  ensures List..head(xs) > 0;
  ensures List..head(List..tail(xs)) > 0;
}
{
};

#end

/--
info: type:
List
Type Arguments:
[]
Constructors:
[Name: Nil Args: [] Tester: List..isNil , Name: Cons Args: [(head, int), (tail, List)] Tester: List..isCons ]

procedure test$$wf :  ((xs : List)) → ()
  modifies: []
  preconditions: 
  postconditions: 
{
  assume [test_requires_0] (~List..isCons xs)
  assert [test_post_test_ensures_1_calls_List..head_0] (~List..isCons xs)
  assume [test_ensures_1] ((~Int.Gt (~List..head xs)) #0)
  assert [test_post_test_ensures_2_calls_List..head_0] (~List..isCons (~List..tail xs))
  assert [test_post_test_ensures_2_calls_List..tail_1] (~List..isCons xs)
  assume [test_ensures_2] ((~Int.Gt (~List..head (~List..tail xs))) #0)
}
procedure test :  ((xs : List)) → ()
  modifies: []
  preconditions: (test_requires_0, ((~List..isCons : (arrow List bool)) (xs : List)))
  postconditions: (test_ensures_1, (((~Int.Gt : (arrow int (arrow int bool))) ((~List..head : (arrow List int)) (xs : List))) #0)) (test_ensures_2, (((~Int.Gt : (arrow int (arrow int bool))) ((~List..head : (arrow List int)) ((~List..tail : (arrow List List)) (xs : List)))) #0))
{
  
}
-/
#guard_msgs in
#eval (Std.format (transformProgram dependentRequiresPgm))

end PrecondElimTests
