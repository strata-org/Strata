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

def transformProgram (t : Strata.Program) : Core.Program :=
  let program := translate t
  -- Build PrecondElim factory from pre-typecheck datatypes + program function decls
  -- (mirrors typeCheckAndPartialEval logic)
  let factory := Core.Factory
  let preDataTypes := program.decls.filterMap fun decl =>
    match decl with
    | .type (.data d) _ => some d
    | _ => none
  let precondFactory := match preDataTypes.foldlM (fun F block => do
    let bf ← Lambda.genBlockFactory (T := CoreLParams) block
    F.addFactory bf) factory with
    | .ok f => f
    | .error e => panic! s!"genBlockFactory failed: {Std.format e}"
  let precondFactory := program.decls.foldl (fun F decl =>
    match decl with
    | .func func _ => F.push func
    | _ => F) precondFactory
  -- Run PrecondElim before typechecking
  let (program, _) := PrecondElim.precondElim program precondFactory
  -- Type check (but don't partial eval)
  match Core.typeCheck Options.default program with
  | .error e => panic! s!"Type check failed: {Std.format e}"
  | .ok program => program.eraseTypes.stripMetaData

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
info: [Strata.Core] Type checking succeeded.

---
info: procedure test :  ((a : int)) → ()
  modifies: []
  preconditions: 
  postconditions: 
{
  {
    assert [init_calls_Int.Div_0] (~Bool.Not (a == #0))
    init (z : int) := (~Int.Div #10 a)
  }
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
info: [Strata.Core] Type checking succeeded.

---
info: procedure safeMod$$wf :  ((x : int) (y : int)) → ()
  modifies: []
  preconditions: 
  postconditions: 
{
  {
    assume [precond_safeMod_0] (~Bool.Not (y == #0))
    assert [safeMod_body_calls_Int.Mod_0] (~Bool.Not (y == #0))
  }
}
func safeMod :  ((x : int) (y : int)) → int :=
  ((~Int.Mod x y))
procedure foo$$wf :  ((x : int) (y : int)) → ()
  modifies: []
  preconditions: 
  postconditions: 
{
  {
    assert [foo_precond_calls_safeMod_0] (~Bool.Not (y == #0))
    assume [precond_foo_0] (~Int.Gt (~safeMod x y) #0)
  }
}
func foo :  ((x : int) (y : int)) → int :=
  ((~Int.Add x y))
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
info: [Strata.Core] Type checking succeeded.

---
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
  {
    assume [test_requires_0] (~List..isCons xs)
    assert [test_pre_test_requires_1_calls_List..head_0] (~List..isCons xs)
    assume [test_requires_1] (~Int.Gt (~List..head xs) #0)
  }
}
procedure test :  ((xs : List)) → ()
  modifies: []
  preconditions: (test_requires_0, ((~List..isCons : (arrow List bool))
   (xs : List))) (test_requires_1, ((~Int.Gt : (arrow int (arrow int bool)))
   ((~List..head : (arrow List int)) (xs : List))
   #0))
  postconditions: 
{
  {}
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
info: [Strata.Core] Type checking succeeded.

---
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
  {
    assume [test_requires_0] (~List..isCons xs)
    assert [test_post_test_ensures_1_calls_List..head_0] (~List..isCons xs)
    assume [test_ensures_1] (~Int.Gt (~List..head xs) #0)
    assert [test_post_test_ensures_2_calls_List..head_0] (~List..isCons (~List..tail xs))
    assert [test_post_test_ensures_2_calls_List..tail_1] (~List..isCons xs)
    assume [test_ensures_2] (~Int.Gt (~List..head (~List..tail xs)) #0)
  }
}
procedure test :  ((xs : List)) → ()
  modifies: []
  preconditions: (test_requires_0, ((~List..isCons : (arrow List bool)) (xs : List)))
  postconditions: (test_ensures_1, ((~Int.Gt : (arrow int (arrow int bool)))
   ((~List..head : (arrow List int)) (xs : List))
   #0)) (test_ensures_2, ((~Int.Gt : (arrow int (arrow int bool)))
   ((~List..head : (arrow List int)) ((~List..tail : (arrow List List)) (xs : List)))
   #0))
{
  {}
}
-/
#guard_msgs in
#eval (Std.format (transformProgram dependentRequiresPgm))

/-! ### Test 5: Function decl statement with precondition referencing local variable -/

def funcDeclPrecondPgm :=
#strata
program Core;

procedure test() returns ()
{
  var x : int := 1;
  function safeDiv(y : int) : int
    requires y div x > 0;
    { y div x }
  var z : int := safeDiv(5);
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: procedure test :  () → ()
  modifies: []
  preconditions: 
  postconditions: 
{
  {
    init (x : int) := #1
    safeDiv$$wf :
    {
      init (y : int) := init_y
      assert [safeDiv_precond_calls_Int.Div_0] (~Bool.Not (x == #0))
      assume [precond_safeDiv_0] (~Int.Gt (~Int.Div y x) #0)
      assert [safeDiv_body_calls_Int.Div_0] (~Bool.Not (x == #0))
    }
    funcDecl <function>
    assert [init_calls_safeDiv_0] (~Int.Gt (~Int.Div #5 x) #0)
    init (z : int) := (~safeDiv #5)
  }
}
-/
#guard_msgs in
#eval (Std.format (transformProgram funcDeclPrecondPgm))

end PrecondElimTests
