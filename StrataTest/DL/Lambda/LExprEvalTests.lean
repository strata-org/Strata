/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprEval

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)

namespace LExpr
---------------------------------------------------------------------

section EvalTest

open LTy.Syntax LExpr.Syntax
open Std (ToFormat Format format)

/-- info: (λ (if (%0 == #1) then #10 else (_minit %0))) -/
#guard_msgs in
#eval format $ Lambda.LExpr.eval 100
                  {Lambda.LState.init with state :=
                      [[("m", (mty[int → int], es[_minit]))]] }
        es[λ (if (%0 == #1) then #10 else (m %0))]

/-- info: #42 -/
#guard_msgs in
#eval format $ LExpr.eval 100
                          { LState.init with state := [[("x", (mty[int], es[(#32 : int)]))]] }
                          es[((λ (if (%0 == #23) then #17 else #42)) (x : int))]

/-- info: (f #true) -/
#guard_msgs in
#eval format $ LExpr.eval 10 ∅ es[(f #true)]

/-- info: (minit #24) -/
#guard_msgs in
#eval format $ LExpr.eval 100
                    { LState.init with state :=
                        [[("m", (none, es[(λ (minit %0))]))], -- most recent scope
                         [("m", (none, (.const "12" none)))]] }
                    es[((λ (if (%0 == #23) then #17 else (m %0)) #24))]

/-- info: (minit #24) -/
#guard_msgs in
#eval format $ LExpr.eval 100
                    { LState.init with state := [[("m", (none, es[minit]))]] }
                    es[((λ (if (%0 == #23) then #17 else (m %0))) #24)]

/-- info: x -/
#guard_msgs in
#eval format $ LExpr.eval 10 ∅ es[if #true then x else y]

-- Ill-formed `abs` is returned as-is in this Curry style...
/-- info: (λ %1) -/
#guard_msgs in
#eval format $ LExpr.eval 10 ∅ es[(λ %1)]

/-- info: ((λ %1) #true) -/
#guard_msgs in
#eval format $ LExpr.eval (Identifier:=String) 10 ∅ (.app (.mdata ⟨"x"⟩ (.abs .none (.bvar 1))) (.const "true" none))

/- Tests for evaluation of BuiltInFunctions. -/

open LTy.Syntax

private def testBuiltIn : @Factory String :=
  #[{ name := "Int.Add",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[int],
      denote := some (fun e args => match args with
                        | [e1, e2] =>
                          let e1i := LExpr.denoteInt e1
                          let e2i := LExpr.denoteInt e2
                          match e1i, e2i with
                          | some x, some y => (.const (toString (x + y)) mty[int])
                          | _, _ => e
                        | _ => e) },
    { name := "Int.Div",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[int],
      denote :=  some (fun e args => match args with
                          | [e1, e2] =>
                            let e1i := LExpr.denoteInt e1
                            let e2i := LExpr.denoteInt e2
                            match e1i, e2i with
                            | some x, some y =>
                              if y == 0 then e else (.const (toString (x / y)) mty[int])
                            | _, _ => e
                          | _ => e) },
    { name := "Int.Neg",
      inputs := [("x", mty[int])],
      output := mty[int],
      denote :=  some (fun e args => match args with
                              | [e1] =>
                                let e1i := LExpr.denoteInt e1
                                match e1i with
                                | some x => (.const (toString (- x)) mty[int])
                                | _ => e
                              | _ => e) },

    { name := "IntAddAlias",
      attr := #["inline"],
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[int],
      body := some es[((~Int.Add x) y)]
    }]

private def testState : LState String :=
  let ans := LState.addFactory LState.init testBuiltIn
  match ans with
  | .error e => panic s!"{e}"
  | .ok ok => ok

/-- info: (#50 : int) -/
#guard_msgs in
#eval format $ LExpr.eval (Identifier:=String) 10 testState es[((~IntAddAlias #20) #30)]

/-- info: ((~Int.Add #20) x) -/
#guard_msgs in
#eval format $ LExpr.eval (Identifier:=String) 10 testState es[((~IntAddAlias #20) x)]

/-- info: ((~Int.Add ((~Int.Add #5) #100)) x) -/
#guard_msgs in
#eval format $ LExpr.eval (Identifier:=String) 10 LState.init es[(( ((λλ (~Int.Add %1) %0)) ((λ ((~Int.Add %0) #100)) #5)) x)]

/-- info: (#50 : int) -/
#guard_msgs in
#eval format $ LExpr.eval (Identifier:=String) 10 testState es[((~Int.Add #20) #30)]

/-- info: ((~Int.Add (#105 : int)) x) -/
#guard_msgs in
#eval format $ LExpr.eval (Identifier:=String) 10 testState es[((((λλ (~Int.Add %1) %0)) ((λ ((~Int.Add %0) #100)) #5)) x)]

/-- info: ((#f #20) (#-5 : int)) -/
#guard_msgs in
#eval format $ LExpr.eval (Identifier:=String) 10 testState es[( ((λλ (#f %1) %0) #20) ((λ (~Int.Neg %0)) (#5 : int)))]

/-- info: ((~Int.Add #20) (~Int.Neg x)) -/
#guard_msgs in
#eval format $ LExpr.eval (Identifier:=String) 10 testState es[( ((λλ (~Int.Add %1) %0) #20) ((λ (~Int.Neg %0)) x))]

/-- info: ((~Int.Add #20) (~Int.Neg x)) -/
#guard_msgs in
#eval format $ LExpr.eval (Identifier:=String) 10 testState es[((~Int.Add #20) (~Int.Neg x))]

/-- info: ((~Int.Add x) (#-30 : int)) -/
#guard_msgs in
#eval format $ LExpr.eval (Identifier:=String) 10 testState es[((~Int.Add x) (~Int.Neg #30))]

/-- info: (#50 : int) -/
#guard_msgs in
#eval format $ LExpr.eval (Identifier:=String) 10 testState es[((λ %0) ((~Int.Add #20) #30))]

/-- info: (#100 : int) -/
#guard_msgs in
#eval format $ LExpr.eval (Identifier:=String) 10 testState es[((~Int.Div #300) ((~Int.Add #2) #1))]

/-- info: (#0 : int) -/
#guard_msgs in
#eval format $ LExpr.eval (Identifier:=String) 10 testState es[((~Int.Add #3) (~Int.Neg #3))]

/-- info: (#0 : int) -/
#guard_msgs in
#eval format $ LExpr.eval (Identifier:=String) 10 testState es[((~Int.Add (~Int.Neg #3)) #3)]

/-- info: ((~Int.Div #300) (#0 : int)) -/
#guard_msgs in
#eval format $ LExpr.eval (Identifier:=String) 10 testState es[((~Int.Div #300) ((~Int.Add #3) (~Int.Neg #3)))]

/-- info: ((~Int.Div x) (#3 : int)) -/
#guard_msgs in
#eval format $ LExpr.eval (Identifier:=String) 10 testState es[((~Int.Div x) ((~Int.Add #2) #1))]

/-- info: ((~Int.Le (#100 : int)) x) -/
#guard_msgs in
#eval format $ LExpr.eval (Identifier:=String) 200 testState
                es[((~Int.Le ((~Int.Div #300) ((~Int.Add #2) #1))) x)]

/--
info: ((~Int.Le ((~Int.Div #300) ((~Int.Add #2) y))) x)
-/
#guard_msgs in
#eval format $ LExpr.eval (Identifier:=String) 200 testState
                es[((~Int.Le ((~Int.Div #300) ((~Int.Add #2) y))) x)]

/-- info: ((~Int.Div x) x) -/
#guard_msgs in
#eval format $ LExpr.eval (Identifier:=String) 200 testState
                es[((~Int.Div x) x)]


end EvalTest
---------------------------------------------------------------------
end LExpr
end Lambda
