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

open LTy.Syntax LExpr.SyntaxMono
open Std (ToFormat Format format)

/-- info: (λ (if (%0 == #1) then #10 else (_minit %0))) -/
#guard_msgs in
#eval format $ Lambda.LExpr.eval 100
                  {Lambda.LState.init with state :=
                      [[("m", (mty[int → int], esM[_minit]))]] }
        esM[λ (if (%0 == #1) then #10 else (m %0))]

/-- info: #42 -/
#guard_msgs in
#eval format $ LExpr.eval 100
                          { LState.init with state := [[("x", (mty[int], esM[(#32 : int)]))]] }
                          esM[((λ (if (%0 == #23) then #17 else #42)) (x : int))]

/-- info: (f #true) -/
#guard_msgs in
#eval format $ LExpr.eval 10 ∅ esM[(f #true)]

/-- info: (minit #24) -/
#guard_msgs in
#eval format $ LExpr.eval 100
                    { LState.init with state :=
                        [[("m", (none, esM[(λ (minit %0))]))], -- most recent scope
                         [("m", (none, (.const "12" none)))]] }
                    esM[((λ (if (%0 == #23) then #17 else (m %0)) #24))]

/-- info: (minit #24) -/
#guard_msgs in
#eval format $ LExpr.eval 100
                    { LState.init with state := [[("m", (none, esM[minit]))]] }
                    esM[((λ (if (%0 == #23) then #17 else (m %0))) #24)]

/-- info: x -/
#guard_msgs in
#eval format $ LExpr.eval 10 ∅ esM[if #true then x else y]

-- Ill-formed `abs` is returned as-is in this Curry style...
/-- info: (λ %1) -/
#guard_msgs in
#eval format $ LExpr.eval 10 ∅ esM[(λ %1)]

/-- info: ((λ %1) #true) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 ∅ (.app (.mdata ⟨"x"⟩ (.abs .none (.bvar 1))) (.const "true" none))

/- Tests for evaluation of BuiltInFunctions. -/

open LTy.Syntax

private def testBuiltIn : @Factory Unit :=
  #[{ name := "Int.Add",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[int],
      concreteEval := some (fun e args => match args with
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
      concreteEval :=  some (fun e args => match args with
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
      concreteEval :=  some (fun e args => match args with
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
      body := some esM[((~Int.Add x) y)]
    }]

private def testState : LState Unit :=
  let ans := LState.addFactory LState.init testBuiltIn
  match ans with
  | .error e => panic s!"{e}"
  | .ok ok => ok

/-- info: (#50 : int) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((~IntAddAlias #20) #30)]

/-- info: ((~Int.Add #20) x) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((~IntAddAlias #20) x)]

/-- info: ((~Int.Add ((~Int.Add #5) #100)) x) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 LState.init esM[(( ((λλ (~Int.Add %1) %0)) ((λ ((~Int.Add %0) #100)) #5)) x)]

/-- info: (#50 : int) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((~Int.Add #20) #30)]

/-- info: ((~Int.Add (#105 : int)) x) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((((λλ (~Int.Add %1) %0)) ((λ ((~Int.Add %0) #100)) #5)) x)]

/-- info: ((#f #20) (#-5 : int)) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[( ((λλ (#f %1) %0) #20) ((λ (~Int.Neg %0)) (#5 : int)))]

/-- info: ((~Int.Add #20) (~Int.Neg x)) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[( ((λλ (~Int.Add %1) %0) #20) ((λ (~Int.Neg %0)) x))]

/-- info: ((~Int.Add #20) (~Int.Neg x)) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((~Int.Add #20) (~Int.Neg x))]

/-- info: ((~Int.Add x) (#-30 : int)) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((~Int.Add x) (~Int.Neg #30))]

/-- info: (#50 : int) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((λ %0) ((~Int.Add #20) #30))]

/-- info: (#100 : int) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((~Int.Div #300) ((~Int.Add #2) #1))]

/-- info: (#0 : int) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((~Int.Add #3) (~Int.Neg #3))]

/-- info: (#0 : int) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((~Int.Add (~Int.Neg #3)) #3)]

/-- info: ((~Int.Div #300) (#0 : int)) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((~Int.Div #300) ((~Int.Add #3) (~Int.Neg #3)))]

/-- info: ((~Int.Div x) (#3 : int)) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((~Int.Div x) ((~Int.Add #2) #1))]

/-- info: ((~Int.Le (#100 : int)) x) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 200 testState
                esM[((~Int.Le ((~Int.Div #300) ((~Int.Add #2) #1))) x)]

/--
info: ((~Int.Le ((~Int.Div #300) ((~Int.Add #2) y))) x)
-/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 200 testState
                esM[((~Int.Le ((~Int.Div #300) ((~Int.Add #2) y))) x)]

/-- info: ((~Int.Div x) x) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 200 testState
                esM[((~Int.Div x) x)]


end EvalTest
---------------------------------------------------------------------
end LExpr
end Lambda
