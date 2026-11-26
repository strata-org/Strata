/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.StatementEval
meta import Strata.Languages.Core.IncrementalSolve
meta import StrataTest.DL.Lambda.RenamingFixtures

meta section

namespace Core
---------------------------------------------------------------------

section Tests

open Std (ToFormat Format format)
open Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Imperative (PureFunc)

/--
info: Error:
none
Expression Env:
State:
[(x : int) → 18]

Evaluation Config:
Eval Depth: 200
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: x_eq_18
Property: assert
Assumptions:
Proof Obligation:
true
-/
#guard_msgs in
#eval (evalOne ∅ [.init "x" t[int] (.det eb[#0]) .empty,
                    .set "x" eb[#18] .empty,
                    .assert "x_eq_18" eb[x == #18] .empty]) |> format

/--
info: Error:
none
Expression Env:
State:
[(y : int) → _yinit
(x : int) → _yinit]

Evaluation Config:
Eval Depth: 200
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: x_eq_12
Property: assert
Assumptions:
Proof Obligation:
_yinit == 12
-/
#guard_msgs in
#eval (evalOne
  ((Env.init (empty_factory := true)).pushScope [("y", (mty[int], eb[_yinit]))])
  [.init "x" t[int] (.det eb[#0]) .empty,
  .set "x" eb[y] .empty,
  .assert "x_eq_12" eb[x == #12] .empty]) |> format

/--
info: Error:
none
Expression Env:
State:
[(x : bool) → x@1 == true]

Evaluation Config:
Eval Depth: 200
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
-/
#guard_msgs in
-- NOTE: no error during evaluation here; the typechecker should flag this
-- though because `x` can't appear in its own initialization expression.
#eval evalOne ∅
       [
       .init "x" t[bool] (.det eb[x == #true]) .empty
       ] |> format

/--
info: Error:
none
Expression Env:
State:
[(minit : (arrow int int)) → _minit
(m : (arrow int int)) → fun __q0 : $__unknown_type => (if __q0 == 3 then 30 else (fun __q1 : $__unknown_type => (if __q1 == 2 then 20 else (fun __q2 : $__unknown_type => (if __q2 == 1 then 10 else _minit(__q2)))(__q1)))(__q0))
(m0 : int) → _minit(0)]

Evaluation Config:
Eval Depth: 200
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: m_5_eq_50
Property: assert
Assumptions:
Proof Obligation:
_minit(5) == 50

Label: m_2_eq_20
Property: assert
Assumptions:
Proof Obligation:
true

Label: m_1_eq_10
Property: assert
Assumptions:
Proof Obligation:
true
-/
#guard_msgs in
#eval (evalOne
  ((Env.init (empty_factory := true)).pushScope
    [("minit", (mty[int → int], eb[(_minit : int → int)]))])
  [.init "m" t[int → int] (.det eb[minit]) .empty,
  .init "m0" t[int] (.det eb[(m #0)]) .empty,
  .set "m" eb[λ (if (%0 == #1) then #10 else ((m : int → int) %0))] .empty,
  .set "m" eb[λ (if (%0 == #2) then #20 else ((m : int → int) %0))] .empty,
  .assert "m_5_eq_50" eb[(m #5) == #50] .empty,
  .assert "m_2_eq_20" eb[(m #2) == #20] .empty,
  .set "m" eb[λ (if (%0 == #3) then #30 else ((m : int → int) %0))] .empty,
  .assert "m_1_eq_10" eb[(m #1) == #10] .empty
  ]) |> format

/--
info: Error:
none
Expression Env:
State:
[minit → _minit
(m : (arrow int int)) → fun __q0 : $__unknown_type => (if __q0 == 3 then 30 else (fun __q1 : $__unknown_type => (if __q1 == 2 then 20 else (fun __q2 : $__unknown_type => (if __q2 == 1 then 10 else _minit(__q2)))(__q1)))(__q0))]

Evaluation Config:
Eval Depth: 200
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: m_5_eq_50
Property: assert
Assumptions:
Proof Obligation:
_minit(5) == 50

Label: m_2_eq_20
Property: assert
Assumptions:
Proof Obligation:
true

Label: m_1_eq_10
Property: assert
Assumptions:
Proof Obligation:
true
-/
#guard_msgs in
#eval (evalOne
  ((Env.init (empty_factory := true)).pushScope [("minit", (none, eb[_minit]))])
  [.init "m" t[int → int] (.det eb[minit]) .empty,
  .set "m" eb[λ (if (%0 == #1) then #10 else (m %0))] .empty,
  .set "m" eb[λ (if (%0 == #2) then #20 else (m %0))] .empty,
  .assert "m_5_eq_50" eb[(m #5) == #50] .empty,
  .assert "m_2_eq_20" eb[(m #2) == #20] .empty,
  .set "m" eb[λ (if (%0 == #3) then #30 else (m %0))] .empty,
  .assert "m_1_eq_10" eb[(m #1) == #10] .empty
  ]) |> format



private def prog1 : Statements :=
 [
 .init "x" t[int] (.det eb[#0]) .empty,
 .init "y" t[int] (.det eb[#6]) .empty,
 .block "label_0"

   [Statement.init "z" t[bool] (.det eb[zinit]) .empty,
    Statement.assume "z_false" eb[z == #false] .empty,

   .ite (.det eb[z == #false])
     [Statement.set "x" eb[y] .empty]
     -- The "trivial" assertion, though unreachable, is still verified away by the
     -- PE because the conclusion of the proof obligation evaluates to `true`.
     -- However, if the conclusion were anything else (including `false`) and
     -- the path conditions weren't empty, then this proof obligation would be
     -- sent on to the SMT solver.
     [Statement.assert "trivial" eb[#true] .empty]
     .empty,

   Statement.assert "x_eq_y_label_0" eb[x == y] .empty,
   ]
   .empty,
 .assert "x_eq_y" eb[x == y] .empty
 ]

/--
info: Error:
none
Expression Env:
State:
[(x : int) → if zinit@1 == false then 6 else 0
(y : int) → 6
zinit → zinit@1]

Evaluation Config:
Eval Depth: 200
Factory Functions:



Datatypes:

Path Conditions:
(z_false, zinit@1 == false)
(<label_ite_cond_true: z == false>, if zinit@1 == false then zinit@1 == false else true)
(<label_ite_cond_false: !(z == false)>, if if zinit@1 == false then false else true then if zinit@1 == false then false else true else true)


Warnings:
[]
Deferred Proof Obligations:
Label: trivial
Property: assert
Assumptions:
(<label_ite_cond_false: !(z == false)>, if zinit@1 == false then false else true)
(z_false, zinit@1 == false)
Proof Obligation:
true

Label: x_eq_y_label_0
Property: assert
Assumptions:
(z_false, zinit@1 == false)
(<label_ite_cond_true: z == false>, if zinit@1 == false then zinit@1 == false else true)
(<label_ite_cond_false: !(z == false)>, if if zinit@1 == false then false else true then if zinit@1 == false then false else true else true)
Proof Obligation:
(if zinit@1 == false then 6 else 0) == 6

Label: x_eq_y
Property: assert
Assumptions:
(z_false, zinit@1 == false)
(<label_ite_cond_true: z == false>, if zinit@1 == false then zinit@1 == false else true)
(<label_ite_cond_false: !(z == false)>, if if zinit@1 == false then false else true then if zinit@1 == false then false else true else true)
Proof Obligation:
(if zinit@1 == false then 6 else 0) == 6
-/
#guard_msgs in
#eval (evalOne ∅ prog1) |> format


private def prog2 : Statements := [
  .init "x" t[int] (.det eb[#0]) .empty,
  .set "x" eb[#1] .empty,
  .havoc "x" .empty,
  .assert "x_eq_1" eb[x == #1] .empty, -- error
  .havoc "x" .empty,
  .set "x" eb[#8] .empty
]

/--
info: Error:
none
Expression Env:
State:
[(x : int) → 8]

Evaluation Config:
Eval Depth: 200
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: x_eq_1
Property: assert
Assumptions:
Proof Obligation:
x@1 == 1
-/
#guard_msgs in
#eval (evalOne ∅ prog2) |> format


-- Nondet if is rejected by the evaluator: it must be eliminated (via the
-- nondetElim transform) before symbolic evaluation, so the env is left in an
-- error state.
/--
info: Error:
some [ERROR] nondeterministic `if *` reached symbolic evaluation; run the nondetElim transform to eliminate nondeterministic control first
Expression Env:
State:
[(x : int) → 0]

Evaluation Config:
Eval Depth: 200
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
-/
#guard_msgs in
#eval (evalOne ∅ [.init "x" t[int] (.det eb[#0]) .empty,
                    .ite .nondet
                      [Statement.set "x" eb[#1] .empty]
                      [Statement.set "x" eb[#2] .empty]
                      .empty,
                    .assert "x_pos" eb[(x == #1)] .empty]) |> format

/-- The proof obligations deferred in `E`, one per line. -/
private def deferredFormat (E : Env) : Format :=
  Format.joinSep (E.deferred.toList.map fun ob =>
    (Lambda.LExpr.instToFormatLExpr CoreLParams.mono).format ob.obligation) Format.line

/-! ### A call's contract does not depend on type variable names

`p<a, b>(x : a, y : b)` requires `opPair(x, y)`, with `opPair : a → b → bool`. Calling `p(u, v)`
with `u : b` and `v : a`, and the same call with the caller's `b` and `a` renamed to `d` and
`c`, gives the same precondition up to that renaming. -/

private def contractRenamed (tyU tyV : Lambda.LMonoTy) : Format :=
  let tvA : Lambda.LMonoTy := .ftvar "a"
  let tvB : Lambda.LMonoTy := .ftvar "b"
  let pre : Expression.Expr := Lambda.RenamingFixtures.opPairCall Core.coreLoc tvA tvB
  let proc : Procedure :=
    { header := { name := "p", typeArgs := ["a", "b"],
                  inputs := [("x", tvA), ("y", tvB)], outputs := [] },
      spec := { preconditions := [("pre", ⟨pre, .Default, #[]⟩)], postconditions := [] } }
  let E := { Env.init with program := { decls := [.proc proc .empty] } }
  let (_, E) := Command.inlineCallContract E [] "p" none
    [.fvar Core.coreLoc "u" (some tyU), .fvar Core.coreLoc "v" (some tyV)] .empty
  deferredFormat E

/-- info: ((~opPair : (arrow b (arrow a bool))) (u : b) (v : a)) -/
#guard_msgs in
#eval contractRenamed (.ftvar "b") (.ftvar "a")

/-- info: ((~opPair : (arrow d (arrow c bool))) (u : d) (v : c)) -/
#guard_msgs in
#eval contractRenamed (.ftvar "d") (.ftvar "c")

/-! `q<a, b, c>(x : a, y : b) returns (r : a)` requires `opQ(x, y, k)`, with
`opQ : a → b → c → bool` and `k : c`. In `w := q(u, v)`, `u` has no known type, `v : a` fixes the
callee's `b`, and `w : b` fixes its `a`. Renaming the caller's `b` and `a` to `d` and `c` renames
the precondition alike; no argument fixes the callee's `c`, which becomes `$__callty2`. -/

private def contractRenamedOut (tyV tyW : Lambda.LMonoTy) : Format :=
  let tvA : Lambda.LMonoTy := .ftvar "a"
  let tvB : Lambda.LMonoTy := .ftvar "b"
  let tvC : Lambda.LMonoTy := .ftvar "c"
  let pre : Expression.Expr :=
    .app Core.coreLoc (.app Core.coreLoc
                       (.app Core.coreLoc (.op Core.coreLoc "opQ"
                                           (some (.arrow tvA (.arrow tvB (.arrow tvC .bool)))))
      (.fvar Core.coreLoc "x" (some tvA))) (.fvar Core.coreLoc "y" (some tvB)))
          (.op Core.coreLoc "k" (some tvC))
  let proc : Procedure :=
    { header := { name := "q", typeArgs := ["a", "b", "c"],
                  inputs := [("x", tvA), ("y", tvB)], outputs := [("r", tvA)] },
      spec := { preconditions := [("pre", ⟨pre, .Default, #[]⟩)], postconditions := [] } }
  let E := { Env.init with program := { decls := [.proc proc .empty] } }
  let E := E.insertInContext ("w", some tyW) (.fvar Core.coreLoc "w" (some tyW))
  let (_, E) := Command.inlineCallContract E ["w"] "q" none
    [.fvar Core.coreLoc "u" none, .fvar Core.coreLoc "v" (some tyV)] .empty
  deferredFormat E

/--
info: ((~opQ : (arrow b (arrow a (arrow $__callty2 bool)))) u (v : a) (~k : $__callty2))
-/
#guard_msgs in
#eval contractRenamedOut (.ftvar "a") (.ftvar "b")

/--
info: ((~opQ : (arrow d (arrow c (arrow $__callty2 bool)))) u (v : c) (~k : $__callty2))
-/
#guard_msgs in
#eval contractRenamedOut (.ftvar "c") (.ftvar "d")

/-! ### A call's stored type arguments give the callee's type instance

`r<a>(x : a)` requires `opR(x)`, with `opR : a → bool`, and is called with an argument `u` whose
type is unknown. A stored `int` instantiates `a`. A stored type that mentions a generated type
variable is not used, so `a` becomes `$__callty0`, as for a call without stored type arguments. -/

private def contractStored (tyArgs : Option (List Core.Expression.Ty)) : Format :=
  let tvA : Lambda.LMonoTy := .ftvar "a"
  let pre : Expression.Expr :=
    .app Core.coreLoc (.op Core.coreLoc "opR" (some (.arrow tvA .bool)))
      (.fvar Core.coreLoc "x" (some tvA))
  let proc : Procedure :=
    { header := { name := "r", typeArgs := ["a"], inputs := [("x", tvA)], outputs := [] },
      spec := { preconditions := [("pre", ⟨pre, .Default, #[]⟩)], postconditions := [] } }
  let E := { Env.init with program := { decls := [.proc proc .empty] } }
  let (_, E) := Command.inlineCallContract E [] "r" tyArgs
    [.fvar Core.coreLoc "u" none] .empty
  deferredFormat E

/-- info: ((~opR : (arrow int bool)) u) -/
#guard_msgs in
#eval contractStored (some [.forAll [] .int])

/-- info: ((~opR : (arrow $__callty0 bool)) u) -/
#guard_msgs in
#eval contractStored (some [.forAll [] (.ftvar "$__ty3")])

/-- info: ((~opR : (arrow $__callty0 bool)) u) -/
#guard_msgs in
#eval contractStored none

/-- A stored `int` against an argument `u : bool`: the evaluator reports the disagreement. -/
private def contractStoredClash : Format :=
  let tvA : Lambda.LMonoTy := .ftvar "a"
  let proc : Procedure :=
    { header := { name := "r", typeArgs := ["a"], inputs := [("x", tvA)], outputs := [] },
      spec := { preconditions := [], postconditions := [] } }
  let E := { Env.init with program := { decls := [.proc proc .empty] } }
  let (_, E) := Command.inlineCallContract E [] "r" (some [.forAll [] .int])
    [.fvar Core.coreLoc "u" (some .bool)] .empty
  match E.error with
  | some e => format e
  | none => "no error"

/--
info: [ERROR] Ill-formed call: the call to r stores a = int,
but its arguments give a = bool
-/
#guard_msgs in
#eval contractStoredClash

/-- The callee `q<a, b>(x : a, y : b)` is called with arguments whose types are both the
    generated variable `$__ty0`, so the call gives `a` and `b` one type. The stored `a = int`
    binds `$__ty0`, and the stored `b = bool` disagrees; the message writes no generated name. -/
private def contractStoredThreaded : Format :=
  let tvA : Lambda.LMonoTy := .ftvar "a"
  let tvB : Lambda.LMonoTy := .ftvar "b"
  let proc : Procedure :=
    { header := { name := "q", typeArgs := ["a", "b"],
                  inputs := [("x", tvA), ("y", tvB)], outputs := [] },
      spec := { preconditions := [], postconditions := [] } }
  let E := { Env.init with program := { decls := [.proc proc .empty] } }
  let (_, E) := Command.inlineCallContract E [] "q" (some [.forAll [] .int, .forAll [] .bool])
    [.fvar Core.coreLoc "u" (some (.ftvar "$__ty0")),
     .fvar Core.coreLoc "v" (some (.ftvar "$__ty0"))] .empty
  match E.error with
  | some e => format e
  | none => "no error"

/--
info: [ERROR] Ill-formed call: the call to q stores b = bool,
but its arguments give b = int
-/
#guard_msgs in
#eval contractStoredThreaded

/-- The callee `r<a>(x : a, y : MyInt)` names an alias that its header does not expand, so the
    call's argument types cannot be matched against it. With stored `a = bool` and arguments
    `u : bool`, `v : int`, the stored list is used and there is no error. -/
private def contractStoredAlias : Format :=
  let tvA : Lambda.LMonoTy := .ftvar "a"
  let pre : Expression.Expr :=
    .app Core.coreLoc (.op Core.coreLoc "opR" (some (.arrow tvA .bool)))
      (.fvar Core.coreLoc "x" (some tvA))
  let proc : Procedure :=
    { header := { name := "r", typeArgs := ["a"], outputs := [],
                  inputs := [("x", tvA), ("y", .tcons "MyInt" [])] },
      spec := { preconditions := [("pre", ⟨pre, .Default, #[]⟩)], postconditions := [] } }
  let E := { Env.init with program := { decls := [.proc proc .empty] } }
  let (_, E) := Command.inlineCallContract E [] "r" (some [.forAll [] .bool])
    [.fvar Core.coreLoc "u" (some .bool), .fvar Core.coreLoc "v" (some .int)] .empty
  match E.error with
  | some e => format e
  | none => deferredFormat E

/-- info: ((~opR : (arrow bool bool)) (u : bool)) -/
#guard_msgs in
#eval contractStoredAlias

/-- The same call as `contractStoredAlias` with a wrong stored `a = int` for `u : bool`. The
    matching still fails on the alias, so nothing is checked and the stored list is used. -/
private def contractStoredAliasWrong : Format :=
  let tvA : Lambda.LMonoTy := .ftvar "a"
  let pre : Expression.Expr :=
    .app Core.coreLoc (.op Core.coreLoc "opR" (some (.arrow tvA .bool)))
      (.fvar Core.coreLoc "x" (some tvA))
  let proc : Procedure :=
    { header := { name := "r", typeArgs := ["a"], outputs := [],
                  inputs := [("x", tvA), ("y", .tcons "MyInt" [])] },
      spec := { preconditions := [("pre", ⟨pre, .Default, #[]⟩)], postconditions := [] } }
  let E := { Env.init with program := { decls := [.proc proc .empty] } }
  let (_, E) := Command.inlineCallContract E [] "r" (some [.forAll [] .int])
    [.fvar Core.coreLoc "u" (some .bool), .fvar Core.coreLoc "v" (some .int)] .empty
  match E.error with
  | some e => format e
  | none => deferredFormat E

/-- info: ((~opR : (arrow int bool)) (u : bool)) -/
#guard_msgs in
#eval contractStoredAliasWrong

/-- A call from a polymorphic caller whose argument has the caller's type variable `b`: the
    stored `b` agrees with the argument type, so there is no error. -/
private def contractStoredCallerVar : Format :=
  let tvA : Lambda.LMonoTy := .ftvar "a"
  let pre : Expression.Expr :=
    .app Core.coreLoc (.op Core.coreLoc "opR" (some (.arrow tvA .bool)))
      (.fvar Core.coreLoc "x" (some tvA))
  let proc : Procedure :=
    { header := { name := "r", typeArgs := ["a"], inputs := [("x", tvA)], outputs := [] },
      spec := { preconditions := [("pre", ⟨pre, .Default, #[]⟩)], postconditions := [] } }
  let E := { Env.init with program := { decls := [.proc proc .empty] } }
  let (_, E) := Command.inlineCallContract E [] "r" (some [.forAll [] (.ftvar "b")])
    [.fvar Core.coreLoc "u" (some (.ftvar "b"))] .empty
  match E.error with
  | some e => format e
  | none => deferredFormat E

/-- info: ((~opR : (arrow b bool)) (u : b)) -/
#guard_msgs in
#eval contractStoredCallerVar

/-- `contractStoredAliasWrong` as a whole program: the call stores `a = int` for a `bool` argument,
    which would prove `opR(x)` by the axiom. `Core.verify` type checks first and replaces the
    stored list, so the precondition stays unproved. -/
private def storedAliasProgram : Program :=
  let tvA : Lambda.LMonoTy := .ftvar "a"
  let opR (ty : Lambda.LMonoTy) : Expression.Expr :=
    .op Core.coreLoc "opR" (some (.arrow ty .bool))
  let rProc : Procedure :=
    { header := { name := "r", typeArgs := ["a"], outputs := [],
                  inputs := [("x", tvA), ("y", .tcons "MyInt" [])] },
      spec := { preconditions :=
                  [("pre", ⟨.app Core.coreLoc (opR tvA) (.fvar Core.coreLoc "x" (some tvA)),
                    .Default, #[]⟩)],
                postconditions := [] } }
  let mainProc : Procedure :=
    { header := { name := "main", typeArgs := [], inputs := [], outputs := [] },
      spec := { preconditions := [], postconditions := [] },
      body := .structured
        [Statement.init "u" (.forAll [] .bool) .nondet .empty,
         Statement.call "r" (some [.forAll [] .int])
           [.inArg (.fvar Core.coreLoc "u" none), .inArg (.intConst Core.coreLoc 0)] .empty] false }
  { decls :=
      [.type (.syn { name := "MyInt", typeArgs := [], type := .int }) .empty,
       .func { name := "opR", typeArgs := ["a"], inputs := [("x", tvA)], output := .bool } .empty,
       .ax { name := "opRInt",
             e := .all Core.coreLoc "x" (some .int)
                    (.app Core.coreLoc (opR .int) (.bvar Core.coreLoc 0)) } .empty,
       .proc rProc .empty, .proc mainProc .empty] }

private def verifyStoredAlias : IO Unit := do
  IO.FS.withTempDir fun tempDir => do
    match ← (Core.verify storedAliasProgram tempDir .quiet).toBaseIO with
    | .ok results =>
      for r in results do
        IO.println s!"{r.obligation.label}: {r.formatOutcome}"
    | .error e => IO.println s!"error: {e}"

/-- info: callElimAssert_pre_2: ❓ unknown -/
#guard_msgs in
#eval verifyStoredAlias

end Tests
---------------------------------------------------------------------
end Core

end
