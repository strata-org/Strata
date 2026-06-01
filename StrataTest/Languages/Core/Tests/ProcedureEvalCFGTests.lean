/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.ProcedureEval

namespace Core

section CFGEvalTests

open Std (ToFormat Format format)
open Procedure Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Imperative

private def cfgEval (p : Procedure) : String :=
  let E := Env.init (empty_factory := true)
  let (E, _stats) := eval E p
  toString (format E)

/-! ## Trivial CFG: single block with finish, no parameters -/

/--
info: Error:
none
Subst Map:

Expression Env:
State:


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
#eval IO.println (cfgEval
  { header := {name := "Trivial", typeArgs := [], inputs := [], outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .cfg { entry := "start",
                   blocks := [("start", { cmds := [], transfer := .finish })] } })

/-! ## Linear CFG: assignment via goto, postcondition holds -/

/--
info: Error:
none
Subst Map:

Expression Env:
State:


Evaluation Config:
Eval Depth: 200
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: y_eq_42
Property: assert
Assumptions:

Proof Obligation:
true
-/
#guard_msgs in
#eval IO.println (cfgEval
  { header := {name := "Linear", typeArgs := [],
               inputs := [], outputs := [("y", mty[int])] },
    spec := { preconditions := [],
              postconditions := [("y_eq_42", ⟨eb[y == #42], .Default, #[]⟩)] },
    body := .cfg { entry := "entry",
                   blocks := [
                     ("entry", { cmds := [CmdExt.cmd (Cmd.set "y" (.det eb[#42]) .empty)],
                                 transfer := .goto "done" }),
                     ("done", { cmds := [], transfer := .finish })
                   ] } })

/-! ## Missing block error -/

/--
info: Error:
some [ERROR] evalCFG: block 'nonexistent' not found in CFG
Subst Map:

Expression Env:
State:
[]

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
#eval IO.println (cfgEval
  { header := {name := "MissingBlock", typeArgs := [], inputs := [], outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .cfg { entry := "start",
                   blocks := [("start", { cmds := [],
                                          transfer := .goto "nonexistent" })] } })

/-! ## Fuel exhaustion: loop back-edge -/

/--
info: has error: true
-/
#guard_msgs in
#eval do
  let E := Env.init (empty_factory := true)
  let p : Procedure :=
    { header := {name := "Loop", typeArgs := [],
                 inputs := [], outputs := [("y", mty[int])] },
      spec := { preconditions := [], postconditions := [] },
      body := .cfg { entry := "loop",
                     blocks := [
                       ("loop", { cmds := [CmdExt.cmd (Cmd.set "y" (.det eb[#1]) .empty)],
                                  transfer := .goto "loop" })
                     ] } }
  let (E, _stats) := eval E p
  IO.println s!"has error: {E.error.isSome}"

/-! ## Postcondition failure: non-trivial proof obligation -/

/--
info: Error:
none
Subst Map:

Expression Env:
State:


Evaluation Config:
Eval Depth: 200
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: y_eq_0
Property: assert
Assumptions:

Proof Obligation:
false
-/
#guard_msgs in
#eval IO.println (cfgEval
  { header := {name := "PostFail", typeArgs := [],
               inputs := [], outputs := [("y", mty[int])] },
    spec := { preconditions := [],
              postconditions := [("y_eq_0", ⟨eb[y == #0], .Default, #[]⟩)] },
    body := .cfg { entry := "entry",
                   blocks := [
                     ("entry", { cmds := [CmdExt.cmd (Cmd.set "y" (.det eb[#42]) .empty)],
                                 transfer := .finish })
                   ] } })

/-! ## Diamond CFG: symbolic branch produces two proof obligations -/

/--
info: Error:
none
Subst Map:

Expression Env:
State:


Evaluation Config:
Eval Depth: 200
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: y_ge_0
Property: assert
Assumptions:
(<cfgBranch_true: x >= 0>, x@1 >= 0)
Proof Obligation:
x@1 >= 0

Label: y_ge_0
Property: assert
Assumptions:
(<cfgBranch_false: !(x >= 0)>, if x@1 >= 0 then false else true)
Proof Obligation:
0 - x@1 >= 0
-/
#guard_msgs in
#eval IO.println (cfgEval
  { header := {name := "Diamond", typeArgs := [],
               inputs := [("x", mty[int])],
               outputs := [("y", mty[int])] },
    spec := { preconditions := [],
              postconditions := [("y_ge_0", ⟨eb[((~Int.Ge y) #0)], .Default, #[]⟩)] },
    body := .cfg { entry := "entry",
                   blocks := [
                     ("entry", { cmds := [],
                                 transfer := .condGoto eb[((~Int.Ge x) #0)] "pos" "neg" }),
                     ("pos", { cmds := [CmdExt.cmd (Cmd.set "y" (.det eb[x]) .empty)],
                               transfer := .goto "done" }),
                     ("neg", { cmds := [CmdExt.cmd (Cmd.set "y" (.det eb[((~Int.Sub #0) x)]) .empty)],
                               transfer := .goto "done" }),
                     ("done", { cmds := [], transfer := .finish })
                   ] } })

/-! ## Pre-split assert deduped across symbolic condGoto

An `assert` evaluated *before* a symbolic `condGoto` lands in the parent
env's `deferred` array. Both branches inherit `env'` by record-update, so
without dedup the pre-split obligation would appear once per terminal
path after `mergeResults` concatenates them. Each `ProofObligation`
captures its assumptions at creation time (see
`Strata/DL/Imperative/CmdEval.lean`), so duplicates are redundant: the
fix in `evalCFGStep` clears the false-branch's `deferred`, mirroring
`Strata/Languages/Core/StatementEval.lean:673` for the structured `.ite`
path. This test exercises that dedup — the `pre_assert` obligation must
appear exactly once in the merged output.
-/

/--
info: Error:
none
Subst Map:

Expression Env:
State:


Evaluation Config:
Eval Depth: 200
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: pre_assert
Property: assert
Assumptions:

Proof Obligation:
x@1 >= 0
-/
#guard_msgs in
#eval IO.println (cfgEval
  { header := {name := "PreSplitAssert", typeArgs := [],
               inputs := [("x", mty[int])],
               outputs := [] },
    spec := { preconditions := [],
              postconditions := [] },
    body := .cfg { entry := "entry",
                   blocks := [
                     ("entry", { cmds := [CmdExt.cmd (Cmd.assert "pre_assert" eb[((~Int.Ge x) #0)] .empty)],
                                 transfer := .condGoto eb[((~Int.Ge x) #0)] "left" "right" }),
                     ("left",  { cmds := [], transfer := .finish }),
                     ("right", { cmds := [], transfer := .finish })
                   ] } })

end CFGEvalTests
end Core
