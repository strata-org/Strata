/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Interpreter
public import Strata.DL.Imperative.InterpreterReplayTactics

/-! # Shared proof automation for the Core-level replay, `EvalM` and call modules -/

namespace Core

open Lean Elab Tactic in
set_option hygiene false in
/-- `core_gen_by [r₁, …] l`: prove the Core instance of `Imperative.Calls.l` by rewriting with
    `r₁, …` and closing the goal with `Calls.l` (Core's stepper, stop hooks and verdicts are
    abbreviations of the generic ones).  Without `l`, `l` is the current theorem's name with
    `core` → `call`. -/
elab "core_gen_by " "[" rs:Parser.Tactic.simpLemma,* "]" l:(ppSpace ident)? : tactic => do
  let l ← match l with
    | some l => pure l
    | none => do
      let some n ← Term.getDeclName? | throwError "no declaration"
      pure (mkIdent (.mkSimple (n.componentsRev.head!.toString.replace "core" "call")))
  let l := mkIdent (`Imperative.Calls ++ l.getId)
  evalTactic (← `(tactic| (
    (try simp only [$rs,*] at *)
    first | exact $l .. | (apply $l <;> assumption))))

/-- `core_gen l`: `core_gen_by [] l`, without rewrites. -/
macro "core_gen" l:(ppSpace ident)? : tactic => `(tactic| core_gen_by [] $[$l]?)

end Core
