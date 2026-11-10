/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterReplay

/-! # Shared proof automation for the DL-level replay modules

Tactic macros for proofs about `ReplayM` programs and interpreter runs:
* `bridge_close` / `bridge_ind`: close a goal stated with a bridge predicate (`DBridge`,
  `FeasBridge`, `StopBridge`, `CoBridge`) by its per-construct lemmas (`dBridge_…`,
  `feasBridge_…`, `stopBridge_…`, `coBridge_…`), and prove those lemmas by recursion;
* `eff_simp` / `eff_inv`: simplify a run of `choose`/`emit` effects, and invert an equation on
  such a run into its success paths.
-/

namespace Imperative

set_option hygiene false in
/-- `bridge_close X` (`X` = `dBridge`, `feasBridge`, `stopBridge` or `coBridge`, the lemma
    prefix of a bridge predicate): close the bridge goal for a `ReplayM` program by the `X_…`
    lemmas and the local hypotheses, at reducible transparency, unfolding `resolveGuard`. -/
macro "bridge_close " b:ident : tactic => do
  let n (s : String) := Lean.mkIdent (b.getId.appendAfter s)
  `(tactic| repeat' with_reducible first
    | apply $(n "_pure")
    | apply $(n "_throw")
    | apply $(n "_choose")
    | apply $(n "_branch")
    | apply $(n "_emit")
    | apply $(n "_forM_emit")
    | apply $(n "_bind'") (hg := fun _ _ => ?_)
    | split
    | dsimp only
    | unfold resolveGuard
    | apply $(n "_stepBaseCmdStore")
    | (apply $(n "_runInterp")
       exact fun _ => by assumption)
    | (apply $(n "_runCallee")
       exact fun _ => by assumption)
    | apply_assumption
    | apply $(n "_stepInterp"))

set_option hygiene false in
/-- `bridge_ind X`: prove an
    `X_{forM_emit,stepBaseCmdStore,stepInterp,runInterp,runCallee,stepCmd}`
    lemma by its recursion, then `bridge_close X`.  A `stepCmd` lemma is stated over the fuel
    and then the call-depth budget; its recursion is on the fuel, and the callee body's case
    uses the induction hypothesis at the callee's budget. -/
macro "bridge_ind " b:ident : tactic => `(tactic| first
  | (match evs with
      | [] | _ :: _ =>
        simp only [List.forM]
        bridge_close $b)
  | (unfold stepBaseCmdStore
     bridge_close $b)
  | (intro n c
     induction c <;> intro _ _ <;> unfold stepInterp <;> bridge_close $b
     done)
  | (intro n
     induction n <;> intro c _ _ <;> cases c <;> unfold runInterp <;> bridge_close $b
     done)
  | (intro k
     induction k with
     | zero => intro _ _ c _ _; cases c <;> simp only [stepCmd] <;> bridge_close $b
     | succ k ih =>
       intro d _ c _ _
       cases c
       · simp only [stepCmd]; bridge_close $b
       · cases d
         · simp only [stepCmd]; bridge_close $b
         · rename_i d; simp only [stepCmd]; have ih := ih d; bridge_close $b))

set_option hygiene false in
/-- `eff_simp [l] at loc`: `simp` unfolding `choose`/`emit`/`branch` and the `replayRun`
    equations for `read`, `get`, `modify`, `pure` and `throw`. -/
macro "eff_simp" "[" a:Lean.Parser.Tactic.simpLemma,* "]" l:(Lean.Parser.Tactic.location)? :
    tactic =>
  `(tactic| simp [InterpEffects.choose, InterpEffects.emit, InterpEffects.branch,
    replayRun_read_bind,
    replayRun_get_bind, replayRun_modify_bind, replayRun_pure, replayRun_throw, $a,*] $(l)?)

set_option hygiene false in
/-- `eff_inv [l]`: split `h : run (choose/emit/branch …) … = …` into its success paths. -/
macro "eff_inv" "[" a:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp only [InterpEffects.choose, InterpEffects.emit, InterpEffects.branch, replayRun_read_bind,
    replayRun_get_bind,
    replayRun_modify_bind, replayRun_pure, replayRun_throw, $a,*] at h
  (repeat' split at h) <;> cases h))

end Imperative
