/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.MetaVerifier -- shake: keep
public import StrataBoole.Verify
meta import Lean.Meta.Eval
import Lean.Meta.Eval -- shake: keep
import Lean.Meta.Tactic.Rewrite -- shake: keep
meta import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Unfold -- shake: keep
meta import Lean.Meta.Tactic.Unfold

/-!
# Boole MetaVerifier

Extends `Strata.MetaVerifier` with Boole dialect support for `genCoreVCs` and
`smtVCsCorrect`. Test files in the `StrataBoole` package should import this
module instead of `Strata.MetaVerifier` directly.
-/

public section

namespace Strata.Boole

open StrataDDM (GlobalContext Program)

def genVCs (program : Strata.Boole.Program) (gctx : GlobalContext) (options : Core.VerifyOptions := .default) : Option Core.coreVCs := do
  let program ← (Strata.Boole.toCoreProgram program gctx).toOption
  Core.genVCs program options

end Strata.Boole

namespace Strata

open StrataDDM (Program)

/--
Generate verification conditions for a `StrataDDM.Program`, with Boole support.
Extends `Strata.genCoreVCs` to handle the Boole dialect.
-/
def genCoreVCsBoole (program : Program)
    (options : MetaVerifier.Options := {}) : Option Core.coreVCs := do
  if program.dialect == "Boole" then
    match Boole.getProgram program with
    | .ok booleProgram =>
      Boole.genVCs booleProgram program.globalContext options.toVerifyOptions
    | .error _ => none
  else
    genCoreVCs program options

/--
Generate SMT verification conditions for a `StrataDDM.Program`, with Boole support.
-/
def genSMTVCsBoole (program : Program)
    (options : MetaVerifier.Options := {}) : Option SMT.SMTVCs := do
  let coreVCs ← genCoreVCsBoole program options
  toSMTVCs coreVCs options

/--
State semantic correctness of the SMT verification conditions generated for a
program under the given metaverifier options, with Boole dialect support. For
example, `options.useArrayTheory` selects how the SMT encoder treats `Map`
types: under `true` they become SMT-LIB arrays, under `false` an uninterpreted
sort with axiomatized `select`/`update` functions.
-/
def smtVCsCorrectBoole (program : Program)
    (options : MetaVerifier.Options := {}) : Prop :=
  match genSMTVCsBoole program options with
  | some vcs => (denoteQueries vcs).getD False
  | none     => False

end Strata

namespace Strata.Meta

open Lean hiding Options

private unsafe def genSMTVCsBooleUnsafe (mv : MVarId) : MetaM (List MVarId) := do
  let type ← mv.getType
  let some (program, options) := type.app2? ``Strata.smtVCsCorrectBoole
    | throwError "Expected a Strata.smtVCsCorrectBoole goal"
  trace[debug] m!"Generating SMT VCs for {program}"
  let mv ← Meta.unfoldTarget mv ``Strata.smtVCsCorrectBoole
  let ovcs := mkApp2 (.const ``Strata.genSMTVCsBoole []) program options
  let ovcsType := .app (.const ``Option [0]) (.const ``Strata.SMT.SMTVCs [])
  let some evcs ← Meta.evalExpr (Option Strata.SMT.SMTVCs) ovcsType ovcs
    | throwError "Failed to generate VCs"
  trace[debug] m!"Generated {repr evcs}"
  let rhs := toExpr (some evcs)
  let eqVCs := mkApp3 (.const ``Eq [1]) ovcsType ovcs rhs
  let hEQVCs ← nativeDecide eqVCs
  let r ← mv.rewrite (← mv.getType) hEQVCs
  let mv ← mv.replaceTargetEq r.eNew r.eqProof
  let mvs ← evcs.mapM SMT.createGoal
  trace[debug] m!"Created {mvs.length} SMT VC goals: {mvs}"
  let ps ← mvs.mapM MVarId.getType
  let hP := andNIntro (List.zip ps (mvs.map Expr.mvar))
  mv.assign hP
  return mvs

@[implemented_by genSMTVCsBooleUnsafe]
meta opaque genSMTVCsBoole (mv : MVarId) : MetaM (List MVarId)

end Strata.Meta

namespace Strata.Tactic

open Lean Elab Tactic in
/--
Generate one Lean goal per SMT verification condition in a goal of the form
`Strata.smtVCsCorrectBoole program`. Boole-aware variant of `gen_smt_vcs`.
-/
syntax (name := genSMTVCsBoole) "gen_smt_vcs_boole" : tactic

open Lean Elab Tactic in
@[tactic genSMTVCsBoole] meta def evalGenSMTVCsBoole : Tactic := fun stx => do
  match stx with
  | `(tactic| gen_smt_vcs_boole) =>
    let mvs ← Meta.genSMTVCsBoole (← Tactic.getMainGoal)
    Tactic.replaceMainGoal mvs
  | _ => throwUnsupportedSyntax

end Strata.Tactic

end -- public section
