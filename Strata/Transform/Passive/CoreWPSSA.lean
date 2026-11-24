/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPCoreProgram
public import Strata.Transform.SSA.SSACoreProgram

/-! # The WP and SSA phases in sequence on Core procedures and programs

The composition of the WP phase (`WP/WPCoreProgram.lean`) and the SSA phase
(`SSA/SSACoreProgram.lean`) on one procedure (`wpSSALoopFree`, `wpSSAProcBody`: both phases'
outputs) and on a program (`wpSSAProgramWith`).  Their properties are in `CoreWPSSAProps.lean`.

Key definitions: `wpSSALoopFree`, `wpSSAProcBody`, `wpSSAProgramWith`. -/

namespace Core
namespace WP

open Imperative Imperative.BigStep Imperative.WP Lambda

public section

/-- **The WP and SSA phases on one loop-free statement list** `ss` of `p`: the output of the WP
    phase, then the entry renaming and the output of the SSA phase on its guarded program, under
    the factory `fac`.  The fresh names of the WP phase avoid `Gw`, those of the SSA phase
    `Gs`. -/
@[expose] def wpSSALoopFree (fac : Lambda.Factory CoreLParams) (Gw Gs : IdSet Expression)
    (p : Procedure) (ss : Statements) :
    Except String (WOut Expression × Ren Expression × SOut Expression) := do
  let w ← wpLoopFree Gw p ss
  let (ρ0, so) ← ssaLoopFree fac Gs p w.lay
  pure (w, ρ0, so)

/-- `wpSSALoopFree` of the loop-free statement list of a procedure with body `body`
    (`Procedure.contractWrapped`). -/
@[expose] def wpSSAProcBody (fac : Lambda.Factory CoreLParams) (Gw Gs : IdSet Expression)
    (p : Procedure) (body : Statements) :
    Except String (WOut Expression × Ren Expression × SOut Expression) :=
  wpSSALoopFree fac Gw Gs p (p.contractWrapped body)

/-- The WP phase of a program, then its SSA phase under the factory `fac`. -/
@[expose] def wpSSAProgramWith (fac : Lambda.Factory CoreLParams)
    (reserved : List Expression.Ident) (declProgram : Program)
    (lemmaObls : List (Imperative.ProofObligation Expression)) (program : Program) :
    Except String Program := do
  let mid ← wpProgramWith reserved declProgram lemmaObls program
  ssaProgram fac reserved mid

end -- public section

end WP
end Core
