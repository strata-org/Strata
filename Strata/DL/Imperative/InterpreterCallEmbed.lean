/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterCall
public import Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.InterpreterCall
import Strata.DL.Imperative.InterpreterReplayTactics

/-! # Base programs as call-free call-aware programs

A program over the base command language `Cmd P` is a program over the call-aware
command language `CmdExt P` that contains no `.call`: every command `c` becomes
`CmdExt.cmd c` (`embedStmt`/`embedBlock`/`embedConfig`, and `embedIConfig` on interpreter
configurations).  On such a program the
call-aware stepper `Calls.stepCmd π` performs exactly the steps of the base stepper
`baseStepCmd`, for every callee table `π`: the two runs emit the same events, consume
the same oracle, and end in corresponding configurations.  Replay of a base
counterexample therefore needs no separate path: it is call-aware replay of its
embedding (`embedCexA`), at any `π`.

These two facts (`runInterp_embedIConfig`, `runReplay_embedConfig`) are proved in
`InterpreterCallEmbedProps.lean`. -/

namespace Imperative

public section

namespace Calls

variable {P : PureExpr} [InterpLang P]

mutual

/-- A base statement as a call-free call-aware statement. -/
@[expose] def embedStmt : Stmt P (Cmd P) → Stmt P (CmdExt P)
  | .cmd c => .cmd (.cmd c)
  | .block l b md => .block l (embedBlock b) md
  | .ite g t e md => .ite g (embedBlock t) (embedBlock e) md
  | .loop g m inv b md => .loop g m inv (embedBlock b) md
  | .exit l md => .exit l md
  | .typeDecl t md => .typeDecl t md

/-- A base block as a call-free call-aware block. -/
@[expose] def embedBlock : List (Stmt P (Cmd P)) → List (Stmt P (CmdExt P))
  | [] => []
  | s :: ss => embedStmt s :: embedBlock ss

end

/-- A base configuration as a call-free call-aware configuration. -/
@[expose] def embedConfig : Config P (Cmd P) → Config P (CmdExt P)
  | .stmt s env => .stmt (embedStmt s) env
  | .stmts ss env => .stmts (embedBlock ss) env
  | .terminal env => .terminal env
  | .exiting l env => .exiting l env
  | .seq inner ss => .seq (embedConfig inner) (embedBlock ss)
  | .block l σ inner => .block l σ (embedConfig inner)

/-- A base interpreter configuration as a call-free call-aware one (same scope frames). -/
@[expose] def embedIConfig : IConfig P (Cmd P) → IConfig P (CmdExt P)
  | .stmt s env => .stmt (embedStmt s) env
  | .stmts ss env => .stmts (embedBlock ss) env
  | .terminal env => .terminal env
  | .exiting l env => .exiting l env
  | .seq inner ss => .seq (embedIConfig inner) (embedBlock ss)
  | .seqs inner k => .seqs (embedIConfig inner) k
  | .block l fr inner => .block l fr (embedIConfig inner)

/-- A base counterexample as a call-aware one (same oracle). -/
@[expose] def embedCexA (cex : CexA P (Cmd P)) : CexA P (CmdExt P) :=
  { cfg := embedIConfig cex.cfg, oracle := cex.oracle }

end Calls

end -- public section

end Imperative
