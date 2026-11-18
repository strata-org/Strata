/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.Languages.Core.SymExecReplay
public meta import Strata.Languages.Core.Verifier
public meta import Strata.SimpleAPI

/-! # Helpers shared by the symbolic-execution tests

Translating and type-checking a test program as the verifier does before VC generation
(`progOf`, `procOf`), running a procedure with the test budgets (`run`), printing obligations
(`oblLines`, `printObls`), replaying a model (`modelOf`, `replayAt`), and verifying a program
(`verifyLines`, which drops an error's source range with `withoutRange`).
-/

meta section

public section

namespace SymExecTestSupport

open Core Core.SymExec Lambda Imperative

/-- `pgm` translated and type-checked as the verifier does before VC generation; `none` if
    type checking fails. -/
def progOf (pgm : StrataDDM.Program) : Option Program :=
  let (prog, _) := Strata.Core.getProgram pgm
  match Core.typeCheck { VerifyOptions.default with verbose := .quiet } prog with
  | .ok prog => some prog
  | .error _ => none

/-- The procedure `name` of `progOf pgm`; `none` if type checking fails or there is no such
    procedure. -/
def procOf (pgm : StrataDDM.Program) (name : String := "P") : Option Procedure :=
  (progOf pgm).bind fun prog => prog.decls.findSome? fun
    | .proc p _ => if p.header.name.name == name then some p else none
    | _ => none

/-- One line per obligation: `[label] under [path condition, oldest first]  check: condition`,
    in Core's text. -/
def oblLines (os : List Obl) : String :=
  "\n".intercalate <| os.map fun o =>
    s!"[{o.label}] under {(pcExprs o.pc).reverse.map (toString <| Std.format ·)}  " ++
      s!"check: {Std.format o.cond}"

/-- A model giving each symbol listed in `bs` (by its name after the default prefix) its paired
    `int` value. -/
def modelOf (bs : List (String × Int)) : CoreIdent → Option Expression.Expr := fun x =>
  (bs.find? fun (n, _) => x.name == defaultSymPrefix ++ n).map fun (_, v) => .intConst valueLoc v

/-- Run `p` under merge policy `pol` and configuration `cfg`, with at most 10000 steps in total
    and `fuel` per path; `none` if there is no procedure. -/
def run (p : Option Procedure) (pol : MergePolicy := .never) (cfg : ExploreCfg := {})
    (fuel : Nat := 1000) : Option Result :=
  p.map (exploreProc cfg 10000 fuel Core.Factory · (pol := pol))

/-- Print the obligations of `r` (`oblLines`), or `no result`. -/
def printObls (r : Option Result) : IO Unit :=
  IO.println <| match r with
    | some r => oblLines r.obligations
    | none => "no result"

/-- The verdict of replaying the model `modelOf bs` for the `i`-th obligation of `run p pol`. -/
def replayAt (p : Option Procedure) (pol : MergePolicy) (i : Nat) (bs : List (String × Int)) :
    Option (CEValidationVerdict StopReason) :=
  (run p pol).bind fun r => r.obligations[i]? >>= fun o => replayObl Core.Factory r o (modelOf bs)

/-- An error message without its leading source range `(start-end) `, which moves with every
    edit above the program. -/
def withoutRange (msg : String) : String :=
  match msg.splitOn ") " with
  | r :: rest => if r.startsWith "(" && !rest.isEmpty then ") ".intercalate rest else msg
  | [] => msg

/-- One line per result of verifying `prog` under `opts`: the label, then `formatOutcome`; or
    the error, without its source range. -/
def verifyLines (prog : Program) (opts : VerifyOptions) : IO String := do
  try
    let rs ← EIO.toIO (fun e => IO.Error.userError (toString e))
      (Strata.Core.verifyProgram prog opts)
    return "\n".intercalate (rs.toList.map fun r => s!"{r.obligation.label}: {r.formatOutcome}")
  catch e => return s!"error: {withoutRange (toString e)}"

end SymExecTestSupport

end

end
