/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.Languages.Cortex
public meta import Strata.Languages.Core.Verifier

/-!
# Hand-built Cortex programs

Builders for one-procedure Cortex programs, and `report`, which prints what
`ToCore.programToCore` makes of such a program.
-/

meta section

public section

namespace Cortex.HandBuilt

open Imperative Lambda

def idn (n : String) : Core.Expression.Ident := ⟨n, ()⟩
def initI (x : String) (v : Int) : IRCmd := .cmd (.init (idn x) (mono .int) (.det (intLit v)) .empty)
def setI (x : String) (v : Int) : IRCmd := .cmd (.set (idn x) (.det (intLit v)) .empty)
def setV (x y : String) : IRCmd := .cmd (.set (idn x) (.det (mkFvar y)) .empty)
def blk (cmds : List IRCmd) (t : DetTransferCmd Label Core.Expression) : LBlock := { cmds, transfer := t }
def br (c lt lf : String) : DetTransferCmd Label Core.Expression := .condGoto (mkFvar c) lt lf .empty
def fin : DetTransferCmd Label Core.Expression := .finish .empty

/-- A program with one procedure `name` whose body is `body`. -/
def mkProgOfBody (name : String) (inputs outputs : List (String × LMonoTy)) (body : Body) :
    UnorderedProgram :=
  { composites := [], procedures := [
      { name, inputs := inputs.map fun (x, t) => (idn x, mono t),
        outputs := outputs.map fun (x, t) => (idn x, mono t), throws := none,
        body := some body }] }

/-- A program with one procedure `name` whose body is the CFG `blocks`. -/
def mkProg (name : String) (inputs outputs : List (String × LMonoTy)) (entry : String)
    (blocks : List (Label × LBlock)) : UnorderedProgram :=
  mkProgOfBody name inputs outputs { cfg := { entry, blocks }, handlers := [] }

def typeCheckResult (p : Core.Program) : String :=
  match Core.typeCheck .quiet p with
  | .ok _ => "type check ok"
  | .error e => s!"type check: {e}"

/-- Run `passes` on `prog` and print how the translation to Core fares on the
result: a translation error, or the result of type-checking the Core program.
With `print`, the Core program is printed as well. A pass that fails is printed
instead. -/
def report (prog : UnorderedProgram) (passes : List Pass := [Ordering.pass])
    (print : Bool := false) : IO Unit := do
  match runPasses passes (.unordered prog) with
  | .error e => IO.println e
  | .ok prog =>
    match ToCore.programToCore prog with
    | .error e => IO.println s!"translation error: {e}"
    | .ok p =>
      if print then IO.println (toString (Std.format p))
      IO.println (typeCheckResult p)

end Cortex.HandBuilt

end

end
