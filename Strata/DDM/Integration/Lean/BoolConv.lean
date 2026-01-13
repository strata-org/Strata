/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Integration.Lean.OfAstM

public section
namespace Strata

/-- Convert Init.Bool inductive to OperationF -/
def OperationF.ofBool {α} (ann : α) (b : Bool) : OperationF α :=
  if b then
    { ann := ann, name := q`Init.boolTrue, args := #[] }
  else
    { ann := ann, name := q`Init.boolFalse, args := #[] }

/-- Convert OperationF to Init.Bool -/
def Bool.ofAst {α} [Inhabited α] [Repr α] (arg : ArgF α) : OfAstM Bool := do
  match arg with
  | .op op =>
    match op.name with
    | q`Init.boolTrue =>
      if op.args.size ≠ 0 then
        .error s!"boolTrue expects 0 arguments, got {op.args.size}"
      pure true
    | q`Init.boolFalse =>
      if op.args.size ≠ 0 then
        .error s!"boolFalse expects 0 arguments, got {op.args.size}"
      pure false
    | _ =>
      .error s!"Unknown Bool operator: {op.name}"
  | _ => .throwExpected "boolean" arg

end Strata
end
