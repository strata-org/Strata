/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Integration.Lean.OfAstM

public section
namespace Strata

/-- Convert Init.Bool inductive to OperationF -/
def Bool.toAst {α} [Inhabited α] (v : Ann Bool α) : OperationF α :=
  if v.val then
    ⟨v.ann, q`Init.boolTrue, #[]⟩
  else
    ⟨v.ann, q`Init.boolFalse, #[]⟩

/-- Convert OperationF to Init.Bool -/
def Bool.ofAst {α} [Inhabited α] [Repr α] (op : OperationF α) : OfAstM (Ann Bool α) :=
  match op.name with
  | q`Init.boolTrue =>
    if op.args.size = 0 then
      pure ⟨op.ann, true⟩
    else
      .error s!"boolTrue expects 0 arguments, got {op.args.size}"
  | q`Init.boolFalse =>
    if op.args.size = 0 then
      pure ⟨op.ann, false⟩
    else
      .error s!"boolFalse expects 0 arguments, got {op.args.size}"
  | _ =>
    .error s!"Unknown Bool operator: {op.name}"

end Strata
end
