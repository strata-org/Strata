/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.AST
public import Strata.Languages.Laurel.LaurelAST
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import StrataDDM.Integration.Lean.HashCommands -- shake: keep

namespace Strata.Laurel

public section

/--
The synthetic backing type for `Array<T>`, expressed in Laurel source (like
`HeapParameterizationConstants`) rather than built as a Lean AST value, so the
definition reads as ordinary Laurel.

`SubscriptElim`/`ArrayElim` injects this composite into a program (when
`Array<T>` is used) and lowers array operations onto its single mutable `$data`
field: `a[i]` → `Sequence.select(a#$data, i)`,
`a[i] := v` → `a#$data := Sequence.update(...)`,
`Array.length(a)` → `Sequence.length(a#$data)`.

The composite name and field name must match `arrayCompositeName` and
`arrayDataField` (the constants the rest of the pass uses to read/write the
field); the `initialize` check below enforces this at module-load time. The
element type is hardcoded as `int`: `Array<T>` with `T ≠ int` is rejected during
resolution, so every program reaching the pass uses only `Array<int>`.
-/
private def arrayCompositeDDM :=
#strata
program Laurel;
composite $Array {
  var $data: Seq<int>
}
#end

/-- The synthetic `$Array` composite, parsed from `arrayCompositeDDM`.
    Mirrors `HeapParameterizationConstants.heapConstants` / `coreDefinitionsForLaurel`:
    a parse failure is a bug in the source literal above, reported via `dbg_trace`.
    The structural invariants (name/field/mutability matching the constants) are
    checked at module load by the `initialize` block below. -/
def arrayComposite : TypeDefinition :=
  match Laurel.TransM.run none (Laurel.parseProgram arrayCompositeDDM) with
  | .ok program =>
    match program.types with
    | [td] => td
    | _ => dbg_trace s!"BUG: $Array prelude has unexpected type count"; default
  | .error e => dbg_trace s!"BUG: $Array prelude parse error: {e}"; default

/-- Whether `arrayComposite` is a `Composite` named `arrayCompositeName` with a
    single mutable field named `arrayDataField` — the shape the pass relies on
    when it reads/writes `a#$data`. Returns an error message on mismatch. -/
private def arrayCompositeError : Option String :=
  match arrayComposite with
  | .Composite ct =>
    if ct.name.text != arrayCompositeName then
      some s!"composite is named '{ct.name.text}', expected '{arrayCompositeName}'"
    else match ct.fields with
      | [f] =>
        if f.name.text != arrayDataField then
          some s!"field is named '{f.name.text}', expected '{arrayDataField}'"
        else if !f.isMutable then
          some s!"field '{arrayDataField}' must be mutable"
        else none
      | fs => some s!"has {fs.length} fields, expected exactly 1 ('{arrayDataField}')"
  | _ => some "did not parse to a Composite"

-- Enforce at module-load time that the `$Array` Laurel source above stays in
-- sync with the `arrayCompositeName` / `arrayDataField` constants the pass uses.
-- (`initialize` rather than `#guard`, which needs interpreter IR unavailable in
-- `module` files — same reason as `LaurelCompilationPipeline`'s ordering check.)
initialize do
  if let some err := arrayCompositeError then
    throw <| .userError s!"SubscriptElimConstants: synthetic $Array composite {err}"

end -- public section

end Strata.Laurel
