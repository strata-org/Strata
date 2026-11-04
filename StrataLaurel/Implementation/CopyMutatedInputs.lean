/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.LaurelAST
public import StrataLaurel.Implementation.LaurelPass
import StrataLaurel.Implementation.MapStmtExpr

/-!
# Copy Mutated Inputs

Laurel permits a procedure body to assign to its input parameters (the Laurel
interpreter executes such programs), but Core does not: Core's
`checkModificationRights` allows writes only to outputs and body-declared
locals, so a body write to an input fails Core type checking — and a pipeline
type-check failure aborts the whole program, not just the offending procedure.

This pass closes that gap. For every input parameter `x` that the body assigns
to (and that is not also an output, i.e. not an inout), it declares a fresh
mutable local initialized from the input and redirects the body to it:

```
procedure f(x: int) returns ($result: int) {   procedure f(x: int) returns ($result: int) {
  x := x + 1;                            ==>     var $mutable_x: int := x;
  $result := x;                                  $mutable_x := $mutable_x + 1;
}                                                $result := $mutable_x;
                                               }
```

`$mutable_x` is fresh without a counter: a procedure's input names are
distinct, a user name cannot start with `$`, and no other pass makes a
`$mutable_` name.

The copy is inserted at the top of the body, before any statement runs, so it
always holds the input's entry value when later statements first read it.

## What is (and is not) substituted

* **Body references** of a mutated input — reads and assignment targets — are
  renamed to the copy, including inside loop invariants and body
  assertions (which observe the current value, matching interpreter behavior).
* **`old(...)` subtrees** are left untouched: `old` denotes the procedure's
  entry state, where the original (now immutable) input holds exactly the
  entry value. Substituting there would instead read the copy at entry, where
  it is not yet assigned. The same applies to the coroutine two-state forms
  `OldRelies`/`OldGuarantee`.
* **Specifications** (preconditions, postconditions, `modifies`, `decreases`)
  are left untouched: they keep referring to the input, which after this pass
  always holds the entry value. For preconditions and `decreases` that is the
  only sensible meaning. For a postcondition or `modifies` clause this fixes
  the meaning of a bare `x` to the ENTRY value of `x`; a hand-written Laurel
  program that wants the exit value must bind it to a local or an output
  itself. (The Java frontend produces exactly this shape — it lowers
  `postcondition(x == 1)` over a body doing `x = 2` to `ensures x == 1` — and
  the entry reading is the one it needs.)
* **Coroutine `relies`/`guarantees` that mention a reassigned input are
  REJECTED** with a diagnostic rather than substituted: the yield lowering
  inlines those clauses into the body (entry-valued original input), while the
  caller path promotes inputs to mutable `self#` fields (current value), so no
  single substitution choice keeps the two paths consistent. Supporting this
  combination means substituting on the body path only; until then it is an
  error. Body `oldGuarantee(...)`/`oldRelies(...)` over a reassigned input are
  rejected for the same reason: they denote the start-of-step value, which the
  entry-frozen original input cannot provide (see `oldStepRefs`).

## Placement in the pipeline

Runs after `EliminateIncrDecrAndCompoundAssign`, so a parameter write is always
a plain `Assign` (`IncrDecr` and `CompoundAssign` are declared `unsupported`
below, which the pipeline ordering check enforces). Nothing else constrains the
position: the inout parameters that later passes introduce (`$heap`, promoted
globals) are inouts from the moment they appear, so the inout rule skips them
wherever this pass runs.

The pass `removes` the obligation kind `Pseudo.mutatedInput`, which
`LaurelToCoreSchemaPass` declares `unsupported`, so a phase order that leaves
this pass out is refused instead of failing Core's type check.

Matching is by resolution `uniqueId`, never by name, so a binder or nested
declaration that shadows a parameter cannot be miscaptured.
-/

namespace Strata.Laurel

namespace CopyMutatedInputs

/-- The diagnostics the pass reports. -/
private structure CopyState where
  diagnostics : List Message := []

private abbrev CopyM := StateM CopyState

/-- The copy's name, `$mutable_<param>`: fresh because input names are distinct,
    a user name cannot start with `$`, and no other pass makes a `$mutable_` name. -/
private def copyName (base : String) : String := s!"$mutable_{base}"

private def addDiagnostic (m : Message) : CopyM Unit :=
  modify fun s => { s with diagnostics := s.diagnostics ++ [m] }

/-- The `(uniqueId, source)` of every `.Local` reference inside `e`. -/
private def localRefs (e : StmtExprMd) : List (Nat × FileRange) :=
  collectStmtExprList (fun n =>
    match n.val with
    | .Var (.Local name) =>
      match name.uniqueId with
      | some uid => [(uid, n.source)]
      | none => []
    | _ => []) e

/-- References to the given inputs under a body `oldGuarantee(...)`/
    `oldRelies(...)`. Those forms promise the value at the start of the current
    coroutine step — after a reassignment in an earlier step, the reassigned
    value. The substitution skips `Old*` subtrees, so the reference would stay
    on the original input, frozen at its ENTRY value; such programs are
    rejected rather than silently given the wrong state. -/
private def oldStepRefs (mutatedIds : Std.HashSet Nat) (body : StmtExprMd) :
    List (Nat × FileRange) :=
  collectStmtExprList (fun n =>
    match n.val with
    | .OldRelies inner | .OldGuarantee inner =>
      (localRefs inner).filter fun (uid, _) => mutatedIds.contains uid
    | _ => []) body

/-- Rename every body reference of the mutated inputs — variable reads and
    assignment targets — to their copies, skipping `old(...)` subtrees (and the
    coroutine `OldRelies`/`OldGuarantee` forms), which denote earlier states
    where the original input is the correct carrier of the value. -/
private def substitute (ren : Std.HashMap Nat Identifier) (body : StmtExprMd) : StmtExprMd :=
  let renamed (name : Identifier) : Option Identifier := do
    let fresh ← ren.get? (← name.uniqueId)
    pure { fresh with source := name.source }
  mapStmtExprPrePostM (m := Id)
    (fun n => match n.val with
      | .Old .. | .OldRelies .. | .OldGuarantee .. => pure (some n)
      | _ => pure none)
    (fun n => match n.val with
      | .Var (.Local name) =>
        match renamed name with
        | some fresh => pure { n with val := .Var (.Local fresh) }
        | none => pure n
      | .Assign targets value =>
        let targets' := targets.map fun t =>
          match t.val with
          | .Local name =>
            match renamed name with
            | some fresh => { t with val := Variable.Local fresh }
            | none => t
          | _ => t
        pure { n with val := .Assign targets' value }
      | _ => pure n)
    body

/-- Legalize one procedure: no-op unless the body assigns to an input that is
    not also an output. -/
private def transformProc (proc : Procedure) : CopyM Procedure := do
  let body? : Option StmtExprMd := match proc.body with
    | .Transparent b => some b
    | .Opaque _ (some impl) _ => some impl
    | _ => none
  let some body := body? | return proc
  -- `assignedLocalIds` also recognizes `x++` and `x += e`; after
  -- `EliminateIncrDecrAndCompoundAssign` only plain assignments remain.
  let written := assignedLocalIds body
  if written.isEmpty then return proc
  -- An input that is also an output is an inout: `resolveOutputParameters`
  -- binds the output to the input's binding, so the two share a `uniqueId`.
  -- Writes to it are already legal in Core, and copying it would disconnect the
  -- write from the output.
  let outputIds : Std.HashSet Nat := proc.outputs.foldl (fun acc o =>
    match o.name.uniqueId with
    | some uid => acc.insert uid
    | none => acc) {}
  let mutated := proc.inputs.filter fun p =>
    match p.name.uniqueId with
    | some uid => written.contains uid && !outputIds.contains uid
    | none => false
  if mutated.isEmpty then return proc
  -- `relies`/`guarantees` mentioning a reassigned input are rejected; the
  -- module header explains why.
  let mutatedIds : Std.HashSet Nat := mutated.foldl (fun acc p =>
    match p.name.uniqueId with
    | some uid => acc.insert uid
    | none => acc) {}
  let clauses := proc.contracts.relies ++ proc.contracts.guarantees
  let clauseOffenders := clauses.flatMap fun c =>
    (localRefs c.condition).filter fun (uid, _) => mutatedIds.contains uid
  let stepOffenders := oldStepRefs mutatedIds body
  if !clauseOffenders.isEmpty || !stepOffenders.isEmpty then
    let nameOf (uid : Nat) : String :=
      (mutated.find? (·.name.uniqueId == some uid)).map (·.name.text) |>.getD "?"
    for (uid, src) in clauseOffenders do
      addDiagnostic <| Message.withRange src
        s!"a coroutine's relies/guarantees cannot YET refer to input parameter \
           '{nameOf uid}', which the body reassigns; copy the input into a local and \
           reassign that instead"
    for (uid, src) in stepOffenders do
      addDiagnostic <| Message.withRange src
        s!"`oldGuarantee(...)`/`oldRelies(...)` cannot YET refer to input parameter \
           '{nameOf uid}', which the body reassigns; copy the input into a local and \
           reassign that instead"
    return proc
  let mut ren : Std.HashMap Nat Identifier := {}
  let mut decls : List StmtExprMd := []
  for p in mutated do
    if let some uid := p.name.uniqueId then
      let src := p.name.source
      let freshId : Identifier := { text := copyName p.name.text, source := src }
      ren := ren.insert uid freshId
      decls := decls ++
        [⟨.Assign [⟨.Declare { name := freshId, type := some p.type }, src⟩]
          ⟨.Var (.Local p.name), src⟩, src⟩]
  let newBody := prependStmts decls (substitute ren body)
  let body := match proc.body with
    | .Opaque posts _ mods => Body.Opaque posts (some newBody) mods
    | _ => Body.Transparent newBody
  return { proc with body }

end CopyMutatedInputs

public section

/-- Copy every mutated input into a fresh mutable local (see the module header). -/
def copyMutatedInputs (program : Program) : Program × List Message :=
  let (program, state) := mapProgramProceduresM CopyMutatedInputs.transformProc program |>.run {}
  (program, state.diagnostics)

/-- Pipeline pass: legalize body writes to input parameters for Core, which
    only lets a procedure write its outputs and body-declared locals. -/
public def copyMutatedInputsPass : LaurelPass where
  name := "CopyMutatedInputs"
  creates := [
      NodeKind.StmtExpr.Assign,
      NodeKind.StmtExpr.Var,
      NodeKind.StmtExpr.Block
    ]
  removes := [NodeKind.Pseudo.mutatedInput]
  unsupported := [NodeKind.StmtExpr.IncrDecr, NodeKind.StmtExpr.CompoundAssign]
  needsResolves := true
  documentation := "Rewrites a body that assigns to an input parameter (legal Laurel, illegal in Core) to assign to a fresh `$mutable_…` local initialized from the input, renaming the body's references (but not `old(...)` subtrees or the procedure's specifications, which keep the entry-value reading). Inout inputs — also present in the outputs — are left alone, and a coroutine whose relies/guarantees — or body `oldGuarantee`/`oldRelies` — mention a reassigned input is rejected (the body and caller lowerings would read different states). Runs after `EliminateIncrDecrAndCompoundAssign` so every write is a plain `Assign`."
  run := fun _ p _m => let (p, diags) := copyMutatedInputs p; (p, diags, {})

end -- public section
end Strata.Laurel
