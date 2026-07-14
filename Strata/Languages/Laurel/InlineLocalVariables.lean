/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelPass
public import Strata.Languages.Laurel.UnorderedCore
import Strata.Languages.Laurel.LaurelAST
import Strata.Languages.Laurel.MapStmtExpr
import Strata.Languages.Laurel.EliminateIncrDecrAndCompoundAssign
import Strata.Languages.Laurel.TransparencyPass

/-!
## Inline Local Variables Pass

Runs after the transparency pass and operates **only on functions** (the
`$asFunction` copies produced by the transparency pass). Function bodies are
pure expressions and cannot contain local variable declarations once they reach
the Core schema translation. This pass eliminates them by inlining.

For each local variable of the form `var <name> := <expr>`, every reference to
`<name>` that occurs after the declaration is replaced with `<expr>`, and the
declaration itself is dropped. The inlined expression is itself inlined first,
so chains like

```
var a := 1;
var b := a + 1;
```

become `b ↦ 1 + 1`.

Because functions are pure, an inlined variable is never reassigned. Any
assignment to such a `<name>` is therefore a user error and emits a diagnostic.
-/

namespace Strata.Laurel

/-- Substitution from an inlined local variable to the expression it was
    initialized with. A later declaration of the same name simply overwrites the
    earlier binding, so a plain map (no ordering) suffices. -/
private abbrev InlineSubst := Std.HashMap Identifier StmtExprMd

/-- State threaded through the traversal: the substitution in scope, a stack of
    saved substitutions (one entry per block/quantifier scope currently being
    traversed), and the accumulated diagnostics. -/
private structure InlineState where
  /-- The bindings visible at the current point of the traversal. -/
  subst : InlineSubst := {}
  /-- Saved `subst` snapshots, pushed on scope entry and restored on scope exit
      so that bindings introduced inside a block/quantifier do not leak out. -/
  saved : List InlineSubst := []
  /-- Diagnostics accumulated so far. -/
  diags : Array DiagnosticModel := #[]

private abbrev InlineM := StateM InlineState

private def emitDiag (d : DiagnosticModel) : InlineM Unit :=
  modify fun s => { s with diags := s.diags.push d }

/-- Enter a new scope: snapshot `subst` so it can be restored on exit. When
    `shadow` is given, that name's binding is removed for the duration of the
    scope (a quantifier's bound variable shadows any inlined local). -/
private def enterScope (shadow : Option Identifier := none) : InlineM Unit :=
  modify fun s =>
    let subst := match shadow with
      | some name => s.subst.erase name
      | none => s.subst
    { s with saved := s.subst :: s.saved, subst }

/-- Exit the most recently entered scope, discarding any bindings it introduced. -/
private def exitScope : InlineM Unit :=
  modify fun s => match s.saved with
    | top :: rest => { s with subst := top, saved := rest }
    | [] => s

/-- Pre-traversal hook (top-down). Only opens scopes: blocks and quantifiers
    each introduce a (sequential) scope so bindings don't leak out. Everything
    else — including reference substitution — is handled bottom-up in
    `inlinePost`. -/
private def inlinePre (_used : Bool) (e : StmtExprMd) : InlineM (Option (List StmtExprMd)) := do
  match e.val with
  | .Block .. => enterScope; return none
  | .Quantifier _ param _ _ => enterScope (shadow := param.name); return none
  | _ => return none

/-- Post-traversal hook (bottom-up, children already rewritten).
    - A reference to an inlined local is replaced by its (already-inlined)
      initializer. `Var` has no child expressions, so doing this in `post`
      (rather than `pre`) is equivalent and keeps it next to the `Assign` logic.
    - A `var <name> := <expr>` declaration is dropped and its name bound to the
      inlined initializer for the remaining statements of the enclosing block.
    - Assignments to an inlined local are reported.
    - Blocks and quantifiers close their scope here.

    `IncrDecr` (a mutation, equally invalid on an inlined local) is not handled
    here: the `comesAfter eliminateIncrDecrAndCompoundAssignPass` constraint
    guarantees those nodes are already gone by the time this pass runs. -/
private def inlinePost (_used : Bool) (e : StmtExprMd) : InlineM (List StmtExprMd) := do
  let source := e.source
  match e.val with
  | .Var (.Local name) =>
    match (← get).subst.get? name with
    | some replacement => return [replacement]
    | none => return [e]
  | .Block .. | .Quantifier .. => exitScope; return [e]
  | .Assign [⟨.Declare param, _⟩] value =>
    -- A local variable declaration: bind the (already-inlined) initializer for
    -- subsequent statements and remove the declaration itself.
    modify fun s => { s with subst := s.subst.insert param.name value }
    return []
  | .Assign targets _ =>
    -- An assignment to an inlined local is contradictory: report it.
    let subst := (← get).subst
    for t in targets do
      match t.val with
      | .Local name =>
        if subst.contains name then
          emitDiag (diagnosticFromSource (t.source.orElse fun _ => source)
            s!"cannot assign to '{name.text}': it is an inlined local variable")
      | _ => pure ()
    return [e]
  | _ => return [e]

/-- Inline local variables within an expression. The generic
    `mapStmtExprFlattenM` drives the structural recursion (and the deletion of
    `var` declarations); `inlinePre`/`inlinePost` carry only the inlining logic. -/
private def inlineExpr (expr : StmtExprMd) : InlineM StmtExprMd :=
  mapStmtExprFlattenM inlinePre inlinePost (resultUsed := false) expr

public section

/-- Inline local variables in a single function, returning the rewritten
    procedure and any diagnostics. -/
def inlineLocalVariablesInFunction (proc : Procedure) : Procedure × Array DiagnosticModel :=
  let runBody (body : StmtExprMd) : StmtExprMd × Array DiagnosticModel :=
    let (body', st) := (inlineExpr body).run {}
    (body', st.diags)
  match proc.body with
  | .Transparent body =>
    let (body', diags) := runBody body
    ({ proc with body := .Transparent body' }, diags)
  | .Opaque postconds impl modif =>
    match impl with
    | some i =>
      let (i', diags) := runBody i
      ({ proc with body := .Opaque postconds (some i') modif }, diags)
    | none => (proc, #[])
  | _ => (proc, #[])

/-- Inline local variables in every function of an `UnorderedCoreWithLaurelTypes`.
    Only `functions` are transformed; `coreProcedures` are left unchanged. -/
def inlineLocalVariablesInFunctions (uc : UnorderedCoreWithLaurelTypes)
    : UnorderedCoreWithLaurelTypes × List DiagnosticModel :=
  let results := uc.functions.map inlineLocalVariablesInFunction
  let functions' := results.map (·.1)
  let diags := results.flatMap (·.2.toList)
  ({ uc with functions := functions' }, diags)

public def inlineLocalVariablesPass : LaurelPass UnorderedCoreWithLaurelTypes UnorderedCoreWithLaurelTypes where
  name := "InlineLocalVariablesPass"
  documentation := "Inlines local variable declarations of the form `var <name> := <expr>` in function bodies. References to the variable after its declaration are replaced with the initializer expression, and the declaration is removed. Assignments to an inlined variable emit a diagnostic. Operates only on functions, which are pure and cannot carry local variable declarations into Core."
  comesAfter := [
    ⟨ transparencyPass.meta, "Inlining of local variables in functions only makes sense after the transparency pass has created the functions"⟩,
    ⟨ eliminateIncrDecrAndCompoundAssignPass.meta, "IncrDecr is a mutation of a local; once it is eliminated, inlining only needs to reject plain assignments to inlined locals, not increments/decrements"⟩
  ]
  run := fun _ p _ =>
    let (uc, diags) := inlineLocalVariablesInFunctions p
    (uc, diags, {})

end -- public section

end Strata.Laurel
