/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Languages.Core.Program

/-! # The names a generated declaration avoids

Passes that generate lemmas (termination checking, precondition elimination)
name them fresh against `Program.takenNames`: every declaration's names and
the labels of every procedure's checks, which name proof obligations too. The
set is read from the program a pass receives, so it holds the lemmas and checks
earlier passes generated. Precondition elimination also inserts checks into
procedure bodies; it renames them after the pass, apart from the declaration
names and the other labels of their own procedure.
-/

public section

namespace Core

/-- Replace the label and the metadata of each `assert`, `assume` and `cover` of
    a procedure body by what `f` returns for them, at every depth of a
    structured body and in every block of a CFG body, in order. -/
def Procedure.Body.mapCheckLabelsM {M : Type → Type} [Monad M]
    (f : String → Imperative.MetaData Expression → M (String × Imperative.MetaData Expression))
    (body : Procedure.Body) : M Procedure.Body := do
  let g : Command → M Command := fun
    | .cmd (.assert l e md) => do let (l, md) ← f l md; return .cmd (.assert l e md)
    | .cmd (.assume l e md) => do let (l, md) ← f l md; return .cmd (.assume l e md)
    | .cmd (.cover l e md) => do let (l, md) ← f l md; return .cmd (.cover l e md)
    | c => pure c
  match body with
  | .structured ss => return .structured (← Imperative.Block.mapExprM pure g ss)
  | .cfg g' =>
    return .cfg { g' with blocks := ← g'.blocks.mapM fun (l, b) =>
      return (l, { b with cmds := ← b.cmds.mapM g }) }

/-- The labels of a procedure's checks: its contract's `requires` and `ensures`
    clauses, which the procedure check turns into an `assume` and an `assert`
    under the same label; its body's `assert`, `assume` and `cover` commands
    (`Procedure.Body.mapCheckLabelsM`); and the loop invariants of a structured
    body. CFG blocks carry no labelled loop invariants, and a block's transfer
    carries no label. -/
def Decl.checkLabels : Decl → List String
  | .proc q _ =>
    let record (l : String) (md : Imperative.MetaData Expression) :
        StateM (List String) (String × Imperative.MetaData Expression) :=
      modifyGet fun ls => ((l, md), l :: ls)
    let (_, bodyLabels) := (Procedure.Body.mapCheckLabelsM record q.body).run []
    let invariantLabels := match q.body with
      | .structured ss => (Statements.collectAssertIds ss).map (·.label)
      | .cfg _ => []
    q.spec.preconditions.map (·.1) ++ q.spec.postconditions.map (·.1) ++
      bodyLabels.reverse ++ invariantLabels
  | _ => []

/-- The names a generated lemma avoids: every declaration's names and the
    labels of every procedure's checks in `p`. -/
def Program.takenNames (p : Program) : List String :=
  p.decls.flatMap fun d => d.names.map (·.name) ++ d.checkLabels

end Core

end -- public section
