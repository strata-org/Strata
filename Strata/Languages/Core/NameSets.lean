/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Languages.Core.Program

/-! # The names a generated name avoids

A pass that generates a name picks it fresh against the names of the program it receives, so the
set holds what earlier passes generated too. Which set depends on what the pass generates:

- `Program.declaredNames`: a declaration (an opaque type, a closed lemma's type). The names of
  the declarations, the types procedure bodies declare, and the datatypes' type parameters.
- `Program.takenNames`: a lemma (termination checking, precondition elimination). The names of
  `Program.declaredNames` and the labels of every procedure's checks, which name proof obligations
  too. Precondition elimination also inserts checks into procedure bodies; it renames them after
  the pass, apart from the declaration names and the other labels of their own procedure.
- `Program.varNames`: a variable (call elimination's temporaries). Every procedure's parameters
  and the variables its body initializes. It holds no declaration names; call elimination adds
  them as a precaution. Bound variables need no entry, since expressions refer to them by de
  Bruijn index and a substitution cannot capture them.
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

/-- The type parameters of the program's datatypes. The SMT encoder declares a datatype with
    its parameters bound by name (`par`), so a sort a pass generates must not reuse one. -/
def Program.dataTypeParams (p : Program) : List String :=
  p.decls.flatMap fun
    | .type (.data block) _ => block.flatMap (·.typeArgs)
    | _ => []

/-- The names `p` declares: the names of its declarations, the types its procedure bodies
    declare, and its datatypes' type parameters. Types, functions, axioms, lemmas and procedures share one
    namespace of declaration names, so a pass that names a new declaration with a prefix
    avoids every one of these names with that prefix, not only the type names. -/
def Program.declaredNames (p : Program) : List String :=
  p.getNames.map (·.name) ++ (p.typeNames ++ p.dataTypeParams)

/-- The names of the variables a procedure declares: its input and output parameters, and the
    variables its body initializes, at any nesting depth of a structured body or in any block of
    a CFG body. A pass that adds variables to the procedure must avoid them. -/
def Procedure.varNames (p : Procedure) : List String :=
  let locals := match p.body with
    | .structured ss => Imperative.Block.definedVars ss false
    | .cfg g => g.blocks.flatMap fun (_, b) => b.cmds.flatMap Command.definedVars
  (p.header.inputs.keys ++ p.header.outputs.keys ++ locals).map (·.name)

/-- The names of the variables the program's procedures declare (`Procedure.varNames`). -/
def Program.varNames (p : Program) : Std.HashSet String :=
  Std.HashSet.ofList <| p.decls.flatMap fun
    | .proc proc _ => proc.varNames
    | _ => []

/-- The names a generated lemma avoids: the names `p` declares (`Program.declaredNames`) and the
    labels of every procedure's checks in `p`. -/
def Program.takenNames (p : Program) : List String :=
  p.declaredNames ++ p.decls.flatMap Decl.checkLabels

end Core

end -- public section
