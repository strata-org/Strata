/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.AbstractionMarkers
public import Strata.Transform.CoreTransform

/-! # Reservation of the marker prefixes

Each abstraction phase reads every assumption of an obligation's path condition whose label starts
with its marker prefix (`Core.abstractionMarkerPrefixes`) as one of its markers. The marker
prefixes lie in the `$__` namespace, reserved for generated names. So that only the assumptions a
phase generates carry its prefix, the phase rejects a program that already has a label with it
(`rejectMarkerLabels`). -/

namespace Core

public section

/-- The label of `c` if `c` is an `assert`, an `assume` or a `cover` whose label starts with
    `pfx`. -/
def Command.labelWithPrefix? (pfx : String) : Command → Option String
  | .cmd (.assert l _ _) | .cmd (.assume l _ _) | .cmd (.cover l _ _) =>
    if l.startsWith pfx then some l else none
  | _ => none

mutual
/-- The first label in `s` that starts with `pfx`: the label of a block, a loop invariant, an
    `assert`, an `assume` or a `cover`, in program order. -/
def Statement.labelWithPrefix? (pfx : String) : Statement → Option String
  | .cmd c => Command.labelWithPrefix? pfx c
  | .exit _ _ | .typeDecl _ _ => none
  | .block l ss _ => if l.startsWith pfx then some l else Statements.labelWithPrefix? pfx ss
  | .ite _ tss ess _ =>
    (Statements.labelWithPrefix? pfx tss).or (Statements.labelWithPrefix? pfx ess)
  | .loop _ _ invs ss _ =>
    ((invs.find? (·.1.startsWith pfx)).map (·.1)).or (Statements.labelWithPrefix? pfx ss)

/-- The first label in `ss` that starts with `pfx` (`Statement.labelWithPrefix?`). -/
def Statements.labelWithPrefix? (pfx : String) : List Statement → Option String
  | [] => none
  | s :: ss => (Statement.labelWithPrefix? pfx s).or (Statements.labelWithPrefix? pfx ss)
end

/-- The first label of `p` that starts with `pfx`: the name of an axiom or a lemma, the label of
    a precondition or a postcondition, a label in a structured procedure body
    (`Statement.labelWithPrefix?`), or the label of a command in a block of a CFG body
    (`Command.labelWithPrefix?`). -/
def Program.labelWithPrefix? (pfx : String) (p : Program) : Option String :=
  p.decls.findSome? fun
    | .ax a _ => if a.name.startsWith pfx then some a.name else none
    | .lemma l _ => if l.name.startsWith pfx then some l.name else none
    | .proc d _ =>
      ((d.spec.preconditions.keys ++ d.spec.postconditions.keys).find? (·.startsWith pfx)).or
        (match d.body with
          | .structured ss _ => Statements.labelWithPrefix? pfx ss
          | .cfg g _ => g.blocks.findSome? fun (_, b) => b.cmds.findSome? (Command.labelWithPrefix?
              pfx)
          | .abstract => none)
    | _ => none

/-- Fails on a program with a label that starts with `pfx`, the label prefix of the marker
    assumptions of the abstraction phase `phase` (see `Core.abstractionMarkerPrefixes`). The
    phase's model check reads every assumption whose label has that prefix as one of its
    markers, so the prefix is reserved for the assumptions the phase generates: a written
    label with it would turn a real failure after it into `unknown`. Every marker prefix starts
    with `$__`, a namespace reserved for names that Strata generates: the parser accepts
    identifiers in it, but a program that uses a marker prefix there, including through a
    default label derived from a procedure name such as `$__callElimAssume_p_ensures_0`, is
    rejected. -/
def rejectMarkerLabels (phase pfx : String) (p : Program) : Transform.CoreTransformM Unit :=
  match Program.labelWithPrefix? pfx p with
  | some l => throw (Strata.Message.fromFormat
      f!"❌ The label \"{l}\" starts with \"{pfx}\", which {phase} reserves for its markers.")
  | none => pure ()

end -- public section

end Core
