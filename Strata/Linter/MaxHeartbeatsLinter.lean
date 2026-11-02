/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Linter.Basic
public meta import Lean.Linter.Util

/-!
# The "maxHeartbeats" linter

Raising the heartbeat budget hides slow declarations and lets elaboration time creep up
unnoticed. This linter makes every such override visible and justified. It warns on any
`set_option maxHeartbeats` or `set_option synthInstance.maxHeartbeats` when

* it is *unscoped*, i.e. a plain `set_option maxHeartbeats N` command that stays in effect for
  the rest of the file, or
* it is scoped with `in` but the `in` is not followed by a comment explaining why the larger
  budget is needed.

```lean
set_option maxHeartbeats 400000 in
-- `simp` needs many unfolds of `foo` here; splitting the lemma did not help.
theorem foo : ... := ...
```

Enable with `set_option linter.strata.maxHeartbeats true` (or in `leanOptions`).
-/

meta section

open Lean Elab Command Linter

namespace Strata.Linter

/-- The maxHeartbeats linter requires `maxHeartbeats` overrides to be scoped with `in` and
followed by a comment explaining why they are needed. -/
public register_option linter.strata.maxHeartbeats : Bool := {
  defValue := false
  descr := "enable the maxHeartbeats linter"
}

namespace MaxHeartbeats

/-- A `set_option` of a `maxHeartbeats` option: the syntax to report on, the option name, and
whether it is scoped by `in`, in which case also whether a comment follows the `in`. -/
structure Occurrence where
  ref : Syntax
  name : Name
  /-- The numeric value the option is set to. -/
  value : Nat
  /-- `none` if unscoped, otherwise `some hasComment`. -/
  scopedWithComment : Option Bool

/-- Whether `s` contains a `--` line comment or a `/- -/` block comment with some text in it.
An empty comment (`--` alone, or `/- -/`) does not justify anything. -/
def commentHasText (s : String) : Bool :=
  let nonBlank (t : String) : Bool := !(t.toList.all Char.isWhitespace)
  ((s.splitOn "--").drop 1).any (fun rest => nonBlank (String.ofList (rest.toList.takeWhile (· != '\n')))) ||
  ((s.splitOn "/-").drop 1).any (fun rest => nonBlank ((rest.splitOn "-/").headD ""))

/-- Whether the trailing whitespace of the last token of `stx` contains a non-empty comment. -/
def trailingHasComment (stx : Syntax) : Bool :=
  match stx.getTailInfo with
  | .original _ _ trailing _ => commentHasText trailing.toString
  | _ => false

/-- Whether `stx` is a `set_option ... in ...` node (command, tactic or term form). -/
def isSetOptionIn (stx : Syntax) : Bool :=
  (stx.getKind == ``Lean.Parser.Command.in && stx[0].getKind == ``Lean.Parser.Command.set_option) ||
  stx.getKind == ``Lean.Parser.Tactic.set_option || stx.getKind == ``Lean.Parser.Term.set_option

/-- The `in` token and the body of a `set_option ... in` node. -/
def inAndBody (stx : Syntax) : Syntax × Syntax :=
  if stx.getKind == ``Lean.Parser.Command.in then (stx[1], stx[2])
  else (stx[stx.getNumArgs - 2], stx[stx.getNumArgs - 1])

/-- The first `set_option ... in` node reached from the start of `stx`, if any, so that chained
`set_option a in set_option b in -- why ...` layers can be looked through. -/
partial def leadingSetOptionIn? (stx : Syntax) : Option Syntax :=
  if isSetOptionIn stx then some stx
  else if stx.getNumArgs == 0 then none
  else leadingSetOptionIn? stx[0]

/-- Whether the `set_option ... in` node `stx` is justified: a non-empty comment follows its `in`,
or follows the `in` of a directly chained `set_option ... in`, or the wrapped declaration starts
with a docstring. -/
partial def isJustified (stx : Syntax) : Bool :=
  let (inTok, body) := inAndBody stx
  trailingHasComment inTok ||
  match leadingSetOptionIn? body with
  | some next => isJustified next
  | none =>
    match body.getHead? with
    | some (.atom _ "/--") => true
    | _ => false

/-- Whether `name` is `maxHeartbeats` or `synthInstance.maxHeartbeats`, the only heartbeat
options registered by Lean core. -/
def isMaxHeartbeats (name : Name) : Bool :=
  name ∈ [`maxHeartbeats, `synthInstance.maxHeartbeats]

/-- The option name of a `set_option name val ...` node (command, tactic or term). -/
def optionName? (stx : Syntax) : Option Name :=
  if stx[1].isIdent then some stx[1].getId else none

/-- Run `k` with the option set by the `set_option` node `setOpt` (`set_option name val`)
applied to the scope, the same way `Lean.Linter.withSetOptionIn` does for the linter's own
traversal: no infotree changes, and errors are ignored since they were reported when the command
was elaborated. -/
def withOptionOf (setOpt : Syntax) (k : CommandElabM α) : CommandElabM α := do
  let opts ← withEnableInfoTree false try
      (·.1) <$> Lean.Elab.elabSetOption setOpt[1] setOpt[3]
    catch _ => getOptions
  withScope ({ · with opts }) k

/-- Collect all `maxHeartbeats` `set_option`s in `stx` for which the linter is enabled. The
options set by enclosing `set_option ... in` wrappers (such as
`set_option linter.strata.maxHeartbeats false in` or `set_option linter.all true in`) are applied
while descending, so `getLinterValue` resolves them exactly as Lean does. -/
partial def collect (stx : Syntax) : CommandElabM (Array Occurrence) := do
  let k := stx.getKind
  -- `ref` is a `set_option name val ...` node (command, tactic or term): `ref[1]` is the name,
  -- `ref[2]` the optional trailing-dot part of it, and `ref[3]` the value. A value that is not
  -- a numeric literal does not elaborate for these `Nat` options, so it is skipped.
  let record (ref : Syntax) (n : Name) (commented : Option Bool) :
      CommandElabM (Array Occurrence) := do
    let some value := ref[3].isNatLit? | return #[]
    if isMaxHeartbeats n && getLinterValue linter.strata.maxHeartbeats (← getLinterOptions) then
      return #[{ ref, name := n, value, scopedWithComment := commented }]
    return #[]
  -- `set_option opt val in body` (command, tactic or term). For the command form the option
  -- node is `stx[0]` and has no `in` of its own; otherwise it is `stx` itself.
  if isSetOptionIn stx then
    let isCmd := k == ``Lean.Parser.Command.in
    let opt := if isCmd then stx[0] else stx
    let (_, body) := inAndBody stx
    let here ← match optionName? opt with
      | some n => record opt n (some (isJustified stx))
      | none => pure #[]
    return here ++ (← withOptionOf opt (collect body))
  -- unscoped `set_option opt val`
  else if k == ``Lean.Parser.Command.set_option then
    match optionName? stx with
    | some n => record stx n none
    | none => return #[]
  else
    stx.getArgs.foldlM (fun acc a => return acc ++ (← collect a)) #[]

/-- Whether the override `o` raises the heartbeat budget above the option's default
(`0` means unlimited). Lowering it, e.g. to make a test fail fast, is not a problem. -/
def raisesBudget (o : Occurrence) : CommandElabM Bool := do
  let v := o.value
  if v == 0 then return true
  let decls ← getOptionDecls
  match decls.find? o.name with
  | some { defValue := .ofNat d, .. } => return v > d
  | _ => return true

/-- The maxHeartbeats linter: see the module docstring. It deliberately does not use
`withSetOptionIn`, which strips the leading `set_option ... in` that this linter inspects.
`collect` instead applies the enclosing `set_option ... in` options itself, so that the linter
can be enabled or disabled inline. -/
def maxHeartbeatsLinter : Linter where run := fun stx => do
  if (← MonadState.get).messages.hasErrors then
    return
  for o in (← collect stx) do
    unless (← raisesBudget o) do continue
    match o.scopedWithComment with
    | none =>
      Linter.logLint linter.strata.maxHeartbeats o.ref
        m!"Unscoped `set_option {o.name}` is not allowed: it affects every later declaration.\n\
          Raising the heartbeat budget usually means the proof is inefficient. Prefer refactoring \
          it so that the default budget suffices. If that is unavoidable, scope the option to \
          the individual definition or theorem that needs it and comment why:\n\
          ```\nset_option {o.name} N in\n-- comment explaining why this is necessary\n\
          theorem ... := ...\n```"
    | some false =>
      Linter.logLint linter.strata.maxHeartbeats o.ref
        m!"`set_option {o.name}` suggests an inefficient proof. Prefer refactoring it so that \
          the default heartbeat budget suffices. If that is unavoidable, add a comment right \
          after `in` explaining why the larger budget is necessary."
    | some true => pure ()

initialize addLinter maxHeartbeatsLinter

end MaxHeartbeats

end Strata.Linter
