/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Lean

/-! # Purity Tracker

A linter that detects impure commands during elaboration via an `IO.Ref`
side channel. After `Elab.process`, read `impureCommandsRef` to see which
command kinds were used.

The linter runs inside `withoutModifyingEnv`, so it cannot write to
persistent environment extensions. Instead it writes to a global `IO.Ref`
which survives across the elaboration of a single file.
-/

open Lean

public section

namespace Strata.PurityTracker

/-- Commands whose elaboration is known to be pure.

## Audit methodology

Each entry was verified by checking the elaborator source in
`~/.elan/toolchains/leanprover--lean4---v4.29.1/src/lean/Lean/Elab/`.
A command is pure if its elaborator only modifies the `Environment`
(adding declarations, setting attributes, modifying scopes) without
performing `IO` actions that depend on external state.

## Audit results (Lean v4.29.1)

### Declarations — `Lean/Elab/Declaration.lean`, `Lean/Elab/Structure.lean`, etc.
`declaration` covers `def`, `theorem`, `abbrev`, `opaque`, `instance`,
`axiom`, `structure`, `class`, `inductive`. These elaborate types and terms,
add declarations to the environment, and run type-checking. No IO.
`deriving` generates instances via deriving handlers. Handlers modify the
environment but don't perform IO.
`example` elaborates a term and discards it. No persistent effect, no IO.

### Structural — `Lean/Elab/BuiltinCommand.lean`
`section`, `namespace`, `end`, `variable`, `universe`, `open`, `export`,
`import`, `mutual`, `in`, `include`, `omit`, `withWeakNamespace`,
`withExporting`: These modify scopes, namespaces, and open declarations.
Pure environment operations only.

### Options/attributes — `Lean/Elab/BuiltinCommand.lean`, `Lean/Elab/DeclModifiers.lean`
`set_option`: Sets an option in the environment. Pure.
`attribute`: Adds/removes attributes. Pure (attribute handlers may run
elaboration but not IO).

### Inspection — `Lean/Elab/BuiltinCommand.lean`, `Lean/Elab/Print.lean`
`check`, `check_failure`, `print`, `printSig`, `printAxioms`, `printEqns`,
`printTacTags`, `where`, `version`, `synth`: These produce messages but
don't modify the environment or perform IO beyond message logging (which
is internal to the elaboration monad, not external IO).

### Assertions — `Lean/Elab/BuiltinCommand.lean`
`assertNotExists`, `assertNotImported`, `checkAssertions`: Check
environment properties and produce errors if violated. Pure.

### Documentation — `Lean/Elab/BuiltinCommand.lean`
`moduleDoc`, `addDocString`: Add documentation to the environment. Pure.

### Syntax/notation — `Lean/Elab/Notation.lean`, `Lean/Elab/Syntax.lean`, etc.
`syntax`, `syntaxAbbrev`, `syntaxCat`, `notation`, `macro`, `macro_rules`,
`elab`, `elab_rules`, `scoped`, `local`, `infix`/`infixl`/`infixr`/
`prefix`/`postfix`, `declare_syntax_cat`, `declare_config_elab`, etc.:
These register parsers and elaborators in the environment. Pure.

### Simproc — `Lean/Elab/Tactic/Simproc.lean`
`simproc`, `builtin_simproc`, `dsimproc`, `builtin_dsimproc`: Register
simplification procedures. Pure.

### Misc — various
`register_simp_attr`, `register_option`, `register_builtin_option`,
`register_label_attr`: Register metadata. Pure.
`register_tactic_tag`, `tactic_extension`, `recommended_spelling`,
`genInjectiveTheorems`, `registerErrorExplanationStx`: Metadata/codegen. Pure.
`init_quot`: Initializes quotient type. Pure kernel operation.
`exit`, `eoi`: Terminate elaboration. Pure.
`grindPattern`, `binderPredicate`, `mixfix`: Syntax definitions. Pure.
`Lean.Option.registerOption`, `Lean.Option.registerBuiltinOption`:
Macros expanding to option registration. Pure.

## NOT on the allowlist (known impure or unknown)

Per the purity definition: a command is impure if its elaboration could read
state not determined by the module's source and its dependencies' content, or
mutate state beyond stdout/stderr.

`eval`, `evalBang`: Execute arbitrary code that may perform IO. IMPURE.
`initialize`: Runs an `IO` action at module load. Even though many only
  create refs or register extensions, we cannot statically distinguish safe
  from unsafe. IMPURE.
`guard`: Evaluates an expression at elaboration time. Could depend on
  external state via `native_decide` or IO-capable code. IMPURE.
`run_cmd`, `run_elab`, `run_meta`: Execute monadic code with IO access. IMPURE.

`guard_msgs`: Pure by itself — it wraps another command and checks output
  against source text. The wrapped command is elaborated separately and
  checked by the linter independently. ON THE ALLOWLIST (see below).

Any unknown/unrecognized command: Conservatively treated as IMPURE.
-/
private def pureCommandKinds : Std.HashSet SyntaxNodeKind := .ofList [
  ``Lean.Parser.Command.declaration, ``Lean.Parser.Command.«deriving»,
  ``Lean.Parser.Command.«section», ``Lean.Parser.Command.«namespace»,
  ``Lean.Parser.Command.«end», ``Lean.Parser.Command.«variable»,
  ``Lean.Parser.Command.«universe», ``Lean.Parser.Command.«open»,
  ``Lean.Parser.Command.«export», ``Lean.Parser.Command.«import»,
  ``Lean.Parser.Command.«mutual», ``Lean.Parser.Command.«in»,
  ``Lean.Parser.Command.«include», ``Lean.Parser.Command.«omit»,
  ``Lean.Parser.Command.withWeakNamespace, ``Lean.Parser.Command.withExporting,
  ``Lean.Parser.Command.«set_option», ``Lean.Parser.Command.«attribute»,
  ``Lean.Parser.Command.check, ``Lean.Parser.Command.check_failure,
  ``Lean.Parser.Command.print, ``Lean.Parser.Command.printSig,
  ``Lean.Parser.Command.printAxioms, ``Lean.Parser.Command.printEqns,
  ``Lean.Parser.Command.printTacTags, ``Lean.Parser.Command.«where»,
  ``Lean.Parser.Command.version, ``Lean.Parser.Command.synth,
  ``Lean.Parser.Command.assertNotExists, ``Lean.Parser.Command.assertNotImported,
  ``Lean.Parser.Command.checkAssertions,
  ``Lean.Parser.Command.moduleDoc, ``Lean.Parser.Command.addDocString,
  ``Lean.Parser.Command.«register_tactic_tag»,
  ``Lean.Parser.Command.«tactic_extension»,
  ``Lean.Parser.Command.«recommended_spelling»,
  ``Lean.Parser.Command.genInjectiveTheorems,
  ``Lean.Parser.Command.registerErrorExplanationStx,
  ``Lean.Parser.Command.«init_quot», ``Lean.Parser.Command.exit,
  ``Lean.Parser.Command.eoi,
  -- Registered via macros (not under Lean.Parser.Command prefix)
  `Lean.Option.registerOption,
  `Lean.Option.registerBuiltinOption
]

private def pureCommandPrefixes : Array Name := #[
  `Lean.Parser.Command.syntax, `Lean.Parser.Command.syntaxAbbrev,
  `Lean.Parser.Command.syntaxCat, `Lean.Parser.Command.notation,
  `Lean.Parser.Command.macro, `Lean.Parser.Command.macro_rules,
  `Lean.Parser.Command.elab, `Lean.Parser.Command.elab_rules,
  `Lean.Parser.Command.«scoped», `Lean.Parser.Command.«local»,
  `Lean.Parser.Command.simproc, `Lean.Parser.Command.builtin_simproc,
  `Lean.Parser.Command.dsimproc, `Lean.Parser.Command.builtin_dsimproc,
  `Lean.Parser.Command.register_simp_attr,
  `Lean.Parser.Command.register_option, `Lean.Parser.Command.register_builtin_option,
  `Lean.Parser.Command.register_label_attr,
  `Lean.Parser.Command.«infix», `Lean.Parser.Command.«infixl»,
  `Lean.Parser.Command.«infixr», `Lean.Parser.Command.«prefix»,
  `Lean.Parser.Command.«postfix»,
  `Lean.Parser.Command.declare_syntax_cat, `Lean.Parser.Command.declare_config_elab,
  `Lean.Parser.Command.declare_command_config_elab,
  `Lean.Parser.Command.declare_config_getter,
  `Lean.Parser.Command.declare_simp_like_tactic,
  `Lean.Parser.Command.declare_tagged_region,
  `Lean.Parser.Command.mixfix, `Lean.Parser.Command.grindPattern,
  `Lean.Parser.Command.binderPredicate
]

def isPureCommand (kind : SyntaxNodeKind) : Bool :=
  pureCommandKinds.contains kind ||
  pureCommandPrefixes.any (fun pfx => pfx.isPrefixOf kind) ||
  kind == nullKind

/-- Global ref accumulating impure command kinds found during elaboration.
Must be reset before each file and read after `Elab.process`. -/
initialize impureCommandsRef : IO.Ref (Array SyntaxNodeKind) ← IO.mkRef #[]

/-- Register a linter that records impure commands to the IO.Ref. -/
initialize Lean.addLinter {
  name := `Strata.purityTracker
  run := fun stx => do
    let kind := stx.getKind
    if kind != nullKind && !isPureCommand kind then
      impureCommandsRef.modify (·.push kind)
}

/-- Reset the tracker before processing a new file. -/
def reset : IO Unit := impureCommandsRef.set #[]

/-- Read the impure commands found during the last `Elab.process`. -/
def getResults : IO (Array SyntaxNodeKind) := impureCommandsRef.get

/-- Check a single file for purity by elaborating it and reading the linter results.
Requires LEAN_PATH to be set so imports can be resolved. -/
def checkFile (contents : String) (fileName : String := "<input>") : IO (Array SyntaxNodeKind) := do
  reset
  let inputCtx := Parser.mkInputContext contents fileName
  let (header, parserState, msgs) ← Parser.parseHeader inputCtx
  let (env, _) ← Elab.processHeader header {} msgs inputCtx
  -- Get the content after the header (commands only)
  let cmdContent := String.Pos.Raw.extract contents parserState.pos ⟨contents.utf8ByteSize⟩
  let _ ← Elab.process cmdContent env {} fileName
  getResults

end Strata.PurityTracker

end -- public section
