/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-!
# Laurel Node Kinds

`NodeKind` is the vocabulary each Laurel pass uses to declare what it
`creates`, `requires`, `removes`, and lists as `unsupported` (see
`StrataLaurel.Implementation.LaurelPass`). The pipeline's ordering constraints are
*derived* from those declarations rather than written by hand; see
`LaurelCompilationPipeline.orderingFailures`.

## Naming

A name is one of two shapes.

An **AST constructor**, qualified by its inductive: `StmtExpr.Throw`,
`TypeDefinition.Composite`. The shape occurs exactly when the program contains
that constructor.

A **field constraint**, a path `Owner.field.Leaf`:

* `Owner` is the constructor or structure that owns the field,
* `field` is the field or constructor-argument name,
* `Leaf` is the constructor of the value sitting in that field — `cons`/`nil`
  for lists, `some`/`none` for options, `true`/`false` for `Bool`, or a named
  constructor.

So `StmtExpr.While.postTest.true` is a `while` whose `postTest` is `true`, and
paths nest: `StmtExpr.Old.value.Var.Local`.

Qualifying by owner is required in both shapes, not cosmetic: `typeArgs` occurs
on five structures (`Procedure`, `CompositeType`, `DatatypeDefinition`,
`TypeAlias`, `OpaqueTypeDefinition`), `postconditions` on three, and `value` on
many.

Every name denotes a property of the **whole program**: the shape occurs if it
occurs anywhere — any declaration, initializer, constraint or contract — not
merely in procedure bodies. So a pass declaring `removes X` claims X is gone
everywhere, and a pass whose traversal reaches only part of the program does not
satisfy that claim. This is the reading the per-pass proofs will use.

Write either kind fully qualified: `NodeKind.StmtExpr.Throw`. Two things force that.
Lean's `.foo` shorthand does not accept a hierarchical name ("must be atomic"),
and `open NodeKind` at file scope makes `StmtExpr.Throw` ambiguous with the real
`StmtExpr.Throw` constructor. An `open NodeKind in` on a single declaration is
safe if the surrounding code needs no bare AST constructors.

## `Pseudo.*`

Everything under `Pseudo` is *not* a Laurel AST constructor. Most could still
carry a predicate over a program the way Core's `ProgramFact.holds` does —
`overload` is a relation over declarations, `heapVar` is a name lookup — but
none carries one yet, so today they are taken on trust. A few never can:
`generatedReturn` is byte-identical to any other `Return`, and `core` names a
representation rather than a property of a Laurel program. Four reasons a name
lands there:

* **position-dependent** — `statementExpression` and `letExpr` depend on the
  path from the root, not on any one field;
* **a relation over several declarations** — `overload` (two static procedures
  sharing a name), `coroutineOverride`;
* **a generated name rather than AST structure** — `heapVar` (`$heap`), `box`,
  `totalMap`, `typeTag`, `asFunctionTwin`;
* **provenance only** — `generatedReturn` is byte-identical to any other
  `Return`; `oldExpr` is the *complement* of `Old.value.Var.Local`, and
  enumerating the other constructors is impractical.

The rest of the vocabulary is decidable from a program, so keeping the split
visible in the name tells a reader at a glance which declarations could be
machine-checked and which are taken on trust.

`Pseudo` is a staging area, not a permanent category: the intent is to empty it
by refactoring the AST and the pipeline so that every shape a pass declares over
is a real constructor. The planned refactors are recorded on the individual
constructors below.

## These declarations are an approximation

The ordering constraints derived from these declarations are not the pipeline's true
dependencies — they are an approximation of them, and the approximation is only as good as
the declarations. Nothing checks a declaration against the pass it describes, so a `removes`
that is too broad, or a dependency recorded on a shape the pass does not really consume,
produces an edge that looks machine-checked but is not.

The true edges will only be known once we prove that each pass satisfies its specification.
Until then, treat a derived edge as a well-documented claim rather than a guarantee, and
prefer declaring nothing over declaring something untrue: a missing edge leaves the ordering
unenforced, but a false one is actively misleading about what has been established.
-/

namespace Strata.Laurel

public section

/-- The vocabulary of AST shapes that passes declare over. See the module
    documentation for the `Owner.field.Leaf` naming scheme and for what
    `Pseudo.*` means. -/
inductive NodeKind where
  -- StmtExpr constructors
  | StmtExpr.Block
  | StmtExpr.Exit
  | StmtExpr.IfThenElse
  | StmtExpr.While
  | StmtExpr.Return
  | StmtExpr.Assign
  | StmtExpr.Var
  | StmtExpr.IncrDecr
  | StmtExpr.CompoundAssign
  | StmtExpr.StaticCall
  | StmtExpr.InstanceCall
  | StmtExpr.This
  | StmtExpr.New
  | StmtExpr.PureFieldUpdate
  | StmtExpr.IsType
  | StmtExpr.AsType
  | StmtExpr.Assert
  | StmtExpr.Assume
  | StmtExpr.Throw
  | StmtExpr.Try
  /-- A `try` carrying a `finally` arm. `EliminateExceptions` removes it along with every
      other `Try`; `EliminateReturnStatements` declares it `unsupported` because it lowers
      `return` to `exit`, and a `return` that a `finally` should have intercepted would then
      leave the procedure without running the arm — silently. -/
  | StmtExpr.Try.finally?.some
  | StmtExpr.Yield
  | StmtExpr.Resume
  | StmtExpr.HasNext
  | StmtExpr.Snapshot
  | StmtExpr.OldGuarantee
  | StmtExpr.OldRelies
  | StmtExpr.LiteralBool
  -- StmtExpr refinements
  /-- A post-test loop: the `do … while` form. -/
  | StmtExpr.While.postTest.true
  /-- `return expr` — a return carrying a value. -/
  | StmtExpr.Return.value.some
  /-- A labeled `old`, i.e. a snapshot read. -/
  | StmtExpr.Old.label?.some
  /-- An `old` already wrapping a bare variable reference. -/
  | StmtExpr.Old.value.Var.Local
  | StmtExpr.Hole.type.none
  | StmtExpr.Hole.type.some
  | StmtExpr.Hole.deterministic.true
  /-- A nondeterministic hole: the `if *` condition, and the value a havoc assigns. -/
  | StmtExpr.Hole.deterministic.false
  /-- A field read, `o#f`. -/
  | StmtExpr.Var.var.Field
  -- Types
  | TypeDefinition.Composite
  | TypeDefinition.Constrained
  | TypeDefinition.Datatype
  | TypeDefinition.Alias
  /-- A generic composite, `composite Box<T>`. -/
  | CompositeType.typeArgs.cons
  /-- A composite carrying at least one method. -/
  | CompositeType.instanceProcedures.cons
  | HighType.Applied
  | HighType.TVar
  -- Program, Procedure, Body
  | Program.staticProcedures.cons
  | Program.staticFields.cons
  | Procedure.inputs.cons
  /-- A coroutine: a procedure whose contracts are not `.Regular`. -/
  | Procedure.contracts.Coroutine
  | Procedure.preconditions.cons
  /-- A procedure declaring `throws T`. -/
  | Procedure.throwsType.some
  /-- A `throwsOn C { ensures … modifies … }` behavior case. -/
  | Procedure.throwsOn.cons
  | Body.postconditions.cons
  | Body.modifies.cons
  /-- A *free* condition: assumed but never asserted. -/
  | Condition.mode.Assume
  -- Operations
  | Operation.AndThen
  | Operation.OrElse
  -- Not AST constructors; see the module documentation.
  /-- The four representations the pipeline passes through. Planned refactor: a
      top-level `inductive Program where | OnlyProcedures .. | ProceduresAndFunctions ..
      | OrderedAndGroupedTopLevels .. | Core ..`, after which these four become
      ordinary constructors and stop being `Pseudo`. -/
  | Pseudo.laurelProgram
  | Pseudo.unorderedDeclarations
  | Pseudo.orderedDeclarations
  | Pseudo.core
  /-- An `old` wrapping a compound expression: the complement of
      `StmtExpr.Old.value.Var.Local`, which no path can name. Planned refactor:
      split the AST's `Old` into two constructors, one taking an arbitrary
      expression and one taking only a variable reference, after which this
      becomes the former and stops being `Pseudo`. -/
  | Pseudo.oldExpr
  /-- The heap held as a file-scope global (`$heap`, `HeapParameterizationConstants.heapVarName`).
      `HeapParameterization` declares it; `TypeHierarchy` and `ModifiesClauses` build frames over
      it while it is still a global; `GlobalParameterization` threads it through signatures and
      clears `staticFields`, which is what removes it. Note this does not capture the *other* half
      of the modifies→globalParameterization dependency — that the heap trio shares one
      re-resolve, ending at `ModifiesClauses`, which binds `$heap` references as `$static`
      fields. `needsResolves` is not modelled by these declarations at all. -/
  | Pseudo.heapVar
  /-- Object state held implicitly, in each composite's own fields, rather than explicitly in
      the heap. `HeapParameterization` removes it: it empties every composite's `fields`
      (`HeapParameterization.lean`, the `.Composite ct => .Composite { ct with fields := [] }`
      arm) and rewrites field access into `readField`/`updateField` over
      `TotalMap Composite (TotalMap Field $Box)`. `TypeHierarchy` and `ModifiesClauses`
      declare it `unsupported` because both work over that explicit form — the former lowers
      `New`/type tests against it, the latter builds frames over `Composite` and `Field`.

      This kind stands in for a refactor these three passes need. They are one logical unit —
      `HeapParameterization` has `needsResolves := false` with the comment that resolution
      should only run again after all three, because they share a single re-resolve — yet they
      are three separate entries in the pipeline whose interdependence is only partly
      expressible here. Two parts are missing: that the shared re-resolve ends at
      `ModifiesClauses` (a `needsResolves` fact, which these declarations do not model at
      all), and that `GlobalParameterization` must follow the whole trio. Merging them, or
      giving the group an explicit representation, would let all of that be stated directly
      instead of approximated by this label. -/
  | Pseudo.implicitHeap  | Pseudo.box
  | Pseudo.totalMap
  | Pseudo.typeTag
  | Pseudo.asFunctionTwin
  | Pseudo.overload
  /-- The program still owes its behavioral-subtyping (Liskov) checkers: for every method
      that overrides an ancestor's, the pair of refinement obligations has not yet been
      emitted. `CheckOverrideRefinement` discharges this by emitting them, which is what
      removes it. `LiftInstanceProcedures` declares it `unsupported` because it flattens
      methods to top-level procedures and clears the override relation — after it, the
      obligations can no longer be generated at all, so a program still owing them would
      silently get none.

      An obligation rather than a shape: unlike the other `Pseudo` kinds this denotes
      something the pipeline owes, not something the AST contains. It exists because the
      dependency it carries is "these methods must still be attached to their composites",
      which no `creates`/`removes` pair over real constructors can express.

      Planned refactor that retires it. Rename `CheckOverrideRefinement` to
      `LowerAbstractBodies` and give it a second job: as well as emitting the override
      refinement checks, replace each abstract body with a dispatch method — the lowering
      `LiftInstanceProcedures` performs today. `LowerAbstractBodies` then genuinely removes
      `Body.Abstract`, and `LiftInstanceProcedures` genuinely cannot handle it, so both
      declarations become true statements about a real AST constructor and this obligation
      kind is no longer needed to force the ordering. -/
  | Pseudo.needsOverrideRules
  | Pseudo.coroutineOverride
  | Pseudo.generatedReturn
  /-- A short-circuit operator (`&&`, `||`, `=>`) whose guarded operand contains an
      assignment or a call to an imperative procedure. `DesugarShortCircuit` rewrites
      exactly these to `IfThenElse`; short-circuits over pure operands survive and are
      handled by the Core translator, so the operator constructors themselves are not
      removed. `LiftImperativeExpressions` cannot handle one, because it would hoist the
      imperative call out of the branch that guards it.

      `Pseudo` because the shape is a constructor together with a property of its operand
      subtree, and which callees count as imperative depends on the program's static
      procedures — neither is an `Owner.field.Leaf` path. -/
  | Pseudo.imperativeShortCircuit
  /-- A statement-shaped construct sitting in an expression position. Planned
      refactor: split `StmtExpr` into `inductive Stmt` and `inductive Expr`, with
      an `Expr` constructor `StmtExpr (stmt : Stmt)` embedding the former in the
      latter. Removing *that* constructor is then what this kind denotes, so it
      stops being `Pseudo`. -/
  | Pseudo.statementExpression
  /-- A let-expression: a `var x := e` binding inside a pure (function) body, which Core has
      no way to encode. `InlineLocalVariables` removes it by substituting the initializer at
      every use, and `LaurelToCoreSchemaPass` declares it `unsupported` because it would
      otherwise have to emit a binding Core cannot express.

      Both users disappear together once Core gains `let`: `InlineLocalVariables` exists only
      because Core lacks it (see that pass's documentation) and the schema pass's matching
      guard is replaced by the `.app`/`.abs` translation already sitting commented out beside
      it. Delete this kind then — but delete *both* declarations, since an `unsupported` left
      without a `removes` is a claim no pass backs. -/
  | Pseudo.letExpr
  deriving BEq, Repr, DecidableEq, Hashable

/-- Whether this shape can occur in a program *as authored* — i.e. whether it is present
    before any lowering pass runs. This is the pipeline check's initial live set: see
    `LaurelCompilationPipeline.orderingFailures`, which folds
    `(live \ removes) ∪ creates` over the passes and demands that no pass's `unsupported`
    shape is live when it runs.

    The match is exhaustive on purpose: a new `NodeKind` cannot be added without deciding
    which side it falls on.

    Getting an entry wrong is not symmetric. Marking a source shape as generated
    **weakens** the check silently — the shape is never live, so an `unsupported`
    declaration on it passes vacuously. Marking a generated shape as source can only make
    the check stricter, and any error surfaces as a build failure. So when in doubt, answer
    `true`. -/
def NodeKind.inSource : NodeKind → Bool
  -- Introduced by a lowering pass; absent from any authored program.
  | NodeKind.Pseudo.unorderedDeclarations   -- TransparencyPass
  | NodeKind.Pseudo.orderedDeclarations     -- Ordering
  | NodeKind.Pseudo.core                    -- LaurelToCoreSchema
  | NodeKind.Pseudo.heapVar                 -- HeapParameterization declares `$heap`
  | NodeKind.Pseudo.box                     -- the generated `$Box` datatype
  | NodeKind.Pseudo.totalMap                -- the generated heap map type
  | NodeKind.Pseudo.typeTag                 -- TypeHierarchy's `TypeTag` datatype
  | NodeKind.Pseudo.asFunctionTwin          -- TransparencyPass's `$asFunction` twins
  | NodeKind.Pseudo.generatedReturn         -- returns in HeapParameterization's helper procedures
  | NodeKind.Pseudo.coroutineOverride       -- CoroutineElaboration's generated overrides
  | NodeKind.StmtExpr.Snapshot              -- YieldElim
  | NodeKind.StmtExpr.Old.label?.some       -- YieldElim's snapshot reads
  | NodeKind.StmtExpr.Hole.type.some => false  -- InferHoleTypes annotates holes
  -- Everything else can be written, or arises directly from what was written. Note in
  -- particular `Pseudo.letExpr`: a `var x := e` in a function body comes from
  -- source, since TransparencyPass carries a transparent body's declarations into the
  -- function it creates — which is why `InlineLocalVariables` exists at all.
  | _ => true

/-- The dotted path, for diagnostics: `StmtExpr.While.postTest.true`. -/
def NodeKind.name (k : NodeKind) : String :=
  -- `Repr` renders the constructor fully qualified, e.g.
  -- `Strata.Laurel.NodeKind.StmtExpr.While.postTest.true`; drop that prefix so
  -- diagnostics show just the path.
  (repr k).pretty.replace "Strata.Laurel.NodeKind." ""

instance : ToString NodeKind where
  toString := NodeKind.name

end -- public section

end Strata.Laurel
