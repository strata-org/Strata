/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import VersoManual

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in
-- the same process and environment as Verso
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Strata Core Transforms and Analysis" =>
%%%
shortTitle := "Core Transforms and Analysis"
%%%

# Introduction

This document describes the transforms and analyses available for Strata Core
programs. Transforms are program-to-program rewrites that are independent of any
specific analysis. Analyses consume a (possibly transformed) Core program and
produce verification results. For the language definition itself, see the
[Strata Core Language Definition](../../langdef/html-single/).

# Program Transforms

Program transforms are applied to a Strata Core program before analysis. They
are independent of the choice of analysis and can be composed in sequence. The
`strata transform` CLI command applies one or more passes to a Core program:

```
strata transform file.core.st --pass <name> [--procedures <procs>] [--pass <name> ...]
```

Passes are applied left to right. The `--procedures` and `--functions` flags
bind to the most recent `--pass`.

## Procedure Inlining (`inlineProcedures`)

Replaces procedure call sites with the body of the callee, substituting actuals
for formals. The `--procedures` flag restricts which procedures are inlined; if
omitted, all eligible procedures are inlined.

## Call Elimination (`callElim`)

Replaces each procedure call with the contract-based encoding described in the
language reference: assert preconditions, havoc outputs, assume postconditions.
This is the standard modular verification encoding.

## Loop Elimination (`loopElim`)

Replaces loops with their invariant-based abstraction: assert the invariant,
havoc the modified variables, assume the invariant and the negation of the
guard.

## CFG Loop Elimination (`cfgLoopElim`)
%%%
tag := "cfg_loop_elim"
%%%

Cuts every loop of an unstructured (`cfg`) procedure body at its header, so that
the body becomes acyclic. A loop header is a block `h` with an incoming *back
edge* `b → h` from a block `b` that `h` dominates. Its invariants are the
expressions of its `@[loopInvariant = (e)]` annotations (none means `true`).
Before `h` the pass inserts a block that asserts the invariants (they hold on
entry), marks the cut with a labelled `assume true`, havocs the variables the
loop modifies, and assumes the invariants;
every edge into `h` that is not a back edge goes through it. Each back edge
`b → h` is redirected to a block that asserts the invariants (they are
maintained) and ends the path. The invariants move from the header's metadata
into these commands. A cycle without a dominating header (irreducible control
flow) is rejected, as are a `loopInvariant` on a reachable block that is not a
loop header and a local declared inside a loop. The choice a nondeterministic
`goto l1, l2;` branches on is not such a local: it is declared once, before the
loops, and havocked where the `goto` is (`hoistNondetChoices`, before type checking).
Precondition elimination runs after the cut, and checks the preconditions of its
`assert`s and `assume`s like those of any other command. A failure resting on the cut
is reported `unknown` unless replaying the model through the program before the cut
confirms it (`CFGLoopElim.replayValidates`). `--vcgen symexec` and `--vcgen usp/uwp`
run it. See [Passive VC Generation](#passive_vc_generation) for the syntax and how
results are reported.

## Procedure Filtering (`filterProcedures`)

Removes all procedures except those named in the `--procedures` flag (and any
procedures they transitively depend on).

## Irrelevant Axiom Removal (`removeIrrelevantAxioms`)

Removes axioms that do not mention any of the functions named in the
`--functions` flag, reducing the size of the analysis problem.

Additional internal transforms (e.g., `PrecondElim`, `DetToKleene`,
`StructuredToUnstructured`) are used by the analysis pipelines but are not
currently exposed via the CLI.

# Configuring the Pipeline

The transforms above run as a *pipeline*: an ordered list of phases, each declaring
what it requires of the program it receives, what it establishes, and what it leaves
standing. A list composes when every phase's requirements are met by the phases before
it, and the back end accepts it when the list also delivers what obligation extraction
needs. Both are checked before anything runs, so an unworkable order is reported rather
than attempted.

`strata verify --display-phases` prints the default order as a pasteable argument, along
with the phases available outside it, and `--display-phase-contracts` prints what each
phase requires, delivers and preserves. Those two commands are the vocabulary: this
document deliberately does not list the phases, because the tool's output cannot fall out
of date and prose can.

`--phases <list>` runs a list of your own. With no file to verify it reports whether the
list composes, which is the cheapest way to try an order out. Order matters and the
checks will tell you so: naming a phase before the one that establishes what it requires
is refused, with the phase that would have established it named in the message.

A phase list may assert a fact instead of establishing it. For every fact with an
executable check there is an `assert<Fact>` phase — `assertNoLoops` and the like — which
checks the fact on the program and passes it through. That is how a list can stand where
another order runs a transform: if the input already has the property, checking it is
cheaper than rewriting the program to produce it.

A tool that keeps a registry of pipelines gates this further. `stratainternal` accepts
`--pipeline <name>` to run a registered pipeline, and refuses a `--phases` list that no
entry holds, answering with the three ways forward: enable unregistered pipelines in a
development build, run an existing pipeline by name if your package already uses that
exact list, or register the list by adding the entry the refusal prints. Where
unregistered pipelines are enabled the list runs and the run says so. Registration is what
lets a change to the phase vocabulary be carried to the packages that depend on one,
rather than silently changing what they verify.

A registered entry may also state facts it assumes of its input, and those are where the
assert forms earn their place: a command line cannot prove anything, so `--pipeline` puts
an `assert<Fact>` phase in front for each assumed fact and reports which ones it added.
The entry's own phases are unchanged; the checks are the price of arriving without a proof.

From Lean there is a second route. A front end that proves facts of the program it emits
can assume them instead, through the validating entry points that take those facts and the
proof that they hold, and then omit the phases that would have established them. A command
line has no way to supply such a proof, which is why the flags offer nothing equivalent.

`--no-cse`, `--function-inlining` and `--unroll-bounded-quantifiers` are unknown options: a
pipeline names the phases it runs, so no option reshapes it. To run those phases, name them
with `--phases` (`--display-phases` prints the default order to start from).

Migrating is mechanical but not a drop-in: a script or CI job still passing one of these
exits with an unknown-option error, and `--phases` names the whole order rather than toggling
one phase. Start from `--display-phases` and edit that list. On `stratainternal` an
unregistered `--phases` list is refused, so a caller of a registered pipeline uses
`--pipeline <name>` instead.

# Analysis Modes
%%%
tag := "analysis_modes"
%%%

Strata supports four analysis modes, selected via `--check-mode`. These modes
are independent of the specific analysis being used — they control how results
are classified.

1. *`deductive`* (default): Prove correctness — every assertion must hold on
   all inputs.
2. *`bugFinding`*: Find bugs assuming incomplete preconditions — only definite
   bugs are errors.
3. *`bugFindingAssumingCompleteSpec`*: Find bugs assuming complete
   preconditions — any counterexample is an error.
4. *`deductiveAssumingSatisfiablePaths`*: Deductive, on the premise that every
   path to an assertion can be taken. An assertion whose goal is reduced by the
   evaluator to the literal `false` is reported failing without asking the
   solver whether its path condition is satisfiable, unless one of its
   assumptions is literally `false`. Passes mean what they mean in `deductive`.

Each verification condition produces two queries: a satisfiability check
(`P ∧ Q`) asking whether the property can be true given the path condition,
and a validity check (`P ∧ ¬Q`) asking whether it can be false. The
combination determines the outcome and severity in each mode.

# Verification-Condition Generation

`strata verify` turns each procedure into proof obligations in one of three
ways, all of which feed the same back end (obligation extraction, SMT encoding,
solver, and the result classification of [Analysis Modes](#analysis_modes)):

- *Symbolic evaluation* (default; `--vcgen symbolic`):
  structured bodies are partially evaluated, path by path, into obligations.
- *Weakest preconditions* (`--vcgen wp`): structured bodies are
  turned into guarded programs and then into obligation programs.
- *Passive VC generation* (`--vcgen usp` or `--vcgen uwp`): structured and
  unstructured bodies are lowered to control-flow graphs, passified, and given
  verification conditions in the strongest-postcondition (`usp`) or
  weakest-precondition (`uwp`) calculus. Described below.

## Passive VC Generation
%%%
tag := "passive_vc_generation"
%%%

Passive VC generation verifies procedures with unstructured (`cfg`) bodies, as
well as structured bodies. Its verification conditions are linear in the size of
the passive control-flow graph (for `usp`; see [Efficiency](#passive_vc_efficiency)),
where symbolic evaluation enumerates paths. A program may have both kinds of
body: structured loops are eliminated by the same phases as under `--vcgen symbolic`
(from their `invariant` and `decreases` clauses), and the loops of a CFG body are
cut by CFG loop elimination (from `@[loopInvariant]` annotations).

### Selecting it

`--vcgen usp` selects it with the strongest-postcondition calculus, and
`--vcgen uwp` with the weakest-precondition calculus. The two have the same
verdicts in principle (the solver's heuristics can differ on their formulas);
`usp`, whose verification conditions are smaller, is the one to use unless you
are comparing calculi. Passive VC generation runs only when selected, since these
modes are not yet proved sound (see [Soundness](#passive_vc_soundness)). The default
`--vcgen symbolic`, and `--vcgen wp`, reject a procedure to be verified that has a CFG
body (with `--procedures`, one of those named or of their callees), with an error that
says to pass `--vcgen symexec`, which handles an acyclic CFG body, or `--vcgen usp`. An
explicit pipeline is run as given.

### Soundness
%%%
tag := "passive_vc_soundness"
%%%

`--vcgen usp` and `--vcgen uwp` are not yet proved sound. The phases they add, or
extend to CFG bodies, have no correctness theorem yet; each needs one, stating that
the phase's output verifying implies its input verifying. As results are reported per
assertion, each is best stated per obligation: if an assertion's obligation is valid,
and so are the obligations it rests on (none under `passiveVC` alone; a loop
invariant's entry and maintenance checks under a cut; a callee's contract under call
elimination), then no run falsifies the assertion.

- `passiveVC`: the obligation procedures it produces hold only if the procedures
  they come from are correct (`Strata/Transform/PassiveVCGenCoreProgram.lean`, over
  the generator `Strata/DL/Imperative/PassiveVCGen.lean`);
- `cfgLoopElim`: cutting the loops of a CFG body
  (`Strata/Transform/CFGLoopElim.lean`; `CFGLoopElimProps.lean` proves only that
  the result is acyclic);
- call elimination (`Strata/Transform/CallElim.lean`), on CFG bodies and on
  structured ones: it has no correctness theorem for either body kind (the
  statement-level theorem of `CallElimCorrect.lean` is commented out); its
  temporaries' freshness is proved (`callElimTemps_spec`);
- precondition elimination on CFG bodies (`transformCFG` in
  `Strata/Transform/PrecondElim.lean`);
- `hoistNondetChoices` (`Strata/Transform/CFGLoopElim.lean`), which is declared
  model-preserving.

Two other pieces they rely on are unproved too:

- the replay validation of a result resting on a loop cut
  (`CFGLoopElim.replayValidates`, through `cfgLoopElimPipelinePhase`), the only new
  validation that turns `unknown` into a definite result. It owes: a model it accepts
  gives a run of the program before the cut that reaches the check with the value
  the query claims, and in which every procedure, the check's own included, is
  entered in a state that meets its preconditions;
- the dominator map (`computeDominators`, a pre/post numbering of the dominator
  tree), used by the CFG type checker's scope checks, by passification's joins, and
  by symbolic execution's merges on the default path. It is checked against a
  textbook fixpoint on random graphs (`CFGDominatorsTest`).

Until then, their results rest on testing: the regression, agreement and
differential tests under `StrataTest`, which compare the verdicts with those of
`--vcgen symbolic` where both apply.

### Unstructured procedure bodies

A procedure body may be a control-flow graph: an entry label and a list of
labelled blocks, each a sequence of commands ending in a transfer.

```
procedure CountUp(n : int, out y : int)
spec {
  requires (int.ge(n, 0));
  ensures (y == n);
}
cfg entry {
  entry: {
    y := 0;
    goto loop;
  }
  @[loopInvariant = (int.le(y, n))]
  loop: {
    branch (int.lt(y, n)) goto body else goto done;
  }
  body: {
    y := int.add(y, 1);
    goto loop;
  }
  done: {
    return;
  }
};
```

A transfer is `goto l;`, `goto l1, l2;` (a nondeterministic choice),
`branch (e) goto l1 else goto l2;`, or `return;`. A block may declare locals; a
local is in scope in the blocks that its declaring block dominates and that come
after it in the text. A local may not be declared in a block on a cycle.

A block may be annotated, before its label, with the same `@[...]` syntax as a
statement: `@[key]`, `@[key = "text"]` or `@[key = (e)]`. The annotations are the
block's metadata. An expression in them is resolved in the scope at the start of
the block (not the block's own locals) and type-checked, at any type. The key
`loopInvariant` gives the loop invariants of a loop header; a header may carry
several. (`invariant` cannot be used as a key, being a keyword.)

### The pipeline

The phases run in this order (`strata verify --vcgen usp --display-phases`
prints them):

1. *Hoisting of loop choices* (`hoistNondetChoices`): in a CFG body with a loop, the
   choice a nondeterministic `goto` branches on, which the translator declares in its
   block, is declared once at the entry and havocked in place, since type checking
   rejects a declaration in a block on a cycle.
2. *Type checking, and procedure filtering* (`typeCheck`, `filterProcedures`) when
   `--procedures` is given, as in the default order. Type checking also checks the
   expressions of block annotations, and a `loopInvariant` must be boolean.
3. *CFG loop elimination* (`cfgLoopElim`): see
   [CFG Loop Elimination](#cfg_loop_elim). It comes before call elimination, so
   that the program a counterexample is replayed through still has its calls.
4. *Call elimination* (`callElim`): each call becomes its callee's contract,
   in structured bodies and CFG blocks alike.
5. *Termination and precondition checks* (`termCheck`, `precondElim`): a call to
   a partial function gets an assertion of its precondition before the command
   that makes it (at the end of the block, for a branch guard), and contract
   and function well-formedness lemmas are generated, as in the default order.
   With `--procedures`, a second `filterProcedures` then keeps only the
   procedures generated from those named.
6. *Structured loop elimination* (`insertLoopInvariantAsserts`, `loopElim`): the
   invariant and measure assertions of each structured loop, and its replacement
   by an acyclic encoding, as in the default order. A CFG body is left as it is.
7. *Opaque type parameters, function monomorphization and simplification*
   (`simplify`), as in the default order: a call of a recursive function on values
   is unfolded, in a structured body.
8. *Declaration obligations* (`declObligations`): each lemma becomes an
   obligation unit, as for `--vcgen wp`.
9. *Passive VC generation* (`passiveVC`): each procedure becomes an obligation
   procedure (below). It requires every CFG body to be acyclic (the fact
   `noCFGCycles`, which only `cfgLoopElim` establishes) and no structured loop
   (`noLoops`), so a `--phases` order without the phases that eliminate loops is
   refused when the order is checked.
10. *Beta reduction*.

The program's functions, axioms and datatypes reach the back end unchanged, so
they are encoded as in [SMT Analysis](#smt_analysis).

### How verification conditions are generated

For each procedure:

1. A structured body is lowered to a deterministic CFG; a CFG body is used as
   is. Before lowering, a local declared again in a sibling scope (two branches
   of an `if`, say) is renamed apart (`x$u`, …), since the CFG has one scope and
   a variable one type; so is a repeated block label, or one ending in
   `_<digits>` (`l$b0`, …), which could collide with the lowering's labels.
   Lowering then rejects a body with an `exit` outside any block of its label,
   or a local named with a prefix the lowering reserves. The specification is
   added at the CFG level: an unconstrained, typed declaration of each
   parameter, a snapshot `old g` of each in-out parameter, and an `assume` of
   each `requires` at the entry; an `assert` of each `ensures` at every exit. A
   `free ensures` is neither checked nor assumed: the body does not establish
   it. A returning block that contains `assume false`, such as each block loop
   elimination adds for a back edge, ends a path but is not an exit. A local
   declared at two different types is an error.
2. The CFG becomes nondeterministic: a branch `branch (e) goto l1 else goto l2`
   becomes a choice between two fresh blocks, one that does `assume e` and goes
   to `l1`, the other `assume !e` and goes to `l2`. Dropping these guards would
   be unsound.
3. The CFG is *passified*: every assignment `x := e` gets a fresh incarnation
   `x@k` constrained by `assume x@k == e`, a havoc a fresh unconstrained one, and
   at each join the incarnations of the branches are reconciled, on edges split
   where needed so that each reconciliation is on one edge only. Afterwards no
   variable is assigned twice, and reads refer to incarnations. A write to a
   function-typed variable (a local function, a copy of one, a conditional of
   two) is substituted into its uses instead of being equated with an
   incarnation, which the solver could not handle; it captures the values of the
   variables it reads where it is written. At a join, a function-typed variable
   that every path writes the same way keeps its value. Otherwise it is
   unconstrained after the join, which starts with a labelled `assume true`: a
   failure or a cover met that rests on this is reported `unknown`.
4. Each block `n` gets a precondition `A_n`, the disjunction of its
   predecessors' postconditions (`true` at the entry). Each `assume e` of the
   block strengthens it: `R_k := R_{k-1} ∧ e`, starting from `A_n`; the last is
   the block's postcondition. An assertion `ψ` reached with precondition `α`
   (the last `R` before it) holds iff `α ⇒ ψ` is valid; a cover `e` is met iff
   `α ∧ e` is satisfiable. A command no path reaches has precondition `false`.
   Under `uwp`, the assertion's goal is instead the weakest precondition of the
   entry when only that assertion is checked, built from definitions `W` for the
   blocks that can reach it.
5. The result is an obligation procedure, which declares the incarnations and
   defines every `A` and `R` by name (each refers to earlier ones by name),
   and then, for each assertion or cover in its own nondeterministic branch,
   defines the `W`s of its goal (under `uwp`), assumes `α` and asserts `ψ` (or
   covers `e`). The obligation also assumes the
   conjunction of the assumptions that hold on every path to the command (those
   of the blocks that dominate it, and those before it in its block), defined
   in the same way as a chain `F`: it follows from `α`, but stated on its own
   it lets the solver use these assumptions directly, which matters for
   quantified ones. The branches are in program order: the order of the blocks
   of the input, and of the commands in each.

Every assertion is checked on its own, as under symbolic evaluation: the
assertions before it are neither assumed nor checked in its obligation.

### Results

Results are reported as for the other generators, one per assertion or cover,
with its source location, label and property type (for instance a division by
zero check). Generated checks are labelled after what they check:

- `cfgLoopElimAssert_entry_<header>_<i>`: invariant `i` of the loop at `<header>`
  holds on entry; `cfgLoopElimAssert_maintain_<header>_<block>_<i>`: it is
  maintained along the back edge from `<block>` (`<header>_<block>` gets a
  numeric suffix if another header and block make the same text). Their location
  is the loop header's transfer: its `branch` or its `goto`.
- `callElimAssert_<label>_<n>`: a callee's precondition at a call.
- `<context>_calls_<function>_<n>`: a partial function's precondition, where
  `<context>` names the command (`set_y`, `assert_<label>`, `branch_cond`, ...).
  In the default order a loop invariant is checked as the command that
  loop elimination made of it, so the context is `assert_cfgLoopElimAssert_entry_…`
  or `assume_$__cfgLoopElimAssume_invariant_…`. Precondition elimination refuses a
  block that still carries a `loopInvariant`, so it always runs after the cut.
- A postcondition is reported under its own label.

A cover in a command no path reaches fails, as its precondition is `false`.

Because each obligation's path condition is exactly the condition of reaching
its command, `--check-level full` classifies results from the satisfiability and
validity queries of [Analysis Modes](#analysis_modes) as symbolic evaluation
does, unreachable commands included, and the check modes apply unchanged (for
instance `bugFinding` reports dead code as an error).

A result that rests on an abstraction is not reported as definite. When a
counterexample to an assertion, or a witness for a cover, may depend on the
assumptions call elimination makes about a callee or loop elimination makes
about an arbitrary loop iteration, the result is `unknown`, as under symbolic
evaluation: such a state need not be reachable in the program. For instance, a
loop invariant that is not maintained is reported `unknown` rather than `fail`.

A result resting on the cut of a CFG loop is checked by replay: the model's values
of the procedure's parameters on entry are run through the procedure as it was
before the cut, with its preconditions assumed and its postconditions asserted, on
the interpreter that validates counterexamples. If that run reaches the check with
the value the query claims (failing, for a counterexample), the result is
definite, since the run is one of the program's; otherwise it stays `unknown`. The
program before the cut still has its calls, and the run executes the callees'
bodies, not their contracts; a run through an assumption of an abstraction that
an earlier phase made (a callee's contract, under an order that eliminates calls
first) is not accepted. A callee without a body is run by its contract only when
it has no outputs, so a call changes no variable: the run assumes its
postconditions. A call of one with outputs stops the run. So a
postcondition that fails whatever the loop does is reported `fail`. Results that
rest on call elimination but on no loop cut, on the loop elimination of structured
loops, or on a join that the passive VC phase resets, are not replayed yet, and stay
`unknown`.

Counterexamples (shown with `--verbose`) are given in the program's variables: each
variable written before the failing check gets its value at that check. The passive VC
phase records, at each check, which incarnation `x@k` of each variable `x` is current
there, and the counterexample gives `x` that incarnation's value. A variable the
procedure never writes before the check is not listed.

### Options

`--vc-directory`, `--sarif`, `--check-level`, `--check-mode`, `--solver`,
`--solver-timeout`, `--procedures` and `--phases` apply as for the other
generators. `cfgLoopElim` and `passiveVC` can be named in `--phases` under every
`--vcgen`, and `cfgLoopElim` is available as `strata transform --pass
cfgLoopElim`. `--vcgen wp` and `--path-cap` select or bound the generators
of `--vcgen symbolic`, and are refused under the default order of `uwp` and
`usp`.

### Efficiency
%%%
tag := "passive_vc_efficiency"
%%%

The block predicates are named definitions, so the obligation procedure is
linear in the size of the passive CFG under `usp`: a chain of `n` branches does
not double the formula at each join. The passive CFG adds, at each join, an
equality per predecessor for each variable written since the join's immediate
dominator, so its size grows with branch nesting depth as well as with the CFG.
A shared definition is declared in front of the first obligation that reads it,
so an obligation's query includes the definitions up to the ones it needs, and
none after; the solver's total input is still up to the number of obligations
times the size of the CFG. Under `uwp`, each assertion's
goal recomputes the predicates of the blocks that can reach it, so the size is
at most the number of assertions times the number of blocks; each assertion's
query, though, contains only its own goal's definitions. For straight-line code
with an assertion after each of `n` assignments this is quadratic in `n`, so
`usp` is the better choice for it. Symbolic
evaluation, by comparison, enumerates paths, which is exponential in the number
of sequential branches.

### Limitations

- Loops in CFG bodies are checked for partial correctness only: there is no
  `decreases` for them.
- Irreducible control flow is rejected.
- A call of a recursive function that the SMT encoding leaves uninterpreted (one
  with a `decreases` clause and no `@[cases]` parameter) is unfolded on values by
  the simplifier, as in the default order, but only in a structured body: the
  simplifier keeps a CFG body as it is. In a CFG body, a check that needs such a
  call's value can be reported `fail`.
- Each assertion is checked on its own, without assuming the assertions before it,
  as under `--vcgen symbolic`. On a long chain of branches with an assertion in
  each, the solver time can grow quickly with the chain; an `assume` of each
  assertion after it keeps the later queries small.
- Proofs that need a quantified assumption instantiated at terms that only occur
  on some paths depend on the solver's heuristics, and may come back `unknown`
  where symbolic evaluation, which checks each path separately, succeeds. A
  stronger solver setting may help (for cvc5, the option `full-saturate-quant`,
  through `--set-option`).
- Block annotations other than `loopInvariant` are not printed by default. A
  printed program (the output of `strata transform`, the files of
  `--keep-all-files`, `toString`) carries its loop invariants, so it verifies the
  same when read back.

# SMT Analysis
%%%
tag := "smt_analysis"
%%%

The SMT analysis translates a Strata Core program into SMT-LIB queries and
delegates reasoning to an external SMT solver.

## Type Encoding

Abstract types are encoded as uninterpreted sorts. Algebraic datatypes are
encoded using the `declare-datatypes` command; the generated functions
(constructors, testers, accessors) are mapped to the corresponding SMT
functions (e.g., `Option..isNone` maps to `is-None`).

## Function Encoding

Functions with bodies are inlined by the partial evaluator where possible.
Functions without bodies are declared as uninterpreted functions.

Recursive functions are simplified by the partial evaluator but are encoded as
uninterpreted functions in the SMT encoding. For recursive functions with
`@[cases]`, per-constructor axioms are generated: for each constructor `C` of
the ADT at the `@[cases]` parameter, an axiom representing the corresponding
rewrite rule (e.g., `List.length Nil = 0` and
`forall h t, List.length (Cons h t) = 1 + List.length t`). Recursive functions
without `@[cases]` are encoded as pure uninterpreted functions with no axioms.

Termination checking is always on for `rec` functions. Strata supports two
termination modes:

- *Structural (ADT):* The TermCheck pipeline phase generates a
  `D..adtRank : D → Int` uninterpreted function with per-constructor axioms
  establishing that recursive fields have strictly smaller rank, and one lemma
  `f_terminates_i` per recursive call site stating
  `adtRank(callArg) < adtRank(callerParam)`.

- *Int-valued:* For functions with an int-valued `decreases` expression, the
  termination lemmas state two obligations at each recursive call site:
  `0 <= call_measure` (non-negativity) and `call_measure < caller_measure`
  (strict decrease), where `call_measure` is the `decreases` expression with
  formals substituted by the actual arguments at the call site.

## Axiom Encoding

Axioms are emitted as universally quantified SMT assertions.
