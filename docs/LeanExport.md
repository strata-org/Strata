# Lean export of undecided verification conditions

With `--lean-directory`, Strata also writes the validity queries the solver
leaves undecided as Lean theorem files. Each file states that the query is valid
and leaves the proof open, so the condition can be proved in Lean by hand or by
another tool.

The export adds files and changes nothing else: solver answers, verification
results, the solver log, standard output and exit codes are those of a run
without it. It needs no Lean installation; Lean is needed only to open the
files. A run with the export takes longer, since each file is written before
the worker that asked the check goes on.

## Command line

```
strata verify Program.core.st --lean-directory lean-out
strata verify Program.core.st --lean-directory lean-out --lean-scope all
strata verify Program.core.st --no-solve --vc-directory vcs \
    --lean-directory lean-out --lean-scope all
```

- `--lean-directory <dir>` writes one file for each validity check that comes
  up for export and is in scope.
- The scope goes by the solver's answer. `--lean-scope undecided` (the default)
  takes the checks answered `unknown` or timed out on. `--lean-scope all` takes
  a check with any answer, and works with `--no-solve`, where no check is
  asked.

What became of each check in scope is appended to `<dir>/export.log`, one line
per check: `wrote` or `kept existing` with the file, or `no file` with the
reason, for a check that has no Lean form here (see "What is translated") or
whose file cannot be written. Only a file that cannot be written, and a line
that cannot be appended to the log, are reported on stderr as well. A disk that
fills up while a line is appended can leave the line cut short, and the next
line appended then continues it.

Some checks never come up for export, in either scope. Strata reports each as
it does without the export, and the log has no line for it:

- a `cover`: it asks whether its condition can be reached, which a proof of
  validity does not show;
- a check Strata decides without the solver (by evaluation, or because its path
  is already known to be contradictory);
- a check whose query Strata cannot encode for the solver and reports as an
  encoding error;
- on the incremental walk (see "The incremental backend"), a check whose solver
  session fails without an answer: a crash, or a remote session that reaches
  its own time limit, which Strata reports as a timeout. (A solver that answers
  `timeout` has answered, and the check is exported. On the per-obligation path
  such a failure is the answer `error`, or `timeout` when its message reads as
  one, and the check is exported.)
- in the mode `bugFinding`, below the full check level and without a
  `@[fullCheck]` or `@[reachCheck]` annotation: only the satisfiability check is
  asked, so there is no validity check.

## The files

A file is named `<label>_<hash>.lean`, where the hash is taken from the
proposition. The name and the proposition of a check's file do not depend on
the order in which checks finish or on the number of workers, so a check that
is exported again finds its file, and two checks with the same label and the
same proposition share one. (In the label, a character other than an ASCII
letter or digit, `_`, `-` and `.` becomes `_`; a name that would start with
`.` or `-`, or be empty, gets `vc` in front; and the first 96 characters are
kept.)

A file that exists is never overwritten: its name says that it states the same
theorem, and its proof may have been filled in. Such a check is logged as
`kept existing`; delete the file to have it written again. The export does not
read an existing file: `kept existing` says that a file of that name is there,
not that its statement is still the check's. A file appears under
its name complete or not at all: the text is written under another name, read
back, and then given its name by a hard link, so the directory must be on a
file system with hard links, and a write that fails is reported and leaves
nothing under the name. The text is not synced to the disk, so a file system
that loses it afterwards can still leave a damaged file there.

The file below is one of those written by
`strata verify Examples/SafeBvOps.core.st --lean-directory lean-out --lean-scope all`.

```lean
-- Strata verification condition: set_a_calls_Bv32.SafeAdd_0
-- Solver's answer: sat (the solver found a counterexample)
-- ...
set_option linter.unusedVariables false in
def vcProp : Prop :=
∀ («y@1» : (@BitVec (@OfNat.ofNat.{0} @Nat (nat_lit 32) (@instOfNatNat (nat_lit 32))))),
∀ («x@1» : (@BitVec (@OfNat.ofNat.{0} @Nat (nat_lit 32) (@instOfNatNat (nat_lit 32))))),
(@Not (@Eq.{1} @Bool (@BitVec.saddOverflow (@OfNat.ofNat.{0} @Nat (nat_lit 32) (@instOfNatNat (nat_lit 32))) «x@1» «y@1») @Bool.true))

theorem vc : vcProp := by
  unfold vcProp
  sorry
```

`vcProp` is Strata's translation to Lean of the query it builds for the solver
for the check: the declared symbols are bound by outer quantifiers, definitions
are `have` bindings, and the assumptions imply the goal. A proof of `vc` shows
the condition as far as that translation is faithful, which is tested and
reviewed, not proved (see "Trust").

The proposition is written out in full: every constant by its full name with
`@`, every argument, universe level, instance and literal explicit. Nothing is
left for Lean to infer, so the text elaborates to the expression Strata built,
up to the names of binders (a binder whose name an enclosing binder or a
constant has is written with a suffix, as in `x_1`, and Lean names the
hypothesis of an implication itself), and the file needs no import. A subterm of
256 bytes or more that occurs several times in a term is written once and bound
by a `let`. The text is not meant to be read: after `unfold vcProp`, Lean
displays the goal in the usual notation,

```
⊢ ∀ («y@1» «x@1» : BitVec 32), ¬«x@1».saddOverflow «y@1» = true
```

and `dsimp only` unfolds the `have` and `let` bindings into the goal, which
some tactics (`omega`) need. A proposition that nests deeper than Lean's
default recursion limit allows sets a higher `maxRecDepth` at the top of its
file, and one longer than 64 KB lifts Lean's time limit (`maxHeartbeats`).

SMT-LIB leaves the value of an integer division or modulo by zero open, and
Lean fixes it (`x / 0 = 0`, `x % 0 = x`). Strata's translator keeps it open in
the file: a proposition whose query has an integer `div` or `mod` binds two
functions, `divByZero modByZero : Int → Int`, before the query's own functions
and variables, and `div x y` reads `if y = 0 then divByZero x else x / y`
(`mod` alike, with `modByZero`). One of
the two that the proposition does not use is written as an arrow, without its
name.

### The solver's answer

The header gives the solver's answer to the validity query: `unsat` (the query
is valid; on a path that cannot be reached it is so vacuously), `sat`,
`unknown`, `timeout`, `error` (the solver failed) or `not asked` (`--no-solve`).
The scope goes by this answer and not by what Strata reports after it: a `sat`
that Strata lowers to unknown, because of axiom pruning or a model it cannot
validate, stays `sat`, and the default scope does not take it. A file that is
kept is left as it is, header included, so its answer is that of the run that
wrote it.

### The incremental backend

The per-obligation path sends each obligation to the solver on its own, with
the check's own query: the batch backend does so for every check, and so does
`--incremental` for a check that is the only goal of its solver session. There
the two checks of an obligation (satisfiability and validity) are asked
together; a timeout on either is the timeout of the obligation, and its validity
check is exported as `timeout`. A session that has several goals answers them
one after another: the walk. (`--vcgen wp` and `--vcgen symexec` leave the goals
of a path together, and `--min-sessions` decides how they are cut into
sessions.)

A walking session may hold more than a check's own query: axioms that this
check's pruning drops, definitions of earlier checks. The file states the
check's own query, the one the per-obligation path sends, so a proof of `vc`
shows the condition as it does there. The solver's `unsat`, though, was given
with the rest at hand and need not hold for the query as the file states it;
the header of such a file reads
`unsat (in a solver session that may hold more than this query states)`.

How the goals are spread over sessions decides whether a check is walked, and
whether Strata decides it without the solver because an earlier check of its
session showed the path contradictory. So the set of exported checks can differ
between runs on the incremental backend; the name and the proposition of a
check's file do not.

## What is translated

The export translates Bool, Int, BitVec, uninterpreted functions and
`define-fun` definitions. A query that reaches a datatype (including `Option`),
an uninterpreted sort, an array, a string, real arithmetic, a regular expression
or a recursive function definition writes no file and reports a diagnostic.
Strings are refused because SMT-LIB's strings and Lean's `String` are different
sets of values, so a statement about Lean strings need not hold for the
solver's. Declarations and sort aliases that no axiom, assumption or goal of the
query reaches are pruned before that check, so a datatype the check does not
reach is no reason to refuse it; a sort that occurs only in the trigger of a
quantifier counts as reached.

A query is also refused when a name would not mean in the file what it means in
the solver's text:

- a variable of the check with the name of a function, since the query can then
  have one symbol for the two. Strata's type checker rejects a procedure whose
  parameter or local variable has the name of a function declared before it; a
  variable that a phase introduces (a common subexpression,
  `$__cse.<n>`) can still meet a function of its name. On the incremental walk
  the built-in functions count as well;
- a declaration with the name of a definition of the context, or a definition
  with the name of a declaration (a symbol of the context that the check itself
  defines, a common subexpression for one, is the usual case and is exported);
  two definitions, two sort aliases, two
  parameters of one definition or two bound variables of one quantifier of one
  name; a declaration that conflicts with a signature of its name;
- a function used under a bound variable of its name; an operator or a constant
  (`true`, `false`, `none`, `some`) used under a bound variable of its name or
  in a query that declares or defines a symbol of that name; a bound variable
  used under a nearer binder of its name and another sort;
- a bound variable or definition parameter named `<x>@<n>` or `<x>.<n>`, the
  shape of the names the solver's encoder gives functions (`abs@1`, `f.0`). The
  rule goes by the shape, so it also refuses such a name when Strata's own
  pipeline generates it, as `me@1` in a Laurel postcondition.

Two limits bound the size. A query whose normalized form has more than one
million term nodes and binders (bound variables, declared symbols, definitions
with their parameters, sort aliases), counted before pruning, is not prepared,
and a
proposition whose text is longer than `ExportConfig.maxFileBytes` (8 MiB unless
set) is not written; either is logged. Below both limits, a query
with quantifiers nested tens of thousands deep can take much memory in the
translator, as it does wherever the translator is used, and a file whose
proposition has thousands of `let` bindings, as thousands of nested or chained
divisions give, is slow for Lean to elaborate.

## Trust

A proof of `vc` shows that the solver's query is valid, and with it the
condition, as far as every step from that query to the file is faithful. One
step is partly proved; the others are tested and reviewed. No verification
result depends on an exported file, so none of this affects what Strata
reports.

**Proved.** Before translating, the export prepares the query (`prepareTerms`):
it assembles the query the solver was sent, prunes it and normalizes operator
shapes. `prepareTerms_sound` in `Strata/DL/SMT/Lean/QueryCorrect.lean`, which
`StrataTest/DL/SMT/Lean/QueryCorrectTests.lean` pins to the axioms `propext`,
`Classical.choice` and `Quot.sound`, says:

> If the assembled query and the prepared query both lie in Strata's typed SMT
> fragment (`SMTQuery.WF`), and the prepared query entails its goal
> (`SMTQuery.EntailsObl`: for every interpretation of sorts, functions and
> variables and every value of a division and a modulo by zero), then the
> assembled query entails the original goal.

- It is one direction, the one a proof of an exported file relies on.
- Both well-formedness conditions are hypotheses. Nothing checks them when a
  file is written.
- The typed fragment is not the set of queries that are exported: it has no
  `abs` and no bit-vector, string or real operation, and it takes `and`, `or`,
  `=>`, `+`, `-`, `*`, `div`, `mod` and the comparisons with exactly two
  operands (the module comment of `QueryCorrect.lean` has the exact
  conditions). On a query outside it the theorem says nothing.
  Of the normalization rules the theorem covers the one for `distinct` of two
  or more operands; the others rewrite shapes outside the fragment, and
  `QueryTests` pins the output of each.

**Tested and reviewed, not proved.**

- The assembly: that the assembled query is the one the solver was sent. The
  solver receives SMT-LIB text that Strata's encoder writes from the terms; the
  file is made from the terms.
- Strata's typed SMT semantics as an account of what the solver implements.
- Preparation of a query outside the typed fragment (tested), and that the
  prepared query is well formed (reviewed only).
- The translation from SMT terms to Lean expressions (`translateQuery`), the
  treatment of a division by zero included. Nothing checks its result here.
- The printer. The tests elaborate exported texts and compare them with the
  expressions they were printed from. The export does not type-check what it
  prints, which would need a Lean environment: an ill-sorted query gives a file
  that Lean rejects when it is opened.
- The Core glue: which checks are exported, with which answer.

## Library use

Set `VerifyOptions.leanExport`:

```lean
import Strata.Languages.Core

def verifyAndExport (program : Core.Program) (directory : System.FilePath) :
    IO Core.VCResults := do
  let leanExport : Core.LeanExport.ExportConfig := {
    directory
    observe := fun event =>
      IO.eprintln s!"{event.label}: {event.stage} {event.diagnostic}"
  }
  EIO.toIO IO.userError <|
    Strata.Core.verifyProgram program
      { Core.VerifyOptions.default with leanExport := some leanExport }
```

Laurel passes the setting through its `verifyOptions`. A custom discharge
function and a custom session factory of the incremental backend are covered,
because the export sits above them; a `CoreSMTSolver` passed as `solver`
replaces the default back end, the export with it. `checkOnly` exports nothing.
`skipSolver` is honoured by the batch backend; the incremental backend, when it
keeps no SMT files, asks its checks all the same, and they are exported with
the solver's answer. A custom discharge function is taken to treat `skipSolver`
as the default one does: with one that does not, the answer in a file's header
and the scope can be off (verification results are not affected).
