# Feature Request: a pre-invariant-proof block on Core loops

*Status: proposal. Measured against `be0fa64db` (`origin/main`).*

## Summary

Core has no program point that denotes *"the loop head, before the invariant is
assumed."* Every well-formedness (WF) obligation arising from a loop invariant
therefore has to be discharged somewhere that is not that point — today, in the
loop's **pre-state**. This is both incomplete (spurious failures) and unsound
(missed division-by-zero and out-of-bounds obligations), and it is not fixable
by moving the existing asserts around: the point where they belong does not
exist in the language.

This document proposes adding that program point as a first-class **loop
pre-invariant-proof block**, and shows why the alternative — Dafny's
`$w$loop#0` auxiliary-boolean encoding — is a workaround forced by the absence
of exactly this construct.

The request is for **Core**, not for a surface language. Core is where
`PrecondElim`, `InsertLoopInvariantAsserts` and `LoopElim` meet, and it is the
only layer where all producers (Laurel, Python, C_Simp, `BoogieToStrata`) can
share one answer.

## Background: how Core checks invariant well-formedness today

Core models partial operations as total functions carrying preconditions
(`Func.preconditions`, `Strata/DL/Util/Func.lean:59`; the Core instances are in
`Strata/Languages/Core/Factory.lean`). `Lambda.collectWFObligations`
(`Strata/DL/Lambda/Preconditions.lean:64`) harvests those preconditions from an
expression, and `PrecondElim` lowers each into an `assert`
(`Strata/Transform/PrecondElim.lean:92`, `collectPrecondAsserts`).

Three passes touch a loop, in this pipeline order
(`Strata/Languages/Core/Verifier.lean:1504-1505`):

```
... precondElimPipelinePhase ... insertLoopInvariantAssertsPipelinePhase, loopElimPipelinePhase
```

1. **`PrecondElim`** (`PrecondElim.lean:287-315`) emits WF asserts for the
   guard, measure and invariants, while the loop is still structured.
2. **`InsertLoopInvariantAsserts`** (`InsertLoopInvariantAsserts.lean:98`)
   materializes the invariant/measure VCs and hands back a *bare* loop
   (`.loop guard none [] new_body`, line 175).
3. **`LoopElim`** (`LoopElim.lean:96`, `removeLoop`) replaces the bare loop with
   its acyclic passive encoding. It now *throws* if invariants are still present
   (lines 100-103), so pass 2 is a prerequisite.

`PrecondElim`'s loop case is where the problem lives:

```lean
| .loop guard measure invariant body md => do
  ...
  let invAsserts := invariant.flatMap (fun (lbl, inv) =>
    let prefix' := if lbl.isEmpty then "loop_invariant" else s!"loop_invariant_{lbl}"
    collectPrecondAsserts F inv prefix' md)
  ...
  return (..., guardAsserts ++ invAsserts ++ measureAsserts ++
    [.loop guard measure invariant (body' ++ measureAssertsEnd ++ guardAssertsEnd) md])
```

Note the asymmetry, which is the whole problem in one expression:

| clause | WF checked in pre-state | WF re-checked at end of body |
|---|---|---|
| guard | yes (`loop_guard`) | yes (`loop_guard_end`) |
| measure | yes (`loop_measure`) | yes (`loop_measure_end`) |
| **invariant** | **yes (`loop_invariant`)** | **no** |

Guard and measure are checked twice because they are *evaluated* twice. The
invariant is likewise used at two states — asserted in the pre-state
(`entry_invariant`, `InsertLoopInvariantAsserts.lean:137`) and both **assumed**
and re-asserted at the arbitrary mid-loop state (`mid_assumes` line 142,
`maintain_asserts` line 145) — but its definedness is checked only once, against
the pre-state.

That is the bug. Those are *different states*.

## Evidence

Both programs below were run at `be0fa64db` via `Core.verify`.

### Defect 1 (unsoundness): the mid-loop occurrence gets no WF obligation

```
procedure Unsound(n : int)
spec { requires (0 <= n); }
{
  var i : int; var d : int;
  i := 0;
  d := 1;
  while (i < n)
  invariant [usesdiv]: ((n / d) >= 0)
  { d := (d - 1); i := (i + 1); }
};
```

`d` starts at `1` and *decreases* toward `0`. The only division-by-zero
obligation Core emits is evaluated in the pre-state, where `d == 1`:

```
Label: loop_invariant_usesdiv_calls_Int.SafeDiv_0
Property: division by zero check
Assumptions:
Unsound_requires_0: 0 <= n@1
Obligation:
true                                    <-- trivially discharged
```

Result: `✅ pass`. But at the arbitrary mid-loop state the invariant is both
assumed and re-asserted with `d@1` unconstrained:

```
Label: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0_usesdiv
Assumptions:
  insertLoopInvAssume_invariant_loop_0_0_usesdiv: n@1 / d@1 >= 0
Obligation:
  n@1 / (d@1 - 1) >= 0
Result: ❓ unknown
Model: (n@1, 1) (d@1, 0) (i@1, 0)
```

The solver hands back `d@1 = 0` — a state in which the invariant Core *assumed*
divides by zero. No obligation was ever generated for it. `n / d` at `d == 0` is
an unconstrained application of `Int.SafeDiv` with an undischarged precondition,
so the assumption is uninterpreted rather than outright false; either way the
definedness of an assumed formula went unchecked, and the assumption is
unjustified.

### Defect 2 (incompleteness): no assume-chaining between invariants

```
procedure Chain(n : int)
{
  var i : int; var d : int;
  i := 0;
  havoc d;
  while (i < n)
  invariant [pos]: (0 < d)
  invariant [usesdiv]: ((n / d) >= 0)
  { i := (i + 1); }
};
```

`pos` is precisely what makes `usesdiv` well-defined. Core emits:

```
Label: loop_invariant_usesdiv_calls_Int.SafeDiv_0
Obligation: !(d@1 == 0)          <-- no assumptions at all
Result: ❌ fail
```

The obligation has an empty assumption set: `invAsserts` is a `flatMap` over
invariants with no accumulator, so invariant *k* cannot rely on invariants
*0..k-1*.

Core already does the right thing for the *same dependency* in a contract,
because `mkContractWFProc` chains assert-then-assume per clause
(`PrecondElim.lean:146` `processCondition`, used from `:166`):

```
procedure Contract(n : int, d : int)
spec { requires (0 < d); requires ((n / d) >= 0); }
```
```
Label: Contract_pre_Contract_requires_1_calls_Int.SafeDiv_0
Assumptions:
Contract_requires_0: 0 < d@1     <-- earlier clause assumed
Obligation: !(d@1 == 0)
Result: ✅ pass
```

So the chaining discipline exists and is understood in this codebase. It is
simply unavailable to loops, for want of a place to put it.

## Why there is no good spot today

Walk every existing position in Core and ask: can the invariant-WF proof go
here? Let the loop be `while (G) invariant I { S }`, and write `L` for the
arbitrary mid-loop state — the loop head after the havoc.

**(a) Before the loop.** This is what Core does. It proves WF of `I` in the
pre-state. But `I` is assumed and re-asserted at `L`, over the havoc'd
loop-carried variables — a *strictly weaker* state. Pre-state WF neither implies
nor is implied by WF at `L`. Defect 1 is exactly this. Unfixable by
construction: the pre-state is the wrong state.

**(b) At the top of the body.** Tempting, and wrong twice over. The body only
runs when `G` holds, so a zero-iteration loop would skip the check even though
`I` is still assumed on the exit path (`exit_assumes`,
`InsertLoopInvariantAsserts.lean:154`). And the top of the body is *after*
`assume(I)` — `new_body := mid_assumes ++ measure_pre ++ bss ++ ...`
(`InsertLoopInvariantAsserts.lean:174`) puts `mid_assumes` first. Proving `I`
well-defined while already assuming `I` is circular, and an ill-defined `I` can
make its own WF obligation vacuous.

**(c) At the end of the body.** Where `guard_end` / `measure_end` go. Same
zero-iteration hole as (b), and still downstream of `mid_assumes`.

**(d) After the loop.** `I` has already been assumed at `L` and at exit
(`exit_assumes`). Too late.

**(e) In a separate synthesized procedure**, as `PrecondElim` does for contracts
via `mkContractWFProc` (`PrecondElim.lean:166`). This works for contracts
because a contract is checked against a *fresh, arbitrary* state that a
procedure signature fully describes — inputs are `nondet`, so the WF procedure
can reconstruct that state from the header alone. A loop head is not
reconstructible that way: it depends on which variables the body writes (Core
computes this internally — `Block.modifiedVars` minus `Block.definedVars`,
`LoopElim.lean:114-116`), on enclosing locals, and on the enclosing path
condition. Loops have no `modifies` clause to hand a synthetic procedure. There
is no signature to build the procedure from.

**(f) A user-written `assert` before the loop.** Same state as (a): wrong state,
and it puts the burden on the user for an obligation the tool generates.

**(g) A labeled `block` around the loop** (`block_statement`,
`Grammar.lean:351`). A block introduces a *label*, not a *state*. It cannot name
the havoc'd loop-head state, which is synthesized inside `LoopElim`
(`havocd`, `LoopElim.lean:117`) and does not exist in the source program.

The pattern: every existing slot is either in the wrong state (a, d, f), after
`assume(I)` (b, c), unreachable on the zero-iteration path (b, c), or unable to
name the loop-head state at all (e, g). **The needed program point — at `L`,
after the havoc, before `assume(I)` — is not expressible.**

This is not an oversight in `PrecondElim`; it is a gap in Core's statement
grammar. `Imperative.Stmt` (`Strata/DL/Imperative/Stmt.lean:31-56`) has `cmd`,
`block`, `ite`, `loop`, `exit`, `funcDecl`, `typeDecl`. The loop constructor
(line 46) is

```lean
| loop     (guard : ExprOrNondet P) (measure : Option P.Expr)
           (invariants : List (String × P.Expr))
           (body : List (Stmt P Cmd)) (md : MetaData P)
```

`body` is the only statement list a loop owns, and it is governed by the guard.
There is no second list, and no list that runs at `L` unconditionally.

## Why the `$w$loop#0` trick is what you get without it

Dafny's encoding:

```
// $w$loop#0 is unconstrained: Boogie must verify for both values
while (true)
  invariant $w$loop#0 ==> J;
  free invariant $w$loop#0 ==> $HeapSucc(...) && ...;
{
    if (!$w$loop#0) {
        // arbitrary loop-head state; J is NOT assumed here
        <check WF of J, conjunct by conjunct, assuming earlier ones>
        assume false;
    }
    // here $w$loop#0 holds, so J *is* assumed
    <check WF of guard>
    if (!guard) { break; }
    <body>
    // must re-establish $w$loop#0 ==> J
}
```

Read structurally, this is a *simulation of the missing program point*. Each
moving part exists only to manufacture what a native construct would give
directly:

- **`$w$loop#0` unconstrained** creates two loop-head copies out of one, since
  the language offers one entry point where two are needed.
- **`invariant $w$loop#0 ==> J`** guards the invariant so the `¬$w$loop#0` copy
  reaches the head *without* `J` assumed. This is the only trick available for
  suppressing `assume(I)` at a point the encoder does not control — precisely
  obstacle (b)/(c) above.
- **`if (!$w$loop#0) { ... assume false; }`** carves the WF-checking region out
  of the body, then severs it so it contributes no path to the real iteration.
- **`assume false`** is load-bearing: without it the WF block would fall through
  and be required to re-establish `J`.
- **conjunct-by-conjunct, assuming earlier ones** is Defect 2's chaining — the
  discipline Core already has for contracts.

The costs of paying for a program point in encoding rather than in syntax:

1. **Soundness rests on an `assume false`.** Every consumer of the IR must know
   that this region is severed. Core treats `assume false` regions as a known
   hazard already (`Strata/DL/Imperative/EvalContext.lean:247`,
   `Strata/DL/Imperative/CmdEval.lean:186`).
2. **`while (true)` + `break`.** Core's loop guard is `ExprOrNondet`
   (`.det`/`.nondet`) and Core has no `break`. Reproducing the trick would mean
   encoding the guard test into the body and using `exit` with a synthetic block
   label — discarding the structured `while (G)` form that
   `InsertLoopInvariantAsserts`, `StructuredToUnstructured` and the GOTO backend
   all consume. The GOTO backend needs real invariants on the backward edge
   (`#spec_loop_invariant`); an `$w$loop#0 ==> J` invariant is not one, and
   `Strata/Languages/GOTO/CFGToCProverGOTO.lean:41-49` already tracks invariant
   loss on the CFG path as a known gap.
3. **`free invariant` does not exist on Core invariants.** Invariants are
   `List (String × P.Expr)` with no per-invariant flag. `free` exists only on
   procedure specs (`Procedure.CheckAttr`, `Procedure.lean:214-219`;
   `Grammar.lean:355-360`). The trick needs it.
4. **Every VC's assumption set is polluted** by `$w$loop#0`. Diagnostics,
   SARIF output (`Strata/Languages/Core/SarifOutput.lean`) and counterexample
   models would all surface a variable with no source counterpart. Core has
   invested in the opposite: per-invariant provenance threaded through metadata
   because the IR lacks a slot for it (`MetaData.lean:326-341`;
   consumed at `InsertLoopInvariantAsserts.lean:130-136`).
5. **Model quality degrades.** Both loop phases already demote models to
   `modelToValidate` when a path condition mentions their assume prefixes
   (`InsertLoopInvariantAsserts.lean:~200`, `LoopElim.lean:147-152`). Adding an
   unconstrained boolean to every loop-head path condition widens that.
6. **Each producer reinvents it.** Laurel, Python, C_Simp and `BoogieToStrata`
   would each need the encoding, and `Strata/Languages/C_Simp/Verify.lean:96-110`
   is already a divergent copy of the invariant-assert recipe.

The trick is a reasonable adaptation for Boogie, whose statement grammar is
fixed and which is a *target*. Core is neither: it is the layer we control, and
the layer whose job is to give producers a place to say this.

## Proposal

Add a **pre-invariant-proof block** to Core's loop: a statement list that
executes at the loop head, over the havoc'd loop-carried state, *before* any
invariant is assumed.

### Semantics

The natural home is `InsertLoopInvariantAsserts`, which already owns the
invariant VCs and the body decoration. For
`while (G) proving { P } invariant I { S }`, `new_body`
(`InsertLoopInvariantAsserts.lean:174`) becomes:

```
new_body := P ++ mid_assumes ++ measure_pre ++ bss ++ maintain_asserts ++ measure_post
                 ^^^^^^^^^^^ P precedes assume(I)
```

and after `LoopElim` (`LoopElim.lean:128-132`) composes, the loop head reads:

```
assert(I); assume(I);          -- VC1 (pre-state), unchanged
if (G) {
  havoc(M);                    -- arbitrary loop-head state
  assume(G);
  { P }                        -- NEW: pre-invariant-proof block.
                               --   runs here, before assume(I);
                               --   may not assume I; may not write M
  assume(I);                   -- mid_assumes
  ...                          -- body, VC2, measure VCs: unchanged
}
```

Key properties, mapped to the obstacles above:

- It runs at `L`, over havoc'd `M` — the state where `I` is assumed and
  re-asserted. Fixes (a)/(d)/(f).
- It runs *before* `mid_assumes`. Fixes (b)/(c), with no `$w$loop#0 ==> J`
  guarding and no `assume false`.
- It is attached to the loop, so it needs no signature and no `modifies` clause
  — Core already computes `M` internally. Fixes (e).
- The loop keeps its structured `while (G)` shape and its real invariants, so
  `StructuredToUnstructured` and the GOTO backend are unaffected.

One wrinkle worth deciding: as sketched, `P` sits *inside* the `if (G)` that
`LoopElim` mints, so a zero-iteration loop would not run it — the same hole as
(b). That is acceptable only if the exit-path `assume(I)` is also justified. Two
options: place `P` in the body (as above) and accept that the exit-path
`exit_assumes` are justified transitively by VC1 + VC2; or have `LoopElim` emit
`P` once outside the `if`, over a havoc'd state. The first is a smaller change
and is what the sketch shows; the second is strictly stronger. This is the main
open design question alongside restriction 2 below.

Two restrictions make the block sound and keep it out of the way of the VCs:

1. **It may not assume the invariant** — that is the point of its position.
2. **It may not modify `M`** (nor any enclosing variable). It is a proof region:
   `assert`, `assume` over its own locals, `init` of fresh locals. With no
   writes to `M` there is no need for an `assume false` to sever it, because it
   cannot perturb the iteration state. This is what makes the construct safe *by
   typing* rather than by encoding discipline.

Restriction 2 is the substantive design question and the main thing worth
review: enforce it syntactically (restrict the block's statement forms), or check
it (reject writes to `M` with a diagnostic, as `InsertLoopInvariantAsserts`
already rejects `while *` carrying `decreases`,
`InsertLoopInvariantAsserts.lean:113-118`)?

### Where generated invariant-WF obligations go

The invariant-WF asserts move out of `PrecondElim`'s pre-state emission and into
the pre-invariant-proof block, **chained** — reusing `processCondition`
(`PrecondElim.lean:146`), the function that already implements this for
contracts:

```
{ P } = for each invariant (lbl, I_k) in order:
          assert WF(I_k);     -- may rely on I_0..I_{k-1}
          assume I_k;
```

This fixes Defect 1 (right state) and Defect 2 (chaining) together, and makes
loops consistent with contracts. The local `assume I_k` inside `P` is the
chaining assumption for later clauses' WF only; the loop-head `assume(I)` still
happens after `P`, via `mid_assumes`.

Because `PrecondElim` runs *before* `InsertLoopInvariantAsserts`
(`Verifier.lean:1504-1505`), the cleanest split is: `PrecondElim` emits the
chained WF statements into the loop's new `proving` field, and
`InsertLoopInvariantAsserts` positions that field. `PrecondElim` never needs to
know about the havoc'd state — it only needs a slot to put the statements in.
That slot is the whole feature.

The guard's WF arguably belongs in `P` too, since the guard is evaluated at `L`.
That would subsume today's `loop_guard` / `loop_guard_end` pair. The current
double-check is at least state-correct, so this is a follow-up, not a
prerequisite.

### Surface syntax

Following `Grammar.lean:327-340`, one new optional category before `Invariants`:

```
category ProvingBlock;
op proving_mk (b : Block) : ProvingBlock => "proving " b:0 "\n";

op while_statement (annots : Option MetadataAnn, c : ExprOrNondet,
                    p : Option ProvingBlock, m : Option Measure,
                    is : Invariants, body : Block) : Statement =>
  annots:0 "while " c:0 "\n" p:0 m:0 is body:0;
```

`proving` is a suggestion; `prelude`, `at_head` and `before_invariant` all read
acceptably. Since the block is generated by `PrecondElim` in the common case,
the syntax matters mainly for hand-written Core, tests and round-tripping — but
it must exist, because Core programs round-trip through `FormatCore.lean`.

### Sketch of the change

`loop` gains one field:

```lean
| loop (guard : ExprOrNondet P) (measure : Option P.Expr)
       (proving : List (Stmt P Cmd))          -- NEW
       (invariants : List (String × P.Expr))
       (body : List (Stmt P Cmd)) (md : MetaData P)
```

Touch points (the `.loop` arity change makes the compiler enumerate most of
these):

- `Strata/DL/Imperative/Stmt.lean:46` — constructor, plus `Stmt.inductionOn`
  (`:71`, loop case `:81`/`:100`), `Stmt.sizeOf` (`:119`), the `BEq` case
  (`:147`), `noFuncDecl` (`:212`) and the expression map (`:246`).
- `Strata/Languages/Core/Statement.lean` — the `.loop` cases at `:220`, `:256`,
  `:338`, `:377`, `:428`, `:486`, `:526`, `:578`. Note `modifiedVarsTrans`
  must *exclude* the proving block, per restriction 2 — which doubles as the
  check for it.
- `Strata/Languages/Core/StatementType.lean:142` — typecheck the block (and the
  second `.loop` case at `:271`).
- `Strata/Transform/InsertLoopInvariantAsserts.lean:174` — position `P` before
  `mid_assumes`.
- `Strata/Transform/LoopElim.lean:96-134` — `removeLoop` must accept a loop
  whose `proving` field is already empty by then, or thread it; its existing
  "still carries invariants/measure" guard (`:100-103`) is the pattern to follow.
- `Strata/Transform/PrecondElim.lean:287-315` — redirect `invAsserts` into the
  `proving` field, chained via `processCondition`.
- `Grammar.lean:327-340` / `Translate.lean:1618-1624` /
  `FormatCore.lean:986-988` (with `invariantsToCST` `:1025`,
  `measureToCST` `:1039`) — syntax round-trip.
- `Strata/Languages/C_Simp/Verify.lean:96-110` — the parallel copy.
- `Strata/Languages/Core/StatementSemantics.lean:332` (`coreIsAtAssert`) and the
  semantics proofs.
- A `GenKind` case in `Translate.lean:276` / `nextLabel` (`:318`) if the block
  owns default assertion labels.

`ObligationExtraction` (`ObligationExtraction.lean:80`) needs no change: the
block is lowered away before it runs, like the loop itself.

### Migration

The field is a list, so existing loops take `[]` and behave as today. The
observable change is that generated invariant-WF assert *labels* move from the
pre-state into the loop and gain chained assumptions. Expected-output tests
covering `loop_invariant_*_calls_*` will need updating —
`Examples/expected/*.core.expected`, `StrataTest/Transform/PrecondElim.lean`,
`StrataTest/Transform/LoopElim.lean`,
`StrataTest/Transform/InsertLoopInvariantAssertsTest.lean`. Some programs that
pass today will start failing correctly (Defect 1); some that fail today will
start passing (Defect 2).

## Alternative considered: fix the passes without touching the grammar

Move invariant-WF generation out of `PrecondElim` and into
`InsertLoopInvariantAsserts`, which does synthesize the loop-head state and could
emit chained WF asserts directly ahead of `mid_assumes`.

This would fix both defects without a grammar change, and is the smaller patch.
It is worth doing if the grammar change is judged too invasive. But it buys less:

- It puts expression-level WF knowledge (the `Factory`, `collectWFObligations`)
  into a pass whose job is the VC recipe, and duplicates it into
  `C_Simp/Verify.lean`, which synthesizes the same state independently.
- It gives *Core-generated* obligations a home but not *user-written* ones. A
  producer that wants to prove a lemma at the loop head — a
  quantifier-instantiation hint, a frame fact, a bitvector identity — still has
  nowhere to put it, and the `$w$loop#0` pressure returns for that use case.
- `PrecondElim`'s contract path stays structurally different from its loop path
  for no reason a reader can see.

The grammar change is the one that makes the program point *nameable*, which is
what both the WF problem and the proof-hint problem actually need.

## Related

- `docs/CoreToGOTO_Gaps.md` — invariants must survive to the backward GOTO edge
  (`#spec_loop_invariant`); an argument against any encoding that rewrites them
  into implications.
- `Strata/Languages/C_Simp/Verify.lean:96-110` — a second, divergent copy of the
  invariant-assert recipe; a per-producer encoding would need the trick twice.
