# Structured-to-Unstructured Loop Extension (v3) — Design Document

Branch: `htd/structured-to-unstructured-loops-v3`
Commit: 0762a29f5bfd1c2521f35f0e50b7c5e6c3ee3020
Forked from: v2 skeleton at 187a81931 (baseline proof state
`origin/htd/structured-to-unstructured-small-step-proof`, commit c81249b49).

Status: 0 sorries, 0 axioms, full project builds green (489 jobs).

---

## 1. Goal

Extend the structured-to-unstructured (str→unstr) correctness proof so that
`while` loops are admitted by the simulation theorems, closing all remaining
`sorry`s in `Strata/Transform/StructuredToUnstructuredCorrect.lean`.

Loops are admitted ONLY when ALL of the following hold:

| Predicate | Meaning |
|---|---|
| `Block.loopBodyNoInits` | the body has no `init` (variable-declaration) commands at any nesting depth |
| `Block.loopHasNoInvariants` | the loop carries an empty invariants list (no `invariant` clauses) |
| `Block.noMeasureLoops` | the loop carries no `measure` / termination-metric clause |
| det guard | the loop guard is `.det _` (a deterministic boolean expression), NOT `.nondet` |

These are exactly the loops whose CFG lowering is a clean back-edge with no
havoc, no auxiliary assertion injection, and no source-side variable
introduction — the cases where the structured and unstructured executions stay
in lockstep under the small-step semantics.

---

## 2. The strengthened `simpleShape` (det loops only)

`Stmt.simpleShape` (in `Strata/DL/Imperative/Stmt.lean`) is the syntactic
admissibility predicate threaded through the simulation theorems. Its `.loop`
arm was strengthened to reject nondeterministic guards:

```lean
@[expose] def Stmt.simpleShape (s : Stmt P (Cmd P)) : Bool :=
  match s with
  ...
  | .loop guard _ _ bss _ =>
      (match guard with | .det _ => true | .nondet => false) && Block.simpleShape bss
```

Two consequences:

1. **Nondet loops are statically dischargeable.** In any simulation arm that is
   handed `Stmt.simpleShape (.loop .nondet ...) = true`, the hypothesis is
   `false = true`, so the arm closes by `absurd ... (by simp [Stmt.simpleShape])`.
   No nondet-loop proof obligation ever reaches the main body.

2. **Det loops expose their guard.** A new lemma extracts the guard expression:

   ```lean
   theorem Stmt.simpleShape_loop_guard_det :
       Stmt.simpleShape (.loop g m is body md) = true → ∃ ge, g = .det ge
   ```

   The existing `Stmt.simpleShape_loop_body` lemma was updated to use
   `unfold + cases on guard` (a bare `simp only` no longer makes progress on the
   strengthened definition).

The module docstring of `Stmt.lean` was updated to note that nondet loops are
excluded from `simpleShape`.

---

## 3. The three admissibility predicates

All three are `Bool`-valued, defined `@[expose]` and lifted to block level
(`Block.foo ss := ss.all Stmt.foo`-style recursion). For each, the file
provides a `_cons_iff` decomposition (head/tail), branch/block recursion
lemmas, and a leaf lemma that projects the relevant fact out of the `.loop`
constructor.

### `Block.loopBodyNoInits` (`Stmt.lean:315`)

```lean
| .loop _ _ _ bss _ => (Block.initVars bss).isEmpty && Block.loopBodyNoInits bss
```

Recursively requires every loop in the term to have a body whose `initVars` are
empty. This is what makes the loop's CFG lowering avoid a havoc/re-declaration
block: with no inits in the body, `Block.initVars (.loop ... :: rest) =
Block.initVars rest`, so the loop contributes nothing to the surrounding init
set and the body re-enters its entry block on each back-edge with the same
variable footprint.

### `Block.loopHasNoInvariants` (`Stmt.lean:394`)

```lean
| .loop _ _ invs bss _ => invs.isEmpty && Block.loopHasNoInvariants bss
```

Requires the invariants list to be empty. With invariants present, the
translator injects `assert`/`assume` blocks at the loop head that have no
structured-side counterpart in the small-step semantics, breaking lockstep.
The leaf lemma `Stmt.loopHasNoInvariants_loop_invs` yields `invariants = []`.

### `Block.noMeasureLoops` (`Stmt.lean:474`)

```lean
| .loop _ m _ bss _ => m.isNone && Block.noMeasureLoops bss
```

Requires the measure/termination-metric clause to be `none`. A measure clause
likewise triggers translator-side instrumentation absent from the structured
small-step run. The leaf gives `measure = .none`.

In the `.loop` dispatch arm these three combine to rewrite the head statement
to the canonical admitted shape `.loop (.det guardExpr) none [] body md :: rest`
via three successive `subst`s.

---

## 4. Why the `LoopArm` namespace was deleted (the forward-reference issue)

The v2 skeleton carried a `namespace LoopArm` containing six helpers:
`peel_off_one_iteration_det`, `step_loop_iteration_det`, `loop_iterations_det`,
`loop_det_decompose_h_gen`, `loop_arm_simulation`, `loop_arm_simulation_to_cont`.

The last two (`loop_arm_simulation`, `loop_arm_simulation_to_cont`) had to
recurse on the body and on `rest` — i.e. they needed to call
`stmtsToBlocks_simulation` / `stmtsToBlocks_simulation_to_cont`. But those
simulation theorems live **inside** the `mutual` block and are defined **after**
the namespace. A standalone helper that calls them is a forward reference:
Lean cannot define `LoopArm.loop_arm_simulation` before the mutual block, and
cannot place it inside the mutual block while it lives in a separate namespace
with its own `termination_by`. The skeleton papered over this with two `sorry`s
in `loop_det_decompose_h_gen` plus stubbed iteration lemmas.

The fix removes the namespace entirely and **inlines the loop-arm proof bodies
directly into the `.loop` dispatch arms** of `stmtsToBlocks_simulation`
(line ~5583) and `stmtsToBlocks_simulation_to_cont` (line ~8290). From there,
the recursive calls to the simulation theorems are ordinary mutual-recursion
calls — the exact same mechanism the `.block` and `.ite` arms already use
(e.g. body recursion at line 5799, `rest` recursion at line 5890). Termination
is the shared `termination_by sizeOf ss` / `decreasing_by simp_wf; omega`.

The genuinely reusable, **non-recursive** pieces (those depending only on CFG +
small-step stmt semantics, never on the simulation theorems) were kept as
private helpers in a new `namespace InlineLoopHelpers` placed *before* the
mutual block. Its docstring explicitly states these helpers MUST NOT call the
simulation theorems, preserving the no-forward-reference discipline.

---

## 5. The inline proof strategy

### 5.1 Helpers in `InlineLoopHelpers`

`ReflTransT`-inversion ("length-indexed") lemmas that peel one structural layer
off a small-step run and return the residual run plus a strict length decrease
(the length index drives the iteration induction):

| Helper | LoC | Role |
|---|---|---|
| `seqT_reaches_terminal'` | 18 | `.seq → .terminal` inversion (re-declared because the upstream version is private) |
| `stmtsT_cons_terminal'` | 13 | `.stmts (s::rest) → .terminal` inversion |
| `seqT_reaches_exiting'` | 28 | `.seq → .exiting` (Sum: inner-exit vs inner-term-then-tail-exit) |
| `stmtsT_cons_exiting'` | 24 | `.stmts (s::rest) → .exiting` inversion |
| `blockT_none_reaches_terminal'` | 22 | unlabeled `.block .none → .terminal` projection |
| `blockT_none_reaches_exiting'` | 22 | unlabeled `.block .none → .exiting` exit-propagation |
| `loop_det_decompose_h_gen` | 79 | translator-shape decomposition of `stmtsToBlocks` on the admitted loop |

`loop_det_decompose_h_gen` was the 2-`sorry` skeleton stub. It was rewritten to
the **actual** v3 translator shape: the fictional `kNext$`-gen step and the
join block of the skeleton were removed, and the emitted block list is
`accumBlocks ++ [(lentry, lentryBlk)] ++ bodyBlocks ++ restBlocks` matching what
`stmtsToBlocks` actually produces for `.loop (.det g) none [] body md :: rest`.

### 5.2 Nat-bounded induction over iteration count

The loop arm proves, by induction on the **length index** of the structured
small-step run, that for any number of loop iterations the structured run and
the CFG run stay in lockstep:

1. **Decompose** `h_gen` with `loop_det_decompose_h_gen` to learn the exact
   block layout (entry block `lentry`, body blocks, rest blocks, generator
   threading `gen → gen_r → gen_le → gen_b → gen_f`).
2. **Split** the terminal/exiting run of `[loop] ++ rest` into a loop run and a
   `rest` run with `stmts_append_terminates`.
3. **Iterate.** Each iteration is: evaluate the det guard; if true, run the body
   (recursive `stmtsToBlocks_simulation` call on `body` with a back-edge
   continuation), which strictly shrinks the length index, then recurse on the
   shorter run; if false, exit to the loop's successor. The strict length
   decrease from the `ReflTransT`-inversion helpers is what discharges
   termination of the iteration induction (it is bounded by the length of the
   structured run, not by a loop-trip count, so non-terminating source loops
   never arise — a terminal small-step run is finite by construction).
4. **Continue** with the `rest` recursion (`stmtsToBlocks_simulation` on `rest`)
   to reach the final config.

The arm carries a strengthened iteration lemma (`loop_iterations_det`) with a
`freshVars`-preservation conjunct so that the generator/freshness invariants the
surrounding mutual proof relies on are maintained across every back-edge.

The `_to_cont` arm (line ~8290) mirrors this but targets the case where the
structured run ends in `.exiting label` caught by an `exitConts` entry, reaching
the labeled CFG continuation instead of the fallthrough.

Inlined sizes: simulation `.loop` arm ≈ 346 LoC; `_to_cont` `.loop` arm ≈ 386 LoC.

---

## 6. Adversarial verification: 6 skeptics across 2 rounds

The proof was subjected to two independent rounds of adversarial review, three
skeptics per round (6 total), each tasked with finding an unsound step, a
hidden axiom, a circular dependency, a forward reference, or a vacuous
hypothesis.

- **Round 1 (Verify1):** sound, sound, sound.
- **Round 2 (Verify2):** sound, sound, sound.

Consensus across both rounds: **all 6 skeptics report sound.** No skeptic found
an `axiom`, a `True := trivial` placeholder, a `sorry`, an `admit`, a
`native_decide`/`implemented_by` escape hatch, or a circular/forward reference.
The mutual recursion is the only recursion and is justified by a genuine
`termination_by sizeOf ss` with `decreasing_by simp_wf; omega`.

Independent re-verification performed for this report:
- `grep -niw sorry` over both files: 0 matches.
- `grep -nE '^\s*axiom\b'` over both files: 0 matches.
- `grep -n 'admit'` over the proof file: 0 matches.
- `grep -n 'namespace LoopArm\|LoopArm\.'`: 0 matches (namespace fully removed).
- Full `lake build`: "Build completed successfully (489 jobs)", exit 0, no
  errors and no `declaration uses 'sorry'` warnings (only cosmetic
  `linter.unusedSimpArgs` and unused-section-variable warnings remain).

---

## 7. Remaining sorries

**0.** Both `.loop` arm sorries (terminal and `_to_cont`) are closed. There are
no remaining `sorry`s, `admit`s, or `axiom`s anywhere in
`StructuredToUnstructuredCorrect.lean` or `Stmt.lean`.

---

## 8. LoC delta vs baseline

Baseline = `origin/htd/structured-to-unstructured-small-step-proof` (c81249b49).

| File | Baseline | v3 | Δ |
|---|---|---|---|
| `Strata/Transform/StructuredToUnstructuredCorrect.lean` | 7331 | 8945 | +1614 |
| `Strata/DL/Imperative/Stmt.lean` | 554 | 833 | +279 |
| **Total** | **7885** | **9778** | **+1893** |

`git diff --stat` over the two files: +1916 insertions, −23 deletions
(net +1893). The +279 in `Stmt.lean` is the strengthened `simpleShape`, the
three admissibility predicates with their full lemma families, and the two new
`simpleShape` lemmas. The +1614 in the proof file is the two inlined loop arms
(≈732 LoC combined) plus the `InlineLoopHelpers` namespace (≈206 LoC of helper
lemmas including the rewritten `loop_det_decompose_h_gen`), net of the deleted
372-line `LoopArm` namespace.

---

## 9. Recommended next steps

1. **Land v3 onto the small-step proof line.** v3 is sorry/axiom-free and builds
   green for the whole project; it supersedes the v2 skeleton. Open a PR from
   `htd/structured-to-unstructured-loops-v3` into the small-step proof branch.
2. **Add end-to-end runtime coverage for the `.cfg` (unstructured) form with a
   loop.** Per the standing project memory, `StrataTest/.../Examples/*.lean`
   SMT-goldens exercise only the structured form; no test drives a lowered loop
   through `ProcedureEval`. Add a golden that round-trips a det `while` with no
   inits/invariants/measure so the newly-proved path has live coverage.
3. **Clear the cosmetic `linter.unusedSimpArgs` warnings** introduced by the
   inlined arms (lines 4401, 5731, 5930, 6983, 8421). Trim the unused
   `StateT.pure` / `List.nil_append` / `List.append_nil` simp args. Mechanical;
   no proof risk.
4. **Relax the admissibility predicates incrementally.** The det-only,
   no-inits/invariants/measure fragment is the lockstep core. The natural next
   extensions, in increasing difficulty: (a) loops whose body declares inits
   (requires modeling the translator's havoc/re-declaration block — see the
   `.loop` axiom-unprovability note); (b) loops with invariants (requires
   relating the injected `assert`/`assume` blocks to a structured-side
   obligation); (c) nondet guards (requires the demonic-branch simulation that
   `simpleShape` currently excludes). Each is a separate workstream and should
   not be folded into the lockstep proof.
5. **Promote the `InlineLoopHelpers` `ReflTransT`-inversion helpers** if other
   arms (block/ite) could reuse them; several are general small-step inversions
   that currently duplicate private upstream lemmas (`seqT_reaches_terminal'`
   was re-declared only because the upstream is private — consider de-privatising
   upstream and deleting the `'` copy).
