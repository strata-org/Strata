# Design Plan: Increment/Decrement Operators for Laurel

**Status:** Draft for review — no code changed yet.
**Date:** 2026-06-02

Adds Java-style `++` / `--` operators to the Laurel dialect, usable both as
statements (`x++;`) and inside expressions (`int y := (x++) + (x++);`), in
prefix and postfix forms.

---

## 1. Semantics (Java-style)

| Form | Surface | Value yielded | Side effect |
|------|---------|---------------|-------------|
| Prefix increment | `++x` | new value (`x+1`) | `x := x+1` |
| Postfix increment | `x++` | old value (`x`) | `x := x+1` |
| Prefix decrement | `--x` | new value (`x-1`) | `x := x-1` |
| Postfix decrement | `x--` | old value (`x`) | `x := x-1` |

As a statement the yielded value is discarded, so prefix and postfix are
equivalent there. The distinction only matters inside a larger expression.

**Terminology note:** the request said "infix and suffix." `++`/`--` are unary,
so there is no true infix form. This plan reads **infix = prefix (`++x`)** and
**suffix = postfix (`x++`)**. *Please confirm.*

---

## 2. Key finding — the `++` token already exists

`++` is currently Laurel's **string concatenation** operator:

```
op strConcat (lhs, rhs): StmtExpr => @[prec(60), leftassoc] lhs " ++ " rhs;
```

It is used in real programs, e.g. `var result: string := s1 ++ s2;`
(`StrataTest/Languages/Laurel/tests/test_strings.lr.st`). `--` is currently
free (subtraction is a single `-`; comments use `//`).

The DDM Pratt parser keeps **separate tables** for *leading* parsers (operator
at the start of an operand — prefix/atom) and *trailing* parsers (operator
after an operand — infix/postfix). See
`StrataDDM/StrataDDM/Parser.lean` (`opSyntaxParser` / `checkLeftRec`) and
`StrataDDM/StrataDDM/Util/PrattParsingTables.lean`. Consequences:

- **Prefix `++x` / `--x`** are *leading* parsers. They do **not** collide with
  the *trailing* `++` (strConcat). Clean.
- **Postfix `x++` / `x--`** are *trailing* parsers. `x++` therefore shares the
  trailing token `++` with strConcat. The trailing table is a multimap keyed on
  the first token, so both can coexist, but `a ++ b` becomes genuinely
  ambiguous (`(a++) b` vs `a ++ b`), and the Pratt parser does only limited
  backtracking. **This is the main risk.**

`--` (prefix and postfix) only needs registering `--` as a token; no existing
conflict.

### Options for postfix (decision needed)

- **P1 — Implement + validate.** Add postfix anyway, then empirically test `++`
  against strConcat. If `a ++ b` breaks, apply a mitigation.
- **P2 — Disambiguate strConcat.** Rename strConcat's surface token (e.g. to a
  `concat` keyword). Clean parsing, but a **breaking change** to existing
  `.lr.st` programs and tests.
- **P3 — Prefix only (for now).** Ship `++x` / `--x` (clean, zero conflict),
  defer postfix until the token question is resolved.

**Recommendation:** start with prefix (clean), implement postfix behind an
empirical parser test (P1), falling back to P3 if `a ++ b` regresses. A focused
parse test will run *before* building the rest.

---

## 3. AST representation — desugar in the translator (recommended)

**Do not add a new `StmtExpr` constructor.** `computeExprType`,
`resolveStmtExpr`, `collectStmtExpr`, `mapStmtExprM`, and the Core translator
are all **exhaustive** matches; a new constructor forces edits to every one.
Instead, desugar to existing nodes in `ConcreteToAbstractTreeTranslator`:

| Surface | Desugars to |
|---------|-------------|
| `++x` | `(x := x + 1)` |
| `x++` | `((x := x + 1) - 1)` |
| `--x` | `(x := x - 1)` |
| `x--` | `((x := x - 1) + 1)` |

Rationale: a Laurel assignment **used as an expression already yields the new
value** (confirmed by existing tests, e.g. `T2_ImpureExpressions.lean` where
`(x := 2)` evaluates to `2`). So:

- Prefix reuses that directly.
- Postfix recovers the old value by subtracting/adding the delta from the new
  value.

The arithmetic trick needs **no fresh temporary and no type annotation**, so it
can run pre-resolution in the translator.

### Correctness check (hand-traced against the existing lift algorithm)

For `int y := (x++) + (x++);` with `x = 0`, desugared to
`((x := x+1) - 1) + ((x := x+1) - 1)`, the `LiftImperativeExpressions` snapshot
mechanism produces (program order):

```
$x_1 := x;   // 0
x := x + 1;  // x = 1
$x_0 := x;   // 1
x := x + 1;  // x = 2
var y := ($x_0 - 1) + (x - 1);   // (1-1) + (2-1) = 0 + 1 = 1
```

`y = 1`, `x = 2` — matches Java `(x++)+(x++)`.

The target must be an lvalue (`.Var` Local or Field), validated exactly as the
existing `assign` op does.

### Alternative (if preferred): new `.IncrDecr` node

Add an `.IncrDecr` `StmtExpr` constructor plus a dedicated pre-`LiftImperativeExpressions`
elimination pass. Pros: self-documenting IR, survives AST round-tripping, emits
a clean `x := x±1` in statement position (no dead snapshot — see §4). Cons:
touches every exhaustive match (`computeExprType`, `resolveStmtExpr`,
`collectStmtExpr`, `mapStmtExprM`, `AbstractToConcreteTreeTranslator`, and any
pass that pattern-matches `StmtExpr`). More files, more code.

---

## 4. Lowering through the pipeline

The existing **`LiftImperativeExpressions`** pass (pipeline step
`LiftExpressionAssignments`) already lowers assignments-in-expression-position
via snapshot variables, so prefix and **postfix-in-expression** work *for free*
once desugared.

**One gap:** a bare postfix **statement** `x++;` desugars to a `Sub`
`PrimitiveOp` at statement position, and `transformStmt` currently has no
`.PrimitiveOp` arm (it falls through unlifted and would reach Core
un-lowered). Fix with a small, general arm:

```lean
| .PrimitiveOp .. =>
    let _ ← transformExpr stmt        -- hoist embedded assignments
    let prepends ← takePrepends
    modify fun s => { s with subst := [] }
    return prepends
```

This is a correct general improvement (handles expression-statements). Cost:
postfix-as-statement leaves one **harmless dead snapshot** local
(`var $x_0 := x`) — it verifies fine, just slightly noisy in generated Core.
(The `.IncrDecr`-node alternative avoids this because `transformStmt` would emit
a clean `x := x±1`.)

**No changes** to resolution, type inference, heap parameterization, or the Core
translator, since everything is plain `.Assign` / `.PrimitiveOp`.

---

## 5. Scope / edge cases (first cut)

- **Type focus: `int`.** `++`/`--` on `real`/`float64` mixes `x` with the int
  literal `1` — needs checking whether `realVar + 1` type-checks (may require
  `1.0`). Bitvectors are not covered by `computeExprType`'s arithmetic arm.
  Tests scope to `int`; real/float64/bv noted as follow-ups.
- **Field targets (`obj#f++`):** supported as a **statement**
  (`obj#f := obj#f+1`). In expression position the lift pass only snapshots
  `.Local` targets, so field-target increment *in expressions* is out of scope
  (consistent with current lift-pass limitations). Expression-position tests use
  local `int` vars.

---

## 6. Grammar changes (`Strata/Languages/Laurel/Grammar/LaurelGrammar.st`)

```
// Prefix (leading) — precedence like neg/not (80)
op preIncr  (target: StmtExpr): StmtExpr => @[prec(80)] "++" target;
op preDecr  (target: StmtExpr): StmtExpr => @[prec(80)] "--" target;
// Postfix (trailing) — binds tightest (90), pending the §2 decision
op postIncr (target: StmtExpr): StmtExpr => @[prec(90)] target "++";
op postDecr (target: StmtExpr): StmtExpr => @[prec(90)] target "--";
```

Plus the required comment-bump in `Grammar/LaurelGrammar.lean` to trigger a
grammar rebuild (the `.st` file is not auto-tracked by the build).

---

## 7. Files to change

1. `Strata/Languages/Laurel/Grammar/LaurelGrammar.st` — 4 new ops.
2. `Strata/Languages/Laurel/Grammar/LaurelGrammar.lean` — comment bump.
3. `Strata/Languages/Laurel/Grammar/ConcreteToAbstractTreeTranslator.lean` —
   4 op cases desugaring to `.Assign` / `.PrimitiveOp`, with lvalue validation.
4. `Strata/Languages/Laurel/LiftImperativeExpressions.lean` — `.PrimitiveOp`
   arm in `transformStmt`.
5. *(Optional)* `AbstractToConcreteTreeTranslator.lean` — only if we keep an
   `.IncrDecr` node; not needed for the desugaring approach.

---

## 8. Tests

- **Lift-level** (style of
  `StrataTest/Languages/Laurel/LiftExpressionAssignmentsTest.lean`, `#guard_msgs`
  on lowered Laurel text): assert exact lowering of `++x`, `x++`, and a bare
  `x++;` statement.
- **Verification-level** (style of
  `StrataTest/Languages/Laurel/Examples/Fundamentals/T12_Operators.lean` and
  `T2_ImpureExpressions.lean`): new `Tnn_IncrDecr.lean` exercising
  - statement use (`x++;`),
  - prefix vs postfix in expressions (`(x++)+(x++)` asserts old-value
    semantics; `(++x)+(++x)` asserts new-value),
  - use in a `for`-loop step,
  - an intentional failing `assert` to confirm error reporting.
- *(Optional)* an `Examples/.../*.lr.st` sample program.

---

## 9. Open decisions

1. **Postfix token conflict (§2):** P1 (try + validate), P2 (rename strConcat),
   or P3 (prefix-only first)?
2. **AST representation (§3):** desugar in translator (recommended, minimal)
   vs. new `.IncrDecr` node (cleaner IR, more files)?
3. **Scope (§5):** `int`-only for the first cut OK?

Once these are confirmed (especially #1), implementation proceeds with
`lake build` + tests. No files have been modified yet.
