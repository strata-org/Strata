# BoogieToStrata: CFG Emission for Unstructured Control Flow

## Problem

BoogieToStrata currently converts Boogie's goto statements into structured
while/if/exit blocks. This works for simple gotos (1-2 targets with matching
assume guards) but fails on:

- **3+ target gotos** — "Unsupported: goto with multiple targets"
- **2-target gotos without inverse assumes** — heuristic in
  `OppositeBlockCondition()` fails
- **Irreducible control flow** — overlapping loop regions rejected by
  `BuildLoopRegions()`

These failures block translation of SMACK-generated Boogie programs, which
use multi-target gotos extensively in both prelude procedures and user code
compiled from C.

## Solution

Emit Strata Core's native CFG syntax for procedures that contain gotos,
instead of structuring them. Strata Core now supports unstructured procedure
bodies (`Procedure.Body.cfg`) with the following syntax:

```
procedure name(params)
spec { ... }
cfg entry_label {
  label1: {
    stmt1;
    stmt2;
    goto label2;
  }
  label2: {
    branch (cond) goto label3 else label4;
  }
  label3: {
    return;
  }
};
```

## Design Decisions

### 1. Auto-detect per procedure

Each procedure is independently checked:
- **No gotos in body** → emit structured syntax (existing behavior, unchanged)
- **Any goto in body** → emit CFG syntax from flat blocks

A single Strata program can mix structured and CFG procedures. This maximizes
compatibility — procedures that work today continue to emit identical output.

**Why per-procedure:** Some Boogie programs have a mix of structured procedures
(pure computation) and unstructured procedures (lowered from C with complex
control flow). Forcing all to one format is unnecessary.

### 2. Map flat blocks directly to CFG syntax

Every Boogie procedure has a flat block list (`Implementation.Blocks`), even
when `StructuredStmts` exists. Each `Block` has:
- A label (string)
- A list of commands: `AssignCmd`, `AssertCmd`, `AssumeCmd`, `CallCmd`,
  `HavocCmd`, `YieldCmd`
- A `TransferCmd`: either `GotoCmd` (1+ label targets) or `ReturnCmd`

For CFG emission, we use these flat blocks directly:

| Boogie construct | Strata Core CFG syntax |
|------------------|----------------------|
| Block label | `label: { ... }` |
| `ReturnCmd` | `return;` |
| `GotoCmd` with 1 target | `goto L;` |
| `GotoCmd` with 2 targets | `goto L1, L2;` |
| `GotoCmd` with 3+ targets | Nested binary nondet (see below) |
| Entry block | First block in Boogie's block list → `cfg entry_label { ... }` |

### 3. Nested binary nondet for 3+ target gotos

Boogie's `goto L1, L2, L3;` is nondeterministic — execution proceeds to any
one target. Strata Core's grammar supports at most 2-target nondet goto
(`goto L1, L2;`). We encode N-target gotos as a chain of synthetic blocks:

**Example:** `goto L1, L2, L3, L4;` becomes:

```
goto L1, __nondet_1;
...
__nondet_1: {
  goto L2, __nondet_2;
}
__nondet_2: {
  goto L3, L4;
}
```

Each synthetic block chooses nondeterministically between one real target and
a continuation block. The last block handles the final 2 targets directly.
This preserves the nondeterministic semantics exactly: each original target
is reachable with nonzero probability.

**Label naming:** Synthetic labels use `__nondet_{N}` where N is a global
counter, avoiding collisions with user labels.

### 4. Always nondet goto (no conditional detection)

Boogie encodes conditional branches as:
```
goto then_block, else_block;
```
where `then_block` starts with `assume cond;` and `else_block` starts with
`assume !cond;`. The existing translator tries to detect this pattern
(`OppositeBlockCondition`) and emit `if (cond) { ... } else { ... }`.

For CFG emission, we skip this detection entirely and always emit nondet
gotos. The assume commands inside the target blocks already enforce the
condition correctly — nondeterministic execution to a block that immediately
assumes a false condition is equivalent to not going there.

**Why:** The detection heuristic is fragile (syntactic matching on inverse
expressions) and adds complexity. With CFG emission, the assume guards work
naturally. The Strata verifier and CBMC pipeline handle assume-guarded nondet
correctly.

### 5. Command translation within CFG blocks

Commands inside CFG blocks use the same translation as structured procedures:

| Boogie command | Strata Core CFG statement |
|----------------|--------------------------|
| `x := expr;` | `x := expr;` |
| `assert expr;` | `assert expr;` |
| `assume expr;` | `assume expr;` |
| `call P(args);` | `call P(args);` |
| `havoc x;` | `havoc x;` |

The existing `VisitAssignCmd`, `VisitAssertCmd`, `VisitAssumeCmd`, etc. methods
are reused. Only the procedure-level structure and transfer command emission are
new.

### 6. Entry block identification

Boogie's `Implementation.Blocks[0]` is always the entry block. We emit it as
the `cfg` entry label:

```
cfg <Blocks[0].Label> {
  ...
}
```

## Implementation Outline

### Changes to StrataGenerator.cs

1. **New method: `HasGotoCmd(Implementation)`** — walk all blocks, return true
   if any `TransferCmd` is a `GotoCmd`.

2. **New method: `EmitCFGBody(Implementation)`** — emit the CFG body:
   - Emit `cfg <entry_label> {`
   - For each block: emit `label: {`, visit commands, emit transfer, emit `}`
   - Handle 3+ target gotos by generating synthetic nondet blocks
   - Emit closing `}`

3. **New method: `EmitTransferCmd(TransferCmd)`** — emit the transfer:
   - `ReturnCmd` → `return;`
   - `GotoCmd` 1 target → `goto L;`
   - `GotoCmd` 2 targets → `goto L1, L2;`
   - `GotoCmd` 3+ targets → `goto L1, __nondet_N;` (chain synthetic blocks,
     which are collected and emitted after the current block)

4. **Modify `VisitImplementation`** — at the top, check `HasGotoCmd()`:
   - If true: call `EmitCFGBody()` instead of the existing structured emission
   - If false: proceed with existing structured logic (unchanged)

### No changes to Lean codebase

The Core grammar already supports the CFG syntax. The parser, type checker,
symbolic executor, and CBMC pipeline all handle `Procedure.Body.cfg`. No Lean
changes are needed.

### Test strategy

1. **Existing BoogieToStrata tests** — all 37 `.bpl` files must still produce
   identical output (they use structured code, so auto-detect keeps them on
   the structured path).

2. **New CFG-specific tests** — add `.bpl` files with:
   - 1-target goto (unconditional jump)
   - 2-target goto (nondeterministic)
   - 3+ target goto (nested nondet encoding)
   - Mixed procedure (one structured, one with gotos)
   - Back-edge goto (loop pattern)

3. **SMACK integration** — generate Boogie from a few aws-c-common benchmarks,
   run through the updated BoogieToStrata without prelude stripping, verify
   the output parses in Strata.

## Scope

This design covers **phase 2 only** (BoogieToStrata unstructured emit). The
following are explicitly deferred:

- **Phase 1:** Generating more Boogie programs from aws-c-common benchmarks
  via the SMACK Docker pipeline.
- **Phase 3:** End-to-end verification of generated unstructured Core programs
  through VC generation, symbolic execution, or the CBMC pipeline.
