# BoogieToStrata CFG Emission Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Extend the BoogieToStrata C# translator to emit Strata Core's native CFG syntax for procedures that contain gotos, instead of failing or structuring them.

**Architecture:** Add a `HasGotoCmd` check in `VisitImplementation`. When gotos are present, emit via a new `EmitCFGBody` method that walks Boogie's flat `Block` list and emits `cfg entry { label: { stmts; transfer; } }` syntax. Multi-target gotos (3+) are encoded as nested binary nondet blocks with synthetic labels.

**Tech Stack:** C# (.NET 8.0), Boogie library, xUnit tests

**Design spec:** `Tools/BoogieToStrata/Docs/cfg-emission-design.md`

---

### Task 1: Add CFG-specific test files

**Files:**
- Create: `Tools/BoogieToStrata/Tests/CFGSimpleGoto.bpl`
- Create: `Tools/BoogieToStrata/Tests/CFGNondetGoto.bpl`
- Create: `Tools/BoogieToStrata/Tests/CFGMultiTargetGoto.bpl`
- Create: `Tools/BoogieToStrata/Tests/CFGMixedProcedures.bpl`
- Create: `Tools/BoogieToStrata/Tests/CFGBackEdge.bpl`

These will initially fail translation (the CFG emission code doesn't exist yet).
The existing xUnit test discovery (`GetBoogieTestFiles`) auto-discovers all
`.bpl` files in `Tests/`, so no test runner changes are needed.

- [ ] **Step 1: Create CFGSimpleGoto.bpl — single-target gotos only**

```boogie
// Test: procedures with single-target gotos emit CFG syntax.
// All gotos have exactly one target (unconditional jumps).

procedure SimpleChain()
{
  var x: int;

  entry:
    x := 0;
    goto next;

  next:
    x := x + 1;
    goto done;

  done:
    assert x == 1;
    return;
}
```

- [ ] **Step 2: Create CFGNondetGoto.bpl — two-target nondet gotos**

```boogie
// Test: 2-target gotos emit nondet goto syntax.

procedure TwoTargetNondet()
{
  var x: int;

  entry:
    x := 0;
    goto left, right;

  left:
    assume x == 0;
    x := 1;
    goto join;

  right:
    assume x == 0;
    x := 2;
    goto join;

  join:
    assert x == 1 || x == 2;
    return;
}
```

- [ ] **Step 3: Create CFGMultiTargetGoto.bpl — 3+ target goto (nested nondet)**

```boogie
// Test: 3+ target gotos are encoded as nested binary nondet.

procedure ThreeTargetGoto()
{
  var x: int;

  entry:
    x := 0;
    goto a, b, c;

  a:
    x := 1;
    goto done;

  b:
    x := 2;
    goto done;

  c:
    x := 3;
    goto done;

  done:
    assert x >= 1 && x <= 3;
    return;
}

procedure FourTargetGoto()
{
  var x: int;

  entry:
    x := 0;
    goto a, b, c, d;

  a:
    x := 1;
    goto done;

  b:
    x := 2;
    goto done;

  c:
    x := 3;
    goto done;

  d:
    x := 4;
    goto done;

  done:
    assert x >= 1 && x <= 4;
    return;
}
```

- [ ] **Step 4: Create CFGMixedProcedures.bpl — one structured, one with gotos**

```boogie
// Test: per-procedure auto-detect. StructuredProc has no gotos (emit structured).
// GotoProc has gotos (emit CFG). Both in the same file.

procedure StructuredProc(x: int) returns (r: int)
{
  if (x > 0) {
    r := x;
  } else {
    r := 0 - x;
  }
}

procedure GotoProc()
{
  var y: int;

  start:
    y := 42;
    goto finish;

  finish:
    assert y == 42;
    return;
}
```

- [ ] **Step 5: Create CFGBackEdge.bpl — loop pattern via back-edge goto**

```boogie
// Test: backward goto (loop pattern).

procedure LoopViaGoto(n: int)
{
  var i: int;

  entry:
    i := 0;
    goto head;

  head:
    goto body, exit;

  body:
    assume i < n;
    i := i + 1;
    goto head;

  exit:
    assume i >= n;
    assert i >= 0;
    return;
}
```

- [ ] **Step 6: Verify test files are syntactically valid Boogie**

Run from `Tools/BoogieToStrata/`:
```bash
dotnet run --project Source/BoogieToStrata.csproj -- Tests/CFGSimpleGoto.bpl
```
Expected: fails with "Unsupported" error (CFG emission not implemented yet).
This confirms the file parses as valid Boogie — the failure is in our translator.

- [ ] **Step 7: Commit test files**

```bash
git add Tools/BoogieToStrata/Tests/CFGSimpleGoto.bpl \
        Tools/BoogieToStrata/Tests/CFGNondetGoto.bpl \
        Tools/BoogieToStrata/Tests/CFGMultiTargetGoto.bpl \
        Tools/BoogieToStrata/Tests/CFGMixedProcedures.bpl \
        Tools/BoogieToStrata/Tests/CFGBackEdge.bpl
git commit -m "test: add .bpl test files for CFG emission"
```

---

### Task 2: Add `HasGotoCmd` detection method

**Files:**
- Modify: `Tools/BoogieToStrata/Source/StrataGenerator.cs`

- [ ] **Step 1: Add `HasGotoCmd` method**

Add this method to the `StrataGenerator` class (after `BlockName` around line 1782):

```csharp
/// <summary>
/// Check whether any block in the implementation uses a GotoCmd.
/// When true, the procedure body should be emitted as CFG syntax.
/// </summary>
private static bool HasGotoCmd(Implementation impl) {
    return impl.Blocks.Any(b => b.TransferCmd is GotoCmd);
}
```

- [ ] **Step 2: Verify the project builds**

```bash
cd Tools/BoogieToStrata && dotnet build Source/BoogieToStrata.csproj
```
Expected: build succeeds (method is added but not called yet).

- [ ] **Step 3: Commit**

```bash
git add Tools/BoogieToStrata/Source/StrataGenerator.cs
git commit -m "feat: add HasGotoCmd detection for CFG auto-detect"
```

---

### Task 3: Add `_nondetLabelCount` counter field

**Files:**
- Modify: `Tools/BoogieToStrata/Source/StrataGenerator.cs`

- [ ] **Step 1: Add the counter field**

Add near the other counter field `_breakLabelCount` (line 47):

```csharp
private int _nondetLabelCount;
```

- [ ] **Step 2: Commit**

```bash
git add Tools/BoogieToStrata/Source/StrataGenerator.cs
git commit -m "feat: add _nondetLabelCount for synthetic CFG labels"
```

---

### Task 4: Implement `EmitCFGTransfer` method

**Files:**
- Modify: `Tools/BoogieToStrata/Source/StrataGenerator.cs`

This method emits the transfer command at the end of a CFG block. It also
collects any synthetic blocks needed for 3+ target gotos.

- [ ] **Step 1: Add `EmitCFGTransfer` and `EmitNondetGotoChain` methods**

Add after the `HasGotoCmd` method:

```csharp
/// <summary>
/// Emit a CFG transfer command for a block's TransferCmd.
/// For 3+ target GotoCmds, synthetic intermediate blocks are appended
/// to <paramref name="syntheticBlocks"/>.
/// </summary>
private void EmitCFGTransfer(
    TransferCmd cmd,
    List<(string label, string target1, string target2)> syntheticBlocks) {
    if (cmd is ReturnCmd) {
        IndentLine("return;");
    } else if (cmd is GotoCmd gotoCmd) {
        var names = gotoCmd.LabelTargets.Select(t => Name(t.Label)).ToList();
        EmitNondetGotoChain(names, syntheticBlocks);
    } else {
        throw new StrataConversionException(cmd.tok,
            $"Unsupported transfer command in CFG: {cmd}");
    }
}

/// <summary>
/// Emit a (possibly chained) nondet goto for the given target labels.
/// 1 target: goto L;
/// 2 targets: goto L1, L2;
/// 3+ targets: goto L1, __nondet_N; with synthetic blocks chaining the rest.
/// </summary>
private void EmitNondetGotoChain(
    List<string> targets,
    List<(string label, string target1, string target2)> syntheticBlocks) {
    if (targets.Count == 1) {
        IndentLine($"goto {targets[0]};");
    } else if (targets.Count == 2) {
        IndentLine($"goto {targets[0]}, {targets[1]};");
    } else {
        // 3+ targets: peel off the first, chain through synthetic blocks
        var synthLabel = $"__nondet_{_nondetLabelCount++}";
        IndentLine($"goto {targets[0]}, {synthLabel};");
        // Build chain: each synthetic block picks one target or continues
        var rest = targets.Skip(1).ToList();
        while (rest.Count > 2) {
            var nextSynth = $"__nondet_{_nondetLabelCount++}";
            syntheticBlocks.Add((synthLabel, rest[0], nextSynth));
            rest.RemoveAt(0);
            synthLabel = nextSynth;
        }
        // Final synthetic block: 2 remaining targets
        syntheticBlocks.Add((synthLabel, rest[0], rest[1]));
    }
}
```

- [ ] **Step 2: Verify build**

```bash
cd Tools/BoogieToStrata && dotnet build Source/BoogieToStrata.csproj
```

- [ ] **Step 3: Commit**

```bash
git add Tools/BoogieToStrata/Source/StrataGenerator.cs
git commit -m "feat: add EmitCFGTransfer and EmitNondetGotoChain methods"
```

---

### Task 5: Implement `EmitCFGBody` method

**Files:**
- Modify: `Tools/BoogieToStrata/Source/StrataGenerator.cs`

- [ ] **Step 1: Add `EmitCFGBody` method**

Add after `EmitNondetGotoChain`:

```csharp
/// <summary>
/// Emit a procedure body as Strata Core CFG syntax:
///   cfg entry_label {
///     label: {
///       stmts;
///       transfer;
///     }
///     ...
///   }
/// </summary>
private void EmitCFGBody(Implementation node) {
    var blocks = node.Blocks;
    if (blocks.Count == 0) return;

    var entryLabel = BlockName(blocks[0]);
    IndentLine($"cfg {entryLabel} {{");
    IncIndent();

    // Collect synthetic blocks generated by multi-target gotos
    var syntheticBlocks = new List<(string label, string target1, string target2)>();

    foreach (var block in blocks) {
        var label = BlockName(block);
        IndentLine($"{label}: {{");
        IncIndent();

        // Emit commands (reuse existing Visit dispatch for each command)
        foreach (var cmd in block.Cmds) {
            Visit(cmd);
        }

        // Emit transfer
        EmitCFGTransfer(block.TransferCmd, syntheticBlocks);

        DecIndent();
        IndentLine("}");
    }

    // Emit synthetic blocks for 3+ target gotos
    foreach (var (label, target1, target2) in syntheticBlocks) {
        IndentLine($"{label}: {{");
        IncIndent();
        IndentLine($"goto {target1}, {target2};");
        DecIndent();
        IndentLine("}");
    }

    DecIndent();
    IndentLine("}");
}
```

- [ ] **Step 2: Verify build**

```bash
cd Tools/BoogieToStrata && dotnet build Source/BoogieToStrata.csproj
```

- [ ] **Step 3: Commit**

```bash
git add Tools/BoogieToStrata/Source/StrataGenerator.cs
git commit -m "feat: add EmitCFGBody for CFG syntax emission"
```

---

### Task 6: Wire `EmitCFGBody` into `VisitImplementation`

**Files:**
- Modify: `Tools/BoogieToStrata/Source/StrataGenerator.cs:1906-1951`

This is the integration point. The existing `VisitImplementation` opens `{`,
emits locals, then dispatches to structured or flat-block emission. For CFG,
we skip the `{` and locals and emit `cfg entry { ... }` instead (locals go
inside the CFG blocks as declarations).

Actually — looking at the Core CFG syntax more carefully, local variables are
declared before the `cfg` keyword, inside the procedure body braces:

```
procedure name(params) {
  var z : int;
  cfg entry {
    entry: { ... }
  }
};
```

So the existing local variable emission (lines 1920-1925) stays. We just
replace the body emission path.

- [ ] **Step 1: Modify `VisitImplementation`**

Replace lines 1927-1944 of `VisitImplementation`:

```csharp
// BEFORE (lines 1927-1944):
if (node.StructuredStmts != null) {
    EmitStmtList(node.StructuredStmts);
} else {
    var blocks = node.Blocks;
    var gotoTargets = CollectGotoTargets(blocks, b => b.TransferCmd);
    var labelToIndex = new Dictionary<string, int>();
    for (var i = 0; i < blocks.Count; i++) {
        labelToIndex[blocks[i].Label] = i;
    }
    labelToIndex[ExitLabel] = blocks.Count;
    EmitWithExitWrappers(gotoTargets, labelToIndex, blocks.Count, i => {
        VisitBlock(blocks[i]);
    });
}
```

Replace with:

```csharp
// AFTER:
if (HasGotoCmd(node)) {
    EmitCFGBody(node);
} else if (node.StructuredStmts != null) {
    EmitStmtList(node.StructuredStmts);
} else {
    var blocks = node.Blocks;
    var gotoTargets = CollectGotoTargets(blocks, b => b.TransferCmd);
    var labelToIndex = new Dictionary<string, int>();
    for (var i = 0; i < blocks.Count; i++) {
        labelToIndex[blocks[i].Label] = i;
    }
    labelToIndex[ExitLabel] = blocks.Count;
    EmitWithExitWrappers(gotoTargets, labelToIndex, blocks.Count, i => {
        VisitBlock(blocks[i]);
    });
}
```

The key change: `HasGotoCmd(node)` is checked first. If any block has a goto,
we emit CFG syntax. Otherwise, fall through to the existing structured paths.

- [ ] **Step 2: Verify build**

```bash
cd Tools/BoogieToStrata && dotnet build Source/BoogieToStrata.csproj
```

- [ ] **Step 3: Test CFGSimpleGoto.bpl translates successfully**

```bash
cd Tools/BoogieToStrata && dotnet run --project Source/BoogieToStrata.csproj -- Tests/CFGSimpleGoto.bpl
```

Expected output should contain:
```
cfg entry {
  entry: {
    ...
    goto next;
  }
  next: {
    ...
    goto done;
  }
  done: {
    assert ...;
    return;
  }
}
```

- [ ] **Step 4: Test CFGNondetGoto.bpl**

```bash
cd Tools/BoogieToStrata && dotnet run --project Source/BoogieToStrata.csproj -- Tests/CFGNondetGoto.bpl
```

Expected: output contains `goto left, right;` (2-target nondet).

- [ ] **Step 5: Test CFGMultiTargetGoto.bpl**

```bash
cd Tools/BoogieToStrata && dotnet run --project Source/BoogieToStrata.csproj -- Tests/CFGMultiTargetGoto.bpl
```

Expected: output contains `goto a, __nondet_0;` and synthetic blocks.

- [ ] **Step 6: Test CFGMixedProcedures.bpl**

```bash
cd Tools/BoogieToStrata && dotnet run --project Source/BoogieToStrata.csproj -- Tests/CFGMixedProcedures.bpl
```

Expected: `StructuredProc` uses `if (...) { ... } else { ... }` (structured),
`GotoProc` uses `cfg start { ... }` (CFG).

- [ ] **Step 7: Test CFGBackEdge.bpl**

```bash
cd Tools/BoogieToStrata && dotnet run --project Source/BoogieToStrata.csproj -- Tests/CFGBackEdge.bpl
```

Expected: output contains backward goto (`goto head;` from body block).

- [ ] **Step 8: Commit**

```bash
git add Tools/BoogieToStrata/Source/StrataGenerator.cs
git commit -m "feat: wire CFG emission into VisitImplementation with auto-detect"
```

---

### Task 7: Verify existing tests still pass

**Files:** (no modifications)

The auto-detect should not change behavior for existing test files that
have no gotos. For files that DO have gotos (like `ForwardGotos.bpl`),
they will now emit CFG syntax instead of structured exit wrappers — this
changes their output but should still be valid.

- [ ] **Step 1: Run the translation tests (no verification)**

```bash
cd Tools/BoogieToStrata && dotnet test IntegrationTests/BoogieToStrata.IntegrationTests.csproj --filter "TranslateTestFileWithoutErrors"
```

Expected: all tests pass (exit code 0, non-empty output).

- [ ] **Step 2: Check ForwardGotos.bpl output**

```bash
cd Tools/BoogieToStrata && dotnet run --project Source/BoogieToStrata.csproj -- Tests/ForwardGotos.bpl
```

This file previously used structured exit wrappers. With `HasGotoCmd` detection,
it will now emit CFG syntax. Verify the output is valid CFG syntax with `goto`
transfers.

- [ ] **Step 3: If any existing tests fail, investigate**

If a previously-passing test now fails because it switched from structured
to CFG emission:
- Check whether the failure is in translation (exit code != 0) or in
  verification (`.expect` file mismatch).
- For `.expect` mismatches: update the `.expect` file if the new CFG output
  is semantically correct.
- For translation failures: investigate what command or pattern in the .bpl
  file triggers the issue.

- [ ] **Step 4: Commit any .expect file updates**

```bash
git add Tools/BoogieToStrata/Tests/*.expect
git commit -m "test: update .expect files for CFG emission output"
```

---

### Task 8: Verify CFG output parses in Strata

**Files:**
- Create: `Tools/BoogieToStrata/Tests/CFGSimpleGoto.expect` (optional)

- [ ] **Step 1: Build Strata verifier**

```bash
cd /Users/htd/Documents/Strata2 && lake build strata
```

- [ ] **Step 2: Translate and verify CFGSimpleGoto.bpl**

```bash
cd Tools/BoogieToStrata
dotnet run --project Source/BoogieToStrata.csproj -- Tests/CFGSimpleGoto.bpl > /tmp/cfg_simple.core.st
cat /tmp/cfg_simple.core.st
../../.lake/build/bin/strata verify --check /tmp/cfg_simple.core.st
```

Expected: Strata parses the CFG output without errors. `--check` performs
type checking only (no verification).

- [ ] **Step 3: Translate and verify CFGNondetGoto.bpl**

```bash
dotnet run --project Source/BoogieToStrata.csproj -- Tests/CFGNondetGoto.bpl > /tmp/cfg_nondet.core.st
../../.lake/build/bin/strata verify --check /tmp/cfg_nondet.core.st
```

- [ ] **Step 4: Translate and verify CFGMultiTargetGoto.bpl**

```bash
dotnet run --project Source/BoogieToStrata.csproj -- Tests/CFGMultiTargetGoto.bpl > /tmp/cfg_multi.core.st
../../.lake/build/bin/strata verify --check /tmp/cfg_multi.core.st
```

- [ ] **Step 5: Translate and verify CFGBackEdge.bpl**

```bash
dotnet run --project Source/BoogieToStrata.csproj -- Tests/CFGBackEdge.bpl > /tmp/cfg_back.core.st
../../.lake/build/bin/strata verify --check /tmp/cfg_back.core.st
```

- [ ] **Step 6: Run full integration test suite**

```bash
cd Tools/BoogieToStrata && bash run-integration-tests.sh
```

Expected: all tests pass. The `VerifyTestFile` tests translate `.bpl` → `.core.st`
and then run `strata verify`, confirming the Strata parser accepts the output.

- [ ] **Step 7: Commit**

```bash
git add Tools/BoogieToStrata/Tests/*.expect
git commit -m "test: verify CFG emission output parses in Strata"
```

---

### Task 9: Final cleanup and documentation commit

**Files:**
- Modify: `Tools/BoogieToStrata/Docs/BUGS.md` (update resolved items)

- [ ] **Step 1: Update BUGS.md**

Add entry documenting that multi-target gotos are now supported via CFG
emission, and that `strip_smack_prelude.py` may no longer be needed for
procedures whose only issue was multi-target gotos.

- [ ] **Step 2: Final commit**

```bash
git add Tools/BoogieToStrata/Docs/BUGS.md
git commit -m "docs: update BUGS.md for CFG emission support"
```
