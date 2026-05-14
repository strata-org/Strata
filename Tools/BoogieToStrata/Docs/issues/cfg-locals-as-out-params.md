# CFG Locals-as-Out-Params Issues

## Background

When BoogieToStrata emits a procedure with CFG syntax, local variables are
promoted to `out` parameters because the DDM parser's `cfg_block` has per-block
scoping (`@[scope(cmds)]` in Grammar.lean:487) — variables declared in one
block aren't visible in other blocks.

This workaround causes two downstream failures.

---

## Issue A: `LExpr.fvar` type error in StrataCoreToGoto

### Symptom

```
Error: [toGotoExprCtx] Not yet implemented: LExpr.fvar () { name := "main::1::_exn", metadata := () } none
```

### Reproduction

```bash
cd /Users/htd/Documents/Strata2/Examples/smack-docker

# 1. Translate simple_add.bpl through the pipeline
python3 strip_smack_prelude.py programs/simple_add.bpl /tmp/simple_add_stripped.bpl
dotnet run --project ../../Tools/BoogieToStrata/Source/BoogieToStrata.csproj -- /tmp/simple_add_stripped.bpl > /tmp/simple_add.core.st
python3 fix_core_st.py /tmp/simple_add.core.st /tmp/simple_add_fixed.core.st

# 2. Run StrataCoreToGoto
../../.lake/build/bin/StrataCoreToGoto --output-dir /tmp /tmp/simple_add_fixed.core.st
```

### Expected output
```
Written /tmp/simple_add_fixed.symtab.json and /tmp/simple_add_fixed.goto.json
```

### Actual output
```
[Strata.Core] Type Checking Succeeded!
Error: [toGotoExprCtx] Not yet implemented: LExpr.fvar () { name := "main::1::_exn", metadata := () } none
```

### Root cause

The `main` procedure has `inout _exn : bool` as a formal parameter. Inside
the body, `_exn := false;` appears as an assignment. The GOTO pipeline:

1. Renames formals to `main::_exn` (via `mkFormalSymbol`) and seeds the type env
2. Collects "defined variables" from the body — finds `_exn` (the assignment target)
3. Renames it as a local to `main::1::_exn` (via `mkLocalSymbol`)
4. Tries to look up `main::1::_exn` in the type environment — it's not there
   because it's actually a formal (already renamed), not a local
5. When converting expressions referencing this variable to GOTO, the `.fvar`
   has `ty = none` and the translator errors

### Minimal reproducer (.core.st)

```
program Core;

procedure main(inout x : bool, out r : int)
cfg entry {
  entry: {
    r := 1;
    x := false;
    return;
  }
};
```

```bash
../../.lake/build/bin/StrataCoreToGoto --output-dir /tmp /tmp/minimal.core.st
# Error: [toGotoExprCtx] Not yet implemented: LExpr.fvar () { name := "main::1::x", ... } none
```

### Affected programs

All 12 SMACK programs (they all have `inout _exn : bool` assigned in `main`).

---

## Issue B: Output length mismatch in callElim

### Symptom

```
<unknown>(1, (0-0)) output length and lhs length mismatch
```

Exit code 3 (internal error) from `strata verify`.

### Reproduction

```bash
cd /Users/htd/Documents/Strata2/Examples/smack-docker

# 1. Translate aws_array_eq.bpl through the pipeline
python3 strip_smack_prelude.py programs/aws_array_eq.bpl /tmp/aws_stripped.bpl
dotnet run --project ../../Tools/BoogieToStrata/Source/BoogieToStrata.csproj -- /tmp/aws_stripped.bpl > /tmp/aws.core.st
python3 fix_core_st.py /tmp/aws.core.st /tmp/aws_fixed.core.st

# 2. Run strata verify
../../.lake/build/bin/strata verify --check-mode deductive /tmp/aws_fixed.core.st
```

### Expected output
```
Successfully parsed.
All N goals passed.
```

### Actual output
```
Successfully parsed.
<unknown>(1, (0-0)) output length and lhs length mismatch
```
Exit code 3.

### Root cause

The `aws_array_eq` procedure is emitted with CFG syntax. Because of the
locals-as-out-params workaround, ALL its local variables become `out`
parameters in the declaration:

```
procedure aws_array_eq(inout _exn : bool, ..., out _r : i1,
    out _i4 : i1, out _i6 : i64, out _i7 : i1, out _p8 : ref,
    out _i9 : i8, out _i10 : i32, out _p11 : ref, out _i12 : i8,
    out _i13 : i32, out _i14 : i1, out _i15 : i64, out _i5 : i1)
```

That's 13 `out` parameters. But call sites in other procedures (e.g., `main`)
use the original Boogie calling convention with only 1 output:

```
call aws_array_eq(inout _exn, ..., _p6, 4, _p7, 4, out _i8);
```

When `callElim` processes this call, it sees 1 LHS variable (`_i8`) but the
callee declares 13 output parameters → "output length and lhs length mismatch".

### Minimal reproducer (.core.st)

```
program Core;

procedure callee(x : int, out r : int, out extra : int)
cfg entry {
  entry: {
    r := x + 1;
    extra := x + 2;
    return;
  }
};

procedure main(out result : int)
{
  call callee(42, out result);
  assert (result == 43);
};
```

```bash
../../.lake/build/bin/strata verify /tmp/mismatch.core.st
# <unknown>(1, (0-0)) output length and lhs length mismatch
```

### Affected programs

aws_array_eq, aws_byte_cursor_advance, aws_ring_buffer — any program where
a CFG procedure (with promoted locals) is called from another procedure.

---

## Potential fixes

### Option 1: Don't promote locals to out params

Instead of emitting locals as `out` parameters, emit them as `var`
declarations inside the `cfg` body but outside any block. This requires
a grammar change to allow declarations between `cfg entry {` and the first
block label.

Example syntax:
```
procedure foo(x : int, out r : int)
cfg entry {
  var temp : int;
  entry: {
    temp := x + 1;
    goto done;
  }
  done: {
    r := temp;
    return;
  }
};
```

### Option 2: Scope declarations across all blocks

Change the DDM grammar so `cfg_block` variables are scoped to the `cfg_body`
level, not per-block. Replace `@[scope(cmds)]` on `cfg_block` with scoping
at the `cfg_body` level.

### Option 3: Only promote locals for entry-point procedures

Only promote locals for the procedure that won't be called by others (the
entry-point). For callee procedures, keep the original signature and emit
`var` declarations inside the entry block. This doesn't fully solve the
scoping issue but avoids the callsite mismatch.

### Option 4: Separate internal/external signatures

Emit two versions: the external declaration (with original Boogie signature)
for callers, and the implementation (with promoted locals) for the body.
This mirrors Boogie's own separate `procedure` declaration vs `implementation`.
