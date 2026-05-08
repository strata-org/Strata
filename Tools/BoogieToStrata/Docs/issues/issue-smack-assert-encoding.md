# BoogieToStrata: Recognize SMACK's `assert_` call pattern and emit Strata `assert` statements

## Problem

SMACK encodes C `assert(expr)` as a call to a procedure named `assert_.i32(cond)` (or `assert_.i64`, etc.). BoogieToStrata translates this as an opaque procedure call, so the Strata verifier generates zero verification conditions for these assertions.

## Example

Given C code with an obviously false assertion:

```c
int x = 0;
assert(x == 1);  // should FAIL
```

SMACK produces Boogie:

```boogie
$i0 := $eq.i32(0, 1);       // evaluates to 0 (false)
$i1 := $zext.i1.i32($i0);   // still 0
call $i2 := assert_.i32($i1);  // should be an assertion failure
```

BoogieToStrata translates this as an opaque call:

```
call assert__i32(0, out _i2);
```

The verifier reports **"All 0 goals passed"** — the false assertion is completely invisible.

What Strata needs to generate a VC is:

```
assert (0 != 0);   // this would correctly FAIL
```

## Steps to Reproduce

1. Save this as `SmackAssert.bpl`:

```boogie
type i32 = int;

procedure assert_.i32(p.0: i32) returns ($r: i32);

procedure main() returns ($r: i32)
{
  // Pass 0 (false) to assert — this should be a verification failure
  call $r := assert_.i32(0);
  $r := 0;
  return;
}
```

2. Translate:
```bash
cd Tools/BoogieToStrata
dotnet run --project Source/BoogieToStrata.csproj -- Tests/SmackAssert.bpl > /tmp/out.core.st
```

3. Verify:
```bash
../../.lake/build/bin/strata verify /tmp/out.core.st
```

4. Observe output:
```
Successfully parsed.
All 0 goals passed.
```

The assertion `assert(false)` passes silently with zero VCs generated.

A minimal test case is saved at `Tools/BoogieToStrata/Tests/SmackAssert.bpl`.

## Expected Behavior

BoogieToStrata should recognize calls to procedures whose names match `assert_.*` and emit them as `assert (arg != 0);` (since SMACK uses 0 = false, nonzero = true).

If the call has a return value (e.g., `call $r := assert_.i32($i2)`), the return variable should be havocked or assigned a default value after the assert, since the original `assert_` procedure is a no-op that returns void semantically.

## Current Infrastructure

Investigation of `Tools/BoogieToStrata/Source/StrataGenerator.cs` reveals:

### What already exists

1. **`VisitAssertCmd` (line 794)**: The generator already handles Boogie's native `AssertCmd` nodes. It emits `assert <expr>;` in the Strata output:

   ```csharp
   public override Cmd VisitAssertCmd(AssertCmd node) {
       Indent("assert ");
       VisitExpr(node.Expr);
       WriteLine(";");
       return node;
   }
   ```

   Similarly, `VisitAssertEnsuresCmd` and `VisitAssertRequiresCmd` also emit `assert` statements. This means the Strata output format and the verifier already understand `assert` as a VC-generating construct.

2. **`VisitAssumeCmd` (line 801)**: Analogous support for `assume` statements exists, showing the pattern for emitting simple keyword statements with expressions.

### What translates procedure calls today

3. **`VisitCallCmd` (line 951)**: This method handles ALL `CallCmd` nodes uniformly. It emits `call <sanitized_proc_name>(globals..., args..., out outputs...);` without any special-casing based on the callee's name. This is where the `assert_` pattern would need to be intercepted.

### What would need to be added

The fix should be implemented in `VisitCallCmd`. Before the generic call emission logic, add a check:

1. **Pattern match**: Check if `node.Proc.Name` matches the regex `^assert_\..*` (or starts with `"assert_"`).
2. **Extract the condition argument**: The first (and typically only) input argument is the condition. In SMACK's encoding, this is an integer where 0 = false and nonzero = true.
3. **Emit an assert**: Instead of emitting a `call`, emit `assert (<arg> != 0);`.
4. **Handle the return variable**: If the call has output variables (e.g., `call $r := assert_.i32(...)`), emit a havoc or assignment for the output variable after the assert, since the procedure is being replaced.

A sketch of the implementation:

```csharp
public override Cmd VisitCallCmd(CallCmd node) {
    // Recognize SMACK's assert_ pattern
    if (node.Proc.Name.StartsWith("assert_")) {
        // The first input argument is the condition (0 = false, nonzero = true)
        if (node.Ins.Count >= 1) {
            Indent("assert (");
            VisitExpr(node.Ins[0]);
            WriteText(" != 0)");
            WriteLine(";");
        }
        // Havoc any output variables since assert_ is semantically void
        foreach (var outVar in node.Outs) {
            IndentLine($"havoc {Name(outVar.Name)};");
        }
        return node;
    }

    // ... existing generic call logic ...
}
```

### Design considerations

- **Name matching**: SMACK generates `assert_.i32`, `assert_.i64`, `assert_.i1`, etc. A prefix match on `"assert_"` (after the `$` prefix is stripped, noting that SMACK uses `$` in names which gets sanitized) should be sufficient. The actual Boogie name is `assert_.i32` so matching on `node.Proc.Name.StartsWith("assert_")` or a regex `^assert_\.` would work.
- **Condition semantics**: SMACK follows C convention where 0 is false and any nonzero value is true. The emitted assert should be `arg != 0` rather than treating it as a boolean directly.
- **Output variables**: The return value of `assert_` procedures in SMACK is unused/meaningless. Havocking it is safe and ensures no downstream code depends on an undefined value.
- **Configuration**: Consider making this behavior opt-in via a flag (e.g., `--smack-mode`) in case other Boogie frontends define procedures named `assert_` with different semantics.
