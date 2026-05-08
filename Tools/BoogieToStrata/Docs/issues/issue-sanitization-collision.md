# BoogieToStrata: Sanitization maps distinct Boogie names to the same Strata identifier

## Problem

`SanitizeNameForStrata` replaces `@`, `.`, `#`, `^`, and `$` with `_`. This means distinct Boogie identifiers that differ only in these characters collide in the Strata output. Unlike the cross-namespace collision (constant vs procedure), this affects entities in the **same** namespace — two functions, two constants, etc.

Strata rejects the output with:

```
error: '_add_i32' already defined
```

## Minimal reproduction

A self-contained Boogie file that triggers the bug is at `Tools/BoogieToStrata/Tests/SanitizationCollision.bpl`:

```boogie
type i32 = int;

function {:inline} $add.i32(i1: i32, i2: i32) returns (i32) { i1 + i2 }
function {:inline} $add_i32(i1: i32, i2: i32) returns (i32) { i1 + i2 }

procedure main() returns (r: i32)
ensures r == 5;
{
  var a: i32;
  var b: i32;
  a := $add.i32(2, 3);
  b := $add_i32(2, 3);
  assert a == 5;
  assert b == 5;
  r := a;
}
```

Both `$add.i32` and `$add_i32` are valid distinct Boogie identifiers. After sanitization, both become `_add_i32`.

## Steps to reproduce

1. Build BoogieToStrata:
   ```bash
   cd Tools/BoogieToStrata && dotnet build Source/BoogieToStrata.csproj
   ```

2. Translate:
   ```bash
   dotnet run --project Source/BoogieToStrata.csproj -- Tests/SanitizationCollision.bpl > /tmp/out.core.st
   ```

3. Verify with Strata:
   ```bash
   ../../.lake/build/bin/strata verify /tmp/out.core.st
   ```

### Expected output

The generated `/tmp/out.core.st` contains duplicate definitions:

```
function _add_i32(i1 : i32, i2 : i32) : (i32) {
  (i1 + i2)
}
function _add_i32(i1 : i32, i2 : i32) : (i32) {
  (i1 + i2)
}
```

Step 3 produces:

```
error: '_add_i32' already defined
```

## Other collision patterns

| Boogie identifier A | Boogie identifier B | Both sanitize to |
|---|---|---|
| `$add.i32` | `$add_i32` | `_add_i32` |
| `foo.bar` | `foo_bar` | `foo_bar` |
| `x@1` | `x_1` | `x_1` |
| `Q#a$1^15` | `Q_a_1_15` | `Q_a_1_15` |
| `$slt.ref.bool` | `$slt_ref_bool` | `_slt_ref_bool` |

The `$name.type` pattern is pervasive in SMACK-generated Boogie (every arithmetic/comparison operation for every integer width), making this a realistic concern if a program also defines `$name_type` variants.

## Suggested fixes

### Option A — Collision-aware sanitization (recommended)

Track all sanitized names in a set. When a collision is detected, disambiguate by appending a numeric suffix:

```csharp
private readonly HashSet<string> _emittedNames = new();
private readonly Dictionary<string, string> _sanitizedNames = new();

private string SafeName(string originalName) {
    if (_sanitizedNames.TryGetValue(originalName, out var cached))
        return cached;
    var candidate = SanitizeNameForStrata(originalName);
    if (!_emittedNames.Add(candidate)) {
        var i = 2;
        while (!_emittedNames.Add($"{candidate}_{i}")) i++;
        candidate = $"{candidate}_{i}";
    }
    _sanitizedNames[originalName] = candidate;
    return candidate;
}
```

This requires a two-pass approach: first collect all names and compute their safe mappings, then emit. The mapping must be used consistently for both declarations and references.

### Option B — Use a different separator character

Replace `.` with a character that is valid in Strata but unlikely to appear in user identifiers, e.g., `'` (prime) if Strata supports it, or a Unicode character. This avoids collisions at the cost of less readable output.

### Option C — Preserve the original name structure

Use a reversible encoding: replace each special character with a distinct multi-character escape (e.g., `.` → `_dot_`, `$` → `_dollar_`, `@` → `_at_`). This guarantees no collisions but produces verbose names.

```csharp
private static string SanitizeNameForStrata(string name) {
    return name
        .Replace("$", "_D_")
        .Replace('.', "_P_")
        .Replace('@', "_A_")
        .Replace('#', "_H_")
        .Replace('^', "_C_");
}
```

### Option D — Subsume into the global rename mechanism

Extend the existing `_renames` / `_constantRenames` collision detection to also check for sanitization collisions within the same namespace. During the upfront declaration scan, if two entities sanitize to the same string, rename the second one with an entity-type prefix or numeric suffix.

## Recommendation

Option A is the most practical — it's a minimal change that handles all collision classes uniformly. Option C is the safest (zero collision risk) but makes all output harder to read. Option D integrates naturally with the existing cross-namespace fix on `htd/smack-fix`.

## Affected files

- `Tools/BoogieToStrata/Source/StrataGenerator.cs` — `SanitizeNameForStrata` (line ~228) and the `Name()` / `ResolveName()` methods that call it.
