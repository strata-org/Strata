# BoogieToStrata: constant and procedure name collision when both share the same identifier

## Problem

In Boogie, constants and procedures live in separate namespaces, so `const main : ref;` and `procedure main()` can coexist without conflict. However, BoogieToStrata emits both into Strata Core, which has a single namespace. Strata's type checker rejects the resulting program with:

```
Error in procedure main: a declaration of this name already exists.
```

## Minimal reproduction

A self-contained Boogie file that triggers the bug is at `Tools/BoogieToStrata/Tests/NamespaceCollision.bpl`:

```boogie
type ref = int;

const main: ref;
axiom (main == 1000);

var x: int;

procedure main()
  modifies x;
{
  x := 42;
  assert x == 42;
}
```

This is valid Boogie (constants and procedures have separate namespaces), but BoogieToStrata maps both `const main` and `procedure main` into Strata Core's single namespace.

## Steps to reproduce

1. Build BoogieToStrata:
   ```bash
   cd Tools/BoogieToStrata && dotnet build Source/BoogieToStrata.csproj
   ```

2. Translate the minimal .bpl file:
   ```bash
   dotnet run --project Source/BoogieToStrata.csproj -- Tests/NamespaceCollision.bpl > /tmp/out.core.st
   ```

3. Verify with Strata:
   ```bash
   ../../.lake/build/bin/strata verify /tmp/out.core.st
   ```

### Expected output

Step 3 produces:

```
Error in procedure main: a declaration of this name already exists.
```

The generated `/tmp/out.core.st` will contain something like:

```
const main : ref;
...
procedure main(...)
{ ... };
```

Both declarations use the identifier `main`, which Strata Core rejects.

## Suggested fix

In BoogieToStrata's `StrataGenerator`, when emitting constants that share a name with a procedure, prefix the constant (e.g., `const __addr_main : ref;` or `const main__ptr : ref;`). The constant is only used in axioms and as an argument to `boogie_si_record_ref`, so renaming it is safe.

Alternatively, skip emitting constants that name procedures entirely (they are SMACK's internal bookkeeping for function pointer addresses).

## Affected files

- `Tools/BoogieToStrata/Source/StrataGenerator.cs` -- the section that emits constants (around the `liveDeclarations.OfType<Constant>()` loop).
