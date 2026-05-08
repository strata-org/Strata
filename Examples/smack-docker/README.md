# Running SMACK with Finch

## Prerequisites

- [Finch](https://github.com/runfinch/finch) installed and VM initialized (`finch vm init`)
- The `smack` container image built (see below)

## Building the SMACK Image

```bash
cd ~/smack-docker
finch build --platform linux/amd64 -t smack .
```

> The image uses `--platform linux/amd64` because SMACK's dependencies (dotnet-sdk-5.0, Z3 x86_64 binaries) are not available for ARM64.

## Running SMACK

### Verify a C program

```bash
finch run --rm --entrypoint /bin/sh \
  -v /path/to/your/programs:/programs \
  smack -c '. /home/user/smack.environment && cd /programs && smack yourfile.c'
```

### Generate Boogie output without verification

```bash
finch run --rm --entrypoint /bin/sh \
  -v /path/to/your/programs:/programs \
  smack -c '. /home/user/smack.environment && cd /programs && smack --no-verify -bpl output.bpl yourfile.c'
```

### Interactive session

```bash
finch run --rm -it --entrypoint /bin/sh \
  -v /path/to/your/programs:/programs \
  smack -c "/bin/bash --rcfile /home/user/.bashrc"
```

Then inside the container:

```bash
cd /programs
smack simple_add.c
smack --no-verify -bpl out.bpl loop_sum.c
```

## Notes

- `-v /host/path:/programs` mounts your local directory into the container.
- `--entrypoint /bin/sh` is required due to a binfmt quirk with amd64 emulation on ARM hosts.
- `. /home/user/smack.environment` sets up PATH for `smack`, `z3`, `boogie`, and `corral`.
- Verification runs under x86_64 QEMU emulation, so it will be slower than native execution.

## Example

Given `simple_add.c`:

```c
#include "smack.h"

int main(void) {
  int x = 1;
  int y = 2;
  int z = x + y;
  assert(z == 3);
  return 0;
}
```

Run:

```bash
finch run --rm --entrypoint /bin/sh \
  -v ~/smack-docker/programs:/programs \
  smack -c '. /home/user/smack.environment && cd /programs && smack simple_add.c'
```

Expected output:

```
SMACK program verifier version 2.8.0
SMACK found no errors with unroll bound 1.
```

## Verifying with BoogieToStrata

SMACK-generated `.bpl` files can be verified through the Strata pipeline:

```
.bpl → strip_smack_prelude.py → BoogieToStrata → .core.st → strata verify
```

### Why stripping is needed

SMACK's Boogie output includes prelude procedures (`__SMACK_and32`, `__SMACK_or64`, etc.)
whose bodies use unstructured multi-target gotos that BoogieToStrata does not yet support.
The `strip_smack_prelude.py` script removes these bodies, leaving them as uninterpreted
procedure declarations. User-defined functions and `main` are preserved.

### Workflow

```bash
# 1. Generate Boogie from C via SMACK
finch run --rm --entrypoint /bin/sh \
  -v ~/Documents/Strata2/Examples/smack-docker/programs:/programs \
  smack -c '. /home/user/smack.environment && cd /programs && smack --no-verify -bpl out.bpl yourfile.c'

# 2. Strip prelude implementations
python3 strip_smack_prelude.py programs/out.bpl programs/out_stripped.bpl

# 3. Translate to Strata Core (requires dotnet and BoogieToStrata built)
#    BoogieToStrata must have InferModifies=true and Prune=true set
cd ../../Tools/BoogieToStrata
dotnet run --project Source/BoogieToStrata.csproj -- \
  ../../Examples/smack-docker/programs/out_stripped.bpl > out.core.st

# 4. Fix known translation issues (forward refs, param/type shadowing)
cd ../../Examples/smack-docker
python3 fix_core_st.py out.core.st

# 5. Verify
../../.lake/build/bin/strata verify out.core.st
```

### Known limitations

- **Multi-target gotos**: Prelude procedures with unstructured CFGs must be stripped.
  They become uninterpreted, so their semantics are lost to the verifier. Even some
  user-level code (if/else, ternary operators) produces multi-target gotos from LLVM.
- **Irreducible control flow**: Programs with loops containing early returns produce
  irreducible CFGs that BoogieToStrata cannot structure.
- **InferModifies + Prune**: BoogieToStrata must have `InferModifies = true` and
  `Prune = true` set (on branch `htd/smack`) because SMACK omits `modifies` clauses
  and includes ~1400 unused prelude functions.
- **Namespace collisions**: SMACK emits `const main : ref;` which conflicts with
  `procedure main(...)` in Strata's single namespace.
- **Assert encoding**: SMACK's `assert()` compiles to a call to `assert_.i32()`,
  not a Strata `assert` statement — the verifier generates no VCs for these.
- **Type synonym resolution**: Strata panics on comparison operators applied to
  types that are synonyms of `int` (e.g., `ref := i64 := int`).
