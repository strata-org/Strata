# BoogieToStrata Verification Experiment

## Overview

Experimented with the BoogieToStrata pass to translate Boogie (.bpl) files into Strata Core, then verified the procedure bodies using symbolic execution and VC generation via the `strata verify` command with the cvc5 SMT solver.

## Pipeline

```
.bpl file → BoogieToStrata (C#) → .core.st file → strata verify → cvc5 (SMT solver)
```

## Commands Used

### Building BoogieToStrata

```bash
cd Tools/BoogieToStrata
dotnet build Source/BoogieToStrata.csproj
```

### Translating Boogie to Strata Core

```bash
dotnet run --project Source/BoogieToStrata.csproj -- <input.bpl> > output.core.st
```

### Verifying with Strata

```bash
# Full verification (symbolic execution + VC generation + SMT solving)
.lake/build/bin/strata verify output.core.st

# Verbose mode (shows assumptions and obligations for each VC)
.lake/build/bin/strata verify --verbose output.core.st

# Specific procedures only
.lake/build/bin/strata verify --procedures ProcName output.core.st

# Parse/type-check only (no verification)
.lake/build/bin/strata verify --check output.core.st

# Generate SMT-LIB files without solving
.lake/build/bin/strata verify --no-solve --vc-directory ./vcs output.core.st

# Generate and solve, keeping SMT-LIB files
.lake/build/bin/strata verify --vc-directory ./vcs output.core.st

# Bug-finding mode (looks for counterexamples)
.lake/build/bin/strata verify --check-mode bugFinding output.core.st
```

### Applying Transforms (intermediate inspection)

```bash
# Loop elimination (havoc/assume/assert pattern)
.lake/build/bin/strata transform --pass loopElim output.core.st

# Call elimination (replace calls with havoc + assume postconditions)
.lake/build/bin/strata transform --pass callElim output.core.st
```

## Results on BoogieToStrata Test Files

| File | VCs | Result |
|------|-----|--------|
| Gauss.bpl (Gauss summation) | 5 | All pass |
| McCarthy-91.bpl (recursive function) | 2 | All pass |
| DivMod.bpl (division/modulo) | 6 | All pass |
| Bubble.bpl (bubble sort) | 30 | All pass |
| ForwardGotos.bpl (control flow) | 4 | All pass |
| Arrays2.bpl (array operations) | 12 | 10 pass, 2 unknown (expected) |
| CrossNestingExit.bpl (nested loops) | 3 | 1 pass, 2 fail (expected) |
| Lambda.bpl (lambda/quantifiers) | 12 | 10 pass, 2 unknown (expected) |
| TripleNestedLoops.bpl | 0 | No VCs (no specs) |

All results matched the `.expect` files in the test suite.

## Results on SMACK-generated .bpl Files (from Examples/smack-docker/programs/)

### Direct translation: FAILED

The SMACK-generated .bpl files (simple_add.bpl, loop_sum.bpl, pointer_arith.bpl) cannot be directly processed by BoogieToStrata due to two issues:

1. **Missing `modifies` clauses**: SMACK generates code for Corral, which doesn't enforce modifies clause checking. The files assign to global variables (`$exn`, `$CurrAddr`, `$M.0`, etc.) without declaring them in `modifies`.

2. **Unsupported control flow**: After fixing modifies clauses, BoogieToStrata hits "Unsupported: goto with two targets that aren't obvious inverses." SMACK uses multi-target gotos with `assume {:branchcond}` guards (unstructured CFG style), which BoogieToStrata doesn't handle — it expects structured if/then/else patterns.

### Workaround: Hand-written Boogie equivalents — PASSED

Created simplified Boogie versions of the same C programs:

| C Program | Assertion | VCs | Result |
|-----------|-----------|-----|--------|
| simple_add.c (`assert(x+y==3)`) | `z == 3` | 2 | All pass |
| loop_sum.c (`assert(sum==10)`) | `sum == 10` | 6 | All pass |
| pointer_arith.c (`assert(arr[0]+arr[1]+arr[2]==60)`) | map sum == 60 | 2 | All pass |

## Verification Approach

The Strata verifier uses:

1. **Loop elimination**: Loops → entry invariant check + havoc + assume invariant + body + maintain invariant check
2. **Call elimination**: Recursive/procedure calls → havoc return values + assume postconditions (modular verification)
3. **Symbolic execution**: Explores paths through the program, collecting path conditions
4. **VC generation**: For each assertion/postcondition, generates a validity query: `path_conditions ∧ ¬obligation` should be UNSAT
5. **SMT solving**: Sends VCs to cvc5 in SMT-LIB2 format (logic: ALL)

## Experiment 2: SMACK Test Suite & AWS C Common Programs

Tested 9 programs through the full pipeline with additional workarounds:

### Programs tested

**SMACK basic tests:**
- `simple_assert.c` — function call + assert
- `abs_func.c` — if/else branch with nondet input
- `max_func.c` — ternary operator + multiple asserts
- `nondet_branch.c` — assume + if/else
- `swap.c` — pointer swap via function call
- `array_sum.c` — loop with array indexing

**AWS C Common style:**
- `aws_byte_cursor_advance.c` — struct manipulation + pointer arithmetic
- `aws_array_eq.c` — loop comparing byte arrays
- `aws_ring_buffer.c` — ring buffer used/free with wrap-around

### Pipeline with workarounds

```
.bpl → strip_smack_prelude.py → BoogieToStrata (InferModifies + Prune) → fix_core_st.py → strata verify
```

### Results

| Step | simple_assert | abs_func | max_func | nondet_branch | swap | array_sum | aws_byte_cursor | aws_array_eq | aws_ring_buffer |
|------|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| SMACK → .bpl | OK | OK | OK | OK | OK | OK | OK | OK | OK |
| Strip prelude | OK | OK | OK | OK | OK | OK | OK | OK | OK |
| BoogieToStrata | OK | FAIL¹ | FAIL¹ | FAIL¹ | OK | OK | OK | FAIL² | OK |
| Strata verify | FAIL³ | — | — | — | FAIL³ | FAIL⁴ | FAIL³ | — | FAIL³ |

**Failure reasons:**
1. **Multi-target goto in user code**: `abs_func`, `max_func`, `nondet_branch` use if/else and ternary
   operators that LLVM compiles to unstructured branches even in the user's own functions.
2. **Irreducible control flow**: `aws_array_eq` has a loop with early return creating irreducible CFG.
3. **Namespace collision**: SMACK emits `const main : ref;` (function pointer address) which conflicts
   with `procedure main(...)` — Strata Core has a single namespace for all declarations.
4. **Type synonym comparison**: Strata's type checker doesn't resolve `ref := i64 := int` when
   checking comparison operators (`le`, `lt`, `ge`) — panics with "unexpected type".

### Additional issue: SMACK assertion encoding

Even for programs that parse and type-check, SMACK encodes C `assert()` as a *call*
to an uninterpreted procedure `assert_.i32(cond)`, not as a Strata `assert` statement.
The verifier sees this as an opaque call with no postcondition, so it generates zero
verification conditions. To make SMACK assertions verifiable, BoogieToStrata would need
to recognize the `assert_` pattern and translate it into a proper `assert` statement.

## Full List of Issues Found (BoogieToStrata + Strata)

### BoogieToStrata issues

1. **Multi-target gotos** — Only handles "obvious inverse" two-target gotos (structured if/else).
   All unstructured CFG patterns (from LLVM's basic block layout) fail.
2. **Irreducible control flow** — No support for loops with multiple entry points.
3. **Parameter/type name shadowing** — Parameters named `i1`, `i8`, etc. shadow type synonyms
   of the same name, causing Strata parse errors. (See `Tools/BoogieToStrata/BUGS.md`)
4. **Function forward references** — Functions emitted in declaration order; callee-before-caller
   ordering not enforced. (See `Tools/BoogieToStrata/BUGS.md`)
5. **Namespace collision** — Boogie separates constant and procedure namespaces; Strata doesn't.
   `const main` and `procedure main` collide.
6. **SMACK assert encoding** — `assert_` calls not translated to `assert` statements.

### Strata verifier issues

7. **Type synonym resolution for operators** — Comparison operators (`le`, `lt`, `ge`) don't
   resolve through type synonym chains (e.g., `ref := i64 := int`). Panics in `translateFunction`.

## Limitations Discovered

- BoogieToStrata requires **structured control flow** (if/else patterns). Unstructured multi-target gotos (as generated by SMACK/LLVM) are not supported.
- SMACK-generated .bpl files are designed for **Corral** (which relaxes modifies checking), not standard Boogie typechecking.
- To verify SMACK output, either (a) restructure the CFG before translation, or (b) use a front-end that generates structured Boogie.
- **SMACK's assertion encoding** (`assert_` calls) is invisible to Strata's VC generation — requires explicit translation to `assert` statements.
- **Type synonym chains** in Strata need fixing for operator type checking to work with SMACK's integer type hierarchy.
