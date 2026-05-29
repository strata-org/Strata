# StrataBoole

StrataBoole is a standalone Lean 4 package implementing the **Boole dialect** for [Strata](../). Boole is a high-level imperative specification language designed for deductive program verification, offering a friendlier surface syntax that compiles down to Strata Core for analysis.

## Overview

Boole extends Strata Core with:

- **Global variables** with `var` declarations and `modifies` clauses (translated to `inout` parameters)
- **`returns` syntax** for procedure outputs (vs. Core's `out` parameter modifiers)
- **`call lhs := f(args)`** syntax for calls with outputs
- **For loops** (`for ... to`, `for ... downto`, C-style `for(;;)`)
- **Unicode quantifiers** (`∀`, `∃`) alongside ASCII (`forall`, `exists`)
- **Extensional equality** (`=~=`) for map types

The analysis pipeline is: **Boole program** → parse via DDM → translate to **Strata Core** → perform analysis

## Package Structure

```
StrataBoole/
├── lakefile.toml            # Lake build config (depends on Strata)
├── lean-toolchain           # Lean version selection
├── StrataBoole.lean         # Root module
├── StrataBoole/
│   ├── Grammar.lean         # DDM dialect grammar definition
│   ├── Boole.lean           # Code generation from grammar (#strata_gen)
│   ├── Verify.lean          # Translation to Core + verification pipeline
│   └── MetaVerifier.lean    # Tactic infrastructure (gen_smt_vcs_boole)
├── StrataBooleTest.lean     # Test root module
└── StrataBooleTest/
    ├── demo.lean            # Basic loop verification example
    ├── find_max.lean         # Array search with quantified invariants
    ├── insertion_sort.lean   # Sorting algorithm verification
    ├── ...                   # Additional test/example files
    └── FeatureRequests/      # Tests for planned/experimental features
```

## Building

From the `StrataBoole/` directory:

```bash
lake build
```

To run all tests (builds the test library, which includes `#eval` and `#guard_msgs` checks):

```bash
lake test
```

The package depends on the parent `Strata` package (via `path = ".."`), so ensure the main Strata package builds first.

## Writing a Boole Program

Programs can be embedded in Lean using the `#strata ... #end` syntax:

```lean
import StrataBoole.MetaVerifier

open Strata

def myProgram : StrataDDM.Program :=
#strata
program Boole;

procedure Add(x: int, y: int) returns (r: int)
spec {
  requires (x >= 0 && y >= 0);
  ensures (r == x + y);
}
{
  r := x + y;
};
#end
```

Programs can also be stored in `*.boole.st` source files. However, there is not
currently a top-level CLI that will process these files. To load external files
in the Boole dialect from a client of the `StrataBoole` package, use
`Strata.readStrataFile` to get a `StrataDDM.Program` and
`Strata.Boole.getProgram` to translate it to a `Strata.Boole.Program`.

## Verifying a Program

### Runtime verification (via SMT solver)

```lean
#eval Strata.Boole.verify "cvc5" myProgram (options := .quiet)
```

### Proof-mode verification (checked by Lean's kernel)

```lean
theorem myProgram_correct : Strata.smtVCsCorrectBoole myProgram := by
  gen_smt_vcs_boole
  all_goals (try grind)
```

The `gen_smt_vcs_boole` tactic unfolds the program into individual SMT
verification conditions as Lean goals. Each goal can then be discharged by
`grind`, `omega`, `simp`, or other Lean tactics.

## Key Concepts

### Verification Pipeline

1. **Parse**: The DDM (Dialect Definition Mechanism) parses Boole syntax from `#strata` blocks
2. **Translate**: `Strata.Boole.toCoreProgram` converts Boole AST to Strata Core
3. **VCG**: Core's verifier generates verification conditions via symbolic execution
4. **Encode**: VCs are encoded as SMT-LIB formulas
5. **Solve**: Either dispatched to an external solver or proved within Lean

### Boole vs. Core Syntax

| Boole | Core equivalent |
|-------|----------------|
| `var x : int;` | inout parameter |
| `var x : int;` (global) | adds `x` as `inout` parameter to procedures whose `modifies` lists it; `in` parameter elsewhere |
| `modifies x;` (clause) | promotes the corresponding global to `inout` in this procedure's signature |
| `returns (r: int)` | `out r: int` parameter |
| `call y := f(x);` | `call(inout globals, in x, out y)` |
| `for i := 0 to n` | `init i; while(i <= n) { ...; i := i + 1 }` |
| `∀ x:int . P` | `forall x:int :: P` |

### Maps (Arrays)

Boole uses `Map` types with select/store syntax:

```
type Array := Map int int;
// Read: A[i]
// Write: A[i] := v;
```

## Testing

Test files serve as both regression tests and usage examples. Each test file:
- Defines a Boole program
- Verifies it using `#eval` (runtime) and/or a `theorem` (proof-mode)
- Uses `#guard_msgs` to pin expected output

Good starting points:
- `demo.lean` - Simple loop with arithmetic invariant
- `find_max.lean` - Array traversal with quantified invariants
- `procedure_signatures.lean` - Procedure calling conventions
- `function_definitions.lean` - Pure function definitions with preconditions

## License

Apache-2.0 OR MIT
