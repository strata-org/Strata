# Python Verification via Laurel

This document covers the Strata Python verification pipeline, which translates
Python programs through Laurel to Core for SMT verification.

## Prerequisites

1. **Build Strata**:
   ```
   lake build strata
   ```

2. **Install the Python bindings** (requires CPython 3.14):
   ```
   cd Tools/Python
   pip install .
   ```

3. **Generate the Python dialect file** (one-time setup):
   ```
   cd Tools/Python
   python -m strata.gen dialect dialects
   ```

## Pipeline Overview

There are two kinds of Python input files that flow through the pipeline:

- **Source programs** (`.py`) — the code you want to verify. These are
  translated to Ion format and then verified.
- **PySpec files** (`.py`) — type-stub-like specifications for external
  libraries. These provide type signatures and overload dispatch information
  to the verifier.

```
Source program (.py)                  PySpec library stubs (.py)
        |                                       |
        v                                       v
  [py_to_strata]                           [pySpecs]
        |                                       |
        v                                       v
  .python.st.ion                         .pyspec.st.ion
        |                                       |
        |                              [pySpecToLaurel]
        |                                       |
        |                                Laurel decls
        |                              + dispatch table
        |                               + methods
        v                                       v
                    [pyAnalyzeLaurel --pyspec ... --dispatch ...]
                                    |
                                    v
                          Verification results
```

## Step 1: Convert Source Programs to Ion

Translate a Python source file to a Strata Ion program file:

```
cd Tools/Python
python -m strata.gen py_to_strata \
   --dialect dialects/Python.dialect.st.ion \
   ../../StrataTest/Languages/Python/test.py \
   ../../StrataTest/Languages/Python/test.python.st.ion
```

The output `.python.st.ion` file contains the Python AST in Strata's Ion
binary format, ready for analysis.

## Step 2: Generate PySpec Ion Files from Library Stubs

If your program calls external libraries, you need PySpec files that describe
their type signatures. Convert a Python spec file to PySpec Ion:

```
lake exe strata pySpecs path/to/service_client.py output_dir/
```

- `python_path` — the `.py` stub file containing type annotations
- `strata_path` — output directory (created if it does not exist)
- Produces `output_dir/<module>.pyspec.st.ion`

**Example** (batch-converting all service stubs in a directory):
```
for pyfile in specs/inputs/*.py; do
    lake exe strata pySpecs "$pyfile" specs/pyspec/
done
```

## Step 3: Verify via the Laurel Pipeline

The primary verification command is `pyAnalyzeLaurel`. It:

1. Reads the Python Ion program
2. Builds a prelude augmented with PySpec-derived declarations
3. Translates Python to Laurel, then Laurel to Core
4. Runs SMT verification and reports results with source locations

```
lake exe strata pyAnalyzeLaurel [flags] <program.python.st.ion>
```

### Flags

`--verbose`
: Print the Python AST, Laurel program, and Core program at each
  stage.

`--pyspec <ion_file>`
: Add PySpec-derived Laurel declarations from an Ion file. Repeatable
  — use once per service. Translates PySpec signatures to Laurel types
  and procedures, and collects the overload dispatch table and method
  registry.

`--dispatch <ion_file>`
: Extract only the overload dispatch table from a PySpec Ion file (no
  Laurel translation). Repeatable. Use for files that define overloaded
  factory functions but no service classes.

### Examples

Verify a simple program (no external dependencies):
```
lake exe strata pyAnalyzeLaurel test.python.st.ion
```

Verify a program that uses multiple services:
```
lake exe strata pyAnalyzeLaurel \
    --pyspec specs/pyspec/ServiceA.pyspec.st.ion \
    --pyspec specs/pyspec/ServiceB.pyspec.st.ion \
    my_program.python.st.ion
```

Verify with a dispatch file (for overloaded factory function resolution):
```
lake exe strata pyAnalyzeLaurel \
    --pyspec specs/pyspec/ServiceA.pyspec.st.ion \
    --dispatch specs/pyspec/factory.pyspec.st.ion \
    my_program.python.st.ion
```

Use `--verbose` to see all intermediate representations:
```
lake exe strata pyAnalyzeLaurel --verbose \
    --pyspec specs/pyspec/ServiceA.pyspec.st.ion \
    my_program.python.st.ion
```

### Output

Verification results include assertion labels and pass/fail status. When the
corresponding `.py` source file is adjacent to the `.python.st.ion` file,
results include line and column numbers:

```
==== Verification Results ====
Assertion failed at line 12, col 4: assert_result_positive: fail
check_return_type: pass (at line 15, col 8)
```

## Diagnostic Commands

These commands are useful for inspecting intermediate artifacts.

### pySpecToLaurel

Translate a PySpec Ion file to Laurel and print a summary of the resulting
types, procedures, and overload dispatch table:

```
lake exe strata pySpecToLaurel path/to/service.py output_dir/
```

Both arguments are used to locate the Ion file: the module name is derived
from `python_path`'s filename stem, and the Ion file is read from
`strata_path/<module>.pyspec.st.ion`.

**Example output:**
```
Laurel: 42 procedure(s), 3 type(s)
Overloads: 0 function(s)
  type MyClient
  procedure MyClient_put_object(Key:TString, ...) returns(result:TString)
```

## Deprecated: Direct-to-Core Path

The `pyAnalyze` and `pyTranslate` commands translate Python directly to Core,
bypassing Laurel. This path is being phased out in favor of the Laurel
pipeline described above.

```
# Deprecated — use pyAnalyzeLaurel instead
lake exe strata pyAnalyze [--verbose] <file.python.st.ion>
lake exe strata pyTranslate <file.python.st.ion>
```
