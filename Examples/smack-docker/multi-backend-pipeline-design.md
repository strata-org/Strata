# Multi-Backend Pipeline Design

## Problem

`run_pipeline.py` currently runs a single verification backend (`strata verify`
in deductive mode). We want to:

1. Test programs through all three verification approaches: deductive VC
   generation, bug-finding symbolic execution, and CBMC.
2. Report results per-program per-backend in a structured table.
3. Handle the new CFG emission (programs with gotos now emit `cfg` syntax).

## Changes to `run_pipeline.py`

### New command-line flags

```
python3 run_pipeline.py [--backends deductive,bugFinding,cbmc] [programs/*.bpl ...]
```

- `--backends`: comma-separated list of backends to run (default: all available)
- Backends:
  - `deductive` — `strata verify --check-mode deductive`
  - `bugFinding` — `strata verify --check-mode bugFinding`
  - `cbmc` — `StrataCoreToGoto` → `.symtab.json` + `.goto.json` → `cbmc` (if available)
- If `cbmc` binary is not found, skip that backend with a warning.

### New binaries to discover

```python
STRATA_CORE_TO_GOTO = REPO_ROOT / ".lake" / "build" / "bin" / "StrataCoreToGoto"
CBMC_BIN = shutil.which("cbmc")  # None if not installed
```

### Pipeline flow per program

```
.bpl → strip_smack_prelude.py → _stripped.bpl
     → BoogieToStrata → .core.st
     → fix_core_st.py → _fixed.core.st
     → [deductive]  strata verify --check-mode deductive
     → [bugFinding]  strata verify --check-mode bugFinding
     → [cbmc]        StrataCoreToGoto → symtab.json + goto.json → cbmc
```

Steps 1-3 (strip, translate, fix) run once. Each backend then runs
independently on the same `_fixed.core.st`.

### CBMC backend specifics

```python
def run_cbmc_backend(core_st: Path, tmpdir: Path) -> tuple[str, str]:
    # Step 1: Core → GOTO JSON
    rc, stdout, stderr = run_cmd([
        str(STRATA_CORE_TO_GOTO), str(core_st),
        "--output-dir", str(tmpdir)
    ], timeout=120)
    if rc != 0:
        return ("FAIL", f"StrataCoreToGoto: {stderr.strip()[:80]}")

    # Step 2: Find generated files
    symtab = tmpdir / f"{core_st.stem}.symtab.json"
    goto_json = tmpdir / f"{core_st.stem}.goto.json"
    if not symtab.exists() or not goto_json.exists():
        return ("FAIL", "GOTO JSON files not generated")

    # Step 3: Convert to GOTO binary via symtab2gb (if available)
    # Or run cbmc --json-ui on the JSON directly
    # For now, just report that GOTO JSON was generated successfully
    if CBMC_BIN is None:
        return ("SKIP", "GOTO JSON generated (cbmc not found)")

    # Step 4: Run CBMC
    goto_bin = tmpdir / f"{core_st.stem}.goto"
    rc, stdout, stderr = run_cmd([
        "symtab2gb", str(symtab), str(goto_json), "--out", str(goto_bin)
    ], timeout=60)
    if rc != 0:
        return ("FAIL", f"symtab2gb: {stderr.strip()[:80]}")

    rc, stdout, stderr = run_cmd([
        CBMC_BIN, str(goto_bin), "--json-ui"
    ], timeout=120)
    # Parse CBMC JSON output for pass/fail
    if rc == 0:
        return ("PASS", "CBMC: all properties hold")
    elif rc == 10:
        return ("FAIL", "CBMC: property violations found")
    else:
        return ("FAIL", f"CBMC exit code {rc}")
```

### CFG body handling

Programs that now emit `cfg` syntax (due to the auto-detect change) will:
- **Deductive/bugFinding**: Hit "cannot apply statement-level transform to
  CFG body" — reported as a distinct error category, not a crash.
- **CBMC**: `StrataCoreToGoto` handles CFG bodies via `procedureToGotoCtxViaCFG`
  — this should work for programs with single-target gotos. Programs with
  nondet gotos may fail due to the `$__nondet_0` type-check issue (#1162).

### Updated reporting

Table columns expand to show each backend:

```
Program          │ Strip │ B2S │ Fix │ deductive  │ bugFinding │ cbmc
─────────────────┼───────┼─────┼─────┼────────────┼────────────┼──────────
simple_add       │ OK    │ OK  │ OK  │ PASS (2vc) │ PASS       │ PASS
aws_byte_cursor  │ OK    │ OK  │ OK  │ FAIL       │ FAIL       │ GOTO JSON
loop_sum         │ OK    │ OK  │ OK  │ PASS (4vc) │ PASS       │ SKIP
```

### PipelineResult changes

```python
class PipelineResult:
    def __init__(self, name: str):
        self.name = name
        self.translation_steps: list[tuple[str, str, str]] = []
        self.backend_results: dict[str, tuple[str, str]] = {}
        # backend_results maps backend_name → (status, detail)
```

### Error categories (expanded)

Add new categories for CFG-related issues:
- `"CFG body not supported by transforms"` — deductive/bugFinding on CFG procedures
- `"Nondet goto type-check error"` — `$__nondet_0` issue
- `"GOTO JSON generation failed"` — StrataCoreToGoto error
- `"cbmc not available"` — skip

## No changes to Lean codebase

All verification backends already exist as built binaries.

## Test strategy

1. Run `python3 run_pipeline.py` on all 16 existing programs
2. Verify deductive results match previous behavior
3. Verify bugFinding produces reasonable results
4. Verify CBMC backend at least generates GOTO JSON for simple cases
