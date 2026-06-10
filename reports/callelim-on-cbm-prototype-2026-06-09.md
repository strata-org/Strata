# Call-elim on CBM prototype — SMACK verification-intrinsic call lowering

**Date:** 2026-06-09
**Branch:** `callelim-cbm` (worktree, off `htd/smack` HEAD `188255668`)
**Worktree:** `/tmp/claude-503/callelim-cbm-wt` (left in place for review — NOT removed)
**Build:** green (`lake build StrataCoreToGoto` → 410/410; all `StrataTest/Backends/CBMC/GOTO/*` → 416/416)

---

## 1. Headline

- **The approach works on the intrinsics it targets.** Calls to the abstract SMACK
  stubs `__VERIFIER_assume` and `assert_.<type>` are now lowered inline to a single
  `ASSUME`/`ASSERT` instruction (`arg != 0`) instead of a `FUNCTION_CALL` to a
  bodyless callee. On the minimal pilot, the two targeted `[.no-body.*]` properties
  **disappear** and the assert becomes a *checked* CBMC property.

- **CBM delta on real pipeline programs: zero.** None of the 8 real SMACK programs
  reach the `[.no-body]` stage — they all abort *earlier* in CBMC on an upstream
  `_initialize` global-initializer typing bug (rc=6: `_initialize::_exnv` /`_M_0`
  bool-vs-integer/array mismatch) or an array-bounds crash (rc=134). BEFORE and AFTER
  are byte-identical on all 8. The fix is **necessary but not yet sufficient** to flip
  any real program to a CBM verdict.

- **Soundness: PASS, no mis-lowering.** Polarity validated end-to-end in both
  directions. A controlled negative test (`x:=0; assert x!=0`) correctly produced
  `ASSERT !=(x,0)` → CBMC `FAILURE` (rc=10) — an `ASSUME`-mis-lowering or `==0` flip
  would have wrongly reported SUCCESS, and did not. GOTO dumps confirm
  `ASSUME !=(x,0)` for `__VERIFIER_assume`, `ASSERT !=(x,0)` for `assert__i32`, never
  the inverse.

- **Next blocker (real path):** the bool-vs-integer/array typing of the synthetic
  `_initialize` procedure's parameters in Core→GOTO emission — strictly upstream of
  `[.no-body]`, identical before/after, independent of call-elim.

- **Next blocker (minimal pilot):** the non-intrinsic `boogie_si_record_i32` bodyless
  stub (deliberately out of scope; needs the orthogonal callee-body emission path),
  which is why the pilot exit code stays 10 (1-of-2 failed instead of 3-of-3).

**Verdict:** `works_reveals_next_blocker`.

---

## 2. Root-cause recap — why CBM emitted bodyless declarations

This is **not** call-elimination misbehaving; it is the *absence* of any handling for
abstract verification intrinsics.

SMACK injects synthetic specs onto a handful of reserved verification procedures via
BoogieToStrata's `--smack` injector (`StrataGenerator.cs:2022-2071`): a
`requires (_p != 0)` on `assert_.<type>`/`__VERIFIER_assert`, and a
`free ensures (_i0 != 0)` on `__VERIFIER_assume`. These procedures are **abstract** —
bodyless declarations with only a spec.

In `CoreCFGToGOTOPipeline.lean`, `emitCalleeProc` skips abstract procedures at the
`isAbstract` guard (the prototype-confirmed `if callee.body.isAbstract then return
(symtab, goto)`, around line 533). The skip is *correct* — there is no Strata body to
translate. But it leaves the callee in the symbol table as a declaration with
`value.id = nil` and **no GOTO function body**. When CBMC reaches a `FUNCTION_CALL` to
such a symbol, it reports `[.no-body.<callee>] no body for callee <callee>: FAILURE`
(documented at `CoreCFGToGOTOPipeline.lean:571,608`).

So the failing diagnostics are not "elimination going wrong" — there is no elimination
at all. The verification intrinsics carry their *entire* meaning in the injected spec
(`!= 0`), and that meaning was being dropped on the floor: the stub became a no-op
declaration, and CBMC flagged the dangling call. The fix is to *consume the spec
inline* (lower the call to the assume/assert it denotes) rather than emit a call to a
body that, by construction, can never exist.

This corrects a key expectation from the task brief and repro: the failure surfaces as
**CBMC exit 10 (`VERIFICATION FAILED`)** with `[.no-body.<callee>]` properties, not
exit 6 — on cbmc 6.9.0 the "no body" diagnostics are emitted as failed verification
properties, not a tool/usage error.

---

## 3. The lowering

### Intercept site
Two parallel sites, sharing the same two pure helpers verbatim:

- **Primary (CFG path — load-bearing for SMACK output):**
  `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOPipeline.lean`, in
  `coreCFGToGotoTransform`'s `.call procName callArgs _md` arm. The branch is inserted
  immediately after `argExprs` is computed and before the `FUNCTION_CALL` Instruction
  is constructed/pushed.
- **Secondary (structured-body path, for parity):**
  `Strata/Backends/CBMC/GOTO/CoreToGOTOPipeline.lean`, in `coreStmtsToGoto`'s
  `.cmd (.call procName callArgs _md)` arm, same placement.

The arg expressions are already lowered to typed GOTO `Expr`s, so `argExprs[0]` is
directly reusable as the guard operand without re-deriving a type.

### Lowering rules
| Callee | Lowers to | Why |
|---|---|---|
| `__VERIFIER_assume(arg)` | `ASSUME (arg != 0)` | Matches the injected `free ensures (_i0 != 0)`. A *free* ensures is **assumed** by the caller after the call — exactly `ASSUME`'s role (constrains paths, never fails). |
| `assert_.<type>(arg)` / `__VERIFIER_assert(arg)` | `ASSERT (arg != 0)` | Matches the injected (non-free) `requires (_p != 0)`. A non-free requires is **asserted** at the call site — a checked property CBMC can fail. |
| user / non-intrinsic callee (incl. `boogie_si_record_i32`) | unchanged `FUNCTION_CALL` | Not an intrinsic; falls through. |
| 0-arg intrinsic (malformed) | unchanged `FUNCTION_CALL` | Guards against `argExprs[0]!` panic by pattern-matching `arg :: _`. |

The guard is built type-faithfully:
`{ id := .binary .NotEqual, type := .Boolean, operands := [arg, Expr.constant "0" arg.type] }`
— the zero constant reuses the arg's already-resolved GOTO type so `NotEqual`'s two
operands share a type (avoids a mixed-width/signedness rejection by `symtab2gb`/CBMC).

### Intrinsic-detection strategy
Strategy **(b) name matching at the emission site**, not (c) abstract-AND-has-synthetic-spec.
Rationale: `coreCFGToGotoTransform`'s signature carries only `TyEnv`/`functionName`/`cfg`/`trans`
— it does **not** receive the `Core.Program` or the callee `Procedure.Spec` (the program is
only in scope two layers up at `coreToGotoFilesDispatch`). Strategy (c) would require threading
a `Program`/spec-map through `procedureToGotoCtxDispatch` → `procedureToGotoCtxViaCFG` →
`coreCFGToGotoTransform` and the structured path — a multi-signature change unsuited to a
prototype. Name matching is faithful to the *actual* injection site (the `--smack` injector
keys on the very same names), and SMACK reserves these names.

**Key design correction discovered during TDD:** the design's prefix `"assert_."` does **not**
match at the GOTO site. BoogieToStrata's `SanitizeNameForStrata` (`StrataGenerator.cs:294-298`)
rewrites `.` → `_` before the name reaches Core, so the callee is spelled `assert__i32` (double
underscore). The implemented matcher keys on prefix `"assert__"` (plus defensive `"assert_."`
and exact `"__VERIFIER_assert"`/`"__VERIFIER_assume"`).

### Patch summary (~108 LoC across 2 source files + 1 test)
- **`CoreToGOTOPipeline.lean` (+70):** two public pure helpers after `hasCallStmt` —
  - `classifySmackIntrinsic : String → Option Bool` (`some true` = assume for `__VERIFIER_assume`;
    `some false` = assert for `__VERIFIER_assert` / `startsWith "assert__"` / `startsWith "assert_."`;
    `none` otherwise), and
  - `mkNeqZeroGuard : CProverGOTO.Expr → CProverGOTO.Expr` (builds the `.NotEqual` `.Boolean` guard,
    reusing the arg's type for the zero constant).
  In `coreStmtsToGoto`'s call arm:
  `match classifySmackIntrinsic procName, argExprs with | some isAssume, arg :: _ => push one Instruction
  {type := if isAssume then .ASSUME else .ASSERT, guard := mkNeqZeroGuard arg, ...} | _, _ => <unchanged FUNCTION_CALL>`.
- **`CoreCFGToGOTOPipeline.lean` (net +38):** identical branch in `coreCFGToGotoTransform`'s `.call` arm
  (imperative for-loop form, `function := functionName`); empty-arg falls through to the unchanged
  `FUNCTION_CALL` else-branch.
- **`StrataTest/Backends/CBMC/GOTO/CallElimSmackLowering.lean` (+190, new):** `#guard`/`#eval`+`assert!`
  instruction-array checks across CFG and structured paths.

A correctness fix to the tooling invocation was also captured: `symtab2gb` must receive goto functions
via `--goto-functions`, not as a positional argument.

---

## 4. TDD evidence

### Failing-test-first (RED)
- **Form (b) e2e baseline (pre-change binary):** `cbmc` exit 10, stdout
  `[.no-body.boogie_si_record_i32] ... FAILURE / [.no-body.__VERIFIER_assume] ... FAILURE /
  [.no-body.assert__i32] ... FAILURE / ** 3 of 3 failed / VERIFICATION FAILED`. Upstream chain all
  green (`C2G_EXIT=0`, `SYMTAB2GB_EXIT=0`), so the failure is genuinely at the cbmc step.
- **Form (a) unit fail-first:** with the two pipeline edits git-stashed, the test module fails to
  build (`Unknown identifier classifySmackIntrinsic` / `mkNeqZeroGuard` — helpers are new), and the
  runtime assertions panic (`countType insts .ASSUME == 1` at line 89; `countType insts .ASSERT == 1`
  at lines 101/112; structured-path equivalents at 174/181). Pre-change those calls emit
  `FUNCTION_CALL`, so ASSUME/ASSERT counts are 0. Stash popped to restore the fix.

### Pass-after (GREEN, classified *partial*)
- **e2e (post-change binary):** the two targeted `[.no-body.*]` properties **disappear**. Final
  stdout: `[.no-body.boogie_si_record_i32] ... FAILURE / [main.1] line 0 smack-lowered assert__i32:
  SUCCESS / ** 1 of 2 failed / VERIFICATION FAILED` (exit 10). The exit stays 10 **only** because of
  the orthogonal, out-of-scope `boogie_si_record_i32` bare-`;`-spec stub. GOTO dump for `main` confirms
  polarity: `idx4 = ASSUME (((main::1::x : integer) != (0 : integer)) : bool)`;
  `idx5 = ASSERT (... != 0 ...)`; `idx3 = FUNCTION_CALL boogie_si_record_i32`.
- **unit (form a):** module builds green ⇒ all `#guard`/`assert!` checks pass — ASSUME/ASSERT counts,
  `NotEqual`-not-`Equal` guard, type-matched zero constant, `FUNCTION_CALL` retained for
  user/`boogie`/0-arg callees, and structured-path parity.

"Partial" reflects only the residual *out-of-scope* `boogie_si_record_i32` keeping the e2e exit at 10,
exactly as the test plan anticipated; the intrinsic lowering itself is fully working.

### No-regression
- `lake build StrataCoreToGoto` → 410/410; the two library modules build clean (203 jobs).
- All `StrataTest/Backends/CBMC/GOTO/*.lean` built together → 416/416. These modules use top-level
  `#eval ... assert!` runtime checks, so a green build means every assertion (incl. `E2E_Call`'s
  `FUNCTION_CALL` test and `E2E_CFGRPOReorder`) still holds. No re-golden needed — the lowering fires
  only on the reserved SMACK names, leaving existing programs' GOTO byte-identical.
- **User-callee unchanged, confirmed three ways:** (1) unit `mkCallProc "userFoo" 5` → `FUNCTION_CALL`==1,
  ASSUME==0, ASSERT==0 on both paths; (2) `classifySmackIntrinsic "userFoo" == none` and
  `"assertionHelper" == none` (a name merely starting with `assert` but not the reserved prefix is NOT
  lowered); (3) e2e `boogie_si_record_i32` still emits `FUNCTION_CALL` and still reports its
  `[.no-body]` property — proving no over-fire onto a same-prefix-adjacent callee.

---

## 5. Measurement

**8 real pipeline programs** (`simple_add`, `simple_assert`, `abs_func`, `max_func`, `swap`,
`loop_sum`, `array_sum`, `aws_array_eq_stripped`) + 1 minimal pilot + 1 negative soundness probe.

| Program | CBM before | CBM after | Delta |
|---|---|---|---|
| simple_add | ERR rc=6 (`_initialize::_exnv` bool/int) | ERR rc=6 (identical) | none |
| simple_assert | ERR rc=6 (`_exnv` bool/int) | ERR rc=6 (identical) | none (CBN=PASS natively) |
| abs_func | ERR rc=6 (`_exnv`) | ERR rc=6 (identical) | none |
| max_func | ERR rc=6 (`_exnv`) | ERR rc=6 (identical) | none |
| swap | ERR rc=6 (`_initialize::_M_0` bool/array) | ERR rc=6 (identical) | none |
| loop_sum | ERR rc=6 (`_exnv`; aborts in `_initialize` before unwinding) | ERR rc=6 (identical) | none |
| array_sum | ERR rc=134 (`from_integer`/`bounds_check_index`) | ERR rc=134 (identical) | none |
| aws_array_eq_stripped | ERR rc=134 (`from_integer` in `bounds_check_index`) | ERR rc=134 (identical) | none |
| **[pilot] simple_assert_pilot_fixed** | FAIL rc=10, `[.no-body]` ×3 (assume, assert, record) all FUNCTION_CALL, **3 of 3 failed** | FAIL rc=10, assume+assert `[.no-body]` **ELIMINATED** → ASSUME/ASSERT emitted, assert **CHECKED=SUCCESS**; only `[.no-body.boogie_si_record_i32]` remains, **1 of 2 failed** | **fix lands here** |
| **[neg3] soundness probe** (`x:=0; assert x!=0`) | n/a | FAIL rc=10, `[main.1] smack-lowered assert__i32: FAILURE` | **soundness PASS** |

**Documented baseline does NOT reproduce on real pipeline output.** The "all FAIL / `[.no-body]`"
baseline was established only on the TDD agent's hand-crafted minimal pilot. On the 8 real programs an
upstream GOTO type-emission bug in the SMACK `_initialize` global-initializer aborts CBMC *during BMC*,
**before** the symbol-resolution `[.no-body]` stage. That blocker is independent of call-elim
(byte-identical before/after) and sits earlier in the pipeline.

**Soundness cross-check vs CBN.** A direct CBM-vs-CBN comparison on real programs is impossible — CBM
produces *no verdict* (aborts upstream), which is the *absence* of a verdict, not a wrong one, so it
cannot be an unsound PASS. Soundness was instead validated with the controlled `neg3` negative test:
the AFTER binary emitted `ASSERT !=(main::1::x,0)` and CBMC correctly returned rc=10 FAILURE. An unsound
lowering (`ASSUME` instead of `ASSERT`, or `==` instead of `!=`) would have wrongly reported SUCCESS; it
did not. On the positive pilot, `assert__i32` reports SUCCESS *only because* the preceding
`__VERIFIER_assume(x)` legitimately constrains `x != 0` — consistent and sound.

**Next blocker (the real one).** The dominant cause on all 8 real programs is now the bool-vs-integer/array
typing of the synthetic `_initialize` procedure's parameters in Core→GOTO emission (`_exnv`,`_M_0`), plus
the array-bounds `from_integer` crash on memory-map programs. This is the next thing to clear before any
real SMACK program can reach a CBM verdict. On the minimal pilot, the residual blocker is the non-intrinsic
`boogie_si_record_i32` bodyless stub (out of scope; needs separate callee-body emission).

**Important real-SMACK caveat (carried from repro).** The SMACK pilot `.bpl` files do **not** exist on
disk and could not be regenerated (no `smack` binary; Docker daemon not running). The repro and the
minimal-pilot delta were produced by pushing a faithful SMACK-style Boogie file through the *exact* real
tool chain (`--smack` BoogieToStrata → `fix_core_st.py` → `StrataCoreToGoto` → `symtab2gb` → `cbmc`), and
cross-validated against the in-tree `Tools/BoogieToStrata/Tests/VerifierAssumeDuplicateSpec.bpl`, which
independently reproduces `[.no-body.__VERIFIER_assume]`. Whether a *real* `simple_assert.bpl` reaches
`[.no-body]` first (vs dying on the `_initialize` typing bug, as the 8 real programs do) is consistent with
the Measure finding: it does **not** — the real programs abort upstream. The intrinsic lowering is still
unambiguously correct on representative abstract-callee inputs.

---

## 6. Recommendation

**Promote to a real PR on `htd/smack` — iterate-then-ship.** The lowering is local, body-free,
call-site-accurate, sound (validated both polarity directions), and regression-free. It directly retires
the *named* residual of §9.1 #8 / issue #1184 (`__VERIFIER_assume` / `assert_.i32` still bodyless). It is
worth landing on its own merits even though it cannot, by itself, flip a real program — because the next
real blocker (`_initialize` typing) is strictly upstream and independent, this fix will be needed regardless
and de-risks that next layer.

**Caveat for the PR:** the CBM/GOTO path is **`htd/smack`-only** (the whole `Strata/Backends/CBMC/GOTO/`
cross-validation surface lives on this branch, per §9.1). This is not an upstream-targetable change yet.
The PR description should state plainly that the e2e win is demonstrated on minimal/representative input
and that the 8 real programs remain cbmc=FAIL on the `_initialize` blocker (no real-program verdict flip
claimed).

**Does the synthetic-body alternative win? No — intercept-and-lower is the right prototype call.**
The alternative (give the abstract stub a one-instruction synthetic GOTO body in `emitCalleeProc` instead
of skipping at `isAbstract`) is arguably more *principled* (it lowers literally from the attached spec and
auto-handles any future spec'd intrinsic without a name set — strategy-(c)-adjacent), but for this prototype
intercept-and-lower wins: it produces strictly simpler GOTO (no inter-procedural edge, faster BMC), it
reports the assert at the *actual call site* (per-call-site property granularity for triage) rather than
once at the callee, and it avoids fabricating CBMC calling-convention plumbing (param binding, return) for
a body we invent. Keep synthetic-body-from-spec as the documented generalization path if more intrinsics
appear or name-coupling becomes a maintenance burden.

**Hardening follow-up (clean, deferred):** thread a `Program`/spec-map down to the emission site and upgrade
detection from strategy (b) name-matching to (c) abstract-AND-has-synthetic-spec. Low urgency: SMACK reserves
these names, and any *real* user proc with a body now gets a GOTO body via the §2.8 callee emission and never
reaches the abstract-stub path.

---

## 7. Implications for BRANCH_FEATURES §9.1 #8 (issue #1184)

**This narrows §9.1 #8 substantially — it does not yet close it.**

§9.1 #8 (line 961) records the §2.8 partial fix (`ca95931be`) and its residual verbatim:
*"`__VERIFIER_assume` / `assert_.i32` still bodyless after the partial fix, so all 93 programs still report
cbmc=FAIL."* §2.8's result text (lines 244-254) lists the residual `[.no-body]` blocker as "narrowed to the
SMACK prelude stubs (`__VERIFIER_assume`, `assert_.i32`, etc.)" plus two further failure shapes (`_exnv`
typing, array-bounds crash).

This prototype **removes the first of those three residuals — the `[.no-body]` blocker for the verification
intrinsics** — by consuming their injected spec inline instead of emitting a dangling call. After this fix:

- `[.no-body.__VERIFIER_assume]` and `[.no-body.assert__i32]` are eliminated (verified on the pilot); the
  assert is now a *checked* CBMC property.
- The `[.no-body]` residual is further narrowed to **non-intrinsic** bodyless stubs (e.g.
  `boogie_si_record_i32`), which the §2.8 text already separates out and which need the orthogonal
  callee-body / record-stub handling, **not** this lowering.
- It does **not** touch the other two §2.8 residuals: the `_exnv`/`_M_0` `_initialize` typing bug and the
  array-bounds crash — and the Measure phase confirms those, not `[.no-body]`, are what actually gate all 8
  real programs today.

**Net for #1184:** the `[.no-body]` failure mode that #8 names is no longer the binding constraint for the
verification intrinsics. The blocker should be re-characterized: #8's `[.no-body]` story is effectively
resolved for the two named intrinsics (pending the PR landing and the orthogonal record-stub handling for the
remainder), and the *real* gate for flipping SMACK programs to a CBM verdict moves to the `_initialize`
parameter-typing bug (a distinct, upstream defect). Recommend updating §9.1 #8 / §2.8 to reflect that the
intrinsic `[.no-body]` sub-blocker has a fix in hand on `callelim-cbm`, and splitting out the `_initialize`
typing bug as the next-in-line CBM blocker if it is not already tracked separately.

---

## 8. Files referenced

**Worktree (left in place — review/promote here):** `/tmp/claude-503/callelim-cbm-wt`
(branch `callelim-cbm`, off `htd/smack` HEAD `188255668`).

Modified / added:
- `/tmp/claude-503/callelim-cbm-wt/Strata/Backends/CBMC/GOTO/CoreCFGToGOTOPipeline.lean` (CFG path, net +38; `.call` arm)
- `/tmp/claude-503/callelim-cbm-wt/Strata/Backends/CBMC/GOTO/CoreToGOTOPipeline.lean` (structured path + 2 helpers, +70)
- `/tmp/claude-503/callelim-cbm-wt/StrataTest/Backends/CBMC/GOTO/CallElimSmackLowering.lean` (new test, +190)

Key reference locations:
- `isAbstract` skip / `[.no-body]` origin: `CoreCFGToGOTOPipeline.lean` `emitCalleeProc` (~line 533); "no body for callee" comments at lines 571/608.
- `--smack` spec injector: `Tools/BoogieToStrata/Source/.../StrataGenerator.cs:2022-2071`; name-sanitizer `SanitizeNameForStrata` at `:294-298`.
- Blocker tracking: `/Users/htd/Documents/Strata-smack/Examples/smack-docker/BRANCH_FEATURES.md` §9.1 #8 (line 961, issue #1184) and §2.8 (lines 224-256).

Persisted repro/measurement inputs (under `/tmp/claude-503/`):
- Minimal pilot: `simple_assert_pilot.bpl`, `simple_assert_pilot_fixed.core.st`, `sap-out/`
- Soundness probe: `neg3.core.st`
- In-tree cross-check: `Tools/BoogieToStrata/Tests/VerifierAssumeDuplicateSpec.bpl` (→ `va2_fixed.core.st`, `va-out/`)
- Build log: `/tmp/claude-503/callelim-build.log`

> Note: the worktree is intentionally **not** removed so the human can inspect and promote the patch. No
> `git add`/`commit` was performed; the three changed files sit uncommitted on branch `callelim-cbm`.
