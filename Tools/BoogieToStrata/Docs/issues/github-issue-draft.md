## Title

BoogieToStrata: Blockers preventing SMACK-generated Boogie verification

## Body

Testing the SMACK → BoogieToStrata → Strata pipeline on 12 C programs reveals systematic issues that block end-to-end verification. All programs that pass translation (8/12) fail at verification time.

See [`Tools/BoogieToStrata/Docs/aws-c-common-test-results.md`](https://github.com/strata-org/Strata/blob/htd/smack/Tools/BoogieToStrata/Docs/aws-c-common-test-results.md) on branch `htd/smack` for full test results.

### 1. Namespace collision: constant and procedure sharing the same name

SMACK emits `const main : ref;` (function pointer address) alongside `procedure main(...)`. Strata Core has a single namespace, rejecting this as a duplicate declaration.

**Impact**: 7/12 programs  
**Fix**: Rename or skip constants that collide with procedure names in `StrataGenerator.cs`.

Details: [`Tools/BoogieToStrata/Docs/issues/issue-namespace-collision.md`](https://github.com/strata-org/Strata/blob/htd/smack/Tools/BoogieToStrata/Docs/issues/issue-namespace-collision.md)  
Reproducer: [`Tools/BoogieToStrata/Tests/NamespaceCollision.bpl`](https://github.com/strata-org/Strata/blob/htd/smack/Tools/BoogieToStrata/Tests/NamespaceCollision.bpl)

---

### 2. Type synonym chain not resolved for comparison/arithmetic operators

Strata's DDM translator panics on `<=`, `<`, `>=`, `>`, `+`, `-`, `*`, `div`, `mod` when operands have a type that is a synonym of `int` (e.g., `ref := i64 := int`). Equality (`==`) is unaffected.

**Impact**: 1/12 programs (blocks more once issue 1 is fixed)  
**Fix**: Make `dealiasTypeExpr` in `Strata/Languages/Core/DDMTransform/Translate.lean:452` resolve transitively.

Details: [`Tools/BoogieToStrata/Docs/issues/issue-type-synonym-comparison.md`](https://github.com/strata-org/Strata/blob/htd/smack/Tools/BoogieToStrata/Docs/issues/issue-type-synonym-comparison.md)  
Reproducer: [`Tools/BoogieToStrata/Tests/TypeSynonymComparison.core.st`](https://github.com/strata-org/Strata/blob/htd/smack/Tools/BoogieToStrata/Tests/TypeSynonymComparison.core.st)

---

### 3. SMACK's `assert_` call pattern not recognized as verification condition

SMACK encodes C `assert(expr)` as `call assert_.i32(cond)`. BoogieToStrata emits this as an opaque procedure call, so zero VCs are generated — even `assert(false)` passes silently.

**Impact**: All programs (latent — only visible once issues 1 and 2 are fixed)  
**Fix**: In `VisitCallCmd`, intercept calls matching `assert_.*` and emit `assert (arg != 0);`. The `VisitAssertCmd` infrastructure already exists.

Details: [`Tools/BoogieToStrata/Docs/issues/issue-smack-assert-encoding.md`](https://github.com/strata-org/Strata/blob/htd/smack/Tools/BoogieToStrata/Docs/issues/issue-smack-assert-encoding.md)  
Reproducer: [`Tools/BoogieToStrata/Tests/SmackAssert.bpl`](https://github.com/strata-org/Strata/blob/htd/smack/Tools/BoogieToStrata/Tests/SmackAssert.bpl)
