# Front-End Testing & Validation

This document covers how to validate your Strata front-end's correctness, set coverage targets, debug translation issues, and understand how translation choices affect downstream verification performance. For the technical guide on building a front-end, see [Front-End Guide](frontend_guide.md). For hosting decisions, see [Hosting & Governance](frontend_hosting.md).

## Validation

### How do I validate that my front-end preserves source language semantics?

To validate that your front-end preserves source language semantics, the recommended approach is differential testing with an executable intermediate representation. Build a testing framework that compiles the same program twice: once using the standard language compiler (like `javac` for Java or CPython for Python) and once through your Strata front-end. Execute both versions and compare their outputs for equivalence. If the outputs don't match, your translation doesn't accurately preserve source language semantics for that test case. Matching outputs increase confidence but don't constitute a proof of correctness. This approach provides independent validation of your front-end without requiring full end-to-end verification workflows, making debugging significantly easier when issues arise. Most Strata dialects have well-defined executable semantics. You can reuse the execution engine of your target dialect to build the differential testing infrastructure.

### What code coverage targets should I aim for?

When building a new Strata front-end, you should aim for at least 80% feature-level coverage of the language features you intend to support. This means tracking not just the percentage of tests that pass, but specifically which language constructs and features are validated by your passing tests. Feature-level coverage ensures you are systematically testing critical language capabilities like lambdas, generics, polymorphism, exception handling, and concurrency primitives rather than just accumulating test counts. Map each test case to the specific language features it exercises, allowing you to identify gaps where certain features remain untested and prioritize improvements accordingly.

Beyond feature coverage, track your test pass rate as a complementary metric that measures overall translation correctness. The framework should maintain both metrics over time, enabling you to monitor progress and detect regressions. For languages with comprehensive conformance test suites (like Python's CPython tests, or TypeScript's ECMAScript Test Suite), these official suites provide excellent baseline coverage targets since they're designed to validate complete language specification compliance. Start with these established test collections rather than building from scratch, as they represent the same standards used by the language maintainers themselves.

---

## Debugging

### How do I debug translation issues?

Implement detailed logging throughout your translation pipeline to facilitate systematic debugging. Your framework should capture intermediate representations at key transformation points—the parsed abstract syntax tree from the source language, the generated Strata IR, and execution traces from both the reference compiler path and your Strata path. When a differential test fails, these logs allow you to pinpoint exactly where the translation diverged by comparing intermediate states. Additionally, maintain a coverage tracking system that maps test outcomes to specific language features over time, creating an audit trail that shows which features consistently pass, which fail, and which remain untested. Log execution metadata like timeout occurrences, crashes, or infinite loops when running on large real-world codebases, as these robustness issues often reveal edge cases that small unit tests miss.

---

## Performance considerations

The considerations below are about the quality of the generated verification conditions, not about translation speed (translation itself is rarely a bottleneck). They are most relevant if you're translating to a dialect like Laurel or Core that feeds into SMT-based verification. If you're targeting a higher-level dialect, you can skip this section. In general, front-end developers should focus on correct, information-preserving translations and leave optimization decisions to backend stages.

### What performance considerations affect verification of translated programs?

Some considerations include:

- If your dialect has nested or recursive structures (e.g., nested pattern matching, comprehensions), flatten them early. Deeply nested translations produce deeply nested verification conditions that are harder for SMT solvers.

- Core uses a flat variable namespace. If your high-level dialect has lexical scoping, shadowing, or closures, you need a renaming strategy. Generating fresh names naively (e.g., appending counters) is fine for correctness but can produce huge variable sets that slow down SMT encoding. Large variable sets also make verification results more brittle and harder to debug.

- The biggest performance bottleneck is usually the SMT solver. Transformations that produce smaller, more modular verification conditions (VCs) win.

- Prefer generating multiple smaller procedures with tight contracts over one monolithic procedure. The [`CallElim`](https://github.com/strata-org/Strata/blob/main/Strata/Transform/CallElim.lean) transformation replaces calls with `assert pre; havoc; assume post`, which is much cheaper than inlining entire bodies.

- If your dialect has features that map to quantifiers (e.g., `forall x in collection`), be careful — quantifiers are expensive for SMT solvers. Use triggers where possible (Lambda expressions support quantifiers with triggers) but also consider whether an encoding that does not use quantifiers is possible.

- The order you compose transformations matters. For example, if your dialect has both loops and procedure calls, translating to Core first and then running [`CallElim`](https://github.com/strata-org/Strata/blob/main/Strata/Transform/CallElim.lean) → [`LoopElim`](https://github.com/strata-org/Strata/blob/main/Strata/Transform/LoopElim.lean) is the standard pipeline. But if your high-level construct can be desugared to avoid loops entirely (e.g., bounded iteration → unrolling), doing that before hitting Core avoids the need for loop invariants.

- Core's `Map` type uses Select/Store axioms, which are well-supported by SMT but can be expensive with many updates. If your dialect has data structures that map to nested maps (e.g., objects with fields that are themselves maps), the encoding can explode. Consider flattening where possible.

- Core supports polymorphic types, but SMT-LIB has limited polymorphism support. The SMT encoder must monomorphize or use sort encodings. If your dialect introduces many generic types, the encoding overhead grows. Prefer concrete types where the high-level semantics allow it.

- Profile with actual examples early. A transformation that looks clean structurally can still produce VCs that time out on the solver.
