# Performant Ordering Variable Numbering - Implementation Tasks

## Implementation Strategy

**Implementation Order**: We will implement changes to the **Lambda Calculus layer first**, then the Imperative layer, then translations and backends. This order is chosen because:
1. Lambda calculus is the foundation - both bvar and fvar changes happen here
2. Imperative layer depends on fvar being updated
3. Translations depend on both layers being complete

**Compiler-Driven Approach**: Make breaking changes, then fix what the compiler complains about.

---

## Phase 1: Core Infrastructure (Foundation)

**Goal**: Establish the basic structures and monad without breaking existing code.

- [ ] 1.1 Create `Strata/Core/NextFree.lean` with `NextFree α` structure
  - [ ] 1.1.1 Define `NextFree` structure with `content` and `nextFree` fields and `HasVars α` constraint
  - [ ] 1.1.2 Implement `NextFree.empty` constructor
  - [ ] 1.1.3 Implement `NextFree.withFreshCounter` constructor
  - [ ] 1.1.4 Define `NextFree.wellFormed` invariant using `HasVars.vars`
  - [ ] 1.1.5 Define `NextFree.wellFormed'` alternative formulation
  - [ ] 1.1.6 Prove `wellFormed_iff_wellFormed'` equivalence
  - [ ] 1.1.7 Add basic helper functions

- [ ] 1.2 Add `HasVars` typeclass to `Strata/DL/Imperative/HasVars.lean`
  - [ ] 1.2.1 Review existing `HasVarsPure` and `HasVarsImp` typeclasses
  - [ ] 1.2.2 Define generic `HasVars` typeclass with `vars : α → List Nat`
  - [ ] 1.2.3 Add default instance for types with `HasVarsPure` (uses `getVars`)
  - [ ] 1.2.4 Add default instance for types with `HasVarsImp` (uses `touchedVars`)
  - [ ] 1.2.5 Verify compilation

- [ ] 1.2 Create `Strata/Core/FreshM.lean` with monad implementation
  - [ ] 1.2.1 Define `FreshM` as `StateM Nat`
  - [ ] 1.2.2 Implement `freshVar` function
  - [ ] 1.2.3 Implement `freshVars` function for multiple variables
  - [ ] 1.2.4 Implement `FreshM.run` function
  - [ ] 1.2.5 Implement `FreshM.runProgram` function
  - [ ] 1.2.6 Prove `freshVar_is_fresh` lemma

- [ ] 1.3 Create `Strata/Core/VarContext.lean` with display context
  - [ ] 1.3.1 Define `VarContext` structure
  - [ ] 1.3.2 Implement `VarContext.empty`
  - [ ] 1.3.3 Implement `VarContext.insert`
  - [ ] 1.3.4 Implement `VarContext.lookup`
  - [ ] 1.3.5 Implement `VarContext.lookupName`
  - [ ] 1.3.6 Implement `VarContext.lookupType`
  - [ ] 1.3.7 Implement `VarContext.fromGlobals`

- [ ] 1.4 Verify infrastructure compiles independently
  - [ ] 1.4.1 Run `lake build` on new files
  - [ ] 1.4.2 Fix any compilation errors
  - [ ] 1.4.3 Ensure no existing code is broken

**Success Criteria**: New code compiles, existing code unchanged.

---

## Phase 2: Lambda Calculus Migration (FIRST IMPLEMENTATION PHASE)

**Goal**: Update LExpr to use Performant Ordering.

**Why First**: Lambda calculus is the foundation. Both `bvar` (lambda-bound variables) and `fvar` (imperative variables) are defined in LExpr, so we must update this layer before the imperative layer can use the new fvar representation.

- [ ] 2.1 Update `Strata/DL/Lambda/LExpr.lean` AST definition
  - [ ] 2.1.1 Change `LExpr.bvar` to use only `Nat` index (remove hint string)
  - [ ] 2.1.2 Change `LExpr.fvar` to use only `Nat` index (remove hint string and `Identifier`)
  - [ ] 2.1.3 Update `LExpr.abs` to store parameter `Nat` + `name : String`
  - [ ] 2.1.4 Update `LExpr.quant` to store `var : Nat` + `name : String` for the bound variable
  - [ ] 2.1.5 Run `lake build` to identify broken files
  - [ ] 2.1.6 Create `broken-files-lambda.md` to track compilation errors

- [ ] 2.2 Remove index shifting functions
  - [ ] 2.2.1 Identify all index shifting functions in Lambda layer
  - [ ] 2.2.2 Remove `shift`, `weaken`, `lift` functions
  - [ ] 2.2.3 Remove all calls to these functions
  - [ ] 2.2.4 Document removed functions in migration notes

- [ ] 2.3 Simplify substitution in `Strata/DL/Lambda/LExpr.lean`
  - [ ] 2.3.1 Update `substitute` to use direct replacement (no shifting)
  - [ ] 2.3.2 Remove index adjustment logic
  - [ ] 2.3.3 Test substitution with simple examples
  - [ ] 2.3.4 Verify compilation

- [ ] 2.4 Simplify beta reduction
  - [ ] 2.4.1 Update `betaReduce` to use simple substitution
  - [ ] 2.4.2 Remove index adjustment logic
  - [ ] 2.4.3 Test beta reduction with simple examples
  - [ ] 2.4.4 Verify compilation

- [ ] 2.5 Update alpha conversion
  - [ ] 2.5.1 Implement `alphaConvert` using `FreshM`
  - [ ] 2.5.2 Generate fresh variable numbers
  - [ ] 2.5.3 Remove index adjustment logic
  - [ ] 2.5.4 Test alpha conversion
  - [ ] 2.5.5 Verify compilation

- [ ] 2.6 Update evaluation in `Strata/DL/Lambda/LExprEval.lean`
  - [ ] 2.6.1 Change environment to use `Map Nat Value`
  - [ ] 2.6.2 Update variable lookup to use numbers
  - [ ] 2.6.3 Remove index-based lookup logic
  - [ ] 2.6.4 Update all evaluation cases
  - [ ] 2.6.5 Verify compilation

- [ ] 2.7 Update type checking in `Strata/DL/Lambda/LExprType*.lean`
  - [ ] 2.7.1 Change type environment to use `Map Nat Type`
  - [ ] 2.7.2 Update type lookup to use numbers
  - [ ] 2.7.3 Update all type checking cases
  - [ ] 2.7.4 Verify compilation

- [ ] 2.8 Update well-formedness in `Strata/DL/Lambda/LExprWF.lean`
  - [ ] 2.8.1 Remove De Bruijn well-formedness checks
  - [ ] 2.8.2 Add Performant Ordering well-formedness checks
  - [ ] 2.8.3 Update all well-formedness lemmas
  - [ ] 2.8.4 Add `sorry` for broken proofs with TODO comments
  - [ ] 2.8.5 Document broken proofs in `broken-proofs.md`

- [ ] 2.9 Update semantics in `Strata/DL/Lambda/Semantics.lean`
  - [ ] 2.9.1 Update semantic definitions to use numbers
  - [ ] 2.9.2 Remove index-based semantic rules
  - [ ] 2.9.3 Update all semantic lemmas
  - [ ] 2.9.4 Add `sorry` for broken proofs with TODO comments
  - [ ] 2.9.5 Verify compilation

- [ ] 2.10 Update scope handling in `Strata/DL/Lambda/Scopes.lean`
  - [ ] 2.10.1 Implement `ScopeStack` structure
  - [ ] 2.10.2 Implement scope operations (push, pop, lookup, insert)
  - [ ] 2.10.3 Update scope-related functions
  - [ ] 2.10.4 Verify compilation

- [ ] 2.11 Fix all broken Lambda layer files
  - [ ] 2.11.1 Review `broken-files-lambda.md`
  - [ ] 2.11.2 Fix each file systematically
  - [ ] 2.11.3 Run `lake build` after each fix
  - [ ] 2.11.4 Continue until Lambda layer compiles

**Success Criteria**: Lambda calculus layer compiles with simplified operations.

---

## Phase 3: Imperative Layer Migration (SECOND IMPLEMENTATION PHASE)

**Goal**: Update Cmd to use Performant Ordering.

**Why Second**: Imperative layer uses `fvar` from LExpr, so it must be updated after the lambda calculus layer is complete.

- [ ] 3.1 Update `Strata/DL/Imperative/Cmd.lean` definition
  - [ ] 3.1.1 Update `Cmd.init` to store `hint : String`, `var : Nat`, `ty : P.Ty`, `e : Option P.Expr`
  - [ ] 3.1.2 Update `Cmd.set` to use `var : Nat`
  - [ ] 3.1.3 Update `Cmd.havoc` to use `var : Nat`
  - [ ] 3.1.4 Ensure all constructors have `md : MetaData P` parameter
  - [ ] 3.1.5 Run `lake build` to identify broken files
  - [ ] 3.1.6 Create `broken-files-imperative.md` to track compilation errors

- [ ] 3.2 Update `Cmd.modifiedVars` implementation
  - [ ] 3.2.1 Change return type to `List Nat`
  - [ ] 3.2.2 Update `init` case to return empty list
  - [ ] 3.2.3 Update `set` case to return `[var]`
  - [ ] 3.2.4 Update `havoc` case to return `[var]`
  - [ ] 3.2.5 Verify compilation

- [ ] 3.3 Implement `Cmd.definedVars`
  - [ ] 3.3.1 Define function with return type `List String`
  - [ ] 3.3.2 Implement `init` case to return `[hint]`
  - [ ] 3.3.3 Implement other cases to return empty list
  - [ ] 3.3.4 Verify compilation

- [ ] 3.4 Update evaluation in `Strata/DL/Imperative/CmdEval.lean`
  - [ ] 3.4.1 Update `EvalContext` to track `nextVar`
  - [ ] 3.4.2 Implement `incrementNextVar` function
  - [ ] 3.4.3 Update `Cmd.eval` for `init` with `some e`
  - [ ] 3.4.4 Update `Cmd.eval` for `init` with `none`
  - [ ] 3.4.5 Update `Cmd.eval` for `set`
  - [ ] 3.4.6 Update `Cmd.eval` for `havoc`
  - [ ] 3.4.7 Verify compilation

- [ ] 3.5 Update type checking in `Strata/DL/Imperative/CmdType.lean`
  - [ ] 3.5.1 Change type environment to use `Map Nat Type`
  - [ ] 3.5.2 Update type lookup to use numbers
  - [ ] 3.5.3 Update all type checking cases
  - [ ] 3.5.4 Verify compilation

- [ ] 3.6 Update semantics in `Strata/DL/Imperative/CmdSemantics.lean`
  - [ ] 3.6.1 Update semantic definitions to use numbers
  - [ ] 3.6.2 Remove name-based semantic rules
  - [ ] 3.6.3 Update all semantic lemmas
  - [ ] 3.6.4 Add `sorry` for broken proofs with TODO comments
  - [ ] 3.6.5 Verify compilation

- [ ] 3.7 Update statement handling in `Strata/DL/Imperative/Stmt.lean`
  - [ ] 3.7.1 Update statement operations to use numbers
  - [ ] 3.7.2 Update all statement cases
  - [ ] 3.7.3 Verify compilation

- [ ] 3.8 Update statement semantics in `Strata/DL/Imperative/StmtSemantics.lean`
  - [ ] 3.8.1 Update semantic definitions to use numbers
  - [ ] 3.8.2 Update all semantic cases
  - [ ] 3.8.3 Add `sorry` for broken proofs with TODO comments
  - [ ] 3.8.4 Verify compilation

- [ ] 3.9 Update semantic properties in `Strata/DL/Imperative/SemanticsProps.lean`
  - [ ] 3.9.1 Update property definitions to use numbers
  - [ ] 3.9.2 Update all property lemmas
  - [ ] 3.9.3 Add `sorry` for broken proofs with TODO comments
  - [ ] 3.9.4 Verify compilation

- [ ] 3.10 Implement pretty printing
  - [ ] 3.10.1 Implement `formatVar` function
  - [ ] 3.10.2 Implement `formatCmd` function
  - [ ] 3.10.3 Implement `formatExpr` function
  - [ ] 3.10.4 Handle disambiguation with @N suffix
  - [ ] 3.10.5 Verify compilation

- [ ] 3.11 Fix all broken Imperative layer files
  - [ ] 3.11.1 Review `broken-files-imperative.md`
  - [ ] 3.11.2 Fix each file systematically
  - [ ] 3.11.3 Run `lake build` after each fix
  - [ ] 3.11.4 Continue until Imperative layer compiles

**Success Criteria**: Imperative layer compiles with number-based variables.

---

## Phase 4: Translation and Backend Updates (THIRD IMPLEMENTATION PHASE)

**Goal**: Update all language frontends and backends.

**Why Third**: Translations depend on both lambda calculus and imperative layers being complete.

- [ ] 4.1 Update Strata Core language in `Strata/Languages/Core/`
  - [ ] 4.1.1 Update `Expressions.lean` to remove `old()` constructor
  - [ ] 4.1.2 Update `Statement.lean` to use Performant Ordering
  - [ ] 4.1.3 Update `Procedure.lean` to use Performant Ordering
  - [ ] 4.1.4 Add `preStateCopies` field to Procedure structure
  - [ ] 4.1.5 Update `Program.lean` to use Performant Ordering
  - [ ] 4.1.6 Update `Verifier.lean` to use FreshM
  - [ ] 4.1.7 Update `SMTEncoder.lean` to use SMTContext
  - [ ] 4.1.8 Verify compilation

- [ ] 4.2 Implement SMT encoding with SMTContext
  - [ ] 4.2.1 Create `SMTContext` structure
  - [ ] 4.2.2 Implement `SMTContext.empty`
  - [ ] 4.2.3 Implement `SMTContext.addVar`
  - [ ] 4.2.4 Implement `SMTContext.lookupVar`
  - [ ] 4.2.5 Update SMT encoding to use SMTContext
  - [ ] 4.2.6 Verify compilation

- [ ] 4.3 Update C_Simp translation in `Strata/Languages/C_Simp/`
  - [ ] 4.3.1 Update translation to use FreshM
  - [ ] 4.3.2 Implement scope stack for shadowing
  - [ ] 4.3.3 Assign fresh numbers to all variables
  - [ ] 4.3.4 Update all translation functions
  - [ ] 4.3.5 Verify compilation

- [ ] 4.4 Implement old() elimination in procedure translation
  - [ ] 4.4.1 Identify modified globals from procedure's modifies clause
  - [ ] 4.4.2 Generate fresh variables for pre-state copies of modified globals only
  - [ ] 4.4.3 Insert initialization statements at procedure entry to copy globals
  - [ ] 4.4.4 Implement `replaceOldReferences` function for global variables
  - [ ] 4.4.5 Replace all `old(global)` references with pre-state variable references
  - [ ] 4.4.6 Update procedure structure to include `preStateCopies`
  - [ ] 4.4.7 Verify compilation

- [ ] 4.5 Update transformations to use FreshM
  - [ ] 4.5.1 Update `CallElim.lean` to use FreshM
  - [ ] 4.5.2 Update `LoopElim.lean` to use FreshM
  - [ ] 4.5.3 Update `DetToNondet.lean` to use FreshM
  - [ ] 4.5.4 Update `ProcedureInlining.lean` to use FreshM
  - [ ] 4.5.5 Verify compilation

- [ ] 4.6 Update loop elimination
  - [ ] 4.6.1 Update to generate havoc statements using variable numbers
  - [ ] 4.6.2 Use `modifiedVars` to get list of indices
  - [ ] 4.6.3 Generate fresh numbers for loop-related variables
  - [ ] 4.6.4 Verify compilation

- [ ] 4.7 Update procedure inlining
  - [ ] 4.6.1 Generate fresh numbers for all parameters
  - [ ] 4.6.2 Generate fresh numbers for all locals
  - [ ] 4.6.3 Update substitution to use numbers
  - [ ] 4.6.4 Verify compilation

- [ ] 4.7 Update all other language frontends
  - [ ] 4.7.1 Update Dyn translation if needed
  - [ ] 4.7.2 Update Laurel translation if needed
  - [ ] 4.7.3 Update Python translation if needed
  - [ ] 4.7.4 Verify compilation

- [ ] 4.8 Update CBMC backend in `Strata/Backends/CBMC/`
  - [ ] 4.8.1 Update to use variable numbers
  - [ ] 4.8.2 Update GOTO translation
  - [ ] 4.8.3 Verify compilation

**Success Criteria**: All translations and backends compile.

---

## Phase 5: Proof Restoration (FINAL PHASE)

**Goal**: Restore all proofs to working state.

- [ ] 5.1 Remove De Bruijn shifting lemmas
  - [ ] 5.1.1 Identify all shifting lemmas
  - [ ] 5.1.2 Remove lemmas that are no longer needed
  - [ ] 5.1.3 Document removed lemmas

- [ ] 5.2 Prove freshness lemmas for FreshM
  - [ ] 5.2.1 Prove `freshVar_is_fresh`
  - [ ] 5.2.2 Prove `freshVars_generates_unique`
  - [ ] 5.2.3 Prove `freshVar_generates_above`
  - [ ] 5.2.4 Prove other freshness properties

- [ ] 5.3 Prove substitution correctness
  - [ ] 5.3.1 Prove `substitute_preserves_semantics`
  - [ ] 5.3.2 Prove substitution is simpler than De Bruijn version
  - [ ] 5.3.3 Prove all substitution lemmas

- [ ] 5.4 Prove transformation correctness
  - [ ] 5.4.1 Update `CallElimCorrect.lean` proofs
  - [ ] 5.4.2 Update `DetToNondetCorrect.lean` proofs
  - [ ] 5.4.3 Prove other transformation correctness lemmas

- [ ] 5.5 Prove invariant preservation
  - [ ] 5.5.1 Prove `transform_preserves_freshness`
  - [ ] 5.5.2 Prove `transform_preserves_uniqueness`
  - [ ] 5.5.3 Prove all invariant preservation lemmas

- [ ] 5.6 Update all semantic proofs
  - [ ] 5.6.1 Review `broken-proofs.md`
  - [ ] 5.6.2 Fix each proof systematically
  - [ ] 5.6.3 Remove all `sorry` placeholders
  - [ ] 5.6.4 Verify all proofs compile

- [ ] 5.7 Final proof verification
  - [ ] 5.7.1 Run `lake build` to ensure all proofs compile
  - [ ] 5.7.2 Search for remaining `sorry` placeholders
  - [ ] 5.7.3 Fix any remaining proof issues
  - [ ] 5.7.4 Verify no `sorry` remains

**Success Criteria**: All proofs compile, no `sorry` remains.

---

## Phase 6: Testing and Validation

**Goal**: Ensure all tests pass.

- [ ] 6.1 Update Lambda layer tests in `StrataTest/DL/Lambda/`
  - [ ] 6.1.1 Update `Lambda.lean` tests
  - [ ] 6.1.2 Update `LExprEvalTests.lean` tests
  - [ ] 6.1.3 Update `LExprTTests.lean` tests
  - [ ] 6.1.4 Update `TypeFactoryTests.lean` tests
  - [ ] 6.1.5 Run tests and fix failures

- [ ] 6.2 Update Imperative layer tests in `StrataTest/DL/Imperative/`
  - [ ] 6.2.1 Update all test files
  - [ ] 6.2.2 Update test expectations if needed
  - [ ] 6.2.3 Run tests and fix failures

- [ ] 6.3 Update Core language tests in `StrataTest/Languages/Core/`
  - [ ] 6.3.1 Update all test files
  - [ ] 6.3.2 Update test expectations if needed
  - [ ] 6.3.3 Run tests and fix failures

- [ ] 6.4 Update transformation tests in `StrataTest/Transform/`
  - [ ] 6.4.1 Update `CallElim.lean` tests
  - [ ] 6.4.2 Update `DetToNondet.lean` tests
  - [ ] 6.4.3 Update `ProcedureInlining.lean` tests
  - [ ] 6.4.4 Run tests and fix failures

- [ ] 6.5 Update all other tests
  - [ ] 6.5.1 Update C_Simp tests if needed
  - [ ] 6.5.2 Update Dyn tests if needed
  - [ ] 6.5.3 Update CBMC tests if needed
  - [ ] 6.5.4 Run tests and fix failures

- [ ] 6.6 Run full test suite
  - [ ] 6.6.1 Run `lake test`
  - [ ] 6.6.2 Fix any test failures
  - [ ] 6.6.3 Verify all tests pass

- [ ] 6.7 Verify examples work
  - [ ] 6.7.1 Run all examples in `Examples/`
  - [ ] 6.7.2 Verify output is correct
  - [ ] 6.7.3 Fix any example issues

- [ ] 6.8 Performance testing
  - [ ] 6.8.1 Measure compilation time
  - [ ] 6.8.2 Measure test execution time
  - [ ] 6.8.3 Compare with baseline
  - [ ] 6.8.4 Document performance results

- [ ] 6.9 Final validation
  - [ ] 6.9.1 Run `lake build` - must succeed
  - [ ] 6.9.2 Run `lake test` - must pass all tests
  - [ ] 6.9.3 Verify no `sorry` remains
  - [ ] 6.9.4 Verify all examples work
  - [ ] 6.9.5 Document completion

**Success Criteria**: Full test suite passes, all examples work.

---

## Success Criteria Summary

### Compilation
- [ ] `lake build` succeeds with no errors
- [ ] No compilation warnings related to variable numbering
- [ ] All modules compile successfully

### Testing
- [ ] `lake test` passes all tests
- [ ] No test failures
- [ ] Test coverage maintained or improved

### Proofs
- [ ] No `sorry` placeholders remain
- [ ] All freshness lemmas proven
- [ ] All substitution lemmas proven
- [ ] All transformation correctness proofs restored
- [ ] All invariant preservation proofs complete

### Code Quality
- [ ] All De Bruijn index shifting code removed
- [ ] All De Bruijn weakening code removed
- [ ] All De Bruijn lifting code removed
- [ ] Code is simpler and more maintainable
- [ ] Documentation updated

### Functionality
- [ ] All examples work correctly
- [ ] All translations work
- [ ] SMT encoding works
- [ ] Verification produces correct results

---

## Notes

- **Incremental Approach**: Fix one file at a time, verify compilation after each fix
- **Track Progress**: Maintain `broken-files-lambda.md`, `broken-files-imperative.md`, and `broken-proofs.md`
- **Proof Strategy**: Add `sorry` with TODO comments for broken proofs, restore them in Phase 5
- **Testing**: Run tests frequently to catch regressions early
- **Documentation**: Update documentation as changes are made
