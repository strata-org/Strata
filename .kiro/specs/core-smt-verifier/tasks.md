# Implementation Plan: CoreSMT Verifier

## Overview

This implementation plan covers the CoreSMT Verifier for Strata Core programs. The verifier operates on a well-defined subset of Strata Core (identified by the `isCoreSMT` predicate) and translates it directly to SMT for verification using an interactive SMT solver.

The implementation follows a phased approach, starting with prerequisites and foundational components, then building up to the full verification pipeline with diagnosis support.

## Tasks

- [x] 1. Prerequisites: Extend Cmd.init for Optional RHS
  - [x] 1.1 Modify `Cmd.init` in `Strata/DL/Imperative/Cmd.lean` to support optional expression
    - Change `| init (name : P.Ident) (ty : P.Ty) (e : P.Expr)` to `| init (name : P.Ident) (ty : P.Ty) (e : Option P.Expr)`
    - _Requirements: 1.3_
  
  - [x] 1.2 Update `Statement.init` pattern in `Strata/Languages/Core/Statement.lean`
    - Update the `@match_pattern` abbreviation to handle `Option Expression.Expr`
    - _Requirements: 1.3_
  
  - [x] 1.3 Update all call sites that construct `Cmd.init` or `Statement.init`
    - Search for `Cmd.init` and `Statement.init` usages and wrap expressions in `some`
    - Update DDM parsing in `Strata/Languages/Core/DDMTransform/Parse.lean`
    - _Requirements: 1.3_
  
  - [x] 1.4 Update type checking in `Strata/Languages/Core/CmdType.lean`
    - Handle `none` case for init without expression
    - _Requirements: 1.3_
  
  - [x] 1.5 Update evaluation in `Strata/Languages/Core/CmdEval.lean`
    - Handle `none` case as equivalent to `havoc` (unconstrained variable)
    - _Requirements: 1.3_
  
  - [x] 1.6 Update semantics in `Strata/DL/Imperative/CmdSemantics.lean`
    - Define semantics for `init x : T` without RHS as declaring unconstrained variable
    - _Requirements: 1.3_

- [x] 2. Checkpoint - Ensure Cmd.init extension compiles and tests pass
  - Ensure all tests pass, ask the user if questions arise.

- [x] 3. SMT Solver Interface Implementation
  - [x] 3.1 Create `Strata/Languages/Core/CoreSMT/SMTSolverInterface.lean`
    - Define `SMTSolverInterface` structure with push, pop, declareSort, declareFun, defineFun, assert, checkSat, checkSatAssuming, getModel, reset methods
    - Use existing `Strata.SMT.Term` and `Strata.SMT.TermType` types
    - _Requirements: 7.1, 7.2, 7.3, 7.4, 7.5, 7.6, 7.7, 7.8_
  
  - [x] 3.2 Implement default solver instance using cvc5
    - Create `mkCvc5Solver : IO SMTSolverInterface` that wraps the existing `SMT.Solver`
    - Use `SMTDDM.toString` for converting `SMT.Term` to SMT-LIB strings
    - _Requirements: 7.9_
  
  - [ ]* 3.3 Write unit tests for SMT solver interface
    - Test push/pop scope management
    - Test declare-fun and define-fun
    - Test check-sat and check-sat-assuming
    - **Property 23: Push/pop preserves solver correctness**
    - **Validates: Requirements 7.6**

- [x] 4. isCoreSMT Predicate Implementation
  - [x] 4.1 Create `Strata/Languages/Core/CoreSMT/IsCoreSMT.lean`
    - Define `Statement.isCoreSMT : Statement → Bool` predicate
    - Include: assume, assert, cover, init, havoc, block (recursive), funcDecl
    - Exclude: ite, loop, goto, call, set
    - _Requirements: 2.1, 2.2, 2.3_
  
  - [x] 4.2 Define `Expression.isCoreSMT : Expression.Expr → Bool` predicate
    - Include: const, fvar, bvar, app (including immediately applied abstractions), ite (expression), quant
    - Exclude: standalone abstractions (not immediately applied)
    - _Requirements: 2.1, 2.2_
  
  - [ ]* 4.3 Write property tests for isCoreSMT predicate
    - **Property 10: Non-CoreSMT input returns error**
    - **Validates: Requirements 1.10, 2.3**

- [x] 5. CoreSMT State and Context Management
  - [x] 5.1 Create `Strata/Languages/Core/CoreSMT/State.lean`
    - Define `ContextItem` inductive (assumption, sortDecl, funcDecl, funcDef, varDecl, varDef)
    - Define `ContextScope` and `ContextStack` types
    - Define `CoreSMTConfig` structure (diagnosisEnabled, accumulateErrors, verbose)
    - Define `CoreSMTState` structure (solver, config, contextStack, results)
    - _Requirements: 1.11, 1.12, 1.13, 6.1, 6.2, 6.3_
  
  - [x] 5.2 Implement state management functions
    - `CoreSMTState.init : SMTSolverInterface → CoreSMTConfig → CoreSMTState`
    - `CoreSMTState.push : CoreSMTState → IO CoreSMTState`
    - `CoreSMTState.pop : CoreSMTState → IO CoreSMTState`
    - `CoreSMTState.addItem : CoreSMTState → ContextItem → CoreSMTState`
    - `CoreSMTState.allContextItems : CoreSMTState → List ContextItem`
    - _Requirements: 6.2, 6.3, 6.4_
  
  - [ ]* 5.3 Write property tests for state management
    - **Property 21: State reuse preserves correctness**
    - **Validates: Requirements 6.2, 6.3**

- [x] 6. Expression Translator
  - [x] 6.1 Create `Strata/Languages/Core/CoreSMT/ExprTranslator.lean`
    - Implement `translateType : Expression.Ty → SMT.TermType`
    - Implement `translateConst : Expression.Const → Except String SMT.Term`
    - _Requirements: 1.9_
  
  - [x] 6.2 Implement `translateExpr : Expression.Expr → IO (Except String SMT.Term)`
    - Handle const, fvar, bvar cases
    - Handle app case including immediately applied abstractions → SMT let
    - Handle ite (expression) case
    - Handle quant case with triggers
    - Return error for standalone abstractions
    - _Requirements: 1.9, 1.10_
  
  - [x] 6.3 Implement `translateApp` for function applications
    - Translate operator and arguments
    - Handle Core operators → SMT operators mapping
    - _Requirements: 1.9_
  
  - [ ]* 6.4 Write property tests for expression translation
    - **Property 9: Function calls translate to SMT applications**
    - **Validates: Requirements 1.9**

- [x] 7. Checkpoint - Ensure expression translator compiles and tests pass
  - Ensure all tests pass, ask the user if questions arise.

- [x] 8. Statement Processor
  - [x] 8.1 Create `Strata/Languages/Core/CoreSMT/StmtProcessor.lean`
    - Implement `processAssume : CoreSMTState → String → Expression.Expr → IO CoreSMTState`
    - Add expression to solver state via `solver.assert`
    - Track in context as `ContextItem.assumption`
    - _Requirements: 1.1_
  
  - [x] 8.2 Implement `processInit` for init statements
    - With expression: emit `define-fun`, track as `varDef`
    - Without expression: emit `declare-fun`, track as `varDecl`
    - _Requirements: 1.2, 1.3_
  
  - [x] 8.3 Implement `processAssert` for assert statements
    - Perform proof check using push/pop (check-sat of negation)
    - Do NOT modify solver state after check
    - Return VCResult with outcome
    - _Requirements: 1.4_
  
  - [x] 8.4 Implement `processCover` for cover statements
    - Perform reachability check (check-sat of expression)
    - sat → reachable, unsat → unreachable
    - Return VCResult with outcome
    - _Requirements: 1.5_
  
  - [x] 8.5 Implement `processBlock` for block statements
    - Call `state.push` before processing inner statements
    - Process each inner statement sequentially
    - Call `state.pop` after processing
    - _Requirements: 1.6_
  
  - [x] 8.6 Implement `processFuncDecl` for function declarations
    - Without body: emit `declare-fun`
    - With body: emit `define-fun` or equivalent axiom
    - _Requirements: 1.7, 1.8_
  
  - [x] 8.7 Implement `processHavoc` for havoc statements
    - Declare fresh unconstrained variable via `declare-fun`
    - _Requirements: 1.3_
  
  - [x] 8.8 Implement main `processStatement : CoreSMTState → Statement → IO (CoreSMTState × Option VCResult)`
    - Check `stmt.isCoreSMT`, return error if false
    - Dispatch to appropriate handler based on statement type
    - _Requirements: 1.10, 1.11_
  
  - [ ]* 8.9 Write property tests for statement processor
    - **Property 1: Assume adds to solver state**
    - **Property 2: Init with expression emits define-fun**
    - **Property 3: Init without expression emits declare-fun**
    - **Property 4: Assert performs proof check without state modification**
    - **Property 5: Cover performs reachability check**
    - **Property 6: Block emits push/pop and processes inner statements**
    - **Property 7: Function declaration without body emits declare-fun**
    - **Property 8: Function declaration with body emits define-fun**
    - **Validates: Requirements 1.1, 1.2, 1.3, 1.4, 1.5, 1.6, 1.7, 1.8**

- [ ] 9. VCResult Extensions
  - [ ] 9.1 Extend `Core.Outcome` in `Strata/Languages/Core/Verifier.lean`
    - Add `refuted` case for provably false assertions
    - Update `smtResultToOutcome` to handle refuted case
    - _Requirements: 3.2_
  
  - [ ] 9.2 Extend `Core.VCResult` structure
    - Add `diagnosis : Option DiagnosisResult` field
    - _Requirements: 3.1, 4.7_
  
  - [ ]* 9.3 Write property tests for VCResult
    - **Property 11: VCResult contains correct information**
    - **Property 19: Refuted outcome in VCResult**
    - **Validates: Requirements 1.12, 3.2**

- [x] 10. Checkpoint - Ensure statement processor compiles and tests pass
  - Ensure all tests pass, ask the user if questions arise.

- [ ] 11. Diagnosis Engine
  - [ ] 11.1 Create `Strata/Languages/Core/CoreSMT/Diagnosis.lean`
    - Define `DiagnosedFailure` structure (expression, isRefuted, result)
    - Define `DiagnosisResult` structure (originalCheck, diagnosedFailures)
    - _Requirements: 4.1, 4.7_
  
  - [ ] 11.2 Implement `splitConjunction : Expression.Expr → Option (Expression.Expr × Expression.Expr)`
    - Detect conjunction expressions (And operator)
    - Return left and right conjuncts
    - _Requirements: 4.3_
  
  - [ ] 11.3 Implement `checkRefuted : CoreSMTState → Expression.Expr → IO Bool`
    - Use push/pop to check if expression is provably false
    - Assert expression, check-sat, return true if unsat
    - _Requirements: 4.5_
  
  - [ ] 11.4 Implement `diagnoseFailure : CoreSMTState → Expression.Expr → Bool → IO DiagnosisResult`
    - Recursively split conjunctions
    - For proof checks: diagnose all conjuncts
    - For cover checks: stop after first unreachable conjunct
    - When diagnosing RHS, temporarily assume LHS as context
    - _Requirements: 4.2, 4.3, 4.4, 4.5, 4.6_
  
  - [ ]* 11.5 Write property tests for diagnosis engine
    - **Property 13: Diagnosis applies when enabled and proof fails**
    - **Property 14: Conjunction splitting diagnoses both conjuncts**
    - **Property 15: Right conjunct diagnosis assumes left conjunct**
    - **Property 16: Refuted detection distinguishes provably false**
    - **Property 17: Cover diagnosis stops after first unreachable**
    - **Property 18: Diagnosed failures include context**
    - **Validates: Requirements 4.2, 4.3, 4.4, 4.5, 4.6, 4.7**

- [x] 12. Public Interface
  - [x] 12.1 Create `Strata/Languages/Core/CoreSMT/Verifier.lean`
    - Implement `verify : CoreSMTState → List Statement → IO (CoreSMTState × Array VCResult)`
    - Process statements sequentially
    - Accumulate results based on config
    - Return updated state for reuse
    - _Requirements: 6.1, 6.2, 6.3_
  
  - [x] 12.2 Implement `processPrelude : CoreSMTState → List Statement → IO CoreSMTState`
    - Process prelude statements to initialize state
    - Return state ready for subsequent verification calls
    - _Requirements: 6.5_
  
  - [x] 12.3 Create main module `Strata/Languages/Core/CoreSMT.lean`
    - Export all CoreSMT components
    - Provide convenience functions for common use cases
    - _Requirements: 6.1_
  
  - [ ]* 12.4 Write property tests for public interface
    - **Property 12: Error accumulation collects all errors**
    - **Property 22: Prelude state reuse**
    - **Validates: Requirements 3.3, 6.5**

- [x] 13. Checkpoint - Ensure public interface compiles and tests pass
  - Ensure all tests pass, ask the user if questions arise.

- [ ] 14. B3 to Core Converter for Test Migration
  - [ ] 14.1 Create `Strata/Languages/B3/ToCore.lean`
    - Implement `convertExpr : B3AST.Expression M → Core.Expression.Expr`
    - Handle literals, identifiers, binary/unary ops, ite, function calls, quantifiers, let expressions
    - _Requirements: 5.1, 5.2_
  
  - [ ] 14.2 Implement `convertStmt : B3AST.Statement M → Core.Statement`
    - B3 check → Core assert
    - B3 assert → Core assert
    - B3 assume → Core assume
    - B3 reach → Core cover
    - B3 blockStmt → Core block
    - _Requirements: 5.3_
  
  - [ ] 14.3 Implement `convertFuncDecl : B3AST.FunctionDecl M → Core.Statement`
    - Convert function parameters and return type
    - Convert optional body
    - _Requirements: 5.4_
  
  - [ ] 14.4 Implement `convertProgram : B3AST.Program M → List Core.Statement`
    - Convert all function declarations and statements
    - _Requirements: 5.1_
  
  - [ ]* 14.5 Write property tests for B3 to Core conversion
    - **Property 20: Equivalent results via B3 to Core conversion**
    - **Validates: Requirements 5.5**

- [ ] 15. Test Migration and Validation
  - [ ] 15.1 Create test harness `testB3ViaCoreVerification`
    - Parse B3 DDM syntax to B3 AST
    - Convert B3 AST to Core AST via B3ToCore
    - Verify Core AST via CoreSMT_Verifier
    - Return VCResult with diagnosis
    - _Requirements: 5.5, 5.7_
  
  - [ ] 15.2 Migrate existing B3 verifier tests to use new pipeline
    - Update `StrataTest/Languages/B3/Verifier/VerifierTests.lean`
    - Tests continue to use B3 DDM syntax (no rewriting)
    - Verify equivalent results
    - _Requirements: 5.5, 5.7_
  
  - [ ] 15.3 Remove direct B3 to SMT translation
    - Remove `Strata/Languages/B3/Verifier/Expression.lean` (B3→SMT conversion)
    - Remove `Strata/Languages/B3/Verifier/Statements.lean` (B3 statement processing)
    - Update B3 verifier entry point to use B3→Core→CoreSMT pipeline
    - _Requirements: 5.6_

- [ ] 16. Integration Tests
  - [ ] 16.1 Create integration test suite in `StrataTest/Languages/Core/CoreSMT/`
    - Test end-to-end verification with cvc5
    - Test diagnosis workflow on complex assertions
    - Test state reuse across multiple verification calls
    - _Requirements: 6.2, 6.3, 4.2_
  
  - [ ]* 16.2 Write property tests for model extraction
    - **Property 24: Model extraction on sat/unknown**
    - **Validates: Requirements 7.7**

- [ ] 17. Final Checkpoint - Ensure all tests pass
  - Ensure all tests pass, ask the user if questions arise.
  - Verify B3 tests produce equivalent results through new pipeline.
  - Verify diagnosis works correctly on failed verifications.

## Notes

- Tasks marked with `*` are optional and can be skipped for faster MVP
- Each task references specific requirements for traceability
- Checkpoints ensure incremental validation
- Property tests validate universal correctness properties
- Unit tests validate specific examples and edge cases
- The B3 to Core converter enables test migration without rewriting tests
- State reuse enables prelude processing and incremental verification
