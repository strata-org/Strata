# PR #488 Review Checklist: Remove Visibility from CoreIdent and old() expressions

## Files to Review

### Examples
- [ ] Examples/HeapReasoning.core.st
- [ ] Examples/SimpleProc.core.st  
- [ ] Examples/expected/SimpleProc.core.expected

### Core Language Implementation
- [ ] Strata/Languages/Core/CmdEval.lean
- [ ] Strata/Languages/Core/CmdType.lean
- [ ] Strata/Languages/Core/CoreGen.lean
- [ ] Strata/Languages/Core/DDMTransform/Grammar.lean
- [ ] Strata/Languages/Core/DDMTransform/Translate.lean
- [ ] Strata/Languages/Core/Env.lean
- [ ] Strata/Languages/Core/Expressions.lean
- [ ] Strata/Languages/Core/Factory.lean
- [ ] Strata/Languages/Core/Function.lean
- [ ] Strata/Languages/Core/Identifiers.lean
- [ ] Strata/Languages/Core/OldExpressions.lean (DELETED)
- [ ] Strata/Languages/Core/Procedure.lean
- [ ] Strata/Languages/Core/ProcedureEval.lean
- [ ] Strata/Languages/Core/ProcedureType.lean
- [ ] Strata/Languages/Core/ProgramWF.lean
- [ ] Strata/Languages/Core/Statement.lean
- [ ] Strata/Languages/Core/StatementEval.lean
- [ ] Strata/Languages/Core/StatementSemantics.lean
- [ ] Strata/Languages/Core/StatementSemanticsProps.lean
- [ ] Strata/Languages/Core/StatementType.lean
- [ ] Strata/Languages/Core/TypeDecl.lean
- [ ] Strata/Languages/Core/WF.lean

### Other Languages
- [ ] Strata/Languages/C_Simp/Verify.lean
- [ ] Strata/Languages/Laurel/Grammar/LaurelGrammar.lean
- [ ] Strata/Languages/Laurel/LaurelToCoreTranslator.lean
- [ ] Strata/Languages/Python/PythonToCore.lean

### Transformations
- [ ] Strata/Transform/CallElim.lean
- [ ] Strata/Transform/CallElimCorrect.lean
- [ ] Strata/Transform/PrecondElim.lean
- [ ] Strata/Transform/ProcedureInlining.lean

### Tests
- [ ] StrataTest/Backends/CBMC/CoreToCProverGOTO.lean
- [ ] StrataTest/DL/Imperative/FormatStmtTest.lean
- [ ] StrataTest/Languages/Core/Examples/DDMAxiomsExtraction.lean
- [ ] StrataTest/Languages/Core/Examples/DDMTransform.lean
- [ ] StrataTest/Languages/Core/Examples/FunctionDeclDDMTest.lean
- [ ] StrataTest/Languages/Core/Examples/OldExpressions.lean
- [ ] StrataTest/Languages/Core/Examples/ProcedureCall.lean
- [ ] StrataTest/Languages/Core/Examples/SafeMap.lean
- [ ] StrataTest/Languages/Core/Examples/SelectiveVerification.lean
- [ ] StrataTest/Languages/Core/Examples/SimpleProc.lean
- [ ] StrataTest/Languages/Core/ExprEvalTest.lean
- [ ] StrataTest/Languages/Core/FunctionTests.lean
- [ ] StrataTest/Languages/Core/OldExpressionsTests.lean
- [ ] StrataTest/Languages/Core/ProcedureEvalTests.lean
- [ ] StrataTest/Languages/Core/ProcedureTypeTests.lean
- [ ] StrataTest/Languages/Core/SMTEncoderDatatypeTest.lean
- [ ] StrataTest/Languages/Core/SarifOutputTests.lean
- [ ] StrataTest/Languages/Core/StatementEvalTests.lean
- [ ] StrataTest/Languages/Core/StatementTypeTests.lean
- [ ] StrataTest/Languages/Core/TestASTtoCST.lean
- [ ] StrataTest/Transform/CallElim.lean
- [ ] StrataTest/Transform/ProcedureInlining.lean

### External Tools
- [ ] Tools/BoogieToStrata/Source/StrataGenerator.cs

## Key Changes to Verify
1. `CoreIdent` changed from `Lambda.Identifier Visibility` to `Lambda.Identifier Unit`
2. All `.unres`/`.locl`/`.glob`/`.temp` replaced with `⟨name, ()⟩`
3. `OldExpressions.lean` deleted
4. `old(g)` syntax replaced by `old g` (no parentheses)
5. Type checker adds `"old g"` to postcondition context
6. VCG substitutes `"old g"` with pre-state values