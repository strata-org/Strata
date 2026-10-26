/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Implementation.LaurelPipelinePrinter

/-! ## The rendered shape lifeline table

Pinning the table here captures the state of the pipeline: a change to what a
pass creates, removes or rejects shows up as a diff in the expected output. -/

/-- info: V starts holding here   | holds, and is carried on   + required here, holds, and is carried on
' was holding, and is dropped here   : not holding, but would be carried   (blank) not holding, and would not be carried
S: LaurelProgram.staticFunctions.cons   O: Program.Ordered   N: Pseudo.needsOverrideRules
I: StmtExpr.IncrDecr   C: StmtExpr.CompoundAssign   Ic: CompositeType.instanceProcedures.cons
R: StmtExpr.Return.value.some   T: CompositeType.typeArgs.cons   In: StmtExpr.InstanceCall
Co: TypeDefinition.Composite   Ne: StmtExpr.New   Is: StmtExpr.IsType
A: StmtExpr.AsType   tC: TypeDefinition.Constrained   Th: StmtExpr.Throw
Tr: StmtExpr.Try   Im: Pseudo.implicitHeap   Ts: Procedure.throwsType.some
H: StmtExpr.Hole.type.none   Tf: StmtExpr.Try.finally?.some   Re: StmtExpr.Return
Sc: LaurelProgram.staticFields.cons   Ov: Pseudo.overload   pI: Pseudo.imperativeShortCircuit
W: StmtExpr.While.postTest.true   V: StmtExpr.Var.var.Field   P: StmtExpr.PureFieldUpdate
Ol: StmtExpr.Old.label?.some   pO: Pseudo.oldExpr   Y: StmtExpr.Yield
sR: StmtExpr.Resume   Ha: StmtExpr.HasNext   Hd: StmtExpr.Hole.deterministic.true
St: Pseudo.statementExpression   L: Pseudo.letExpr   sT: StmtExpr.This
pM: Pseudo.imperativeFunction   U: Program.Unordered   Al: TypeDefinition.Alias
pN: Pseudo.needsLoopInvariantChecks   M: Pseudo.mutatedInput   CC: Procedure.contracts.Coroutine
sO: StmtExpr.OldGuarantee   sL: StmtExpr.OldRelies

                                      S   N   C   R   In  Ne  A   Th  Im  H   Re  Ov  W   P   pO  sR  Hd  L   pM  Al  M   sO
phase                                   O   I   Ic  T   Co  Is  tC  Tr  Ts  Tf  Sc  pI  V   Ol  Y   Ha  St  sT  U   pN  CC  sL
 1 CoroutineElaboration               + + : : :   : :     : : : : : : : : : : : : : : : : : | : : V V : : | : | : : : : V
 2 CheckOverrideRefinement            + + V : : : : : : : : : : : : : : : : : : : : : : : : | : : | | : : | : | : : : : | : :
 3 LiftInstanceProcedures             + + + : : V : : V : : : : : : : : : : : : : : : : : : | : : | | : : | V | : : : : | : :
 4 TypeAliasElim                      + + | : : | : : | : : : : : : : : : : : : : : : : : : | : : | | : : | | | : V : : | : :
 5 MonomorphizeComposites             + + | : : | : V |   : : : : : : : : : : : : : : : : : | : : | | : : | | | : | : : | : :
 6 OpaqueUnusedTypeParams             + + | : : | : | | : : : : : : : : : : : : : : : : : : | : : | | : : | | | : | : : | : :
 7 EliminateDoWhile                   | | | : : | : | | : : : : : : : : : : : : : : : V : : | : : | | : : | | | : | : : | : :
 8 EliminateIncrDecrAndCompoundAssign | | | V V | : | | : : : : : : : : : : : : : : : |   : | : : | | : : | | | : | : : | : :
 9 CopyMutatedInputs                  | | | + + | : | | : : : : : : : : : : : : : : : | : : | : : | | : : | | | : | : V | : :
10 EliminateValueInReturns            | | | | | + V | | : : : : : : : : : : :   : : : | : : | : : | | : : | | | : | : | | : :
11 EliminateExceptions                + + | | | | + | | : : : : : V V : V : V : : : : | : : | : : | | : : | | | : | : | | : :
12 LowerComposite                     + + | | | + | + | V V V V : | | : | : | : : : : | : : | : : | | : : | | | : | : | | : :
13 ConstrainedTypeElim                + + | | | | + | | | | | | V | | : | : | : : : : | : : | : : | | : : | | | : | : | | : :
14 YieldElim                          + + | | | | | | + | | | | | | | : | : | : :   : | : : ' : V | | : : | | | : | : | | V V
15 HeapParameterization               + + | | | | + | | + + + + + + + V | : | :   : : | V V V   | | | :   | | | : | : | | | |
16 ModifiesClausesTransform           + + | | | | | | | | | | | | | | + | : | : :   : | | | |   | | | : : | | | : | : | | | |
17 GlobalParameterization             + + | | | + + | | | | | | | | | | + : | : V : : | | | | : | | | :   | | | : | : | | | |
18 PushOldInward                      | | | | | | | | | | | | | | | | | | : | : | : : | | | | V | | | : : | | | : | : | | | |
19 InferHoleTypes                     | | | | | | | | | | | | | | | | | | V | : | : : | | | | | | | | : : | | | : | : | | | |
20 EliminateDeterministicHoles        + + | | | | | | | | | | | | | | | | + | : | : : | | | | | | | | V : | | | : | : | | | |
21 UniqueOverloadNames                + + | | | | | | | | | | | | | | | | + | : | V : | | | | | | | | | : | | | : | : | | | |
22 DesugarShortCircuit                + + | | | | | | | | | | | | | | | | | | : | | V | | | | | | | | |   | | | : | : | | | |
23 EliminateReturnStatements          | | | | | | | | | | | | | | | | | | | + V | | | | | | | | | | | | : | | | : | : | | | |
24 LoopInvariantWellFormedness        | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | : | | | : | V | | | |
25 Contracts                          + + | | | | | | | | | | | | | | | | | | + + + | | | | | | | | | | : | | | : | | | | | |
26 Transparency                       ' + | | | | | | | | | | | | | | | | | | | | + | | | | | | | | | |   ' | ' : | | | | | |
27 PackageFunctionOutputsPass         : + | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | : : | : : | | | | | |
28 FunctionalRewritePass              : + | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | :   | V : | | | | | |
29 LiftImperativeExpressions          : + | + + | | | | | | | | | | | | | | | | | | + | | | | | | | | | V : | | : | | | | | |
30 InlineLocalVariables               : + | + | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | V | | : | | | | | |
31 Ordering                           : ' | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | V | | | | | |
32 LaurelToCoreSchema                 : : | + + + | + + | + + + | + + | | | | | | | | + + + + + + + + + + + + + + + + + + + + -/
#guard_msgs in
#eval IO.println Strata.Laurel.shapeLifelineTable

#guard (Strata.Laurel.shapeLabels.map (·.2)).Nodup
