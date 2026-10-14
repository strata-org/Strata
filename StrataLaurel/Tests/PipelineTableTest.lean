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
N: Pseudo.needsOverrideRules   I: CompositeType.instanceProcedures.cons   R: StmtExpr.Return.value.some
In: StmtExpr.InstanceCall   T: CompositeType.typeArgs.cons   C: TypeDefinition.Constrained
Th: StmtExpr.Throw   Tr: StmtExpr.Try   Im: Pseudo.implicitHeap
Ts: Procedure.throwsType.some   H: StmtExpr.Hole.type.none   Tf: StmtExpr.Try.finally?.some
Re: StmtExpr.Return   S: Program.staticFields.cons   O: Pseudo.overload
L: Pseudo.laurelProgram   pI: Pseudo.imperativeShortCircuit   sI: StmtExpr.IncrDecr
Co: StmtExpr.CompoundAssign   W: StmtExpr.While.postTest.true   V: StmtExpr.Var.var.Field
P: StmtExpr.PureFieldUpdate   Is: StmtExpr.IsType   A: StmtExpr.AsType
Ne: StmtExpr.New   Ol: StmtExpr.Old.label?.some   pO: Pseudo.oldExpr
Y: StmtExpr.Yield   sR: StmtExpr.Resume   Ha: StmtExpr.HasNext
Hd: StmtExpr.Hole.deterministic.true   St: Pseudo.statementExpression   U: Pseudo.unorderedDeclarations
Le: Pseudo.letExpr   sT: StmtExpr.This

                                      N   R   T   Th  Im  H   Re  O   pI  Co  V   Is  Ne  pO  sR  Hd  U   sT
pass                                    I   In  C   Tr  Ts  Tf  S   L   sI  W   P   A   Ol  Y   Ha  St  Le
 1 CoroutineElaboration               :   :   : : : : : : : : : : : : : : : : : : : : : | : : V V : : | : :
 2 CheckOverrideRefinement            V : : : : : : : : : : : : : : : : : : : : : : : : | : : | | : : | : :
 3 LiftInstanceProcedures             + V : V : : : : : : : : : : : : : : : : : : : : : | : : | | : : | : V
 4 TypeAliasElim                      | | : | : : : : : : : : : : : : : : : : : : : : : | : : | | : : | : |
 5 MonomorphizeComposites             | | : | V : : : : : : : : : : : : : : : : : : : : | : : | | : : | : |
 6 EliminateDoWhile                   | | : | | : : : : : : : : : : : : : : V : : : : : | : : | | : : | : |
 7 EliminateIncrDecrAndCompoundAssign | | : | | : : : : : : : : : : : : V V |   : : : : | : : | | : : | : |
 8 ConstrainedTypeElim                | | : | | V : : : : : : : : : : : | | | : : : : : | : : | | : : | : |
 9 EliminateValueInReturns            | + V | | | : : : : : :   : : : : | | | : : : : : | : : | | : : | : |
10 EliminateExceptions                | | + | | | V V : V : V : : : : : | | | : : : : : | : : | | : : | : |
11 YieldElim                          | | | + | | | | : | : | : :   : : | | | : : : : : ' : V | | : : | : |
12 HeapParameterization               | | + | + + + + V | : | :   : : : | | | V V : V : V   | | | :   | : |
13 TypeHierarchyTransform             | | | | | | | | + | : | : : : : : | | | | | V | V | : | | | : : | : |
14 ModifiesClausesTransform           | | | | | | | | + | : | : :   : : | | | | | | | | |   | | | : : | : |
15 GlobalParameterization             | + + | | | | | | + : | : V : : : | | | | | | | | | : | | | :   | : |
16 UniqueOverloadNames                | | | | | | | | | | : | : | V : : | | | | | | | | | : | | | : : | : |
17 PushOldInward                      | | | | | | | | | | : | : | | : : | | | | | | | | | V | | | : : | : |
18 InferHoleTypes                     | | | | | | | | | | V | : | | : : | | | | | | | | | | | | | : : | : |
19 EliminateDeterministicHoles        | | | | | | | | | | + | : | | : : | | | | | | | | | | | | | V : | : |
20 DesugarShortCircuit                | | | | | | | | | | | | : | | : V | | | | | | | | | | | | | |   | : |
21 EliminateReturnStatements          | | | | | | | | | | | + V | | : | | | | | | | | | | | | | | | : | : |
22 LoopInvariantWellFormedness        | | | | | | | | | | | | | | | : | | | | | | | | | | | | | | | : | : |
23 Contracts                          | | | | | | | | | | | | + + + : | | | | | | | | | | | | | | | : | : |
24 Transparency                       | | | | | | | | | | | | | | + V | | | | | | | | | | | | | | | : ' : |
25 FunctionalRewritePass              | | | | | | | | | | | | | | | + | | | | | | | | | | | | | | | : : : |
26 LiftImperativeExpressions          | | | | | | | | | | | | | | | | + + + | | | | | | | | | | | | V : : |
27 InlineLocalVariables               | | | | | | | | | | | | | | | | | + | | | | | | | | | | | | | | : V |
28 Ordering                           | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | V | |
29 LaurelToCoreSchema                 | + | + + | + + | | | | | | | | | + + + + + + + + + + + + + + + + + + -/
#guard_msgs in
#eval IO.println Strata.Laurel.shapeLifelineTable

#guard (Strata.Laurel.shapeLabels.map (·.2)).Nodup
