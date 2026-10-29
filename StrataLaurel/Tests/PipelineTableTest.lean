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
I: CompositeType.instanceProcedures.cons   R: StmtExpr.Return.value.some   In: StmtExpr.InstanceCall
T: CompositeType.typeArgs.cons   C: TypeDefinition.Constrained   Th: StmtExpr.Throw
Tr: StmtExpr.Try   Im: Pseudo.implicitHeap   Ts: Procedure.throwsType.some
H: StmtExpr.Hole.type.none   Tf: StmtExpr.Try.finally?.some   Re: StmtExpr.Return
Sc: LaurelProgram.staticFields.cons   Ov: Pseudo.overload   pI: Pseudo.imperativeShortCircuit
sI: StmtExpr.IncrDecr   Co: StmtExpr.CompoundAssign   W: StmtExpr.While.postTest.true
V: StmtExpr.Var.var.Field   P: StmtExpr.PureFieldUpdate   Is: StmtExpr.IsType
A: StmtExpr.AsType   Ne: StmtExpr.New   Ol: StmtExpr.Old.label?.some
pO: Pseudo.oldExpr   Y: StmtExpr.Yield   sR: StmtExpr.Resume
Ha: StmtExpr.HasNext   Hd: StmtExpr.Hole.deterministic.true   St: Pseudo.statementExpression
L: Pseudo.letExpr   sT: StmtExpr.This   pM: Pseudo.imperativeFunction
U: Program.Unordered   Al: TypeDefinition.Alias   pN: Pseudo.needsLoopInvariantChecks
CC: Procedure.contracts.Coroutine   sO: StmtExpr.OldGuarantee   sL: StmtExpr.OldRelies

                                      S   N   R   T   Th  Im  H   Re  Ov  sI  W   P   A   Ol  Y   Ha  St  sT  U   pN  sO
phase                                   O   I   In  C   Tr  Ts  Tf  Sc  pI  Co  V   Is  Ne  pO  sR  Hd  L   pM  Al  CC  sL
 1 CoroutineElaboration               + + :   :   : : : : : : : : : : : : : : : : : : : : | : : V V : : | : | : : : V
 2 CheckOverrideRefinement            + + V : : : : : : : : : : : : : : : : : : : : : : : | : : | | : : | : | : : : | : :
 3 LiftInstanceProcedures             + + + V : V : : : : : : : : : : : : : : : : : : : : | : : | | : : | V | : : : | : :
 4 TypeAliasElim                      + + | | : | : : : : : : : : : : : : : : : : : : : : | : : | | : : | | | : V : | : :
 5 MonomorphizeComposites             + + | | : | V : : : : : : : : : : : : : : : : : : : | : : | | : : | | | : | : | : :
 6 EliminateDoWhile                   | | | | : | | : : : : : : : : : : : : : V : : : : : | : : | | : : | | | : | : | : :
 7 EliminateIncrDecrAndCompoundAssign | | | | : | | : : : : : : : : : : : V V |   : : : : | : : | | : : | | | : | : | : :
 8 ConstrainedTypeElim                + + | | : | | V : : : : : : : : : : | | | : : : : : | : : | | : : | | | : | : | : :
 9 EliminateValueInReturns            | | | + V | | | : : : : : :   : : : | | | : : : : : | : : | | : : | | | : | : | : :
10 EliminateExceptions                + + | | + | | | V V : V : V : : : : | | | : : : : : | : : | | : : | | | : | : | : :
11 YieldElim                          + + | | | + | | | | : | : | : :   : | | | : : : : : ' : V | | : : | | | : | : | V V
12 HeapParameterization               + + | | + | + + + + V | : | :   : : | | | V V : V : V   | | | :   | | | : | : | | |
13 TypeHierarchyTransform             + + | | | | | | | | + | : | : : : : | | | | | V | V | : | | | : : | | | : | : | | |
14 ModifiesClausesTransform           + + | | | | | | | | + | : | : :   : | | | | | | | | |   | | | : : | | | : | : | | |
15 GlobalParameterization             + + | + + | | | | | | + : | : V : : | | | | | | | | | : | | | :   | | | : | : | | |
16 PushOldInward                      | | | | | | | | | | | | : | : | : : | | | | | | | | | V | | | : : | | | : | : | | |
17 InferHoleTypes                     | | | | | | | | | | | | V | : | : : | | | | | | | | | | | | | : : | | | : | : | | |
18 EliminateDeterministicHoles        + + | | | | | | | | | | + | : | : : | | | | | | | | | | | | | V : | | | : | : | | |
19 UniqueOverloadNames                + + | | | | | | | | | | + | : | V : | | | | | | | | | | | | | | : | | | : | : | | |
20 DesugarShortCircuit                + + | | | | | | | | | | | | : | | V | | | | | | | | | | | | | |   | | | : | : | | |
21 EliminateReturnStatements          | | | | | | | | | | | | | + V | | | | | | | | | | | | | | | | | : | | | : | : | | |
22 LoopInvariantWellFormedness        | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | : | | | : | V | | |
23 Contracts                          + + | | | | | | | | | | | | + + + | | | | | | | | | | | | | | | : | | | : | | | | |
24 Transparency                       ' + | | | | | | | | | | | | | | + | | | | | | | | | | | | | | |   ' | ' : | | | | |
25 FunctionalRewritePass              : + | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | :   | V : | | | | |
26 LiftImperativeExpressions          : + | | | | | | | | | | | | | | | + + + | | | | | | | | | | | | V : | | : | | | | |
27 InlineLocalVariables               : + | | | | | | | | | | | | | | | | + | | | | | | | | | | | | | | V | | : | | | | |
28 Ordering                           : ' | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | V | | | | |
29 LaurelToCoreSchema                 : : | + | + + | + + | | | | | | | | + + + + + + + + + + + + + + + + + + + + + + + + -/
#guard_msgs in
#eval IO.println Strata.Laurel.shapeLifelineTable

#guard (Strata.Laurel.shapeLabels.map (·.2)).Nodup
