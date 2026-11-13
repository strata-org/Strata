/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Implementation.LaurelPipelinePrinter

/-! ## The rendered shape lifeline table

Pinning the table here captures the state of the pipeline: a change to what a
pass creates, removes or rejects shows up as a diff in the expected output. -/

/--
info: V starts holding here   | holds, and is carried on   + required here, holds, and is carried on
' was holding, and is dropped here   : not holding, but would be carried   (blank) not holding, and would not be carried
S: LaurelProgram.staticFunctions.cons   O: Program.Ordered   N: Pseudo.needsOverrideRules
C: StmtExpr.Call.receiver?.some   R: StmtExpr.Resume   U: Pseudo.unstableFieldReceiver
I: StmtExpr.IncrDecr   Co: StmtExpr.CompoundAssign   Ic: CompositeType.instanceProcedures.cons
Rv: StmtExpr.Return.value.some   T: CompositeType.typeArgs.cons   tC: TypeDefinition.Composite
Ne: StmtExpr.New   Is: StmtExpr.IsType   A: StmtExpr.AsType
tO: TypeDefinition.Constrained   Th: StmtExpr.Throw   Tr: StmtExpr.Try
Im: Pseudo.implicitHeap   Ts: Procedure.throwsType.some   H: StmtExpr.Hole.type.none
Tf: StmtExpr.Try.finally?.some   G: StmtExpr.Goto.destination.blockStart   B: StmtExpr.Block.invariants.cons
Bd: StmtExpr.Block.decreases.some   Re: StmtExpr.Return   Sc: LaurelProgram.staticFields.cons
Ov: Pseudo.overload   pI: Pseudo.imperativeShortCircuit   W: StmtExpr.While.postTest.true
V: StmtExpr.Var.var.Field   P: StmtExpr.PureFieldUpdate   Ol: StmtExpr.Old.label?.some
pO: Pseudo.oldExpr   Y: StmtExpr.Yield   Ha: StmtExpr.HasNext
Hd: StmtExpr.Hole.deterministic.true   St: Pseudo.statementExpression   L: Pseudo.letExpr
sT: StmtExpr.This   pM: Pseudo.imperativeFunction   Un: Program.Unordered
Al: TypeDefinition.Alias   pN: Pseudo.needsLoopInvariantChecks   M: Pseudo.mutatedInput
CC: Procedure.contracts.Coroutine   sO: StmtExpr.OldGuarantee   sL: StmtExpr.OldRelies

                                      S   N   R   I   Ic  T   Ne  A   Th  Im  H   G   Bd  Sc  pI  V   Ol  Y   Hd  L   pM  Al  M   sO
phase                                   O   C   U   Co  Rv  tC  Is  tO  Tr  Ts  Tf  B   Re  Ov  W   P   pO  Ha  St  sT  Un  pN  CC  sL
 1 EliminateStack                     | | : : : : : : : : : : : : : : : : : : : : : : : : : : : : : : | : : : : : | : | : : : : : : :
 2 CoroutineElaboration               + + :   V : : :   : :   : : : : : : : : : : : : : : : : : : : : | : : V : : | : | : : : : V
 3 CheckOverrideRefinement            + + V : | : : : : : : : : : : : : : : : : : : : : : : : : : : : | : : | : : | : | : : : : | : :
 4 LiftInstanceProcedures             + + + V | : : : V : : : : : : : : : : : : : : : : : : : : : : : | : : | : : | V | : : : : | : :
 5 InlinePreconditionOf               | + | | | : : : | : : : : : : : : : : : : : : : : : : : : : : : | : : | : : | | | : : : : | : :
 6 TypeAliasElim                      + + | | | : : : | : : : : : : : : : : : : : : : : : : : : : : : | : : | : : | | | : V : : | : :
 7 MonomorphizeComposites             + + | | | : : : | : V   : : : : : : : : : : : : : : : : : : : : | : : | : : | | | : | : : | : :
 8 OpaqueUnusedTypeParams             + + | | | : : : | : | : : : : : : : : : : : : : : : : : : : : : | : : | : : | | | : | : : | : :
 9 EliminateDoWhile                   | | | | | : : : | : | : : : : : : : : : : : : : : : : : : V : : | : : | : : | | | : | : : | : :
10 BindFieldReceivers                 + + | + + V : : | : | : : : : : : : : : : : : : : : : :   | : : | : : | :   | | | : | : : | : :
11 EliminateIncrDecrAndCompoundAssign | | | | | + V V | : | : : : : : : : : : : : : : : : : : : |   : | : : | : : | | | : | : : | : :
12 CopyMutatedInputs                  | | | | | | + + | : | : : : : : : : : : : : : : : : : : : | : : | : : | : : | | | : | : V | : :
13 EliminateValueInReturns            | | | | | | | | + V | : : : : : : : : : : : : : :   : : : | : : | : : | : : | | | : | : | | : :
14 EliminateExceptions                + + | | | | | | | + | : : : : : V V : V : V : : : : : : : | : : | : : | : : | | | : | : | | : :
15 LowerComposite                     + + | | | | | | + | + V V : :   | | : | : | : : : : : : : | : : | : : | : : | | | : | : | | : :
16 ConstrainedTypeElim                + + | | | + | | | + | | | V V V | | : | : | : : : : : : : | : : | : : | : : | | | : | : | | : :
17 YieldElim                          + + | + | | | | | | | | | | | | | | : | : | : : : : :   : | : : ' : V | : : | | | : | : | | V V
18 HeapParameterization               + + | | | + | | | + | + + + + + + + V | : | : : : :   : : | V V V   | | :   | | | : | : | | | |
19 ModifiesClausesTransform           + + | | | | | | | | | | | | | | | | + | : | : : : : :   : | | | |   | | : : | | | : | : | | | |
20 GlobalParameterization             + + | | | | | | + + | | | | | | | | | + : | : : : : V : : | | | | : | | :   | | | : | : | | | |
21 PushOldInward                      | | | | | | | | | | | | | | | | | | | | : | : : : : | : : | | | | V | | : : | | | : | : | | | |
22 InferHoleTypes                     | | | | | | | | | | | | | | | | | | | | V | : : : : | : : | | | | | | | : : | | | : | : | | | |
23 EliminateDeterministicHoles        + + | | | | | | | | | | | | | | | | | | + | : : : : | : : | | | | | | | V : | | | : | : | | | |
24 UniqueOverloadNames                + + | | | | | | | | | | | | | | | | | | + | : : : : | V : | | | | | | | | : | | | : | : | | | |
25 DesugarShortCircuit                + + | | | | | | | | | | | | | | | | | | | | : : : : | | V | | | | | | | |   | | | : | : | | | |
26 EliminateReturnStatements          | | | | | | | | | | | | | | | | | | | | | + : : : V | | | | | | | | | | | : | | | : | : | | | |
27 RestructureGotos                   | | | | | | | | | | | | | | | | | | | | | | V V V | | | | | | | | | | | | : | | | : | : | | | |
28 LoopInvariantWellFormedness        | | | | | | | | | | | | | | | | | | | | | | + + + | | | | | | | | | | | | : | | | : | V | | | |
29 Contracts                          + + | | | | | | | | | | | | | | | | | | | | | | | + + + | | | | | | | | | : | | | : | | | | | |
30 Transparency                       ' + | | | | | | | | | | | | | | | | | | | | | | | | | + | | | | | | | | |   ' | ' : | | | | | |
31 PackageFunctionOutputsPass         : + | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | : : | : : | | | | | |
32 FunctionalRewritePass              : + | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | :   | V : | | | | | |
33 LiftImperativeExpressions          : + | | | | + + | | | | | | | | | | | | | | | | | | | | + | | | | | | | | V : | | : | | | | | |
34 InlineLocalVariables               : + | | | | + | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | V | | : | | | | | |
35 Ordering                           : ' | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | V | | | | | |
36 LaurelToCoreSchema                 : : | + + | + + + | + | + + + | + + | | | | + + + | | | | + + + + + + + + + + + + + + + + + + +
-/
#guard_msgs in
#eval IO.println Strata.Laurel.shapeLifelineTable

#guard (Strata.Laurel.shapeLabels.map (·.2)).Nodup
