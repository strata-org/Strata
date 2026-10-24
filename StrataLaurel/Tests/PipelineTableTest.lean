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
I: StmtExpr.InstanceCall   R: StmtExpr.Resume   U: Pseudo.unstableFieldReceiver
In: StmtExpr.IncrDecr   C: StmtExpr.CompoundAssign   Ic: CompositeType.instanceProcedures.cons
Rv: StmtExpr.Return.value.some   T: CompositeType.typeArgs.cons   Co: TypeDefinition.Composite
Ne: StmtExpr.New   Is: StmtExpr.IsType   A: StmtExpr.AsType
tC: TypeDefinition.Constrained   Th: StmtExpr.Throw   Tr: StmtExpr.Try
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

                                      S   N   R   In  Ic  T   Ne  A   Th  Im  H   G   Bd  Sc  pI  V   Ol  Y   Hd  L   pM  Al  M   sO
phase                                   O   I   U   C   Rv  Co  Is  tC  Tr  Ts  Tf  B   Re  Ov  W   P   pO  Ha  St  sT  Un  pN  CC  sL
 1 CoroutineElaboration               + + :   V : : :   : :   : : : : : : : : : : : : : : : : : : : : | : : V : : | : | : : : : V
 2 CheckOverrideRefinement            + + V : | : : : : : : : : : : : : : : : : : : : : : : : : : : : | : : | : : | : | : : : : | : :
 3 LiftInstanceProcedures             + + + V | : : : V : : : : : : : : : : : : : : : : : : : : : : : | : : | : : | V | : : : : | : :
 4 TypeAliasElim                      + + | | | : : : | : : : : : : : : : : : : : : : : : : : : : : : | : : | : : | | | : V : : | : :
 5 MonomorphizeComposites             + + | | | : : : | : V   : : : : : : : : : : : : : : : : : : : : | : : | : : | | | : | : : | : :
 6 OpaqueUnusedTypeParams             + + | | | : : : | : | : : : : : : : : : : : : : : : : : : : : : | : : | : : | | | : | : : | : :
 7 EliminateDoWhile                   | | | | | : : : | : | : : : : : : : : : : : : : : : : : : V : : | : : | : : | | | : | : : | : :
 8 BindFieldReceivers                 + + | + + V : : | : | : : : : : : : : : : : : : : : : :   | : : | : : | :   | | | : | : : | : :
 9 EliminateIncrDecrAndCompoundAssign | | | | | + V V | : | : : : : : : : : : : : : : : : : : : |   : | : : | : : | | | : | : : | : :
10 CopyMutatedInputs                  | | | | | | + + | : | : : : : : : : : : : : : : : : : : : | : : | : : | : : | | | : | : V | : :
11 EliminateValueInReturns            | | | | | | | | + V | : : : : : : : : : : : : : :   : : : | : : | : : | : : | | | : | : | | : :
12 EliminateExceptions                + + | | | | | | | + | : : : : : V V : V : V : : : : : : : | : : | : : | : : | | | : | : | | : :
13 LowerComposite                     + + | | | | | | + | + V V : :   | | : | : | : : : : : : : | : : | : : | : : | | | : | : | | : :
14 ConstrainedTypeElim                + + | | | + | | | + | | | V V V | | : | : | : : : : : : : | : : | : : | : : | | | : | : | | : :
15 YieldElim                          + + | + | | | | | | | | | | | | | | : | : | : : : : :   : | : : ' : V | : : | | | : | : | | V V
16 HeapParameterization               + + | | | + | | | + | + + + + + + + V | : | : : : :   : : | V V V   | | :   | | | : | : | | | |
17 ModifiesClausesTransform           + + | | | | | | | | | | | | | | | | + | : | : : : : :   : | | | |   | | : : | | | : | : | | | |
18 GlobalParameterization             + + | | | | | | + + | | | | | | | | | + : | : : : : V : : | | | | : | | :   | | | : | : | | | |
19 PushOldInward                      | | | | | | | | | | | | | | | | | | | | : | : : : : | : : | | | | V | | : : | | | : | : | | | |
20 InferHoleTypes                     | | | | | | | | | | | | | | | | | | | | V | : : : : | : : | | | | | | | : : | | | : | : | | | |
21 EliminateDeterministicHoles        + + | | | | | | | | | | | | | | | | | | + | : : : : | : : | | | | | | | V : | | | : | : | | | |
22 UniqueOverloadNames                + + | | | | | | | | | | | | | | | | | | + | : : : : | V : | | | | | | | | : | | | : | : | | | |
23 DesugarShortCircuit                + + | | | | | | | | | | | | | | | | | | | | : : : : | | V | | | | | | | |   | | | : | : | | | |
24 EliminateReturnStatements          | | | | | | | | | | | | | | | | | | | | | + : : : V | | | | | | | | | | | : | | | : | : | | | |
25 RestructureGotos                   | | | | | | | | | | | | | | | | | | | | | | V V V | | | | | | | | | | | | : | | | : | : | | | |
26 LoopInvariantWellFormedness        | | | | | | | | | | | | | | | | | | | | | | + + + | | | | | | | | | | | | : | | | : | V | | | |
27 Contracts                          + + | | | | | | | | | | | | | | | | | | | | | | | + + + | | | | | | | | | : | | | : | | | | | |
28 Transparency                       ' + | | | | | | | | | | | | | | | | | | | | | | | | | + | | | | | | | | |   ' | ' : | | | | | |
29 PackageFunctionOutputsPass         : + | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | : : | : : | | | | | |
30 FunctionalRewritePass              : + | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | :   | V : | | | | | |
31 LiftImperativeExpressions          : + | | | | + + | | | | | | | | | | | | | | | | | | | | + | | | | | | | | V : | | : | | | | | |
32 InlineLocalVariables               : + | | | | + | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | V | | : | | | | | |
33 Ordering                           : ' | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | V | | | | | |
34 LaurelToCoreSchema                 : : | + + | + + + | + | + + + | + + | | | | + + + | | | | + + + + + + + + + + + + + + + + + + +
-/
#guard_msgs in
#eval IO.println Strata.Laurel.shapeLifelineTable

#guard (Strata.Laurel.shapeLabels.map (·.2)).Nodup
