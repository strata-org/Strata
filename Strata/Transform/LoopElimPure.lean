/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.LoopElim

/-! # Structural loop elimination

A pure, structural counterpart of the Core loop-elimination pass (`Core.removeLoop`, run by
`Core.loopElim`), over Imperative statements, whose correctness `LoopElimCorrect` and
`LoopElimCoreCorrect` prove.  It builds the passive encoding of the module note of
`Core.removeLoop` (`Stmt.loopPassive`), with the label prefixes (`Core.loopElimBlockPrefix`,
`Core.loopElimAssumePrefix`) of the Core pass, and eliminates every loop of a statement list
in one structural traversal (`Block.loopElim`), numbering loops from a `StringGenState`. -/

namespace Imperative

public section

variable {P : PureExpr} {C : Type}

/-- The loop-carried variables of a loop body: those it modifies and does not define.
    Variables the body defines are block-local to each iteration. -/
def Block.carriedVars [HasVarsImp P C] (bss : List (Stmt P C)) : List P.Ident :=
  let local_defs := Block.definedVars bss false
  (Block.modifiedVars bss).filter (fun v => v ∉ local_defs)

/-- The block of loop `loop_num` that havocs the variables `M`. -/
def LoopElim.havocBlock [HasHavoc P C] (loop_num : String) (M : List P.Ident)
    (md : MetaData P) : Stmt P C :=
  .block s!"{Core.loopElimBlockPrefix}havoc_{loop_num}"
    (M.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) {}

/-- The assumption of loop `loop_num` that its guard holds; none for a nondeterministic
    guard. -/
def LoopElim.enterAssume [HasPassiveCmds P C] (loop_num : String) (guard : ExprOrNondet P)
    (md : MetaData P) : List (Stmt P C) :=
  match guard with
  | .det g =>
    [Stmt.cmd (HasPassiveCmds.assume s!"{Core.loopElimAssumePrefix}guard_{loop_num}" g md)]
  | .nondet => []

/-- The assumption of loop `loop_num` that its guard fails; none for a nondeterministic
    guard. -/
def LoopElim.exitAssume [HasPassiveCmds P C] [HasBoolOps P] (loop_num : String)
    (guard : ExprOrNondet P) (md : MetaData P) : List (Stmt P C) :=
  match guard with
  | .det g =>
    [Stmt.cmd (HasPassiveCmds.assume s!"{Core.loopElimAssumePrefix}not_guard_{loop_num}"
      (HasBoolOps.not g) md)]
  | .nondet => []

/-- The passive encoding of `loop guard { body }`, numbered `loop_num`, with the loop-carried
    variables `M` and `body'` in place of the body, as built by `Core.removeLoop`:

    ```
    if (guard) {
      arbitrary_iter_facts: { havoc: { havoc(M) }; assume(guard); body' }
      havoc: { havoc(M) }
      assume(¬guard)
    }
    ```
    -/
def Stmt.loopPassive [HasHavoc P C] [HasPassiveCmds P C] [HasBoolOps P] (loop_num : String)
    (guard : ExprOrNondet P) (M : List P.Ident) (body' : List (Stmt P C)) (md : MetaData P) :
    Stmt P C :=
  let havocd := LoopElim.havocBlock loop_num M md
  let arbitrary_iter_facts :=
    Stmt.block s!"{Core.loopElimBlockPrefix}arbitrary_iter_facts_{loop_num}"
      ([havocd] ++ LoopElim.enterAssume loop_num guard md ++ body') {}
  .ite guard (arbitrary_iter_facts :: ([havocd] ++ LoopElim.exitAssume loop_num guard md)) [] {}

mutual
/-- Eliminate the loops of a statement, numbering them from `γ`: each loop without invariants
    and measure becomes its passive encoding (`Stmt.loopPassive`) over its loop-carried
    variables, with its body's loops eliminated.  Fails (`none`) on a loop with invariants or a
    measure. -/
def Stmt.loopElimM [HasVarsImp P C] [HasHavoc P C] [HasPassiveCmds P C] [HasBoolOps P] :
    Stmt P C → StringGenState → Option (Stmt P C × StringGenState)
  | .loop guard none [] body md, γ =>
    let (loop_num, γ) := StringGenState.gen "loop" γ
    match Block.loopElimM body γ with
    | some (body', γ) => some (Stmt.loopPassive loop_num guard (Block.carriedVars body) body' md, γ)
    | none => none
  | .loop _ _ _ _ _, _ => none
  | .block l bss md, γ =>
    match Block.loopElimM bss γ with
    | some (bss', γ) => some (.block l bss' md, γ)
    | none => none
  | .ite c tss ess md, γ =>
    match Block.loopElimM tss γ with
    | some (tss', γ) =>
      match Block.loopElimM ess γ with
      | some (ess', γ) => some (.ite c tss' ess' md, γ)
      | none => none
    | none => none
  | .cmd c, γ => some (.cmd c, γ)
  | .exit l md, γ => some (.exit l md, γ)
  | .typeDecl tc md, γ => some (.typeDecl tc md, γ)

/-- Eliminate the loops of a statement list (`Stmt.loopElimM` on each statement). -/
def Block.loopElimM [HasVarsImp P C] [HasHavoc P C] [HasPassiveCmds P C] [HasBoolOps P] :
    List (Stmt P C) → StringGenState → Option (List (Stmt P C) × StringGenState)
  | [], γ => some ([], γ)
  | s :: rest, γ =>
    match Stmt.loopElimM s γ with
    | some (s', γ) =>
      match Block.loopElimM rest γ with
      | some (rest', γ) => some (s' :: rest', γ)
      | none => none
    | none => none
end

/-- Eliminate every loop of a statement list (`Block.loopElimM`, numbering loops from
    `StringGenState.emp`). -/
def Block.loopElim [HasVarsImp P C] [HasHavoc P C] [HasPassiveCmds P C] [HasBoolOps P]
    (ss : List (Stmt P C)) : Option (List (Stmt P C)) :=
  (Block.loopElimM ss StringGenState.emp).map (·.1)

end -- public section

end Imperative
