/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.LaurelAST
public import StrataLaurel.Implementation.MapStmtExpr
import Strata.Util.Tactics

/-!
# Labelled jumps

A `Goto L d` either leaves or restarts an *enclosing* block labelled `L`, or
jumps to a labelled block elsewhere in the same procedure body. The second kind,
a *non-enclosing* jump, is what a front end translating a control-flow graph
emits: one labelled block per jump target and one `if c then { goto T }` per
branch. `RestructureGotos` nests the blocks so that every jump becomes an
enclosing one.

A non-enclosing jump is only meaningful between *statement positions*: the
statements reachable from the procedure body through blocks and `if` arms. A
`while` body and each arm of a `try` are regions of their own: a jump may leave
one, but may not enter one. Nor may a jump land in the scope of a local past its
declaration. `validateJumps` checks these rules and that the target label names
one block. A coroutine body may not jump between
blocks at all: its suspension points split it into states. It also checks the placement of a
stack annotation (`stackAnnotation?`), which is only meaningful on a label.

These helpers are shared by resolution, the interpreter and the passes that see
non-enclosing jumps.
-/

namespace Strata.Laurel

public section

/-- The reserved callee of a stack annotation `$stackShape<T₁, …, Tₙ>()`. -/
def stackShapeName : String := "$stackShape"

/-- The types a stack annotation lists, bottom of the stack first, when `s` is
    one. A stack annotation is the first statement of a labelled block and states
    the types of the operand stack values live at the block's start. -/
def stackAnnotation? (s : StmtExprMd) : Option (List HighTypeMd) :=
  match s.val with
  | .Call none callee [] typeArgs => if callee.text == stackShapeName then some typeArgs else none
  | _ => none

/-- The labels of every labelled block in `e`, with repetitions. -/
def blockLabels (e : StmtExprMd) : List String :=
  collectStmtExprList (fun n => match n.val with
    | .Block _ (some l) _ _ => [l]
    | _ => []) e

/-- How many labelled blocks of `e` carry each label. -/
def labelCounts (e : StmtExprMd) : Std.HashMap String Nat :=
  (blockLabels e).foldl (fun m l => m.insert l (m.getD l 0 + 1)) {}

/-- The labels a statement-position jump can reach inside `s`: those of `s` and
    of the blocks nested in it through blocks and `if` arms. -/
@[expose] def statementLabels (s : StmtExprMd) : List String :=
  match _h : s.val with
  | .Block stmts label _ _ => label.toList ++ (stmts.attach.map fun ⟨t, _⟩ => statementLabels t).flatten
  | .IfThenElse _ th el => statementLabels th ++ (el.attach.map fun ⟨e, _⟩ => statementLabels e).getD []
  | _ => []
termination_by sizeOf s
decreasing_by
  all_goals simp_wf
  all_goals (try have := AstNode.sizeOf_val_lt s)
  all_goals (try term_by_mem)
  all_goals (cases s; simp_all; omega)

/-- The statement-position labels of a block: its own and those of its statements. -/
theorem statementLabels_block (stmts : List StmtExprMd) (label : Option String) (invs : List StmtExprMd)
    (dec : Option StmtExprMd) (src : Strata.FileRange) :
    statementLabels ⟨.Block stmts label invs dec, src⟩ = label.toList ++ (stmts.map statementLabels).flatten := by
  rw [statementLabels]
  simp

/-- The statement-position labels of an `if`: those of its two arms. -/
theorem statementLabels_ite (c th : StmtExprMd) (el : Option StmtExprMd) (src : Strata.FileRange) :
    statementLabels ⟨.IfThenElse c th el, src⟩ = statementLabels th ++ (el.map statementLabels).getD [] := by
  rw [statementLabels]
  cases el <;> simp

/-- A node that is neither a block nor an `if` has no statement-position labels. -/
theorem statementLabels_other (v : StmtExpr) (src : Strata.FileRange) (hb : ∀ a b c d, v ≠ .Block a b c d)
    (hi : ∀ c t e, v ≠ .IfThenElse c t e) : statementLabels ⟨v, src⟩ = [] := by
  rw [statementLabels]
  split <;> first | rfl | (rename_i h; exact absurd h.symm (by simp_all))

/-- The jumps in `e` whose target is not an enclosing labelled block. -/
partial def nonEnclosingJumps (e : StmtExprMd) : List StmtExprMd :=
  ((go [] e).run #[]).2.toList
where
  go (enclosing : List String) (e : StmtExprMd) : StateM (Array StmtExprMd) Unit := do
    let _ ← mapStmtExprPrePostM (fun n => match n.val with
      | .Block stmts (some l) invs dec => do
          for x in invs ++ dec.toList do go enclosing x
          for s in stmts do go (l :: enclosing) s
          pure (some n)
      | .Goto l _ => do
          unless enclosing.contains l do modify (·.push n)
          pure (some n)
      | _ => pure none) pure e

/-- Whether `e` contains a jump to a block that does not enclose it. -/
def hasNonEnclosingJump (e : StmtExprMd) : Bool := !(nonEnclosingJumps e).isEmpty

/-- The targets of the non-enclosing jumps in `e`. -/
def nonEnclosingTargets (e : StmtExprMd) : Std.HashSet String :=
  (nonEnclosingJumps e).foldl (fun s j => match j.val with
    | .Goto l _ => s.insert l
    | _ => s) {}

private inductive Region where
  | body
  | loop (id : Nat)
  | tryArm (id : Nat)
  deriving BEq, Inhabited

private structure Site where
  node : StmtExprMd
  statement : Bool
  regions : List Region
  enclosing : List String
  visible : List (Nat × String)

private structure JumpScan where
  next : Nat := 0
  blocks : Std.HashMap String (Array Site) := {}
  jumps : Array Site := #[]
  order : Nat := 0
  misplacedAnnotations : Array StmtExprMd := #[]
  annotatedBlocks : Array (String × StmtExprMd) := #[]

private abbrev ScanM := StateM JumpScan

/-- The labels some `exit` in `e` leaves: the blocks whose end a jump reaches. -/
def exitedLabels (e : StmtExprMd) : Std.HashSet String :=
  collectStmtExprList (fun n => match n.val with
    | .Goto l .blockEnd => [l]
    | _ => []) e |>.foldl (·.insert ·) {}

/-- Whether control cannot run off the end of `s`: every path ends in a jump,
    `return` or `throw`. A labelled block falls through when its last statement does
    or when an `exit` reaches its end, which `exited` tells. -/
partial def endsAbruptlyIn (exited : Std.HashSet String) (s : StmtExprMd) : Bool :=
  match s.val with
  | .Return _ | .Throw _ | .Goto .. => true
  | .Block stmts label _ _ =>
    !(label.any exited.contains) && ((stmts.getLast?.map (endsAbruptlyIn exited)).getD false)
  | .IfThenElse _ th (some el) => endsAbruptlyIn exited th && endsAbruptlyIn exited el
  | .Try body catches fin =>
    (endsAbruptlyIn exited body && catches.all (endsAbruptlyIn exited ·.body))
      || (fin.map (endsAbruptlyIn exited)).getD false
  | _ => false

/-- Run `f` on each direct child of `e`. -/
def forChildren [Monad m] (f : StmtExprMd → m Unit) (e : StmtExprMd) : m Unit := do
  let _ ← (mapStmtExprPrePostM (m := StateT Bool m) (fun n => do
      if ← get then do
        f n
        pure (some n)
      else do
        set true
        pure none) pure e).run false

private def freshRegion : ScanM Nat := modifyGet fun s => (s.next, { s with next := s.next + 1 })

private def tick : ScanM Nat := modifyGet fun s => (s.order, { s with order := s.order + 1 })

/-- The locals a statement declares: each `Declare` target of an assignment, or a
    bare declaration. -/
def statementDecls (s : StmtExprMd) : List String :=
  match s.val with
  | .Assign targets _ => targets.filterMap fun t => match t.val with
    | .Declare p => some p.name.text
    | _ => none
  | .Var (.Declare p) => [p.name.text]
  | _ => []

private partial def scan (statement : Bool) (regions : List Region) (enclosing : List String)
    (visible : List (Nat × String)) (e : StmtExprMd) : ScanM Unit := do
  let site : Site := { node := e, statement, regions, enclosing, visible }
  let expr (x : StmtExprMd) : ScanM Unit := scan false regions enclosing visible x
  match e.val with
  | .Block stmts label invs dec =>
    if let some l := label then
      modify fun s => { s with blocks := s.blocks.alter l (some <| ·.getD #[] |>.push site) }
    for x in invs ++ dec.toList do expr x
    let inner := label.toList ++ enclosing
    let mut inScope := visible
    for (s, k) in stmts.zipIdx do
      if (stackAnnotation? s).isSome then
        match label with
        | some l =>
          if k == 0 && statement then
            modify fun st => { st with annotatedBlocks := st.annotatedBlocks.push (l, s) }
          else modify fun st => { st with misplacedAnnotations := st.misplacedAnnotations.push s }
        | none => modify fun st => { st with misplacedAnnotations := st.misplacedAnnotations.push s }
      scan statement regions inner inScope s
      for name in statementDecls s do
        inScope := (← tick, name) :: inScope
  | .IfThenElse c th el =>
    expr c
    scan statement regions enclosing visible th
    if let some x := el then scan statement regions enclosing visible x
  | .While c invs dec body _ =>
    expr c
    for x in invs ++ dec.toList do expr x
    let r ← freshRegion
    scan statement (if statement then .loop r :: regions else regions) enclosing visible body
  | .Try body catches fin =>
    let arm (x : StmtExprMd) : ScanM Unit := do
      let r ← freshRegion
      scan statement (if statement then .tryArm r :: regions else regions) enclosing visible x
    arm body
    for c in catches do arm c.body
    if let some f := fin then arm f
  | .Goto l _ =>
    unless enclosing.contains l do modify fun s => { s with jumps := s.jumps.push site }
  | _ => forChildren expr e

private def isSuffix (short long : List Region) : Bool :=
  short.length ≤ long.length && long.drop (long.length - short.length) == short

/-- Check the non-enclosing jumps of a procedure body (see the module docstring).
    A jump to a label that names no block is left to `Check.goto`, which reports
    it on every resolution. -/
def validateJumps (body : StmtExprMd) (coroutine : Bool := false) : List Message := Id.run do
  let ((), st) := (scan true [.body] [] [] body).run {}
  let targeted : Std.HashSet String := st.jumps.foldl (init := {}) fun acc j => match j.node.val with
    | .Goto l _ => acc.insert l
    | _ => acc
  let mut errors : Array Message := st.misplacedAnnotations.map fun a =>
    diagnosticFromSource a.source "a stack annotation must be the first statement of a labelled block"
  for (l, a) in st.annotatedBlocks do
    unless targeted.contains l do
      errors := errors.push (diagnosticFromSource a.source
        s!"a stack annotation states the stack a jump carries to its block, and no jump from outside '{l}' targets it")
  if coroutine then
    return errors.toList ++ st.jumps.toList.filterMap fun j => match j.node.val with
      | .Goto l _ => if (st.blocks.getD l #[]).isEmpty then none else
        some (diagnosticFromSource j.node.source
          s!"a jump to '{l}', a block that does not enclose it, is not supported in a coroutine")
      | _ => none
  for j in st.jumps do
    let .Goto l _ := j.node.val | continue
    match (st.blocks.getD l #[]).toList with
    | [] => continue
    | [target] =>
      if !j.statement then
        errors := errors.push (diagnosticFromSource j.node.source
          s!"a jump inside an expression can only leave an enclosing block, and '{l}' does not enclose it")
      else if !target.statement then
        errors := errors.push (diagnosticFromSource j.node.source
          s!"block '{l}' is inside an expression, so a jump cannot reach it")
      else if !isSuffix target.regions j.regions then
        let shared := ((target.regions.reverse.zip j.regions.reverse).takeWhile fun (a, b) => a == b).length
        let entered := (target.regions.take (target.regions.length - shared)).getLast?
        let what := match entered with
          | some (.tryArm _) => "a try block, catch handler or finally block"
          | _ => "a loop body"
        errors := errors.push (diagnosticFromSource j.node.source
          s!"a jump to '{l}' would enter {what} from outside it")
      else if let some (_, name) := target.visible.find? (fun d => !j.visible.contains d) then
        errors := errors.push (diagnosticFromSource j.node.source
          s!"a jump to '{l}' would enter the scope of '{name}' past its declaration")
    | _ =>
      errors := errors.push (diagnosticFromSource j.node.source
        s!"label '{l}' names more than one block, so a jump from outside it is ambiguous")
  return errors.toList

end -- public section

end Strata.Laurel
