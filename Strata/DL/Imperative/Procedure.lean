/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module


public import Strata.DL.Imperative.HasVars
public import Strata.DL.Imperative.BasicBlock
public import Strata.DL.Imperative.Stmt
public import Strata.Util.ListMap

/-! # Procedure

`Procedure P C Hdr` and its parts — `Body` (structured statements or a
control-flow graph), `Spec` (pre/postconditions), and the header — parameterized
over an expression bundle `P`, a command type `C`, and a header type `Hdr`.

`Hdr` is opaque here. The `ProcedureHeader` class gives a header's name and
input/output formal parameters, which is all the definitions in this file use;
a dialect fills in `Hdr` with its own header type and provides the instance. -/

namespace Imperative

public section

/-- A deterministic control-flow graph over commands `C` and expressions `P`:
labeled deterministic basic blocks with string labels. -/
@[expose] abbrev DetCFG (P : PureExpr) (C : Type) :=
  CFG String (DetBlock String C P)

/-- The body of a procedure: either structured (a list of statements) or
unstructured (a control-flow graph of basic blocks). An empty structured body
(`structured []`) represents an abstract/bodyless procedure. -/
inductive Body (P : PureExpr) (C : Type) where
  /-- A structured body: a sequential list of statements. -/
  | structured : List (Stmt P C) → Body P C
  /-- An unstructured body: a control-flow graph of deterministic basic blocks. -/
  | cfg        : DetCFG P C → Body P C

instance : Inhabited (Body P C) := ⟨.structured []⟩

instance [DecidableEq C] [DecidableEq P.Expr] [DecidableEq P.Ident] [DecidableEq P.Ty]
    [DecidableEq P.ExprMetadata] : DecidableEq (Body P C) := fun a b =>
  match a, b with
  | .structured x, .structured y => decidable_of_iff (x = y) (by simp)
  | .cfg x, .cfg y => decidable_of_iff (x = y) (by simp)
  | .structured _, .cfg _ => isFalse (by simp)
  | .cfg _, .structured _ => isFalse (by simp)

/-- Extract the structured statements, or error if the body is a CFG. -/
@[simp, expose]
def Body.getStructured : Body P C → Except String (List (Stmt P C))
  | .structured ss => .ok ss
  | .cfg _ => .error "expected structured body, got CFG"

/-- Extract the CFG, or error if the body is structured. -/
@[simp]
def Body.getCfg : Body P C → Except String (DetCFG P C)
  | .cfg c => .ok c
  | .structured _ => .error "expected CFG body, got structured"

/-- Variables read (referenced in expressions) by a CFG body. -/
@[simp]
def DetCFG.getVars [HasVarsImp P C] [HasFvars P] (cfg : DetCFG P C) : List P.Ident :=
  cfg.blocks.flatMap fun (_, blk) =>
    blk.cmds.flatMap HasVarsImp.readVars ++
    (match blk.transfer with
      | .condGoto p _ _ _ => HasFvars.getFvars p
      | .finish _ => [])

/-- Get variables referenced in the body. For a CFG body, this includes the
variables read by the guard of each conditional transfer (`condGoto`), mirroring
how the structured form collects the condition variables of `if`/`while`. -/
@[simp]
def Body.getVars [HasVarsImp P C] [HasFvars P] : Body P C → List P.Ident
  | .structured ss => ss.flatMap HasVarsImp.readVars
  | .cfg c => DetCFG.getVars c

/-- Is this body abstract (no implementation)? Only empty structured bodies
    are abstract. CFG bodies always have an implementation. -/
@[simp]
def Body.isAbstract : Body P C → Bool
  | .structured ss => ss.isEmpty
  | .cfg _ => false

/-- Does this body have a structured implementation? -/
@[simp]
def Body.isStructured (b : Body P C) : Bool := b.getStructured.isOk

/-- The statements of a body. A CFG block's commands come back `.cmd`-wrapped,
    which is what lets a property of statements — `noCalls`, say — see a CFG
    body too, while a property of a statement form that cannot occur in a
    block, such as a `loop`, holds there vacuously.

    A structured body's statements are in program order. A CFG body's blocks
    have no inherent order, so the result is a set of statements rather than an
    ordered sequence. -/
@[expose] def Body.statements : Body P C → List (Stmt P C)
  | .structured ss => ss
  | .cfg g => g.blocks.flatMap fun (_, blk) => blk.cmds.map .cmd

@[expose] def Body.allStatements (f : List (Stmt P C) → Bool) (body : Body P C) : Bool :=
  f body.statements

/-- Does this body have a CFG implementation? -/
@[simp]
def Body.isCfg (b : Body P C) : Bool := b.getCfg.isOk

def Body.structuredLength : Body P C → Nat
  | .structured ss => ss.length
  | .cfg _ => 0

/--
Attribute controlling whether a specification clause is checked or free.

- `Default`: The clause is checked (asserted at call sites for preconditions,
  checked on exit for postconditions).
- `Free`: The clause is assumed but not checked. A free precondition is assumed
  by the implementation but not asserted at call sites. A free postcondition is
  assumed upon return from calls but not checked on exit from implementations.

This is similar to Boogie IVL's assume/check axis (Section 8.1 of "This is Boogie 2").
-/
inductive CheckAttr where
  /-- The clause is free: assumed but not checked. -/
  | Free
  /-- The clause is checked (default behavior). -/
  | Default
  deriving Repr, DecidableEq

/-- A single specification clause: a boolean expression with an optional `Free`
attribute and optional metadata. -/
structure Check (P : PureExpr) where
  /-- The boolean expression of this specification clause. -/
  expr : P.Expr
  /-- Whether this clause is checked (`Default`) or free (`Free`). -/
  attr : CheckAttr := .Default
  /-- Optional metadata (e.g., source location). -/
  md   : Imperative.MetaData P := #[]

instance [Inhabited P.Expr] : Inhabited (Check P) where
  default := { expr := Inhabited.default }

instance [DecidableEq P.Expr] [DecidableEq P.Ident] : DecidableEq (Check P) := fun a b =>
  decidable_of_iff (a.expr = b.expr ∧ a.attr = b.attr ∧ a.md = b.md)
    (by cases a; cases b; simp)

/--
The specification (contract) of a procedure.

- `preconditions`: Labeled boolean expressions that must hold before the
  procedure executes. Checked (asserted) at call sites unless marked `Free`.
- `postconditions`: Labeled boolean expressions that must hold when the
  procedure returns. Assumed at call sites unless the implementation is being
  verified.
-/
structure Spec (P : PureExpr) where
  /-- Labeled preconditions (`requires` clauses). -/
  preconditions  : ListMap String (Check P)
  /-- Labeled postconditions (`ensures` clauses). -/
  postconditions : ListMap String (Check P)

instance : Inhabited (Spec P) :=
  ⟨{ preconditions := default, postconditions := default }⟩

instance [DecidableEq P.Expr] [DecidableEq P.Ident] : DecidableEq (Spec P) := fun a b =>
  decidable_of_iff (a.preconditions = b.preconditions ∧ a.postconditions = b.postconditions)
    (by cases a; cases b; simp)

/-- A procedure header's name and its input/output formal parameters. A dialect
    provides an instance for its header type; no other header data is available
    through this class. -/
class ProcedureHeader (P : PureExpr) (Hdr : Type) where
  name         : Hdr → P.Ident
  inputParams  : Hdr → List P.Ident
  outputParams : Hdr → List P.Ident

/-- A header, a specification, and a body. The header is used only through its
    `ProcedureHeader` instance. -/
structure Procedure (P : PureExpr) (C : Type) (Hdr : Type)
    [DecidableEq Hdr] [Inhabited Hdr] where
  header : Hdr
  spec   : Spec P
  body   : Body P C := .structured []

variable {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr]

instance : Inhabited (Procedure P C Hdr) :=
  ⟨{ header := default, spec := default }⟩

instance [DecidableEq C] [DecidableEq P.Expr] [DecidableEq P.Ident] [DecidableEq P.Ty]
    [DecidableEq P.ExprMetadata] : DecidableEq (Procedure P C Hdr) := fun a b =>
  decidable_of_iff (a.header = b.header ∧ a.spec = b.spec ∧ a.body = b.body)
    (by cases a; cases b; simp)

/-! ### Variable analysis for procedures, their bodies, and CFGs. -/

instance [HasFvars P] [HasVarsImp P C] : HasVarsImp P (DetCFG P C) where
  definedVars cfg excludeScoped := cfg.blocks.flatMap fun (_, blk) =>
    blk.cmds.flatMap (fun c => HasVarsImp.definedVars c excludeScoped)
  modifiedVars cfg := cfg.blocks.flatMap fun (_, blk) =>
    blk.cmds.flatMap HasVarsImp.modifiedVars
  readVars := DetCFG.getVars

instance [HasFvars P] [HasVarsImp P C] : HasVarsImp P (Body P C) where
  definedVars b excludeScoped := match b with
    | .structured ss => HasVarsImp.definedVars ss excludeScoped
    | .cfg cfgBody => HasVarsImp.definedVars cfgBody excludeScoped
  modifiedVars b := match b with
    | .structured ss => HasVarsImp.modifiedVars ss
    | .cfg cfgBody => HasVarsImp.modifiedVars cfgBody
  readVars := Body.getVars

/-- A procedure reads the free variables of its contract clauses and the read
    variables of its body, minus its own input formals. -/
def Procedure.getVars [HasFvars P] [HasVarsImp P C] [ProcedureHeader P Hdr]
    (p : Procedure P C Hdr) : List P.Ident :=
  (p.spec.postconditions.values.map Check.expr).flatMap HasFvars.getFvars ++
  (p.spec.preconditions.values.map Check.expr).flatMap HasFvars.getFvars ++
  Body.getVars p.body |> List.filter
    (fun x => (ProcedureHeader.inputParams p.header).all (fun f => !(P.EqIdent x f).decide))

instance [HasFvars P] [HasVarsImp P C] [ProcedureHeader P Hdr] :
    HasVarsImp P (Procedure P C Hdr) where
  definedVars _ _ := []
  modifiedVars p := ProcedureHeader.outputParams p.header
  readVars := Procedure.getVars

/-- Non-transitive modified-variable lookup: the procedure's own modified
    variables plus its body's, ignoring called procedures. -/
def Procedure.modifiedVarsTrans [HasFvars P] [HasVarsImp P C] [ProcedureHeader P Hdr]
    (_ : String → Option (Procedure P C Hdr)) (p : Procedure P C Hdr) : List P.Ident :=
  HasVarsImp.modifiedVars p ++ HasVarsImp.modifiedVars p.body

/-- Non-transitive read-variable lookup, the counterpart to
    `Procedure.modifiedVarsTrans`. -/
def Procedure.getVarsTrans [HasFvars P] [HasVarsImp P C] [ProcedureHeader P Hdr]
    (_ : String → Option (Procedure P C Hdr)) (p : Procedure P C Hdr) : List P.Ident :=
  HasVarsImp.readVars p ++ HasVarsImp.readVars p.body

instance [HasFvars P] [HasVarsImp P C] [ProcedureHeader P Hdr] :
    HasVarsProcTrans P (Procedure P C Hdr) where
  modifiedVarsTrans := Procedure.modifiedVarsTrans
  getVarsTrans := Procedure.getVarsTrans
  definedVarsTrans := λ _ _ ↦ []
  modifiedOrDefinedVarsTrans := Procedure.modifiedVarsTrans
  allVarsTrans := λ π p ↦ Procedure.getVarsTrans π p ++ Procedure.modifiedVarsTrans π p

end

end Imperative
