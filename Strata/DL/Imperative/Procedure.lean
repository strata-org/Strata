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
abbrev DetCFG (P : PureExpr) (C : Type) :=
  CFG String (DetBlock String C P)

/-- The body of a procedure: structured (a list of statements), unstructured
(a control-flow graph of basic blocks), or absent (`abstract`: the procedure
has no implementation and is reasoned about only via its contract). An empty
structured body (`structured [] _`) is a real body that does nothing. A structured or CFG body
carries an *opaque* flag: callers of an opaque procedure know it only through its contract, while
its body is still verified against that contract and can still be executed. An abstract body is
opaque (`Body.isOpaque`). -/
inductive Body (P : PureExpr) (C : Type) where
  /-- A structured body: a sequential list of statements, and whether it is opaque. -/
  | structured : List (Stmt P C) → Bool → Body P C
  /-- An unstructured body: a control-flow graph of deterministic basic blocks, and whether it is
      opaque. -/
  | cfg        : DetCFG P C → Bool → Body P C
  /-- No body: the procedure is known only through its contract. -/
  | abstract   : Body P C

instance : Inhabited (Body P C) := ⟨.abstract⟩

instance [DecidableEq C] [DecidableEq P.Expr] [DecidableEq P.Ident] [DecidableEq P.Ty]
    [DecidableEq P.ExprMetadata] : DecidableEq (Body P C) := fun a b =>
  match a, b with
  | .structured x o, .structured y o' => decidable_of_iff (x = y ∧ o = o') (by simp)
  | .cfg x o, .cfg y o' => decidable_of_iff (x = y ∧ o = o') (by simp)
  | .abstract, .abstract => isTrue rfl
  | .structured _ _, .cfg _ _ | .structured _ _, .abstract | .cfg _ _, .structured _ _
  | .cfg _ _, .abstract | .abstract, .structured _ _ | .abstract, .cfg _ _ => isFalse (by simp)

/-- Extract the structured statements, or error if the body is a CFG or abstract. -/
@[simp, expose]
def Body.getStructured : Body P C → Except String (List (Stmt P C))
  | .structured ss _ => .ok ss
  | .cfg _ _ => .error "expected structured body, got CFG"
  | .abstract => .error "expected structured body, got an abstract procedure"

/-- Extract the CFG, or error if the body is structured or abstract. -/
@[simp]
def Body.getCfg : Body P C → Except String (DetCFG P C)
  | .cfg c _ => .ok c
  | .structured _ _ => .error "expected CFG body, got structured"
  | .abstract => .error "expected CFG body, got an abstract procedure"

/-- The statements of a structured body, the empty list for an abstract one, which has no
    statements, or an error for a CFG. -/
@[simp]
def Body.getStructuredOrEmpty : Body P C → Except String (List (Stmt P C))
  | .abstract => .ok []
  | b => b.getStructured

/-- Is this body abstract (no implementation)? -/
@[simp, expose]
def Body.isAbstract : Body P C → Bool
  | .abstract => true
  | _ => false

/-- Is this body opaque, so that callers know the procedure only through its contract? An abstract
    body is opaque, and a structured or CFG body is opaque when its flag says so. -/
@[simp, expose]
def Body.isOpaque : Body P C → Bool
  | .structured _ o => o
  | .cfg _ o => o
  | .abstract => true

/-- Is this body the implementation of an opaque procedure: a structured or CFG body whose flag
    marks it opaque? Such a body is checked on its own, since callers know the procedure only
    through its contract. -/
@[simp, expose]
def Body.isOpaqueWithBody : Body P C → Bool
  | .structured _ o => o
  | .cfg _ o => o
  | .abstract => false

/-- How an interpreter runs a call to an opaque callee (`Body.isOpaque`). `contract` runs it as
    its contract, as the reference semantics does (`EvalCmdExtE.call_abstract_sem`). `execute`
    runs the body of an opaque callee that has one, and the contract of an abstract callee
    (`Body.abstract`). -/
inductive CallMode where
  | contract
  | execute
  deriving DecidableEq, Repr, Inhabited

/-- Whether a call in mode `mode` to a callee with body `b` runs the callee's contract instead of
    its body: under `contract`, exactly when `b` is opaque; under `execute`, exactly when `b` is
    abstract. -/
@[simp, expose] def CallMode.runsContract : CallMode → Body P C → Bool
  | .contract, b => b.isOpaque
  | .execute, b => b.isAbstract

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
  | .structured ss _ => ss
  | .cfg g _ => g.blocks.flatMap fun (_, blk) => blk.cmds.map .cmd
  | .abstract => []

@[expose] def Body.allStatements (f : List (Stmt P C) → Bool) (body : Body P C) : Bool :=
  f body.statements

/-- Does this body have a CFG implementation? -/
@[simp]
def Body.isCfg (b : Body P C) : Bool := b.getCfg.isOk

def Body.structuredLength : Body P C → Nat
  | .structured ss _ => ss.length
  | .cfg _ _ | .abstract => 0

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
  body   : Body P C := .abstract

variable {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr]

instance : Inhabited (Procedure P C Hdr) :=
  ⟨{ header := default, spec := default }⟩

/-- How a dialect instantiates a procedure's type parameters at a call.  `instantiate p tys` is
    `p` with its type parameters replaced, positionally, by the call's type arguments `tys`: a
    monomorphic procedure the call can run.  It is `none` when `tys` does not instantiate `p`
    (for example, the wrong number of type arguments), and then the call has no step. -/
class ProcedureTypeInstantiation (P : PureExpr) (Hdr : Type) [DecidableEq Hdr] [Inhabited Hdr]
    where
  instantiate : Procedure P (CmdExt P) Hdr → List P.Ty → Option (Procedure P (CmdExt P) Hdr)

instance [DecidableEq C] [DecidableEq P.Expr] [DecidableEq P.Ident] [DecidableEq P.Ty]
    [DecidableEq P.ExprMetadata] : DecidableEq (Procedure P C Hdr) := fun a b =>
  decidable_of_iff (a.header = b.header ∧ a.spec = b.spec ∧ a.body = b.body)
    (by cases a; cases b; simp)

/-! ### Variable analysis for procedures, their bodies, and CFGs. -/

instance [HasFvars P] [HasVarsImp P C] : HasVarsImp P (DetCFG P C) where
  -- CFGs have a flat scope, so definitions always include every command-level
  -- declaration. Current transfer commands neither define nor modify variables.
  definedVars cfg _ := cfg.blocks.flatMap fun (_, blk) =>
    blk.cmds.flatMap (fun c => HasVarsImp.definedVars c false)
  modifiedVars cfg := cfg.blocks.flatMap fun (_, blk) =>
    blk.cmds.flatMap HasVarsImp.modifiedVars
  -- Conditional transfers read their guard; `finish` reads nothing.
  readVars cfg := cfg.blocks.flatMap fun (_, blk) =>
    blk.cmds.flatMap HasVarsImp.readVars ++
      match blk.transfer with
      | .condGoto guard _ _ _ => HasFvars.getFvars guard
      | .finish _ => []

/-- The declared types of every `init` command across all blocks of a CFG.  The
    CFG analog of `Block.initTypes`. -/
@[expose] def DetCFG.initTypes [HasInitTypesImp P C] (cfg : DetCFG P C) :
    List P.Ty :=
  cfg.blocks.flatMap fun (_, blk) => blk.cmds.flatMap (HasInitTypesImp.initTypes (P := P))

/-- Every init-type a CFG declares has a `valueOfTy` witness in the factory `f`;
    types absent from the CFG need no witness.  The CFG analog of
    `Block.InitTypesInhabited`. -/
@[expose] def DetCFG.InitTypesInhabited [HasVal P] [HasInitTypesImp P C]
    (f : P.Factory) (cfg : DetCFG P C) : Prop :=
  ∀ ty ∈ DetCFG.initTypes cfg, ∃ v, HasVal.valueOfTy f v ty

/-- Variables read by a body. CFG reads include command expressions and
conditional-transfer guards through the `HasVarsImp (DetCFG P C)` instance. -/
@[simp] def Body.readVars [HasFvars P] [HasVarsImp P C] :
    Body P C → List P.Ident
  | .structured ss _ => ss.flatMap HasVarsImp.readVars
  | .cfg cfgBody _ => HasVarsImp.readVars cfgBody
  | .abstract => []

instance [HasFvars P] [HasVarsImp P C] : HasVarsImp P (Body P C) where
  definedVars b excludeScoped := match b with
    | .structured ss _ => HasVarsImp.definedVars ss excludeScoped
    | .cfg cfgBody _ => HasVarsImp.definedVars cfgBody excludeScoped
    | .abstract => []
  modifiedVars b := match b with
    | .structured ss _ => HasVarsImp.modifiedVars ss
    | .cfg cfgBody _ => HasVarsImp.modifiedVars cfgBody
    | .abstract => []
  readVars := Body.readVars

/-- A procedure reads the free variables of its contract clauses and the read
    variables of its body, minus its own input formals. -/
def Procedure.getVars [HasFvars P] [HasVarsImp P C] [ProcedureHeader P Hdr]
    (p : Procedure P C Hdr) : List P.Ident :=
  (p.spec.postconditions.values.map Check.expr).flatMap HasFvars.getFvars ++
  (p.spec.preconditions.values.map Check.expr).flatMap HasFvars.getFvars ++
  Body.readVars p.body |> List.filter
    (fun x => (ProcedureHeader.inputParams p.header).all (fun f => !(P.EqIdent x f).decide))

instance [HasFvars P] [HasVarsImp P C] [ProcedureHeader P Hdr] :
    HasVarsImp P (Procedure P C Hdr) where
  definedVars _ _ := []
  modifiedVars p := ProcedureHeader.outputParams p.header
  readVars := Procedure.getVars

/-- An `assume` of each clause of `checks`, free or not. -/
@[expose] def Check.assumes {P : PureExpr} {C : Type} [HasPassiveCmds P C]
    (checks : ListMap String (Check P)) : List C :=
  checks.toList.map fun (label, check) => HasPassiveCmds.assume label check.expr check.md

/-- An `assert` of each clause of `checks`. A free clause is not checked: it becomes
    `assume true`, its label and expression kept in the metadata, with the message
    `FreePostCondition`. -/
@[expose] def Check.asserts {P : PureExpr} {C : Type} [HasBool P] [HasPassiveCmds P C]
    (checks : ListMap String (Check P)) : List C :=
  checks.toList.map fun (label, check) =>
    match check.attr with
    | .Free =>
      -- TODO: Perhaps introduce an "opaque" expression construct that hides the expression from
      -- the evaluator, allowing us to retain the postcondition body instead of replacing it
      -- with "true".
      HasPassiveCmds.assume label HasBool.tt
        ((MetaData.pushElem (MetaData.pushElem #[] (.label label) (.expr check.expr))
          (.label label) (.msg "FreePostCondition")))
    | .Default => HasPassiveCmds.assert label check.expr check.md

/-- The statement list that checks `body` against the contract of `p`: an `assume` of each
    precondition, then `body`, then an `assert` of each postcondition (`Check.asserts`). -/
@[expose] def Procedure.contractWrapped [HasBool P] [HasPassiveCmds P C] (p : Procedure P C Hdr)
    (body : List (Stmt P C)) : List (Stmt P C) :=
  (Check.assumes p.spec.preconditions).map Stmt.cmd ++ body ++
    (Check.asserts p.spec.postconditions).map Stmt.cmd

end

end Imperative
