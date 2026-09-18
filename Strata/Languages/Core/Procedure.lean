/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module


public import Strata.DL.Imperative.HasVars
public import Strata.DL.Imperative.BasicBlock
public import Strata.DL.Imperative.Procedure
public import Strata.Languages.Core.Statement

---------------------------------------------------------------------

namespace Core
public section

open Std (ToFormat Format format)
open Lambda
open Std.Format

-- Type class instances to enable deriving for structures containing Expression.Expr
instance : DecidableEq ExpressionMetadata :=
  show DecidableEq Unit from inferInstance

instance : Repr ExpressionMetadata :=
  show Repr Unit from inferInstance

instance : DecidableEq (⟨⟨ExpressionMetadata, CoreIdent⟩, LMonoTy⟩ : LExprParamsT).base.Metadata :=
  show DecidableEq ExpressionMetadata from inferInstance

instance : DecidableEq (⟨⟨ExpressionMetadata, CoreIdent⟩, LMonoTy⟩ : LExprParamsT).base.IDMeta :=
  show DecidableEq CoreIdent from inferInstance

instance : DecidableEq (⟨⟨ExpressionMetadata, CoreIdent⟩, LMonoTy⟩ : LExprParamsT).TypeType :=
  show DecidableEq LMonoTy from inferInstance

instance : Repr (⟨⟨ExpressionMetadata, CoreIdent⟩, LMonoTy⟩ : LExprParamsT).base.Metadata :=
  show Repr ExpressionMetadata from inferInstance

instance : Repr (⟨⟨ExpressionMetadata, CoreIdent⟩, LMonoTy⟩ : LExprParamsT).base.IDMeta :=
  show Repr CoreIdent from inferInstance

instance : Repr (⟨⟨ExpressionMetadata, CoreIdent⟩, LMonoTy⟩ : LExprParamsT).TypeType :=
  show Repr LMonoTy from inferInstance

instance : Repr Expression.Expr :=
  show Repr Expression.Expr from inferInstance

/-! # Strata Core Procedures

A *procedure* is the main verification unit in Strata Core. It is a named
signature with typed input and output parameters, a specification (contract),
and an optional implementation body.

## Syntax

`[]` is an optional keyword.
```
procedure Name<TypeArgs>([out/inout] x₁ : T₁, ..., [out/inout] xₙ : Tₙ)
spec {
  [free] requires [label] P;
  [free] ensures  [label] Q;
}
{ body };
```

## Parameters

Each procedure has three kinds of parameters:

- **Input parameters** (`name : T`) are passed by value from the caller to the callee.
  They are immutable within the procedure body.
- **Output parameters** (`out name : T`) are passed by value from the callee back to the
  caller. They are mutable within the procedure body and their final values are
  returned to the caller.
- **Input-output parameters** (`inout name : T`) appear in both input and output roles.
  The input value is the pre-state and the output value is the post-state. These
  are not only used to model mutable global variables but also pass mutable
  "references" to local variables.

## Specification

A procedure's specification (`Procedure.Spec`) consists of two parts:

- **Preconditions** (`requires`): Boolean expressions that must hold at the call site
  before the procedure is invoked. Their free variables must be a subset of the
  input parameters.

- **Postconditions** (`ensures`): Boolean expressions that must hold when the procedure
  returns. Their free variables may reference input parameters, output parameters,
  and `old(expr)` expressions.

### Free specifications

Both preconditions and postconditions may be marked `free`:

- A **free precondition** (`free requires`) is assumed by the implementation but
  *not* checked at call sites.
- A **free postcondition** (`free ensures`) is assumed upon return from calls but
  *not* checked on exit from implementations.

This follows the semantics described in Section 8.1 of "This is Boogie 2".

### Labels

Preconditions and postconditions may carry an optional label (e.g.,
`requires [myLabel]: P`). Labels are used to identify individual proof obligations
in verification output and diagnostics.

## The `old` expression

Postconditions and procedure bodies are *two-state contexts*: they can refer to
both the pre-state (on entry) and the post-state (on exit) of a procedure
invocation. The pre-state value of a variable `x` is denoted by `old x`.

- `old` applies to parameters that appear in both inputs and outputs (`inout`).
   For such a parameter `g`, `old g` refers to the input value.
- `old` is not allowed in preconditions.

See `OldExpressions.lean` for the normalization and substitution implementation.

## Procedure calls

A procedure is invoked via the `call` statement:

```
call ProcName([out/inout] e₁, ..., [out/inout] eₙ);
```

Note that `out` and `inout` keywords can only be attached when `e_i` is a variable.

The semantics of a call (see `CallElim` and `StatementSemantics`) are:

1. Evaluate the argument expressions `e₁, ..., eₙ`.
2. **Assert** each (non-free) precondition, substituting actuals for formals.
3. **Havoc** the output variables `y₁, ..., yₘ`.
4. **Assume** each postcondition, substituting actuals for formals and binding
   `old g` to the value of `g` immediately before the call.
5. Update the caller's state with the new values of the output variables.

This enables *modular verification*: each procedure is verified against its
contract independently, and callers reason only about the contract, not the body.

## Body

If a procedure has a body, it is verified as follows: the preconditions are
assumed, the body is symbolically executed, and the postconditions are asserted
at the end. It is a verification error if a postcondition does not hold at the
end of the body.

## Type parameters

Procedures may be polymorphic, parameterized by type variables (`typeArgs`).
These type variables can be used in the types of input/output parameters and
in the specification and body.

## Example

```
procedure Test(x : bool, out y : bool)
spec {
  ensures (y == x);
}
{
  y := x || x;
};
```

This declares a procedure `Test` with one input `x`, one output `y`, and a
postcondition that `y` equals `x`.
-/

/-- The header of a procedure: its name, type parameters, and input/output signatures. -/
structure Procedure.Header where
  /-- The procedure's name. -/
  name     : CoreIdent
  /-- Type parameters for polymorphic procedures. -/
  typeArgs : List TyIdentifier
  /-- Input parameters: passed by value from caller to callee (immutable in body). -/
  inputs   : @LMonoTySignature Unit
  /-- Output parameters: passed by value from callee to caller (mutable in body). -/
  outputs  : @LMonoTySignature Unit
  /-- If true, FilterProcedures will never remove this procedure. -/
  noFilter : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Parameters that appear in both `inputs` and `outputs` (in-out parameters).
    These are the parameters for which `old x` snapshots are meaningful. -/
@[expose] def getInoutParams (inputs outputs : @LMonoTySignature Unit) : @LMonoTySignature Unit :=
  inputs.filter fun (id, _) => (ListMap.keys outputs).contains id

/-- Parameters that appear in both `inputs` and `outputs` (in-out parameters). -/
@[expose] def Procedure.Header.getInoutParams (h : Procedure.Header) : @LMonoTySignature Unit :=
  Core.getInoutParams h.inputs h.outputs

/-- Output parameters that do NOT appear in `inputs` (output-only parameters). -/
@[expose] def Procedure.Header.getOutputOnlyParams (h : Procedure.Header) : @LMonoTySignature Unit :=
  h.outputs.filter fun (id, _) => !(ListMap.keys h.inputs).contains id

instance : ToFormat Procedure.Header where
  format p :=
    let typeArgs := if p.typeArgs.isEmpty then f!"" else f!"∀{Format.joinSep p.typeArgs " "}."
    f!"procedure {p.name} : {typeArgs} ({Signature.format p.inputs}) → \
      ({Signature.format p.outputs})"

/-- The check/free attribute of a specification clause. -/
abbrev Procedure.CheckAttr := Imperative.CheckAttr

@[match_pattern] abbrev Procedure.CheckAttr.Free := Imperative.CheckAttr.Free
@[match_pattern] abbrev Procedure.CheckAttr.Default := Imperative.CheckAttr.Default

/-- A single specification clause over Core expressions. -/
abbrev Procedure.Check := Imperative.Check Expression

def Procedure.Check.eraseTypes (c : Procedure.Check) : Procedure.Check :=
  { c with expr := c.expr.eraseTypes }

/-- A procedure's specification (contract) over Core expressions.
    Postconditions may reference `old v` for pre-state values. -/
abbrev Procedure.Spec := Imperative.Spec Expression

def Procedure.Spec.preconditionNames (s : Procedure.Spec) : List CoreLabel :=
  s.preconditions.keys

def Procedure.Spec.postconditionNames (s : Procedure.Spec) : List CoreLabel :=
  s.postconditions.keys

def Procedure.Spec.eraseTypes (s : Procedure.Spec) : Procedure.Spec :=
  { s with
    preconditions := s.preconditions.map (fun (l, c) => (l, Procedure.Check.eraseTypes c)),
    postconditions := s.postconditions.map (fun (l, c) => (l, Procedure.Check.eraseTypes c))
  }

def Procedure.Spec.getCheckExprs (conds : ListMap CoreLabel Procedure.Check) :
  List Expression.Expr :=
  let checks := conds.values
  checks.map (fun c => c.expr)

def Procedure.Spec.updateCheckExprs
  (es : List Expression.Expr) (conds : ListMap CoreLabel Procedure.Check) :
  ListMap CoreLabel Procedure.Check :=
  let checks := go es conds.values
  conds.keys.zip checks
  where go (es : List Expression.Expr) (checks : List Procedure.Check) :=
  match es, checks with
  | [], [] | [], _ | _, [] => checks
  | e :: erest, c :: crest =>
    { c with expr := e } :: go erest crest

/-- A deterministic control-flow graph over Core commands and expressions. -/
@[expose] abbrev DetCFG := Imperative.DetCFG Expression Command

/-- The body of a Core procedure. An empty structured body (`structured []`)
    represents an abstract/bodyless procedure. -/
abbrev Procedure.Body := Imperative.Body Expression Command

@[match_pattern] abbrev Procedure.Body.structured := @Imperative.Body.structured Expression Command
@[match_pattern] abbrev Procedure.Body.cfg := @Imperative.Body.cfg Expression Command

/-- A Strata Core procedure: the main verification unit. A procedure is a header
    (name, type parameters, input/output signatures), a specification (contract),
    and an optional body. An empty body makes the procedure abstract, reasoned
    about only via its contract. -/
abbrev Procedure := Imperative.Procedure Expression Command Procedure.Header

/-- Apply `f` to every expression of a procedure: the specification's
    pre/postcondition checks and the structured body. CFG bodies are left
    unchanged. -/
@[expose] def Procedure.mapExprs (f : Expression.Expr → Expression.Expr)
    (p : Procedure) : Procedure :=
  let mapCheck (c : Procedure.Check) : Procedure.Check := { c with expr := f c.expr }
  { p with
    spec := { p.spec with
      preconditions := p.spec.preconditions.map (fun (l, c) => (l, mapCheck c))
      postconditions := p.spec.postconditions.map (fun (l, c) => (l, mapCheck c)) }
    body := match p.body with
      | .structured ss => .structured (Statements.mapExprs f ss)
      | .cfg c => .cfg c }

---------------------------------------------------------------------

open Imperative

instance : Imperative.ProcedureHeader Expression Procedure.Header where
  name h         := h.name
  inputParams  h := h.inputs.keys
  outputParams h := h.outputs.keys

def DetCFG.eraseTypes (cfg : DetCFG) : DetCFG :=
  { cfg with blocks := cfg.blocks.map fun (lbl, blk) =>
      (lbl, { blk with cmds := blk.cmds.map Command.eraseTypes,
                        transfer := match blk.transfer with
                          | .condGoto p lt lf md => .condGoto p.eraseTypes lt lf md
                          | .finish md => .finish md }) }

-- Only transfer metadata is stripped because command metadata (on assert,
-- assume, init, set, cover) is not included in formatted output — formatCmd
-- discards it. Transfer metadata, however, appears in CFG formatting.
def DetCFG.stripMetaData (cfg : DetCFG) : DetCFG :=
  { cfg with blocks := cfg.blocks.map fun (lbl, blk) =>
      (lbl, { blk with transfer := match blk.transfer with
                          | .condGoto p lt lf _ => .condGoto p lt lf .empty
                          | .finish _ => .finish .empty }) }

def Procedure.eraseTypes (p : Procedure) : Procedure :=
  let body' := match p.body with
    | .structured ss => .structured (Statements.eraseTypes ss)
    | .cfg c => .cfg (DetCFG.eraseTypes c)
  { p with body := body', spec := p.spec }

def Procedure.stripMetaData (p : Procedure) : Procedure :=
  let body' := match p.body with
    | .structured ss => .structured (Imperative.Block.stripMetaData ss)
    | .cfg c => .cfg (DetCFG.stripMetaData c)
  { p with body := body' }

-- NOTE : simply discarding the procedure lookup function for now
instance : HasVarsTrans Expression Statement Procedure where
  modifiedVarsTrans := Statement.modifiedVarsTrans
  getVarsTrans := Statement.getVarsTrans
  definedVarsTrans := Statement.definedVarsTrans
  modifiedOrDefinedVarsTrans := Statement.modifiedOrDefinedVarsTrans
  allVarsTrans := Statement.allVarsTrans

instance : HasVarsTrans Expression (List Statement) Procedure where
  modifiedVarsTrans := Statements.modifiedVarsTrans
  getVarsTrans := Statements.getVarsTrans
  definedVarsTrans := Statements.definedVarsTrans
  modifiedOrDefinedVarsTrans := Statements.modifiedOrDefinedVarsTrans
  allVarsTrans := Statements.allVarsTrans

end
end Core
