/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module


public import Strata.DL.Imperative.HasVars
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
  /-- If true, PrecondElim will skip this procedure's body and contract. -/
  noPrecondElim : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Parameters that appear in both `inputs` and `outputs` (in-out parameters).
    These are the parameters for which `old x` snapshots are meaningful. -/
@[expose] def Procedure.Header.getInoutParams (h : Procedure.Header) : @LMonoTySignature Unit :=
  h.inputs.filter fun (id, _) => (ListMap.keys h.outputs).contains id

/-- Output parameters that do NOT appear in `inputs` (output-only parameters). -/
@[expose] def Procedure.Header.getOutputOnlyParams (h : Procedure.Header) : @LMonoTySignature Unit :=
  h.outputs.filter fun (id, _) => !(ListMap.keys h.inputs).contains id

instance : ToFormat Procedure.Header where
  format p :=
    let typeArgs := if p.typeArgs.isEmpty then f!"" else f!"∀{Format.joinSep p.typeArgs " "}."
    f!"procedure {p.name} : {typeArgs} ({Signature.format p.inputs}) → \
      ({Signature.format p.outputs})"

/--
Attribute controlling whether a specification clause is checked or free.

- `Default`: The clause is checked (asserted at call sites for preconditions,
  checked on exit for postconditions).
- `Free`: The clause is assumed but not checked. A free precondition is assumed
  by the implementation but not asserted at call sites. A free postcondition is
  assumed upon return from calls but not checked on exit from implementations.

See Section 8.1 of "This is Boogie 2" for motivation.
-/
inductive Procedure.CheckAttr where
  /-- The clause is free: assumed but not checked. -/
  | Free
  /-- The clause is checked (default behavior). -/
  | Default
  deriving Repr, DecidableEq

/-- A single specification clause: a boolean expression with an optional `Free` attribute
and optional metadata. -/
structure Procedure.Check where
  /-- The boolean expression of this specification clause. -/
  expr : Expression.Expr
  /-- Whether this clause is checked (`Default`) or free (`Free`). -/
  attr : CheckAttr := .Default
  /-- Optional metadata (e.g., source location). -/
  md : Imperative.MetaData Expression := #[]
  deriving Repr, DecidableEq

instance : Inhabited Procedure.Check where
  default := { expr := Inhabited.default }

def Procedure.Check.eraseTypes (c : Procedure.Check) : Procedure.Check :=
  { c with expr := c.expr.eraseTypes }

/--
The specification (contract) of a procedure.

- `preconditions`: Labeled boolean expressions that must hold before the procedure
  executes. Checked (asserted) at call sites unless marked `Free`.
- `postconditions`: Labeled boolean expressions that must hold when the procedure
  returns. May reference `old v` for pre-state values. Assumed at call sites
  unless the implementation is being verified.
-/
structure Procedure.Spec where
  /-- Labeled preconditions (`requires` clauses). -/
  preconditions  : ListMap CoreLabel Procedure.Check
  /-- Labeled postconditions (`ensures` clauses). -/
  postconditions : ListMap CoreLabel Procedure.Check
  deriving Inhabited, Repr

def Procedure.Spec.preconditionNames (s : Procedure.Spec) : List CoreLabel :=
  s.preconditions.keys

def Procedure.Spec.postconditionNames (s : Procedure.Spec) : List CoreLabel :=
  s.postconditions.keys

def Procedure.Spec.eraseTypes (s : Procedure.Spec) : Procedure.Spec :=
  { s with
    preconditions := s.preconditions.map (fun (l, c) => (l, c.eraseTypes)),
    postconditions := s.postconditions.map (fun (l, c) => (l, c.eraseTypes))
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

/--
A Strata Core procedure: the main verification unit.

A procedure consists of a header (name, type parameters, input/output signatures),
a specification (contract), and an optional body (list of statements). If the body
is empty, the procedure is abstract and can only be reasoned about via its contract.
If the body is present, it is verified against the specification.
-/
structure Procedure where
  /-- The procedure header: name, type parameters, and parameter signatures. -/
  header : Procedure.Header
  /-- The procedure's contract: modifies clause, preconditions, and postconditions. -/
  spec   : Procedure.Spec
  /-- The procedure body. Empty for abstract (bodyless) procedures. -/
  body   : List Statement
  deriving Inhabited

---------------------------------------------------------------------

open Imperative

def Procedure.definedVars (_ : Procedure) : List Expression.Ident := []
def Procedure.modifiedVars (p : Procedure) : List Expression.Ident :=
  p.header.outputs.keys

def Procedure.getVars (p : Procedure) : List Expression.Ident :=
  (p.spec.postconditions.values.map Procedure.Check.expr).flatMap HasVarsPure.getVars ++
  (p.spec.preconditions.values.map Procedure.Check.expr).flatMap HasVarsPure.getVars ++
  p.body.flatMap HasVarsPure.getVars |> List.filter (not $ Membership.mem p.header.inputs.keys ·)

instance : HasVarsPure Expression Procedure where
  getVars := Procedure.getVars

instance : HasVarsImp Expression Procedure where
  definedVars := Procedure.definedVars
  modifiedVars := Procedure.modifiedVars

def Procedure.eraseTypes (p : Procedure) : Procedure :=
  { p with body := Statements.eraseTypes p.body, spec := p.spec }

/-- Remove all metadata from procedure. -/
def Procedure.stripMetaData (p : Procedure) : Procedure :=
  { p with body := Imperative.Block.stripMetaData p.body }

/-- Transitive variable lookup for procedures.
    This is a version that looks into the body,
    but does not transitively search all variables occuring in the body.
    Transitively searching procedure bodies being called is possible,
    but the termination argument needs to be provided.
    One possible implementation is to store _a list of procedures_ in each procedure structure,
    and use the decreasing list size as a termination metric,
    as one traverses through recursively called procedure bodies.
-/
def Procedure.modifiedVarsTrans
  (_ : String → Option Procedure)
  (p: Procedure) : List Expression.Ident :=
  HasVarsImp.modifiedVars p ++
  HasVarsImp.modifiedVars p.body

/-- As `Procedure.modifiedVarsTrans`,
    this function is also non-transitive in terms of nested procedure calls.
    But it should be possible to implement one that is transtiive.
-/
def Procedure.getVarsTrans
  (_ : String → Option Procedure)
  (p: Procedure) : List Expression.Ident :=
  HasVarsPure.getVars p ++
  HasVarsPure.getVars p.body

instance : HasVarsProcTrans Expression Procedure where
  modifiedVarsTrans := Procedure.modifiedVarsTrans
  getVarsTrans := Procedure.getVarsTrans
  definedVarsTrans := λ _ _ ↦ [] -- procedures cannot define global variables
  touchedVarsTrans := Procedure.modifiedVarsTrans
  allVarsTrans :=
    λ π p ↦ Procedure.getVarsTrans π p ++ Procedure.modifiedVarsTrans π p

-- NOTE : simply discarding the procedure lookup function for now
instance : HasVarsTrans Expression Statement Procedure where
  modifiedVarsTrans := Statement.modifiedVarsTrans
  getVarsTrans := Statement.getVarsTrans
  definedVarsTrans := Statement.definedVarsTrans
  touchedVarsTrans := Statement.touchedVarsTrans
  allVarsTrans := Statement.allVarsTrans

instance : HasVarsTrans Expression (List Statement) Procedure where
  modifiedVarsTrans := Statements.modifiedVarsTrans
  getVarsTrans := Statements.getVarsTrans
  definedVarsTrans := Statements.definedVarsTrans
  touchedVarsTrans := Statements.touchedVarsTrans
  allVarsTrans := Statements.allVarsTrans

end
end Core
