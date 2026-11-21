/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module


public import Strata.DL.Imperative.HasVars
public import Strata.DL.Imperative.BasicBlock
public import Strata.DL.Imperative.Procedure
public import Strata.Languages.Core.Statement
public import Strata.DL.Lambda.LTyMatch

---------------------------------------------------------------------

namespace Core
public section

open Std (ToFormat Format format)
open Lambda
open Std.Format

-- Type class instances to enable deriving for structures containing Expression.Expr
instance : DecidableEq ExpressionMetadata :=
  show DecidableEq ExprSourceLoc from inferInstance

instance : Repr ExpressionMetadata :=
  show Repr ExprSourceLoc from inferInstance

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
  /-- Names of the top-level lemmas this procedure depends on, such as the
      well-formedness lemmas of its contract. -/
  lemmas : List String := []
  deriving Repr, DecidableEq, Inhabited

/-- The free type variables of a procedure signature are among its type parameters. -/
@[expose] def Procedure.Header.SigDeclared (hdr : Procedure.Header) : Prop :=
  ∀ v, v ∈ LMonoTys.freeVars hdr.inputs.values ++ LMonoTys.freeVars hdr.outputs.values →
    v ∈ hdr.typeArgs

/-- Parameters that appear in both `inputs` and `outputs` (in-out parameters).
    These are the parameters for which `old x` snapshots are meaningful. -/
@[expose] def getInoutParams (inputs outputs : @LMonoTySignature Unit) : @LMonoTySignature Unit :=
  inputs.filter fun (id, _) => (ListMap.keys outputs).contains id

/-- Parameters that appear in both `inputs` and `outputs` (in-out parameters). -/
@[expose] def Procedure.Header.getInoutParams (h : Procedure.Header) : @LMonoTySignature Unit :=
  Core.getInoutParams h.inputs h.outputs

/-- No input or output parameter is named `CoreIdent.mkOld g.name` for an in-out parameter `g`,
    the name under which a call saves `g`'s starting value. -/
@[expose] def Procedure.Header.oldNamesFresh (h : Procedure.Header) : Prop :=
  ∀ g ∈ h.getInoutParams.keys, CoreIdent.mkOld g.name ∉ h.inputs.keys ++ h.outputs.keys

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

/-- Expressions of checks that are obligations rather than `free` assumptions. -/
def Procedure.Spec.getDefaultCheckExprs
    (conds : ListMap CoreLabel Procedure.Check) : List Expression.Expr :=
  conds.values.filterMap fun c =>
    if c.attr = .Default then some c.expr else none

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
abbrev DetCFG := Imperative.DetCFG Expression Command

/-- The body of a Core procedure: structured, CFG, or `abstract` (no body). -/
abbrev Procedure.Body := Imperative.Body Expression Command

@[match_pattern] abbrev Procedure.Body.structured := @Imperative.Body.structured Expression Command
@[match_pattern] abbrev Procedure.Body.cfg := @Imperative.Body.cfg Expression Command
@[match_pattern] abbrev Procedure.Body.abstract := @Imperative.Body.abstract Expression Command

/-- The procedure names a structured body calls; empty for a CFG body. -/
@[simp] def Procedure.Body.calledProcedureNames : Procedure.Body → List String
  | .structured ss _ => Statements.calledProcedureNames ss
  | .cfg _ _ | .abstract => []

/-- A Strata Core procedure: the main verification unit. A procedure is a header
    (name, type parameters, input/output signatures), a specification (contract),
    and a body. An `abstract` body makes the procedure reasoned about only via
    its contract. -/
abbrev Procedure := Imperative.Procedure Expression Command Procedure.Header

/-- The procedure names a procedure's body calls. -/
@[simp] def Procedure.calledProcedureNames (p : Procedure) : List String :=
  Procedure.Body.calledProcedureNames p.body

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
      | .structured ss o => .structured (Statements.mapExprs f ss) o
      | .cfg c o => .cfg c o
      | .abstract => .abstract }

/-- The assertions of the procedure's non-free preconditions, which a caller checks. -/
@[expose] def Procedure.preconditionAsserts (p : Procedure) : List Statement :=
  p.spec.preconditions.toList.filterMap fun (label, check) =>
    if check.attr matches .Free then none else some (Statement.assert label check.expr check.md)

/-- The procedure's contract as statements, the meaning of a call to an opaque callee: assert the
    non-free preconditions, havoc `havocs` (with metadata `md`), then assume every postcondition. -/
@[expose] def Procedure.contractStmts (p : Procedure) (havocs : List Expression.Ident)
    (md : Imperative.MetaData Expression) : List Statement :=
  p.preconditionAsserts ++ havocs.map (Statement.havoc · md) ++
    p.spec.postconditions.toList.map fun (label, check) =>
      Statement.assume label check.expr check.md

section Collect

variable {β : Type} (fe : Expression.Expr → List β) (ft : LMonoTy → List β)

/-- What `fe` and `ft` collect from a procedure body: a statement list, the blocks of a control
    flow graph with the expressions in their metadata, or nothing for an abstract procedure. -/
def bodyCollect (body : Procedure.Body) : List β :=
  match body with
  | .structured ss _ => stmtsCollect fe ft ss
  | .cfg c _ => c.blocks.flatMap fun (_, blk) =>
      blk.md.exprs.flatMap fe ++ blk.cmds.flatMap (cmdCollect fe ft) ++
        match blk.transfer with
        | .condGoto g _ _ _ => fe g
        | .finish _ => []
  | .abstract => []

/-- The commands of a procedure body, in order: those of its statements, or of the blocks of its
    control flow graph; none for an abstract procedure. -/
def bodyCmds (body : Procedure.Body) : List Command :=
  match body with
  | .structured ss _ => stmtsCmds ss
  | .cfg c _ => c.blocks.flatMap fun (_, blk) => blk.cmds
  | .abstract => []

/-- What `fe` and `ft` collect from a procedure's conditions and body. -/
def procCollect (proc : Procedure) : List β :=
  proc.spec.preconditions.values.flatMap (fun chk => fe chk.expr) ++
    proc.spec.postconditions.values.flatMap (fun chk => fe chk.expr) ++
    bodyCollect fe ft proc.body

end Collect

/-- Does every type annotation in a procedure body, including control-flow graph guards
    and the expressions in block metadata, satisfy `p`? -/
def Procedure.allBodyTys (p : LMonoTy → Bool) (body : Procedure.Body) : Bool :=
  (bodyCollect exprAnnotTys ([·]) body).all p

/-- Does every type annotation in a procedure's preconditions, postconditions, and body
    satisfy `p`? -/
def Procedure.allTys (p : LMonoTy → Bool) (proc : Procedure) : Bool :=
  (procCollect exprAnnotTys ([·]) proc).all p

---------------------------------------------------------------------

open Imperative

instance : Imperative.ProcedureHeader Expression Procedure.Header where
  name h         := h.name
  inputParams  h := h.inputs.keys
  outputParams h := h.outputs.keys

/-- Apply `fc` to every command, and `fe` to every branch guard and every expression of
    the block metadata (a loop invariant), of a control-flow graph, keeping its labels
    and shape. -/
def DetCFG.mapCmdsGuards (cfg : DetCFG) (fc : Command → Command)
    (fe : Expression.Expr → Expression.Expr) : DetCFG :=
  { cfg with blocks := cfg.blocks.map fun (lbl, blk) =>
      (lbl, { blk with
                cmds := blk.cmds.map fc,
                md := blk.md.mapExprs fe,
                transfer := match blk.transfer with
                  | .condGoto p lt lf md => .condGoto (fe p) lt lf md
                  | .finish md => .finish md }) }

def DetCFG.eraseTypes (cfg : DetCFG) : DetCFG :=
  DetCFG.mapCmdsGuards cfg Command.eraseTypes (·.eraseTypes)

/-- Erase every annotation of a control-flow graph: its commands, branch guards and the loop
    invariants in its block metadata. -/
def DetCFG.eraseAnnots (cfg : DetCFG) : DetCFG :=
  DetCFG.mapCmdsGuards cfg Command.eraseAnnots Lambda.LExpr.eraseTypes

/-- `proc` with `f` applied to every type it mentions (its formals' types, the type annotations
    of its contract and its body) and its type parameters replaced by `typeArgs`. -/
def Procedure.mapTys (proc : Procedure) (f : LMonoTy → LMonoTy)
    (typeArgs : List TyIdentifier) : Procedure :=
  let mapChecks (cs : ListMap CoreLabel Procedure.Check) :=
    cs.map fun p => (p.1, { p.2 with expr := mapExprTys f p.2.expr })
  { header := { proc.header with
      typeArgs := typeArgs,
      inputs := proc.header.inputs.map fun p => (p.1, f p.2),
      outputs := proc.header.outputs.map fun p => (p.1, f p.2) },
    spec := { proc.spec with
      preconditions := mapChecks proc.spec.preconditions,
      postconditions := mapChecks proc.spec.postconditions },
    body := match proc.body with
      | .structured ss o => .structured (mapStmtsTys f ss) o
      | .cfg c o => .cfg (DetCFG.mapCmdsGuards c (mapCmdTys f) (mapExprTys f)) o
      | .abstract => .abstract }

/-- `proc` with its type parameters renamed by `ren` throughout, as
    `renameTyArgList` does to the parameter list. -/
def Procedure.renameTypeArgs (proc : Procedure) (ren : List (String × String)) :
    Procedure :=
  proc.mapTys (LMonoTy.subst (Subst.ofRenaming ren)) (renameTyArgList ren proc.header.typeArgs)

/-- Whether every type the body of `proc` declares a variable at (`init`) is a monotype.  The
    typing rules require this (`CmdWellTyped.init_det`, `CmdHasType.init_det`), so it holds of
    every type-checked procedure. -/
@[expose] def Procedure.initTypesMono (proc : Procedure) : Bool :=
  (match proc.body with
    | .structured ss _ => Imperative.Block.initTypes ss
    | .cfg c _ => Imperative.DetCFG.initTypes c
    | .abstract => []).all LTy.isMonoType

/-- `proc` instantiated at the type arguments `tys` of a call: each type parameter is replaced
    throughout by its type argument, position by position, and the result has no type
    parameters.  A monomorphic procedure is its own instance at `[]`.  `none` when `tys` has
    the wrong length or holds a type that is not a monotype, and, for a polymorphic procedure,
    when its body declares a variable at a quantified type (`initTypesMono`).  With every type
    of the procedure a monotype, the substitution has no binder to go under, so it is exact for
    any monotypes `tys`, ground or not; under a quantified `init` type it would substitute
    bound variables and could capture a variable of `tys`.  The typing rules allow only
    monotypes there, so no type-checked procedure is refused. -/
@[expose] def Procedure.instantiateTypes (proc : Procedure) (tys : List Expression.Ty) :
    Option Procedure :=
  if proc.header.typeArgs.isEmpty then
    if tys.isEmpty then some proc else none
  else if tys.length ≠ proc.header.typeArgs.length then none
  else if !proc.initTypesMono then none
  else (tys.mapM LTy.toMonoType?).map fun ms =>
    proc.mapTys (LMonoTy.subst (Strata.Util.HMaps.ofScopes [proc.header.typeArgs.zip ms])) []

instance : Imperative.ProcedureTypeInstantiation Expression Procedure.Header where
  instantiate := Procedure.instantiateTypes

-- Only transfer metadata is stripped: command metadata (on assert, assume,
-- init, set, cover) is not part of the formatted output (formatCmd discards
-- it), while transfer metadata is. Block metadata is kept: it holds the block's
-- annotations (`@[loopInvariant = (e)]`), which are part of the program.
def DetCFG.stripMetaData (cfg : DetCFG) : DetCFG :=
  { cfg with blocks := cfg.blocks.map fun (lbl, blk) =>
      (lbl, { blk with transfer := match blk.transfer with
                          | .condGoto p lt lf _ => .condGoto p lt lf .empty
                          | .finish _ => .finish .empty }) }

def Procedure.eraseTypes (p : Procedure) : Procedure :=
  let body' := match p.body with
    | .structured ss o => .structured (Statements.eraseTypes ss) o
    | .cfg c o => .cfg (DetCFG.eraseTypes c) o
    | .abstract => .abstract
  { p with body := body', spec := p.spec }

/-- Erase every annotation of a procedure: type parameters become placeholders (count and
    order kept), signature types are erased, and so are the specification and the body. -/
def Procedure.eraseAnnots (p : Procedure) : Procedure :=
  { p with
    header := { p.header with
      typeArgs := p.header.typeArgs.map fun _ => "",
      inputs := p.header.inputs.map fun (x, _) => (x, LMonoTy.erased),
      outputs := p.header.outputs.map fun (x, _) => (x, LMonoTy.erased) },
    spec := Procedure.Spec.eraseTypes p.spec,
    body := match p.body with
      | .structured ss o => .structured (Statements.eraseAnnots ss) o
      | .cfg c o => .cfg (DetCFG.eraseAnnots c) o
      | .abstract => .abstract }

def Procedure.stripMetaData (p : Procedure) : Procedure :=
  let body' := match p.body with
    | .structured ss o => .structured (Imperative.Block.stripMetaData ss) o
    | .cfg c o => .cfg (DetCFG.stripMetaData c) o
    | .abstract => .abstract
  { p with body := body' }

/-- The calls in `p`'s body: structured bodies in statement order, CFG bodies in
    block order. -/
def Procedure.callSites (p : Procedure) : List CallSite :=
  match p.body with
  | .structured ss _ => Statements.callSites ss
  | .cfg g _ => g.blocks.flatMap fun (_, blk) => blk.cmds.flatMap Command.callSites
  | .abstract => []

/-- The type arguments of `proc` at a call, matched one-way against the known types of the
    call's inputs `inTys` and outputs `outTys`; `none` on a mismatch. -/
def Procedure.matchCall? (proc : Procedure) (inTys outTys : List (Option LMonoTy)) :
    Option SubstOne :=
  LMonoTys.matchKnown? proc.header.typeArgs
    (proc.header.inputs.values.zip inTys ++ proc.header.outputs.values.zip outTys)

/-- The type variables of `m` generated by the type checker or by an earlier evaluated call
    (`$__ty`, `$__callty`). -/
private def generatedVars (m : LMonoTy) : List TyIdentifier :=
  m.freeVars.filter fun a =>
    [Lambda.genTyPrefix, Lambda.callTyVarPrefix].any fun p => a.startsWith p

/-- `m` with every generated type variable written as `_`, for error messages. -/
private def hideGenerated (m : LMonoTy) : LMonoTy :=
  LMonoTy.subst
    [(generatedVars m).foldl (init := Strata.Util.HMap.empty) fun S a => S.insert a (.ftvar "_")] m

/-- The type arguments of `proc` at a call that stores `tyArgs`. When `tyArgs` has one entry per
    type parameter, they are read from it, position by position; a parameter whose entry is not a
    monotype, or mentions a generated type variable, is left unbound. Otherwise (a call that was
    not type-checked) they are matched one-way against the known types of the call's inputs
    `inTys` and outputs `outTys`, as in `Procedure.matchCall?`.
    Every stored entry that is used agrees with the types of the call's arguments; an error
    names the first parameter on which they disagree. A matched type with generated variables
    agrees with the stored one when the stored type is an instance of it, and the bindings of
    those variables carry from one parameter to the next. If the matching fails (the header may
    name an alias it does not expand, or two arguments may give one parameter different types),
    the stored entries are then used unchecked. In an error message, generated type variables
    are written `_`. -/
def Procedure.callTypeArgs (proc : Procedure) (tyArgs : Option (List LTy))
    (inTys outTys : List (Option LMonoTy)) : Except String (Option SubstOne) :=
  match tyArgs with
  | some tys =>
    if tys.length = proc.header.typeArgs.length then
      let stored : SubstOne :=
        (proc.header.typeArgs.zip tys).foldl (init := Strata.Util.HMap.empty) fun S (a, t) =>
          match t.toMonoType? with
          | some m =>
            if m.freeVars.any (·.startsWith Lambda.genTyPrefix) then S else S.insert a m
          | none => S
      let matched := (proc.matchCall? inTys outTys).getD Strata.Util.HMap.empty
      let agreement : Except (TyIdentifier × LMonoTy × LMonoTy) SubstOne :=
        proc.header.typeArgs.foldlM (init := Strata.Util.HMap.empty) fun S a =>
          match stored.find? a, matched.find? a with
          | some s, some m =>
            match LMonoTy.matchTy? (generatedVars m) S m s with
            | some S' => .ok S'
            | none => .error (a, s, LMonoTy.subst [S] m)
          | _, _ => .ok S
      match agreement with
      | .error (a, s, m) =>
        .error s!"the call to {proc.header.name.name} stores {a} = {format (hideGenerated s)},\n\
          but its arguments give {a} = {format (hideGenerated m)}"
      | .ok _ => .ok (some stored)
    else .ok (proc.matchCall? inTys outTys)
  | none => .ok (proc.matchCall? inTys outTys)

namespace Transform

/-- A reference to the variable `ident`, annotated with `ty` when given. -/
def createFvar (ident : Expression.Ident) (ty : Option Lambda.LMonoTy := none)
  : Expression.Expr
  := Lambda.LExpr.fvar (ExprSourceLoc.synthesized "transform") ident ty

/-- The expressions a call passes for the callee inputs `inputs`, each `inout` variable annotated
    with its input's type. -/
def typedInputExprs (inputs : @Lambda.LMonoTySignature Unit)
    (callArgs : List (Imperative.CallArg Expression)) : List Expression.Expr :=
  ((Imperative.CallArg.inputArgs callArgs).zip inputs.values).filterMap fun
    | (.inArg e, _) => some e
    | (.inoutArg x, ty) => some (createFvar x (some ty))
    | (.outArg _, _) => none

end Transform

/-! ## The variables of a procedure

The variables of a procedure's body that its header binds: its parameters, and `old x` for each
in-out parameter `x`, which denotes the entry value of `x`. -/

/-- Types of a procedure's parameters (and of `old x` for its in-out parameters). -/
@[expose] def Procedure.paramTys (p : Procedure) : List (Expression.Ident × Expression.Ty) :=
  let params := (p.header.inputs ++ p.header.outputs).map fun (x, ty) =>
    ((x : CoreIdent), (.forAll [] ty : Expression.Ty))
  let olds := p.header.getInoutParams.map fun (x, ty) =>
    (CoreIdent.mkOld x.name, (.forAll [] ty : Expression.Ty))
  params ++ olds

/-- The variables in scope at the entry of a statement list of the procedure `p`: its parameters
    and `old x` for its in-out parameters `x`. -/
@[expose] def Procedure.entryScope (p : Procedure) : List Expression.Ident :=
  (Procedure.paramTys p).map (·.1)

/-- The parameters of `p`, inputs then outputs, each once. -/
@[expose] def Procedure.entryParams (p : Procedure) : List Expression.Ident :=
  Strata.Util.OrderedSet.eraseDups
    ((p.header.inputs ++ p.header.outputs).map fun (x, _) => (x : CoreIdent))

/-- The variables of `p` that denote the entry value of a parameter: `old x`, with `x`, for each
    in-out parameter `x`. -/
@[expose] def Procedure.oldAliases (p : Procedure) : List (Expression.Ident × Expression.Ident) :=
  p.header.getInoutParams.map fun (x, _) => (CoreIdent.mkOld x.name, x)

end
end Core
