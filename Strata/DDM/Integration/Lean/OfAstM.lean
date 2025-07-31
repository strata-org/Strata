/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST

namespace Strata

class HasEta (α : Type u) (β : outParam (Type v)) where
  bvar : Nat → α
  lambda : String → β → α → α

def etaExpand {E T} [HasEta E T] (argTypes : Array (String × T)) (provided : Nat) (e : E) : E :=
  if argTypesP  : provided < argTypes.size then
    let b := argTypes[argTypes.size - 1]
    let e := HasEta.lambda b.fst b.snd e
    etaExpand argTypes.pop provided e
  else
    e

def OfAstM (α : Type _) := Except String α

instance [ToString α] : ToString (OfAstM α) where
  toString e :=
    match e with
    | .error e => e
    | .ok r => toString r

instance [Repr α] : Repr (OfAstM α) where
  reprPrec e prec :=
    match e with
    | .error e => Repr.addAppParen ("error " ++ reprArg e) prec
    | .ok r => Repr.addAppParen ("ok " ++ reprArg r) prec

namespace OfAstM

instance : Monad OfAstM := inferInstanceAs (Monad (Except _))

/--
Thrown when an expression is provided but not expected.
-/
def throwUnknownExpr (tp : QualifiedIdent) (e : Expr) : OfAstM α :=
  Except.error s!"Unknown expr {repr e} when parsing as {tp}."

/--
Thrown when an expression is provided but not expected.
-/
def throwUnknownType (e : TypeExpr) : OfAstM α :=
  Except.error s!"Unknown type {repr e}."

/--
Raise error when passed an argument that is not an expression when expression expected.
-/
def throwExpected (cat : String) (a : Arg) : OfAstM α :=
  Except.error s!"Expected {cat} {repr a}."

/--
Raise error when passed an argument that is not an expression when expression expected.
-/
def throwExpectedExpr (a : Arg) : OfAstM α :=
  throwExpected "expression" a

/--
Raise error when passed an argument that is not an expression when expression expected.
-/
def throwExpectedOperation (a : Arg) : OfAstM α :=
  throwExpected "operation" a

def throwUnexpectedBvar (tp : QualifiedIdent) : OfAstM α :=
  Except.error s!"{tp} has unexpected bound variable."

def throwUnexpectedArgCount (tp : QualifiedIdent) (expected : Nat) (actual : Nat)
  : OfAstM α :=
  Except.error s!"{tp} expected {expected} arguments when {actual} provided."

def throwUnknownIdentifier (tp : QualifiedIdent) (f: QualifiedIdent) : OfAstM α :=
  Except.error s!"{tp} given unknown operator {f}."

protected def checkTypeArgCount
    (expected : Nat)
    (args : Array TypeExpr)
    : OfAstM (PLift (args.size = expected)) :=
  if p : args.size = expected then
    return .up p
  else
    .throwUnexpectedArgCount q`Init.Type expected args.size

protected def checkArgCount
    (tp : QualifiedIdent)
    (expected : Nat)
    (args : Array Arg)
    : OfAstM (PLift (args.size = expected)) :=
  if p : args.size = expected then
    return .up p
  else
    .throwUnexpectedArgCount tp expected args.size

protected def checkEtaExprArgCount
    {Tp : Type _}
    (tp : QualifiedIdent)
    (expected : Array (String × Tp))
    (args : Array Arg)
    : OfAstM (PLift (args.size ≤ expected.size)) :=
  if p : args.size ≤ expected.size then
    return .up p
  else
    .throwUnexpectedArgCount tp expected.size args.size

def ofExpressionM {α β} [SizeOf α] {e : α} {c : Int}
        (act : SizeBounded Expr e c → OfAstM β)
      : SizeBounded Arg e c → OfAstM β
| ⟨.expr a1, p⟩ => act ⟨a1, by simp at p; omega⟩
| a => .throwExpected "expression" a.val

def ofTypeM {α β} [SizeOf α] {e : α} {c : Int}
        (act : SizeBounded TypeExpr e c → OfAstM β)
      : SizeBounded Arg e c → OfAstM β
| ⟨.type a1, p⟩ => act ⟨a1, by simp at p; omega⟩
| a => .throwExpected "type" a.val

def ofOperationM {α β} [SizeOf α] {e : α} {c : Int}
        (act : SizeBounded Operation e c → OfAstM β)
      : SizeBounded Arg e c → OfAstM β
| ⟨.op a1, p⟩ => act ⟨a1, by simp only [Arg.op.sizeOf_spec] at p; omega⟩
| a => .throwExpected "operation" a.val

def ofIdentM {α} [SizeOf α] {e : α} {c : Int}
      : SizeBounded Arg e c → OfAstM String
| ⟨.ident a, _⟩ => pure a
| a => .throwExpected "identifier" a.val

def ofNumM {α} [SizeOf α] {e : α} {c : Int}
      : SizeBounded Arg e c → OfAstM Nat
| ⟨.num a, _⟩ => pure a
| a => .throwExpected "numeric literal" a.val

def ofDecimalM {α} [SizeOf α] {e : α} {c : Int}
      : SizeBounded Arg e c → OfAstM Decimal
| ⟨.decimal a, _⟩ => pure a
| a => .throwExpected "scientific literal" a.val

def ofStrlitM {α} [SizeOf α] {e : α} {c : Int}
      : SizeBounded Arg e c → OfAstM String
| ⟨.strlit a, _⟩ => pure a
| a => .throwExpected "string literal" a.val

def ofOptionM {α} [SizeOf α] {e : α} {c : Int}
      (act : SizeBounded Arg e c → OfAstM β)
      (a : SizeBounded Arg e c)
      : OfAstM (Option β) :=
  match a with
  | ⟨.option none, _⟩ => pure none
  | ⟨.option (some v), bndP⟩ => some <$> act ⟨v, by
    simp at bndP
    omega⟩
  | _ => throwExpected "option" a.val

def ofCommaSepByM {α} [SizeOf α] {e : α} {c : Int}
      (act : SizeBounded Arg e c → OfAstM β)
      (arg : SizeBounded Arg e c)
      : OfAstM (Array β) :=
  match arg with
  | ⟨.commaSepList a, bndP⟩ =>
    a.attach.mapM fun ⟨v, vp⟩  => do
      act ⟨v, by
        have p := Array.sizeOf_lt_of_mem_strict vp
        simp at bndP
        omega⟩
  | _ => throwExpected "seq" arg.val

def ofSeqM {α} [SizeOf α] {e : α} {c : Int}
      (act : SizeBounded Arg e c → OfAstM β)
      (arg : SizeBounded Arg e c)
      : OfAstM (Array β) :=
  match arg with
  | ⟨.seq a, bndP⟩ =>
    a.attach.mapM fun ⟨v, vp⟩  => do
      act ⟨v, by
        have p := Array.sizeOf_lt_of_mem_strict vp
        simp at bndP
        omega⟩
  | _ => throwExpected "seq" arg.val

/--
Get the expression at index `lvl` in the arguments.

Note that in conversion, we will
-/
def atArg {α β} [SizeOf α] {e : α} (as : SizeBounded (Array Arg) e 1) (lvl : Nat)
        (act : (s : SizeBounded Arg e (-1)) → OfAstM β)
        (lvlP : lvl < as.val.size := by get_elem_tactic) :
        OfAstM β :=
  have lvlP : lvl < as.val.size := by omega
  have p : sizeOf as.val[lvl] ≤ sizeOf e + (-1 : Int) := by
      have asP := as.property
      have inP : as.val[lvl] ∈ as.val := by simp
      have eltSizeOfP := Array.sizeOf_lt_of_mem_strict inP;
      omega
  act ⟨as.val[lvl], p⟩

/--
Get the expression at index `lvl` in the arguments.

Note that in conversion, we will
-/
def exprEtaArg [HasEta α T] {e : Expr} {n : Nat} (as : SizeBounded (Array Arg) e 1) (_ : as.val.size ≤ n) (lvl : Nat)
        (act : (s : Expr) → sizeOf s < sizeOf e → OfAstM α) :
        OfAstM α :=
  if lvlP : lvl < as.val.size then
    let i := as.val.size - 1 - lvl
    have iP : i < as.val.size := by omega
    match arg_eq : as.val[i] with
    | .expr a1 => act a1 (by
        have asP := as.property
        have idxP := Array.sizeOf_getElem as.val i iP;
        simp +arith [arg_eq] at idxP;
        omega)
    | _ => .throwExpectedExpr as.val[i]
  else
    let i := n - 1 - lvl
    return HasEta.bvar i

end Strata.OfAstM
