/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Init

public section
/-!
## Structured Function Attributes

Structured attributes for controlling partial evaluator behavior
(inlining, concrete evaluation).
-/

namespace Strata.DL.Util

/-- Attributes for functions that control partial evaluator behavior. -/
inductive FuncAttr where
  /-- Always inline the function body when called. -/
  | inline
  /-- Inline when argument at `paramIdx` is a constructor application. -/
  | inlineIfConstr (paramIdx : Nat)
  /-- Use concrete evaluation when argument at `paramIdx` is a constructor application. -/
  | evalIfConstr (paramIdx : Nat)
  /-- Use concrete evaluation when argument at `paramIdx` is a value. -/
  | evalIfValue (paramIdx : Nat)
  /-- Inline the function body when every argument satisfies `LExpr.isInlineArg`: a
  value in which closed quantifiers may also appear. -/
  | inlineIfAllValues
  /-- Evaluate the first argument alone, and if it is a value, apply concrete
      evaluation to it and the other arguments as they are, before evaluating them.
      Concrete evaluation either decides the result from the first argument or
      returns the rest of the computation, which is then evaluated once. -/
  | shortCircuit
  /-- The function is the copy monomorphization made of the factory function `base` at an
      instantiation, and denotes `base` there, so the SMT encoder encodes it as `base`. The
      attribute is what identifies a copy, never its name, since a user function can be named
      like one; only monomorphization sets it, and Core's syntax cannot state it. -/
  | monoCopyOf (base : String)
  deriving DecidableEq, Repr, Inhabited, BEq

open Std (ToFormat Format format)

instance : ToFormat FuncAttr where
  format
    | .inline => "inline"
    | .inlineIfConstr i => f!"inlineIfConstr {i}"
    | .evalIfConstr i => f!"evalIfConstr {i}"
    | .evalIfValue i => f!"evalIfValue {i}"
    | .inlineIfAllValues => "inlineIfAllValues"
    | .shortCircuit => "shortCircuit"
    | .monoCopyOf base => f!"monoCopyOf {base}"

instance : ToFormat (Array FuncAttr) where
  format attrs := Format.joinSep (attrs.toList.map format) ", "

/-- Return the `paramIdx` of the first `inlineIfConstr` attribute, if any. -/
def FuncAttr.findInlineIfConstr (attrs : Array FuncAttr) : Option Nat :=
  attrs.findSome? fun | .inlineIfConstr i => some i | _ => none

/-- Return the `paramIdx` of the first `evalIfConstr` attribute, if any. -/
def FuncAttr.findEvalIfConstr (attrs : Array FuncAttr) : Option Nat :=
  attrs.findSome? fun | .evalIfConstr i => some i | _ => none

/-- Return the `paramIdx` of the first `evalIfValue` attribute, if any. -/
def FuncAttr.findEvalIfValue (attrs : Array FuncAttr) : Option Nat :=
  attrs.findSome? fun | .evalIfValue i => some i | _ => none

/-- Return `true` if the attributes contain `inlineIfAllValues`. -/
def FuncAttr.hasInlineIfAllValues (attrs : Array FuncAttr) : Bool :=
  attrs.any (· == .inlineIfAllValues)

/-- Return `true` if the attributes contain `shortCircuit`. -/
@[expose] def FuncAttr.hasShortCircuit (attrs : Array FuncAttr) : Bool :=
  attrs.toList.any fun | .shortCircuit => true | _ => false

/-- `base` if these attributes carry `monoCopyOf base`. -/
def FuncAttr.findMonoCopyOf (attrs : Array FuncAttr) : Option String :=
  attrs.findSome? fun | .monoCopyOf base => some base | _ => none

/-- These attributes without `monoCopyOf`. -/
def FuncAttr.withoutMonoCopyOf (attrs : Array FuncAttr) : Array FuncAttr :=
  attrs.filter fun | .monoCopyOf _ => false | _ => true

end Strata.DL.Util
end
