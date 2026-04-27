/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LState

/-! ## Partial evaluator for Lambda expressions

See function `Lambda.LExpr.eval` for the implementation.
-/

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)
open Strata.DL.Util (FuncAttr)

public section

namespace LExpr

variable {T : LExprParamsT} {TBase : LExprParams} [BEq T.TypeType] [DecidableEq T.base.Metadata] [DecidableEq TBase.IDMeta] [ToFormat T.base.Metadata]
         [Inhabited T.base.IDMeta] [Inhabited TBase.IDMeta] [DecidableEq T.base.IDMeta] [ToFormat T.base.IDMeta] [Traceable EvalProvenance TBase.Metadata]

inductive EvalProvenance
  | Original -- The metadata of the original expression
  | ReplacementVar -- The original bound variable that was replaced
  | Abstraction -- The lambda that triggered the replacement

/--
Check for boolean equality of two expressions `e1` and `e2` after erasing any
metadata.
-/
def eqModuloMeta (e1 e2 : LExpr T) : Bool :=
  e1.eraseMetadata == e2.eraseMetadata

/-- Three-valued `and` for `Option Bool`: `some false` if either is `some false`,
  `some true` if both are `some true`, `none` (inconclusive) otherwise. -/
def eqlCombine (o1 o2: Option Bool) :=
  match o1, o2 with
  | some false, _ => some false
  | _, some false => some false
  | some true, some true => some true
  | _, _ => none

/--
Semantic equality check for two expressions `e1` and `e2`.

Returns `some true` if provably equal, `some false` if provably not equal,
`none` if inconclusive.

This test is relatively conservative:
- Terms are equal if syntactically equal
- Syntactically different, non-real constants are not equal
- Closed lambdas of the same type are compared extensionally (i.e.
syntactically after substituting a fresh variable for the body). Note that this
does not evaluate the body, which may not be a canonical value.
- Datatype constructor applications are compared using known injectivity
and disjointness properties of datatypes.
-/
def eql (F : @Factory T.base) (e1 e2 : LExpr T) : Option Bool :=
  -- If syntactic equality holds, so does semantic equality
  if eqModuloMeta e1 e2 then some true
  else
  -- Disproving equality is harder, we have several special cases
  match _he: e1, e2 with
  -- Case 1: Syntactic inequality of (non-real) constants implies semantic inequality
  | .const _ c1, .const _ c2 =>
    match c1, c2 with
    | .realConst _, .realConst _ => none
    | _, _ =>  some (c1 == c2)
  -- Case 2: Comparing Lambdas
  | .abs _ _ ty1 e1, .abs _ _ ty2 e2 =>
    if ty1 != ty2 then some false
    -- "x" is fresh, so if this gives `some b` then
    -- we have proved or disproved functional extensionality
    -- It may be inconclusive if inequality requires
    -- a specific value or if the body is not reduced
    -- E.g. λ x. if x == 0 then 1 else 2 and λ x. 2 is inconclusive
    else if e1.closed && e2.closed then
      eql F (e1.varOpen 0 ("x", ty1)) (e2.varOpen 0 ("x", ty2))
    else none
  -- Some known inequalities
  | .const _ _, .abs _ _ _ _ => some false
  | .abs _ _ _ _, .const _ _ => some false
  -- Case 3: datatype constructor applications
  | _, _ =>
    match _h1: Factory.callOfLFunc F e1 false, Factory.callOfLFunc F e2 false with
    | some (_, args1, f1), some (_, args2, f2) =>
      -- Only apply disjointness/injectivity to constructors
      if !f1.isConstr || !f2.isConstr then none
      else if f1.name.name != f2.name.name then some false
      else
      -- If all arguments are provably equal, constructor app is equal
      -- If any are not equal, then they are not equal by injectivity
      -- Otherwise, incomparable
      List.foldl (fun acc (⟨a1, _⟩, a2) =>
        eqlCombine acc (eql F a1 a2)
      ) (some true) (args1.attach.zip args2)
    | _, _ => none
  termination_by e1.sizeOf
  decreasing_by
    . rw[varOpen_sizeOf]; simp_all
    . have := Factory.callOfLFunc_smaller _h1; subst_vars; grind


/--
Canonical values of `LExpr`s.

If `e:LExpr` is `.app`, say `e1 e2 .. en`, `e` is a canonical value if
(1) `e1` is a constructor and `e2 .. en` are all canonical values, or
(2) `e1` is a named function `f` (not abstraction) and `n` is less than the
    number of arguments required to run the function `f`.

The intuition of case (2) is as follows. Let's assume that we would like to
calculate `Int.Add 1 (2+3)`. According to the small step semantics, we would
like to calculate `2+3` to `5`, hence it becomes `Int.Add 1 5` and eventually 6.
Without (2), this is impossible because the `reduce_2` rule of small step
semantics only fires when `Int.Add 1` is a 'canonical value'. Therefore, without
(2), the semantics stuck and `2+3` can never be evaluated to `5`.
-/
def isCanonicalValue (F : @Factory T.base) (e : LExpr T) : Bool :=
  match he: e with
  | .const _ _ => true
  | .abs _ _ _ _ | .quant _ _ _ _ _ _ =>
    -- We're using the locally nameless representation, which guarantees that
    -- `closed (.abs e) = closed e` (see theorem `closed_abs`).
    -- So we could simplify the following to `closed e`, but leave it as is for
    -- clarity.
    LExpr.closed e
  | e' =>
    match h: Factory.callOfLFunc F e true with
    | some (_, args, f) =>
      (f.isConstr || Nat.blt args.length f.inputs.length) &&
      List.all (args.attach.map (fun ⟨ x, _⟩ =>
        have : x.sizeOf < e'.sizeOf := by
          have Hsmall := Factory.callOfLFunc_smaller h; grind
        (isCanonicalValue F x))) id
    | none => false
  termination_by e.sizeOf

/--
Check if `e` is a constructor application.
-/
def isConstrApp (F : @Factory T.base) (e : LExpr T) : Bool :=
  match Factory.callOfLFunc F e true with
  | some (_, _, f) => f.isConstr
  | none => false

/--
Check if `e` contains a binder (abstraction or quantifier) anywhere in its
structure. Used to prevent reducing equality to `false` under binders, since
syntactic inequality does not imply semantic inequality for expressions with
binders (e.g., `λx. x+1` vs `λx. 1+x`).
-/
def containsBinder (e : LExpr T) : Bool :=
  match e with
  | .abs _ _ _ _ | .quant _ _ _ _ _ _ => true
  | .app _ e1 e2 | .eq _ e1 e2 => containsBinder e1 || containsBinder e2
  | .ite _ c t f => containsBinder c || containsBinder t || containsBinder f
  | _ => false

instance [ToFormat T.TypeType]: ToFormat (Except Format (LExpr T)) where
  format x := match x with
              | .ok e => format e
              | .error err => err

instance [ToFormat T.TypeType]: ToFormat (Except Strata.DiagnosticModel (LExpr T)) where
  format x := match x with
              | .ok e => format e
              | .error err => f!"{err.message}"

/--
A metadata merger. It will be invoked 'subst s e' is invoked, to create a new
metadata.
-/
def mergeMetadataForSubst (metaAbs metaE2 metaReplacementVar: TBase.Metadata) :=
  Traceable.combine
  [(EvalProvenance.Original,       metaE2),
    (EvalProvenance.ReplacementVar, metaReplacementVar),
    (EvalProvenance.Abstraction,    metaAbs)]


mutual
/--
(Partial) evaluator for Lambda expressions w.r.t. a module, written using a fuel
argument.

Note that this function ascribes Curry-style semantics to `LExpr`s, i.e., we
can evaluate ill-typed terms w.r.t. a given type system here.

We prefer Curry-style semantics because they separate the type system from
evaluation, allowing us to potentially apply different type systems with our
expressions, along with supporting dynamically-typed languages.

Currently evaluator only supports LExpr with LMonoTy because LFuncs registered
at Factory must have LMonoTy.
-/
def eval (n : Nat) (σ : LState TBase) (e : (LExpr TBase.mono))
    : LExpr TBase.mono :=
  match n with
  | 0 => e
  | n' + 1 =>
    if isCanonicalValue σ.config.factory e then
      e
    else
      -- Special handling for Factory functions.
      match σ.config.factory.callOfLFunc e with
      | some (op_expr, args, lfunc) =>
        let args := args.map (fun a => eval n' σ a)
        let constrArgAt (idx : Option Nat) :=
          match idx with
          | some i => (args[i]? |>.map (isConstrApp σ.config.factory)).getD false
          | none => false
        let canonicalArgAt (idx : Option Nat) :=
          match idx with
          | some i => (args[i]? |>.map (isCanonicalValue σ.config.factory)).getD false
          | none => false
        if h: lfunc.body.isSome && (lfunc.attr.contains .inline ||
          constrArgAt (FuncAttr.findInlineIfConstr lfunc.attr)) then
          -- Inline a function only if it has a body.
          let body := lfunc.body.get (by simp_all)
          -- Apply type substitution to instantiate polymorphic type variables.
          match LFunc.computeTypeSubst lfunc op_expr args with
          | some tySubst =>
            let body := body.applySubst tySubst
            let input_map := lfunc.inputs.keys.zip args
            let new_e := substFvarsLifting body input_map
            eval n' σ new_e
          | none => e -- cannot happen in well-typed terms
        else
          let new_e := @mkApp TBase.mono e.metadata op_expr args
            -- All arguments in the function call are concrete.
            -- We can, provided a denotation function, evaluate this function
            -- call.
          if args.all (isCanonicalValue σ.config.factory) ||
            -- Other functions (e.g. Eliminators) only require the designated
            -- arg to be a constructor
            constrArgAt (FuncAttr.findEvalIfConstr lfunc.attr) ||
            -- Some functions (e.g. regex) only require the designated
            -- arg to be a canonical value (e.g. a constant string)
            canonicalArgAt (FuncAttr.findEvalIfCanonical lfunc.attr) then
            match lfunc.concreteEval with
            | none => new_e
            | some ceval =>
              match ceval new_e.metadata args with
              | .some e' => eval n' σ e'
              | .none => new_e
          else
            -- At least one argument in the function call is symbolic.
            new_e
      | none =>
        -- Not a call of a factory function - go through evalCore
        evalCore n' σ e

@[expose] def evalCore  (n' : Nat) (σ : LState TBase) (e : LExpr TBase.mono) : LExpr TBase.mono :=
  match e with
  | .const _ _  => e
  | .op _ _ _     => e
  | .bvar _ _     => e
  | .fvar _ x ty  => (σ.state.findD x (ty, e)).snd
   -- Note: closed .abs terms are canonical values; we'll be here if .abs
   -- contains free variables.
  | .abs _ _ _ _   => LExpr.substFvarsFromState σ e
  | .quant _ _ _ _ _ _ => LExpr.substFvarsFromState σ e
  | .app _ e1 e2 => evalApp n' σ e e1 e2
  | .eq m e1 e2 => evalEq n' σ m e1 e2
  | .ite m c t f => evalIte n' σ m c t f

-- Note: this evaluation is eager -- both branches are fully evaluated even when
-- the condition is not resolved to true/false. This was originally lazy (only
-- substituting free variables via `substFvarsFromState`), but we switched to
-- eager evaluation to support recursive functions, where the branches may
-- contain recursive calls that need to be unfolded. If we ever need a lazy mode
-- again, we should add a flag.
def evalIte (n' : Nat) (σ : LState TBase) (m: TBase.Metadata) (c t f : LExpr TBase.mono) : LExpr TBase.mono :=
  let c' := eval n' σ c
  match c' with
  | .true _ => eval n' σ t
  | .false _ => eval n' σ f
  | _ =>
    let t' := eval n' σ t
    let f' := eval n' σ f
    .ite m c' t' f'

def evalEq (n' : Nat) (σ : LState TBase) (m: TBase.Metadata) (e1 e2 : LExpr TBase.mono) : LExpr TBase.mono :=
  open LTy.Syntax in
  let e1' := eval n' σ e1
  let e2' := eval n' σ e2
  match eql σ.config.factory e1' e2' with
  | some b => .const m (.boolConst b)
  | none => .eq m e1' e2'

def evalApp (n' : Nat) (σ : LState TBase) (e e1 e2 : LExpr TBase.mono) : LExpr TBase.mono :=
  let e1' := eval n' σ e1
  let e2' := eval n' σ e2
  match e1' with
  | .abs mAbs _ _ e1' =>
    let e' := subst (fun metaReplacementVar =>
      let newMeta := mergeMetadataForSubst mAbs e2'.metadata metaReplacementVar
      replaceMetadata1 newMeta e2') e1'
    if eqModuloMeta e e' then e else eval n' σ e'
  | _e =>
    -- Re-evaluate when subexpressions changed (e.g. fvar resolved to .op),
    -- so that `callOfLFunc` in `eval` can recognise the rebuilt expression
    -- as a factory function call.  When nothing changed, `eqModuloMeta`
    -- short-circuits and we return immediately.
    let e' := .app e.metadata e1' e2'
    if eqModuloMeta e e' then e else eval n' σ e'
end

instance : Traceable EvalProvenance Unit where
  combine _ := ()


/-! ## Expression Evaluation -/

/-- Walk a post-eval expression looking for a stuck redex: a fully-applied
non-constructor factory function whose arguments are all canonical values.
Such a call *should* have reduced during `eval` but didn't (e.g. missing `body`
or `concreteEval`). Returns the stuck subexpression if found.

This helps errors point more precisely to where the interpreter got stuck.
 -/
def findStuckRedex (F : @Lambda.Factory TBase) : LExpr TBase.mono → Option (LExpr TBase.mono)
  | .const _ _ | .op _ _ _ | .bvar _ _ | .fvar _ _ _ | .abs _ _ _ _ | .quant _ _ _ _ _ _ => none
  | .eq _m e1 e2 =>
    (findStuckRedex F e1).orElse (fun _ => findStuckRedex F e2)
  | .ite _m c t f =>
    (findStuckRedex F c).orElse (fun _ => (findStuckRedex F t).orElse (fun _ => findStuckRedex F f))
  | e@(.app _m fn arg) =>
    match Factory.callOfLFunc F e false with
    | some (_, args, f) =>
      if !f.isConstr && args.all (LExpr.isCanonicalValue F) then
        some e
      else
        -- Non-stuck call: recurse into fn and arg (structural subterms)
        (findStuckRedex F fn).orElse (fun _ => findStuckRedex F arg)
    | none =>
      (findStuckRedex F fn).orElse (fun _ => findStuckRedex F arg)

/-- Evaluate an expression using the interpreter's environment.

This is the interpreter's own expression evaluator, defined as a separate
function so that we can later prove it consistent with the small-step
`Lambda.Step` relation from `Strata.DL.Lambda.Semantics`.

Currently delegates to `LExpr.eval` with the fuel and state from `Env`.
If the result contains a stuck redex (a fully-applied function that should
have reduced but didn't), returns an error.
-/
def run (σ : LState TBase) (e : (LExpr TBase.mono)) : Except String (LExpr TBase.mono) :=
  let v := e.eval σ.config.fuel σ
  if LExpr.isCanonicalValue σ.config.factory v then
    .ok v
  else
    match findStuckRedex σ.config.factory v with
    | some _ => .error "expression contains stuck redex"
    | none => .ok v

end LExpr
end -- public section
end Lambda
