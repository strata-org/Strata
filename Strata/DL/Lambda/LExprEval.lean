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
@[expose] def isCanonicalValue (F : @Factory T.base) (e : LExpr T) : Bool :=
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


/--
Classification of partial evaluation outcome.
- `outOfFuel`: ran out of fuel before reaching a normal form.
- `value`: the result is a canonical value (satisfies `isCanonicalValue`).
  The Boolean flag `everyStepFullyReduced` records whether every recursive
  invocation of `eval` performed by the current call itself returned
  `.value true` — i.e. whether the entire evaluation was fully reduced end
  to end, with no `.nonvalue`/`.outOfFuel`/`.value false` subterm masked.
- `nonvalue`: evaluation terminated (not out of fuel) but the result is not a
  canonical value.
-/
inductive EvalResult where
  | outOfFuel
  | value (everyStepFullyReduced : Bool)
  | nonvalue

/-- Was `r` produced by an evaluation whose every recursive `eval` call itself
    returned `.value true`? -/
def EvalResult.isValueTrue : EvalResult → Bool
  | .value true => true
  | _ => false

/-- Is `r` a `.value _`? -/
def EvalResult.isValue : EvalResult → Bool
  | .value _ => true
  | _ => false

def EvalResult.combineValueFlag (r : EvalResult) (b : Bool) : EvalResult :=
  match r with
  | .value b' => .value (b' && b)
  | _ => r

@[expose] def combineEvalResValueFlag {α : Type} (b : Bool) (p : α × EvalResult) : α × EvalResult :=
  (p.fst, p.snd.combineValueFlag b)

@[simp] theorem combineEvalResValueFlag_eq_pair {α : Type} (b : Bool) (p : α × EvalResult) :
    combineEvalResValueFlag b p = (p.fst, p.snd.combineValueFlag b) := rfl

@[simp] theorem List_map_fst_map_eval {α β γ : Type} (args : List α) (g : α → β × γ) :
    List.map Prod.fst (List.map g args) = List.map (fun a => (g a).fst) args := by
  induction args with
  | nil => rfl
  | cons a as ih => simp [ih]

@[simp] theorem List_all_snd_isValueTrue_map_eval {α β : Type} (args : List α)
    (g : α → β × EvalResult) :
    (List.map g args).all (fun r => r.snd.isValueTrue) =
    args.all (fun a => (g a).snd.isValueTrue) := by
  induction args with
  | nil => rfl
  | cons a as ih => simp [ih]


mutual
/--
(Partial) evaluator for Lambda expressions w.r.t. a module, written using a fuel
argument.

The behavior of eval depends on the annotated types in expression `e` when
`e` contains an equality; see `eql`.

Currently evaluator only supports LExpr with LMonoTy because LFuncs registered
at Factory must have LMonoTy.
-/
def eval (n : Nat) (F : @Factory TBase) (env : Env TBase) (e : (LExpr TBase.mono))
    : LExpr TBase.mono × EvalResult :=
  match n with
  | 0 => (e, if isCanonicalValue F e then .value true else .outOfFuel)
  | n' + 1 =>
    if isCanonicalValue F e then
      (e, .value true)
    else
      match F.callOfLFunc e with
      | some (op_expr, args, lfunc) =>
        let argResults := args.map (fun a => eval n' F env a)
        let argsAllFull := argResults.all (fun r => r.snd.isValueTrue)
        let args := argResults.map Prod.fst
        let constrArgAt (idx : Option Nat) :=
          match idx with
          | some i => (args[i]? |>.map (isConstrApp F)).getD false
          | none => false
        let canonicalArgAt (idx : Option Nat) :=
          match idx with
          | some i => (args[i]? |>.map (isCanonicalValue F)).getD false
          | none => false
        if h: lfunc.body.isSome && (lfunc.attr.contains .inline ||
          constrArgAt (FuncAttr.findInlineIfConstr lfunc.attr) ||
          (FuncAttr.hasInlineIfAllCanonical lfunc.attr && args.all (isCanonicalValue F))) then
          -- Inline a function only if it has a body.
          let body := lfunc.body.get (by simp_all)
          -- Apply type substitution to instantiate polymorphic type variables.
          match LFunc.computeTypeSubst lfunc op_expr args with
          | some tySubst =>
            let body := body.applySubst tySubst
            let input_map := lfunc.inputs.keys.zip args
            let new_e := substFvarsLifting body input_map
            combineEvalResValueFlag argsAllFull (eval n' F env new_e)
          | none => (e, .nonvalue) -- cannot happen in well-typed terms
        else
          let new_e := @mkApp TBase.mono e.metadata op_expr args
          if -- Case 1: All arguments in the function call are concrete.
            -- We can, provided a denotation function, evaluate this function
            -- call.
            args.all (isCanonicalValue F) ||
            -- Case 2: Some functions (e.g. Eliminators) only require the designated
            -- arg to be a constructor
            constrArgAt (FuncAttr.findEvalIfConstr lfunc.attr) ||
            -- Case 3: Some functions (e.g. regex) only require the designated
            -- arg to be a canonical value (e.g. a constant string)
            canonicalArgAt (FuncAttr.findEvalIfCanonical lfunc.attr) then
            match lfunc.concreteEval with
            | none =>
              -- No concrete evaluation available. The rebuilt call can still
              -- be a value: constructor applications (and partial
              -- applications) of canonical arguments are canonical (e.g.
              -- `Cons (1+1) nil` rebuilds to the canonical `Cons 2 nil`).
              -- Canonicity alone decides value-hood; `argsAllFull` tempers
              -- the every-step-fully-reduced bit as everywhere else.
              combineEvalResValueFlag argsAllFull
                (new_e, if isCanonicalValue F new_e then .value true else .nonvalue)
            | some ceval =>
              match ceval new_e.metadata args with
              | .some e' =>
                combineEvalResValueFlag argsAllFull (eval n' F env e')
              | .none => (new_e, .nonvalue)
          else
            -- At least one argument in the function call is symbolic.
            (new_e, .nonvalue)
      | none =>
        -- Not a call of a factory function - go through evalCore
        evalCore n' F env e

def evalCore (n' : Nat) (F : @Factory TBase) (env : Env TBase) (e : LExpr TBase.mono)
    : LExpr TBase.mono × EvalResult :=
  match e with
  | .const _ _  => (e, .value true)
  | .op _ _ _     => (e, .nonvalue)
  | .bvar _ _     => (e, .nonvalue)
  | .fvar _ x _  =>
    -- Note: closed .abs terms are canonical values; we'll be here if .abs
    -- contains free variables.
    match env x with
    | some v => (v, if isCanonicalValue F v then .value true else .nonvalue)
    | none => (e, .nonvalue)
  | .abs _ _ _ _   =>
    let e' := LExpr.substFvarsFromEnv env e
    (e', if isCanonicalValue F e' then .value true else .nonvalue)
  | .quant _ _ _ _ _ _ =>
    let e' := LExpr.substFvarsFromEnv env e
    (e', if isCanonicalValue F e' then .value true else .nonvalue)
  | .app _ e1 e2 => evalApp n' F env e e1 e2
  | .eq m e1 e2 => evalEq n' F env m e1 e2
  | .ite m c t f => evalIte n' F env m c t f

-- Note: this evaluation is eager -- both branches are fully evaluated even when
-- the condition is not resolved to true/false. This was originally lazy (only
-- substituting free variables via `substFvarsFromEnv`), but we switched to
-- eager evaluation to support recursive functions, where the branches may
-- contain recursive calls that need to be unfolded. If we ever need a lazy mode
-- again, we should add a flag.
def evalIte (n' : Nat) (F : @Factory TBase) (env : Env TBase) (m: TBase.Metadata)
    (c t f : LExpr TBase.mono) : LExpr TBase.mono × EvalResult :=
  let cRes := eval n' F env c
  let c' := cRes.fst
  match c' with
  | .true _ =>
    let (e_out, res_out) := eval n' F env t
    (e_out, res_out.combineValueFlag cRes.snd.isValueTrue)
  | .false _ =>
    let (e_out, res_out) := eval n' F env f
    (e_out, res_out.combineValueFlag cRes.snd.isValueTrue)
  | _ =>
    let t' := (eval n' F env t).fst
    let f' := (eval n' F env f).fst
    (.ite m c' t' f', .nonvalue)

def evalEq (n' : Nat) (F : @Factory TBase) (env : Env TBase) (m: TBase.Metadata)
    (e1 e2 : LExpr TBase.mono) : LExpr TBase.mono × EvalResult :=
  open LTy.Syntax in
  let r1 := eval n' F env e1
  let r2 := eval n' F env e2
  let e1' := r1.fst
  let e2' := r2.fst
  match eql F e1' e2' with
  | some b => (.const m (.boolConst b),
      .value (r1.snd.isValueTrue && r2.snd.isValueTrue))
  | none => (.eq m e1' e2', .nonvalue)

def evalApp (n' : Nat) (F : @Factory TBase) (env : Env TBase) (e e1 e2 : LExpr TBase.mono)
    : LExpr TBase.mono × EvalResult :=
  let r1 := eval n' F env e1
  let r2 := eval n' F env e2
  let e1' := r1.fst
  let e2' := r2.fst
  let subsFull := r1.snd.isValueTrue && r2.snd.isValueTrue
  match e1' with
  | .abs mAbs _ _ e1' =>
    let e' := subst (fun metaReplacementVar =>
      let newMeta := mergeMetadataForSubst mAbs e2'.metadata metaReplacementVar
      replaceMetadata1 newMeta e2') e1'
    if eqModuloMeta e e' then (e, .nonvalue)
    else
      let (e_out, res_out) := eval n' F env e'
      (e_out, res_out.combineValueFlag subsFull)
  | _e =>
    -- Re-evaluate when subexpressions changed (e.g. fvar resolved to .op),
    -- so that `callOfLFunc` in `eval` can recognise the rebuilt expression
    -- as a factory function call.  When nothing changed, `eqModuloMeta`
    -- short-circuits and we return immediately.
    let e' := .app e.metadata e1' e2'
    if eqModuloMeta e e' then (e, .nonvalue)
    else
      let (e_out, res_out) := eval n' F env e'
      (e_out, res_out.combineValueFlag subsFull)
end

instance : Traceable EvalProvenance Unit where
  combine _ := ()

def evalWithLState (n : Nat) (σ : LState TBase) (e : LExpr TBase.mono)
    : LExpr TBase.mono × EvalResult :=
  eval n σ.config.factory (Scopes.toEnv σ.state) e

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

Currently delegates to `LExpr.eval` with the fuel and state from `LState`.
If the result contains a stuck redex (a fully-applied function that should
have reduced but didn't), returns an error.
-/
def run (σ : LState TBase) (e : (LExpr TBase.mono)) : Except String (LExpr TBase.mono) :=
  let result := evalWithLState σ.config.fuel σ e
  match result.snd with
  | .value _ => .ok result.fst
  | .outOfFuel => .error "out of fuel"
  | .nonvalue =>
    match findStuckRedex σ.config.factory result.fst with
    | some _ => .error "expression contains stuck redex"
    | none => .ok result.fst

/-- Fully evaluate an expression `e` using `eval` with a given starting `fuel`,
    incrementally increasing the fuel until the result becomes a
    fully-reduced `.value true`.

    Thanks to `partial_fixpoint`, this function is `.none` when no amount of fuel
    ever yields a `.value true`. -/
def evalFullyAux (F : @Factory TBase) (env : Env TBase) (e : LExpr TBase.mono)
    (fuel : Nat) : Option (LExpr TBase.mono) :=
  let (e', res) := eval fuel F env e
  match res with
  | .value true => some e'
  | .value false => evalFullyAux F env e (fuel + 1)
  | .nonvalue => evalFullyAux F env e (fuel + 1)
  | .outOfFuel => evalFullyAux F env e (fuel + 1)
partial_fixpoint

/-- Fully evaluate an expression by incrementally increasing the fuel given to
    `eval` (starting from `0`) until the result is a `.value`.  See
    `evalFullyAux` for details. -/
def evalFully (F : @Factory TBase) (env : Env TBase) (e : LExpr TBase.mono)
    : Option (LExpr TBase.mono) :=
  evalFullyAux F env e 0

end LExpr
end -- public section
end Lambda
