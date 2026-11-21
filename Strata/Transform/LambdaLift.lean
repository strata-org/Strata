/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
import Strata.DL.Lambda.LExprType
import Strata.Languages.Core.NameMangling
public import Strata.Util.PtrCache

/-! # Lambda lifting

Core-to-Core transformation that removes every abstraction from the program.
In its output every abstraction has become a first-order function applied to what
it captures, so any back end that
interprets function types and application, but not abstraction, can consume
it. The SMT back end encodes a function type `A -> B` as the array sort
`(Array A B)` and has no term for an abstraction: in a pipeline without this
phase, an obligation that still contains a lambda fails with an encoding error
naming it.

The phase works in two steps on every expression of the program.

1. **Eta expansion.** An operator applied to fewer arguments than it takes
   becomes an abstraction over the missing ones: with `sub : int -> int -> int`
   taking two arguments, `sub(1)` becomes `fun y : int => sub(1, y)`. An operator
   used as a value with no argument, such as `add1` in `T..f(t) == add1`, is
   expanded the same way. A free variable of function type is left as it is,
   applied or not: the encoder applies it with `select` and uses it unapplied as
   its array, or, when that array sort would be indexed by an array, applies it
   as an uninterpreted function and uses it unapplied as an opaque constant.
2. **Lifting.** Each abstraction, innermost first, becomes a fresh function
   `$__lam_N` applied to the values it captures, which are the bound variables
   of enclosing binders and the free variables it mentions, in order of first
   occurrence. The function is declared without a body and carries one axiom,
   `forall k₁ … kₙ, x :: { $__lam_N(k₁, …, kₙ)(x) } $__lam_N(k₁, …, kₙ)(x) == e`,
   where `e` is the body with `x` and the captures bound by the quantifier.
   The same abstraction, up to the names of what it captures, lifts to the same
   function, so two occurrences of one closure are equal.

Every model of the input extends to a model of the output, by interpreting
`$__lam_N(k̄)` as the function the abstraction denotes, which satisfies its axiom.
So a valid output is a valid input, and the phase is sound for proofs. This is
argued, not proved.

From there to the solver, the argument relies on SMT-LIB's array theory. An
`unsat` stands: taking every function as an array satisfies the array axioms,
so a model of the query over all functions is a solver model too, and when the
solver finds none, there is none over all functions either. A `sat` needs
care. The arrays of a solver model may be only some of the functions. Such a
model still fixes every lifted function at every capture: its axiom makes
`$__lam_N(k̄)` the array of `x ↦ e(k̄)`, the function the lambda denotes. A free
variable of function type is existential in the query, so the model gives it an
array, which is a real function, and it needs no marking. What a model with too
few arrays can get wrong is a quantifier over a function type, `forall g : int ->
int :: P(g)`, which may hold over the arrays of the model and fail over all
functions.

So the phase marks every obligation whose query may contain such a quantifier,
with the assumption `assume [Core.spuriousModelsLabel]: true` placed on its path:
before each statement whose expressions quantify over a type that contains a
function type (directly, under a type constructor, through a type synonym or the
fields of a datatype), or apply a function whose body or axioms do, transitively,
lifted functions included; at the start of a body whose contract does; at the
start of every body declared after a program axiom that does; and, for a lemma, in
its metadata (`Core.spuriousModelsField`), which its obligation alone carries. A
binder without a type annotation is marked too. A map type is not a function type
and does not mark: the array theory's arrays already range over every map. The
label starts with `$__`, which is meant for internal use. The back end reads the
marker through `Core.spuriousModelsValidation`, which reports the model of a
marked obligation as unknown and leaves any other obligation's model a
counterexample. A satisfiable query for a marked obligation is thus never reported
as a failure: `spuriousVerdictPgm` in `LambdaHigherOrderTests` pins this, and
`spuriousModelsPgm` there pins which procedures and lemmas are marked. The marking
is tested, not proved.

The lifted functions' names carry the reserved prefix
`Core.NameMangling.liftedLambdaPrefix` and are numbered by the
`CoreTransformState` counter. -/

public section

namespace Core.LambdaLift

open Lambda Imperative

/-- Location of the expressions this phase builds itself. -/
abbrev lambdaLiftLoc : ExpressionMetadata := ExprSourceLoc.synthesized "lambda-lift"

/-! ## Eta expansion -/

/-- `fn` applied to `args`, each application carrying the location paired with
    its argument. -/
def applyAll (fn : Expression.Expr) (args : List (ExpressionMetadata × Expression.Expr)) :
    Expression.Expr :=
  args.foldl (fun f (m, a) => .app m f a) fn

/-- `head`, of type `ty` and taking `arity` arguments, applied to `args`, as an
    abstraction over the arguments it is missing. -/
def etaHead (head : Expression.Expr) (ty : LMonoTy) (arity : Nat)
    (args : List (ExpressionMetadata × Expression.Expr)) : Expression.Expr :=
  let missing := ((LMonoTy.splitArrows arity ty).1).drop args.length
  if args.length < arity && missing.length == arity - args.length then
    let k := missing.length
    let lifted := args.map fun (m, a) => (m, LExpr.liftBVars k a)
    let extra := (List.range k).reverse.map fun i =>
      (lambdaLiftLoc, (.bvar lambdaLiftLoc i : Expression.Expr))
    missing.foldr (fun t body => .abs lambdaLiftLoc "" (some t) body)
      (applyAll head (lifted ++ extra))
  else applyAll head args

mutual
/-- Eta-expand every operator of `e` that is applied to fewer arguments than
    `arity` gives it. -/
def etaExpand (arity : String → Option Nat) (e : Expression.Expr) : Expression.Expr :=
  etaSpine arity e []
termination_by (sizeOf e, 1)

/-- `etaExpand` of `e` applied to the already expanded `args`. -/
def etaSpine (arity : String → Option Nat) (e : Expression.Expr)
    (args : List (ExpressionMetadata × Expression.Expr)) : Expression.Expr :=
  match e with
  | .app m fn arg => etaSpine arity fn ((m, etaExpand arity arg) :: args)
  | .op m o (some ty) =>
    match arity o.name with
    | some n => etaHead (.op m o (some ty)) ty n args
    | none => applyAll e args
  | .abs m n ty body => applyAll (.abs m n ty (etaExpand arity body)) args
  | .quant m k n ty tr body =>
    applyAll (.quant m k n ty (etaExpand arity tr) (etaExpand arity body)) args
  | .ite m c t f =>
    applyAll
      (.ite m (etaExpand arity c) (etaExpand arity t) (etaExpand arity f)) args
  | .eq m a b =>
    applyAll (.eq m (etaExpand arity a) (etaExpand arity b)) args
  | _ => applyAll e args
termination_by (sizeOf e, 0)
end

/-! ## Lifting -/

/-- What an abstraction captures: a bound variable of an enclosing binder, by
    its index outside the abstraction, or a free variable. -/
inductive Capture where
  | bvar (i : Nat)
  | fvar (x : Expression.Ident)
  deriving DecidableEq

/-- The captures of `e` under `depth` binders of its own, in order of first
    occurrence and possibly repeated: its bound variables that escape those
    binders, and its free variables with their types. -/
def captures (depth : Nat) : Expression.Expr → List (Capture × Option LMonoTy)
  | .bvar _ j => if j ≥ depth then [(.bvar (j - depth), none)] else []
  | .fvar _ x ty => [(.fvar x, ty)]
  | .abs _ _ _ b => captures (depth + 1) b
  | .quant _ _ _ _ tr b => captures (depth + 1) tr ++ captures (depth + 1) b
  | .app _ f a => captures depth f ++ captures depth a
  | .ite _ c t f => captures depth c ++ captures depth t ++ captures depth f
  | .eq _ a b => captures depth a ++ captures depth b
  | _ => []

/-- Bind the captures `caps` of `e`, under `depth` binders of its own: the
    capture at position `p` of `n` becomes the bound variable `depth + n - 1 - p`,
    so the first capture is bound by the outermost of `n` quantifiers placed
    around `e`. -/
def bindCaptures (caps : List Capture) (depth : Nat) : Expression.Expr → Expression.Expr
  | .bvar m j =>
    if j < depth then .bvar m j
    else match caps.idxOf? (.bvar (j - depth)) with
      | some p => .bvar m (depth + caps.length - 1 - p)
      | none => .bvar m j
  | .fvar m x ty =>
    match caps.idxOf? (.fvar x) with
    | some p => .bvar m (depth + caps.length - 1 - p)
    | none => .fvar m x ty
  | .abs m n ty b => .abs m n ty (bindCaptures caps (depth + 1) b)
  | .quant m k n ty tr b =>
    .quant m k n ty (bindCaptures caps (depth + 1) tr) (bindCaptures caps (depth + 1) b)
  | .app m f a => .app m (bindCaptures caps depth f) (bindCaptures caps depth a)
  | .ite m c t f =>
    .ite m (bindCaptures caps depth c) (bindCaptures caps depth t) (bindCaptures caps depth f)
  | .eq m a b => .eq m (bindCaptures caps depth a) (bindCaptures caps depth b)
  | e => e

/-- A lifted abstraction: the types of what it captures, the type of its bound
    variable, and its body with the captures bound, which identify it up to the
    names of the captures, together with the function it lifts to. -/
structure Lifted where
  capTys : List LMonoTy
  argTy : LMonoTy
  body : Expression.Expr
  func : Function

/-- The state of the phase: the abstractions lifted so far, newest first. -/
abbrev LiftM := StateT (List Lifted) Transform.CoreTransformM

/-- The function `l` lifts to, with its defining axiom. -/
def liftedFunc (name : Expression.Ident) (capTys : List LMonoTy) (argTy resTy : LMonoTy)
    (body : Expression.Expr) : Function :=
  let n := capTys.length
  let fnTy := LMonoTy.mkArrow' (.arrow argTy resTy) capTys
  let m := lambdaLiftLoc
  let applied := LExpr.mkApp m (.op m name (some fnTy))
    ((List.range n).reverse.map fun i => (.bvar m (i + 1) : Expression.Expr))
  let lhs : Expression.Expr := .app m applied (.bvar m 0)
  let inner : Expression.Expr := .quant m .all "x" (some argTy) lhs (.eq m lhs body)
  let ax := capTys.foldr (fun t e => .quant m .all "" (some t) (LExpr.noTrigger m) e) inner
  { name, inputs := (capTys.zipIdx).map fun (t, i) => (⟨s!"k{i}", ()⟩, t),
    output := .arrow argTy resTy, axioms := [ax] }

/-- Replace the abstraction `fun x : argTy => body`, whose body is already free
    of abstractions and whose enclosing binders have the types `ctx`, by its
    lifted function applied to its captures, located at `m`, the abstraction's
    location. -/
def liftAbs (m : ExpressionMetadata) (ctx : List LMonoTy) (argTy : LMonoTy)
    (body : Expression.Expr) :
    LiftM Expression.Expr := do
  let all := captures 1 body
  let caps := all.foldl (fun acc (c, _) => if acc.contains c then acc else acc ++ [c]) []
  let capTys ← caps.mapM fun c => match c with
    | .bvar i => match ctx[i]? with
      | some t => pure t
      | none => throw (Strata.Message.fromFormat
          f!"❌ Lambda lifting: bound variable {i} is out of scope.")
    | .fvar x => match (all.find? (·.1 == c)).bind (·.2) with
      | some t => pure t
      | none => throw (Strata.Message.fromFormat
          f!"❌ Lambda lifting: free variable {x.name} has no type annotation.")
  let some resTy := LExpr.typeCheck (T := CoreLParams) (argTy :: ctx) body
    | throw (Strata.Message.fromFormat
        f!"❌ Lambda lifting: cannot compute the type of {body}.")
  let bound := bindCaptures caps 1 body
  let lifted ← get
  let same (l : Lifted) :=
    l.capTys == capTys && l.argTy == argTy && LExpr.eqModuloMeta l.body bound
  let func ← match lifted.find? same with
    | some l => pure l.func
    | none => do
      let fresh := CoreGenState.gen ⟨Core.NameMangling.liftedLambdaPrefix, ()⟩
      let name ←
        (Transform.liftCoreGenM fresh : StateM Transform.CoreTransformState Expression.Ident)
      let func := liftedFunc name capTys argTy resTy bound
      set ({ capTys, argTy, body := bound, func } :: lifted)
      pure func
  let fnTy := LMonoTy.mkArrow' (.arrow argTy resTy) capTys
  let args := caps.map fun c => match c with
    | .bvar i => (.bvar m i : Expression.Expr)
    | .fvar x => .fvar m x (capTys[caps.idxOf c]?)
  return LExpr.mkApp m (.op m func.name (some fnTy)) args

/-- Lift every abstraction of `e`, innermost first, where the binders enclosing
    `e` have the types `ctx`. -/
def liftExpr (ctx : List LMonoTy) : Expression.Expr → LiftM Expression.Expr
  | .abs m _ (some ty) body => do liftAbs m ctx ty (← liftExpr (ty :: ctx) body)
  | .abs _ _ none _ => throw (Strata.Message.fromFormat
      f!"❌ Lambda lifting: an abstraction has no type annotation.")
  | .quant m k n (some ty) tr body => do
    return .quant m k n (some ty) (← liftExpr (ty :: ctx) tr) (← liftExpr (ty :: ctx) body)
  | .quant _ _ _ none _ _ => throw (Strata.Message.fromFormat
      f!"❌ Lambda lifting: a quantifier has no type annotation.")
  | .app m f a => do return .app m (← liftExpr ctx f) (← liftExpr ctx a)
  | .ite m c t f => do return .ite m (← liftExpr ctx c) (← liftExpr ctx t) (← liftExpr ctx f)
  | .eq m a b => do return .eq m (← liftExpr ctx a) (← liftExpr ctx b)
  | e => pure e

/-! ## Which obligations may have spurious models -/

/-- Does `ty` contain a function type, directly, under a type constructor, or
    through a datatype or type synonym among `dts`, the names of those known to? -/
def tyHasFunctions (dts : Std.HashSet String) (ty : LMonoTy) : Bool :=
  ty.containsArrow || (Lambda.getTypeRefs ty).any dts.contains

/-- The datatypes and type synonyms of `p` that contain a function type,
    through their fields or definitions, transitively. -/
def typesWithFunctions (p : Program) : Std.HashSet String := Id.run do
  -- Each named type with the types it is made of.
  let named : List (String × List LMonoTy) := p.decls.flatMap fun
    | .type (.data block) _ =>
      block.map fun d => (d.name, d.constrs.flatMap fun c => c.args.map (·.2))
    | .type (.syn ts) _ => [(ts.name, [ts.type])]
    | _ => []
  let mut found : Std.HashSet String := {}
  -- Each round adds at least one type or stops, so `named.length + 1` rounds suffice.
  for _ in [0:named.length + 1] do
    let next := named.filter fun (n, tys) => !found.contains n && tys.any (tyHasFunctions found)
    if next.isEmpty then break
    found := next.foldl (fun acc (n, _) => acc.insert n) found
  return found

/-- Does a quantifier binding `ty` mark its obligation? An unannotated binder, which
    `typeAnnotated` rules out, does. -/
def binderMarks (dts : Std.HashSet String) (ty : Option LMonoTy) : Bool :=
  (ty.map (tyHasFunctions dts)).getD true

/-- Does `e` quantify over a type that contains a function type? It visits each
    physically distinct subterm once. -/
def quantifiesOverFunctions (dts : Std.HashSet String) (e : Expression.Expr) : Bool :=
  (Lambda.LExpr.Traversal.visitDFSPtrCached .preorder
    (fun (e : Expression.Expr) => match e with
      | .quant _ _ _ ty _ _ => (⟨binderMarks dts ty⟩ : AnyFlag)
      | _ => ⟨false⟩)
    e).flag

/-- Does `e` quantify over a type containing a function type, among the named types
    `dts` that do, or apply a function among `funcs`? -/
def marks (dts funcs : Std.HashSet String) : Expression.Expr → Bool
  | .quant _ _ _ ty tr b =>
    binderMarks dts ty || marks dts funcs tr || marks dts funcs b
  | .abs _ _ _ b => marks dts funcs b
  | .app _ f a => marks dts funcs f || marks dts funcs a
  | .ite _ c t f => marks dts funcs c || marks dts funcs t || marks dts funcs f
  | .eq _ a b => marks dts funcs a || marks dts funcs b
  | .op _ o _ => funcs.contains o.name
  | _ => false

open Strata.PtrCache in
/-- `marks`, computed once per physically distinct subterm. -/
def marksPtrCache (dts funcs : Std.HashSet String) :
    (e : Expression.Expr) → PtrCacheM (marks dts funcs) e
  | .quant m k n ty tr b => do
    let rt ← evalPtrCache tr (marksPtrCache dts funcs tr)
    let rb ← evalPtrCache b (marksPtrCache dts funcs b)
    pure ⟨binderMarks dts ty || rt.output || rb.output,
      by simp only [marks, rt.h, rb.h]⟩
  | .abs _ _ _ b => do
    let rb ← evalPtrCache b (marksPtrCache dts funcs b)
    pure ⟨rb.output, by simp only [marks, rb.h]⟩
  | .app _ f a => do
    let rf ← evalPtrCache f (marksPtrCache dts funcs f)
    let ra ← evalPtrCache a (marksPtrCache dts funcs a)
    pure ⟨rf.output || ra.output, by simp only [marks, rf.h, ra.h]⟩
  | .ite _ c t f => do
    let rc ← evalPtrCache c (marksPtrCache dts funcs c)
    let rt ← evalPtrCache t (marksPtrCache dts funcs t)
    let rf ← evalPtrCache f (marksPtrCache dts funcs f)
    pure ⟨rc.output || rt.output || rf.output, by simp only [marks, rc.h, rt.h, rf.h]⟩
  | .eq _ a b => do
    let ra ← evalPtrCache a (marksPtrCache dts funcs a)
    let rb ← evalPtrCache b (marksPtrCache dts funcs b)
    pure ⟨ra.output || rb.output, by simp only [marks, ra.h, rb.h]⟩
  | .op m o ty => pure ⟨marks dts funcs (.op m o ty), rfl⟩
  | .const m c => pure ⟨marks dts funcs (.const m c), rfl⟩
  | .bvar m i => pure ⟨marks dts funcs (.bvar m i), rfl⟩
  | .fvar m x ty => pure ⟨marks dts funcs (.fvar m x ty), rfl⟩

mutual
/-- `s` with `marker` placed just before every statement of it, at any depth, whose
    own expressions satisfy `marks`: a command, or the guard, measure or
    invariants of a conditional or loop. An obligation then carries the marker
    exactly when a statement on its path does, so other paths of the same body
    are not marked. -/
def markStmt (marks : Expression.Expr → Bool) (marker : Statement) (s : Statement) :
    Statements :=
  match s with
  | .cmd c =>
    if (Statements.allExprs [.cmd c]).any marks then [marker, s] else [s]
  | .block l b md => [.block l (markStmts marks marker b) md]
  | .ite g t e md =>
    let s' := .ite g (markStmts marks marker t) (markStmts marks marker e) md
    let guardMarks := match g with | .det c => marks c | .nondet => false
    if guardMarks then [marker, s'] else [s']
  | .loop g m inv b md =>
    let s' := .loop g m inv (markStmts marks marker b) md
    let ownMarks := (match g with | .det c => marks c | .nondet => false) ||
      (m.map marks).getD false || inv.any (fun (_, e) => marks e)
    if ownMarks then [marker, s'] else [s']
  | .exit _ _ | .typeDecl _ _ => [s]

/-- `markStmt` on each statement of `ss`. -/
def markStmts (marks : Expression.Expr → Bool) (marker : Statement) (ss : Statements) :
    Statements :=
  match ss with
  | [] => []
  | s :: rest => markStmt marks marker s ++ markStmts marks marker rest
end

/-- `p` with every obligation whose models may be spurious marked, by the policy of the
    module header, and whether it marked anything. -/
def markSpuriousModels (p : Program) : Program × Bool :=
  let dts := typesWithFunctions p
  let quantifies := quantifiesOverFunctions dts
  let allFuncs := p.decls.flatMap fun
    | .func f _ => [f]
    | .recFuncBlock fs _ => fs
    | _ => []
  -- The functions whose body or axioms quantify over a function type, or apply
  -- such a function, transitively: the encoder emits the definitions and axioms
  -- of every function an obligation reaches.
  -- Each function's body and axioms are walked once: whether they quantify over a
  -- function type, and which operators they apply, which gives each operator its callers.
  let read (f : Function) : List Expression.Expr := f.body.toList ++ f.axioms
  let own := allFuncs.filter fun f => (read f).any quantifies
  let callers : Std.HashMap String (List String) := allFuncs.foldl (fun m f =>
    (read f).foldl (fun m e => (Expression.opNames e).fold (init := m) fun m o =>
      m.insert o (f.name.name :: m.getD o [])) m) {}
  let funcs : Std.HashSet String := Id.run do
    let mut found : Std.HashSet String := own.foldl (fun acc f => acc.insert f.name.name) {}
    let mut frontier := own.map (·.name.name)
    -- Each round adds at least one function or stops.
    for _ in [0:allFuncs.length + 1] do
      let mut next : List String := []
      for n in frontier do
        for c in callers.getD n [] do
          if !found.contains c then
            found := found.insert c
            next := c :: next
      if next.isEmpty then break
      frontier := next
    return found
  -- Expressions after symbolic evaluation share subterms, so this test visits each
  -- distinct subterm of one expression once (`marksPtrCache`). A subterm shared by
  -- several statements is walked once per statement.
  let exprMarks (e : Expression.Expr) : Bool :=
    ((marksPtrCache dts funcs e).run' Strata.PtrCache.PtrCache.empty).output
  -- A program axiom is a path condition of every obligation of the declarations after
  -- it, so one that quantifies over a function type, or applies a function whose body or
  -- axioms do, marks all of theirs. `globally` holds of the declarations after the first
  -- such axiom.
  let firstMarkingAxiom : Option Nat := p.decls.findIdx? fun
    | .ax a _ => exprMarks a.e
    | _ => false
  -- A lemma is an obligation of its own, with no statement to mark: one that marks
  -- carries `Core.spuriousModelsField` in its metadata, which its obligation alone keeps.
  let markLemma (globally : Bool) (d : Decl) : Option Decl := match d with
    | .lemma l md =>
      if globally || exprMarks l.e then
        some (.lemma l (md.pushElem Core.spuriousModelsField (.switch true)))
      else none
    | _ => none
  let markProc (globally : Bool) (q : Procedure) (md : Imperative.MetaData Expression) :
      Option Decl :=
    let stmtMarker := Core.spuriousModelsMarker (LExpr.true lambdaLiftLoc)
    match q.body with
    | .structured ss isOpaque =>
      if globally || (Decl.proc q md).ownExprs.any exprMarks then
        some (.proc { q with body := .structured (stmtMarker :: ss) isOpaque } md)
      -- `markStmts` places a marker exactly when some statement's expressions mark.
      else if (Statements.allExprs ss).any exprMarks then
        some (.proc { q with body := .structured (markStmts exprMarks stmtMarker ss) isOpaque } md)
      else none
    -- Unreachable: the phase requires `noCFGBodies`, and `run` rejects a CFG body
    -- before marking.
    | .cfg _ _ => none
    -- An abstract body has no statement, so nothing to mark.
    | .abstract .. => none
  let procs := p.decls.mapIdx fun i d =>
    let globally := match firstMarkingAxiom with
      | some k => decide (k < i)
      | none => false
    match d with
    | .proc q md => match markProc globally q md with
      | some d' => (d', true)
      | none => (d, false)
    | d => match markLemma globally d with
      | some d' => (d', true)
      | none => (d, false)
  ({ decls := procs.map (·.1) }, procs.any (·.2))

/-! ## Which expressions need the phase

Expressions after symbolic evaluation share subterms, so a walk of the tree can
visit a node many times over. `needsLift` decides, visiting each distinct node once,
whether `transformExpr` can change an expression; the phase leaves every declaration
whose expressions all answer no as it is. -/

/-- What `needsLift` computes of an expression: whether it contains an abstraction
    or an operand that lacks arguments (`needs`), and how many arguments its own head
    still lacks (`missing`). -/
structure LiftSummary where
  needs : Bool
  missing : Nat

/-- The `LiftSummary` of `e`, where `arity` gives the arguments an operator takes. -/
def liftSummary (arity : String → Option Nat) : Expression.Expr → LiftSummary
  | .abs .. => ⟨true, 0⟩
  | .op _ o (some _) => ⟨false, (arity o.name).getD 0⟩
  -- A free variable needs no expansion: the encoder applies one, however many arguments
  -- it is given, with `select`, and uses one given none as its array.
  | .fvar _ _ (some _) => ⟨false, 0⟩
  | .app _ f a =>
    let sf := liftSummary arity f
    let sa := liftSummary arity a
    ⟨sf.needs || sa.needs || sa.missing > 0, sf.missing - 1⟩
  | .ite _ c t f =>
    let sc := liftSummary arity c
    let st := liftSummary arity t
    let sf := liftSummary arity f
    ⟨sc.needs || st.needs || sf.needs || sc.missing > 0 || st.missing > 0 || sf.missing > 0, 0⟩
  | .eq _ a b =>
    let sa := liftSummary arity a
    let sb := liftSummary arity b
    ⟨sa.needs || sb.needs || sa.missing > 0 || sb.missing > 0, 0⟩
  | .quant _ _ _ _ tr b =>
    let st := liftSummary arity tr
    let sb := liftSummary arity b
    ⟨st.needs || sb.needs || st.missing > 0 || sb.missing > 0, 0⟩
  | _ => ⟨false, 0⟩

open Strata.PtrCache in
/-- `liftSummary`, computed once per physically distinct subterm. -/
def liftSummaryPtrCache (arity : String → Option Nat) :
    (e : Expression.Expr) → PtrCacheM (liftSummary arity) e
  | .abs m n ty b => pure ⟨⟨true, 0⟩, by simp only [liftSummary]⟩
  | .op m o ty => pure ⟨liftSummary arity (.op m o ty), rfl⟩
  | .fvar m x ty => pure ⟨liftSummary arity (.fvar m x ty), rfl⟩
  | .const m c => pure ⟨liftSummary arity (.const m c), rfl⟩
  | .bvar m i => pure ⟨liftSummary arity (.bvar m i), rfl⟩
  | .app _ f a => do
    let rf ← evalPtrCache f (liftSummaryPtrCache arity f)
    let ra ← evalPtrCache a (liftSummaryPtrCache arity a)
    pure ⟨⟨rf.output.needs || ra.output.needs || ra.output.missing > 0, rf.output.missing - 1⟩,
      by simp only [liftSummary, rf.h, ra.h]⟩
  | .ite _ c t f => do
    let rc ← evalPtrCache c (liftSummaryPtrCache arity c)
    let rt ← evalPtrCache t (liftSummaryPtrCache arity t)
    let rf ← evalPtrCache f (liftSummaryPtrCache arity f)
    pure ⟨⟨rc.output.needs || rt.output.needs || rf.output.needs || rc.output.missing > 0 ||
        rt.output.missing > 0 || rf.output.missing > 0, 0⟩,
      by simp only [liftSummary, rc.h, rt.h, rf.h]⟩
  | .eq _ a b => do
    let ra ← evalPtrCache a (liftSummaryPtrCache arity a)
    let rb ← evalPtrCache b (liftSummaryPtrCache arity b)
    pure ⟨⟨ra.output.needs || rb.output.needs || ra.output.missing > 0 || rb.output.missing > 0, 0⟩,
      by simp only [liftSummary, ra.h, rb.h]⟩
  | .quant _ _ _ _ tr b => do
    let rt ← evalPtrCache tr (liftSummaryPtrCache arity tr)
    let rb ← evalPtrCache b (liftSummaryPtrCache arity b)
    pure ⟨⟨rt.output.needs || rb.output.needs || rt.output.missing > 0 || rb.output.missing > 0, 0⟩,
      by simp only [liftSummary, rt.h, rb.h]⟩

/-- Can `transformExpr arity` change `e`? Only if `e` contains an abstraction or an
    operator or function-typed free variable applied to fewer arguments than it takes:
    eta expansion changes nothing else, and lifting only removes abstractions. The
    answer errs only towards yes, which costs a walk. A wrong no would be safe too: the
    abstraction left in reaches the SMT encoder, which rejects the obligation with an
    error naming it, never a verdict. -/
def needsLift (arity : String → Option Nat) (e : Expression.Expr) : Bool :=
  let s := ((liftSummaryPtrCache arity e).run' Strata.PtrCache.PtrCache.empty).output
  s.needs || s.missing > 0

/-! ## The program -/

/-- Eta-expand the partially applied operators of one closed expression and lift it. A
    function-typed free variable is left as it is, applied or not: the encoder applies it
    with `select` and uses it unapplied as its array (or, when that array sort would be
    indexed by an array, as an uninterpreted function and an opaque constant), so
    expanding it would only add a lifted function whose axiom quantifies over a function
    type. -/
def transformExpr (arity : String → Option Nat) (e : Expression.Expr) :
    LiftM Expression.Expr :=
  liftExpr [] (etaExpand arity e)

/-- Transform every expression of a function. -/
def transformFunc (arity : String → Option Nat) (f : Function) : LiftM Function := do
  return { f with
    body := ← f.body.mapM (transformExpr arity)
    axioms := ← f.axioms.mapM (transformExpr arity)
    preconditions := ← f.preconditions.mapM fun pc => do
      return { pc with expr := ← transformExpr arity pc.expr }
    measure := ← f.measure.mapM (transformExpr arity) }

/-- Transform every expression of a declaration. -/
def transformDecl (arity : String → Option Nat) : Decl → LiftM Decl
  | .proc q md => do
    let spec := { q.spec with
      preconditions := ← q.spec.preconditions.mapM fun (n, c) => do
        return (n, { c with expr := ← transformExpr arity c.expr })
      postconditions := ← q.spec.postconditions.mapM fun (n, c) => do
        return (n, { c with expr := ← transformExpr arity c.expr }) }
    let body ← match q.body with
      | .structured ss isOpaque =>
        pure (.structured (← Statements.mapExprsM (transformExpr arity) ss) isOpaque)
      | b@(.abstract ..) => pure b
      | .cfg _ _ => throw (Strata.Message.fromFormat
          f!"❌ Lambda lifting: procedure {q.header.name.name} has a CFG body.")
    return .proc { q with spec, body } md
  | .func f md => do return .func (← transformFunc arity f) md
  | .recFuncBlock fs md => do return .recFuncBlock (← fs.mapM (transformFunc arity)) md
  | .ax a md => do return .ax { a with e := ← transformExpr arity a.e } md
  | .lemma l md => do return .lemma { l with e := ← transformExpr arity l.e } md
  | .distinct n es md => do return .distinct n (← es.mapM (transformExpr arity)) md
  | d => pure d

/-- Lift every abstraction of `p`. The functions lifted from a declaration are
    declared just before it, in the order they were lifted, so each precedes
    the functions lifted after it that use it. -/
def run (p : Program) : Transform.CoreTransformM (Bool × Program) := do
  -- The table is built once here: a lookup closing over it reads it, where one
  -- built inside the closure would rebuild it on every call.
  let arities := p.declArities
  let F ← Transform.getFactory
  let arity := Program.arityIn arities F
  let mut decls : Array Decl := #[]
  let mut lifted : List Lifted := []
  let mut changed := false
  for d in p.decls do
    -- A declaration whose expressions `transformExpr` cannot change is kept as it is,
    -- without a walk that would rebuild, and compare, its shared subterms.
    unless (Decl.ownExprs d ++ Statements.allExprs d.statements).any (needsLift arity) do
      decls := decls.push d
      continue
    let before := lifted.length
    let (d', lifted') ← (transformDecl arity d).run lifted
    let fresh := (lifted'.take (lifted'.length - before)).reverse
    decls := decls ++ (fresh.map fun l => Decl.func l.func .empty).toArray
    decls := decls.push d'
    changed := true
    lifted := lifted'
  -- A program with nothing to lift or mark is returned as it is, the same object.
  let p' : Program := if changed then { decls := decls.toList } else p
  let (marked, markedAny) := markSpuriousModels p'
  return (changed || markedAny, if markedAny then marked else p')

/-- Whether an expression the back end reads of `p` holds a lambda or a partial
    application to eta-expand, with `arity` the number of arguments of each operator. A
    program none of whose expressions needs it is answered with one walk, without
    computing the expressions the back end reads. -/
def liveNeedsLift (arity : String → Option Nat) (p : Program) : Bool :=
  !p.allExprs (fun e => !needsLift arity e) && p.liveExprs.any (needsLift arity)

/-- Whether `run` has work to do on what the back end reads of `p`, with `arity` the
    number of arguments of each operator: `liveNeedsLift`, or an obligation's models may
    be spurious and need the marker. When this is false, `p` satisfies `noLambdas`. -/
def needsRun (arity : String → Option Nat) (p : Program) : Bool :=
  liveNeedsLift arity p || (markSpuriousModels p).2

/-- `run`, on a program it has work to do on (`needsRun`); any other program is returned
    unchanged. When only marking is needed, it marks without walking the program to
    lift. -/
def runIfNeeded (p : Program) : Transform.CoreTransformM (Bool × Program) := do
  let F ← Transform.getFactory
  if liveNeedsLift (Program.arityIn p.declArities F) p then run p
  else
    -- Nothing the back end reads needs lifting, so `run` would only mark: mark here,
    -- once.
    let marked := markSpuriousModels p
    pure (marked.2, if marked.2 then marked.1 else p)

end Core.LambdaLift

/-- Lambda-lifting pipeline phase: removes every abstraction, so the back end
    sees only first-order terms. It needs type annotations to type the lifted
    functions, monomorphic functions and procedures so that each lifted function has
    one signature with no type variable, and no redex, which `betaReduce` contracts
    instead.

    It rewrites expressions in place, adds function declarations without
    preconditions or type parameters, and adds one kind of statement, the marker
    `assume [Core.spuriousModelsLabel]: true`, placed before a statement or at the
    start of a body and never after the last one. An `assume` is in obligation and
    tree form; it declares, assigns and exits nothing; it is not a call, loop or
    conditional; and an arm it is added to keeps its checks. So the phase preserves
    every fact about statements, contracts and polymorphism. It preserves
    `noBetaRedexes`: what it builds applies an operator or a free variable, never
    an abstraction. It preserves `typeAnnotated`: each capture becomes a parameter
    typed by the binder that bound it or by its own annotation, and the run fails
    when a capture has neither. These claims are not proved; `LambdaHigherOrderTests`
    checks each one that has an executable check on every program of that file. -/
def Core.lambdaLiftPipelinePhase : Core.PipelinePhase where
  transform := Core.LambdaLift.run
  phase.name := "lambdaLift"
  phase.getValidation := Core.spuriousModelsValidation
  requires := factSet![.noCFGBodies, .noBetaRedexes, .noPolymorphicProcedures,
                       .noPolymorphicFunctions, .typeAnnotated]
  establishes := factSet![.noLambdas]
  preserves := factSet![.noCFGBodies, .noCalls, .noLoops, .noLoopInvariants,
                       .noLoopMeasures, .staticSingleAssignment, .noBetaRedexes,
                       .noPrecondsFromFuncs, .noNondetGuards, .hasObligationForm,
                       .noProcedureContracts, .noPolymorphicProcedures,
                       .noPolymorphicFunctions, .typeAnnotated, .noInits, .treeForm,
                       .exitsCovered, .armsHaveObligations]

/-- `lambdaLift`, run only on a program it has work to do on: a lambda or a partial
    application the back end would read, or an obligation whose models may be spurious
    (`LambdaLift.needsRun`); every other program is returned unchanged. A pipeline that
    does not lift lambdas can run it before the back end, so that a program it would
    otherwise refuse is lifted, while every other program keeps the output it has without
    the phase. Its contract is `lambdaLift`'s: on a program that already satisfies
    `noLambdas` it is the identity, which establishes and preserves the same facts. -/
def Core.lambdaLiftIfNeededPipelinePhase : Core.PipelinePhase :=
  { Core.lambdaLiftPipelinePhase with
    transform := Core.LambdaLift.runIfNeeded
    phase := { Core.lambdaLiftPipelinePhase.phase with name := "lambdaLiftIfNeeded" }
    establishes_ok := by unproved_contract
    preserves_ok := by unproved_contract }

end -- public section
