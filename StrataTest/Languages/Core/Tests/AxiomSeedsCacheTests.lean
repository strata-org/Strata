/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.Verifier

meta section

/-! # The cached axiom-relevance seeds and model variables against their specifications

`preprocessObligation` and `collectModelVars` read each path expression's function names
and free variables from an `ExprFactsCache` shared across obligations. These tests pin the
cached code against its specification, written here as the plain `List` definitions it
replaces:

- under the precise mode, the seeds are `List.uniq` of the goal's function names followed
  by those of every non-axiom expression of the path condition;
- under the directed mode, the same concatenation, not deduplicated;
- the reported variables are `ProofObligation.getVars`, kept when the goal or a non-managed
  entry reaches them through the managed definitions, `Core.SMT.isReportedName` names them
  and their type is not a function type.

The path conditions repeat names across expressions, across path conditions and with the
goal, include an axiom whose names must not seed, a managed definition, a `distinct` entry
and a nondeterministic declaration. Each check runs on a fresh cache and on one already
filled by another obligation over the same expressions, so cache hits are covered too. -/

namespace Core.AxiomSeedsCacheTests

open Lambda Imperative
open LExpr.SyntaxMono LTy.Syntax Core.Syntax

private def opName (op : CoreIdent) : String := Core.NameMangling.demangledBaseName op.toPretty

/-- Specification of the precise seeds and of `antecedentOpsCached`: the function names of
    the path condition's expressions, in order, skipping the assumptions labelled in
    `axiomSet`. -/
private def antecedentSpec (pcs : PathConditions Expression) (axiomSet : Std.HashSet String) :
    List String :=
  pcs.flatten.flatMap fun
    | .assumption label e => if axiomSet.contains label then [] else (LExpr.getOps e).map opName
    | .varDecl _ _ (.det e) => (LExpr.getOps e).map opName
    | .varDecl _ _ .nondet => []
    | .distinct _ es => es.flatMap fun e => (LExpr.getOps e).map opName

/-- Specification of `collectModelVars`: the variables of `ProofObligation.getVars` that the
    goal and the non-managed entries reach through the managed definitions, that
    `Core.SMT.isReportedName` names, and whose type is not a function type. The closure is iterated once per definition. -/
private def modelVarsSpec (ob : ProofObligation Expression) (defs : List VarDefinition)
    (decls : List VarDeclaration) : List (IdentT LMonoTy Unit) :=
  let managed := defs.map (·.name) ++ decls.map (·.name)
  let names := fun (e : Expression.Expr) => (LExpr.freeVars e).map (·.1.name)
  let definitions := ob.assumptions.flatten.filterMap fun
    | .varDecl n _ (.det rhs) => if n.name ∈ managed then some (n.name, rhs) else none
    | _ => none
  let roots := names ob.obligation ++ ob.assumptions.flatten.flatMap fun
    | .assumption _ e => names e
    | .distinct _ es => es.flatMap names
    | .varDecl n _ (.det rhs) => if n.name ∈ managed then [] else names rhs
    | .varDecl _ _ .nondet => []
  let reached := (List.range (definitions.length + 1)).foldl (fun reached _ =>
    reached ++ definitions.flatMap fun (n, rhs) => if n ∈ reached then names rhs else [])
    roots
  let defined := Std.HashSet.ofList (defs.map (·.name))
  (ProofObligation.getVars ob).filter fun (v, ty) =>
    v.name ∈ reached && Core.SMT.isReportedName defined v.name &&
      (ty.bind LMonoTy.isArrow).isNone

/-- Shared path conditions: `f`, `g` and `h` repeat across expressions and path conditions,
    `ax` is an axiom whose `k` must not seed, `d` is a managed definition. -/
private def pcs : PathConditions Expression :=
  [[.assumption "h1" eb[((~f x) (~g x))],
    .varDecl "d" t[int] (.det eb[((~g y) (~h y))]),
    .assumption "ax" eb[(~k z)]],
   [.distinct "dd" [eb[(~f x)], eb[(~h w)]],
    .assumption "h2" eb[((~g d) (~f d))],
    .varDecl "u" t[int] .nondet,
    .varDecl "e" t[int] (.det eb[(~h v)])]]

private def axiomSet : Std.HashSet String := Std.HashSet.ofList ["ax"]

private def obligation (goal : Expression.Expr) : ProofObligation Expression :=
  { label := "goal", property := .assert, assumptions := pcs, obligation := goal,
    metadata := .empty }

/-- Two goals over the shared path: one repeating `h` and `f` of the path, one with a name
    of its own. -/
private def goals : List Expression.Expr := [eb[((~h d) (~f x))], eb[((~m d) x)]]

private def defs : List VarDefinition := [{ name := "d", ty := default, body := default }]

/-- The cached seeds for `goal`, run on `cache`, with the cache it leaves. -/
private def seedsCached (goal : Expression.Expr) (cache : ExprFactsCache) :
    List String × ExprFactsCache :=
  (seedsKeepLastCached ((LExpr.getOps goal).map opName) pcs axiomSet).run cache

private def seedsSpec (goal : Expression.Expr) : List String :=
  ((LExpr.getOps goal).map opName ++ antecedentSpec pcs axiomSet).uniq

-- Precise seeds: fresh cache, and the cache left by the other goal.
#guard goals.all fun g => (seedsCached g ExprFactsCache.empty).1 == seedsSpec g
#guard (goals.foldl (fun (ok, c) g =>
    let (s, c) := seedsCached g c; (ok && s == seedsSpec g, c)) (true, ExprFactsCache.empty)).1
-- The names repeat, so deduplication matters, and the axiom's `k` is left out.
#guard seedsSpec goals[0]! == ["g", "f", "h"]
#guard seedsSpec goals[1]! == ["m", "g", "f", "h"]

-- Directed seeds (not deduplicated).
#guard Id.run ((antecedentOpsCached pcs axiomSet).run' ExprFactsCache.empty) ==
  antecedentSpec pcs axiomSet

-- Model variables: fresh cache, and the cache left by the other goal.
#guard goals.all fun g =>
  collectModelVars (obligation g) defs [] == modelVarsSpec (obligation g) defs []
#guard (goals.foldl (fun (ok, c) g =>
    let (vs, c) := (collectModelVarsCached (obligation g) defs []).run c
    (ok && vs == modelVarsSpec (obligation g) defs [], c)) (true, ExprFactsCache.empty)).1
-- `d` is defined, so it is not reported, but `y`, which only its definition reaches, is;
-- `z` and `v` are reached by an axiom and an unmanaged definition.
#guard (ProofObligation.getVars (obligation goals[0]!)).map (·.1.name) ==
  ["d", "x", "y", "z", "w", "v"]
#guard (modelVarsSpec (obligation goals[0]!) defs []).map (·.1.name) == ["x", "y", "z", "w", "v"]

end Core.AxiomSeedsCacheTests
