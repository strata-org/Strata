/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.SMT.Translate
import Strata.DL.SMT.Symbol
import Strata.Util.ListUtils

public section

/-!
# Preparing SMT queries for the Lean export

Preparation has two parts. `prepareTerms` is a pure function on SMT terms and contexts: it
assembles the query the solver was sent (`completeContext`; that the assembly matches what the
encoders send is tested, not proved), prunes it to what the goal, the assumptions and the
context's axioms reach, refuses what is not translated, and normalizes operator shapes the shallow
translator does not accept. A binary integer `div` or `mod` is left as it is: the translator gives a
division or modulo by zero its own meaning (below).
`prepareClosed` runs the steps in this order: `withinPreparedNodes` refuses a query that is too
large; `declareApplied` declares the functions the terms apply that no declaration lists, as the
solver's encoder does; `prepareTerms` assembles from that context and prepares; and the result
goes to the shallow translator (`translateQuery`). The assembled query
of `prepareTerms_sound` is the one `prepareTerms` builds, so `declareApplied` belongs to the
tested assembly, not to what is proved.

The sorts translated are Bool, Int and BitVec; uninterpreted functions and `define-fun`
definitions are. A query that reaches a String, Real or RegLan value, a datatype (including
`Option`), an uninterpreted sort or an array is refused with a diagnostic and writes no file.
Sort aliases are left to the translator's own `define-sort` handling.

What is proved, and what is not (`Strata.DL.SMT.Lean.QueryCorrect`, `prepareTerms_sound`):
- One direction only: if the prepared query entails its goal, so does the assembled query with
  the original assumptions and goal. Both sides are read in Strata's typed SMT semantics
  (`Strata.SMT.DenoteTyped`).
- Under two hypotheses that nothing checks at run time: that the assembled query and the
  prepared query are well formed (`SMTQuery.WF`). The first covers the whole assembled query,
  including what pruning drops.
- `SMTQuery.WF` admits only a fragment, listed exactly in the module comment of
  `Strata.DL.SMT.Lean.QueryCorrect`: roughly the binary forms of the connectives, `=`, integer
  arithmetic and comparisons, with negation, `ite`, `distinct`, quantifiers, `Option` and arrays,
  and no bit-vector, string or real operation. On a query outside it the theorem says
  nothing. In particular, of the normalization rules only the rule for `distinct` of two or more
  operands is proved; the output of the others (`and`/`or` with fewer than two operands, n-ary
  chains, n-ary `div`, `distinct` of zero or one operand) is pinned by `QueryTests`, not proved.
- That semantics reads an SMT string as a Lean `String`, which is not the solver's string; the
  export refuses strings, so no exported query relies on that reading.
- The theorem says nothing about the translation to Lean, `translateQuery`, or the printing of
  the proposition: that the proposition of a file means the prepared query is not proved.
- Division and modulo by zero: Strata's semantics leaves their values unspecified (an
  interpretation chooses them), and the translator does the same in Lean. When the query uses
  integer `div` or `mod`, it quantifies over two functions `divByZero` and `modByZero` and writes
  `x div y` as `if y = 0 then divByZero x else x / y`; where it translates a `div` or `mod`
  with another number of operands, it refuses the query (it translates no trigger and no
  definition that pruning drops). That translation is part of what is tested, not proved.
-/

namespace Strata.SMT.LeanExport

open Lean

/-- The query an exported file states, before translation. -/
structure PreparedTerms where
  context : Core.SMT.Context
  assumptions : List Term
  goal : Term

/-- A prepared query and the proposition it translates to: the validity of `goal` under
`assumptions` in `context`. -/
structure PreparedQuery extends PreparedTerms where
  validity : Expr

/-- The context the solver was sent: the given one with the obligation's own declarations and
definitions. A declaration named like a definition is refused: given a function definition `x`
of the context and a declaration `x`, the solver's encoders declare `x` and do not define it, and
given a declaration and a definition of one name they send both, which the solver rejects. A
symbol of the context that the obligation defines is the usual case (a common subexpression):
the encoders send the definition, and so does this context, through `kept`. -/
def completeContext (ctx : Core.SMT.Context)
    (definitions : List Core.VarDefinition)
    (declarations : List Core.VarDeclaration) : Except String Core.SMT.Context := do
  let contextDefinitions : Std.HashSet String :=
    ctx.ifs.toArray.foldl (fun names f => names.insert f.id) {}
  let declared : Std.HashSet String := declarations.foldl (fun names d => names.insert d.name) {}
  let mut ctx := ctx
  let mut signatures : Std.HashMap String UF := {}
  for uf in ctx.ufs.toArray ++ ctx.ifs.toArray.map IF.toUF do
    if let some prior := signatures[uf.id]? then
      unless prior == uf do
        throw s!"Conflicting signature for '{uf.id}'"
    signatures := signatures.insert uf.id uf
  for d in declarations do
    if contextDefinitions.contains d.name then
      throw s!"Declaration '{d.name}' has the name of a definition in the context"
    let uf : UF := { id := d.name, args := [], out := d.ty }
    if let some prior := signatures[d.name]? then
      unless prior == uf do
        throw s!"Conflicting managed declaration '{d.name}'"
    signatures := signatures.insert d.name uf
    ctx := ctx.addUF uf
  let mut definedNames := contextDefinitions
  for d in definitions do
    if definedNames.contains d.name then
      throw s!"Duplicate definition '{d.name}'"
    if declared.contains d.name then
      throw s!"Definition '{d.name}' has the name of a declaration"
    let f : SMT.IF := { id := d.name, args := [], out := d.ty, body := d.body }
    if let some prior := signatures[d.name]? then
      unless prior == f.toUF do
        throw s!"Conflicting managed definition '{d.name}'"
    unless d.body.typeOf == d.ty do
      throw s!"Definition '{d.name}' has a different body sort"
    signatures := signatures.insert d.name f.toUF
    definedNames := definedNames.insert d.name
    ctx := { ctx with ifs := ctx.ifs.insert f }
  let kept := ctx.ufs.toArray.filter fun uf =>
    !ctx.ifs.containsKey uf
  return { ctx with ufs := .ofArray kept }

/-- Visit each term before its children, including quantifier bodies and triggers. -/
private def foldTerm {α : Type} (visit : α → Term → α) (acc : α) (t : Term) : α :=
  let acc := visit acc t
  match t with
  | .app _ args _ => args.attach.foldl (fun acc t => foldTerm visit acc t.1) acc
  | .some t => foldTerm visit acc t
  | .quant _ _ triggers body =>
    triggers.attach.foldl (fun acc ts =>
      ts.1.attach.foldl (fun acc t => foldTerm visit acc t.1) acc)
      (foldTerm visit acc body)
  | _ => acc
termination_by sizeOf t
decreasing_by all_goals simp_wf; all_goals grind [→ List.sizeOf_lt_of_mem]

/-- Add to `acc` every function that `t` applies, including below quantifiers and in triggers. -/
def collectFunctions (acc : Std.HashSet UF) (t : Term) : Std.HashSet UF :=
  foldTerm (fun acc t => match t with
    | .app (.uf f) _ _ => acc.insert f
    | _ => acc) acc t

/-- The functions the query and every context axiom reach, through definition bodies. -/
def neededFunctions (ctx : Core.SMT.Context) (roots : List Term) : Std.HashSet UF := Id.run do
  let mut needed := (roots ++ ctx.axms.toList).foldl collectFunctions {}
  -- Each needed definition's body is collected once. Definitions usually precede their uses,
  -- so a pass from the last definition to the first reaches the fixed point, and a pass that
  -- collects nothing ends the search. Every pass before that one collects at least one more
  -- definition, so `ctx.ifs.size + 1` passes suffice and the loop needs no `partial` definition.
  let definitions := ctx.ifs.toArray.reverse
  let mut collected : Std.HashSet UF := {}
  for _ in [0:ctx.ifs.size + 1] do
    let before := collected.size
    for f in definitions do
      if needed.contains f.toUF && !collected.contains f.toUF then
        needed := collectFunctions needed f.body
        collected := collected.insert f.toUF
    if collected.size == before then break
  return needed

/-- The declarations and definitions of `ctx` that `needed` names, in context order. -/
def retainedContext (ctx : Core.SMT.Context) (needed : Std.HashSet UF) : Core.SMT.Context :=
  -- A filtered array of distinct elements is still distinct; store it verbatim.
  { ctx with
    ufs := .ofArrayUnchecked (ctx.ufs.toArray.filter needed.contains)
    ifs := .ofArrayUnchecked (ctx.ifs.toArray.filter fun f => needed.contains f.toUF) }

/-- Retain the closure rooted in the query and every context axiom. -/
def retainFunctions (ctx : Core.SMT.Context) (roots : List Term) :
    Except String Core.SMT.Context := do
  let needed := neededFunctions ctx roots
  let retained := retainedContext ctx needed
  let given : Std.HashSet UF := retained.ifs.toArray.foldl (fun given f => given.insert f.toUF)
    (retained.ufs.toArray.foldl (fun given f => given.insert f) {})
  for f in needed.toArray do
    unless given.contains f do
      throw s!"Missing function declaration or definition '{f.id}'"
  for f in retained.ifs.toArray do
    if f.isRec then throw s!"Recursive define-fun '{f.id}' is unsupported"
  return retained

/-- Each alias name with its definition; the first definition of a name counts, as for
`List.lookup` (`admissible` refuses a name defined twice before it resolves anything). -/
def aliasDefinitions (ctx : Core.SMT.Context) : Std.HashMap String TermType :=
  ctx.tySubst.foldl (fun m (name, ty) => if m.contains name then m else m.insert name ty) {}

/-- The aliases resolved so far, and those being resolved (to find a cycle). -/
abbrev ResolveM := StateT (Std.HashMap String TermType × Std.HashSet String) (Except String)

/-- Resolve the aliases in `ty`. Each alias is resolved once and remembered, so the time is
linear in the number of aliases. A chain of aliases each defined as the next one's bare name
(`A := B`) is followed by a loop, so its length costs no stack; an alias reached through a
compound sort (`A := Option B`, `A := C B`) is resolved by recursion, one level per such step.
An alias whose resolution reaches itself is refused. -/
partial def resolveSortIn (definitions : Std.HashMap String TermType) (ty : TermType) :
    ResolveM TermType := do
  match ty with
  | .constr n [] =>
    unless definitions.contains n do return ty
    let mut chain : Array String := #[]
    let mut current := ty
    let mut found : Option TermType := none
    repeat
      match current with
      | .constr m [] =>
        match definitions[m]? with
        | none => found := some current; break
        | some definition =>
          let (resolved, active) ← get
          if let some r := resolved[m]? then found := some r; break
          if active.contains m then throw "Cyclic sort alias"
          set (resolved, active.insert m)
          chain := chain.push m
          current := definition
      | _ => break
    -- The end of the chain is a resolved sort, a sort that names no alias, or a compound sort.
    let result ← match found with
      | some r => pure r
      | none => resolveSortIn definitions current
    modify fun (resolved, active) =>
      (chain.foldl (fun m name => m.insert name result) resolved, chain.foldl (·.erase ·) active)
    return result
  | .constr n args => return .constr n (← args.mapM (resolveSortIn definitions))
  | .option ty => return .option (← resolveSortIn definitions ty)
  | ty => return ty

/-- Resolve the aliases in `ty`; a cycle is refused ("Cyclic sort alias"). -/
def resolveSort (ctx : Core.SMT.Context) (ty : TermType) : Except String TermType :=
  (resolveSortIn (aliasDefinitions ctx) ty).run' ({}, {})

/-- Add `ty` and the sorts it is built from to `acc`, each sort once. -/
private def collectSort (acc : Array TermType) (ty : TermType) : Array TermType :=
  let acc := if acc.contains ty then acc else acc.push ty
  match ty with
  | .option ty => collectSort acc ty
  | .constr _ args => args.foldl collectSort acc
  | _ => acc

/-- Add to `acc`, with their component sorts (`collectSort`), the sort of every subterm of `t`,
the sort of every variable a quantifier of `t` binds, and the argument sorts of every function
`t` applies. Triggers are included, although the translator drops them: a sort that occurs only
in a trigger is checked like any other, so such a query is refused rather than exported (fail
closed). (`collectFunctions` walks triggers too, so a function applied only there is retained.) -/
private def collectTermSorts (acc : Array TermType) (t : Term) : Array TermType :=
  foldTerm (fun acc t =>
    let acc := collectSort acc t.typeOf
    match t with
    | .app (.uf uf) _ _ => uf.args.foldl collectSort acc
    | .quant _ vars _ _ => vars.foldl (fun acc v => collectSort acc v.ty) acc
    | _ => acc) acc t

/-- Every sort the pruned query reaches: in its terms, its quantified variables and the
signatures of its retained functions. The sorts are taken as written, aliases unresolved, so
that the alias names the query uses can be read from them. Resolve a sort before checking it. -/
private def requiredSorts (ctx : Core.SMT.Context) (roots : List Term) : Array TermType :=
  let sorts := roots.foldl collectTermSorts #[]
  (ctx.ufs.toArray ++ ctx.ifs.toArray.map IF.toUF).foldl
    (fun sorts uf => (uf.out :: uf.args).foldl collectSort sorts) sorts

/-- The sort aliases the pruned query reaches: those its sorts name, and those the definitions
of reached aliases name. The translator introduces every alias it is given, so an alias the
query does not use must not reach it: its definition may be a sort that is not
translated, which is no reason to refuse the query or to write a file that names it. -/
def reachedAliases (ctx : Core.SMT.Context) (roots : List Term) : Map String TermType :=
  let named (reached : Std.HashSet String) (ty : TermType) : Std.HashSet String :=
    (collectSort #[] ty).foldl (fun reached ty =>
      match ty with
      | .constr name [] => reached.insert name
      | _ => reached) reached
  let direct := (requiredSorts ctx roots).foldl named {}
  -- An alias may be defined by another: follow each reached alias's definition once.
  let definitions := aliasDefinitions ctx
  let rec close (fuel : Nat) (pending : List String) (reached : Std.HashSet String) :
      Std.HashSet String :=
    match fuel, pending with
    | 0, _ | _, [] => reached
    | fuel + 1, name :: rest =>
      match definitions[name]? with
      | none => close fuel rest reached
      | some ty =>
        let new := (named {} ty).toList.filter fun n =>
          definitions.contains n && !reached.contains n
        close fuel (new ++ rest) (new.foldl (·.insert ·) reached)
  -- `pending` starts with the names the query's sorts give, aliases or not; after that only
  -- aliases enter it, each at most once (it enters `reached` at the same time). So the fuel, one
  -- step for each of those names and one more, suffices.
  let reached := close (direct.size + ctx.tySubst.length + 1) direct.toList direct
  ctx.tySubst.filter fun (name, _) => reached.contains name

/-- The sorts that are translated: Bool, Int and bit-vectors. A query that reaches another is
refused. Strings are refused because the solver's strings are sequences of code points
0..0x2FFFF while Lean's `String` is another set of values, so a proof about Lean strings need
not hold for the solver's; the sort check sees every term, so a string literal is refused too. -/
private def checkSupportedSort (ty : TermType) : Except String Unit :=
  match ty with
  | .prim .bool | .prim .int | .prim (.bitvec _) => pure ()
  | .prim .string =>
    throw "unsupported sort 'String': the solver's strings (sequences of code points \
      0..0x2FFFF) are not Lean's `String`, so a proof about one need not hold for the other"
  | .prim .real => throw "unsupported sort 'Real'"
  | .prim .regex => throw "unsupported sort 'RegLan': regexes are not supported"
  | .option _ | .constr _ _ =>
    -- `reprStr` of a sort can break lines and indent; a diagnostic is one line, single-spaced.
    let name := " ".intercalate (((reprStr ty).replace "\n" " ").splitOn " " |>.filter (· ≠ ""))
    throw s!"unsupported sort '{name}': datatypes, Option, uninterpreted sorts and arrays are \
      not translated"

/-- The variables bound around a term: the nearest binder of each name, and the names as the
solver's text writes them. Both are shared between a scope and the scopes under it, so a
term under many binders does not look through them all at every symbol. -/
private structure BoundVars where
  nearest : Lean.PersistentHashMap String TermVar := {}
  symbols : Lean.PersistentHashSet String := {}

/-- Enter the scope of the binders `vars`: each becomes the nearest binder of its name, and its
name as the solver's text writes it is marked bound. -/
private def BoundVars.enter (bound : BoundVars) (vars : List TermVar) : BoundVars :=
  vars.foldl (fun bound v => {
    nearest := bound.nearest.insert v.id v
    symbols := bound.symbols.insert (_root_.Strata.SMT.Symbol.escapeForSMT v.id) }) bound

/-- Whether no name stands twice among `vars` (linear: `List.nodupB` uses a hash set). -/
private def distinctNames (vars : List TermVar) : Bool :=
  (vars.map (·.id)).nodupB

/-- Whether `name` has the shape of a name the solver's encoder generates: `f.<n>` for every
function it defines, `<name>@<n>` for a symbol renamed apart from another. A binder of that shape
could capture a generated name in the solver's text, where the proposition, which keeps the names
apart, does not: the file would state another query than the solver was sent. The rule goes by the
shape alone, so it also refuses such a name when Strata's own pipeline gave it (`me@1` in a Laurel
postcondition); the pipeline names a quantified variable that shadows another that way, so nested
quantifiers over one name are refused too. A narrower rule has to compare with the names the encoder
emitted (its state), and to keep refusing `f.<n>`. -/
private def generatedShape (name : String) : Bool :=
  ["@", "."].any fun separator =>
    match (name.splitOn separator).reverse with
    | last :: _ :: _ => !last.isEmpty && last.all Char.isDigit
    | _ => false

/-- SMT binds by name, whereas the shallow translator keys variables by their
typed identity and keeps UFs separate. Reject terms where those scopes differ, and binders that
could capture a name the solver's encoder generates. -/
private def checkBindings (globals : Std.HashSet String) (bound : BoundVars) (t : Term) :
    Except String Unit := do
  let checkSymbol (symbol : String) (includeGlobals : Bool := true) := do
    if bound.symbols.contains symbol then
      throw s!"Symbol '{symbol}' is shadowed by an SMT binder"
    if includeGlobals && globals.contains symbol then
      throw s!"Symbol '{symbol}' is also the name of a function the query declares or defines"
  match t with
  | .var v =>
    unless bound.nearest.find? v.id == some v do
      throw s!"Variable '{v.id}' does not match its nearest SMT binder"
  | .app (.uf f) args _ =>
    checkSymbol (_root_.Strata.SMT.Symbol.escapeForSMT f.id) false
    for t in args do checkBindings globals bound t
  | .app op args _ =>
    match op with
    | .bv (.zero_extend _) | .bv (.int_to_bv _) |
      .str (.re_index _) | .str (.re_loop _ _) =>
      -- Indexed identifiers do not refer to plain bound variables.
      pure ()
    | _ => checkSymbol op.mkName
    for t in args do checkBindings globals bound t
  | .prim (.bool b) => checkSymbol (if b then "true" else "false")
  | .none _ => checkSymbol "none"
  | .some t =>
    checkSymbol "some"
    checkBindings globals bound t
  | .quant _ vars triggers body =>
    unless distinctNames vars do
      throw "Duplicate SMT quantifier binder"
    if let some v := vars.find? (generatedShape ·.id) then
      throw s!"SMT binder '{v.id}' has the shape of a name the solver's encoder generates"
    let bound := bound.enter vars
    checkBindings globals bound body
    for ts in triggers do
      for t in ts do checkBindings globals bound t
  | _ => pure ()
termination_by sizeOf t
decreasing_by all_goals simp_wf; all_goals grind [→ List.sizeOf_lt_of_mem]

/-- The conjunction of `terms` as a balanced tree of binary `and`s, `true` when there are none:
its depth grows with the logarithm of the number of conjuncts, so a long conjunction does not
nest deeply. -/
def conjunction (terms : List Term) : Term :=
  match terms with
  | [] => .bool true
  | [t] => t
  | t :: u :: rest =>
    let half := (rest.length + 2) / 2
    .app .and [conjunction ((t :: u :: rest).take half),
      conjunction ((t :: u :: rest).drop half)] .bool
termination_by terms.length
decreasing_by all_goals simp only [List.length_take, List.length_drop, List.length_cons]; omega

/-- `x ≠ y` for every unordered pair of distinct positions, first position outermost. -/
def distinctPairs : List Term → List Term
  | [] => []
  | x :: rest => rest.map (fun y => .app .not [.app .eq [x, y] .bool] .bool) ++ distinctPairs rest

/-- Normalize n-ary operations into the binary shapes the shallow translator accepts. -/
def normalizeTerm (t : Term) : Term :=
  match t with
  | .some t => .some (normalizeTerm t)
  | .quant q vs ts b => .quant q vs (ts.map (·.map normalizeTerm)) (normalizeTerm b)
  | .app op args ty =>
    let args := args.map normalizeTerm
    match op, args with
    | .core .and, [] => .bool true
    | .core .or, [] => .bool false
    | .core .and, [x] | .core .or, [x] => x
    | .core .distinct, _ => conjunction (distinctPairs args)
    | .core .eq, x :: y :: z :: rest =>
      conjunction (chain .eq (x :: y :: z :: rest))
    | .num .le, x :: y :: z :: rest =>
      conjunction (chain .le (x :: y :: z :: rest))
    | .num .lt, x :: y :: z :: rest =>
      conjunction (chain .lt (x :: y :: z :: rest))
    | .num .ge, x :: y :: z :: rest =>
      conjunction (chain .ge (x :: y :: z :: rest))
    | .num .gt, x :: y :: z :: rest =>
      conjunction (chain .gt (x :: y :: z :: rest))
    -- SMT-LIB `div` is left-associative; the translator takes binary applications only.
    | .num .div, x :: y :: z :: rest =>
      (z :: rest).foldl (fun acc t => .app .div [acc, t] ty) (.app .div [x, y] ty)
    | _, _ => .app op args ty
  | _ => t
termination_by sizeOf t
decreasing_by all_goals simp_wf; all_goals grind [→ List.sizeOf_lt_of_mem]
where
  chain (op : Op) (args : List Term) : List Term :=
    match args with
    | x :: y :: rest => .app op [x, y] .bool :: chain op (y :: rest)
    | _ => []

/-- Replace every definition body and axiom of `ctx` by `f` of it. The keys of the
definitions (their signatures) do not change, so the arrays are stored verbatim. -/
def mapContextTerms (f : Term → Term) (ctx : Core.SMT.Context) : Core.SMT.Context :=
  { ctx with
    ifs := .ofArrayUnchecked (ctx.ifs.toArray.map fun d => { d with body := f d.body })
    axms := .ofArrayUnchecked (ctx.axms.toArray.map f) }

/-- The largest query that preparation works on, counted in term nodes after normalization plus
binders: every quantified variable, declared symbol, definition, definition parameter, declaration
and sort alias counts as one node. The bound also bounds the binders of the proposition, because
Lean's runtime cannot represent a variable that crosses 2^20 − 1 = 1,048,575 or more binders (the
translator would panic). Each binder of the proposition is counted: a declared symbol, a definition
or a parameter directly, an assumption or axiom (a premise) by its term, and a function declared on
first use by the application that declares it. Preparation adds no binder, and the translator at
most two (`divByZero` and `modByZero`), so 1,000,000 keeps the proposition well below that limit. -/
def maxPreparedNodes : Nat := 1000000

/-- The number of nodes `normalizeTerm t` has as a tree, counting each quantified variable as a
node, or `none` once the count passes `limit`. Normalization writes a middle operand of a chain
twice and an operand of `distinct` once for every other operand, so nesting them multiplies the
size, and the passes after normalization walk their input as a tree. The count is taken on `t`
itself and visits at most `limit` of its nodes; `visited` is the number visited so far. A
`distinct` whose pairs alone pass the limit is refused before its operands are visited. -/
partial def normalizedNodes (limit : Nat) (t : Term) (visited : Nat := 0) :
    Option (Nat × Nat) := do
  if visited ≥ limit then none
  let mut visited := visited + 1
  let mut size := 1
  match t with
  | .some t =>
    let (n, v) ← normalizedNodes limit t visited
    size := 1 + n
    visited := v
  | .quant _ vars triggers body =>
    size := size + vars.length
    if size > limit then none
    for t in body :: triggers.flatten do
      let (n, v) ← normalizedNodes limit t visited
      size := size + n
      visited := v
  | .app op args _ =>
    if let .core .distinct := op then
      -- Each operand stands in `n - 1` pairs and each pair adds a `not` and an `=`, whatever
      -- the operands are; a query this wide is refused without visiting them.
      let n := args.length
      if (n - 1) * n + 2 * (n * (n - 1) / 2) > limit then none
    let mut sizes : Array Nat := Array.mkEmpty args.length
    for t in args do
      let (n, v) ← normalizedNodes limit t visited
      sizes := sizes.push n
      visited := v
    let total := sizes.foldl (· + ·) 0
    let n := sizes.size
    -- The shapes `normalizeTerm` gives: `conjunction` of `k ≥ 1` conjuncts adds `k - 1` nodes,
    -- of none the node `true`.
    let conjoined (k : Nat) : Nat := if k == 0 then 1 else k - 1
    size := match op with
      | .core .and | .core .or => if n == 0 then 1 else if n == 1 then total else 1 + total
      | .core .distinct =>
        (n - 1) * total + 2 * (n * (n - 1) / 2) + conjoined (n * (n - 1) / 2)
      | .core .eq | .num .le | .num .lt | .num .ge | .num .gt =>
        if n > 2 then 2 * total - sizes[0]! - sizes[n - 1]! + (n - 1) + conjoined (n - 1)
        else 1 + total
      | .num .div => if n > 2 then total + (n - 1) else 1 + total
      | _ => 1 + total
  | _ => pure ()
  if size > limit then none
  return (size, visited)

/-- Refuse a query whose terms, normalized, have more than `maxPreparedNodes` nodes as trees,
together with its binders. Every pass of preparation and the translator walk a term as a tree,
so a term whose subterms are shared in memory, or multiplied by normalization, would cost them
its size written out. This check comes before all of them and visits at most
`maxPreparedNodes` nodes itself. -/
def withinPreparedNodes (context : Core.SMT.Context) (assumptions : List Term) (goal : Term)
    (definitions : List Core.VarDefinition) (declarations : List Core.VarDeclaration) :
    Except String Unit := do
  let tooLarge := s!"The query is too large to export: its normalized terms and its binders \
    have more than {maxPreparedNodes} nodes"
  -- Every declared symbol, definition, definition parameter, declaration and sort alias is a
  -- binder.
  let mut nodes := context.ufs.size + definitions.length + declarations.length +
    context.tySubst.length + context.ifs.toList.foldl (fun n f => n + 1 + f.args.length) 0
  if nodes > maxPreparedNodes then throw tooLarge
  for t in goal :: assumptions ++ definitions.map (·.body) ++ context.axms.toList ++
      context.ifs.toList.map (·.body) do
    match normalizedNodes (maxPreparedNodes - nodes) t with
    | some (size, _) => nodes := nodes + size
    | none => throw tooLarge

/-- The terms of a query: its goal, its assumptions, the axioms and the definition bodies. -/
def queryTerms (ctx : Core.SMT.Context) (assumptions : List Term) (goal : Term) : List Term :=
  goal :: assumptions ++ ctx.axms.toList ++ ctx.ifs.toList.map (·.body)

/-- The checks that refuse a query that is not translated: SMT binders that would
change what a symbol refers to, duplicate parameters, and unsupported sorts. Nothing here
changes the query. -/
def admissible (ctx : Core.SMT.Context) (assumptions : List Term) (goal : Term) :
    Except String Unit := do
  let globals : Std.HashSet String :=
    (ctx.ufs.toList.map (·.id) ++ ctx.ifs.toList.map (·.id)).foldl
      (fun globals id => globals.insert (_root_.Strata.SMT.Symbol.escapeForSMT id)) {}
  for t in goal :: assumptions ++ ctx.axms.toList do
    checkBindings globals {} t
  for f in ctx.ifs.toArray do
    unless distinctNames f.args do
      throw s!"Duplicate SMT parameter in '{f.id}'"
    if let some v := f.args.find? (generatedShape ·.id) then
      throw s!"SMT parameter '{v.id}' of '{f.id}' has the shape of a name the solver's encoder \
        generates"
    checkBindings globals (({} : BoundVars).enter f.args) f.body
  -- The query's own lookup takes an alias's first definition, the translator its last.
  unless (ctx.tySubst.map (·.1)).nodupB do
    throw "Duplicate sort alias"
  let roots := queryTerms ctx assumptions goal
  -- Only the sorts the pruned query reaches matter: a datatype or an array declared for
  -- another obligation is no reason to refuse this one. Aliases are resolved for the check.
  -- One resolution state for all the sorts, so that each alias is resolved once.
  let definitions := aliasDefinitions ctx
  let checkAll : ResolveM Unit := (requiredSorts ctx roots).forM fun ty => do
    checkSupportedSort (← resolveSortIn definitions ty)
  checkAll.run' ({}, {})

/-- The pure part of preparation: assemble, prune, filter, normalize.
`Strata.SMT.LeanExport.prepareTerms_sound` (in `QueryCorrect`) shows, in Strata's typed SMT
semantics, that when the result entails its goal, so does the assembled query
`completeContext context definitions declarations` with the original assumptions and goal; one
direction only, and only when both queries are well formed (`SMTQuery.WF`), which nothing
checks at run time. The module comment of `Strata.DL.SMT.Lean.QueryCorrect` lists the
fragment that `SMTQuery.WF` admits. -/
def prepareTerms (context : Core.SMT.Context) (assumptions : List Term) (goal : Term)
    (definitions : List Core.VarDefinition) (declarations : List Core.VarDeclaration) :
    Except String PreparedTerms := do
  let ctx ← completeContext context definitions declarations
  let ctx ← retainFunctions ctx (goal :: assumptions)
  admissible ctx assumptions goal
  -- No reachable sort is uninterpreted, so the translator binds no sort variables. It is
  -- given only the sort aliases the pruned query reaches.
  let ctx := mapContextTerms normalizeTerm { ctx with
    sorts := .empty
    tySubst := reachedAliases ctx (queryTerms ctx assumptions goal) }
  return { context := ctx, assumptions := assumptions.map normalizeTerm,
           goal := normalizeTerm goal }

/-- The solver's encoder declares a function the first time a term applies it, also when the
context does not list it (the abstracted functions of termination lemmas, for example). Add
those declarations, in the order the terms apply them, so that the assembled query is the one
the solver received. A name the context, a definition or a declaration already gives is left
alone. -/
def declareApplied (ctx : Core.SMT.Context) (roots : List Term)
    (definitions : List Core.VarDefinition) (declarations : List Core.VarDeclaration) :
    Core.SMT.Context :=
  let known : Std.HashSet String :=
    (ctx.ufs.toArray.map (·.id) ++ ctx.ifs.toArray.map (·.id)).foldl (·.insert ·) {}
  let known := definitions.foldl (fun known d => known.insert d.name) known
  let known := declarations.foldl (fun known d => known.insert d.name) known
  let terms := roots ++ definitions.map (·.body) ++ ctx.axms.toList ++
    ctx.ifs.toArray.toList.map (·.body)
  let (_, applied) := terms.foldl (fun state t =>
    foldTerm (fun (known, applied) t => match t with
      | .app (.uf f) _ _ =>
        if known.contains f.id then (known, applied) else (known.insert f.id, applied.push f)
      | _ => (known, applied)) state t) (known, (#[] : Array UF))
  applied.foldl (fun ctx f => ctx.addUF f) ctx

/-- Prepare a closed validity proposition over the supported sorts: the size check
(`withinPreparedNodes`), the functions declared on first use, the pure preparation, then the
shallow translation (`translateQuery`). Needs no Lean environment. -/
def prepareClosed (context : Core.SMT.Context)
    (assumptions : List Term) (goal : Term)
    (definitions : List Core.VarDefinition)
    (declarations : List Core.VarDeclaration) : Except MessageData PreparedQuery := do
  match withinPreparedNodes context assumptions goal definitions declarations with
  | .ok () => pure ()
  | .error message => throw m!"{message}"
  let context := declareApplied context (goal :: assumptions) definitions declarations
  let p ← match prepareTerms context assumptions goal definitions declarations with
    | .ok p => pure p
    | .error message => throw m!"{message}"
  let validity ← _root_.translateQuery p.context p.assumptions p.goal
  if validity.hasFVar || validity.hasMVar || validity.hasLooseBVars then
    throw m!"Prepared query is not closed"
  return { p with validity }

end Strata.SMT.LeanExport
