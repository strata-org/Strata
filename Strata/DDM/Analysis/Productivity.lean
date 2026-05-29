/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.AST

/-!
# Grammar Productivity Checker

A category is *productive* iff some operator builds it from productive
arguments.  The only base case is `frameworkAtomicCategories` — what
the parser constructs directly.
-/

public section

namespace Strata.DDM.Productivity

/-! ## Skeleton types -/

structure OpInfo where
  name : String
  result : QualifiedIdent
  args : Array QualifiedIdent
  deriving Repr, Inhabited

structure Blocker where
  opName : String
  unmetArgCats : Array QualifiedIdent
  deriving Repr, Inhabited

structure UnproductiveCategory where
  category : QualifiedIdent
  blockers : Array Blocker
  deriving Repr, Inhabited

structure Result where
  dialect : DialectName
  productive : Array QualifiedIdent
  unproductive : Array UnproductiveCategory
  deriving Repr, Inhabited

namespace Result

def isOk (r : Result) : Bool := r.unproductive.isEmpty

end Result

/-! ## Skeleton extraction -/

/-- Containers whose empty form is a valid value. -/
def nullableContainers : Array QualifiedIdent := #[
  q`Init.Seq, q`Init.Option,
  q`Init.CommaSepBy, q`Init.SpaceSepBy, q`Init.SpacePrefixSepBy,
  q`Init.NewlineSepBy, q`Init.SemicolonSepBy
]

private def isNullableContainer (c : SyntaxCat) : Bool :=
  nullableContainers.any (· == c.name)

private def isNonemptyMeta (m : Metadata) : Bool :=
  q`StrataDDL.nonempty ∈ m

/-- Every category in `c`'s type tree, DFS, head first. -/
partial def collectAllCategories (c : SyntaxCat) : Array QualifiedIdent :=
  c.args.foldl (init := #[c.name]) fun acc a => acc ++ collectAllCategories a

/-- Argument's productivity obligations, accounting for `@[nonempty]`. -/
def collectArgCategories (ad : ArgDecl) : Array QualifiedIdent :=
  let cat := ad.kind.categoryOf
  if cat.name == q`Init.Option then
    #[cat.name]
  else if isNullableContainer cat && !isNonemptyMeta ad.metadata then
    #[cat.name]
  else
    collectAllCategories cat

def opInfoOfDecl (decl : OpDecl) : OpInfo :=
  let args := decl.argDecls.toArray.foldl (init := #[]) fun acc ad =>
    acc ++ collectArgCategories ad
  { name := decl.name, result := decl.category, args }

def extractOps (d : Dialect) : Array OpInfo := Id.run do
  let mut out : Array OpInfo := #[]
  for decl in d.declarations do
    if let .op od := decl then
      out := out.push (opInfoOfDecl od)
  return out

def declaredCategories (d : Dialect) : Array QualifiedIdent := Id.run do
  let mut out : Array QualifiedIdent := #[]
  for decl in d.declarations do
    if let .syncat sc := decl then
      out := out.push { dialect := d.name, name := sc.name }
  return out

/-! ## Trusted seed (framework atoms only) -/

/-- Categories the parser constructs directly — the only trusted base. -/
def frameworkAtomicCategories : Array QualifiedIdent := #[
  q`Init.Ident, q`Init.Num, q`Init.Str, q`Init.ByteArray, q`Init.Decimal,
  q`Init.Seq, q`Init.Option,
  q`Init.CommaSepBy, q`Init.SpaceSepBy, q`Init.SpacePrefixSepBy,
  q`Init.NewlineSepBy, q`Init.SemicolonSepBy
]

@[expose] def trustedCategories : Std.HashSet QualifiedIdent :=
  frameworkAtomicCategories.foldl (init := (∅ : Std.HashSet QualifiedIdent))
    (fun acc c => acc.insert c)

theorem trustedCategories_eq :
    trustedCategories =
      frameworkAtomicCategories.foldl (init := (∅ : Std.HashSet QualifiedIdent))
        (fun acc c => acc.insert c) := rfl

/-! ## Import closure -/

private def transitiveImports.step (dialects : DialectMap)
    (state : Std.HashSet DialectName × Array DialectName)
    : Std.HashSet DialectName × Array DialectName :=
  let (seen, stack) := state
  match stack.back? with
  | none => (seen, stack)
  | some name =>
    let stack := stack.pop
    if seen.contains name then (seen, stack)
    else
      let seen := seen.insert name
      let stack :=
        if hMem : name ∈ dialects then
          (dialects[name]'hMem).imports.foldl (init := stack) fun s imp =>
            if seen.contains imp then s else s.push imp
        else stack
      (seen, stack)

private def transitiveImports.loop (dialects : DialectMap)
    : Nat → Std.HashSet DialectName × Array DialectName
            → Std.HashSet DialectName
  | 0,     (seen, _) => seen
  | _ + 1, (seen, #[]) => seen
  | n + 1, state =>
    transitiveImports.loop dialects n (transitiveImports.step dialects state)

/-- Fuel for the closure walk: pushes ≤ `n` (fresh-seen) × `n`
(imports per dialect) = `n²`; `n³` is comfortable slack. -/
def transitiveImports.fuel (n : Nat) : Nat := n * n * n

/-- Dialects reachable from `start` via `imports` (including `start`). -/
def transitiveImports
    (dialects : DialectMap) (start : DialectName) : Std.HashSet DialectName :=
  let n := dialects.toList.length
  transitiveImports.loop dialects (transitiveImports.fuel n) ({}, #[start])

/-- Spec: `d` is reachable from `start` via `imports` edges. -/
inductive ReachableViaImports (D : DialectMap) (start : DialectName)
    : DialectName → Prop where
  | self : ReachableViaImports D start start
  | step : ∀ {a b}, ReachableViaImports D start a →
      (h : a ∈ D) → b ∈ (D[a]'h).imports →
      ReachableViaImports D start b

/-- The closure walk returns exactly the reachable set.  Open obligation. -/
theorem transitiveImports.fuel_suffices
    (D : DialectMap) (start : DialectName) :
    ∀ d, ReachableViaImports D start d ↔ d ∈ transitiveImports D start := by
  sorry

/-- Operators from `target` and its transitive imports. -/
def extractOpsClosure (dialects : DialectMap) (target : DialectName)
    : Array OpInfo := Id.run do
  let imports := transitiveImports dialects target
  let mut out : Array OpInfo := #[]
  for d in dialects.toList do
    if imports.contains d.name then
      out := out ++ extractOps d
  return out

/-! ## Fixpoint -/

/-- One round: add `op.result` for every op whose args are all in `productive`. -/
@[expose] def step (ops : Array OpInfo) (productive : Std.HashSet QualifiedIdent)
    : Std.HashSet QualifiedIdent :=
  ops.foldl (init := productive) fun acc op =>
    if op.args.all acc.contains then acc.insert op.result else acc

theorem step_eq (ops : Array OpInfo) (productive : Std.HashSet QualifiedIdent) :
    step ops productive =
    ops.foldl (init := productive)
      (fun acc op => if op.args.all acc.contains then acc.insert op.result else acc) :=
  rfl

/-- Iterate `step`, early-exit on no growth. -/
@[expose] def iterate (ops : Array OpInfo) (productive : Std.HashSet QualifiedIdent)
    : Nat → Std.HashSet QualifiedIdent
  | 0 => productive
  | n + 1 =>
    let next := step ops productive
    if next.size == productive.size then productive
    else iterate ops next n

theorem iterate_zero (ops : Array OpInfo) (s : Std.HashSet QualifiedIdent) :
    iterate ops s 0 = s := rfl

theorem iterate_succ
    (ops : Array OpInfo) (s : Std.HashSet QualifiedIdent) (n : Nat) :
    iterate ops s (n + 1) =
      (let next := step ops s
       if next.size == s.size then s else iterate ops next n) := rfl

/-- Least productive set.  Fuel `ops.size + 1` suffices (one op-result per round). -/
@[expose] def runFixpoint
    (trusted : Std.HashSet QualifiedIdent) (ops : Array OpInfo)
    : Std.HashSet QualifiedIdent :=
  iterate ops trusted (ops.size + 1)

theorem runFixpoint_eq
    (trusted : Std.HashSet QualifiedIdent) (ops : Array OpInfo) :
    runFixpoint trusted ops = iterate ops trusted (ops.size + 1) := rfl

/-! ## Diagnostics -/

def blockersForCategory
    (cat : QualifiedIdent) (ops : Array OpInfo)
    (productive : Std.HashSet QualifiedIdent) : Array Blocker := Id.run do
  let mut out : Array Blocker := #[]
  for op in ops do
    if op.result != cat then continue
    let unmet := op.args.filter (! productive.contains ·)
    out := out.push { opName := op.name, unmetArgCats := unmet }
  return out

/-- Run the checker on `target`.  Seed: framework atoms; pool: `target` +
transitive imports; output: verdicts for `target`'s declared categories. -/
@[expose] def check (dialects : DialectMap) (target : DialectName) : Result :=
  if h : target ∈ dialects then
    let d := dialects[target]
    let ops := extractOpsClosure dialects target
    let cats := declaredCategories d
    let productive := runFixpoint trustedCategories ops
    let prodOut := cats.filter (productive.contains ·)
    let unprodOut := (cats.filter (! productive.contains ·)).map fun c =>
      { category := c, blockers := blockersForCategory c ops productive }
    { dialect := target, productive := prodOut, unproductive := unprodOut }
  else
    panic! s!"productivity check: dialect {target} not in DialectMap"

/-- `check`'s `productive` field as a `filter`. -/
theorem check_productive_eq
    (dialects : DialectMap) (target : DialectName) (h : target ∈ dialects) :
    (check dialects target).productive =
      (declaredCategories (dialects[target]'h)).filter
        ((runFixpoint trustedCategories
            (extractOpsClosure dialects target)).contains ·) := by
  simp [check, h]

/-! ## Pretty-printing -/

private def joinCommaSep (xs : Array QualifiedIdent) : String :=
  String.intercalate ", " (xs.toList.map QualifiedIdent.fullName)

private def formatBlocker (b : Blocker) : String :=
  s!"    op {b.opName} blocked on: {joinCommaSep b.unmetArgCats}"

private def formatUnproductive (u : UnproductiveCategory) : String :=
  let header := s!"  ✗ {u.category.fullName}"
  if u.blockers.isEmpty then
    s!"{header}\n    (no operator declares this category)"
  else
    String.intercalate "\n" (header :: u.blockers.toList.map formatBlocker)

def Result.format (r : Result) : String :=
  let head := s!"Productivity check for dialect {r.dialect}:"
  let noun := if r.productive.size == 1 then "category" else "categories"
  let prodLine := s!"  ✓ {r.productive.size} {noun} productive"
  if r.unproductive.isEmpty then
    s!"{head}\n{prodLine}"
  else
    let unprodHdr := s!"  ✗ {r.unproductive.size} unproductive:"
    String.intercalate "\n"
      (head :: prodLine :: unprodHdr :: r.unproductive.toList.map formatUnproductive)

end Strata.DDM.Productivity

end
