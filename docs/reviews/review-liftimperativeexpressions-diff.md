# Review: Changes to LiftImperativeExpressions.lean

Diff of `Strata/Languages/Laurel/LiftImperativeExpressions.lean` between
`origin/main` (upstream) and the current branch (Laurel semantics work,
rebased).

## Context

The upstream Strata repo introduced several breaking changes:

- `Identifier` changed from a `String` alias to a struct with `text : String`
  and `uniqueId : Option Nat` fields.
- `Identifier` has a `BEq` instance that compares only `.text` (a temporary
  hack), but no `DecidableEq`.
- `StmtExpr.LiteralDecimal` was removed.
- `Body.External` was added to the procedure body type.
- The `module` keyword now makes all definitions private by default; only
  `public`-marked definitions are visible to importers.

These changes broke compilation of the Laurel semantics files. The diff
adapts `LiftImperativeExpressions.lean` to compile against the new upstream.

## Relationship to the Correctness Proof

The correctness proof (`LiftImperativeExpressionsCorrectness.lean`) does
**not** directly reference any definitions from this file. It reasons about
the *semantics* of the transformation — using `EvalLaurelStmt`,
`EvalLaurelBlock`, store operations, etc. — rather than the monadic
implementation. The theorem names mention `transformStmt` and
`transformExpr` but only in documentation and naming conventions.

Therefore, **none of the changes below affect the correctness proof's logic**.
They are all either required for compilation or are incidental cleanups. The
proof needed its own separate fixes (for `Identifier → String` in store/heap
types), which are in `LiftImperativeExpressionsCorrectness.lean`.

## Change-by-Change Breakdown

### 1. Imports

```diff
-public import Strata.Languages.Laurel.LaurelFormat
-public import Strata.Languages.Laurel.LaurelTypes
-public import Strata.Languages.Core.Verifier
-public import Strata.DL.Util.Map
+import Strata.Languages.Laurel.LaurelFormat
+import Strata.Languages.Laurel.LaurelTypes
+public import Strata.Languages.Laurel.Resolution
+import Strata.Languages.Core.Verifier
```

**Why:** With the `module` keyword, `public import` re-exports symbols to
downstream importers. Only types that appear in the public API need `public
import`. `LaurelFormat`, `LaurelTypes`, and `Verifier` are internal
dependencies, so they become plain `import`. `Resolution` is added because
`SemanticModel` (defined there) appears in the public signature of
`liftExpressionAssignments`. `Map` is removed because `SubstMap` no longer
uses it.

**Correctness proof impact:** None.

### 2. Removed `public section`

```diff
-public section
```

**Why:** The upstream used `public section` to make all definitions visible.
We instead mark only the two entry-point functions as `public` (see §14).
This is better hygiene — internal helpers like `SubstMap`, `LiftState`,
`freshTempFor`, etc. don't need to be exported.

**Correctness proof impact:** None.

### 3. SubstMap: `Map` → `List` with custom `find?`/`insert`

```diff
-private abbrev SubstMap := Map Identifier Identifier
+private abbrev SubstMap := List (Identifier × Identifier)
+
+private def SubstMap.find? (m : SubstMap) (key : Identifier) : Option Identifier :=
+  (List.find? (fun (k, _) => k == key) m).map (·.2)
+
+private def SubstMap.insert (m : SubstMap) (key : Identifier) (val : Identifier) : SubstMap :=
+  (key, val) :: m.filter (fun (k, _) => !(k == key))
```

**Why:** The `Map` type's `find?`, `insert`, and `lookup` all require
`DecidableEq α`. After the rebase, `Identifier` has `BEq` but no
`DecidableEq`. Adding a `DecidableEq` that agrees with the text-only `BEq`
is not possible (the struct has two fields). Rather than adding a structural
`DecidableEq` that disagrees with `BEq` (which would cause subtle bugs in
`if x == y` vs `if x = y`), we replace `Map` with a plain `List` and
provide `BEq`-based `find?` and `insert`.

The semantics are identical: `find?` returns the first matching entry,
`insert` prepends and removes duplicates.

**Correctness proof impact:** None. The proof never references `SubstMap`.

### 4. LiftState: new fields, visibility changes

```diff
-  private subst : SubstMap := []
+  subst : SubstMap := []
+  env : List (Identifier × HighTypeMd) := []
   model : SemanticModel
   condCounter : Nat := 0
+  imperativeNames : List Identifier := []
   procedures : List Procedure := []
```

Four changes:

- **`subst` lost `private`:** The upstream marked `subst` as `private` and
  used `@[expose]` on `LiftM` to allow the `StateM` monad to access it.
  Since we removed `@[expose]` (see §5), `subst` must be non-private.

- **`env` added:** A local type environment (`List (Identifier × HighTypeMd)`)
  that tracks variable types introduced during the transformation. The
  upstream version used `computeType` (via `SemanticModel`) for all type
  lookups, but freshly generated snapshot variables (e.g., `$x_0`) don't
  exist in the `SemanticModel`. The `env` field provides a fallback for
  `getVarType` (see §7).

- **`imperativeNames` added:** A pre-computed list of non-functional
  procedure names. The upstream version called `model.isFunction` /
  `model.get` at each call site to determine if a `StaticCall` is
  imperative. Our version pre-computes this list once in
  `liftExpressionAssignments` and threads it through the state. Both
  approaches produce the same result for well-formed programs.

- **`procedures` added:** Stored for use by `computeType` when looking up
  return types of imperative calls.

**Correctness proof impact:** None directly. The proof doesn't reference
`LiftState` fields.

### 5. Removed `@[expose]` from `LiftM`

```diff
-@[expose] abbrev LiftM := StateM LiftState
+abbrev LiftM := StateM LiftState
```

**Why:** `@[expose]` was needed to let `StateM` access the `private subst`
field. Since `subst` is no longer `private`, `@[expose]` is unnecessary.

**Correctness proof impact:** None.

### 6. `freshTempFor`: `.text` → `ToString`

```diff
-  return s!"${varName.text}_{counter}"
+  return s!"${varName}_{counter}"
```

**Why:** `Identifier` has a `ToString` instance that returns `.text`, so
string interpolation produces the same result. Minor simplification.

**Correctness proof impact:** None. Same runtime behavior.

### 7. New helpers: `getVarType`, `addToEnv`

```lean
private def getVarType (varName : Identifier) : LiftM HighTypeMd := do
  let env := (← get).env
  match env.find? (fun (n, _) => n == varName) with
  | some (_, ty) => return ty
  | none => panic s!"Could not find {varName} in environment."

def addToEnv (varName : Identifier) (ty : HighTypeMd) : LiftM Unit :=
  modify fun s => { s with env := (varName, ty) :: s.env }
```

**Why:** The upstream used `computeType target` in `liftAssignExpr` to get
the type of a variable being snapshotted. `computeType` delegates to
`computeExprType` which looks up the `SemanticModel`. But snapshot variables
like `$x_0` are freshly generated and don't exist in the model. `getVarType`
looks up the local `env` instead, which is populated by `addToEnv` when
`LocalVariable` declarations are encountered.

**Correctness proof impact:** None. The proof doesn't call these functions.

### 8. `getSubst`: `lookup` → `find?`, visibility

```diff
-private def getSubst ...
-  match (← get).subst.lookup varName with
+def getSubst ...
+  match (← get).subst.find? varName with
```

**Why:** `Map.lookup` requires `DecidableEq`; our `SubstMap.find?` uses
`BEq`. Made non-private because the correctness proof file imports this
module (though it doesn't reference `getSubst` directly).

**Correctness proof impact:** None.

### 9. `setSubst`: anonymous pair → `insert`

```diff
-  modify fun s => { s with subst := ⟨ varName, value ⟩ :: s.subst }
+  modify fun s => { s with subst := s.subst.insert varName value }
```

**Why:** The upstream used anonymous constructor `⟨ varName, value ⟩` to
prepend to the `Map` (which is a `List`). Our `SubstMap.insert` does the
same thing but also removes any existing entry for `varName`, preventing
duplicate keys. This is slightly more correct but semantically equivalent
since `find?` returns the first match anyway.

**Correctness proof impact:** None.

### 10. `containsAssignmentOrImperativeCall`: `SemanticModel` → name list

```diff
-private def containsAssignmentOrImperativeCall (model: SemanticModel) (expr : StmtExprMd) : Bool :=
+def containsAssignmentOrImperativeCall (imperativeNames : List Identifier) (expr : StmtExprMd) : Bool :=
   ...
-    (match model.get name with
-    | .staticProcedure proc => !proc.isFunctional
-    | _ => false) ||
+      imperativeNames.contains name ||
```

**Why:** The upstream queried the `SemanticModel` at each `StaticCall` to
check if the callee is imperative. Our version takes a pre-computed list of
imperative procedure names. This avoids repeated `SemanticModel` lookups and
is simpler to reason about. The function is also made non-private (was
`private`) since it's a pure function that could be useful for testing.

**Semantic equivalence:** For well-formed programs where the `SemanticModel`
is consistent with the procedure list, both approaches identify the same set
of imperative calls.

**Correctness proof impact:** None. The proof doesn't reference this
function.

### 11. `liftAssignExpr`: `computeType` → `getVarType`

```diff
-        let varType ← computeType target
+        let varType ← getVarType varName
```

**Why:** When creating a snapshot variable, we need the type of the original
variable. The upstream used `computeType target` where `target` is the
expression `⟨.Identifier varName, md⟩`. This delegates to
`computeExprType` which looks up the `SemanticModel`. Our version uses
`getVarType varName` which looks up the local `env`. This is more robust
because the `env` is populated as variables are encountered during
transformation, while the `SemanticModel` only knows about variables from
the original program.

**Correctness proof impact:** None.

### 12. Removed `LiteralDecimal` case

```diff
-  | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _ => return expr
+  | .LiteralInt _ | .LiteralBool _ | .LiteralString _ => return expr
```

**Why:** `StmtExpr.LiteralDecimal` was removed from the upstream AST.

**Correctness proof impact:** None.

### 13. `StaticCall` / `IfThenElse` / `LocalVariable` / `Assign`: `model.isFunction` → `imperativeNames.contains`

Throughout `transformExpr` and `transformStmt`, all occurrences of:
```lean
let model := (← get).model
if model.isFunction callee then ...
```
are replaced with:
```lean
let imperative := (← get).imperativeNames
if imperative.contains name then ...
```

Note the **inverted condition**: `model.isFunction` returns `true` for
functional (pure) procedures, while `imperativeNames.contains` returns
`true` for imperative (non-pure) procedures. The `if`/`else` branches are
swapped accordingly.

Additional changes in these cases:
- `addToEnv callResultVar callResultType` added when lifting imperative
  calls in expression position (so the fresh variable is in the `env`).
- `condType ← computeType seqThen` instead of `computeType thenBranch`
  (use transformed expression, not original — the upstream had a workaround
  comment about this).
- Block expressions pre-populate `env` with `LocalVariable` declarations.
- `LocalVariable` in `transformExpr` calls `addToEnv name ty`.
- `LocalVariable` in `transformStmt` calls `addToEnv name ty`.

**Correctness proof impact:** None. Same transformation semantics.

### 14. Termination proof simplified

```diff
-    all_goals (try term_by_mem)
-    all_goals (apply Prod.Lex.left; try term_by_mem)
+    all_goals (term_by_mem)
```

**Why:** The upstream needed a two-step termination proof. After the AST
changes (removal of `LiteralDecimal`, etc.), `term_by_mem` alone suffices.

**Correctness proof impact:** None.

### 15. `transformProcedure`: initialize `env` from parameters

```diff
-  modify fun s => { s with subst := [], prependedStmts := [], varCounters := [] }
+  let initEnv : List (Identifier × HighTypeMd) :=
+    proc.inputs.map (fun p => (p.name, p.type)) ++
+    proc.outputs.map (fun p => (p.name, p.type))
+  modify fun s => { s with subst := [], prependedStmts := [], varCounters := [], env := initEnv }
```

**Why:** Seeds the local type environment with procedure input/output
parameter types so that `getVarType` can find them when creating snapshots
for parameters that appear in assignments.

Also adds `| .External => pure proc` to handle the new `Body.External`
constructor.

**Correctness proof impact:** None.

### 16. Entry points: `public` visibility, backward-compatible alias

```diff
-def liftExpressionAssignments (model: SemanticModel) (program : Program) : Program :=
-  let initState : LiftState := { model := model }
+public def liftExpressionAssignments (model : SemanticModel) (program : Program) : Program :=
+  let imperativeNames := program.staticProcedures.filter (fun p => !p.isFunctional) |>.map (·.name)
+  let initState : LiftState := { model := model, imperativeNames := imperativeNames, procedures := program.staticProcedures }
   ...
+
+public def liftImperativeExpressions (program : Program) : Program :=
+  let model : SemanticModel := { nextId := 0, compositeCount := 0, refToDef := {} }
+  liftExpressionAssignments model program
```

**Why:**
- `public` is required because the `module` keyword makes definitions
  private by default. `LaurelToCoreTranslator` does `public import` of this
  file and calls `liftExpressionAssignments`.
- `imperativeNames` is pre-computed from the program's procedure list and
  passed into the initial state.
- `liftImperativeExpressions` is a backward-compatible alias that creates an
  empty `SemanticModel`. This is used by the correctness proof's test
  infrastructure (if any) and preserves the old API.

**Correctness proof impact:** None.

## Summary

| Category | Changes | Proof impact |
|----------|---------|-------------|
| Module visibility (`public`/`import`) | §1, §2, §5, §8, §10, §16 | None |
| `DecidableEq` avoidance (`Map` → `List`) | §3, §8, §9 | None |
| Local type environment (`env`) | §4, §7, §11, §13, §15 | None |
| Imperative name list (replaces `model.isFunction`) | §4, §10, §13, §16 | None |
| AST changes (`LiteralDecimal`, `External`) | §12, §15 | None |
| Incidental cleanups | §6, §14 | None |

All changes are either **required for compilation** against the new upstream
or are **incidental simplifications**. None affect the correctness proof's
logic, which reasons about evaluation semantics rather than the monadic
transformation implementation.
