# Path Cap: Batch Evaluation Refactor

## Problem

The current evaluator processes one path at a time:

```
evalAuxGo : Nat → SubstMap → EnvWithNext → Statements → ... → List EnvWithNext × Statistics
```

After evaluating the current statement for one input `Ewn`, it produces
`EAndNexts : List EnvWithNext`. The fold sends each result independently
through `go' ewn rest` to evaluate remaining statements. Results
accumulate across fold iterations.

With `cap N > 1`, each fold iteration may return up to N paths. With K
fold iterations, the accumulator grows to K × N paths. The pre-fold
merge caps `EAndNexts` at N, and the fold-internal merge caps the
accumulator, but neither prevents the exponential work inside each
`go'` call — by the time results return, obligations are already
generated on all paths.

## Solution: batch evaluation

Change `evalAuxGo` to take a list of paths as input:

```
evalAuxGo : Nat → SubstMap → List EnvWithNext → Statements → ... → List EnvWithNext × Statistics
```

The evaluation loop becomes:

```
1. For the current statement, evaluate it for EACH input path,
   collecting all results into one list.
2. Enforce the path cap on the combined results (merge .none paths).
3. Recurse on remaining statements with the merged list.
```

No fold needed. The merge fires between every pair of consecutive
statements with full visibility of all paths. `cap N` means at most N
continuing paths enter each statement.

## Changes

### `evalAuxGo` signature

```
-- Before:
def evalAuxGo (steps : Nat) (old_var_subst : SubstMap)
    (Ewn : EnvWithNext) (ss : Statements) (optExit : ...) :
    List EnvWithNext × Statistics

-- After:
def evalAuxGo (steps : Nat) (old_var_subst : SubstMap)
    (Ewns : List EnvWithNext) (ss : Statements) :
    List EnvWithNext × Statistics
```

Key changes:
- `Ewn : EnvWithNext` → `Ewns : List EnvWithNext` (batch input)
- `optExit` parameter removed — each `EnvWithNext` already carries its
  own `exitLabel`, and `processExit` is applied per-path

### Evaluation loop

```lean
def evalAuxGo (steps : Nat) (old_var_subst : SubstMap)
    (Ewns : List EnvWithNext) (ss : Statements) :
    List EnvWithNext × Statistics :=
  -- Handle errors and empty paths
  let (errors, good) := Ewns.partition (fun ewn => ewn.env.error.isSome)
  if good.isEmpty then (Ewns, noStats)
  else
  match steps with
  | 0 => (Ewns.map (fun ewn => { ewn with env.error := some .OutOfFuel }), ...)
  | steps' + 1 =>
    match ss with
    | [] => (Ewns, noStats)
    | s :: rest =>
      -- Separate exiting paths (skip this statement) from continuing
      let (continuing, exiting) := good.partition (fun ewn => ewn.exitLabel.isNone)
      -- Evaluate `s` for each continuing path
      let (results, stmtStats) := continuing.foldl
        (fun (acc, statsAcc) ewn =>
          let (res, s) := evalOneStmt steps' old_var_subst ewn s
          (acc ++ res, statsAcc.merge s))
        ([], noStats)
      -- Enforce path cap on combined results
      let (results, stmtStats) := enforcePathCap results stmtStats
      -- Recurse on remaining statements with merged paths + exiting
      let allPaths := results ++ exiting ++ errors
      evalAuxGo steps' old_var_subst allPaths rest
```

### `evalOneStmt` helper

Extract the per-statement evaluation into a helper that takes one
`EnvWithNext` and one `Statement`, returning `List EnvWithNext`:

```lean
private def evalOneStmt (steps : Nat) (old_var_subst : SubstMap)
    (Ewn : EnvWithNext) (s : Statement) :
    List EnvWithNext × Statistics :=
  match s with
  | .cmd c => ...
  | .block label ss md => ...
  | .ite cond then_ss else_ss md => ...
  | .funcDecl decl _ => ...
  | .typeDecl tc _ => ...
  | .exit l md => ...
```

This is the current statement match body, extracted verbatim.

### `processIteBranches`

Minimal change — it still takes one `Ewn` and evaluates both branches.
The key difference: it no longer calls `evalAuxGo` for remaining
statements. It just evaluates `then_ss` and `else_ss` and returns the
combined results. The caller (the batch loop) handles remaining
statements and path merging.

Actually, `processIteBranches` already works this way — it calls
`evalAuxGo` on `then_ss` and `else_ss` (sub-statement lists), not on
`rest`. So its signature stays the same. The only change is that
`evalAuxGo` it calls now takes `List EnvWithNext` instead of one `Ewn`.
It would pass `[{Ewn with pathConditions := ...}]` as a singleton list.

### `enforcePathCap` helper

```lean
private def enforcePathCap (ewns : List EnvWithNext) (stats : Statistics) :
    List EnvWithNext × Statistics :=
  match ewns.head?.bind (fun e => e.env.pathCap) with
  | .some cap =>
    let (noExit, hasExit) := ewns.partition (fun e => e.exitLabel.isNone)
    if noExit.length > cap then
      let merged := mergeCondPairs noExit.length noExit
      (merged ++ hasExit,
       stats.increment s!"{Evaluator.Stats.betweenStmt_capMerged}")
    else (ewns, stats)
  | .none => (ewns, stats)
```

### Termination

Current termination measure: `(steps, Imperative.Block.sizeOf ss)`.

The batch version recurses on `(steps', rest)` where `rest` is the tail
of `ss`. `Block.sizeOf rest < Block.sizeOf (s :: rest)` and `steps'
< steps' + 1`. Same lexicographic argument. The `Ewns` list doesn't
appear in the termination measure — it's just data being threaded
through.

`processIteBranches` calls `evalAuxGo` on `then_ss` and `else_ss` which
are sub-lists of the ITE statement. Same termination argument as before.

### Callers to update

1. `evalAux` (line 696): wraps single `Env` in singleton list
   ```lean
   evalAuxGo (Block.sizeOf ss) old_var_subst [{ env := E }] ss
   ```

2. `processIteBranches` (lines 660, 666): wraps single `Ewn` in list
   ```lean
   evalAuxGo steps old_var_subst [{Ewn with ...}] then_ss
   ```

3. Block case (line 533): wraps single `Ewn` in list
   ```lean
   evalAuxGo steps' old_var_subst [{Ewn with ...}] ss
   ```

4. Nondet ITE desugar (line 555): wraps single `Ewn` in list
   ```lean
   evalAuxGo steps' old_var_subst [{Ewn}] [initStmt, iteStmt]
   ```

5. Concrete ITE live branch (line 563): wraps single `Ewn` in list

### What gets simpler

- The fold + accumulator merge is replaced by a flat loop
- No duplication of merge logic (pre-fold and in-fold)
- `cap N` for any N works correctly — the merge fires once between
  each pair of statements with full visibility of all paths
- `processExit` logic is clearer — exiting paths are separated at the
  top of each iteration

### What stays the same

- `processIteBranches`: still evaluates both branches, returns combined
  results. The batch loop handles merging.
- `mergeCondPairs`, `findCondPairs`, `extractMatchingTrue`, `condEq`:
  all unchanged.
- `splitConds` tagging in `processIteBranches`: unchanged.
- Special-case merge (both branches single result, no exit): unchanged.

### Corrections from review

1. **Don't extract `evalOneStmt`** — keep the statement match inline
   inside the `mutual` block. Extracting it would require adding it
   to the mutual recursion group (it calls `evalAuxGo` for blocks and
   ITEs), which complicates termination. The inline match is clearer.

2. **Error handling**: paths with errors should be separated at each
   recursion step and passed through unchanged (current behavior). The
   `(errors, good)` partition at the top of each step is correct.

3. **`processExit` replacement**: the current `processExit ss optExit`
   is replaced by partitioning `Ewns` into continuing (`.none` exit)
   and exiting (non-`.none` exit) paths. Exiting paths pass through
   with their exit labels preserved — they propagate up to the
   enclosing block exactly as before.

4. **Steps decrement**: `steps` decrements once per statement, not per
   path. This bounds the total number of statement evaluations on any
   single path, which is the correct fuel semantics.

### Risk

- Termination proof may need adjustment if Lean's elaborator handles
  the `List EnvWithNext` parameter differently. But since the list
  doesn't appear in the termination measure, this should be fine.
- The `continuing` vs `exiting` partition must agree with the old
  `processExit` semantics. The key equivalence: `processExit ss (.some l)`
  returns `([], .some l)` (skip all), which is the same as putting
  the path in the `exiting` group and passing it through unchanged.

### TODO

After implementing, add test demonstrating `cap 2` on `exponentialItePgm`
produces 2 obligations (not 16). Also add the linear-accumulation test
from PathCapDesign.md (N ITEs with exits, N+1 exiting paths).
