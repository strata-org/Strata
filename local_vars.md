# Plan: Recursive Module Assignment Collection

## Problem

`collectModuleAssignments` only scans top-level statements. Assignments nested
inside `if`, `for`, `while`, `try`, `with` blocks are missed. This causes
variables like `region` (assigned inside `if __name__ == "__main__":`) to be
unresolved in both `@module_init` and other functions.

Python has no block scoping — all assignments within module-level code are
module globals, regardless of nesting depth.

## Design

### Change 1: Make `collectModuleAssignments` recursive

Scan all assignment targets recursively through the entire module-level
statement body, descending into `if`/`for`/`while`/`try`/`with` bodies.

User: Can we make this more efficient?  Maybe "worklist" should be an array of arrays of statements?

```lean
private def collectModuleAssignments (stmts : Array (stmt SourceRange))
    : Std.HashSet String := Id.run do
  let mut vars : Std.HashSet String := {}
  let mut worklist := stmts.toList
  while h : !worklist.isEmpty do
    let s := worklist.head (by simp_all)
    worklist := worklist.tail
    match s with
    | .Assign _ ⟨_, targets⟩ _ _ =>
      for t in targets do
        match t with
        | .Name _ ⟨_, name⟩ _ => vars := vars.insert name
        | _ => pure ()
    | .AnnAssign _ (.Name _ ⟨_, name⟩ _) _ _ _ =>
      vars := vars.insert name
    | .AugAssign _ (.Name _ ⟨_, name⟩ _) _ _ =>
      vars := vars.insert name
    | .For _ _ _ ⟨_, body⟩ ⟨_, orelse⟩ _ =>
      worklist := body.toList ++ orelse.toList ++ worklist
    | .While _ _ ⟨_, body⟩ ⟨_, orelse⟩ =>
      worklist := body.toList ++ orelse.toList ++ worklist
    | .If _ _ ⟨_, body⟩ ⟨_, orelse⟩ =>
      worklist := body.toList ++ orelse.toList ++ worklist
    | .With _ _ ⟨_, body⟩ _ =>
      worklist := body.toList ++ worklist
    | .Try _ ⟨_, body⟩ ⟨_, handlers⟩ ⟨_, orelse⟩ ⟨_, finalbody⟩ =>
      worklist := body.toList ++ orelse.toList ++ finalbody.toList ++ worklist
      for h in handlers do
        match h with
        | .ExceptHandler _ _ _ ⟨_, hbody⟩ =>
          worklist := hbody.toList ++ worklist
    | _ => pure ()
  return vars
```

This does NOT descend into `FunctionDef` or `ClassDef` — those create
their own scopes and are handled by `scanModule`.

### Change 2: Give `@module_init` the same globals as other functions

Currently `scanModule` gives `@module_init` the base `globals` set (no
assignment targets) and other functions get `funcGlobals` (with assignment
targets). Since all module-level assignments are module globals — even within
`@module_init` — there's no reason to treat `@module_init` differently.

`@module_init` should use `funcGlobals` too. Within `@module_init`, once
`x = 1` executes, `bindVar` overwrites the qualified ref with a local value.
If `x` is referenced before assignment on some path, it resolves to
`qualifiedRef M.x` — which is correct (the variable has its previous module
value, or doesn't exist yet at runtime).

### Change 3: Combine the three collection scans

`collectModuleGlobals`, `collectModuleAssignments`, and `collectImportBindings`
all scan the top-level statements. Combine into a single function:

```lean
private structure ModuleInfo where
  globals        : Std.HashSet String      -- for demand analysis exclusion
  assignmentVars : Std.HashSet String      -- module-level assignments (recursive)
  importBindings : Std.HashMap String QualifiedName  -- import qualified refs

private def collectModuleInfo (stmts : Array (stmt SourceRange))
    : ModuleInfo
```

The `globals` field = function names ∪ class names ∪ import names ∪ assignment
names (i.e., everything). This is what all functions use, including `@module_init`.

## Impact on remaining warnings

The 20 remaining "Unresolved name" warnings are all variables assigned inside
nested blocks within `@module_init` or within functions. The module-level ones
(like `region` inside `if __name__ == "__main__":`) will be fixed by this change.

Function-local variables assigned inside conditional branches (the majority of
the 20) are a separate issue — those need the function-local variable collection
described in ssa_steps.md. That can be a follow-up.

## Test plan

- Existing 35/35 tests should still pass
- Check that `region` in `test_lex_bot.py` resolves to `qualifiedRef module.region`
- Corpus warning count should drop further
