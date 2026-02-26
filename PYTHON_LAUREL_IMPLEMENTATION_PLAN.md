# Python → Laurel Implementation Plan

## Executive Summary

Goal: Support as many of the 50 kiro_tests_annotated benchmarks as possible using the Python → Laurel → Core pipeline.

**Current Status:**
- **Passing:** 2/50 benchmarks (4%) - `get_iam_role_arn`, `delete_s3_object` (but with empty bodies)
- **PythonToLaurel:** ~600 lines, supports basic expressions, control flow, but missing critical features

**Target:** Support 35-40 benchmarks (70-80%) with focused implementation effort

---

## Analysis Summary

### Benchmark Complexity Distribution
- **Simple (15 files):** Single function, basic control flow, minimal logic
- **Medium (19 files):** Multiple functions, moderate logic, some advanced patterns
- **Complex (16 files):** Classes with methods, advanced patterns, paginators

### Currently Supported in PythonToLaurel
✅ **Expressions:**
- Literals: int, string, bool
- Variables: name references
- Binary ops: +, -, *, //, %
- Comparisons: ==, !=, <, <=, >, >=
- Boolean ops: and, or, not
- Unary ops: not, - (negation)
- Function calls (basic)

✅ **Statements:**
- Assignment: `x = expr`
- Annotated assignment: `x: int = expr`
- If/else
- While loops
- Return
- Assert
- Expression statements

✅ **Types:**
- Primitives: int, bool, str
- Core types: DictStrAny, ListStr, PyAnyType
- Prelude types (via context)

❌ **Missing (Critical for Benchmarks):**
- Dict subscript access: `response['key']`
- For loops
- Try/except blocks
- String methods: .split(), .join(), .lower(), .startswith()
- Dict methods: .get(), .items(), .keys(), .values()
- List operations: .append(), list comprehensions, indexing
- F-string formatting (partially supported)
- Classes and methods
- Import statements (ignored currently)
- Nested subscripts: `response['A']['B']`
- List/dict literals in expressions

---

## Implementation Phases (Prioritized by ROI)

### **Phase 1: Dict Access & Basic For Loops**
**Impact:** Unlocks ~30 benchmarks (60%)
**Effort:** Medium (3-4 days)
**Files affected:** PythonToLaurel.lean

#### Features:
1. **Dict subscript access** - `response['key']`
   - Used in 50/50 files
   - Translate to: `StaticCall "dict_str_any_get_str" [dict, key]`
   - Handle nested access: `response['A']['B']` → chain calls

2. **For loops** - `for item in collection:`
   - Used in 33/50 files
   - Translate to: `While` with iteration (simplified model)
   - Support: `for item in response['items']:`

3. **List indexing** - `items[0]`, `items[-1]`
   - Used in 45/50 files
   - Translate to: `StaticCall "list_get" [list, index]`
   - Handle negative indices

4. **Dict .get() method** - `response.get('key', default)`
   - Used in 50/50 files
   - Translate to: `StaticCall "dict_str_any_get_or_default" [dict, key, default]`

**Expected Coverage After Phase 1:** ~25 benchmarks

---

### **Phase 2: Exception Handling**
**Impact:** Unlocks ~10 more benchmarks (20%)
**Effort:** Medium-High (4-5 days)
**Files affected:** PythonToLaurel.lean, Laurel grammar

#### Features:
1. **Try/except blocks** - `try: ... except Exception: ...`
   - Used in 49/50 files
   - Translate to: Laurel exception handling with `maybe_except` variable
   - Support specific exception types: `ClientError`, `NoSuchEntityException`
   - Support exception binding: `except Exception as e:`

2. **Raise statements** - `raise Exception(msg)`
   - Used in 11/50 files
   - Translate to: Setting `maybe_except` and jumping to handler

**Expected Coverage After Phase 2:** ~35 benchmarks

---

### **Phase 3: String & List Operations**
**Impact:** Unlocks ~5 more benchmarks (10%)
**Effort:** Medium (3-4 days)
**Files affected:** PythonToLaurel.lean, CorePrelude.lean

#### Features:
1. **String methods:**
   - `.split()` (13 files) → `StaticCall "str_split" [str, delim]`
   - `.join()` (14 files) → `StaticCall "str_join" [sep, list]`
   - `.lower()` (6 files) → `StaticCall "str_lower" [str]`
   - `.startswith()` (6 files) → `StaticCall "str_startswith" [str, prefix]`
   - `.strip()` (2 files) → `StaticCall "str_strip" [str]`

2. **List operations:**
   - `.append()` (18 files) → `StaticCall "list_append" [list, item]`
   - `.extend()` (3 files) → `StaticCall "list_extend" [list1, list2]`
   - List comprehensions (12 files) → Translate to while loop pattern

3. **String membership:** `'x' in str`
   - Used in 15 files
   - Translate to: `StaticCall "str_contains" [str, substr]`

4. **F-string formatting:** `f"Value: {x}"`
   - Used in 50/50 files
   - Currently only handles first element - need full concatenation

**Expected Coverage After Phase 3:** ~40 benchmarks

---

### **Phase 4: Classes & Methods** (Optional - Lower ROI)
**Impact:** Unlocks ~5-8 more benchmarks (10-16%)
**Effort:** High (7-10 days)
**Files affected:** PythonToLaurel.lean, Laurel grammar, heap parameterization

#### Features:
1. **Class definitions** - `class MyClass:`
   - Used in 16/50 files
   - Translate to: Laurel heap-based objects
   - Support `__init__` constructors
   - Support methods with `self`

2. **Object field access** - `self.field`, `obj.field`
   - Translate to: Heap read operations

3. **Instance creation** - `MyClass(args)`
   - Translate to: Constructor call + heap allocation

**Expected Coverage After Phase 4:** ~45 benchmarks

---

### **Phase 5: Advanced Features** (Deferred)
**Impact:** Unlocks ~2-5 remaining benchmarks (<10%)
**Effort:** Very High (10+ days)
**Files affected:** Multiple modules

#### Features (deprioritized):
- While loops (only 4 files) - Low ROI, already tested in Phase 1
- Set data structure (5 files)
- Generator expressions (2 files)
- Module imports: csv, argparse, logging, zipfile
- Paginators (boto3-specific, 4 files)
- Waiters (boto3-specific, 1 file)
- defaultdict (2 files)

---

## Detailed Implementation Plan: Phase 1

### Task 1.1: Dict Subscript Access (2 days)

**Location:** `PythonToLaurel.lean` line ~276

**Add to `translateExpr` match:**
```lean
| .Subscript _ value slice _ => do
  let valueExpr ← translateExpr ctx value
  let sliceExpr ← translateExpr ctx slice

  -- Determine if value is a dict or list based on context type
  -- For now, assume dict (can enhance with type tracking)
  match sliceExpr.val with
  | .LiteralString key =>
    -- Dict access with string key: response['key']
    return mkStmtExprMd (StmtExpr.StaticCall "dict_str_any_get_str" [valueExpr, sliceExpr])
  | .LiteralInt idx =>
    -- List access with int index: items[0]
    return mkStmtExprMd (StmtExpr.StaticCall "list_str_get" [valueExpr, sliceExpr])
  | _ =>
    -- Variable index - need runtime dispatch
    return mkStmtExprMd (StmtExpr.StaticCall "dict_str_any_get" [valueExpr, sliceExpr])
```

**Add to CorePrelude if needed:**
- `list_str_get : (list : ListStr, idx : int) → string`
- `dict_str_any_get : (dict : DictStrAny, key : string) → PyAnyType`

**Tests:**
- `ssm_get_parameter.py` - nested subscript
- `check_cloudwatch_metrics.py` - single subscript

### Task 1.2: For Loops (2 days)

**Location:** `PythonToLaurel.lean` line ~380

**Add to `translateStmt` match:**
```lean
| .For _ target iter body orelse _ => do
  -- Translate: for target in iter: body
  -- Map to: while(hasNext(iter)) { target = next(iter); body }

  let targetName ← match target with
    | .Name _ name _ => .ok name.val
    | _ => throw (.unsupportedConstruct "Only simple variable in for target supported" (toString (repr s)))

  let iterExpr ← translateExpr ctx iter

  -- Create iteration variable
  let iterVar := s!"{targetName}_iter"
  let hasNextCall := mkStmtExprMd (StmtExpr.StaticCall "iterator_has_next" [mkStmtExprMd (.Identifier iterVar)])

  -- Translate body with target in scope
  let targetType := mkCoreType "PyAnyType"  -- Or infer from context
  let bodyCtx := { ctx with variableTypes := ctx.variableTypes ++ [(targetName, targetType)] }
  let (_, bodyStmts) ← translateStmtList bodyCtx body.val.toList

  -- Add target assignment at start of body
  let nextCall := mkStmtExprMd (StmtExpr.StaticCall "iterator_next" [mkStmtExprMd (.Identifier iterVar)])
  let targetAssign := mkStmtExprMd (StmtExpr.Assign [mkStmtExprMd (.Identifier targetName)] nextCall)
  let fullBody := [targetAssign] ++ bodyStmts
  let bodyBlock := mkStmtExprMd (StmtExpr.Block fullBody none)

  -- Create while loop
  let whileStmt := mkStmtExprMd (StmtExpr.While hasNextCall [] none bodyBlock)

  -- Wrap in block with iterator initialization
  let iterInit := mkStmtExprMd (StmtExpr.LocalVariable iterVar (mkCoreType "Iterator") (some iterExpr))
  let block := mkStmtExprMd (StmtExpr.Block [iterInit, whileStmt] none)

  return (bodyCtx, block)
```

**Add to CorePrelude:**
- `iterator_has_next : (iter : Iterator) → bool`
- `iterator_next : (iter : Iterator) → PyAnyType`
- Iterator type for lists/dicts

**Tests:**
- Any benchmark with `for` loop (33 files)

### Task 1.3: Dict .get() Method (1 day)

**Location:** Handle in `translateExpr` for `.Attribute` followed by `.Call`

**Enhancement:** Detect method calls like `response.get('key', default)`

```lean
| .Call _ (.Attribute _ obj method _) args _ => do
  let objExpr ← translateExpr ctx obj
  let methodName := method.val

  match methodName with
  | "get" =>
    -- Dict.get(key, default)
    if args.size == 0 || args.size > 2 then
      throw (.typeError "Dict.get requires 1 or 2 arguments")
    let keyExpr ← translateExpr ctx args[0]!
    let defaultExpr ← if args.size == 2 then
      translateExpr ctx args[1]!
    else
      .ok (mkStmtExprMd .Hole)  -- None default
    return mkStmtExprMd (StmtExpr.StaticCall "dict_str_any_get_or_default"
      [objExpr, keyExpr, defaultExpr])
  | _ => throw (.unsupportedConstruct s!"Method {methodName} not yet supported" (toString (repr e)))
```

---

## Success Metrics

### Phase 1 Target (Week 1)
- ✅ Dict subscript access working
- ✅ Basic for loops working
- ✅ Dict .get() working
- ✅ 25+ benchmarks passing

### Phase 2 Target (Week 2)
- ✅ Try/except handling working
- ✅ 35+ benchmarks passing

### Phase 3 Target (Week 3)
- ✅ String/list operations working
- ✅ 40+ benchmarks passing

### Phase 4 Target (Optional)
- ✅ Basic class support
- ✅ 45+ benchmarks passing

---

## Testing Strategy

1. **Unit tests:** Test each feature in isolation
   - Create minimal test files for each new feature
   - Use `pyAnalyzeLaurel` to verify translation

2. **Benchmark progression:**
   - Track benchmark pass rate after each task
   - Identify common failure patterns
   - Prioritize fixes by impact

3. **Regression testing:**
   - Ensure existing passing benchmarks continue to pass
   - Run full benchmark suite after each phase

4. **Error analysis:**
   - Collect error messages from failed benchmarks
   - Group by root cause
   - Use to guide next implementation priorities

---

## Risk Mitigation

1. **Type inference complexity:**
   - Start with conservative assumptions (everything is PyAnyType)
   - Add type tracking incrementally
   - Use Core prelude's runtime type checking

2. **Laurel limitations:**
   - Some Python features may not map cleanly to Laurel
   - Document workarounds and limitations
   - Consider extending Laurel grammar if needed

3. **Prelude gaps:**
   - Many Core prelude functions may be missing
   - Need to add dict/list operations to CorePrelude.lean
   - Coordinate with Core prelude maintainers

4. **Time constraints:**
   - Focus on Phase 1-2 for maximum ROI
   - Phase 3-4 are optional enhancements
   - Document future work for community

---

## Next Steps

1. **Immediate (Today):**
   - Review and approve this plan
   - Set up development branch
   - Start Task 1.1 (Dict subscript access)

2. **This Week:**
   - Complete Phase 1 implementation
   - Test on 15 simple benchmarks
   - Iterate based on failures

3. **Next Week:**
   - Phase 2 implementation (try/except)
   - Aim for 35+ passing benchmarks

4. **Week 3+:**
   - Phase 3 if time permits
   - Documentation and cleanup
