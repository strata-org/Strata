# Core-to-GOTO Translation: Remaining Gaps

This document tracks the remaining gaps in the Strata Core → CProver GOTO
translation pipeline used for CBMC verification.

## Pipeline Overview

### Laurel pipeline (with DFCC contracts)

```
strata laurelAnalyzeToGoto <file.lr.st>
python3 process_json.py combine defaults.json <basename>.symtab.json > full.symtab.json
symtab2gb full.symtab.json --goto-functions <basename>.goto.json --out output.gb
goto-cc --function main -o output_cc.gb output.gb
goto-instrument --dfcc main output_cc.gb output_dfcc.gb
cbmc output_dfcc.gb --function main
```

### Python pipeline (direct verification)

```
strata pyAnalyzeLaurelToGoto <file.py.ion>
python3 process_json.py combine defaults.json <basename>.symtab.json > full.symtab.json
symtab2gb full.symtab.json --goto-functions <basename>.goto.json --out output.gb
cbmc output.gb --function main --z3
```

## Implemented Features

- Global variables (`Decl.var`) with optional initializers
- Procedure contracts: `requires`, `ensures`, `modifies` → DFCC annotations
- Free requires/ensures: silently filtered (no CBMC equivalent)
- `exit` statement → unconditional GOTO to end of enclosing labeled block
- Loop invariants → `#spec_loop_invariant` on backward GOTO edge (multiple invariants supported)
- `old(expr)` → resolved by Core verifier before GOTO translation; `old`
  variables appear as regular symbols in GOTO (no GOTO `Old` expression needed)
- All arithmetic, comparison, boolean, bitvector, and real operators
- BV Extract operations → `extractbits`
- `cover` command → ASSERT instruction
- Datatypes and type constructors → struct symbol table entries (type
  constructors with no fields get a dummy `__padding` bool component to
  satisfy CBMC's requirement that structs have at least one component)
- Pure functions with bodies → GOTO functions with SET_RETURN_VALUE
- Procedure calls → FUNCTION_CALL instructions (including inside if-then-else and loops)
- Axioms (`Decl.ax`) → ASSUME instructions at procedure start (axioms with
  quantifiers over types unsupported by CBMC's SMT2 backend — `string`,
  `struct_tag`, `regex`, `empty` — are silently skipped for soundness; see
  Known Limitations below)
- Distinct declarations (`Decl.distinct`) → pairwise `!=` ASSUME instructions
- `Map.const` → GOTO `array_of` expression (constant-valued map/array)

- Loop measure (decreases clause) → `#spec_decreases` on backward GOTO edge
- Regex type → GOTO primitive type `regex`, CBMC maps to SMT-LIB `RegLan`
- String/regex operations → `function_application` in GOTO, CBMC maps to SMT-LIB
  (`Str.Length` → `str.len`, `Re.Star` → `re.*`, etc.)
- Local function declarations (`funcDecl`) → lifted to top-level GOTO functions
- Multi-procedure programs: symbol table deduplication preserves proper code types
- Output parameter types emitted in GOTO symbol table (not empty)
- Source locations propagated to GOTO instructions (CBMC reports correct line numbers)

## Soundness

The translation must be sound: if a program state is reachable in Core/Laurel,
then CBMC must also consider it reachable (or the translation must abort). A
false negative (CBMC says "verified" when a bug exists) must never occur due to
the translation.

### Design principles

- **Unhandled constructs abort.** Unrecognized types (`LMonoTy.ftvar`, `.arrow`),
  expressions (`.abs`), and statements (`funcDecl` at the Imperative level) return
  `Except.error`, halting the translation. They never silently produce wrong GOTO.

- **Unknown operators over-approximate.** Operators not explicitly mapped
  fall through to `functionApplication`, which CBMC encodes as uninterpreted
  functions in SMT. This is sound: the SMT solver considers all possible
  return values, which is an over-approximation (may produce false positives /
  spurious counterexamples, but never false negatives). String and regex
  operations intentionally use `functionApplication` so that CBMC's string
  solver patch maps them to the corresponding SMT-LIB theories.

- **Unresolved `exit` statements abort.** If an `exit` targets a label with no
  matching enclosing block, `Stmts.toGotoTransform` returns an error rather than
  producing a GOTO instruction with no target.

### Operator semantics

- **Integer division/modulo:** Core has three variants with different semantics:
  - `Int.Div` / `Int.SafeDiv` / `Int.Mod` / `Int.SafeMod`: Euclidean (Lean's
    `· / ·`, rounds toward negative infinity). These are **not** mapped to GOTO's
    `div`/`mod` (which is truncating) — they fall through to `functionApplication`
    for soundness.
  - `Int.DivT` / `Int.ModT`: Truncating (rounds toward zero). These match CBMC's
    `div`/`mod` semantics and are mapped directly.

- **Signed bitvector operations:** Core distinguishes signed (`SDiv`, `SMod`,
  `SLt`, `SLe`, `SGt`, `SGe`) from unsigned (`UDiv`, `UMod`, `ULt`, etc.)
  bitvector operations. Signed operations are mapped to the same GOTO operators
  as their unsigned counterparts, but with operands cast from `unsignedbv` to
  `signedbv` so that CBMC interprets them with signed semantics.

- **`free requires` / `free ensures`:** Free specification clauses (assumed but
  not checked) are silently omitted from the GOTO output. This is sound:
  - Dropping a `free requires` means the implementation is verified under
    *weaker* assumptions (more input states considered).
  - Dropping a `free ensures` means callers cannot assume the postcondition
    (more return states considered).
  Both directions are over-approximations.

## Open Gaps

### Low Priority

#### Unhandled types

The GOTO type translation (`LMonoTy.toGotoType` in `LambdaToCProverGOTO.lean`)
handles all concrete types: `bitvec n`, `int`, `bool`, `string`, `real`,
`regex`, `Map k v` (→ GOTO array), and named type constructors (→ struct tags).
The following `LMonoTy` forms are not handled:

- **`.ftvar`** (free type variables): Represented as `LMonoTy.ftvar name`.
  These appear when a polymorphic type (`LTy.forAll ["a"] (.ftvar "a")`) has
  not been fully instantiated. After type checking, all types should be
  monomorphized — if a `.ftvar` survives to GOTO translation, it indicates
  that monomorphization was incomplete. CBMC is monomorphic and has no type
  variable concept.

- **Function types** (`.arrow`): Represented as `LMonoTy.tcons "arrow" [argTy, retTy]`
  (or via `LMonoTy.mkArrow`). The translation returns an error for this type.
  CBMC has `mathematical_function` for declaring function *symbols* but cannot
  represent function *values* as data (no first-class functions). Programs
  passing functions as arguments must be defunctionalized before GOTO
  translation.

These are inherent limitations of targeting CBMC. Programs using these features
must be monomorphized and defunctionalized before GOTO translation.

#### Unhandled expressions

The expression translation (`LExprT.toGotoExpr` / `LExpr.toGotoExprCtx` in
`LambdaToCProverGOTO.lean`) handles constants, variables, operators, quantifiers,
conditionals, and function application. The following `LExpr` constructor is
not handled:

- **`.abs`** (lambda abstractions): `LExpr.abs m ty body` represents an
  anonymous function `fun (x : ty) => body`. GOTO programs have no concept of
  anonymous functions or closures. To support this, lambdas would need to be
  eliminated before GOTO translation, either by:
  - **Lambda-lifting**: extract each lambda into a named top-level function
    (already done for `funcDecl` via `collectFuncDecls` in `StrataMain.lean`).
  - **Inlining**: substitute the lambda body at every application site.

  In practice, well-prepared Core programs reaching the GOTO backend should not
  contain raw `.abs` nodes — they should have been eliminated by earlier
  transformations in the pipeline.

### Known Limitations

#### DFCC with mathematical integers

CBMC's DFCC instrumentation requires concrete-sized types for assigns clause
targets. The `modifies` clause now emits actual variable types (looked up from
the program's declarations) instead of hardcoded `integer`, which fixes the
"no definite size for lvalue target" error for programs using bounded types.
Programs that genuinely use mathematical integers in `modifies` targets will
still fail, as `integer` has no fixed bit width.

## Known Issues

### CBMC crashes on quantifiers over non-integer types (patched)

**Root cause:** CBMC's simplifier (`simplify_expr.cpp`) processes all operands
of quantifier expressions, including bound variables. This converts bound
variable symbols into non-symbol expressions, violating the `quantifier_exprt`
invariant that bound variables must be symbols.

**Fix:** The patch `cbmc-quantifier-simplify.patch` modifies the simplifier's
preorder traversal to only simplify the body (operand 1) of quantifier
expressions, leaving bound variables (operand 0) untouched. Applied
automatically in CI.

Additionally, quantifier bound variables are emitted wrapped in a `tuple`
node in the GOTO JSON to match CBMC's `binding_exprt` internal structure,
which expects `op0()` to be a tuple containing the variable list.

### Axioms with quantifiers over non-primitive types are skipped

**Root cause:** CBMC's SMT2 backend cannot encode quantifier bound variables
of `string`, `struct_tag`, `regex`, or `empty` type. String-typed quantifier
variables cause Z3 to hang; struct/regex/empty types have no SMT2 sort mapping
for quantifier variable declarations.

**Mitigation:** The `hasUnsupportedQuantifierTypes` filter in `Expr.lean`
detects axioms containing quantifiers over these types. Such axioms are
silently skipped during GOTO emission. This is sound: dropping an axiom
(which is an ASSUME instruction) means the verifier considers more states,
which is an over-approximation (may produce false positives, never false
negatives).

### #490: DDM parser infinite loop with `modifies` before `ensures`

**Root cause:** The Laurel DDM grammar defines the procedure syntax as:
```
op procedure (..., ensures, modifies, body) =>
  "procedure " ... ensures modifies body;
```

The DDM parser expects `ensures` clauses before `modifies` clauses. When
`modifies` appears before `ensures` in the source text, the parser enters an
infinite loop instead of reporting a syntax error.

**Reproduction:**
```
procedure test(x: int) returns (r: int)
  modifies x        -- modifies BEFORE ensures → infinite loop
  ensures r > 0
{ r := 1; }
```

**Workaround:** Always write `ensures` before `modifies`:
```
procedure test(x: int) returns (r: int)
  ensures r > 0     -- ensures FIRST → works
  modifies x
{ r := 1; }
```

**Proper fix:** The DDM parser should either:
1. Accept clauses in any order (preferred), or
2. Report a clear syntax error when clauses are out of order.

This is a DDM infrastructure issue, not specific to the GOTO backend.
