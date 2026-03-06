# Core-to-GOTO Translation: Remaining Gaps

This document tracks the remaining gaps in the Strata Core → CProver GOTO
translation pipeline used for CBMC verification.

## Pipeline Overview

### Laurel pipeline (with DFCC — Dynamic Frame Condition Checking — contracts)

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

Both pipelines require a patched CBMC build (see "CBMC Patches" below).

## Implemented Features

- Global variables (`Decl.var`) with optional initializers
- Procedure contracts: `requires`, `ensures`, `modifies` → DFCC annotations
  (`#spec_requires`, `#spec_ensures`, `#spec_assigns`)
- Free requires/ensures: silently filtered (no CBMC equivalent)
- `exit` statement → unconditional GOTO to end of enclosing labeled block
- Loop invariants → `#spec_loop_invariant` on backward GOTO edge (multiple
  invariants supported)
- Loop measure (decreases clause) → `#spec_decreases` on backward GOTO edge
- `old(expr)` → GOTO unary `Old` expression when `old` appears as a function
  application; in pipelines where the Core verifier resolves `old` to plain
  variables (e.g., after contract inlining), `old` variables appear as regular
  symbols in GOTO
- All arithmetic, comparison, boolean, bitvector, and real operators
- Integer Euclidean division/modulo (`Int.Div`, `Int.SafeDiv`, `Int.Mod`,
  `Int.SafeMod`) → expanded into compound GOTO expressions using truncating
  div/mod with a correction term
- Integer truncating division/modulo (`Int.DivT`, `Int.ModT`) → GOTO `div`/`mod`
  directly
- Signed bitvector operations (`SDiv`, `SMod`, `SLt`, `SLe`, `SGt`, `SGe`) →
  same GOTO operators as unsigned, with operands cast from `unsignedbv` to
  `signedbv`
- BV Extract operations → `extractbits`
- `cover` command → ASSERT instruction
- Datatypes and type constructors → struct symbol table entries (type
  constructors with no fields get a dummy `__padding` bool component to
  satisfy CBMC's requirement that structs have at least one component)
- Pure functions with bodies → GOTO functions with SET_RETURN_VALUE
- Procedure calls → FUNCTION_CALL instructions (including inside if-then-else
  and loops)
- Axioms (`Decl.ax`) → ASSUME instructions at procedure start (axioms with
  quantifiers over types unsupported by CBMC's SMT2 backend — `string`,
  `struct_tag`, `regex`, `empty` — are silently skipped; see Known Limitations)
- Distinct declarations (`Decl.distinct`) → pairwise `!=` ASSUME instructions
- `Map.const` → GOTO `array_of` expression (constant-valued map/array)
- Regex type → GOTO primitive type `regex`, CBMC maps to SMT-LIB `RegLan`
- String/regex operations → `function_application` in GOTO; CBMC's string
  solver patch maps these to the corresponding SMT-LIB theories
  (`Str.Length` → `str.len`, `Re.Star` → `re.*`, etc.)
- Local function declarations (`funcDecl`) → lifted to top-level GOTO functions
- Multi-procedure programs: symbol table deduplication preserves proper code types
- Output parameter types emitted in GOTO symbol table (not empty)
- Source locations reconstructed from byte offsets in the source text and
  propagated to GOTO instructions (CBMC reports correct line numbers)

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

- **Skipped axioms are sound.** Axioms with quantifiers over types unsupported
  by CBMC's SMT2 backend are silently skipped. Dropping an axiom (which is an
  ASSUME instruction) means the verifier considers more states, which is an
  over-approximation (may produce false positives, never false negatives).

- **Dropped free specs are sound.** Free specification clauses (assumed but not
  checked) are silently omitted from the GOTO output:
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

#### Procedure inlining duplicates variable declarations

The `ProcedureInlining` transform does not rename local variables when inlining
a procedure body. If multiple inlined procedures declare a variable with the
same name (e.g., `maybe_except`), the type checker rejects the program with
"Variable ... already in context." This affects `test_function_def_calls` in
the Python pipeline.

## CBMC Patches

The CI builds CBMC 6.8.0 from source with four patches applied:

1. **`cbmc-string-support.patch`** (`StrataTest/Languages/Python/`): Adds
   `String` as a recognized type in CBMC's SMT2 backend, enabling string
   constants and operations to be encoded in SMT-LIB.

2. **`cbmc-bounds-check.patch`** (`StrataTest/Languages/Laurel/`): Adjusts
   bounds checking for the Laurel pipeline.

3. **`cbmc-regex-support.patch`** (`StrataTest/Backends/CBMC/`): Adds `regex`
   as a primitive type in CBMC, mapped to SMT-LIB `RegLan`.

4. **`cbmc-quantifier-simplify.patch`** (`StrataTest/Backends/CBMC/`): Modifies
   the simplifier's preorder traversal to only simplify the body (operand 1) of
   quantifier expressions, leaving bound variables (operand 0) untouched. Without
   this patch, the simplifier converts bound variable symbols into non-symbol
   expressions, violating the `quantifier_exprt` invariant.

Additionally, quantifier bound variables are emitted wrapped in a `tuple` node
in the GOTO JSON to match CBMC's `binding_exprt` internal structure, which
expects `op0()` to be a tuple containing the variable list.

## Known Issues

### Axioms with quantifiers over non-primitive types are skipped

CBMC's SMT2 backend cannot encode quantifier bound variables of `string`,
`struct_tag`, `regex`, or `empty` type. String-typed quantifier variables cause
Z3 to hang; struct/regex/empty types have no SMT2 sort mapping for quantifier
variable declarations.

The `hasUnsupportedQuantifierTypes` filter in `Expr.lean` detects axioms
containing quantifiers over these types. Such axioms are silently skipped
during GOTO emission (see Soundness section for why this is safe).

### Z3 timeout on complex quantified axioms

Some tests (`test_missing_models`, `test_precondition_verification` in the
Python pipeline) produce axioms with deeply nested integer quantifiers that
cause Z3 to hang indefinitely. These tests are marked SKIP in
`cbmc_expected.txt`.

### #490: DDM parser infinite loop with `modifies` before `ensures`

The DDM parser expects `ensures` clauses before `modifies` clauses. When
`modifies` appears before `ensures` in the source text, the parser enters an
infinite loop instead of reporting a syntax error.

**Workaround:** Always write `ensures` before `modifies`.

**Proper fix:** The DDM parser should either accept clauses in any order
(preferred) or report a clear syntax error when clauses are out of order.
This is a DDM infrastructure issue, not specific to the GOTO backend.
