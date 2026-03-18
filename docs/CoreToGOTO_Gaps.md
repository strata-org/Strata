# Core-to-GOTO Translation: Remaining Gaps

This document tracks the remaining gaps in the Strata Core → CProver GOTO
translation pipeline used for CBMC verification.

## Pipeline Overview

### Laurel pipeline (with DFCC — Dynamic Frame Condition Checking — contracts)

```
strata laurelAnalyzeToGoto <file.lr.st>
symtab2gb <basename>.symtab.json --goto-functions <basename>.goto.json --out output.gb
goto-cc --function main -o output_cc.gb output.gb
goto-instrument --dfcc main output_cc.gb output_dfcc.gb
cbmc output_dfcc.gb --function main
```

### Python pipeline (direct verification)

```
strata pyAnalyzeLaurelToGoto <file.py.ion>
symtab2gb <basename>.symtab.json --goto-functions <basename>.goto.json --out output.gb
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
  quantifiers over types unsupported by CBMC's SMT2 backend — `array`,
  `struct_tag`, `regex`, `empty` — are silently skipped; see Known Limitations)
- Distinct declarations (`Decl.distinct`) → pairwise `!=` ASSUME instructions
- `Map.const` → GOTO `array_of` expression (constant-valued map/array)
- `Map k v` types → GOTO array with `#index_type` annotation preserving the
  key type (enables CBMC's SMT2 backend to use the correct sort for array
  indices instead of defaulting to `c_index_type`)
- Regex type → GOTO primitive type `regex`, CBMC maps to SMT-LIB `RegLan`
- String/regex operations → `function_application` in GOTO; CBMC's string
  solver patch maps these to the corresponding SMT-LIB theories
  (`Str.Length` → `str.len`, `Re.Star` → `re.*`, etc.)
- Local function declarations (`funcDecl`) → lifted to top-level GOTO functions
- Multi-procedure programs: symbol table deduplication preserves proper code types
- Output parameter types emitted in GOTO symbol table (not empty)
- Source locations reconstructed from byte offsets in the source text and
  propagated to GOTO instructions (CBMC reports correct line numbers)
- Function definition inlining (`inlineFuncDefsInProgram`): before GOTO
  translation, fully-applied calls to non-recursive, non-polymorphic functions
  with known bodies are replaced by the body with arguments substituted. This
  avoids emitting uninterpreted `mathematical_function` symbols in GOTO.
- Datatype axiom generation (`generateDatatypeAxioms`): for each datatype
  constructor `C(f₁:T₁,...,fₙ:Tₙ)` of datatype `D`, generates tester-positive
  (`D..isC(C(args)) = true`), tester-negative (`D..isC'(C(args)) = false`),
  and selector (`D..fᵢ!(C(args)) = xᵢ`) axioms. Only for constructors whose
  field types are all GOTO-translatable.
- Main parameter conversion (`asMain`): when translating the entry-point
  procedure, formal parameters are converted to havoc'd local variables so
  CBMC accepts the function as a standard C entry point (`void main(void)`).
- Default symbols: architecture constants and CBMC builtins are generated in
  Lean (`DefaultSymbols.lean`) and included in the symbol table, eliminating
  the Python `defaults.py` / `process_json.py` combine step.
- `goto-cc` entry point selection: the Laurel pipeline uses `goto-cc` to
  select the entry point function, enabling multi-procedure programs.
- Property summary metadata: user-facing assertion descriptions from Laurel
  (e.g., "divisor is zero") are propagated through Core metadata to GOTO
  source location comments, so CBMC reports meaningful descriptions instead
  of opaque labels like "assert_0".
- `cprover` backend: an alternative CHC-based verification backend using
  `cprover --smt2` for programs with mathematical types (Int, Real, String).
  Enabled via `--backend cprover` in the comparison script.

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

CBMC's DFCC instrumentation (`goto-instrument --dfcc`) provides native
contract checking as an alternative to Strata's CallElim transformation.

**What works:** The GOTO backend emits `contract::FUNC` symbols with
`is_property=true` containing lambda-wrapped `#spec_requires`,
`#spec_ensures`, and `#spec_assigns` clauses — matching the format
produced by CBMC's C front-end (`InstToJson.lean: createContractSymbol`,
`wrapInLambda`). All postconditions (including `free ensures`) are
included in the contract symbol. `goto-instrument --dfcc` recognizes
these contracts and begins instrumentation. Use `--no-call-elim` with
`StrataCoreToGoto` to preserve raw procedure calls for DFCC.

**Blocker:** DFCC requires all assigns-clause targets to have a
computable byte size (`size_of_expr` in `dfcc_utils.cpp`). Our GOTO
encoding uses mathematical types that lack byte sizes:

1. **`bool` type**: CBMC's mathematical boolean has no byte size. The C
   front-end uses `c_bool` (width 8) instead. Changing all `bool` to
   `c_bool` in the GOTO encoding risks affecting the SMT encoding path.

2. **Abstract struct types**: Partially addressed — padding changed from
   `bool` to `unsignedbv(8)` so abstract structs have a 1-byte size.

3. **Mathematical integer types**: `__CPROVER_integer` used for Map
   indices has no byte size.

**Recommendation:** Use CallElim (default) until the type issue is
resolved. See `docs/DFCC_Integration.md` for detailed analysis and
three possible fix options.

#### Procedure inlining duplicates variable declarations

The `ProcedureInlining` transform does not rename local variables when inlining
a procedure body. If multiple inlined procedures declare a variable with the
same name (e.g., `maybe_except`), the type checker rejects the program with
"Variable ... already in context." This affects `test_function_def_calls` in
the Python pipeline.

## CBMC Patches

The CI builds CBMC from source at base commit `c15f21fec0` ("Use SMT-LIB div
for integer division, add string/regex/mod support"), which already includes
string/regex type support (`String`, `RegLan`), string constant encoding, and
string/regex function mappings (`Str.Concat` → `str.++`, `Re.Star` → `re.*`,
etc.). The following patches are applied on top:

1. **`cbmc-unbounded-arrays.patch`** (`StrataTest/Backends/CBMC/`): Handles
   unbounded (non-constant-size) arrays used by the heap model. Includes:
   - Skip value-set tracking for `function_application` RHS (`value_set.cpp`)
   - Skip field-sensitive decomposition for opaque function applications
     returning structs with unbounded array components (`field_sensitivity.cpp`)
   - Skip bounds checking for arrays with non-constant size (`goto_check_c.cpp`)
   - Remove nil-size `CHECK_RETURN` for arrays, conditional typecast only for
     bitvector index types, recurse into `#index_type` in `find_symbols_rec`,
     tag-based dedup for struct datatypes in `datatype_map` (`smt2_conv.cpp`)
   - Add `ID_regex` to `irep_ids.def`

2. **`cbmc-quantifier-simplify.patch`** (`StrataTest/Backends/CBMC/`): Modifies
   the simplifier's preorder traversal to only simplify the body (operand 1) of
   quantifier expressions, leaving bound variables (operand 0) untouched. Without
   this patch, the simplifier converts bound variable symbols into non-symbol
   expressions, violating the `quantifier_exprt` invariant.

3. **`cbmc-bounds-check.patch`** (`StrataTest/Languages/Laurel/`): More
   extensive bounds checking adjustments for the Laurel DFCC pipeline. Overlaps
   with the simpler fix in `cbmc-unbounded-arrays.patch`; only needed for the
   Laurel pipeline.

4. **`cbmc-string-support.patch`** (`StrataTest/Languages/Python/`): Predates
   the current CBMC base commit and is now redundant — its changes (string type,
   string constants, `Str.Concat` mapping) are already in the base.

Patches 1 and 2 must be applied in order: `cbmc-unbounded-arrays` first, then
`cbmc-quantifier-simplify`.

5. **`cprover-strata-support.patch`** (`StrataTest/Backends/CBMC/`): Enables the
   `cprover` CHC-based verifier to handle GOTO programs from the Strata pipeline.
   Changes:
   - Handle `function_application` expressions in `state_encoding.cpp`: skip
     `address_rec` for `mathematical_function` symbols, walk member/index chains
     to find addressable bases, skip struct decomposition for computed RHS values
   - Fallback size for `enter_scope_state` with unsized types
     (`state_encoding_targets.cpp`)
   - Enable `use_datatypes` in SMT2 output so structs with mathematical types
     (Int, Real, String) are encoded as SMT datatypes, not bitvectors
   - Add `type2id` support for integer, real, string, mathematical_function
     types (`smt2_conv.cpp`)
   - Skip incompatible address types in `evaluate_fc` (`axioms.cpp`)
   - Add `--smt2-solver` CLI option for external SMT solver backend
   - `cprover_smt2_dec.h`: SMT2 decision procedure with datatypes enabled

   Use `cprover --smt2` to produce the SMT2 encoding (the default built-in
   solver does not support mathematical types).

Additionally, quantifier bound variables are emitted wrapped in a `tuple` node
in the GOTO JSON to match CBMC's `binding_exprt` internal structure, which
expects `op0()` to be a tuple containing the variable list.

## Known Issues

### Axioms with quantifiers over non-primitive types are skipped

CBMC's SMT2 backend cannot encode quantifier bound variables of `array`,
`struct_tag`, `regex`, or `empty` type. Array-typed quantifier variables have
no finite SMT2 sort; struct/regex/empty types have no SMT2 sort mapping for
quantifier variable declarations.

The `hasUnsupportedQuantifierTypes` filter in `Expr.lean` detects axioms
containing quantifiers over these types (`array`, `struct_tag`, `regex`,
`empty`). Such axioms are silently skipped
during GOTO emission (see Soundness section for why this is safe).

### Z3 timeout / cvc5 UNKNOWN on complex quantified axioms

Some tests in the Python pipeline produce axioms with deeply nested quantifiers
over uninterpreted functions that solvers cannot decide efficiently:
- `test_missing_models`, `test_precondition_verification`, `test_datetime`,
  `test_class_field_use`: Z3 hangs indefinitely (TIMEOUT); cvc5 quickly
  determines the formula is undecidable and returns UNKNOWN in 1–4 seconds.

These tests are marked SKIP in `cbmc_expected.txt`.

### #490: DDM parser infinite loop with `modifies` before `ensures`

The DDM parser expects `ensures` clauses before `modifies` clauses. When
`modifies` appears before `ensures` in the source text, the parser enters an
infinite loop instead of reporting a syntax error.

**Workaround:** Always write `ensures` before `modifies`.

**Proper fix:** The DDM parser should either accept clauses in any order
(preferred) or report a clear syntax error when clauses are out of order.
This is a DDM infrastructure issue, not specific to the GOTO backend.
