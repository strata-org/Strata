# Plan: Generic Metadata Annotations in Core Grammar

## Goal

Add a generic `@[key, key = value, ...]` dictionary syntax to Core's DDM Grammar
so that metadata fields from `Imperative.MetaData` can be visualized in
pretty-printed Core output without per-field grammar changes.

This follows the MLIR approach: operations carry an attribute dictionary with a
distinction between *inherent* attributes (known keys with validated types) and
*discardable* attributes (unknown keys accepted permissively for forward
compatibility).

## Design Principles

- **Single dictionary** per construct: `@[reachCheck, propertyType = "divisionByZero"]`
  rather than repeated `@[reachCheck] @[propertyType("divisionByZero")]`.
  This avoids collision with `{ }` which is already used for blocks in the grammar.
- **Order-preserving**: The annotation list is ordered, not a map. This is
  load-bearing for `relatedFileRange` entries which encode inlining call-stack
  depth (innermost first).
- **Tag-based emission**: The pretty-printer uses a `Set String` of keys to emit
  (plus `all`/`none` presets), not a linear verbosity hierarchy.
- **Inherent vs. discardable keys**: Known keys are validated at parse time;
  unknown keys are accepted as discardable for forward compatibility.

## Architecture: Shared Utilities, Inline Grammar

The annotation grammar categories (5 categories, 6 ops) are defined **inline
in each dialect's grammar** rather than factored into a shared DDM dialect.
Rationale:

- Core's grammar is inline Lean (`#dialect` / `#end`), not a `.st` file.
  Importing a non-builtin dialect from an inline grammar would require making
  MetadataAnn a StrataDDM built-in — coupling the DDM package to
  Strata-specific concepts.
- The grammar surface is tiny — duplication cost is negligible.
- Laurel support is future work; requirements may shift.

The **Lean-side translation and validation utilities** live in a shared
location (`Strata/MetadataAnn/`) and operate on generic `Arg`/`Operation`
types. This is where the real reuse value is:

- `translateMetadataAnn : Arg → TransM (MetaData P)` — parses `@[...]`
  AST into `MetaData`, dispatching to per-dialect validation.
- `metaDataToAnnotationArg : MetaData P → MetadataAnnFilter → Arg` —
  formats `MetaData` back to grammar AST for pretty-printing.
- `MetadataAnnConfig` — a configuration struct that each dialect
  instantiates with its inherent key set and validation rules.

```lean
structure MetadataAnnConfig where
  inherentKeys : Std.HashSet String
  validateKey : String → Option MetadataAnnValue → TransM (Option String)
```

When Laurel adopts annotations, it duplicates the 6 grammar ops in
`LaurelGrammar.st` (trivial) and instantiates `MetadataAnnConfig` with
its own inherent set. The shared Lean utilities handle the rest.

This design does not interfere with runtime metadata manipulation by
transforms — passes operate directly on `Array (MetaDataElem P)` in Lean,
below the grammar layer. The translation utilities are only invoked during
parsing (`.st` text → `MetaData`) and emission (`MetaData` → `.st` text).

## Grammar Changes (Grammar.lean)

### Step 1: Define annotation value and entry categories

```
category MetadataAnnValue;
op mdAnnValStr (s : Str) : MetadataAnnValue => s;
op mdAnnValExpr (e : Expr) : MetadataAnnValue => "(" e ")";

category MetadataAnnKey;
op mdAnnKeyBare (name : Ident) : MetadataAnnKey => name;
op mdAnnKeyPrefixed (dialect : Ident, name : Ident) : MetadataAnnKey =>
  dialect "." name;

category MetadataAnnEntry;
op mdAnnFlag (key : MetadataAnnKey) : MetadataAnnEntry => key;
op mdAnnKV (key : MetadataAnnKey, value : MetadataAnnValue) : MetadataAnnEntry =>
  key " = " value;
```

Values come in three forms:
- **Bare flag**: `reachCheck` — maps to `MetaDataElem.Value.switch true`
- **String literal**: `propertyType = "divisionByZero"` — maps to `.msg` or
  `.provenance` depending on the key
- **Parenthesized expression**: `bound = (n + 1)` — maps to `.expr`. Parens
  delimit where the expression ends.

### Step 2: Define the annotation dictionary

```
category MetadataAnn;
op mdAnn (entries : CommaSepBy MetadataAnnEntry) : MetadataAnn =>
  "@[" entries "]";
```

### Step 3: Attach to constructs via `SpacePrefixSepBy` or `Option`

Add `annots : Option MetadataAnn` as the first argument to all:
- **Statements**: `assert`, `cover`, `assume`, `assign`, `varStatement`,
  `initStatement`, `havoc_statement`, `if_statement`, `while_statement`,
  `call_statement`, `block_statement`, `exit_statement`
- **Commands**: `command_procedure`, `command_typedecl`, `command_typesynonym`,
  `command_constdecl`, `command_fndecl`, `command_fndef`, `command_recfndefs`,
  `command_axiom`, `command_distinct`, `command_block`,
  `command_cfg_procedure`, `command_datatypes`
- **Spec elements**: `ensures_spec`, `requires_spec`

Example for `assert`:
```
op assert (annots : Option MetadataAnn, label : Option Label, c : bool) :
  Statement => annots "assert " label c ";";
```

### Step 4: Remove the dedicated ReachCheck category

Once `MetadataAnn` is in place, `@[reachCheck]` becomes just one
`mdAnnFlag "reachCheck"` entry. Remove:
- `category ReachCheck;`
- `op reachCheck () : ReachCheck => "@[reachCheck] ";`
- The `reachCheck? : Option ReachCheck` parameters on `assert` / `cover`

This is a **breaking change** to the grammar AST. Existing `.st` files
using `@[reachCheck] assert ...` will still parse (the surface syntax is
preserved), but the underlying DDM AST node changes from `Core.reachCheck`
to `Core.metaFlag`. Migration of on-disk `.st` files that are parsed
by the old grammar is accepted as necessary.

## Value Encoding Conventions

### MetaDataElem.Value mapping

| Value variant | Grammar form | Round-trip notes |
|---|---|---|
| `.switch true` | bare flag (`key`) | absence = false |
| `.switch false` | (omitted) | not emitted |
| `.msg s` | `key = "s"` | literal string |
| `.provenance (.loc uri range)` | `key = "uri:startLine:startCol-endLine:endCol"` | structured encoding |
| `.provenance (.synthesized origin)` | `key = "<synthesized:origin>"` | convention: angle brackets + `synthesized:` prefix |
| `.expr e` | `key = (e)` | parenthesized Core expression |

### Provenance string conventions

File-based provenance uses `"file.st:10:3-15:7"` (URI, start line:col, end line:col).

Synthesized provenance uses the `<synthesized:ORIGIN>` convention:
```
@[provenance = "<synthesized:loopUnrolling>"]
@[provenance = "<synthesized:inlining/foo>"]
```

The parser recognizes the `<synthesized:...>` wrapper and constructs
`Provenance.synthesized origin` accordingly. This is unambiguous because
file URIs cannot start with `<`.

### relatedFileRange ordering

Multiple `relatedFileRange` entries encode the inlining call stack. The
order in the annotation list is the array order — innermost (most deeply
inlined) call first:

```
@[provenance = "inner.st:5:1",
  relatedFileRange = "mid.st:10:3",
  relatedFileRange = "outer.st:20:1"]
```

The pretty-printer must emit them in array order, not sorted or grouped.

## Inherent vs. Discardable Keys

### Inherent keys (validated at parse time)

| Key | Expected value form | Maps to |
|---|---|---|
| `reachCheck` | bare flag | `.switch true` |
| `fullCheck` | bare flag | `.switch true` |
| `validityCheck` | bare flag | `.switch true` |
| `satisfiabilityCheck` | bare flag | `.switch true` |
| `propertyType` | string | `.msg` |
| `propertySummary` | string | `.msg` |
| `provenance` | string (structured) | `.provenance` |
| `relatedFileRange` | string (structured) | `.provenance` |

The parser validates that inherent keys have the correct value form.
For example, `@[reachCheck = "foo"]` is a parse error (expected bare flag).

### Discardable keys (forward-compatible)

Any key not in the inherent set is accepted permissively:
- Bare flag → stored as `.label key` + `.switch true`
- With string value → stored as `.label key` + `.msg value`
- With expression value → stored as `.label key` + `.expr e`

This allows downstream passes or external tools to introduce new metadata
without grammar changes.

### Namespace prefix convention

Strata is a multi-dialect ecosystem with Core at the neck of the hourglass.
Multiple source dialects (Laurel, C_Simp, B3, Python, etc.) lower through
Core and may attach their own metadata. Following MLIR's convention:

- **Unprefixed keys** are inherent to Core (the set listed above). Core
  owns their semantics and validates them.
- **Dialect-prefixed keys** use `dialect.key` syntax and are discardable
  from Core's perspective. The originating dialect owns verification.

Examples:
```
@[reachCheck, python.source_line = "42"]
@[provenance = "file.st:10:3", laurel.loop_id = "L7"]
@[b3.diagnosis_id = "D-1234", b3.severity = "warning"]
```

Core passes must preserve discardable (prefixed) keys they don't recognize
— they flow through opaquely. A pass that strips metadata must only strip
keys it owns (unprefixed, or its own dialect prefix).

The parser accepts any `ident.ident` or bare `ident` as a key. Validation
rules:
- Unprefixed key not in inherent set → warning (possible typo or missing
  dialect prefix)
- Prefixed key → always accepted, no validation of value form

### Current state of metadata mutations in transforms

Today, all existing transforms that add or remove metadata operate
exclusively on Core-inherent keys:

| Transform | Adds | Removes |
|---|---|---|
| PrecondElim | `propertyType` | `propertySummary` |
| ProcedureInlining | `relatedFileRange` (via `setCallSiteFileRange`) | replaces `provenance` |
| CoreTransform | `relatedFileRange` (via `setCallSiteFileRange`) | replaces `provenance` |
| CmdEval | `.var` + `.expr` on havoc'd variables | — |
| ProcedureEval | `.label` + `.expr`/`.msg` on free postconditions | — |

No transform currently introduces keys meaningful only to itself. The
dialect-prefixed namespace convention is a **forward-looking design
provision** — it handles the case when it arises (e.g., a future pass
wants to tag statements with its own bookkeeping), but is not a launch
requirement. At launch, only Core-inherent keys need validation
infrastructure.

**Typo detection**: Optionally, the parser may emit a warning for unknown
unprefixed keys that are edit-distance ≤ 2 from an inherent key. This is
a refinement for later, not a launch blocker.

## Pretty-Printing / Emission Changes

### Step 5: Tag-based annotation filter

The pretty-printer carries a filter configuration:

```lean
inductive MetadataAnnFilter where
  | none                    -- Emit no annotations (default, preserves existing behavior)
  | all                     -- Emit all metadata as annotations
  | only (keys : Std.HashSet String)  -- Emit only these keys
  | allExcept (keys : Std.HashSet String)  -- Emit all except these keys
```

Convenience presets:
- `checks`: `only {"reachCheck", "fullCheck", "validityCheck", "satisfiabilityCheck"}`
- `properties`: checks + `{"propertyType", "propertySummary"}`
- `full`: `all`

Default filter: `none` (existing behavior preserved — no annotations printed
unless explicitly requested).

### Step 6: MetaData-to-Annotations rendering

In the Core pretty-printer, add a function that selects and formats
metadata entries based on the active filter:

```lean
def MetaData.toAnnotationEntries (md : MetaData P) (filter : MetadataAnnFilter)
    : List (String × Option MetadataAnnValue)
```

When `filter = .none`, this returns `[]` and the grammar emits `none`
for `Option MetadataAnn` (rendering as empty string).

### Step 7: Parsing direction (Annotations → MetaData)

When parsing `@[...]` entries:
1. For inherent keys: validate value form, construct the appropriate
   `MetaDataElem` with correct `Field` and `Value` variants.
2. For discardable keys: store as `(.label key, value)` with the value
   mapped from the grammar form.
3. For provenance strings: parse the structured format back to
   `Provenance.loc` or `Provenance.synthesized`.

## Migration

### Step 8: Update all existing `reachCheck` usage sites

Grep for `reachCheck` in:
- `FormatCore.lean`: Replace `ReachCheck` CST construction with
  `MetadataAnn` construction
- `Translate.lean`: Replace `translateOptionReachCheck` with generic
  annotation-list translation
- Test `.st` files that use `@[reachCheck] assert ...` (surface syntax
  unchanged, but verify they parse)
- The DDM `ofAst` / `toAst` round-trip logic

Each site switches from `some (reachCheck ())` to the new annotation
dictionary containing `mdAnnFlag "reachCheck"`.

### Step 9: Regenerate editor syntax

Per the comment at the top of Grammar.lean:
```
lake env lean --run editors/GenSyntax.lean all
```

## Testing

- Round-trip tests: parse `@[reachCheck] assert e;` → AST → pretty-print → same text.
- Multi-entry: `@[fullCheck, propertyType = "divisionByZero"] assert e;`
- Empty annotations: plain `assert e;` still works.
- Provenance round-trip: `@[provenance = "file.st:10:3-15:7"]` → MetaData → emit → same.
- Synthesized provenance: `@[provenance = "<synthesized:loopUnrolling>"]` round-trips.
- relatedFileRange order preservation across parse-print cycles.
- Discardable key acceptance: `@[x_custom = "hello"] assert e;` parses without error.
- Inherent key validation: `@[reachCheck = "foo"]` produces a parse error.
- Verify existing `.st` test files still parse after ReachCheck removal.
- Tag-based filter: print with `only {"reachCheck"}` shows only that annotation.

## Open Questions

1. Should the filter be exposed as a CLI flag (e.g., `--meta=checks`,
   `--meta=all`, `--meta=reachCheck,provenance`)? Starting with a config
   field in the printer options; CLI exposure follows.
2. Should expression-valued annotations be supported at launch, or deferred
   until there's a concrete use case? Deferring is lower risk.
3. Edit-distance typo warnings: implement now or later?

---

## Implementation Context (for handoff to another session)

### Current state (2026-06-30)

**Branch**: `shilpi/meta-annotations`

**Commits**:
- `667bdad`: Grammar — added MetadataAnn categories/ops, removed ReachCheck,
  added `annots : Option MetadataAnn` to `assert`/`cover`/`assume`.
- `dea7fe7`: Translate + FormatCore — `translateMetadataAnnKey`,
  `translateMetadataAnnEntry`, `translateOptMetadataAnn`; `metadataElemToEntry`,
  `metadataToAnn`; `translateLabeledCheck` uses annotations.
- `0e6dd83`: Extend to all statements, fix paren/spacing, add filter.

**Uncommitted changes (2026-06-30)**: Extend `Option MetadataAnn` to all Commands.

All statement ops and all command ops now take `annots : Option MetadataAnn`
as first arg with `:0` precedence in format strings. The `mdAnn` format is
`"@[" entries "] "` (trailing space). The DDM framework's `Option` paren
wrapping is suppressed by `:0`.

**Key design decision**: We use `Option MetadataAnn` (not a custom
`OptMetadataAnn` category). The original paren/spacing bug was caused by
missing `:0` precedence annotations, not by `Option` itself. Using `Option`
gives us the DDM framework's native handling for parsing (position tracking,
empty match), which avoids issues with zero-width ops at the command level.

### Tag-based filter

`MetadataAnnFilter` in FormatCore.lean controls emission:
- `.none` — emit nothing (default, preserves existing behavior)
- `.all` — emit all metadata as annotations
- `.only keys` — emit only listed keys
- `.allExcept keys` — emit all except listed keys

Presets: `.checks`, `.properties`. Threaded via `ToCSTContext.annFilter`.
`Core.formatProgram` accepts an `annFilter` parameter.

### Provenance behavior

Explicit `@[provenance = "..."]` annotations are **additive** — they do not
replace the DDM source-position provenance from `getOpMetaData`. Both entries
coexist in the metadata array:
```
@[provenance = ":4655-4712", provenance = "myfile.st:100-200"] assert [a1]: ...
```
The first entry is the DDM parser's byte-offset provenance; the second is the
user-supplied annotation parsed back to a `.provenance` value.

### What remains

- ~~**Fix the Option paren/spacing issue**~~ ✅ DONE — `:0` on all `annots`
  format references suppresses DDM paren wrapping.
- ~~**Implement tag-based filter**~~ ✅ DONE
- ~~**Extend to all Statement ops**~~ ✅ DONE
- ~~**Extend to Command-level ops**~~ ✅ DONE
- ~~**Provenance string parsing**~~ ✅ DONE — `parseProvenanceString` in
  Translate.lean parses `"path:start-stop"` and `"<synthesized:origin>"` back
  to `.provenance` values. Uses `ToFormat SynthesizedOrigin` as single source
  of truth for origin strings.
- ~~**Regenerate editor syntax**~~ ✅ No changes needed — annotation tokens
  (`@[`, `]`) are handled by the DDM parser's static patterns, not the
  dialect grammar.
- **Inherent key validation**: Deferred to typechecking (not parse time).
  Currently, misused keys (e.g., `@[reachCheck = "foo"]`) are silently
  stored as `.msg` — `hasReachCheck` won't find them, but no error is raised.

### Build commands (on Cloud Desktop)

```bash
cd /home/shilgoel/Code/StrataWS/src/Strata
git fetch origin && git checkout shilpi/meta-annotations && git pull
brazil-build release
```

### Key file locations

- Grammar: `Strata/Languages/Core/DDMTransform/Grammar.lean`
- Parser (CST→AST): `Strata/Languages/Core/DDMTransform/Translate.lean`
- Pretty-printer (AST→CST): `Strata/Languages/Core/DDMTransform/FormatCore.lean`
- MetaData definition: `Strata/DL/Imperative/MetaData.lean`
- Existing transforms that mutate metadata:
  - `Strata/Transform/PrecondElim.lean` (adds propertyType, erases propertySummary)
  - `Strata/Transform/ProcedureInlining.lean` (setCallSiteFileRange)
  - `Strata/Transform/CoreTransform.lean` (setCallSiteFileRange)
- Generated types: `CoreDDM` namespace at bottom of Grammar.lean (`#strata_gen Core`)
