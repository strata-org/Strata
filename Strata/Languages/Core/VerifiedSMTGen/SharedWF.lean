/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.Languages.Core.VerifiedSMTGen.SMTEncoder
import all Strata.Languages.Core.VerifiedSMTGen.SMTEncoder

/-!
# Refactored SMT encoder — shared name-hygiene well-formedness (collect ⊳ translate)

The `uAT`-dependent, encoder-aware name preconditions that both phases touch: `collect_WF` establishes
`CoreCtx.NamesWF`, `translateQuery_WF` consumes it. Homed here (downstream of the encoder, upstream of
both phase-soundness files) so neither phase depends on the other — `corePredefinedOpToSMTOp` stays in
the encoder, and the collect ⊳ translate edge is severed.
-/

open Core Lambda Imperative Strata.SMT Std

namespace Core.Refactor

/-- **Well-formedness of the function context `Ψ`** — every user-function name, after demangling, is NOT
    a predefined operator, so `translateAppHead` routes it to the UF branch instead of a built-in. -/
def FnNamesNotPredefined (Ψ : FnCtx) (useArrayTheory : Bool) : Prop :=
  ∀ nm ∈ Ψ.map Prod.fst,
    corePredefinedOpToSMTOp useArrayTheory (CoreOp.ofString (Core.NameMangling.demangledBaseName nm)) = none

/-- **SMT-translation name preconditions of a collected `CoreCtx`** — the name-side conditions `translate`
    needs, which (unlike the source `CoreCtx.WF`) are SMT-specific: all declared/defined names are distinct
    and none collides with the reserved `$__bv{n}` binder prefix, and every user-function name demangles to
    a non-predefined operator so `translateAppHead` routes it to a UF (not a builtin). `uAT`-dependent (via
    `FnNamesNotPredefined`), hence homed here rather than in the `uAT`-free `VerifiedSMTGen.CoreCtx`. -/
structure CoreCtx.NamesWF (cctx : CoreCtx) (useArrayTheory : Bool) : Prop where
  names_nodup : ((cctx.toΨ ++ cctx.toΦ).map Prod.fst).Nodup
  names_no_reserved : ∀ n : Nat, s!"$__bv{n}" ∉ (cctx.toΨ ++ cctx.toΦ).map Prod.fst
  fnNamesNotPredefined : FnNamesNotPredefined cctx.toΨ useArrayTheory

end Core.Refactor
