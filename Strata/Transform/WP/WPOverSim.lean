/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPOverList
public import Strata.Transform.WP.WPOverCmd
public import Strata.Transform.WP.WPOverExit
public import Strata.Transform.WP.WPOverBlock
public import Strata.Transform.WP.WPOverIte

/-! # The forward simulation of the WP walk

Every walk of a statement list or a statement has the simulation property (`Spec`), by
induction on the fragment from the cases of `WPOverList`, `WPOverCmd`, `WPOverExit`,
`WPOverBlock` and `WPOverIte`.

Key theorems: `listSpec_all`, `stmtSpec_all`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasBool P]
  [HasFvar P] [HasSubstFvar P] [HasIdent P] [LawfulHasIdent P] [Hashable P.Ident] [HasFvars P]
  [WPLang P] [HasOps P] [LawfulHasFvar P] [LawfulHasFvars P] [LawfulHasVal P]
variable {tE : TypedEval P}

mutual
/-- **Every statement-list walk simulates its list** (`ListSpec`).  For a well-formed factory,
    every walk of the WP phase over a statement list `ss` (reach context `κ`, depth `d`) that
    succeeds, from a well-formed walk state and under the scope, typing, freshness and label
    conditions of `Spec`, relates `ss` to the guarded output of the walk forward: with the
    loop-free store and the guarded store related before `ss`
    on the path the reach context selects (`OnInv`),
    an assertion or cover of `ss` failing there fails in the output, at a check of the same kind
    (`HitPost`); and when an obligation follows `ss`, a run of `ss` whose assumptions hold is
    matched by a run of the output whose assumptions hold and that ends related again
    (`RunPost`), except for an `exit` that ends the main list, and off the path (`OffInv`) every
    shadow run of `ss` is matched by a run of the output (`OffPost`). -/
theorem listSpec_all [WPIteLang P] {F : P.Factory} (hF : WellFormedSemanticEvalBase F)
    (Lc : List P.Ident) :
    ∀ (ss : PStmts P) (κ : RE P) (d : Nat) (fEnd : Bool), ListSpec F tE Lc κ d fEnd ss
  | [], κ, d, fEnd => listSpec_nil Lc κ d fEnd
  | s :: rest, κ, d, fEnd =>
    listSpec_cons hF (stmtSpec_all hF Lc s κ d) (stmtTyCtx Lc κ d s)
      (listSpec_all hF Lc rest κ d fEnd)
/-- **Every statement walk simulates its statement** (`StmtSpec`).  For a well-formed factory,
    every walk of the WP phase over one statement `s` (reach context `κ`, depth `d`) that
    succeeds, from a well-formed walk state and under the scope, typing, freshness and label
    conditions of `Spec`, relates `s` to the guarded output of the walk forward: with the
    loop-free store and the guarded store related before `s`
    on the path the reach context selects (`OnInv`), an
    assertion or cover of `s` failing there fails in the output, at a check of the same kind
    (`HitPost`); and when an obligation follows `s`, a run of `s` whose assumptions hold is matched
    by a run of the output whose assumptions hold and that ends related again (`RunPost`), except
    for an `exit` that ends the main list, and off the path (`OffInv`) every shadow run of `s` is
    matched by a run of the output (`OffPost`). -/
theorem stmtSpec_all [WPIteLang P] {F : P.Factory} (hF : WellFormedSemanticEvalBase F)
    (Lc : List P.Ident) :
    ∀ (s : PStmt P) (κ : RE P) (d : Nat) (f : Bool), StmtSpec F tE Lc κ d f s
  | .cmd c, κ, d, f => stmtSpec_cmd hF Lc κ d f c
  | .exit l md, κ, d, f => stmtSpec_exit hF Lc κ d f l md
  | .block _ b md, _, d, f => stmtSpec_block hF md (listSpec_all hF Lc b · (d + 1) f)
  | .ite (.det _) t e md, _, d, _ =>
    stmtSpec_ite hF md (listSpec_all hF Lc t · d) (listSpec_all hF Lc e · d)
  | .ite .nondet .., κ, d, f | .loop .., κ, d, f | .typeDecl .., κ, d, f =>
    stmtSpec_other Lc κ d f _ ⟨nofun, nofun, nofun, nofun⟩
end

end -- public section

end WP
end Imperative
