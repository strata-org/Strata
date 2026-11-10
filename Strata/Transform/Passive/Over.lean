/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPProps
public import Strata.Transform.SSA.SSAProps

/-! # Properties of the WP and SSA phases together

The SSA output of a WP output has the shape and the well-scopedness of an obligation program
(`wpSSA_shape`, `wpSSA_wellScoped`).

Key theorems: `wpSSA_shape`, `wpSSA_wellScoped`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iBE : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iHB : HasBool P] [iHF : HasFvar P] [iSF : HasSubstFvar P] [iHI : HasIdent P]
  [iLI : LawfulHasIdent P] [iHa : Hashable P.Ident] [iHFs : HasFvars P] [iWL : WPLang P]
  [iOp : HasOps P] [iLF : LawfulHasFvar P] [iLFs : LawfulHasFvars P] [iLV : LawfulHasVal P]

/-! ## The obligation program -/

omit iLI iOp iLF iLFs iLV in
/-- **Structural shape of the obligation program**: the SSA output of a WP output is in tree form
    (`Block.treeForm`: every `ite *` last in its list, no loop), has only `assert`s and `cover`s
    after every `assert` (`Block.onlyChecksAfterAssert`), and has no loop at any depth
    (`Block.noLoops`). -/
theorem wpSSA_shape {Gw Gs : IdSet P} {tys : Tys P} {xs : List P.Ident}
    {al : List (P.Ident × P.Ident)} {ss : PStmts P} {w : WOut P}
    (hw : wpEntry Gw tys ss = .ok w) {ρ0 : Ren P} {so : SOut P}
    (hs : ssaEntry Gs tys xs al w.lay = .ok (ρ0, so)) :
    Block.treeForm so.out = true ∧ Block.onlyChecksAfterAssert so.out = true ∧
      Block.noLoops so.out = true :=
  let h := ssaBody_shape (wpBody_shape hw).1 (wpBody_shape hw).2 (ssaEntry_ok hs).2
  ⟨h.1, h.2.1, h.2.2.2⟩

/-- **Well-scopedness of the obligation program**: the SSA output of the WP output of a
    well-scoped list whose free variables are names of `xs` or of the aliases `al` (each
    `(a, x)` with `x` in `xs`) is syntactically well scoped from the entry names. -/
theorem wpSSA_wellScoped {Gw Gs : IdSet P} {tys : Tys P} {xs : List P.Ident}
    {al : List (P.Ident × P.Ident)} {ss : PStmts P} {w : WOut P}
    (hw : wpEntry Gw tys ss = .ok w) {ρ0 : Ren P} {so : SOut P}
    (hs : ssaEntry Gs tys xs al w.lay = .ok (ρ0, so)) (hal : ∀ q ∈ al, q.2 ∈ xs)
    {Lc S : List P.Ident} (hwf : Block.WellScoped Lc S ss)
    (hfv : ∀ x ∈ Block.freeVars ss, x ∈ xs ∨ x ∈ al.map (·.1)) :
    Block.readsDefined (ρ0.map (·.2)) so.out = true :=
  ssaEntry_wellScoped hs hal fun x hx => hfv x (wpEntry_fv hw hwf x hx)

end -- public section

end WP
end Imperative
