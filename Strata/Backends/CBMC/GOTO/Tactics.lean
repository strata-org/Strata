/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public section

/-! # GOTO backend tactic helpers -/

/-- `inj_subst h₁ h₂` closes the recurring boilerplate

```
have h_eq : x = y := Option.some.inj (h₁.symm.trans h₂)
subst h_eq
```

where `h₁ : f a = some x` and `h₂ : f a = some y`. After the macro
runs, `x` is substituted by `y` (or vice versa, depending on which
side `subst` picks as the local variable to eliminate). -/
macro "inj_subst" h1:ident h2:ident : tactic =>
  `(tactic| (
    have h_eq := Option.some.inj (Eq.trans (Eq.symm $h1) $h2)
    subst h_eq))

end
