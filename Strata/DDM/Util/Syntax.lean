/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

namespace Lean

theorem node_getelem (info : SourceInfo) (i : Nat) : (Syntax.node info kind args)[i] = args.getD i .missing := by
  simp [GetElem.getElem, Syntax.getArg]

theorem atom_getelem  (info : SourceInfo) (i : Nat) : (Syntax.atom info val)[i] = Syntax.missing := by
  simp [GetElem.getElem, Syntax.getArg]

theorem ident_getelem  (info : SourceInfo) (rv : Substring) (v : Name) (pre : List Syntax.Preresolved)
       (i : Nat) : (Syntax.ident info rv v pre)[i] = Syntax.missing := by
  simp [GetElem.getElem, Syntax.getArg]

def sizeOfSyntaxArgLt (stx : Syntax) (i : Nat)
      (nm : stx.getKind ≠ `missing) : sizeOf stx[i] < sizeOf stx := by
  cases stx with
  | missing =>
    simp [Syntax.getKind] at nm
  | node info kind args =>
    simp [node_getelem, Array.getD_getElem?]
    if p : i < args.size then
      simp [p]
      decreasing_trivial
    else
      simp [p]
      cases args; decreasing_trivial
  | atom info val =>
    simp [atom_getelem]
    cases val; decreasing_trivial
  | ident info rv v pre =>
    simp [ident_getelem]
    cases rv; decreasing_trivial

end Lean
