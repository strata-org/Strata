/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
public import Strata.DDM.AST
import all Strata.DDM.Util.Array

public section
namespace Strata

/--
Array ofelements whose sizes are bounded by a value.
-/
public abbrev SizeBounded (α : Type _) [SizeOf α] {β} [SizeOf β] (e : β) (c : Int) := { a : α // sizeOf a ≤ sizeOf e + c }

namespace ExprF

/--
Head-normal form for an expression consists of an operation
-/
structure HNF {α} (e : ExprF α) where
  fn : ExprF α
  args : SizeBounded (Array (ArgF α)) e 1

protected def hnf {α} (e0 : ExprF α) : HNF e0 :=
  let rec aux (e : ExprF α) (args : Array (ArgF α) := #[])
              (szP : sizeOf e + sizeOf args ≤ sizeOf e0 + 2): HNF e0 :=
    match e with
    | .bvar .. | .fvar .. | .fn .. =>
      { fn := e, args := ⟨args.reverse, by simp at szP; simp; omega⟩ }
    | .app _ f a =>
      aux f (args.push a) (by simp at *; omega)
  aux e0 #[] (by simp)

end ExprF
end Strata
end
