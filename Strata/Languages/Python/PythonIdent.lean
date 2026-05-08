/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public section
namespace Strata.Python

abbrev ModuleComponent := { nm : String // nm ≠ "" }

/--
A Python module name split into its dot-separated components.
For example, `typing.List` has components `["typing", "List"]`.
The size constraint ensures at least one component exists.
-/
structure ModuleName where
  private mk ::
  private componentsM : Array ModuleComponent
  private componentsSizePos : componentsM.size > 0
  deriving DecidableEq, Hashable, Ord

namespace ModuleName

instance : LT ModuleName where
  lt a b := compare a b == .lt

instance (a b : ModuleName) : Decidable (a < b) :=
  inferInstanceAs (Decidable (compare a b == .lt))

instance : Inhabited ModuleName where
  default := private {
    componentsM := #[⟨"placeholder", by simp⟩],
    componentsSizePos := by simp
  }

def components (m : ModuleName) : Array String :=
  m.componentsM.unattach

private
def ofStringAux (mod : String) (a : Array ModuleComponent) (start cur : mod.Pos) : Option ModuleName :=
  if h : cur.IsAtEnd then
    let r := mod.extract start cur
    if ne : r = "" then
      .none
    else
      some {
        componentsM := a.push ⟨r, ne⟩
        componentsSizePos := by simp
      }
  else
    let c := cur.get h
    if _ : c = '.' then
      let r := mod.extract start cur
      if ne : r = "" then
        .none
      else
        let next := cur.next h
        ofStringAux mod (a.push ⟨r, ne⟩) next next
    else
      let next := cur.next h
      ofStringAux mod a start next
  termination_by cur

/-- Parses a dot-separated module name string (e.g., "typing.List"). -/
def ofString? (mod : String) : Option ModuleName :=
  ofStringAux mod #[] mod.startPos mod.startPos

/--
Parses a dot-separated module name string (e.g., "typing.List")
and panics if parsing fails.
-/
def ofString! (mod : String) : ModuleName :=
  match ofStringAux mod #[] mod.startPos mod.startPos with
  | .some m => m
  | .none => panic! "Malformed module {mod}" -- nopanic:ok

/-- Convert a module name to a string, joining components with `sep` (default `"."`). -/
protected def toString (m : ModuleName) (sep : String := ".") : String :=
  let p : m.componentsM.size > 0 := m.componentsSizePos
  m.componentsM.foldl (init := m.componentsM[0]) (start := 1) fun a m =>
    a ++ sep ++ m.val

instance : ToString ModuleName where
  toString m := m.toString

theorem components_size_pos (m : ModuleName) : m.components.size > 0 := by
  simp [ModuleName.components]
  exact m.componentsSizePos

/-- The last component of the module name. E.g., `"typing.List"` → `"List"`. -/
def back (m : ModuleName) : String :=
  let p := m.componentsSizePos
  m.componentsM.back.val

/-- Drop the last `n` components. Returns `none` if fewer than `n` components remain. -/
def parent (m : ModuleName) (n : Nat := 1) : Option ModuleName :=
  let c := m.componentsM.toSubarray (stop := m.componentsM.size - n) |>.toArray
  if h : c.size > 0 then
    some ⟨c, h⟩
  else
    none

/-- Create a single-component module name. -/
def ofComponent (c : ModuleComponent) : ModuleName :=
  ⟨#[c], by simp⟩

/-- Append a component to the end. E.g., `"typing".push "List"` → `"typing.List"`. -/
def push (m : ModuleName) (c : ModuleComponent) : ModuleName :=
  ⟨m.componentsM.push c, by simp⟩

/-- Concatenate two module names. E.g., `"a.b" ++ "c.d"` → `"a.b.c.d"`. -/
def append (m1 m2 : ModuleName) : ModuleName :=
  ⟨m1.componentsM ++ m2.componentsM, by have p := m1.componentsSizePos; grind⟩

instance : HAppend ModuleName ModuleName ModuleName where
  hAppend := append

instance : Repr ModuleName where
  reprPrec m prec := Repr.addAppParen s!"Stata.ModuleName.ofString! {m}" prec

end ModuleName

/--
A fully-qualified Python identifier consisting of a module path and a name.
For example, `typing.List` has module "typing" and name "List".
-/
structure PythonIdent where
  mkRaw ::
  pythonModule : ModuleName
  name : String
  deriving DecidableEq, Hashable, Ord, Repr

namespace PythonIdent

instance : Inhabited PythonIdent where
  default := {
    pythonModule := default
    name := "default"
  }

/-- Construct from a single-component module name. Compile-time error if `mod` is empty. -/
def ofComponent (mod : String) (name : String) (h : mod ≠ "" := by decide) : PythonIdent :=
  { pythonModule := .ofComponent ⟨mod, h⟩, name }

protected def ofString (s : String) : Option PythonIdent := do
  let idx ← s.revFind? '.'
  let m ← ModuleName.ofString? (s.extract s.startPos idx)
  some {
    pythonModule := m
    name := s.extract idx.next! s.endPos
  }

instance : ToString PythonIdent where
  toString i := s!"{i.pythonModule}.{i.name}"

end PythonIdent

end Strata.Python
end
