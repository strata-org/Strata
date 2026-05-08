/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public section
namespace Strata.Python

abbrev ModuleComponent := { nm : String // nm ≠ "" }

def ModuleComponent.ofString (s : String) (h : s ≠ "" := by decide) : ModuleComponent := ⟨s, h⟩

/--
A Python module name split into its dot-separated components.
For example, `typing.List` has components `["typing", "List"]`.
The size constraint ensures at least one component exists.
-/
structure ModuleName where
  mk ::
  components : Array ModuleComponent
  components_size_pos : components.size > 0
  deriving DecidableEq, Hashable, Ord

namespace ModuleName

instance : LT ModuleName where
  lt a b := compare a b == .lt

instance (a b : ModuleName) : Decidable (a < b) :=
  inferInstanceAs (Decidable (compare a b == .lt))

instance : Inhabited ModuleName where
  default := private {
    components := #[⟨"placeholder", by simp⟩],
    components_size_pos := by simp
  }


private
def ofStringAux (mod : String) (a : Array ModuleComponent) (start cur : mod.Pos) : Option ModuleName :=
  if h : cur.IsAtEnd then
    let r := mod.extract start cur
    if ne : r = "" then
      .none
    else
      some {
        components := a.push ⟨r, ne⟩
        components_size_pos := by simp
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
  let p : m.components.size > 0 := m.components_size_pos
  m.components.foldl (init := m.components[0]) (start := 1) fun a m =>
    a ++ sep ++ m.val

instance : ToString ModuleName where
  toString m := m.toString

/-- The last component of the module name. E.g., `"typing.List"` → `"List"`. -/
def back (m : ModuleName) : String :=
  let p := m.components_size_pos
  m.components.back.val

/-- Drop the last `n` components. Returns `none` if fewer than `n` components remain. -/
def parent (m : ModuleName) (n : Nat := 1) : Option ModuleName :=
  let c := m.components.toSubarray (stop := m.components.size - n) |>.toArray
  if h : c.size > 0 then
    some ⟨c, h⟩
  else
    none

/-- Create a single-component module name. -/
def ofComponent (c : ModuleComponent) : ModuleName :=
  ⟨#[c], by simp⟩

/-- Append a component to the end. E.g., `"typing".push "List"` → `"typing.List"`. -/
def push (m : ModuleName) (c : ModuleComponent) : ModuleName :=
  ⟨m.components.push c, by simp⟩

/-- Concatenate two module names. E.g., `"a.b" ++ "c.d"` → `"a.b.c.d"`. -/
def append (m1 m2 : ModuleName) : ModuleName :=
  ⟨m1.components ++ m2.components, by have p := m1.components_size_pos; grind⟩

instance : HAppend ModuleName ModuleName ModuleName where
  hAppend := append

instance : Repr ModuleName where
  reprPrec m prec := Repr.addAppParen s!"Stata.ModuleName.ofString! {m}" prec

/--
Result of parsing a Python file path into a module name.
`isInit` indicates whether the file is a package `__init__.py`.
-/
structure ModuleOfPath where
  moduleName : ModuleName
  isInit : Bool

namespace ModuleOfPath

/-- The package prefix for relative import resolution.
    For `__init__.py` files, this is the full module name's components.
    For regular files, this is the module name minus the last component (may be empty). -/
def modulePrefix (m : ModuleOfPath) : Array ModuleComponent :=
  if m.isInit then
    m.moduleName.components
  else
    m.moduleName.components.toSubarray (stop := m.moduleName.components.size - 1) |>.toArray

end ModuleOfPath

/-- Derive a `ModuleName` from a file path relative to a search root.

    Examples:
      "module.py"               → .ok { moduleName := "module",             isInit := false }
      "service/__init__.py"     → .ok { moduleName := "service",            isInit := true  }
      "service/sub/module.py"   → .ok { moduleName := "service.sub.module", isInit := false }
      "service/sub/__init__.py" → .ok { moduleName := "service.sub",        isInit := true  }

    Fails if the path doesn't end in `.py` or would produce an empty component. -/
def ofRelativePath (relativePath : System.FilePath) : Except String ModuleOfPath := do
  let pathStr := relativePath.toString
  let parts := pathStr.splitOn "/"
  let some last := parts.getLast?
    | throw s!"empty path: {relativePath}"
  let (stems, isInit) ←
    if last == "__init__.py" then
      pure (parts.dropLast, true)
    else if last.endsWith ".py" then
      pure (parts.dropLast ++ [last.dropEnd 3 |>.toString], false)
    else
      throw s!"path does not end in .py: {relativePath}"
  let mut components : Array ModuleComponent := #[]
  for s in stems do
    if h : s = "" then
      throw s!"empty component in path: {relativePath}"
    else
      components := components.push ⟨s, h⟩
  if h : components.size > 0 then
    .ok { moduleName := ⟨components, h⟩, isInit }
  else
    throw s!"no module components in path: {relativePath}"

private def testOfRelativePath (path : String) (expectedMod : String) (expectedInit : Bool) : Bool :=
  match ofRelativePath path with
  | .ok info => info.moduleName.toString == expectedMod && info.isInit == expectedInit
  | .error _ => false

#guard testOfRelativePath "module.py" "module" false
#guard testOfRelativePath "service/__init__.py" "service" true
#guard testOfRelativePath "service/sub/module.py" "service.sub.module" false
#guard testOfRelativePath "service/sub/__init__.py" "service.sub" true
#guard match ofRelativePath "readme.txt" with | .error _ => true | .ok _ => false
#guard match ofRelativePath "__init__.py" with | .error _ => true | .ok _ => false

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

/-- Convert to a string, joining module components and name with `sep` (default `"."`). -/
protected def toString (i : PythonIdent) (sep : String := ".") : String :=
  i.pythonModule.toString sep ++ sep ++ i.name

instance : ToString PythonIdent where
  toString := PythonIdent.toString

end PythonIdent

end Strata.Python
end
