/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Python.TypeCheck.AbstractType
public import Strata.Languages.Python.Specs.DDM

/-!
# Spec Environment for On-Demand PySpec Loading

Provides `ModuleSpec` (a parsed module's exports) and `SpecEnv` (a cache of
loaded modules), plus helpers to convert PySpec types into the analysis-level
`AbstractType` lattice.
-/

public section
namespace Strata.Python.TypeCheck

open Strata.Python (PythonIdent)
open Strata.Python.Specs

/-! ## Builtin type mapping -/

private def builtinIdentMap : Std.HashMap PythonIdent AbstractType :=
  .ofList [
    (.builtinsInt, .int),
    (.builtinsStr, .str),
    (.builtinsBool, .bool),
    (.builtinsFloat, .float),
    (.builtinsBytes, .bytes),
    (.noneType, .none),
    (.typingAny, .any (.unknown "typing.Any"))
  ]

def resolveIdent (id : PythonIdent) : AbstractType :=
  builtinIdentMap.getD id (.instance_ s!"{id.pythonModule}.{id.name}")

/-! ## SpecType → AbstractType conversion -/

partial def specAtomToAbstract : SpecAtomType → AbstractType
  | .ident id _ => resolveIdent id
  | .intLiteral v => .literal (.int v)
  | .stringLiteral v => .literal (.str v)
  | .typedDict .. => .instance_ "TypedDict"

def specTypeToAbstract (st : SpecType) : AbstractType :=
  match st.asSingleton with
  | some atom => specAtomToAbstract atom
  | none =>
    if st.atoms.size > 1 then
      AbstractType.joinAll (st.atoms.map specAtomToAbstract)
    else .any (.unknown "unrecognized spec type")

/-! ## Module exports -/

/-- A group of function signatures sharing the same name.
    Overloads whose first positional parameter has a `Literal["..."]` type are
    indexed by that string in `byFirstArg` for O(1) dispatch.  All other
    signatures (non-overloaded, or overloaded without a literal first param)
    go into `fallbacks`. -/
structure FunctionGroup where
  byFirstArg : Std.HashMap String Specs.FunctionDecl := {}
  fallbacks  : Array Specs.FunctionDecl := #[]
deriving Inhabited

namespace FunctionGroup

def singleton (d : Specs.FunctionDecl) : FunctionGroup :=
  match firstArgLiteral? d with
  | some key => { byFirstArg := .ofList [(key, d)] }
  | none     => { fallbacks := #[d] }
where
  firstArgLiteral? (d : Specs.FunctionDecl) : Option String :=
    if !d.isOverload then none
    else do
      let arg ← d.args.args[0]?
      let atom ← arg.type.asSingleton
      match atom with
      | .stringLiteral s => some s
      | _ => none

def push (g : FunctionGroup) (d : Specs.FunctionDecl) : FunctionGroup :=
  match FunctionGroup.singleton.firstArgLiteral? d with
  | some key => { g with byFirstArg := g.byFirstArg.insert key d }
  | none     => { g with fallbacks := g.fallbacks.push d }

/-- Look up the best-matching overload for a call whose first positional arg
    has the given `AbstractType`.  O(1) when the arg is a string literal. -/
def resolve (g : FunctionGroup) (firstArgType : AbstractType)
    : Option Specs.FunctionDecl :=
  match firstArgType with
  | .literal (.str key) => g.byFirstArg.get? key |>.or g.fallbacks[0]?
  | _ => g.fallbacks[0]?

def single? (g : FunctionGroup) : Option Specs.FunctionDecl :=
  if g.byFirstArg.isEmpty && g.fallbacks.size == 1 then g.fallbacks[0]?
  else none

end FunctionGroup

/-- A single named export from a Python module's PySpec file.
    The `exports` map in `ModuleSpec` holds one `ModuleExport` per name. -/
inductive ModuleExport where
  /-- A class with methods, fields, and an optional `exhaustive` flag. -/
  | classDef      (d : ClassDef)
  /-- One or more function signatures sharing the same name, indexed for
      efficient overload dispatch.  See `FunctionGroup`. -/
  | functionGroup (g : FunctionGroup)
  /-- A module-level type alias (e.g. `pi: float`). -/
  | typeDef       (t : SpecType)
  /-- A re-export that refers to a type defined in another module. -/
  | externType    (source : PythonIdent)
deriving Inhabited

structure ModuleSpec where
  exports : Std.HashMap String ModuleExport := {}
deriving Inhabited

namespace ModuleSpec

def ofSignatures (sigs : Array Signature) : ModuleSpec :=
  let m := sigs.foldl (init := ({}  : Std.HashMap String ModuleExport)) fun m sig =>
    match sig with
    | .classDef d => m.insert d.name (.classDef d)
    | .functionDecl d =>
      match m.get? d.name with
      | some (.functionGroup g) =>
        m.insert d.name (.functionGroup (g.push d))
      | _ => m.insert d.name (.functionGroup (.singleton d))
    | .typeDef d => m.insert d.name (.typeDef d.definition)
    | .externTypeDecl name source => m.insert name (.externType source)
  { exports := m }

/-- Build a `FunctionGroup` from a class's method array (which may contain
    multiple overloads with the same name). -/
def methodGroup (methods : Array Specs.FunctionDecl) (name : String) : FunctionGroup :=
  methods.foldl (init := ({} : FunctionGroup)) fun g m =>
    if m.name == name then g.push m else g

end ModuleSpec

/-! ## Spec environment (cache) -/

structure SpecEnv where
  cache : Std.HashMap String (Option ModuleSpec) := {}
deriving Inhabited

namespace SpecEnv

def empty : SpecEnv := {}

def get? (env : SpecEnv) (modName : String) : Option (Option ModuleSpec) :=
  env.cache.get? modName

def insert (env : SpecEnv) (modName : String) (ms : Option ModuleSpec) : SpecEnv :=
  { cache := env.cache.insert modName ms }

end SpecEnv

end Strata.Python.TypeCheck
end -- public section
