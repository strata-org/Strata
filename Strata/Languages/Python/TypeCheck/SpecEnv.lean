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

inductive ModuleExport where
  | classDef    (d : ClassDef)
  | functionDecl (d : Specs.FunctionDecl)
  | typeDef     (t : SpecType)
  | externType  (source : PythonIdent)
deriving Inhabited

structure ModuleSpec where
  exports : Std.HashMap String ModuleExport := {}
deriving Inhabited

namespace ModuleSpec

def ofSignatures (sigs : Array Signature) : ModuleSpec :=
  let m := sigs.foldl (init := ({}  : Std.HashMap String ModuleExport)) fun m sig =>
    match sig with
    | .classDef d => m.insert d.name (.classDef d)
    | .functionDecl d => m.insert d.name (.functionDecl d)
    | .typeDef d => m.insert d.name (.typeDef d.definition)
    | .externTypeDecl name source => m.insert name (.externType source)
  { exports := m }

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
