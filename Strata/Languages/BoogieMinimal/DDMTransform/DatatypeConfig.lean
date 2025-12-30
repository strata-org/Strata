/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST

namespace Strata

/--
Configuration for BoogieMinimal datatype encoding.
Unlike Boogie which uses boolean testers, BoogieMinimal uses integer indexers.
This configuration is shared between Parse.lean (DDM annotation) and Translate.lean.
-/
structure BoogieMinimalDatatypeConfig where
  /-- Pattern for indexer function names: datatype$idx$<constructor> -/
  indexerPattern : Array NamePatternPart := #[.datatype, .literal "$idx$", .constructor]
  deriving Repr, Inhabited

/-- Default BoogieMinimal datatype configuration -/
def defaultBoogieMinimalDatatypeConfig : BoogieMinimalDatatypeConfig := {}

/-- Build the indexer function template from the config -/
def BoogieMinimalDatatypeConfig.indexerTemplate (config : BoogieMinimalDatatypeConfig) : FunctionTemplate :=
  { scope := .perConstructor
    namePattern := config.indexerPattern
    paramTypes := #[.datatype]
    returnType := .builtin "int" }

/-- Get all function templates from the config (only indexer, no field accessors) -/
def BoogieMinimalDatatypeConfig.functionTemplates (config : BoogieMinimalDatatypeConfig) : Array FunctionTemplate :=
  #[config.indexerTemplate]

end Strata
