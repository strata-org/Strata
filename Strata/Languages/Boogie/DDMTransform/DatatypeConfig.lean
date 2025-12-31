/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST

namespace Strata

/--
Configuration for Boogie datatype encoding.
Stores the naming patterns for tester and field accessor functions.
This configuration is shared between Parse.lean (DDM annotation) and Translate.lean.
-/
structure BoogieDatatypeConfig where
  /-- Pattern for tester function names: datatype..is<constructor> -/
  testerPattern : Array NamePatternPart := #[.datatype, .literal "..is", .constructor]
  /-- Pattern for field accessor names: <field> -/
  accessorPattern : Array NamePatternPart := #[.field]
  deriving Repr, Inhabited

/-- Default Boogie datatype configuration -/
def defaultDatatypeConfig : BoogieDatatypeConfig := {}

/-- Build the tester function template from the config -/
def BoogieDatatypeConfig.testerTemplate (config : BoogieDatatypeConfig) : FunctionTemplate :=
  { scope := .perConstructor
    namePattern := config.testerPattern
    paramTypes := #[.datatype]
    returnType := .builtin "bool" }

/-- Build the accessor function template from the config -/
def BoogieDatatypeConfig.accessorTemplate (config : BoogieDatatypeConfig) : FunctionTemplate :=
  { scope := .perField
    namePattern := config.accessorPattern
    paramTypes := #[.datatype]
    returnType := .fieldType }

/-- Get all function templates from the config -/
def BoogieDatatypeConfig.functionTemplates (config : BoogieDatatypeConfig) : Array FunctionTemplate :=
  #[config.testerTemplate, config.accessorTemplate]

end Strata
