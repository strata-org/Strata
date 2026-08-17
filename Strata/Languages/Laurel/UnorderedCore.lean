/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
public import Strata.Languages.Laurel.LaurelAST
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator

namespace Strata.Laurel

open Std (Format ToFormat)
/--
An intermediate representation produced by the transparency pass.
Functions are pure computational procedures (suffixed `$asFunction`);
coreProcedures are the original procedures with any free postconditions
embedded in their `Body.Opaque` postcondition lists.
-/
public structure UnorderedCoreWithLaurelTypes where
  functions : List Procedure
  coreProcedures : List Procedure
  datatypes : List DatatypeDefinition
  /-- Opaque (natively implemented) types. Kept separate from `datatypes` because they
      lower to a different Core declaration (`TypeDecl.con`, not `.data`) and, having no
      constructor arguments, cannot participate in a dependency cycle. -/
  opaqueTypes : List OpaqueTypeDefinition := []
  constants : List Constant

public def formatUnorderedCoreWithLaurelTypes (p : UnorderedCoreWithLaurelTypes) : Format :=
  let opaqueFmts := p.opaqueTypes.map ToFormat.format
  let datatypeFmts := p.datatypes.map ToFormat.format
  let constantFmts := p.constants.map ToFormat.format
  let functionFmts := p.functions.map ToFormat.format
  let procFmts := p.coreProcedures.map ToFormat.format
  Format.joinSep (opaqueFmts ++ datatypeFmts ++ constantFmts ++ functionFmts ++ procFmts) "\n\n"

public instance : ToFormat UnorderedCoreWithLaurelTypes where
  format := formatUnorderedCoreWithLaurelTypes
