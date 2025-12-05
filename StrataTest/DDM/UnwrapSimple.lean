/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST

open Strata

-- Test that UnwrapSpec exists and can be used
def testUnwrapSpec : UnwrapSpec := UnwrapSpec.nat

-- Test that SyntaxDefAtom.ident accepts unwrap parameter
def testSyntaxAtom : SyntaxDefAtom := SyntaxDefAtom.ident 0 0 (some UnwrapSpec.nat)

-- Test that it defaults to none
def testSyntaxAtomDefault : SyntaxDefAtom := SyntaxDefAtom.ident 0 0 none

#guard testSyntaxAtom != testSyntaxAtomDefault

-- Verify the structure
#guard match testSyntaxAtom with
  | SyntaxDefAtom.ident _ _ (some UnwrapSpec.nat) => true
  | _ => false
