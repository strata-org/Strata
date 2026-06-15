/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Axiom audit for the general body transport.  `#print axioms` cannot run under a
-- `module` header, so this non-module file imports the body-transport module and
-- prints the axiom dependencies of `Block.bodyTransport` and the supporting
-- relation/structural lemmas.  A clean result is
-- `[propext, Classical.choice, Quot.sound]` with NO `sorryAx`.
import Strata.Transform.LoopInitHoistBodyTransport

-- The general body transport: BodyTransport derivation → BodySimE.
#print axioms Imperative.LoopInitHoistBodyTransport.Block.bodyTransport
-- The body-transport correspondence relation.
#print axioms Imperative.LoopInitHoistBodyTransport.BodyTransport
-- Structural facts consumed by the transport.
#print axioms Imperative.LoopInitHoistBodyTransport.BodyTransport.src_no_exit
#print axioms Imperative.LoopInitHoistBodyTransport.BodyTransport.noFuncDecl_src
#print axioms Imperative.LoopInitHoistBodyTransport.BodyTransport.noFuncDecl_h
