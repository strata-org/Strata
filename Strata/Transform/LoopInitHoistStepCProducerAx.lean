/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT

  Axiom audit (non-`module`, so `#print axioms` is permitted): confirms the
  Step-C producer `Block.bodyTransport_of_lift` and the updated body-transport
  driver `Block.bodyTransport` rest only on the Lean standard axioms.
-/
import Strata.Transform.LoopInitHoistStepCProducer

open Imperative LoopInitHoistStepCProducer LoopInitHoistBodyTransport

#print axioms Imperative.LoopInitHoistStepCProducer.Block.bodyTransport_of_lift
#print axioms Imperative.LoopInitHoistBodyTransport.Block.bodyTransport
-- The shape derivation: `transportShape` follows from the §E preconds + `noExit`.
#print axioms Imperative.LoopInitHoistStepCProducer.Block.transportShape_of_arm_preconds
