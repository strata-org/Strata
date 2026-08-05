/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Pipeline.Messages

namespace Strata.Pipeline

/-- Stamp a phase-independent `Message` with a `Phase` to produce a
    `PipelineMessage`. -/
public def PipelineMessage.fromMessage (phase : Phase) (m : Message) : PipelineMessage :=
  { phase, message := m }

/-- Stamp a list of `Message` values with a `Phase`. -/
public def PipelineMessage.fromMessages (phase : Phase) (ms : List Message)
    : Array PipelineMessage :=
  ms.toArray.map (PipelineMessage.fromMessage phase)

end Strata.Pipeline
