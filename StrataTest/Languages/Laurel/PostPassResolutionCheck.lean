/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Pipeline.Messages
import Strata.Languages.Laurel.LaurelCompilationPipeline

open Strata Strata.Laurel

private def warn := Message.fromString "`old(...)` has no effect" .warning
private def err := Message.fromString "unresolved identifier" .userError
private def priorErr := Message.fromString "throws with two value outputs" .userError

#guard newPostPassResolutionErrors (.ofArray #[warn]) [warn] #[err] == #[err]
#guard newPostPassResolutionErrors {} [] #[err] == #[err]
#guard (newPostPassResolutionErrors (.ofArray #[warn]) [warn, priorErr] #[err]).isEmpty
#guard (newPostPassResolutionErrors (.ofArray #[err]) [] #[err]).isEmpty
#guard (newPostPassResolutionErrors (.ofArray #[warn]) [warn] #[warn]).isEmpty
#guard newPostPassResolutionErrors (.ofArray #[warn]) [warn] #[warn, err] == #[err]
