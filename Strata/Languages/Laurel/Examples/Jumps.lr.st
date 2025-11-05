/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
val forLoopLikeWithBreakAndContinue = procedure(steps: int, continueSteps: int, exitSteps: int): int {
  var counter = 0
  breakLabel {
    while(steps > 0) 
      invariant counter >= 0
    {
      continueLabel {
        if (steps == exitSteps) {
          counter = -10;
          exit breakLabel;
        }
        if (steps == continueSteps) {
          exit continueLabel;
        }
        counter = counter + 1
      }
      steps = steps - 1;
    }
  }
  counter;
}