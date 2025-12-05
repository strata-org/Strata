/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/
procedure whileWithBreakAndContinue(steps: int, continueSteps: int, exitSteps: int): int {
  var counter = 0
  {
    while(steps > 0) 
      invariant counter >= 0
    {
      {
        if (steps == exitSteps) {
          counter = -10;
          exit breakBlock;
        }
        if (steps == continueSteps) {
          exit continueBlock;
        }
        counter = counter + 1;
      } continueBlock;
      steps = steps - 1;
    }
  } breakBlock;
  counter;
}


/*
Translation towards SMT:

proof whileWithBreakAndContinue_body() {
  var steps: int;
  var continueSteps: int;
  var exitSteps: int;

  var counter = 0;
  
  label loopStart;
  assert counter >= 0;
  if (steps > 0) {
    if (steps == exitSteps) {
      counter = -10;
      goto breakLabel;
    }
    if (steps == continueSteps) {
      goto continueLabel;
    }
    counter = counter + 1;
    label continueLabel;
    steps = steps - 1;
    goto loopStart;
  }
  label breakLabel;
  counter;
}


*/