#!/usr/bin/env python3
# Copyright Strata Contributors
# SPDX-License-Identifier: Apache-2.0 OR MIT

"""Deterministic solver stand-in for the Lean export tests.

It answers each emitted SMT check independently, in either file or streaming
mode. The name it is installed under selects the answers:

- a name that starts with "timeout-first": `timeout` (the word Strata reads as
  a solver timeout) to the first check of the run and `unknown` to the others;
- another name that starts with "timeout": `timeout` to every check;
- a name that starts with "crash-timeout": no answer; at the first check it
  stops with a message Strata reads as a timeout;
- another name that starts with "crash": no answer; at the first check it stops;
- any other name: `unknown` to every check.

When the environment variable STRATA_TEST_SOLVER_LOG names a file, one line is
appended to it for each check answered, so a test can count the answers.
"""

import os
import sys

name = os.path.basename(sys.argv[0])
log = os.environ.get("STRATA_TEST_SOLVER_LOG")
source = open(sys.argv[1], encoding="utf-8") if len(sys.argv) == 2 else sys.stdin
checks = 0
for line in source:
    command = line.lstrip()
    if command.startswith(("(check-sat)", "(check-sat-assuming ")):
        if name.startswith("crash"):
            if name.startswith("crash-timeout"):
                print("interrupted by timeout.", flush=True)
            sys.exit(1)
        first_only = name.startswith("timeout-first")
        timeout = name.startswith("timeout") and (checks == 0 or not first_only)
        answer = "timeout" if timeout else "unknown"
        checks += 1
        if log:
            with open(log, "a", encoding="utf-8") as record:
                record.write(f"{answer}\n")
        print(answer, flush=True)
    elif command.startswith("(get-value "):
        print('(error "fixture has no model")', flush=True)
    elif command.startswith("(exit)"):
        break
