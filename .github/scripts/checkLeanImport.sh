#!/bin/sh
# Check to identify modules that inadvertently import all of Lean.
# We want to encourage only importing parts of Lean when needed.

! (find . -name "*.lean" -type f -print0 | xargs -0 grep -E -n '^import Lean$')