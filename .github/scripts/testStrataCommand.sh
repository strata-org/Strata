#!/bin/bash
set -e

# This runs the Strata command line to validate some basic functionality.

temp_dir=$(mktemp -d)
echo "Storing temporary results in $temp_dir"

function exiting() { rm -R "${temp_dir}"; exit; }
trap exiting exit

strata="./.lake/build/bin/strata"

failed=0

# Expect a non-zero exit and a substring in stderr.
expect_error() {
  local description="$1" expected="$2"
  shift 2
  output=$("$@" 2>&1) && { echo "FAIL: $description (expected nonzero exit)"; failed=1; return; }
  if ! echo "$output" | grep -qF "$expected"; then
    echo "FAIL: $description"
    echo "  expected substring: $expected"
    echo "  got: $output"
    failed=1
  else
    echo "PASS: $description"
  fi
}

# Expect a zero exit and a substring in stdout.
expect_output() {
  local description="$1" expected="$2"
  shift 2
  output=$("$@" 2>&1)
  rc=$?
  if [ $rc -ne 0 ]; then
    echo "FAIL: $description (exit code $rc)"
    failed=1
  elif ! echo "$output" | grep -qF "$expected"; then
    echo "FAIL: $description"
    echo "  expected substring: $expected"
    echo "  got: $output"
    failed=1
  else
    echo "PASS: $description"
  fi
}

# --- Error message and help output tests ---
# Disable set -e so we can test commands that intentionally fail.
set +e

# Error cases
expect_error "no args"            "Expected subcommand"              $strata
expect_error "unknown command"    "Expected subcommand, got bogus"   $strata bogus
expect_error "unknown flag"       "Unknown option --bogus"           $strata check --bogus
expect_error "missing flag value" "Expected value after --include"   $strata check --include
expect_error "missing positional" "check expects 1 argument(s)"      $strata check
expect_error "extra positional"   "check expects 1 argument(s)"      $strata check a b

# Per-command hint in error messages
expect_error "hint for check"     "strata check --help"              $strata check --bogus
expect_error "hint for diff"      "strata diff --help"               $strata diff --bogus

# Help output
expect_output "global help"            "Command-line utilities"      $strata --help
expect_output "per-command help"       "Usage: strata check"         $strata check --help
expect_output "help with other flags"  "Usage: strata check"         $strata check --include foo --help

set -e

# --- Ion round-trip tests ---

# Convert dialect to Ion
$strata toIon --include Examples/dialects Examples/dialects/Arith.dialect.st "$temp_dir/Arith.dialect.st.ion"

# Pretty print dialect to remove spacing.
$strata print --include Examples/dialects Examples/dialects/Arith.dialect.st > "$temp_dir/Arith.dialect.st"

# Print Ion file and compare with previous run
$strata print --include Examples/dialects "$temp_dir/Arith.dialect.st.ion" | cmp - "$temp_dir/Arith.dialect.st"

if [ $failed -ne 0 ]; then
  echo "Some tests failed."
  exit 1
fi
